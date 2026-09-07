/*
 * Chameleon BLE relay — WebSocket rendezvous server (Phase 2).
 *
 * LAB / AUTHORISED-RESEARCH USE ONLY.
 *
 * A dumb pipe: two browsers (the mole phone and the ghost phone) each open a
 * WebSocket, send {t:'join', room, role}, and every other message one sends is
 * forwarded verbatim to the other member of the same room. No card logic lives
 * here. Rooms hold at most two members; a third join to a full room is rejected.
 *
 * Local:  npm install && npm start   -> ws://localhost:8080
 * Render: Web Service, build `npm install`, start `npm start` -> wss://<app>.onrender.com
 */
'use strict';
const http = require('http');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 8080;
const rooms = new Map(); // room -> Set<ws>

const server = http.createServer((req, res) => {
  if (req.url === '/health') { res.writeHead(200); res.end('ok'); return; }
  res.writeHead(200, { 'content-type': 'text/plain' });
  res.end('chameleon relay rendezvous — lab use only');
});

const wss = new WebSocketServer({ server });

function roomSet(room) {
  let s = rooms.get(room);
  if (!s) { s = new Set(); rooms.set(room, s); }
  return s;
}
function peersInfo(room) {
  const s = rooms.get(room);
  const roles = s ? [...s].map(c => c.role).filter(Boolean) : [];
  return { n: s ? s.size : 0, roles };
}
function announce(room) {
  const s = rooms.get(room); if (!s) return;
  const info = peersInfo(room);
  const text = JSON.stringify({ t: 'peers', n: info.n, roles: info.roles });
  for (const c of s) if (c.readyState === 1) c.send(text);
}

wss.on('connection', (ws) => {
  ws.room = null; ws.role = null;
  ws.on('message', (data) => {
    let msg;
    try { msg = JSON.parse(data.toString()); } catch { return; }
    if (msg.t === 'join') {
      const room = String(msg.room || '').slice(0, 64);
      if (!room) { ws.send(JSON.stringify({ t: 'error', reason: 'no room' })); return; }
      const s = roomSet(room);
      if (s.size >= 2 && !s.has(ws)) { ws.send(JSON.stringify({ t: 'error', reason: 'room full' })); return; }
      ws.room = room; ws.role = String(msg.role || '').slice(0, 16);
      s.add(ws);
      ws.send(JSON.stringify({ t: 'joined', room, role: ws.role, ...peersInfo(room) }));
      announce(room);
      return;
    }
    // forward everything else to the OTHER member(s) of the room
    if (!ws.room) return;
    const s = rooms.get(ws.room); if (!s) return;
    const text = data.toString();
    for (const c of s) if (c !== ws && c.readyState === 1) c.send(text);
  });
  ws.on('close', () => {
    if (ws.room && rooms.has(ws.room)) {
      const s = rooms.get(ws.room);
      s.delete(ws);
      if (s.size === 0) rooms.delete(ws.room); else announce(ws.room);
    }
  });
});

server.listen(PORT, () => console.log('chameleon relay rendezvous on :' + PORT));
