# Chameleon relay — rendezvous server (Phase 2)

A tiny WebSocket broker that lets the two phones (Mole side + Ghost side) reach
each other over the internet. Two phones on cellular/WiFi can't connect directly
(carrier NAT), so both open a WebSocket *out* to this server; it pairs them by a
room code and forwards every message between them. **No card logic here — a dumb
pipe. Lab/authorised use only.**

## Run locally (for the two-desktop-windows test)

```
cd relay-server
npm install
npm start          # ws://localhost:8080  (health: http://localhost:8080/health)
```

Local testing note: Web Bluetooth needs a secure context, so serve the page at
`http://localhost` (e.g. `python3 -m http.server` in the repo root) and open **two
Chrome windows** there — one set to **Mole**, one to **Ghost**, both pointing at
`ws://localhost:8080`, same room code. Each window connects one board over BLE.
(Phones can't use `ws://` from the `https` Pages site — see below.)

## Deploy to Render (for real phones over 3G/5G/WiFi)

1. New → **Web Service**, point at this repo, root directory `relay-server/`.
2. Build command `npm install`, start command `npm start`.
3. Render serves it over TLS, so the phones use **`wss://<your-app>.onrender.com`**
   as the relay server URL (an `https` page must use `wss://`, not `ws://`).
4. On each phone: open the Pages site, pick **Mole** or **Ghost**, enter that
   `wss://` URL and the same room code, connect the link, connect the board, Start.

Free Render instances sleep when idle and take a few seconds to wake on the first
connection — just retry the link once if the first attempt times out.

## Protocol

Clients send `{t:"join", room, role}` once; thereafter every message is forwarded
verbatim to the other room member. App-level messages (handled by the web app, not
the server): `scan`/`scan_res`, `apdu`/`apdu_res`, `stat`/`stat_res`, `stop`. The
server also emits `joined`, `peers` (membership) and `error` (e.g. room full).
