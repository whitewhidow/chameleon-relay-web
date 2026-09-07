# Chameleon Ultra — BLE EMV Relay (web app)

A single web page that connects to **both** Chameleon Ultras over **Bluetooth**
(Web Bluetooth) and bridges an ISO14443-4 / EMV relay in the browser. No USB, no
host script — the two boards are battery-powered and untethered.

```
[real card] <-RF-> MOLE (board2, reader)  ==BLE==\
                                                   >== browser bridges the APDUs
[terminal/phone] <-RF-> GHOST (board1, tag) ==BLE=/
```

**Lab / authorised-research use only.** Relay only cards you own, against
terminals you own or are authorised to test.

## Requirements

- The relay firmware on both Ultras (reports app_version `99.x`).
- A **Web Bluetooth** browser: desktop or Android **Chrome/Edge**. iOS Safari has
  no Web Bluetooth (Bluefy works). The bridging browser needs a working BLE radio.
- BLE pairing is **disabled** on the Ultra by default, so there is no passkey and
  no OS pairing step. (If you enabled pairing in the GUI, pair the board in the OS
  first.)

## Run it

Web Bluetooth needs a secure context — `https://` or `http://localhost` (not
`file://`).

- **Hosted:** GitHub Pages serves this repo at
  `https://<owner>.github.io/chameleon-relay-web/`.
- **Local:** `python3 -m http.server 8000` in this folder, open `http://localhost:8000`.

## Use

1. **Connect** Board 1 (Ghost — at the terminal/phone) and pick an Ultra in the
   chooser; it lights **red**. **Connect** Board 2 (Mole — at the card); it lights
   **blue**. (Both advertise as "ChameleonUltra", so the identify colour tells them
   apart.)
2. Pick a **Mode**:
   - **A** — ghost emulates continuously, re-scans the mole per tap.
   - **B** (gate-on-card) — ghost withholds emulation (phone sees nothing) until
     the mole has the card seated; re-arms live on placement, dark on removal.
3. Put the card on the **mole**, click **Start relay**, tap the terminal/phone on
   the **ghost**. On-screen dots mirror each board's LED (green ready · blue
   relaying · red waiting) and the log shows every APDU.

## How it works

`relay.js` is a browser port of the reference host tool `relay_poc.py`:

- **Transport** — Nordic UART Service (`6E40xxxx` UUIDs). The Ultra carries the
  same `0x11`-SOF/LRC command frames over BLE as over USB, so the frame codec is a
  1:1 port (verified byte-identical to the reference `make_data_frame_bytes`).
- **Bridge** — the mole opens a persistent reader session (`RELAY_START`) and the
  ghost's `APDU_RECV`/`APDU_SEND` are wired straight to the mole's `RELAY_APDU`. On
  PPSE (a new transaction) the mole session is re-opened for a fresh cryptogram.

## Notes / limits

- Web Bluetooth = Chrome/Edge/Android only; no iOS Safari.
- Each board is a separate `requestDevice()` call — one click each.
- BLE adds latency over USB; the firmware's WTX keep-alives cover the terminal's
  wait, but reads are a little slower than the USB path.
- The relay firmware for the Ultras lives in a separate (private) repository.
