# Lab terminal test - runbook

Lab / authorised-research use only. Relay only cards you own, against terminals you
own or are authorised to test. Never submit a relayed or manipulated transaction to a
real issuer or over live payment rails. A genuine test terminal is not on live rails,
which is what makes this a legitimate test.

## 0. Prerequisites

- Both Chameleon Ultras flashed with the current relay firmware (lab/relay-poc), on
  battery, charged. Battery percentage shows in each board's status line in the portal
  (it turns red under 20 percent).
- Portal open in desktop or Android Chrome/Edge (not iOS Safari): the Pages site
  https://whitewhidow.github.io/chameleon-relay-web/ , or http://localhost:PORT if
  serving locally. Confirm the first log line shows the expected build tag.
- Your own card, and the terminal under test.

Roles: Ghost = the board you present to the terminal. Mole = the board at your card.

## 1. Does YOUR CARD support RRP?

Purpose: know whether the card even advertises relay resistance, so a "no RRP" result
later is interpretable.

1. Connect the Mole, place your card on it, relay stopped.
2. Click "Check RRP".
3. Read the log: per AID it shows the AIP relay-resistance bit and the result of the
   80 EA probe. The 80 EA probe is authoritative; the AIP bit is best-effort.

## 2. Does the TERMINAL use RRP? (one board, no live payment)

Purpose: determine whether the terminal enforces relay resistance, using a lure card
that advertises RRP. This does not complete a payment.

1. One-time: connect a board with your card on it, click "Build lure". Watch for
   "GPO AIP ... (RRP bit SET)". The lure is saved in this browser (per-origin,
   per-device - build it on whatever device you will carry to the terminal).
2. Connect the board you will tap on the terminal, click "RRP POS test".
3. Tap that board on the terminal.
   - "POS SENT 80 EA ... USES RRP" => the terminal enforces RRP.
   - "READ RECORD ... does NOT use RRP" => it does not.
4. The verdict is stored in Readers (timestamped). Open "Readers", rename the new entry
   to this terminal, and use "Download CSV" to keep the dataset.

A "yes" is conclusive. A "no" is only trustworthy because the lure genuinely advertises
RRP (that is what the forced AIP bit guarantees).

## 3. Full relay against the terminal

Purpose: relay your real card through to the terminal end to end.

1. Role: Local. Connect both boards. Card on the Mole, present the Ghost to the terminal.
2. Cache: off (live relay).
3. Click "Start relay".
4. Tap the Ghost on the terminal. Keep the card firm and centred on the Mole.
5. Watch the log: PPSE, SELECT, GPO, READ RECORD, GET DATA, and - if the terminal runs a
   payment - GENERATE AC. Per-APDU timing is printed.
   - If the terminal enforces RRP, the log prints an "RRP TIMING" line showing the 80 EA
     round trip versus the sub-millisecond a distance bound allows: the relay is orders of
     magnitude over budget and an enforcing terminal will reject it. This is physics, not a
     bug.
   - GENERATE AC is the one hop never exercised by the phone readers, so this may be the
     first time it relays live. Watch that it relays and returns a response.

## 4. Capture for analysis

Do this with the session STOPPED (an active session monopolises the board BLE channel,
so a log read times out; the ring buffers persist after Stop, nothing is lost).

- "Decode trace": prints a human-readable annotated transcript (PCB type + APDU name) to
  the log - reader<->ghost then mole<->card.
- "Export trace": downloads the full both-sides trace as JSON for deeper analysis.

Connect both boards before capturing so the trace has both sides. The ring holds 72
frames per direction; if a flow is long, Stop soon after the interesting part so it does
not scroll out.

## 5. Interpreting outcomes

- Terminal enforces RRP + card advertises RRP: the full relay's last step is time-rejected.
  Expected. Record it.
- Terminal does not enforce RRP: the relay can carry the whole flow including GENERATE AC,
  subject to floor limit and CVM rules.
- Empty/aborted mid-flow: usually coupling. Reposition the card on the Mole and the Ghost
  on the terminal; re-tap.
