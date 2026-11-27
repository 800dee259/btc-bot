#!/usr/bin/env python3
"""
Kalshi 15-minute Bitcoin (KXBTC15M) bot, v3: trades only when it has PROVEN it beats the market.

Why v3
  v2 sent lots of alerts (open calls, scalps, end calls) from a model that had never been shown
  to beat Kalshi's own prices. v3 removes the noise and changes three things:
    1. Settlement-aware model. Kalshi settles on a 60-second average. Late in the window part of
       that average is already known; v3 uses the real recorded prices for it, then models only
       the remaining uncertainty.
    2. Own volatility from live ticks (last 5 and 15 minutes, takes the larger), not stale candles.
    3. A PROOF GATE. Every would-be trade is tracked on paper through settlement with fees.
       --live only sends real orders while the paper record is positive AND statistically
       better than zero AND the model beats the market's own price (Brier). Otherwise it
       keeps paper-trading and sends nothing.

  Scalp signals (added): repeated ENTER alerts for the low-% side across most of the window,
  plus a regular pulse update. Alerts only, no orders.

  Snipe detector (added): warns when BTC is moving fast and accelerating toward the strike while
  Kalshi's price starts jumping, with a strength score. Warns loudly if it is against your side.

Modes
  python kalshi_bot_v3.py            DRY RUN / paper (no orders)
  python kalshi_bot_v3.py --demo     orders to Kalshi DEMO (fake money, gate ignored)
  python kalshi_bot_v3.py --live     real orders, but only while the gate is open
  python kalshi_bot_v3.py --stats    print the paper record and gate status, then exit

Setup
  pip install cryptography
  KALSHI_KEY_ID, KALSHI_KEY_PATH (or KALSHI_PRIVATE_KEY), optional TELEGRAM_TOKEN / TELEGRAM_CHAT_ID

Check the settlement rules of the market on Kalshi and set SETTLE_AVG_SECS to match.
NOT financial advice. Most traders in these markets lose money.
"""
import argparse
import base64
import http.client
import json
import math
import os
import socket
import statistics
import threading
import time
import urllib.parse
import urllib.request
import uuid
from collections import deque
from datetime import datetime, timezone

PROD = "https://external-api.kalshi.com/trade-api/v2"
DEMO = "https://external-api.demo.kalshi.co/trade-api/v2"
SERIES = "KXBTC15M"
LABEL = "BTC"

SPOT_SOURCES = {
    "coinbase": ("api.exchange.coinbase.com", "/products/BTC-USD/ticker", lambda d: float(d["price"])),
    "kraken": ("api.kraken.com", "/0/public/Ticker?pair=XBTUSD",
               lambda d: float(next(iter(d["result"].values()))["c"][0])),
    "bitstamp": ("www.bitstamp.net", "/api/v2/ticker/btcusd/", lambda d: float(d["last"])),
    "gemini": ("api.gemini.com", "/v1/pubticker/btcusd", lambda d: float(d["last"])),
}
FEED_GAP = {"coinbase": 0.25, "kraken": 1.0, "bitstamp": 0.5, "gemini": 1.0}

# ---- settings ----
STAKE_USD = 5.0
SETTLE_AVG_SECS = 60        # VERIFY on Kalshi: seconds averaged at settlement (0 = single price)
MIN_SECS, MAX_SECS = 15, 240  # only trade late, when the settlement average is mostly determined
MIN_EDGE = 0.05             # blended edge after fee must beat this
MAX_EDGE = 0.25             # larger "edges" are almost always bad data
MIN_PRICE, MAX_PRICE = 0.10, 0.92
MAX_SPREAD = 0.06
MARKET_WEIGHT = 0.5         # final probability = (1-w)*model + w*market mid; shrinks model overconfidence
VOL_MULT = 1.15             # inflate volatility a bit: overconfidence is what loses money
BASIS_FRAC = 0.0001         # allowance for our spot differing from Kalshi's reference index
MAX_SOURCE_DISAGREE = 0.0015
FEE_RATE = 0.07             # taker fee ~ FEE_RATE*p*(1-p) per contract; verify on Kalshi
POLL_SECS = 0.1
QUOTE_GAP, BOUNDARY_GAP, BOUNDARY_SECS = 0.3, 0.1, 3
QUOTE_MAX_AGE, FEED_MAX_AGE, REQUEST_TIMEOUT = 2.0, 3.0, 4
MAX_TRADES_PER_DAY = 20
MAX_DAILY_LOSS_USD = 20.0
MAX_ATTEMPTS, RETRY_SECS = 3, 5
BALANCE_REFRESH_SECS = 15
# proof gate
GATE_MIN_TRADES = 100       # paper/real trades needed before real money is allowed
GATE_MIN_MEAN = 0.01        # average profit per contract (after fees) must exceed this...
GATE_Z = 1.0                # ...and stay positive even one standard error lower
CALIB_LOG = "kalshi_v3_log.jsonl"
STATE_FILE = "kalshi_v3_state.json"
HEARTBEAT_SECS = 3600
CLOSED_STATES = {"closed", "settled", "finalized", "determined", "inactive"}

# ---- scalp signals (low-% side) ----
SCALP_MIN_PRICE = 0.15   # never scalp a side this cheap or cheaper (no 1c-10c lottery tickets)
SCALP_MAX_PRICE = 0.35   # ...and at most this (the "low percentage" side)
SCALP_MIN_SECS = 300     # no scalp entries in the last 5 min: too little time for a swing
SCALP_MAX_SECS = 840     # start signaling about 1 minute into the window
SCALP_MIN_EDGE = 0.05    # model win chance must beat price + fee by this
SCALP_COOLDOWN = 20      # seconds between ENTER alerts per window
SCALP_TARGET = 0.10      # take-profit: exit when price is 10c above entry
PULSE_SECS = 30          # status update interval when there's no entry
SURGE_MOVE = 0.35        # market price jump (35 points) from early in the window = "unexpected surge"
SCALP_MAX_SPREAD = 0.03  # bid/ask gap must be tight so you can actually get out
DECIDED_PRICE = 0.88     # if either side is priced 88%+ the round is decided: no scalps
VERDICT_MIN_EDGE = 0.05  # VALUE call: BTC model must beat Kalshi's price by this much after fees
VALUE_MIN_SECS = 90      # no VALUE alerts with under 1.5 min left
VALUE_MIN_PRICE, VALUE_MAX_PRICE = 0.15, 0.85   # never call value on a side priced outside this range
VALUE_COOLDOWN = 90      # secs between VALUE alerts for the same side
SWING_WINDOW = 180       # swing proof: look at the last 3 minutes of this side's price
SWING_MIN_MOVE = 0.04    # a swing = a move of at least 4 points one way, then back
SWING_MIN_REVERSALS = 2  # needs at least 2 reversals, and the price must have been at the exit level recently
SCALP_STOP = 0.08        # CUT alert if the exit price falls this far below entry
FLIP_WARN_PEAK_DROP = 0.05  # FLIP WARNING if your side falls 5c from its high since entry...
FLIP_WARN_FAST_DROP = 0.05  # ...or falls 5c in under 30s (a sudden flip)
FLIP_FAST_SECS = 30
HOLD_SECS = 45           # how often to send HOLD updates while a scalp is open
END_WARN_SECS = 45       # warn this many secs before the window ends if a scalp is still open
# market regime (choppy vs steady one-sided), measured on the Kalshi price
REGIME_WINDOW = 120      # look at the last 2 minutes
REGIME_STEP = 5          # sample the price every 5s
CHOP_MIN_PATH = 0.15     # price must have travelled at least 15 points...
CHOP_MAX_ER = 0.35       # ...while making little net progress = CHOPPY
TREND_MIN_NET = 0.10     # net move of at least 10 points...
TREND_MIN_ER = 0.55      # ...mostly in one direction = STEADY ONE-SIDED
OPEN_CALL_WINDOW = 45     # send the opening call within the first 45s of a window
WINDOW_SECS = 900         # length of a window (15 minutes)
SURGE_START_SECS = 600   # only measure the surge against prices seen with more than this many secs left

# ---- snipe detector ----
SNIPE_WATCH, SNIPE_BUILD, SNIPE_STRONG = 35, 55, 75   # score thresholds
SNIPE_COOLDOWN = 15       # secs between snipe alerts at the same level per window
SNIPE_REPEAT_SECS = 45    # re-alert at the same level only after this long


def stamp():
    return datetime.now().strftime("%H:%M:%S")


def mins(secs):
    """Time left as minutes, e.g. 12.5 min."""
    return f"{max(secs, 0) / 60:.1f} min"


def parse_time(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


# ---------- HTTP with kept-alive connections ----------
class _Conn(http.client.HTTPSConnection):
    def connect(self):
        super().connect()
        try:
            self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass


_tls = threading.local()


def _conn(host):
    conns = getattr(_tls, "conns", None)
    if conns is None:
        conns = _tls.conns = {}
    if host not in conns:
        conns[host] = _Conn(host, timeout=REQUEST_TIMEOUT)
    return conns[host]


def _drop(host):
    c = getattr(_tls, "conns", {}).pop(host, None)
    if c is not None:
        try:
            c.close()
        except Exception:
            pass


def request(host, method, path, headers=None, body=None):
    hdrs = {"User-Agent": "kalshi-bot/3.0", "Accept": "application/json"}
    if headers:
        hdrs.update(headers)
    for attempt in (0, 1):
        try:
            c = _conn(host)
            c.request(method, path, body=body, headers=hdrs)
            r = c.getresponse()
            data = r.read()
        except (http.client.HTTPException, OSError):
            _drop(host)
            if attempt:
                raise
            continue
        if r.status >= 400:
            raise RuntimeError(f"{method} {path} -> HTTP {r.status}: {data.decode(errors='replace')[:300]}")
        return json.loads(data) if data else {}


# ---------- Kalshi API ----------
class Kalshi:
    def __init__(self, base, key_id=None, key_path=None):
        u = urllib.parse.urlparse(base)
        self.host, self.prefix = u.netloc, u.path
        self.key_id, self.key = key_id, None
        if key_id and key_path:
            from cryptography.hazmat.primitives import serialization
            with open(key_path, "rb") as f:
                self.key = serialization.load_pem_private_key(f.read(), password=None)

    def _sign(self, ts, method, path):
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives.asymmetric import padding
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        msg = f"{ts}{method}{path}".encode()
        if isinstance(self.key, Ed25519PrivateKey):
            sig = self.key.sign(msg)
        else:
            sig = self.key.sign(msg, padding.PSS(mgf=padding.MGF1(hashes.SHA256()),
                                                 salt_length=padding.PSS.DIGEST_LENGTH), hashes.SHA256())
        return base64.b64encode(sig).decode()

    def call(self, method, endpoint, params=None, body=None):
        path = self.prefix + endpoint
        full = path + ("?" + urllib.parse.urlencode(params) if params else "")
        headers = {"Content-Type": "application/json"}
        if self.key:
            ts = str(int(time.time() * 1000))
            headers.update({"KALSHI-ACCESS-KEY": self.key_id, "KALSHI-ACCESS-TIMESTAMP": ts,
                            "KALSHI-ACCESS-SIGNATURE": self._sign(ts, method, path)})
        data = json.dumps(body).encode() if body is not None else None
        return request(self.host, method, full, headers, data)

    def open_market(self, series):
        res = self.call("GET", "/markets", {"series_ticker": series, "status": "open", "limit": 20})
        now = datetime.now(timezone.utc)
        live = [m for m in res.get("markets", []) if parse_time(m["close_time"]) > now]
        live.sort(key=lambda m: m["close_time"])
        return live[0] if live else None

    def get_market(self, ticker):
        return self.call("GET", f"/markets/{ticker}")["market"]

    def balance_usd(self):
        return self.call("GET", "/portfolio/balance")["balance"] / 100.0

    def place(self, ticker, side, price, count):
        body = {"ticker": ticker, "side": side, "count": f"{count:.2f}", "price": f"{price:.4f}",
                "time_in_force": "immediate_or_cancel", "self_trade_prevention_type": "taker_at_cross",
                "client_order_id": str(uuid.uuid4())}
        return self.call("POST", "/portfolio/events/orders", body=body)


# ---------- background data ----------
class Feeds:
    def __init__(self):
        self.latest, self.stop = {}, threading.Event()

    def start(self):
        for name in SPOT_SOURCES:
            threading.Thread(target=self._loop, args=(name,), daemon=True).start()

    def _loop(self, name):
        host, path, parse = SPOT_SOURCES[name]
        gap = FEED_GAP.get(name, 1.0)
        while not self.stop.is_set():
            t0 = time.time()
            try:
                self.latest[name] = (parse(request(host, "GET", path)), time.time())
            except Exception:
                self.stop.wait(2.0)
            self.stop.wait(max(0.0, gap - (time.time() - t0)))

    def quotes(self):
        now = time.time()
        return {n: p for n, (p, t) in list(self.latest.items()) if now - t <= FEED_MAX_AGE}


class MarketWatcher:
    def __init__(self, api):
        self.api, self.snap, self.stop = api, (None, 0.0), threading.Event()
        self.no_mkt_since, self._err_t = None, 0.0

    def start(self):
        threading.Thread(target=self._loop, daemon=True).start()

    def step(self):
        gap, cur, now = QUOTE_GAP, self.snap[0], datetime.now(timezone.utc)
        if cur is None or parse_time(cur["close_time"]) <= now:
            m, gap = self.api.open_market(SERIES), BOUNDARY_GAP
        else:
            m = self.api.get_market(cur["ticker"])
            if (parse_time(m["close_time"]) - now).total_seconds() <= BOUNDARY_SECS:
                gap = BOUNDARY_GAP
        if m is not None and m.get("status") in CLOSED_STATES:
            m = None
        if m is None:
            self.no_mkt_since = self.no_mkt_since or time.time()
            if time.time() - self.no_mkt_since > 20:
                gap = 1.0
        else:
            self.no_mkt_since = None
        self.snap = (m, time.time())
        return gap

    def _loop(self):
        while not self.stop.is_set():
            t0 = time.time()
            try:
                gap = self.step()
            except Exception as e:
                gap = 0.5
                if time.time() - self._err_t > 10:
                    self._err_t = time.time()
                    print(f"[{stamp()}] Kalshi quote error: {e}")
            self.stop.wait(max(0.0, gap - (time.time() - t0)))


def combine(quotes):
    vals = [v for v in quotes.values() if v and v > 0]
    if not vals:
        return None, "no spot data"
    med = statistics.median(vals)
    vals = [v for v in vals if abs(v - med) / med <= 0.005]
    spot = statistics.median(vals)
    if len(vals) > 1 and (max(vals) - min(vals)) / spot > MAX_SOURCE_DISAGREE:
        return None, f"exchange prices disagree ({min(vals):,.0f}-{max(vals):,.0f})"
    return spot, f"{len(vals)}/{len(SPOT_SOURCES)} feeds"


# ---------- model ----------
def realized_sigma(hist, window, step=10.0):
    """Dollar volatility per sqrt(second) from our own recorded prices over the last `window` secs."""
    if not hist:
        return None
    now, pts, last = hist[-1][0], [], None
    for t, p in hist:
        if t < now - window:
            continue
        if last is None or t - last >= step:
            pts.append((t, p))
            last = t
    if len(pts) < 12:
        return None
    r = [(b[1] - a[1]) / math.sqrt(b[0] - a[0]) for a, b in zip(pts, pts[1:])]
    return math.sqrt(sum(x * x for x in r) / len(r))


def t4_cdf(x):
    u = 1 + x * x / 4.0
    return 0.5 + 0.375 * (x / math.sqrt(u)) * (1 - (x * x / u) / 12.0)


def settle_distribution(spot, hist, now_t, close_t, sigma):
    """Mean and variance of the final settlement value (the average of the last SETTLE_AVG_SECS).
    The part of that average that has already happened is taken from recorded prices."""
    s, W = close_t - now_t, float(SETTLE_AVG_SECS)
    if W <= 0:
        return spot, sigma ** 2 * s
    if s >= W:
        return spot, sigma ** 2 * ((s - W) + W / 3.0)
    pts = [p for t, p in hist if close_t - W <= t <= now_t]
    if len(pts) < 5:
        return None
    a_obs = sum(pts) / len(pts)
    mean = ((W - s) * a_obs + s * spot) / W
    return mean, (s / W) ** 2 * sigma ** 2 * s / 3.0


def prob_up(spot, strike, hist, now_t, close_t, sigma):
    d = settle_distribution(spot, hist, now_t, close_t, sigma * VOL_MULT)
    if d is None:
        return None
    mean, var = d
    sd = math.sqrt(var + (BASIS_FRAC * spot) ** 2)
    p = t4_cdf((mean - strike) / sd * math.sqrt(2))     # t4 has variance 2: rescale to unit variance
    return min(0.97, max(0.03, p))


def fee(p):
    return FEE_RATE * p * (1 - p)


def lean_tag(p_up):
    """Green/red indicator plus how close the call is to a coin flip.
    Returns (text, side, win_chance). 'risk' = chance the call is wrong."""
    side = "UP" if p_up >= 0.5 else "DOWN"
    conf = p_up if side == "UP" else 1 - p_up
    dot = "\U0001F7E2" if side == "UP" else "\U0001F534"
    label = ("COIN FLIP" if conf < 0.60 else "RISKY" if conf < 0.75
             else "LEANING" if conf < 0.90 else "STRONG")
    return f"{dot} {side} {conf:.0%} ({label}, {1 - conf:.0%} risk)", side, conf


def pressure_score(hist, strike, mid_move, sigma, now_t):
    """-100..+100: which side is pushing harder right now. Positive = UP.
    Blends BTC momentum (30s and 2 min), time spent above/below the strike, and the Kalshi price move."""
    if not hist or not sigma:
        return None
    clip = lambda x: max(-1.0, min(1.0, x))

    def spot_ago(age):
        for t, p in hist:
            if t >= now_t - age:
                return p
        return None

    cur = hist[-1][1]
    s30, s120 = spot_ago(30), spot_ago(120)
    z30 = clip((cur - s30) / (sigma * math.sqrt(30)) / 2) if s30 else 0.0
    z120 = clip((cur - s120) / (sigma * math.sqrt(120)) / 2) if s120 else 0.0
    win = [p for t, p in hist if t >= now_t - 120]
    share = (sum(1 for p in win if p > strike) / len(win) - 0.5) * 2 if win else 0.0
    kd = clip(mid_move / 0.10)
    return round(100 * (0.35 * z30 + 0.20 * z120 + 0.25 * share + 0.20 * kd))


def snipe_score(hist, strike, sigma, now_t, secs, mid_move10):
    """0-100 strength of a sharp move toward flipping the round. Returns (score, dir, parts) or None."""
    if len(hist) < 60 or not sigma or secs <= 0:
        return None
    clip = lambda x: max(0.0, min(1.0, x))

    def ago(a):
        for t, p in hist:
            if t >= now_t - a:
                return p
        return hist[0][1]

    cur, p5, p20 = hist[-1][1], ago(5), ago(20)
    move = cur - p5
    if move == 0:
        return None
    d = "UP" if move > 0 else "DOWN"
    gap = strike - cur
    if gap * move < 0:                       # moving away from the strike: not a flip threat
        return None
    speed = clip(abs(move) / (sigma * math.sqrt(5)) / 3)
    r5, r15 = abs(move) / 5, abs(p5 - p20) / 15
    accel = clip((r5 / max(r15, sigma * 0.5) - 1) / 3)
    need = abs(gap) / (sigma * math.sqrt(max(secs, 1)))
    reach = clip(1 - need / 2.5)             # how close the move is to crossing the strike
    kal = clip(mid_move10 / 0.08) if (mid_move10 > 0) == (d == "UP") else 0.0
    score = round(100 * (0.30 * speed + 0.20 * accel + 0.30 * reach + 0.20 * kal))
    return score, d, {"speed": speed, "accel": accel, "reach": reach, "kalshi": kal}


def snipe_bar(sc):
    """10-block strength bar: yellow = watch, orange = building, red = imminent."""
    fill = max(0, min(10, round(sc / 10)))
    block = "\U0001F7E5" if sc >= SNIPE_STRONG else "\U0001F7E7" if sc >= SNIPE_BUILD else "\U0001F7E8"
    return block * fill + "\u2B1C" * (10 - fill)


def num(m, key):
    try:
        return float(m.get(key) or 0)
    except (TypeError, ValueError):
        return 0.0


def decide(m, spot, sigma, hist, now_t):
    """Returns (action or None, info, snapshot or None)."""
    strike = m.get("floor_strike")
    if strike is None:
        return None, "no strike yet", None
    strike = float(strike)
    close_t = parse_time(m["close_time"]).timestamp()
    secs = close_t - now_t
    if not (MIN_SECS <= secs <= MAX_SECS):
        return None, f"outside trading window ({mins(secs)} left)", None
    p_model = prob_up(spot, strike, hist, now_t, close_t, sigma)
    if p_model is None:
        return None, "not enough recorded prices yet", None
    ya, yb, na = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars"), num(m, "no_ask_dollars")
    mid = (ya + yb) / 2 if 0 < yb <= ya < 1 else None
    if mid is None:
        return None, "no two-sided book", None
    p = (1 - MARKET_WEIGHT) * p_model + MARKET_WEIGHT * mid
    snap = {"secs_left": round(secs), "spot": spot, "strike": strike, "p_model": round(p_model, 4),
            "p_blend": round(p, 4), "mid": mid, "sigma": round(sigma, 3)}
    info = f"{lean_tag(p)[0]} | {mins(secs)} model={p_model:.0%} mid={mid:.0%} blend={p:.0%} gap=${spot - strike:+,.0f}"
    if ya - yb > MAX_SPREAD:
        return None, info + f" | spread {ya - yb:.2f} too wide", snap
    opts = []
    if MIN_PRICE <= ya <= MAX_PRICE:
        opts.append(("UP", "bid", ya, ya, p - ya - fee(ya), p_model - ya - fee(ya)))
    if MIN_PRICE <= na <= MAX_PRICE:
        opts.append(("DOWN", "ask", yb, na, (1 - p) - na - fee(na), (1 - p_model) - na - fee(na)))
    if not opts:
        return None, info + " | price too extreme", snap
    name, side, order_price, cost, edge, raw_edge = max(opts, key=lambda o: o[4])
    info += f" | best={name} edge={edge:+.2f}"
    if edge < MIN_EDGE or raw_edge < MIN_EDGE:         # blended AND raw model must both clear the bar
        return None, info + " | no trade", snap
    if raw_edge > MAX_EDGE:
        return None, info + " | edge too large, likely bad data", snap
    count = int(STAKE_USD // cost)
    if count < 1:
        return None, info + " | stake too small", snap
    return {"name": name, "side": side, "price": order_price, "count": count,
            "cost": round(cost, 4), "edge": round(edge, 4),
            "p_win": round(p if name == "UP" else 1 - p, 4)}, info, snap


def scalp_signal(m, spot, sigma, hist, now_t):
    """Low-% side scalp signal. Returns a dict (with 'enter' True/False) or None. Alert only."""
    strike = m.get("floor_strike")
    if strike is None:
        return None
    close_t = parse_time(m["close_time"]).timestamp()
    secs = close_t - now_t
    if not (SCALP_MIN_SECS <= secs <= SCALP_MAX_SECS):
        return None
    pm = prob_up(spot, float(strike), hist, now_t, close_t, sigma)
    if pm is None:
        return None
    ya, yb, na = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars"), num(m, "no_ask_dollars")
    if not (0 < yb <= ya < 1) or ya - yb > SCALP_MAX_SPREAD:
        return None
    p = (1 - MARKET_WEIGHT) * pm + MARKET_WEIGHT * (ya + yb) / 2
    name, cost, p_side = ("UP", ya, p) if ya <= na else ("DOWN", na, 1 - p)
    if not (SCALP_MIN_PRICE <= cost <= SCALP_MAX_PRICE):
        return None
    edge = p_side - cost - fee(cost)
    return {"name": name, "cost": cost, "p_side": p_side, "p_up": p, "edge": edge,
            "target": min(0.95, cost + SCALP_TARGET), "secs": secs,
            "enter": edge >= SCALP_MIN_EDGE}


def mark(ok):
    return "\u2705" if ok else "\u274C"


def streak_text(seq):
    """seq is a list of 1 (win) / 0 (loss) in order. Returns e.g. '12W-8L (60%) | \U0001F525 3 win streak (best 6)'."""
    n = len(seq)
    if not n:
        return "no results yet"
    w = sum(seq)
    run, last = 0, seq[-1]
    for x in reversed(seq):
        if x != last:
            break
        run += 1
    best = cur = 0
    for x in seq:
        cur = cur + 1 if x == 1 else 0
        best = max(best, cur)
    now = f"\U0001F525 {run} win streak" if last == 1 else f"{run} loss streak"
    return f"{w}W-{n - w}L ({w / n:.0%}) | {now} (best {best})"


# ---------- ledger: tracks every trade to settlement and runs the proof gate ----------
class Ledger:
    def __init__(self, api):
        self.api, self.lock = api, threading.Lock()
        self.snaps, self.trades, self.opens = {}, {}, {}
        self.open_n, self.open_hit = 0, 0
        self.calls, self.call_seq, self.scalp_seq = {}, [], []
        self.pnl, self.bm, self.bk, self.nb = [], 0.0, 0.0, 0
        try:
            with open(CALIB_LOG) as f:
                for line in f:
                    r = json.loads(line)
                    if r.get("pnl") is not None:
                        self.pnl.append(r["pnl"])
                    if r.get("call_hit") is not None:
                        self.call_seq.append(int(r["call_hit"]))
                    if r.get("scalp_hit") is not None:
                        self.scalp_seq.append(int(r["scalp_hit"]))
                    if r.get("open_hit") is not None:
                        self.open_n += 1
                        self.open_hit += int(r["open_hit"])
                    if "p_model" in r and r.get("y") is not None:
                        self._brier(r["p_model"], r["mid"], r["y"])
        except Exception:
            pass

    def _brier(self, pm, mid, y):
        self.nb += 1
        self.bm += (pm - y) ** 2
        self.bk += (mid - y) ** 2

    def record_snap(self, tk, snap):
        if snap["secs_left"] <= 120 and tk not in self.snaps:
            self.snaps[tk] = snap               # one comparable forecast per window, ~2 min out

    def add_call(self, tk, side, conf):
        self.calls[tk] = {"side": side, "conf": round(conf, 4)}

    def record_scalp(self, tk, hit, how):
        """Log a finished scalp (take-profit = win, cut = loss, or judged at settlement). Returns record text."""
        with self.lock:
            self.scalp_seq.append(1 if hit else 0)
            txt = streak_text(self.scalp_seq)
        log_line(CALIB_LOG, {"t": datetime.now(timezone.utc).isoformat(), "market": tk,
                             "scalp_hit": 1 if hit else 0, "how": how})
        return txt

    def add_open(self, tk, side, conf):
        self.opens[tk] = {"side": side, "conf": round(conf, 4)}

    def open_stats(self):
        with self.lock:
            return self.open_hit, self.open_n

    def add_trade(self, tk, a):
        self.trades[tk] = dict(a)

    def stats(self):
        with self.lock:
            n = len(self.pnl)
            mean = sum(self.pnl) / n if n else 0.0
            se = (statistics.stdev(self.pnl) / math.sqrt(n)) if n > 1 else float("inf")
            bm = self.bm / self.nb if self.nb else None
            bk = self.bk / self.nb if self.nb else None
        return n, mean, se, bm, bk

    def gate(self):
        n, mean, se, bm, bk = self.stats()
        if n < GATE_MIN_TRADES:
            return False, f"need {GATE_MIN_TRADES} tracked trades, have {n}"
        if mean - GATE_Z * se <= GATE_MIN_MEAN:
            return False, f"avg {mean * 100:+.1f}c/contract (+/-{se * 100:.1f}c) is not clearly profitable"
        if bm is None or bm >= bk:
            return False, "model does not beat the market's own price (Brier)"
        return True, f"avg {mean * 100:+.1f}c/contract over {n} trades"

    def finish(self, tk, open_scalp=None):
        snap, trade, opn = self.snaps.pop(tk, None), self.trades.pop(tk, None), self.opens.pop(tk, None)
        call = self.calls.pop(tk, None)
        if snap or trade or opn or call or open_scalp:
            threading.Thread(target=self._settle, args=(tk, snap, trade, opn, call, open_scalp), daemon=True).start()

    def _settle(self, tk, snap, trade, opn=None, call=None, open_scalp=None):
        result = None
        for _ in range(20):
            time.sleep(15)
            try:
                result = self.api.get_market(tk).get("result")
            except Exception:
                continue
            if result in ("yes", "no"):
                break
        else:
            return
        y = 1.0 if result == "yes" else 0.0
        rec = {"t": datetime.now(timezone.utc).isoformat(), "market": tk, "result": result, "y": y}
        if snap:
            rec.update(snap)
            with self.lock:
                self._brier(snap["p_model"], snap["mid"], y)
        if trade:
            win = (trade["name"] == "UP") == (y == 1.0)
            pnl = (1.0 if win else 0.0) - trade["cost"] - fee(trade["cost"])
            rec["trade"], rec["pnl"] = trade, round(pnl, 4)
            with self.lock:
                self.pnl.append(pnl)
        lines = []
        if call:
            chit = (call["side"] == "UP") == (y == 1.0)
            rec["call"], rec["call_hit"] = call, int(chit)
            with self.lock:
                self.call_seq.append(int(chit))
                ctxt = streak_text(self.call_seq)
            lines.append(f"{mark(chit)} Call: {call['side']} at {call['conf']:.0%} "
                         f"{'WON' if chit else 'LOST'} (ended {result.upper()})\nCalls: {ctxt}")
        if opn:
            hit = (opn["side"] == "UP") == (y == 1.0)
            rec["open_call"], rec["open_hit"] = opn, int(hit)
            with self.lock:
                self.open_n += 1
                self.open_hit += int(hit)
                oh, on = self.open_hit, self.open_n
            lines.append(f"{mark(hit)} Opening call: {opn['side']} at {opn['conf']:.0%} "
                         f"{'HIT' if hit else 'MISSED'}\nOpening calls: {oh}/{on} ({oh / on:.0%})")
        if open_scalp:
            shit = (open_scalp["name"] == "UP") == (y == 1.0)
            stxt = self.record_scalp(tk, shit, "settlement")
            lines.append(f"{mark(shit)} Scalp held to settlement: {open_scalp['name']} "
                         f"{'WON' if shit else 'LOST'}\nScalps: {stxt}")
        log_line(CALIB_LOG, rec)
        if lines:
            report = "\n".join(lines)
            print(f"[{stamp()}] ROUND RESULT {tk}: " + report.replace("\n", " | "))
            notify(f"\U0001F4CA {LABEL} round result", report)
        n, mean, se, bm, bk = self.stats()
        msg = f"settled {tk}: {result.upper()}"
        if trade:
            msg += f" | {trade['name']} {'WON' if rec['pnl'] > 0 else 'LOST'} {rec['pnl'] * 100:+.0f}c/contract"
        msg += f" | record: {n} trades, avg {mean * 100:+.1f}c"
        if bm is not None:
            msg += f" | Brier model {bm:.3f} vs market {bk:.3f}"
        print(f"[{stamp()}] {msg}")


# ---------- alerts / logs / state ----------
def log_line(path, rec):
    with open(path, "a") as f:
        f.write(json.dumps(rec) + "\n")


_pending = []


def notify(title, message, block=False):
    token, chat = os.environ.get("TELEGRAM_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    if not (token and chat):
        return

    def send():
        for cid in [c.strip() for c in chat.split(",") if c.strip()]:
            try:
                body = json.dumps({"chat_id": cid, "text": f"{title}\n{message}"}).encode()
                urllib.request.urlopen(urllib.request.Request(
                    f"https://api.telegram.org/bot{token}/sendMessage", data=body, method="POST",
                    headers={"Content-Type": "application/json"}), timeout=10).close()
            except Exception as e:
                print(f"[{stamp()}] could not send alert: {e}")

    if block:
        send()
    else:
        t = threading.Thread(target=send, daemon=True)
        t.start()
        _pending.append(t)


def flush_alerts(timeout=15):
    end = time.time() + timeout
    for t in _pending:
        t.join(max(0.0, end - time.time()))


def load_state():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except Exception:
        return {}


# ---------- the bot ----------
class Bot:
    def __init__(self, api, send_orders, gated, once):
        self.api, self.send, self.gated, self.once = api, send_orders, gated, once
        self.feeds, self.watch, self.ledger = Feeds(), MarketWatcher(api), Ledger(api)
        self.hist = deque(maxlen=4000)           # (time, spot) every ~0.4s, about 27 minutes
        self.market, self.attempts, self._said = None, {}, {}
        self.sig_cache = (0.0, None)
        self.called, self.sat_out, self.coinflip, self.reason = set(), set(), set(), {}
        self._err_alert = 0.0
        self.lean = {}                           # ticker -> (current side, flip count)
        self.last_scalp, self.last_pulse = {}, {}  # scalp signal timers per ticker
        self.opened = set()
        self.mids, self.cur_regime, self.last_regime_alert = deque(maxlen=600), ("WARMING", None), 0.0
        self.scalp_pos, self.rotate_from, self.last_hold = {}, {}, {}
        self.tp_sent, self.end_sent, self.warn_sent = set(), set(), set()
        self.cur_press, self.press_hist, self.last_shift = None, deque(maxlen=200), {}
        self.cur_snipe, self.snipe_sent = None, {}   # snipe detector state
        self.cur_verdict, self.last_value = None, {}
        self.first_mid, self.surged = {}, {}       # surge detection per ticker
        self.scalp_lean = {}                       # ticker -> (side, flip count) for scalp messages
        self.last_log, self.last_hb = 0.0, time.time()
        self.bal, self.bal_t = None, 0.0
        self.day = datetime.now(timezone.utc).date()
        st = load_state()
        if st.get("day") != str(self.day):
            st = {"day": str(self.day), "traded": [], "trades_today": 0, "start_bal": None}
        self.traded, self.trades_today, self.start_bal = set(st["traded"]), st["trades_today"], st["start_bal"]

    def save(self):
        with open(STATE_FILE, "w") as f:
            json.dump({"day": str(self.day), "traded": sorted(self.traded),
                       "trades_today": self.trades_today, "start_bal": self.start_bal}, f)

    def refresh_balance(self):
        self.bal, self.bal_t = self.api.balance_usd(), time.time()
        return self.bal

    def _say(self, key, msg, every=5.0):
        if time.time() - self._said.get(key, 0.0) >= every:
            self._said[key] = time.time()
            print(f"[{stamp()}] {msg}")

    def sigma(self):
        t, v = self.sig_cache
        if time.time() - t < 3.0:
            return v
        h = list(self.hist)
        a, b = realized_sigma(h, 900), realized_sigma(h, 300)
        v = max(a, b) if a and b else None       # take the larger: err toward less confidence
        if v is not None:
            spot = h[-1][1]
            v = min(max(v, 0.00002 * spot), 0.0003 * spot)
        self.sig_cache = (time.time(), v)
        return v

    def startup(self):
        if self.api.key:
            try:
                if self.start_bal is None:
                    self.start_bal = self.refresh_balance()
                print(f"[{stamp()}] starting balance ${self.start_bal:,.2f}")
            except Exception as e:
                print(f"[{stamp()}] could not read balance: {e}")
        self.save()
        if self.send and self.start_bal is None:
            print("Refusing to send orders without a readable balance (needed for the loss limit).")
            return False
        return True

    def tick(self):
        today = datetime.now(timezone.utc).date()
        if today != self.day:
            self.day, self.trades_today = today, 0
            self.traded.clear()
            self.start_bal = self.refresh_balance() if self.api.key else None
            self.save()
        if self.send and self.start_bal is not None:
            if self.bal is None or time.time() - self.bal_t > BALANCE_REFRESH_SECS:
                self.refresh_balance()
            if self.bal <= self.start_bal - MAX_DAILY_LOSS_USD:
                print(f"[{stamp()}] daily loss limit reached (${self.bal:,.2f}). Stopping.")
                notify("Kalshi bot STOPPED: daily loss limit", f"Balance ${self.bal:,.2f}", block=True)
                return True
        if not self.once and time.time() - self.last_hb >= HEARTBEAT_SECS:
            self.last_hb = time.time()
            n, mean, se, bm, bk = self.stats_line()
            notify("Kalshi bot alive", f"{self.trades_today} trades today | {n} tracked, avg {mean * 100:+.1f}c/contract\n"
                   f"Calls: {streak_text(self.ledger.call_seq)}\nScalps: {streak_text(self.ledger.scalp_seq)}")

        m, m_t = self.watch.snap
        if self.market is not None and (m is None or m["ticker"] != self.market["ticker"]):
            old = self.market["ticker"]
            self.ledger.finish(old, self.scalp_pos.pop(old, None))
            if old not in self.called:
                notify(f"\u23F8\uFE0F Kalshi {LABEL}: SAT OUT last round",
                       f"No call was sent for {old}. Reason: {self.reason.get(old, 'never reached the trading window')}.\n"
                       + self.surge_note(old))
        self.market = m
        if m is None:
            self._say("nomkt", "no open market found (watching for the next one)")
            return False
        q_age = time.time() - m_t
        if q_age > QUOTE_MAX_AGE:
            self._say("stale", f"Kalshi quote is {q_age:.1f}s old, skipping")
            self.sit_out(m, f"Kalshi quote is stale ({q_age:.0f}s old)")
            return False
        spot, note = combine(self.feeds.quotes())
        if spot is None:
            self._say("spot", f"skipping, {note}")
            self.sit_out(m, note)
            return False
        now_t = time.time()
        if not self.hist or now_t - self.hist[-1][0] >= 0.4:
            self.hist.append((now_t, spot))
        sigma = self.sigma()
        if sigma is None:
            self._say("warm", "warming up: collecting prices for volatility (about 3 minutes)")
            self.sit_out(m, "bot is still warming up (collecting prices)")
            return False

        tk = m["ticker"]
        action, info, snap = decide(m, spot, sigma, list(self.hist), now_t)
        self.reason[tk] = info
        self.open_call(m, spot, sigma, now_t)       # quick opening call (first ~45s of a window)
        self.surge_check(m)                         # detect unexpected surges (explains late calls)
        self.update_regime(m, now_t)                # choppy vs steady one-sided
        self.update_pressure(m, spot, sigma, now_t) # which side is pushing harder
        self.snipe_check(m, spot, sigma, now_t)     # sudden sharp move toward flipping the round
        self.update_verdict(m, spot, sigma, now_t)  # where the BTC model disagrees with Kalshi's price
        self.scalp_check(m, spot, sigma, now_t)     # low-% side scalp signals (alert only)
        self.manage_position(m, now_t)              # take-profit / hold / cut / rotate alerts
        if not snap:
            self.sit_out(m, info)
        if snap:
            self.ledger.record_snap(tk, snap)
            _, side_now, conf_now = lean_tag(snap["p_blend"])
            prev = self.lean.get(tk)
            if prev and prev[0] != side_now and conf_now >= 0.60:
                n = prev[1] + 1
                self.lean[tk] = (side_now, n)
                print(f"[{stamp()}] \U0001F504 FLIP {tk}: now {lean_tag(snap['p_blend'])[0]} | flipped {n}x this window")
                notify(f"\U0001F504 Kalshi {LABEL} FLIP", f"{lean_tag(snap['p_blend'])[0]}\n"
                       f"Flipped {n}x this window. {mins(snap['secs_left'])} left, spot ${spot:,.2f} vs strike ${snap['strike']:,.2f}.")
            elif not prev:
                self.lean[tk] = (side_now, 0)
            if tk in self.coinflip and conf_now >= 0.75:
                self.coinflip.discard(tk)
                notify(f"\u2705 Kalshi {LABEL}: RISK DROPPED", f"{lean_tag(snap['p_blend'])[0]}\n"
                       f"{mins(snap['secs_left'])} left. This was a coin flip earlier; it is a firmer call now.")
            if tk not in self.called:               # one call per window, as soon as it is inside the trading window
                self.called.add(tk)
                self.ledger.add_call(tk, side_now, conf_now)
                flip = conf_now < 0.60
                if flip:
                    self.coinflip.add(tk)
                ya, na = num(m, "yes_ask_dollars"), num(m, "no_ask_dollars")
                if tk not in self.surged and tk not in self.last_scalp and conf_now >= 0.90:
                    self.surged[tk] = (side_now, None, snap["mid"])
                flips_n = max(self.lean.get(tk, (None, 0))[1], self.scalp_lean.get(tk, (None, 0))[1])
                notify(f"Kalshi {LABEL} CALL", f"{lean_tag(snap['p_blend'])[0]}\n"
                       f"{self.verdict_line()}\n"
                       f"Flip risk: {1 - conf_now:.0%} | flipped {flips_n}x\n"
                       f"Snipe: {self.snipe_label()}\n"
                       f"Market: {self.regime_label()}\n"
                       f"\u2694\uFE0F Pressure: {self.press_line()}\n"
                       f"{mins(snap['secs_left'])} left | spot ${spot:,.2f} vs strike ${snap['strike']:,.2f} "
                       f"({spot - snap['strike']:+,.0f})\nKalshi: YES ask {ya * 100:.0f}c / NO ask {na * 100:.0f}c\n"
                       + ("\u23F8\uFE0F SIT OUT: this is a coin flip. Wait, risk drops later in the window; "
                          "you will get a RISK DROPPED alert if it firms up.\n" if flip else "")
                       + self.surge_note(tk)
                       + "Alert only, no order placed.")
        tries, next_try = self.attempts.get(tk, (0, 0.0))
        will_act = bool(action) and tk not in self.traded and self.trades_today < MAX_TRADES_PER_DAY \
            and now_t >= next_try
        if will_act or now_t - self.last_log >= 15:
            self.last_log = now_t
            print(f"[{stamp()}] {tk} spot={spot:,.2f} ({note}) strike={m.get('floor_strike')} | {info}")
        if will_act:
            self.act(tk, action, tries)
        return False

    def open_call(self, m, spot, sigma, now_t):
        """One quick call in the first seconds of a window: where will price settle vs the strike?"""
        tk = m["ticker"]
        if tk in self.opened or m.get("floor_strike") is None:
            return
        close_t = parse_time(m["close_time"]).timestamp()
        secs = close_t - now_t
        if not (WINDOW_SECS - OPEN_CALL_WINDOW <= secs <= WINDOW_SECS):
            return
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        if not (0 < yb <= ya < 1):
            return
        strike = float(m["floor_strike"])
        pm = prob_up(spot, strike, list(self.hist), now_t, close_t, sigma)
        if pm is None:
            return
        p = (1 - MARKET_WEIGHT) * pm + MARKET_WEIGHT * (ya + yb) / 2
        txt, side, conf = lean_tag(p)
        self.opened.add(tk)
        self.ledger.add_open(tk, side, conf)
        hit, n = self.ledger.open_stats()
        rec_txt = f"Opening-call record: {hit}/{n} ({hit / n:.0%})" if n else "Opening-call record: no results yet"
        notify(f"\u26A1 {LABEL} OPENING CALL",
               f"{txt}\n{mins(secs)} left | spot ${spot:,.2f} vs strike ${strike:,.2f} ({spot - strike:+,.0f})\n"
               f"Early read with ~15 min to go: far less certain than the late call, "
               f"price can still swing either way. {rec_txt}.")
        print(f"[{stamp()}] OPENING CALL {tk}: {txt}")

    def surge_check(self, m):
        """Flag a sudden one-sided move so the group knows why there were no early calls."""
        tk = m["ticker"]
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        if not (0 < yb <= ya < 1):
            return
        mid = (ya + yb) / 2
        secs = parse_time(m["close_time"]).timestamp() - time.time()
        if tk not in self.first_mid:
            # starting price is only trusted if we saw the window early
            self.first_mid[tk] = mid if secs > SURGE_START_SECS else None
        first = self.first_mid[tk]
        if tk in self.surged or secs <= MAX_SECS:
            return
        side = "UP" if mid >= 0.5 else "DOWN"
        if first is not None and abs(mid - first) >= SURGE_MOVE:
            self.surged[tk] = (side, first, mid)
            notify(f"\U0001F680 {LABEL} SURGE {side}",
                   f"Unexpected sudden move: market went {first:.0%} -> {mid:.0%} on UP with {mins(secs)} left.\n"
                   f"The price jumped too fast to enter safely, so NO early calls this round. "
                   f"The bot will send its normal call in the last 4 minutes.")
        elif first is None and (mid >= 0.85 or mid <= 0.15):
            self.surged[tk] = (side, None, mid)
            notify(f"\U0001F680 {LABEL} ONE-SIDED MARKET",
                   f"Market is already {mid:.0%} on UP with {mins(secs)} left. No safe entry, so NO early calls. "
                   f"The bot will send its normal call in the last 4 minutes.")
        else:
            return
        print(f"[{stamp()}] SURGE {side} {tk}: {self.surged[tk]}")

    def surge_note(self, tk):
        s = self.surged.get(tk)
        if not s:
            return ""
        side, first, mid = s
        if first is None:
            why = f"the market moved sharply {side} early and stayed one-sided ({mid:.0%} on UP)"
        else:
            why = f"unexpected {side} surge, market went {first:.0%} -> {mid:.0%}"
        return (f"\U0001F680 WHY NO EARLIER CALLS: {why}. "
                f"There was no safe entry, so the bot sat out the round and is calling it now.\n")

    def regime_label(self):
        name, d = self.cur_regime[0], self.cur_regime[1]
        if name == "CHOPPY":
            return "\U0001F500 CHOPPY (swinging up and down)"
        if name == "TRENDING":
            return f"\u27A1\uFE0F STEADY ONE-SIDED {d}"
        if name == "DECIDED":
            return f"\U0001F512 DECIDED {d} (round is basically over, no scalps)"
        return "\u23F3 MIXED / unclear" if name == "MIXED" else "\u23F3 measuring..."

    def model_trust(self):
        n, mean, se, bm, bk = self.ledger.stats()
        nb = self.ledger.nb
        if nb < 30:
            return f"model unproven: only {nb} rounds scored"
        if bm < bk:
            return f"model has beaten Kalshi's price over {nb} rounds"
        return f"model has NOT beaten Kalshi's price over {nb} rounds, treat as weak"

    def update_verdict(self, m, spot, sigma, now_t):
        """Compare the bot's own BTC-based probability with Kalshi's price. Only a gap is real information."""
        self.cur_verdict = None
        tk, strike = m["ticker"], m.get("floor_strike")
        if strike is None or sigma is None:
            return
        close_t = parse_time(m["close_time"]).timestamp()
        secs = close_t - now_t
        pm = prob_up(spot, float(strike), list(self.hist), now_t, close_t, sigma)   # raw model, not blended
        ya, yb, na = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars"), num(m, "no_ask_dollars")
        if pm is None or not (0 < yb <= ya < 1):
            return
        opts = []
        if VALUE_MIN_PRICE <= ya <= VALUE_MAX_PRICE:
            opts.append(("UP", ya, pm - ya - fee(ya)))
        if VALUE_MIN_PRICE <= na <= VALUE_MAX_PRICE:
            opts.append(("DOWN", na, (1 - pm) - na - fee(na)))
        best = max(opts, key=lambda o: o[2]) if opts else None
        self.cur_verdict = {"pm": pm, "mid": (ya + yb) / 2, "best": best, "spread": ya - yb, "secs": secs}
        if (best and VERDICT_MIN_EDGE <= best[2] <= MAX_EDGE and ya - yb <= MAX_SPREAD and secs >= VALUE_MIN_SECS
                and self.cur_regime[0] != "DECIDED"
                and now_t - self.last_value.get((tk, best[0]), 0) >= VALUE_COOLDOWN):
            self.last_value[(tk, best[0])] = now_t
            notify(f"\U0001F3AF {LABEL} VALUE: {best[0]} is underpriced",
                   f"{self.verdict_line()}\nSnipe: {self.snipe_label()}\n"
                   f"{mins(secs)} left | spot ${spot:,.2f} vs strike ${float(strike):,.2f}\n"
                   f"A mispricing estimate from the BTC model, NOT a guarantee. Alert only.")
            print(f"[{stamp()}] VALUE {best[0]} {tk} edge={best[2]:+.2f}")

    def verdict_line(self):
        v = self.cur_verdict
        if not v:
            return "Verdict: measuring..."
        pm, mid, best = v["pm"], v["mid"], v["best"]
        trust = self.model_trust()
        if best and best[2] > MAX_EDGE:
            return f"Verdict: model and Kalshi disagree by too much (likely bad data). No pick.\n({trust})"
        if best and best[2] >= VERDICT_MIN_EDGE and v["spread"] <= MAX_SPREAD:
            side, price, edge = best
            p_side, k_side = (pm, mid) if side == "UP" else (1 - pm, 1 - mid)
            return (f"\U0001F3AF VALUE: {side} looks underpriced. BTC model {p_side:.0%} vs Kalshi {k_side:.0%} "
                    f"(buy @ {price * 100:.0f}c, edge {edge:+.2f})\n({trust})")
        return (f"Verdict: NO EDGE. BTC model says UP {pm:.0%}, Kalshi says UP {mid:.0%}. "
                f"They agree, so there is no pick here.\n({trust})")

    def press_line(self):
        sc = self.cur_press
        if sc is None:
            return "measuring..."
        up = (sc + 100) // 2
        filled = round(up / 10)
        bar = "\U0001F7E2" * filled + "\U0001F534" * (10 - filled)
        if abs(sc) < 15:
            tag = "even fight"
        else:
            side = "UP" if sc > 0 else "DOWN"
            tag = f"{side} pushing harder" if abs(sc) >= 40 else f"{side} edging ahead"
        return f"{bar} UP {up}% / DOWN {100 - up}% ({tag})"

    def update_pressure(self, m, spot, sigma, now_t):
        tk, strike = m["ticker"], m.get("floor_strike")
        if strike is None or sigma is None:
            return
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        mid_move = 0.0
        if 0 < yb <= ya < 1:
            past = [mid for t, k, mid in self.mids if k == tk and 25 <= now_t - t <= 45]
            if past:
                mid_move = (ya + yb) / 2 - past[-1]
        score = pressure_score(list(self.hist), float(strike), mid_move, sigma, now_t)
        if score is None:
            return
        self.cur_press = score
        if not self.press_hist or now_t - self.press_hist[-1][0] >= 5:
            self.press_hist.append((now_t, tk, score))
        old = [sc for t, k, sc in self.press_hist if k == tk and 20 <= now_t - t <= 90]
        flipped = any((o > 0) != (score > 0) and abs(o) >= 20 for o in old)
        if flipped and abs(score) >= 30 and now_t - self.last_shift.get(tk, 0) >= 60:
            self.last_shift[tk] = now_t
            side = "UP" if score > 0 else "DOWN"
            secs = parse_time(m["close_time"]).timestamp() - now_t
            notify(f"\u2694\uFE0F {LABEL} MOMENTUM SHIFT: {side} now pushing harder",
                   f"{self.press_line()}\nThe other side was ahead a minute ago. {mins(secs)} left.")
            print(f"[{stamp()}] MOMENTUM SHIFT -> {side} {tk} score={score}")

    def snipe_label(self):
        s = self.cur_snipe
        if not s or s[0] < SNIPE_WATCH:
            return "none detected"
        sc, d = s[0], s[1]
        lvl = "IMMINENT" if sc >= SNIPE_STRONG else "BUILDING" if sc >= SNIPE_BUILD else "WATCH"
        return f"\U0001F3AF {lvl} {d} ({sc}/100)\n{snipe_bar(sc)}"

    def snipe_check(self, m, spot, sigma, now_t):
        """Detect a sharp, accelerating BTC move toward the strike and alert with a strength level.
        If you hold a side (scalp or paper trade) or there is a main lean, warns when it is against it."""
        tk, strike = m["ticker"], m.get("floor_strike")
        self.cur_snipe = None
        if strike is None or sigma is None:
            return
        secs = parse_time(m["close_time"]).timestamp() - now_t
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        mid_move = 0.0
        if 0 < yb <= ya < 1:
            past = [mid for t, k, mid in self.mids if k == tk and 8 <= now_t - t <= 14]
            if past:
                mid_move = (ya + yb) / 2 - past[-1]
        r = snipe_score(list(self.hist), float(strike), sigma, now_t, secs, mid_move)
        if not r:
            return
        self.cur_snipe = r
        sc, d, parts = r
        if sc < SNIPE_WATCH:
            return
        lvl = 3 if sc >= SNIPE_STRONG else 2 if sc >= SNIPE_BUILD else 1
        prev_lvl, last_t = self.snipe_sent.get(tk, (0, 0.0))
        if lvl <= prev_lvl and now_t - last_t < SNIPE_REPEAT_SECS:   # re-alert only on escalation or after a while
            return
        if lvl > prev_lvl and now_t - last_t < SNIPE_COOLDOWN and prev_lvl > 0 and lvl < 3:
            return                                                   # throttle small escalations (IMMINENT always passes)
        self.snipe_sent[tk] = (lvl, now_t)
        pos = self.scalp_pos.get(tk) or self.ledger.trades.get(tk)
        held = pos["name"] if pos else None
        lean = self.lean.get(tk, (None, 0))[0]
        mine = held or lean
        against = mine is not None and mine != d
        name = ("IMMINENT", "BUILDING", "WATCH")[3 - lvl]
        title = (f"\U0001F6A8 {LABEL} SNIPE {name} {d}"
                 + (f": AGAINST your {held}" if against and held
                    else f": against the {lean} lean" if against else ""))
        action = ("Consider exiting or tightening your stop NOW." if against and lvl >= 2
                  else "Stay alert, don't add to your side." if against else "It is moving with your side.")
        notify(title, f"Strength {sc}/100 ({name})\n{snipe_bar(sc)}\n"
               f"Speed {parts['speed']:.0%} | Acceleration {parts['accel']:.0%} | "
               f"Closing on strike {parts['reach']:.0%} | Kalshi jumping {parts['kalshi']:.0%}\n"
               f"{action}\n{mins(secs)} left | spot ${spot:,.2f} vs strike ${float(strike):,.2f}\n"
               f"Early warning, NOT a guarantee. Alert only.")
        print(f"[{stamp()}] SNIPE {name} {d} {tk} score={sc} against={against}")

    def swing_proof(self, tk, side, now_t):
        """Has THIS side's price actually been swinging, and was it recently at the exit level?
        Evidence only: it cannot promise the price will swing back again."""
        pts = [(t, mid if side == "UP" else 1 - mid) for t, k, mid in self.mids
               if k == tk and t >= now_t - SWING_WINDOW]
        if len(pts) < 20:
            return False, "still measuring"
        vals = [v for _, v in pts]
        cur = vals[-1]
        tp, peak = max(pts, key=lambda x: x[1])
        swings, d, ext = 0, 0, vals[0]
        for v in vals[1:]:
            if d == 0:
                if v - ext >= SWING_MIN_MOVE:
                    d, ext = 1, v
                elif ext - v >= SWING_MIN_MOVE:
                    d, ext = -1, v
            elif d == 1:
                if v > ext:
                    ext = v
                elif ext - v >= SWING_MIN_MOVE:
                    swings, d, ext = swings + 1, -1, v
            else:
                if v < ext:
                    ext = v
                elif v - ext >= SWING_MIN_MOVE:
                    swings, d, ext = swings + 1, 1, v
        txt = f"{swings} swings, was {peak * 100:.0f}c {now_t - tp:.0f}s ago, now {cur * 100:.0f}c"
        return swings >= SWING_MIN_REVERSALS and peak - cur >= SCALP_TARGET, txt

    def update_regime(self, m, now_t):
        """Classify the market as CHOPPY or TRENDING from how the Kalshi price has moved."""
        tk = m["ticker"]
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        if not (0 < yb <= ya < 1):
            return
        mid = (ya + yb) / 2
        if not self.mids or now_t - self.mids[-1][0] >= REGIME_STEP:
            self.mids.append((now_t, tk, mid))
        if mid >= DECIDED_PRICE or mid <= 1 - DECIDED_PRICE:     # one side priced 88%+: the round is decided
            self.cur_regime = ("DECIDED", "UP" if mid >= 0.5 else "DOWN", 0.0, 0.0)
            return
        pts = [x[2] for x in self.mids if x[1] == tk and x[0] >= now_t - REGIME_WINDOW]
        if len(pts) < 8:
            self.cur_regime = ("WARMING", None, 0.0, 0.0)
            return
        path = sum(abs(b2 - a2) for a2, b2 in zip(pts, pts[1:]))
        net = pts[-1] - pts[0]
        er = abs(net) / path if path > 0 else 0.0
        if abs(net) >= TREND_MIN_NET and er >= TREND_MIN_ER:
            new = ("TRENDING", "UP" if net > 0 else "DOWN", net, er)
        elif path >= CHOP_MIN_PATH and er <= CHOP_MAX_ER:
            new = ("CHOPPY", None, net, er)
        else:
            new = ("MIXED", None, net, er)
        old = self.cur_regime
        self.cur_regime = new
        changed = (old[0], old[1]) != (new[0], new[1])
        secs = parse_time(m["close_time"]).timestamp() - now_t
        if changed and new[0] in ("CHOPPY", "TRENDING") and secs > SCALP_MIN_SECS \
                and now_t - self.last_regime_alert >= 60:
            self.last_regime_alert = now_t
            if new[0] == "CHOPPY":
                txt = ("Price is swinging up and down with no clear direction. This is NOT an entry signal. "
                       "Only buy if you get a \u26A1 ENTER alert, which is sent only when price, time and edge all pass.")
            else:
                txt = (f"Price is moving steadily {new[1]}. Hold with the trend, take profit on target, and do NOT "
                       f"buy the cheap side against it.")
            notify(f"{self.regime_label()}", f"{txt}\n{mins(secs)} left.")
            print(f"[{stamp()}] REGIME {new[0]} {new[1] or ''} {tk}")

    def scalp_check(self, m, spot, sigma, now_t):
        """Send repeated ENTER alerts for the low-% side, plus a regular pulse. Alert only."""
        tk = m["ticker"]
        s = scalp_signal(m, spot, sigma, list(self.hist), now_t)
        if not s:
            return
        dot = "\U0001F7E2" if s["name"] == "UP" else "\U0001F534"
        lean_txt, lean_side, lean_conf = lean_tag(s["p_up"])
        prev = self.scalp_lean.get(tk)
        flips = prev[1] if prev else 0
        if prev and prev[0] != lean_side and lean_conf >= 0.60:
            flips += 1
            self.scalp_lean[tk] = (lean_side, flips)
            if s["secs"] > MAX_SECS:       # inside the last 4 minutes the main FLIP alert handles it
                notify(f"\U0001F504 {LABEL} FLIP", f"{lean_txt}\nFlipped {flips}x this window. {mins(s['secs'])} left.")
        elif not prev:
            self.scalp_lean[tk] = (lean_side, 0)
        rname, rdir = self.cur_regime[0], self.cur_regime[1]
        against = rname == "TRENDING" and rdir != s["name"]    # cheap side is against a steady trend
        swing_ok, swing_txt = self.swing_proof(tk, s["name"], now_t)
        fair_ok = s["p_side"] >= s["target"]          # model must value this side at/above the exit price
        enter = (s["enter"] and rname == "CHOPPY" and tk not in self.surged and swing_ok and fair_ok)
        lean_dot = "\U0001F7E2" if lean_side == "UP" else "\U0001F534"
        common = (f"Snipe: {self.snipe_label()}\nFlip risk: {1 - lean_conf:.0%} | flipped {flips}x\n"
                  f"Market: {self.regime_label()}\n"
                  f"\u2694\uFE0F Pressure: {self.press_line()}\n"
                  f"{mins(s['secs'])} left | spot ${spot:,.2f} vs strike ${float(m['floor_strike']):,.2f}")
        if enter and now_t - self.last_scalp.get(tk, 0) >= SCALP_COOLDOWN:
            self.last_scalp[tk] = now_t
            self.scalp_pos.setdefault(tk, {"name": s["name"], "cost": s["cost"], "target": s["target"]})
            rot = self.rotate_from.pop(tk, None)
            cents = f"{s['cost'] * 100:.0f}c"
            stop_c = max(0.01, s["cost"] - SCALP_STOP) * 100
            title = (f"\U0001F501 {LABEL} SCALP: BUY {s['name']} @ {cents} (rotate)" if rot and rot != s["name"]
                     else f"\u26A1 {LABEL} SCALP: BUY {s['name']} @ {cents}")
            rel = (f"This is AGAINST the main lean ({lean_side}). " if lean_side != s["name"]
                   else f"This is WITH the main lean ({lean_side}). ")
            body = (f"{rel}Small size, quick exit, stop at {stop_c:.0f}c.\n"
                    f"Win chance {s['p_side']:.0%} | edge {s['edge']:+.2f} | exit target {s['target'] * 100:.0f}c\n"
                    f"Main lean: {lean_txt}\n{common}")
            print(f"[{stamp()}] SCALP ENTER {body}")
            notify(title, body + f"\nSwing proof: {swing_txt}\n"
                   f"Evidence of a swing, NOT a guarantee. Alert only.")
        elif now_t - self.last_pulse.get(tk, 0) >= PULSE_SECS:
            self.last_pulse[tk] = now_t
            extra = ""
            if s["enter"] and not enter:
                if against:
                    extra = f"\nSteady {rdir} trend: this cheap side is against it, so no entry."
                elif tk in self.surged:
                    extra = "\nSurge this round: no scalp entries."
                elif not swing_ok:
                    extra = f"\nNo proven swing yet ({swing_txt}), so no entry."
                elif not fair_ok:
                    extra = "\nModel doesn't value this side up at the exit price, so no entry."
                else:
                    extra = "\nMarket isn't clearly choppy, so no entry."
            elif not s["enter"]:
                extra = "\nNo entry yet."
            # the lean goes first (title + first line) so the phone preview shows the favored side, not the cheap one
            notify(f"{LABEL} pulse | LEAN {lean_dot} {lean_side} {lean_conf:.0%}",
                   f"Lean: {lean_txt}\n{self.verdict_line()}\n{common}{extra}")

    def manage_position(self, m, now_t):
        """Track the open scalp (from the first ENTER alert) and say when to take profit, hold, cut or rotate."""
        tk = m["ticker"]
        pos = self.scalp_pos.get(tk)
        if not pos:
            return
        ya, yb = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars")
        if not (0 < yb <= ya < 1):
            return
        name, cost, target = pos["name"], pos["cost"], pos["target"]
        exit_bid = yb if name == "UP" else (num(m, "no_bid_dollars") or (1 - ya))
        other = "DOWN" if name == "UP" else "UP"
        other_cost = num(m, "no_ask_dollars") if name == "UP" else ya
        pnl = exit_bid - cost
        secs = parse_time(m["close_time"]).timestamp() - now_t
        rname, rdir = self.cur_regime[0], self.cur_regime[1]
        pos["peak"] = peak = max(pos.get("peak", cost), exit_bid, cost)
        drop_peak = peak - exit_bid
        side_mid = (ya + yb) / 2 if name == "UP" else 1 - (ya + yb) / 2
        past = [(mid if name == "UP" else 1 - mid) for t, k, mid in self.mids
                if k == tk and FLIP_FAST_SECS <= now_t - t <= FLIP_FAST_SECS + 15]
        fast_drop = (past[-1] - side_mid) if past else 0.0
        stop_price = max(0.01, cost - SCALP_STOP)
        flipping = drop_peak >= FLIP_WARN_PEAK_DROP or fast_drop >= FLIP_WARN_FAST_DROP
        if flipping or pnl <= -0.05:
            danger = "\U0001F534 HIGH"
        elif pnl < 0 or drop_peak >= 0.03:
            danger = "\U0001F7E1 MEDIUM"
        else:
            danger = "\U0001F7E2 LOW"
        if exit_bid >= target:
            if rname == "CHOPPY":
                adv = (f"Choppy market: the {other} side is now {other_cost * 100:.0f}c. Watch for a ROTATE alert "
                       f"to scalp it back the other way.")
                self.rotate_from[tk] = name
            elif rname == "TRENDING" and rdir == name:
                adv = f"Steady {name} trend, so it could run further, but profit is in hand. Take it, or hold with care."
            else:
                adv = "Take it. Don't chase more."
            rec_txt = self.ledger.record_scalp(tk, True, "take_profit")
            notify(f"\U0001F4B0 {LABEL} TAKE PROFIT: SELL {name} now",
                   f"Exit ~{exit_bid * 100:.0f}c vs entry {cost * 100:.0f}c ({pnl * 100:+.0f}c per contract).\n{adv}\n"
                   f"{mins(secs)} left. Scalps: {rec_txt}. Alert only.")
            print(f"[{stamp()}] TAKE PROFIT {name} {tk} exit={exit_bid:.2f} entry={cost:.2f}")
            self.scalp_pos.pop(tk, None)
            return
        if pnl <= -SCALP_STOP:
            rec_txt = self.ledger.record_scalp(tk, False, "cut")
            notify(f"\U0001F6D1 {LABEL} CUT: SELL {name} (going against you)",
                   f"Exit ~{exit_bid * 100:.0f}c vs entry {cost * 100:.0f}c ({pnl * 100:+.0f}c per contract).\n"
                   f"Market: {self.regime_label()}. Consider cutting the loss. Scalps: {rec_txt}. Alert only.")
            print(f"[{stamp()}] CUT {name} {tk} exit={exit_bid:.2f} entry={cost:.2f}")
            self.scalp_pos.pop(tk, None)
            return
        if flipping and tk not in self.warn_sent:
            self.warn_sent.add(tk)
            how = (f"fell {fast_drop * 100:.0f}c in the last {FLIP_FAST_SECS}s" if fast_drop >= FLIP_WARN_FAST_DROP
                   else f"fell {drop_peak * 100:.0f}c from its high of {peak * 100:.0f}c")
            keep = " You are still in profit, so consider locking it in." if pnl > 0 else ""
            notify(f"\u26A0\uFE0F {LABEL} FLIP WARNING: {name} is falling",
                   f"{name} {how}, now ~{exit_bid * 100:.0f}c (entry {cost * 100:.0f}c, {pnl * 100:+.0f}c). "
                   f"The market may be flipping to {other} ({other_cost * 100:.0f}c).{keep}\n"
                   f"Snipe: {self.snipe_label()}\n"
                   f"\u2694\uFE0F Pressure: {self.press_line()}\n"
                   f"Consider exiting now to protect your money. Stop level: {stop_price * 100:.0f}c. "
                   f"{mins(secs)} left. Alert only.")
            print(f"[{stamp()}] FLIP WARNING {name} {tk} exit={exit_bid:.2f} peak={peak:.2f}")
        elif not flipping and tk in self.warn_sent and drop_peak < 0.02:
            self.warn_sent.discard(tk)            # it recovered: allow a fresh warning later
        if secs <= END_WARN_SECS and tk not in self.end_sent:
            self.end_sent.add(tk)
            notify(f"\u23F1\uFE0F {LABEL} ENDING SOON: {name} still open",
                   f"{mins(secs)} left. Sell now at ~{exit_bid * 100:.0f}c, or hold to settlement "
                   f"(pays 100c if {name} wins, 0 if not).")
            return
        if now_t - self.last_hold.get(tk, 0) >= HOLD_SECS:
            self.last_hold[tk] = now_t
            cp = self.cur_press or 0
            against_txt = "\nPressure is AGAINST your side." if (name == "DOWN" and cp >= 40) or (name == "UP" and cp <= -40) else ""
            sn = self.cur_snipe
            if sn and sn[0] >= SNIPE_WATCH and sn[1] != name:
                against_txt += "\n\U0001F6A8 SNIPE is AGAINST your side."
            if rname == "TRENDING" and rdir == name:
                why = f"Steady {name} trend is with you. Hold toward the target."
            elif rname == "TRENDING":
                why = f"Steady {rdir} trend is AGAINST you. Don't add; consider cutting if it keeps falling."
            elif rname == "CHOPPY":
                why = (f"Choppy market: a dip can bounce back or keep falling. Don't hold past the stop "
                       f"({stop_price * 100:.0f}c). You'll get a FLIP WARNING if it turns fast.")
            else:
                why = "No clear trend yet. Hold for the target."
            notify(f"\u270B {LABEL} HOLD {name}",
                   f"Now ~{exit_bid * 100:.0f}c vs entry {cost * 100:.0f}c ({pnl * 100:+.0f}c). "
                   f"Target {target * 100:.0f}c | Stop {stop_price * 100:.0f}c.\n"
                   f"Snipe: {self.snipe_label()}\n"
                   f"Danger: {danger}\n\u2694\uFE0F Pressure: {self.press_line()}{against_txt}\n{why}\n{mins(secs)} left.")

    def sit_out(self, m, reason):
        """Tell the group once per window that no call is coming yet, and why."""
        tk = m["ticker"]
        self.reason[tk] = reason
        secs = parse_time(m["close_time"]).timestamp() - time.time()
        if tk in self.called or tk in self.sat_out or not (MIN_SECS < secs <= MAX_SECS):
            return
        self.sat_out.add(tk)
        notify(f"\u23F8\uFE0F Kalshi {LABEL}: SITTING OUT (for now)",
               f"No call yet, {mins(secs)} left. Reason: {reason}.\n"
               f"Wait: a call will be sent if the data clears before the window ends.")

    def stats_line(self):
        return self.ledger.stats()

    def act(self, tk, a, tries):
        dot = "\U0001F7E2" if a["name"] == "UP" else "\U0001F534"
        tag = lean_tag(a["p_win"] if a["name"] == "UP" else 1 - a["p_win"])[0]
        desc = f"{dot} {a['name']} x{a['count']} @ ~{a['cost']:.2f} (edge {a['edge']:+.2f}) on {tk} | {tag}"
        live_ok, why = (True, "") if not (self.send and self.gated) else self.ledger.gate()
        if not self.send or not live_ok:
            mode_tag = "PAPER" if self.send else "DRY RUN"
            self._say("gate" + tk, f"{mode_tag}: {desc}" + ("" if live_ok else f" | gate closed: {why}"), every=60)
            self.ledger.add_trade(tk, a)
            self.traded.add(tk)
            self.save()
            notify(f"Kalshi {mode_tag} signal", desc)
            return
        res = self.api.place(tk, a["side"], a["price"], a["count"])
        try:
            filled = float(res.get("fill_count") or 0)
        except (TypeError, ValueError):
            filled = 0.0
        print(f"[{stamp()}] ORDER {desc} -> filled {res.get('fill_count')} of {a['count']}")
        log_line(CALIB_LOG, {"t": datetime.now(timezone.utc).isoformat(), "market": tk, "order": a, "response": res})
        if filled > 0:
            self.ledger.add_trade(tk, a)
            self.traded.add(tk)
            self.trades_today += 1
            try:
                self.refresh_balance()
            except Exception:
                pass
            notify("Kalshi order", f"{desc}\nFilled {res.get('fill_count')} of {a['count']}. Gate: {why or 'open'}")
        else:
            tries += 1
            self.attempts[tk] = (tries, time.time() + RETRY_SECS)
            if tries >= MAX_ATTEMPTS:
                self.traded.add(tk)
        self.save()

    def run(self):
        if not self.startup():
            return
        self.feeds.start()
        self.watch.start()
        while True:
            t0 = time.time()
            try:
                if self.tick():
                    return
            except Exception as e:
                print(f"[{stamp()}] error: {e}")
                if time.time() - self._err_alert > 900:
                    self._err_alert = time.time()
                    notify("Kalshi bot error", str(e)[:300])
            if self.once:
                return
            time.sleep(max(0.0, POLL_SECS - (time.time() - t0)))


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--demo", action="store_true")
    g.add_argument("--live", action="store_true")
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--stats", action="store_true")
    a = ap.parse_args()
    if a.stats:
        lg = Ledger(None)
        n, mean, se, bm, bk = lg.stats()
        ok, why = lg.gate()
        print(f"tracked trades: {n} | avg {mean * 100:+.2f}c/contract after fees (+/-{se * 100:.2f}c)")
        print(f"Brier: model {bm if bm is None else round(bm, 4)} vs market {bk if bk is None else round(bk, 4)}")
        oh, on = lg.open_stats()
        print(f"opening calls: {oh}/{on} correct")
        print(f"calls: {streak_text(lg.call_seq)}")
        print(f"scalps: {streak_text(lg.scalp_seq)}")
        print(f"live gate: {'OPEN' if ok else 'CLOSED'} ({why})")
        return
    key_id, key_path = os.environ.get("KALSHI_KEY_ID"), os.environ.get("KALSHI_KEY_PATH")
    key_text = os.environ.get("KALSHI_PRIVATE_KEY")
    if key_id and key_text and not key_path:
        key_path = "kalshi_key.pem"
        with open(key_path, "w") as f:
            f.write(key_text.replace("\\n", "\n").strip() + "\n")
        os.chmod(key_path, 0o600)
    if (a.demo or a.live) and not (key_id and key_path):
        raise SystemExit("Set KALSHI_KEY_ID and KALSHI_KEY_PATH first.")
    if a.live and input("LIVE mode places REAL orders (only while the proof gate is open). Type YES: ") != "YES":
        return
    api = Kalshi(PROD if not a.demo else DEMO, key_id, key_path)
    mode = "LIVE (gated)" if a.live else "DEMO" if a.demo else "DRY RUN (paper only)"
    print(f"Kalshi bot v3 ({SERIES}) | mode: {mode} | stake ${STAKE_USD:.2f}")
    if not a.once:
        notify("Kalshi bot v3 started", f"Mode: {mode}")
    try:
        Bot(api, send_orders=a.demo or a.live, gated=a.live, once=a.once).run()
    except KeyboardInterrupt:
        notify("Kalshi bot stopped", "Stopped manually.", block=True)
    except Exception as e:
        notify("Kalshi bot CRASHED", f"{type(e).__name__}: {str(e)[:300]}", block=True)
        raise
    finally:
        flush_alerts()


if __name__ == "__main__":
    main()
