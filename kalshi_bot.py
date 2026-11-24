#!/usr/bin/env python3
"""
Kalshi 15-minute Bitcoin (KXBTC15M) bot, v2: faster calls, better price model.

What it does
  Every second or so it reads the open 15-minute "BTC up or down" market, estimates the
  chance Bitcoin finishes above the strike, and trades only when that estimate beats
  Kalshi's price by a margin after fees.

What changed from v1
  Speed
    - Kept-alive HTTPS connections (no new TLS handshake on every call).
    - The market is found once per 15-minute window, then only its quote is refreshed.
    - Four exchanges are read in parallel with a short deadline; a slow one is skipped.
    - Balance is cached (refreshed every 30s and after fills) instead of fetched each loop.
    - Volatility refreshes in the background, never blocking a trade decision.
  Model ("indicator")
    - Spot = median of Coinbase, Kraken, Bitstamp and Gemini (closer to Kalshi's reference
      index than Coinbase alone). Outliers and disagreeing feeds are skipped.
    - Volatility = blend of EWMA (reacts fast) and plain 1-hour realized volatility.
    - Settlement averaging: if the market settles on a 60-second average, the last minute
      carries much less risk. Modeled via SETTLE_AVG_SECS (set 0 if it settles on one price).
    - Fat-tailed distribution (Student-t, 4 d.o.f.) instead of a normal curve.
    - Model probability is blended with the market's own mid price, so the bot only trades
      when it disagrees with the crowd by a real margin.
  Safety
    - A trade only counts if it actually filled; zero-fill attempts retry a few times.
    - Wide-spread books and disagreeing price feeds are skipped.
  Learning
    - After each window closes, logs model vs market accuracy (Brier score) to
      kalshi_calibration.jsonl so you can see whether the model has any edge.

Modes (safe by default)
  python kalshi_bot_v2.py            DRY RUN: reads markets, logs decisions, places NO orders
  python kalshi_bot_v2.py --demo     sends orders to Kalshi's DEMO environment (fake money)
  python kalshi_bot_v2.py --live     sends REAL orders (asks you to type YES first)
  python kalshi_bot_v2.py --once     run a single check and exit (works with any mode)

Setup
  pip install cryptography
  export KALSHI_KEY_ID="your-api-key-id"
  export KALSHI_KEY_PATH="/path/to/your/private-key.pem"
  (Demo and live use different accounts and different keys.)

Telegram alerts (optional)
  export TELEGRAM_TOKEN="your-bot-token"
  export TELEGRAM_CHAT_ID="your-chat-id"
  TELEGRAM_CHAT_ID can hold several chats separated by commas (e.g. a group and a person).
  Alerts: startup, signals (dry run), orders/fills, errors, loss limit, crash, heartbeat.

Always-on hosting (Railway/Render/VPS)
  Start command: python kalshi_bot_v2.py   (no --once). Set POLL_SECS=1 for 1-second checks.
  Instead of KALSHI_KEY_PATH you may set KALSHI_PRIVATE_KEY to the key's text.
  (If these are not set but NTFY_TOPIC is, alerts go through ntfy.sh instead.)

NOT financial advice. The model is simple and has no proven edge. Test in dry-run,
then demo, and use only money you can afford to lose. Read kalshi_calibration.jsonl
to see whether the model actually beats the market.
"""
import argparse
import base64
import http.client
import json
import math
import os
import statistics
import threading
import time
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor, wait
from datetime import datetime, timezone

PROD = "https://external-api.kalshi.com/trade-api/v2"
DEMO = "https://external-api.demo.kalshi.co/trade-api/v2"
# (label, Kalshi series, Coinbase product)
ASSETS = [
    ("BTC", "KXBTC15M", "BTC-USD"),
]
LABEL, SERIES, PRODUCT = ASSETS[0]   # v2 trades the first entry; spot feeds below are BTC-specific

# (host, path, parser) for each spot price feed. Median of the ones that answer is used.
SPOT_SOURCES = {
    "coinbase": ("api.exchange.coinbase.com", "/products/BTC-USD/ticker",
                 lambda d: float(d["price"])),
    "kraken": ("api.kraken.com", "/0/public/Ticker?pair=XBTUSD",
               lambda d: float(next(iter(d["result"].values()))["c"][0])),
    "bitstamp": ("www.bitstamp.net", "/api/v2/ticker/btcusd/",
                 lambda d: float(d["last"])),
    "gemini": ("api.gemini.com", "/v1/pubticker/btcusd",
               lambda d: float(d["last"])),
}

# ---- settings you can change ----
STAKE_USD = 5.0            # max spend per trade
MIN_EDGE = 0.06            # model chance must beat price + fee by 8 cents
MAX_EDGE = 0.30            # bigger "edges" are treated as model/data errors and skipped
MIN_PRICE = 0.05           # skip a side whose ask is below this (fees/model error dominate)
MAX_PRICE = 0.95           # skip a side whose ask is above this
PROB_FLOOR = 0.05          # model probability is clamped to [PROB_FLOOR, PROB_CAP]
PROB_CAP = 0.95            # keep MIN_PRICE/MAX_PRICE inside this range so a clamped model
                           # probability can never look like an edge against an extreme price
MODEL_WEIGHT = 0.7         # 1.0 = trust only the model, 0.0 = trust only the market mid
MAX_SPREAD = 0.08          # skip if yes_ask - yes_bid is wider than this (thin/stale book)
FEE_RATE = 0.07            # approx. taker fee = FEE_RATE * p * (1 - p) per contract; verify on Kalshi
BASIS_FRAC = 0.00017       # allowance for Coinbase spot differing from Kalshi's reference (about $15 on BTC at 90k)
SETTLE_AVG_SECS = 60       # seconds of averaging at settlement; 0 if it settles on one price.
                           # VERIFY in the market rules on Kalshi.
MAX_SOURCE_DISAGREE = 0.0015  # skip if exchange prices differ by more than 0.15%
MIN_SECS_LEFT = 120        # don't trade in the last 2 minutes
MAX_SECS_LEFT = 600        # don't trade in the first 5 minutes
MAX_TRADES_PER_DAY = 20
MAX_DAILY_LOSS_USD = 20.0  # stop trading if cash balance falls this far below the start
MAX_ATTEMPTS = 3           # tries per market if orders fill nothing
RETRY_SECS = 5             # wait between those tries
POLL_SECS = float(os.environ.get("POLL_SECS", "1"))  # seconds between checks; set POLL_SECS=1 for faster
SIGMA_REFRESH_SECS = 60    # recompute volatility this often (saves API calls)
EWMA_LAMBDA = 0.94         # volatility decay per minute
VOL_EWMA_WEIGHT = 0.6      # share of EWMA vs plain 1-hour realized vol
BALANCE_REFRESH_SECS = 30
LOG_EVERY_SECS = 15        # print a status line at most this often
TRADE_LOG = "kalshi_trades.jsonl"
CALIB_LOG = "kalshi_calibration.jsonl"
STATE_FILE = "kalshi_state.json"
HEARTBEAT_SECS = 1800      # "still alive" ping every 30 minutes
ERROR_ALERT_COOLDOWN = 900  # send the same kind of error alert at most every 15 minutes
CLOSED_STATES = {"closed", "settled", "finalized", "determined", "inactive"}


# ---------- fast HTTP (kept-alive connections, one per thread per host) ----------
_tls = threading.local()


def _conn(host):
    conns = getattr(_tls, "conns", None)
    if conns is None:
        conns = _tls.conns = {}
    c = conns.get(host)
    if c is None:
        c = conns[host] = http.client.HTTPSConnection(host, timeout=6)
    return c


def _drop(host):
    c = getattr(_tls, "conns", {}).pop(host, None)
    if c is not None:
        try:
            c.close()
        except Exception:
            pass


def request(host, method, path, headers=None, body=None):
    """JSON request. Retries once if a kept-alive connection went stale. The retry re-sends the
    identical body, so an order keeps its client_order_id and cannot be double-placed."""
    hdrs = {"User-Agent": "kalshi-bot/2.0", "Accept": "application/json"}
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
            sig = self.key.sign(
                msg,
                padding.PSS(mgf=padding.MGF1(hashes.SHA256()),
                            salt_length=padding.PSS.DIGEST_LENGTH),
                hashes.SHA256(),
            )
        return base64.b64encode(sig).decode()

    def call(self, method, endpoint, params=None, body=None):
        path = self.prefix + endpoint                      # signed path has no query string
        full = path + ("?" + urllib.parse.urlencode(params) if params else "")
        headers = {"Content-Type": "application/json"}
        if self.key:
            ts = str(int(time.time() * 1000))
            headers.update({
                "KALSHI-ACCESS-KEY": self.key_id,
                "KALSHI-ACCESS-TIMESTAMP": ts,
                "KALSHI-ACCESS-SIGNATURE": self._sign(ts, method, path),
            })
        data = json.dumps(body).encode() if body is not None else None
        return request(self.host, method, full, headers, data)

    def open_market(self, series):
        res = self.call("GET", "/markets", {"series_ticker": series, "status": "open", "limit": 20})
        now = datetime.now(timezone.utc)
        live = [m for m in res.get("markets", []) if parse_time(m["close_time"]) > now]
        live.sort(key=lambda m: m["close_time"])
        return live[0] if live else None

    def get_market(self, ticker):
        """Single-market quote refresh: much smaller and faster than listing markets."""
        return self.call("GET", f"/markets/{ticker}")["market"]

    def balance_usd(self):
        return self.call("GET", "/portfolio/balance")["balance"] / 100.0  # cents -> dollars

    def place(self, ticker, side, price, count):
        body = {
            "ticker": ticker,
            "side": side,                       # "bid" buys YES, "ask" sells YES
            "count": f"{count:.2f}",
            "price": f"{price:.4f}",
            "time_in_force": "immediate_or_cancel",
            "self_trade_prevention_type": "taker_at_cross",
            "client_order_id": str(uuid.uuid4()),
        }
        return self.call("POST", "/portfolio/events/orders", body=body)


# ---------- spot price ----------
_inflight = set()


def parse_time(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def _fetch_one(name):
    host, path, parse = SPOT_SOURCES[name]
    try:
        return parse(request(host, "GET", path))
    finally:
        _inflight.discard(name)


def spot_quotes(spot_pool, wait_secs=3.0):
    """Ask every exchange in parallel; return whichever answered within wait_secs.
    A feed that is still stuck from the last round is skipped, not queued."""
    futs = {}
    for name in SPOT_SOURCES:
        if name in _inflight:
            continue
        _inflight.add(name)
        futs[spot_pool.submit(_fetch_one, name)] = name
    done, _ = wait(futs, timeout=wait_secs)
    out = {}
    for f in done:
        try:
            out[futs[f]] = f.result()
        except Exception:
            pass
    return out


def combine(quotes):
    """Median of the feeds, dropping outliers. Returns (spot, note) or (None, reason)."""
    vals = [v for v in quotes.values() if v and v > 0]
    if not vals:
        return None, "no spot data"
    med = statistics.median(vals)
    vals = [v for v in vals if abs(v - med) / med <= 0.005]
    spot = statistics.median(vals)
    if len(vals) > 1 and (max(vals) - min(vals)) / spot > MAX_SOURCE_DISAGREE:
        return None, f"exchange prices disagree ({min(vals):,.0f}-{max(vals):,.0f})"
    return spot, f"{len(vals)}/{len(SPOT_SOURCES)} feeds"


# ---------- volatility ----------
class Vol:
    """Std dev of 1-minute price changes in dollars (per sqrt-minute), refreshed in the background."""

    def __init__(self, pool):
        self.pool, self.val, self.t, self.busy = pool, None, 0.0, False

    def _refresh(self):
        try:
            rows = request("api.exchange.coinbase.com", "GET",
                           f"/products/{PRODUCT}/candles?granularity=60")
            closes = [r[4] for r in rows[:61]][::-1]            # oldest -> newest
            d = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
            if len(d) >= 10:
                n = len(d)
                w = [EWMA_LAMBDA ** (n - 1 - i) for i in range(n)]   # newest weight = 1
                ewma = math.sqrt(sum(wi * x * x for wi, x in zip(w, d)) / sum(w))
                rms = math.sqrt(sum(x * x for x in d) / n)
                self.val = VOL_EWMA_WEIGHT * ewma + (1 - VOL_EWMA_WEIGHT) * rms
        except Exception as e:
            print(f"[{stamp()}] volatility refresh failed: {e}")
        finally:
            self.busy = False

    def get(self, spot):
        if time.time() - self.t > SIGMA_REFRESH_SECS and not self.busy:
            self.t, self.busy = time.time(), True
            if self.val is None:
                self._refresh()                       # first load: wait for it
            else:
                self.pool.submit(self._refresh)       # later: never block a decision
        s = self.val if self.val is not None else 0.0008 * spot
        return min(max(s, 0.0003 * spot), 0.003 * spot)


# ---------- model ----------
def phi(z):
    """Normal CDF (v1 used this; v2 uses t4_cdf below, kept here for reference)."""
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def t4_cdf(x):
    """CDF of a Student-t with 4 degrees of freedom (closed form, no libraries)."""
    u = 1 + x * x / 4.0
    return 0.5 + 0.375 * (x / math.sqrt(u)) * (1 - (x * x / u) / 12.0)


def eff_minutes(secs):
    """Minutes of price variance left. If settlement averages the last w seconds, that last
    stretch adds only w/3 seconds of variance instead of w."""
    w = min(SETTLE_AVG_SECS, secs)
    return (secs - w + w / 3.0) / 60.0


def prob_up(spot, strike, secs_left, sigma):
    sd = math.sqrt(sigma ** 2 * eff_minutes(secs_left) + (BASIS_FRAC * spot) ** 2)
    z = (spot - strike) / sd
    # t4 has variance 2, so rescale z to unit variance before taking the CDF
    return min(PROB_CAP, max(PROB_FLOOR, t4_cdf(z * math.sqrt(2))))


def fee(p):
    return FEE_RATE * p * (1 - p)


def num(m, key):
    try:
        return float(m.get(key) or 0)
    except (TypeError, ValueError):
        return 0.0


def decide(m, spot, sigma, now):
    """Returns (action, info, snapshot). action is None or a dict describing the order;
    snapshot holds the model's numbers for the calibration log (None outside the window)."""
    strike = m.get("floor_strike")
    if strike is None:
        return None, "market has no strike; skipping", None
    strike = float(strike)
    secs = (parse_time(m["close_time"]) - now).total_seconds()
    if not (MIN_SECS_LEFT <= secs <= MAX_SECS_LEFT):
        return None, f"outside trading window ({secs:.0f}s left)", None
    p_model = prob_up(spot, strike, secs, sigma)
    ya, yb, na = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars"), num(m, "no_ask_dollars")
    mid = (ya + yb) / 2 if 0 < yb <= ya < 1 else None
    p = p_model if mid is None else MODEL_WEIGHT * p_model + (1 - MODEL_WEIGHT) * mid
    snap = {"spot": spot, "strike": strike, "secs_left": round(secs), "p_model": round(p_model, 4),
            "p_blend": round(p, 4), "mid": mid, "yes_ask": ya, "yes_bid": yb, "sigma": round(sigma, 2)}
    info = f"model={p_model:.0%} blend={p:.0%} mid={'n/a' if mid is None else f'{mid:.2f}'} ask={ya:.2f}/{na:.2f}"
    if ya > 0 and yb > 0 and ya - yb > MAX_SPREAD:
        return None, info + f" | spread {ya - yb:.2f} too wide", snap
    options = []
    # Only consider a side priced inside [MIN_PRICE, MAX_PRICE]: at extremes fees and model
    # error dominate and a clamped probability can fake an edge.
    if MIN_PRICE <= ya <= MAX_PRICE:
        options.append(("UP", "bid", ya, ya, p - ya - fee(ya)))
    if MIN_PRICE <= na <= MAX_PRICE and 0 < yb < 1:
        options.append(("DOWN", "ask", yb, na, (1 - p) - na - fee(na)))
    if not options:
        if 0 < ya < 1 or 0 < na < 1:
            return None, info + " | price too extreme, skipping", snap
        return None, info + " | no liquidity", snap
    name, side, order_price, cost, edge = max(options, key=lambda o: o[4])
    info += f" | best={name} edge={edge:+.2f}"
    if edge < MIN_EDGE:
        return None, info + " | no trade", snap
    if edge > MAX_EDGE:
        return None, info + " | edge too large, likely bad data; skipping", snap
    count = int(STAKE_USD // cost)
    if count < 1:
        return None, info + " | stake too small for one contract", snap
    return {"name": name, "side": side, "price": order_price, "count": count,
            "cost": cost, "edge": edge}, info, snap


# ---------- calibration: did the model beat the market? ----------
class Tracker:
    def __init__(self, api):
        self.api, self.snaps = api, {}
        self.n, self.b_model, self.b_mid = 0, 0.0, 0.0
        self.lock = threading.Lock()

    def record(self, ticker, snap):
        self.snaps[ticker] = snap            # last in-window snapshot = final forecast

    def finish(self, ticker):
        snap = self.snaps.pop(ticker, None)
        if snap:
            threading.Thread(target=self._settle, args=(ticker, snap), daemon=True).start()

    def _settle(self, ticker, snap):
        result = None
        for _ in range(16):
            time.sleep(15)
            try:
                result = self.api.get_market(ticker).get("result")
            except Exception:
                continue
            if result in ("yes", "no"):
                break
        else:
            return
        y = 1.0 if result == "yes" else 0.0
        mid = snap["mid"] if snap["mid"] is not None else 0.5
        with self.lock:
            self.n += 1
            self.b_model += (snap["p_model"] - y) ** 2
            self.b_mid += (mid - y) ** 2
            n, bm, bk = self.n, self.b_model / self.n, self.b_mid / self.n
        log_line(CALIB_LOG, {"t": datetime.now(timezone.utc).isoformat(), "market": ticker,
                             "result": result, **snap})
        print(f"[{stamp()}] settled {ticker}: {result.upper()} | model said {snap['p_model']:.0%}, "
              f"market said {mid:.0%} | Brier so far (lower is better): model {bm:.3f} vs market {bk:.3f} "
              f"over {n} windows")


# ---------- alerts, logs, state ----------
def log_line(path, rec):
    with open(path, "a") as f:
        f.write(json.dumps(rec) + "\n")


def stamp():
    return datetime.now().strftime("%H:%M:%S")


_last_alert = {}
_pending = []


def notify(title, message, key=None, cooldown=0, block=False):
    """Phone alert via Telegram (TELEGRAM_TOKEN + TELEGRAM_CHAT_ID, comma separated chats) or
    ntfy.sh (NTFY_TOPIC). Sent in the background so a slow network never delays trading.
    Call flush_alerts() before exiting. Never raises."""
    if key:
        if time.time() - _last_alert.get(key, 0) < cooldown:
            return
        _last_alert[key] = time.time()
    token, chat = os.environ.get("TELEGRAM_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    topic = os.environ.get("NTFY_TOPIC")

    def post(req):
        try:
            urllib.request.urlopen(req, timeout=10).close()
        except Exception as e:
            print(f"[{stamp()}] could not send alert: {e}")

    def send():
        if token and chat:
            for cid in [c.strip() for c in chat.split(",") if c.strip()]:
                body = json.dumps({"chat_id": cid, "text": f"{title}\n{message}"}).encode("utf-8")
                post(urllib.request.Request(
                    f"https://api.telegram.org/bot{token}/sendMessage", data=body,
                    headers={"Content-Type": "application/json", "User-Agent": "kalshi-bot/2.0"},
                    method="POST"))
        elif topic:
            post(urllib.request.Request(
                "https://ntfy.sh/" + urllib.parse.quote(topic), data=message.encode("utf-8"),
                headers={"Title": title, "Priority": "high", "User-Agent": "kalshi-bot/2.0"},
                method="POST"))

    if not (token and chat) and not topic:
        return
    if block:
        send()
    else:
        t = threading.Thread(target=send, daemon=True)
        t.start()
        _pending.append(t)


def flush_alerts(timeout=15):
    deadline = time.time() + timeout
    for t in _pending:
        t.join(max(0.0, deadline - time.time()))
    _pending.clear()


def load_state():
    try:
        with open(STATE_FILE) as f:
            return json.load(f)
    except Exception:
        return {}


def save_state(day, traded, trades_today, start_bal):
    with open(STATE_FILE, "w") as f:
        json.dump({"day": str(day), "traded": sorted(traded),
                   "trades_today": trades_today, "start_bal": start_bal}, f)


# ---------- the bot ----------
class Bot:
    def __init__(self, api, send_orders, once):
        self.api, self.send, self.once = api, send_orders, once
        self.pool = ThreadPoolExecutor(max_workers=3)
        self.spot_pool = ThreadPoolExecutor(max_workers=len(SPOT_SOURCES))
        self.vol = Vol(self.pool)
        self.tracker = Tracker(api)
        self.market = None
        self.attempts = {}                     # ticker -> (tries, next_try_time)
        self.last_log = 0.0
        self.last_heartbeat = time.time()
        self.bal, self.bal_t = None, 0.0

        self.day = datetime.now(timezone.utc).date()
        st = load_state()
        if st.get("day") != str(self.day):
            st = {"day": str(self.day), "traded": [], "trades_today": 0, "start_bal": None}
        self.traded = set(st["traded"])
        self.trades_today = st["trades_today"]
        self.start_bal = st["start_bal"]

    def refresh_balance(self):
        self.bal, self.bal_t = self.api.balance_usd(), time.time()
        return self.bal

    def save(self):
        save_state(self.day, self.traded, self.trades_today, self.start_bal)

    def startup(self):
        if self.api.key and self.start_bal is None:
            try:
                self.start_bal = self.refresh_balance()
                print(f"[{stamp()}] starting balance ${self.start_bal:,.2f}")
            except Exception as e:
                print(f"[{stamp()}] could not read balance: {e}")
        self.save()
        if self.send and self.start_bal is None:
            print("Refusing to send orders without a readable balance (needed for the loss limit).")
            notify("Kalshi bot NOT started", "Could not read balance, so orders are disabled. Check API key.")
            return False
        return True

    def tick(self):
        """One check. Returns True when the bot should stop."""
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
                notify("Kalshi bot STOPPED: daily loss limit",
                       f"Balance ${self.bal:,.2f} (started ${self.start_bal:,.2f}). No more trades today.")
                return True

        if not self.once and time.time() - self.last_heartbeat >= HEARTBEAT_SECS:
            self.last_heartbeat = time.time()
            msg = f"{self.trades_today} trades today"
            if self.bal is not None:
                msg += f", balance ${self.bal:,.2f}"
            notify("Kalshi bot alive", msg)

        # market quote and spot feeds are fetched at the same time
        now = datetime.now(timezone.utc)
        rediscover = self.market is None or parse_time(self.market["close_time"]) <= now
        if rediscover:
            f_mkt = self.pool.submit(self.api.open_market, SERIES)
        else:
            f_mkt = self.pool.submit(self.api.get_market, self.market["ticker"])
        quotes = spot_quotes(self.spot_pool)
        m = f_mkt.result(timeout=10)

        if m is not None and m.get("status") in CLOSED_STATES:
            m = None
        if self.market is not None and (m is None or m["ticker"] != self.market["ticker"]):
            self.tracker.finish(self.market["ticker"])
        self.market = m
        if m is None:
            print(f"[{stamp()}] {LABEL}: no open {SERIES} market found")
            return False

        spot, note = combine(quotes)
        if spot is None:
            print(f"[{stamp()}] {LABEL} {m['ticker']}: skipping, {note}")
            return False

        now = datetime.now(timezone.utc)
        action, info, snap = decide(m, spot, self.vol.get(spot), now)
        tk = m["ticker"]
        if snap:
            self.tracker.record(tk, snap)

        tries, next_try = self.attempts.get(tk, (0, 0.0))
        will_act = bool(action) and tk not in self.traded and self.trades_today < MAX_TRADES_PER_DAY \
            and time.time() >= next_try
        if will_act or time.time() - self.last_log >= LOG_EVERY_SECS:
            self.last_log = time.time()
            print(f"[{stamp()}] {LABEL} {tk} spot={spot:,.2f} ({note}) strike={m.get('floor_strike')} | {info}")
        if will_act:
            self.act(m, action, spot, now, tries)
        return False

    def act(self, m, action, spot, now, tries):
        tk = m["ticker"]
        desc = (f"{LABEL} {action['name']} x{action['count']} @ ~{action['cost']:.2f} "
                f"(edge {action['edge']:+.2f}) on {tk}")
        if not self.send:
            print(f"[{stamp()}] DRY RUN would place: {desc}")
            mins = (parse_time(m["close_time"]) - now).total_seconds() / 60
            kalshi_side = "YES (price goes UP)" if action["name"] == "UP" else "NO (price goes DOWN)"
            notify(f"Kalshi {LABEL} signal",
                   f"Buy {kalshi_side} on the 15-min {LABEL} market. "
                   f"Price about {action['cost'] * 100:.0f}c, model edge {action['edge'] * 100:+.0f}c. "
                   f"Closes in {mins:.0f} min. Check the live price in the Kalshi app first; "
                   f"this alert may be a few minutes old.")
            self.traded.add(tk)
            self.save()
            return
        res = self.api.place(tk, action["side"], action["price"], action["count"])
        try:
            filled = float(res.get("fill_count") or 0)
        except (TypeError, ValueError):
            filled = 0.0
        print(f"[{stamp()}] ORDER {desc} -> filled {res.get('fill_count')} "
              f"of {action['count']}, remaining {res.get('remaining_count')}")
        log_line(TRADE_LOG, {"t": now.isoformat(), "market": tk, "action": action,
                             "spot": spot, "response": res})
        if filled > 0:
            self.traded.add(tk)
            self.trades_today += 1
            try:
                self.refresh_balance()
            except Exception:
                pass
            notify(f"Kalshi {LABEL} order",
                   f"{desc}\nFilled {res.get('fill_count')} of {action['count']}, "
                   f"remaining {res.get('remaining_count')}. Trades today: {self.trades_today}")
        else:
            tries += 1
            self.attempts[tk] = (tries, time.time() + RETRY_SECS)
            if tries >= MAX_ATTEMPTS:
                self.traded.add(tk)             # give up on this window
                notify(f"Kalshi {LABEL} no fill", f"{desc}\nNothing filled after {tries} tries; skipping this window.")
        self.save()

    def run(self):
        if not self.startup():
            return
        while True:
            t0 = time.time()
            try:
                if self.tick():
                    return
            except Exception as e:
                print(f"[{stamp()}] {LABEL} error: {e}")
                notify(f"Kalshi {LABEL} error", str(e)[:300], key="err", cooldown=ERROR_ALERT_COOLDOWN)
            if self.once:
                return
            time.sleep(max(0.0, POLL_SECS - (time.time() - t0)))


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--demo", action="store_true", help="send orders to the DEMO environment")
    g.add_argument("--live", action="store_true", help="send REAL orders")
    ap.add_argument("--once", action="store_true", help="run one check and exit")
    a = ap.parse_args()

    key_id, key_path = os.environ.get("KALSHI_KEY_ID"), os.environ.get("KALSHI_KEY_PATH")
    key_text = os.environ.get("KALSHI_PRIVATE_KEY")
    if key_id and key_text and not key_path:
        key_path = "kalshi_key.pem"
        with open(key_path, "w") as f:
            f.write(key_text.replace("\\n", "\n").strip() + "\n")
        os.chmod(key_path, 0o600)
    if (a.demo or a.live) and not (key_id and key_path):
        raise SystemExit("Set KALSHI_KEY_ID and KALSHI_KEY_PATH first.")
    if a.live and input("LIVE mode places REAL orders. Type YES to continue: ") != "YES":
        return

    api = Kalshi(PROD if not a.demo else DEMO, key_id, key_path)
    mode = "LIVE" if a.live else "DEMO" if a.demo else "DRY RUN (no orders)"
    names = ", ".join(s for _, s, _ in ASSETS)
    print(f"Kalshi bot v2 ({names}) | mode: {mode} | stake ${STAKE_USD:.2f} | min edge {MIN_EDGE:.2f} | poll {POLL_SECS:g}s")
    if os.environ.get("GITHUB_EVENT_NAME") == "workflow_dispatch":
        notify("Kalshi bot test", f"Manual run worked. Telegram alerts are connected. Mode: {mode}")
    if not a.once:
        notify("Kalshi bot started", f"Mode: {mode} | stake ${STAKE_USD:.2f} | min edge {MIN_EDGE:.2f}")
    try:
        Bot(api, send_orders=a.demo or a.live, once=a.once).run()
    except KeyboardInterrupt:
        notify("Kalshi bot stopped", "Stopped manually (Ctrl+C).", block=True)
    except Exception as e:
        notify("Kalshi bot CRASHED", f"{type(e).__name__}: {str(e)[:300]}", block=True)
        raise
    finally:
        flush_alerts()


if __name__ == "__main__":
    main()
