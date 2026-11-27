"""
Kalshi BTC 15-minute (KXBTC15M) bot -- Railway edition (headless, paper-trading by default).

Signals blended into one probability: lognormal model (spot vs strike, realized vol, time
left), 60s momentum, order-book imbalance -- shrunk toward the market price. It only calls
when the market is trending (not chopping), the lean is stable, and conviction is high.
Every trade (paper or live) is tracked to settlement and logged to trades_v5.csv.

Railway variables:
  KALSHI_KEY_ID          your API key id
  KALSHI_PRIVATE_KEY     the full PEM private key text (never commit it to GitHub)
  KALSHI_DEMO=true       demo environment (default true)
  DRY_RUN=true           paper trades only, no orders sent (default true)
  PROFILE=SAFE           SAFE | BALANCED | COINFLIP
  DATA_DIR=/data         add a Railway Volume mounted at /data so history survives redeploys
Kill switch: create a file named STOP in DATA_DIR. Local dashboard: HEADLESS=false.
"""
import base64, csv, json, math, os, sys, time, uuid
from collections import deque
from datetime import datetime, timezone
from urllib.parse import urlparse

import requests
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding

# ---------------- config ----------------
HEADLESS = os.getenv("HEADLESS", "true").lower() == "true"   # true = clean log lines (Railway)
DATA_DIR = os.getenv("DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
DEMO = os.getenv("KALSHI_DEMO", "true").lower() == "true"
DRY_RUN = os.getenv("DRY_RUN", "true").lower() == "true"
PROFILE = os.getenv("PROFILE", "SAFE").upper()
BASE = ("https://demo-api.kalshi.co/trade-api/v2" if DEMO
        else "https://api.elections.kalshi.com/trade-api/v2")
SERIES = "KXBTC15M"

PROFILES = {
    #            min net edge, $/trade cap, Kelly frac, max open, loss stop $, shrink to mkt, min signals agreeing
    "SAFE":     dict(min_edge=0.09, stake=3,  kelly=0.10, max_open=1, loss_stop=15, shrink=0.35, min_agree=2, max_flip=70, min_conv=70, persist=45, min_z=0.9, max_cross=1),
    "BALANCED": dict(min_edge=0.06, stake=5,  kelly=0.15, max_open=2, loss_stop=25, shrink=0.25, min_agree=2, max_flip=85, min_conv=60, persist=30, min_z=0.6, max_cross=2),
    "COINFLIP": dict(min_edge=0.03, stake=15, kelly=0.35, max_open=3, loss_stop=50, shrink=0.10, min_agree=1, max_flip=100, min_conv=45, persist=10, min_z=0.3, max_cross=3),
}
PROF = PROFILES.get(PROFILE, PROFILES["BALANCED"])

MIN_SECS_LEFT, MAX_SECS_LEFT = 90, 780   # entry window (secs before close)
MIN_PRICE, MAX_PRICE = 0.12, 0.88
MAX_SPREAD = 0.06                       # wide bid/ask = poor fills
MAX_VOL_ANN = 1.5                        # skip if realized vol > 150% annualized
MAX_SPOT_DIVERGENCE = 0.001              # skip if Coinbase vs Kraken differ > 0.1%
POLL_SECS = 2
VOL_WINDOW_SECS = 600
CSV_PATH = os.path.join(DATA_DIR, "trades_v5.csv")
VIEW = os.getenv("VIEW", "simple").lower()   # simple (default) | full
MAX_TRADES_DAY = 12                          # hard cap on entries per day
LOSS_COOLDOWN_SECS = 900                     # pause after 2 losses in a row
STOP_FILE = os.path.join(DATA_DIR, "STOP")                           # create a file named STOP to halt new trades
MIN_PAPER_TRADES = 30                        # paper trades required before real-money mode

# ---------------- ANSI ----------------
G, R, Y, C, D, B, RST = ("\033[92m", "\033[91m", "\033[93m", "\033[96m",
                         "\033[90m", "\033[1m", "\033[0m")


def col(t, k): return f"{k}{t}{RST}"


if HEADLESS:                      # no color codes in Railway logs
    G = R = Y = C = D = B = RST = ""
def sgn_col(x, txt): return col(txt, G if x > 0 else R if x < 0 else Y)
def dot(ok): return col("●", G if ok else R)
def arrow(x, dead=0): return col("▲", G) if x > dead else col("▼", R) if x < -dead else col("■", Y)
def clamp(x, lo, hi): return max(lo, min(hi, x))


# ---------------- Kalshi client ----------------
class Kalshi:
    def __init__(self):
        self.key_id = os.environ["KALSHI_KEY_ID"]
        pem = os.getenv("KALSHI_PRIVATE_KEY")
        if pem:
            pem = pem.strip().strip('"').replace("\\n", "\n").encode()
        else:
            with open(os.environ["KALSHI_KEY_PATH"], "rb") as f:
                pem = f.read()
        self.pk = serialization.load_pem_private_key(pem, password=None)
        self.s = requests.Session()

    def _headers(self, method, url):
        ts = str(int(time.time() * 1000))
        msg = f"{ts}{method}{urlparse(url).path}".encode()  # no query string
        sig = self.pk.sign(msg, padding.PSS(mgf=padding.MGF1(hashes.SHA256()),
                                            salt_length=padding.PSS.DIGEST_LENGTH),
                           hashes.SHA256())
        return {"KALSHI-ACCESS-KEY": self.key_id, "KALSHI-ACCESS-TIMESTAMP": ts,
                "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode(),
                "Content-Type": "application/json"}

    def req(self, method, path, **kw):
        url = BASE + path
        r = self.s.request(method, url, headers=self._headers(method, url), timeout=10, **kw)
        r.raise_for_status()
        return r.json()

    def balance_usd(self): return self.req("GET", "/portfolio/balance")["balance"] / 100

    def open_markets(self):
        ms = self.req("GET", "/markets", params={"series_ticker": SERIES,
                                                 "status": "open", "limit": 5})["markets"]
        return sorted(ms, key=lambda m: m["close_time"])

    def market(self, ticker): return self.req("GET", f"/markets/{ticker}")["market"]

    def book_imbalance(self, ticker):
        """(yes_depth - no_depth)/(total) over top levels, in [-1, 1]. 0 if unavailable."""
        try:
            ob = self.req("GET", f"/markets/{ticker}/orderbook", params={"depth": 5}).get("orderbook") or {}
            y = sum(q for _, q in (ob.get("yes") or [])[-5:])
            n = sum(q for _, q in (ob.get("no") or [])[-5:])
            return (y - n) / (y + n) if (y + n) else 0.0
        except Exception:
            return 0.0

    def buy(self, ticker, side, count, price_cents):
        return self.req("POST", "/portfolio/orders", json={
            "ticker": ticker, "action": "buy", "side": side, "count": count,
            "type": "limit", "client_order_id": str(uuid.uuid4()),
            f"{side}_price": price_cents})


# ---------------- data / model ----------------
def get_spot():
    """Average of Coinbase + Kraken. Returns (avg, coinbase, kraken, divergence)."""
    cb = kr = None
    try:
        cb = float(requests.get("https://api.coinbase.com/v2/prices/BTC-USD/spot",
                                timeout=4).json()["data"]["amount"])
    except Exception:
        pass
    try:
        kr = float(requests.get("https://api.kraken.com/0/public/Ticker?pair=XBTUSD",
                                timeout=4).json()["result"]["XXBTZUSD"]["c"][0])
    except Exception:
        pass
    px = [p for p in (cb, kr) if p]
    if not px:
        raise RuntimeError("no spot price")
    div = abs(cb - kr) / min(cb, kr) if cb and kr else 0.0
    return sum(px) / len(px), cb, kr, div


class PriceBuf:
    def __init__(self): self.buf = deque()

    def add(self, t, p):
        self.buf.append((t, p))
        while self.buf and t - self.buf[0][0] > VOL_WINDOW_SECS:
            self.buf.popleft()

    def sigma(self):
        pts = list(self.buf)
        if len(pts) < 30: return None
        var, n = 0.0, 0
        for (t0, p0), (t1, p1) in zip(pts, pts[1:]):
            if t1 > t0:
                var += math.log(p1 / p0) ** 2 / (t1 - t0); n += 1
        return math.sqrt(var / n) if n else None

    def momentum(self, now, secs=60):
        """Fractional price change over last `secs` (0.001 = +0.1%)."""
        if len(self.buf) < 5: return 0.0
        old = next((p for t, p in self.buf if now - t <= secs), self.buf[0][1])
        return self.buf[-1][1] / old - 1

    def resampled(self, now, secs=300, step=15):
        out, last = [], None
        for t, p in self.buf:
            if now - t > secs: continue
            if last is None or t - last >= step:
                out.append(p); last = t
        return out

    def efficiency(self, now, secs=300):
        """Net move / total path over last `secs`. ~1 = clean trend, ~0 = sideways chop."""
        r = self.resampled(now, secs)
        if len(r) < 8: return None
        path = sum(abs(b - a) for a, b in zip(r, r[1:]))
        return abs(r[-1] - r[0]) / path if path else 0.0

    def crossings(self, strike, now, secs=300):
        """How many times price crossed the strike in the last `secs`."""
        r = self.resampled(now, secs)
        sd = [1 if p >= strike else -1 for p in r]
        return sum(1 for a, b in zip(sd, sd[1:]) if a != b)


def norm_cdf(x): return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def prob_up(spot, strike, secs, sigma):
    sigma = max(sigma, 0.00002)
    return norm_cdf(math.log(spot / strike) / (sigma * math.sqrt(max(secs, 1))))


def fee_per_contract(p): return 0.07 * p * (1 - p)


def settle_pnl(side, result, count, ask):
    fee = math.ceil(0.07 * count * ask * (1 - ask) * 100) / 100
    won = side == result
    return (count * (1 - ask) if won else -count * ask) - fee, won


def parse_close(m): return datetime.fromisoformat(m["close_time"].replace("Z", "+00:00"))


# ---------------- analysis ----------------
def analyze(m, spot, sigma, mom, imb, now, ctx=None):
    ctx = ctx or {}
    strike = float(m["floor_strike"])
    secs = (parse_close(m) - now).total_seconds()
    p_model = prob_up(spot, strike, secs, sigma)
    raw = clamp(p_model + clamp(mom * 20, -0.03, 0.03) + 0.03 * imb, 0.02, 0.98)
    ya, na = m["yes_ask"] / 100, m["no_ask"] / 100
    yb = (m.get("yes_bid") or 0) / 100
    mid = (ya + yb) / 2 if yb else ya
    p = (1 - PROF["shrink"]) * raw + PROF["shrink"] * mid
    sides = {s: dict(p=pp, ask=ask, edge=pp - ask - fee_per_contract(ask))
             for s, pp, ask in (("yes", p, ya), ("no", 1 - p, na))}
    sig = {"model": 1 if p_model > 0.52 else -1 if p_model < 0.48 else 0,
           "mom": 1 if mom > 0.0002 else -1 if mom < -0.0002 else 0,
           "book": 1 if imb > 0.1 else -1 if imb < -0.1 else 0}
    agree = {"yes": sum(v == 1 for v in sig.values()), "no": sum(v == -1 for v in sig.values())}
    flip = 1 - abs(p - 0.5) * 2          # 1.0 = pure coin flip, 0.0 = decisive
    spread = (ya - yb) if yb else None
    z = math.log(spot / strike) / (max(sigma, 0.00002) * math.sqrt(max(secs, 1)))
    return dict(er=ctx.get("er"), cross=ctx.get("cross", 0), swing=ctx.get("swing", 0.0), z=z,
                flip=flip, spread=spread, strike=strike, secs=secs, dist=spot - strike, dist_pct=spot / strike - 1,
                p_model=p_model, p=p, sides=sides, sig=sig, agree=agree, imb=imb)


def add_conviction(a):
    """0-100 score for the leaning side. Needs to clear the profile's min_conv."""
    lean = a["lean"]
    d = a["sides"][lean]
    parts = {
        "edge": min(max(d["edge"], 0) / 0.15, 1) * 25,
        "decisive": min((1 - a["flip"]) / 0.5, 1) * 20,
        "agree": a["agree"][lean] / 3 * 15,
        "trend": min((a["er"] or 0) / 0.5, 1) * 15,
        "persist": min(a["persist"] / 60, 1) * 10,
        "no_chop": (1 - min(a["cross"] / 3, 1)) * 10,
        "calm": (1 - min(a["swing"] / 0.20, 1)) * 5,
    }
    a["conv"] = sum(parts.values())
    a["conv_parts"] = parts


def check_gates(a, ticker, open_pos, traded, div, sigma, pnl):
    """List of (ok, label, detail). Any failed gate => WAIT."""
    g = []
    g.append((sigma is not None, "Vol data", "warming up, need ~1 min of prices"))
    ann = sigma * math.sqrt(31536000) if sigma else 0
    g.append((ann <= MAX_VOL_ANN, "Volatility", f"spike {ann*100:.0f}% ann (> {MAX_VOL_ANN*100:.0f}%)"))
    s = a["secs"]
    if s > MAX_SECS_LEFT:
        g.append((False, "Timing", f"too early, entry opens in {int(s - MAX_SECS_LEFT)}s"))
    elif s < MIN_SECS_LEFT:
        g.append((False, "Timing", "too close to close, wait for next window"))
    else:
        g.append((True, "Timing", "inside entry window"))
    g.append((a["flip"] * 100 <= PROF["max_flip"], "Coin-flip risk",
              f"{a['flip']*100:.0f}% (max {PROF['max_flip']}%), too close to 50/50"))
    g.append((a["spread"] is None or a["spread"] <= MAX_SPREAD, "Spread",
              f"{(a['spread'] or 0)*100:.0f}c wide (max {MAX_SPREAD*100:.0f}c)"))
    g.append((div <= MAX_SPOT_DIVERGENCE, "Price feeds", "Coinbase and Kraken disagree"))
    er = a["er"]
    g.append((er is not None, "Regime", "need ~2 min of price history"))
    if er is not None:
        g.append((er >= 0.20, "Regime", f"CHOP: price going sideways (efficiency {er:.2f})"))
    g.append((a["cross"] <= PROF["max_cross"], "Strike crosses",
              f"price crossed strike {a['cross']}x in 5 min (max {PROF['max_cross']})"))
    g.append((a["swing"] <= 0.15, "Market whipsaw", f"YES price swung {a['swing']*100:.0f}c in 2 min"))
    g.append((a["lean_flips"] <= 1, "Lean flips", f"direction flipped {a['lean_flips']}x in 3 min"))
    g.append((a["persist"] >= PROF["persist"], "Persistence",
              f"{a['lean'].upper()} lean only {a['persist']:.0f}s old (need {PROF['persist']}s)"))
    g.append((abs(a["z"]) >= PROF["min_z"], "Distance",
              f"only {abs(a['z']):.2f} sigma from strike (need {PROF['min_z']})"))
    g.append((a["conv"] >= PROF["min_conv"], "Conviction",
              f"{a['conv']:.0f}/100 (need {PROF['min_conv']})"))
    g.append((ticker not in traded, "Window", "already traded this window"))
    g.append((len(open_pos) < PROF["max_open"], "Positions", "max open positions reached"))
    g.append((pnl > -PROF["loss_stop"], "Loss stop", "daily loss limit hit"))
    return g


def decide(a, ticker, open_pos, traded, div, sigma, pnl):
    """Returns (side|None, reason, status, failed_reasons). status: TRADE | WATCH | WAIT."""
    gates = check_gates(a, ticker, open_pos, traded, div, sigma, pnl)
    fails = [f"{lbl}: {det}" for ok, lbl, det in gates if not ok]
    if fails:
        return None, fails[0], "WAIT", fails
    best = None
    for s, d in a["sides"].items():
        if not (MIN_PRICE <= d["ask"] <= MAX_PRICE): continue
        if d["edge"] < PROF["min_edge"]: continue
        if a["agree"][s] < PROF["min_agree"]: continue
        if best is None or d["edge"] > a["sides"][best]["edge"]: best = s
    if best and best != a["lean"]:
        return None, f"edge on {best.upper()} conflicts with {a['lean'].upper()} lean, no call", "WATCH", []
    if best:
        return best, f"CALL {best.upper()}: conviction {a['conv']:.0f}/100", "TRADE", []
    return None, "conditions OK but no edge yet, watching", "WATCH", []


def flip_bar(flip, width=10):
    n = int(round(flip * width))
    k = R if flip * 100 >= 85 else Y if flip * 100 >= 60 else G
    return col("█" * n + "░" * (width - n), k)


# ---------------- bot ----------------
class Bot:
    def __init__(self):
        self.k = Kalshi()
        self.pb = PriceBuf()
        self.start_bal = self.k.balance_usd()
        self.bal = self.start_bal
        self.bal_t = time.time()
        self.open_pos, self.traded, self.done = [], set(), []
        self.pnl = 0.0
        self.events = deque(maxlen=6)
        self.qh, self.lean = {}, {}
        self.loss_streak, self.cooldown_until, self.trades_today = 0, 0.0, 0
        self.day = datetime.now().date()
        self.load_history()
        self.last_spot = None
        if not os.path.exists(CSV_PATH):
            with open(CSV_PATH, "w", newline="") as f:
                csv.writer(f).writerow(["time", "ticker", "side", "count", "ask", "model_p",
                                        "edge", "result", "won", "pnl", "mode", "conviction", "regime", "env"])

    def log(self, msg, k=Y):
        self.events.append(f"{D}{datetime.now():%H:%M:%S}{RST} {col(msg, k)}")
        if HEADLESS:
            seen = self.__dict__.setdefault("_seen", {})
            if time.time() - seen.get(msg, 0) > 30:      # don't spam repeated errors
                seen[msg] = time.time()
                print(f"{datetime.now():%Y-%m-%d %H:%M:%S} {msg}", flush=True)

    def load_history(self):
        """Reload past settled trades so the scorecard survives redeploys."""
        if not os.path.exists(CSV_PATH):
            return
        today = datetime.now().date().isoformat()
        try:
            with open(CSV_PATH) as f:
                for r in csv.DictReader(f):
                    pnl = float(r["pnl"])
                    self.done.append(dict(p=float(r["model_p"]), pnl=pnl,
                                          won=r["won"] == "True"))
                    if r["time"].startswith(today):
                        self.pnl += pnl
                        self.trades_today += 1
            self.log(f"Loaded {len(self.done)} past trades from {CSV_PATH}", Y)
        except Exception as e:
            self.log(f"Could not load history: {e}", R)

    def settle(self):
        now = datetime.now(timezone.utc)
        for pos in list(self.open_pos):
            if (now - pos["close"]).total_seconds() < 5: continue
            try:
                m = self.k.market(pos["ticker"])
            except Exception:
                continue
            if m.get("result") in ("yes", "no"):
                pnl, won = settle_pnl(pos["side"], m["result"], pos["count"], pos["ask"])
                pos.update(pnl=pnl, won=won, result=m["result"])
                self.pnl += pnl
                self.loss_streak = 0 if won else self.loss_streak + 1
                if self.loss_streak >= 2:
                    self.cooldown_until = time.time() + LOSS_COOLDOWN_SECS
                    self.loss_streak = 0
                    self.log("2 losses in a row: pausing new trades for 15 min", Y)
                self.open_pos.remove(pos); self.done.append(pos)
                self.log(f"SETTLED {pos['side'].upper()} x{pos['count']} -> "
                         f"{'WIN' if won else 'LOSS'} ${pnl:+.2f}", G if won else R)
                print("TRADE_RECORD " + json.dumps(dict(
                    ticker=pos["ticker"], side=pos["side"], count=pos["count"], ask=pos["ask"],
                    model_p=round(pos["p"], 4), result=m["result"], won=won, pnl=round(pos["pnl"], 2),
                    conv=round(pos.get("conv", 0)), mode="paper" if DRY_RUN else "live")), flush=True)
                with open(CSV_PATH, "a", newline="") as f:
                    csv.writer(f).writerow([datetime.now().isoformat(timespec="seconds"),
                                            pos["ticker"], pos["side"], pos["count"],
                                            pos["ask"], round(pos["p"], 4), round(pos["edge"], 4),
                                            m["result"], won, round(pnl, 2),
                                            "paper" if DRY_RUN else "live",
                                            round(pos.get("conv", 0)), pos.get("regime"),
                                            "demo" if DEMO else "prod"])

    def enter(self, m, a, side):
        d = a["sides"][side]
        bankroll = self.start_bal + self.pnl
        kelly = max(0.0, (d["p"] - d["ask"]) / (1 - d["ask"]))
        usd = min(PROF["stake"], bankroll * PROF["kelly"] * kelly)
        count = int(usd // d["ask"])
        if count < 1: return
        if not DRY_RUN:
            self.k.buy(m["ticker"], side, count, int(round(d["ask"] * 100)))
        self.traded.add(m["ticker"])
        self.trades_today += 1
        self.open_pos.append(dict(ticker=m["ticker"], side=side, count=count, ask=d["ask"],
                                  p=d["p"], edge=d["edge"], close=parse_close(m),
                                  conv=a["conv"], regime=a["regime"]))
        self.log(f"{'PAPER' if DRY_RUN else 'BUY'} {side.upper()} x{count} @ {d['ask']*100:.0f}c "
                 f"edge {d['edge']*100:+.1f}% conv {a['conv']:.0f}", C)

    def headless(self, spot, div, sigma, info):
        """One clean heartbeat line a minute (status changes and trades log separately)."""
        now = time.time()
        if now - self.__dict__.get("_hb", 0) < 60:
            return
        self._hb = now
        vol = "{:.0f}%".format(sigma * math.sqrt(31536000) * 100) if sigma else "warming"
        parts = [f"{m['ticker'][-12:]} {status} lean={a['lean']} conv={a['conv']:.0f} "
                 f"regime={a['regime']} ({why})" for m, a, side, why, status, fails in info]
        print(f"{datetime.now():%Y-%m-%d %H:%M:%S} HEARTBEAT BTC ${spot:,.0f} vol {vol} "
              f"feed_gap {div*100:.3f}% | " + " || ".join(parts or ["no open market"])
              + f" | open {len(self.open_pos)} today ${self.pnl:+.2f}", flush=True)
        if now - self.__dict__.get("_sc", 0) > 600:
            self._sc = now
            print(f"{datetime.now():%Y-%m-%d %H:%M:%S} SCORECARD " + " | ".join(self.scorecard()),
                  flush=True)

    def bot_gates(self, side, why, status, fails):
        """Bot-level safety rails: kill switch, loss cooldown, daily trade cap."""
        now = time.time()
        if datetime.now().date() != self.day:
            self.day, self.trades_today = datetime.now().date(), 0
        block = None
        if os.path.exists(STOP_FILE):
            block = "Kill switch: STOP file found, delete it to resume"
        elif now < self.cooldown_until:
            block = f"Cooldown after 2 losses in a row ({int(self.cooldown_until - now)}s left)"
        elif self.trades_today >= MAX_TRADES_DAY:
            block = f"Daily trade cap reached ({MAX_TRADES_DAY})"
        if block:
            return None, block, "WAIT", [block] + fails
        return side, why, status, fails

    def scorecard(self):
        """Honest running report: is the edge real, and is the model overconfident?"""
        n = len(self.done)
        w = sum(1 for p in self.done if p["won"])
        lines = [f"Trades today {self.trades_today}/{MAX_TRADES_DAY}"]
        if n == 0:
            lines.append(col("Scorecard: no settled trades yet", Y))
            return lines
        tot = sum(p["pnl"] for p in self.done)
        wr = w / n
        avg_p = sum(p["p"] for p in self.done) / n
        lines.append(f"Predicted win {avg_p*100:.0f}% vs actual {wr*100:.0f}%   "
                     f"total ${tot:+.2f}  avg ${tot / n:+.2f}/trade")
        if n < 20:
            lines.append(col(f"Edge NOT PROVEN yet ({n}/20 trades)", Y))
        elif tot > 0 and wr >= avg_p - 0.05:
            lines.append(col("Edge looks real so far (keep paper trading to confirm)", G))
        else:
            lines.append(col("No proven edge: do NOT go live", R))
        if n >= 20 and wr < avg_p - 0.10:
            lines.append(col("Model is overconfident: raise the edge threshold", Y))
        return lines

    def read_market(self, m, spot, sigma, mom, imb, now):
        """Build the full 'market read': regime, whipsaw, lean persistence, conviction."""
        t = time.time()
        strike = float(m["floor_strike"])
        ya = m["yes_ask"] / 100
        yb = (m.get("yes_bid") or 0) / 100
        mid = (ya + yb) / 2 if yb else ya
        h = self.qh.setdefault(m["ticker"], deque())
        h.append((t, mid))
        while h and t - h[0][0] > 120: h.popleft()
        swing = max(x for _, x in h) - min(x for _, x in h)
        ctx = dict(er=self.pb.efficiency(t), cross=self.pb.crossings(strike, t), swing=swing)
        a = analyze(m, spot, sigma or 0.0001, mom, imb, now, ctx)
        st = self.lean.get(m["ticker"])
        side = "yes" if a["p"] >= 0.5 else "no"
        if st is not None and abs(a["p"] - 0.5) < 0.02:
            side = st["side"]                      # deadband: don't flip on noise
        if st is None:
            st = self.lean[m["ticker"]] = dict(side=side, since=t, flips=deque())
        elif st["side"] != side:
            st["side"], st["since"] = side, t
            st["flips"].append(t)
        while st["flips"] and t - st["flips"][0] > 180: st["flips"].popleft()
        a.update(lean=side, persist=t - st["since"], lean_flips=len(st["flips"]))
        er = a["er"]
        a["regime"] = ("WARMING" if er is None else "CHOP" if er < 0.20
                       else "TREND" if er >= 0.35 else "MIXED")
        add_conviction(a)
        return a

    def banner(self, info):
        if not info:
            return col("█ WAIT ", R) + " no open market yet"
        for m, a, side, why, status, fails in info:
            if status == "TRADE":
                return (col(f"█ CALL: BUY {side.upper()} ", G)
                        + f"conviction {a['conv']:.0f}/100, edge {a['sides'][side]['edge']*100:+.1f}%")
        for m, a, side, why, status, fails in info:
            if status == "WATCH":
                return col("█ WATCHING ", Y) + "good conditions, waiting for an edge"
        fails = info[0][5]
        extra = f" (+{len(fails)-1} more)" if len(fails) > 1 else ""
        return col("█ NOT A GOOD TIME, WAIT ", R) + f"{fails[0]}{extra}"

    def render(self, spot, cb, kr, div, sigma, mom, markets_info):
        w = sum(1 for p in self.done if p["won"]); n = len(self.done)
        out = ["\033[H\033[J"]
        mode = col("PAPER", Y) if DRY_RUN else col("LIVE $$", R)
        env = col("DEMO", Y) if DEMO else col("PROD", R)
        out.append(f"{B}KALSHI BTC-15M BOT{RST}  {mode} {env}  profile={col(PROFILE, C)}")
        out.append("─" * 62)
        out.append(self.banner(markets_info))
        out.append("─" * 62)
        cb_t = "{:,.0f}".format(cb) if cb else "n/a"
        kr_t = "{:,.0f}".format(kr) if kr else "n/a"
        out.append(f"BTC {B}${spot:,.2f}{RST}  CB {cb_t}  "
                   f"KR {kr_t}  feed {dot(div <= MAX_SPOT_DIVERGENCE)} "
                   f"({div*100:.3f}% apart)")
        vol_txt = f"{sigma*math.sqrt(31536000)*100:.0f}% ann" if sigma else "warming up..."
        mom_txt = "{:+.3f}%".format(mom * 100)
        out.append(f"Vol {vol_txt}   Mom60s {sgn_col(mom, mom_txt)} {arrow(mom, 0.0002)}")
        out.append("─" * 62)
        for m, a, side, why, status, fails in markets_info:
            mm, ss = divmod(int(max(a['secs'], 0)), 60)
            if VIEW != "full":
                above = a["dist"] >= 0
                pos_t = col("ABOVE" if above else "BELOW", G if above else R)
                lean_t = col(a["lean"].upper(), G if a["lean"] == "yes" else R)
                cv_t = col("{:.0f}/100".format(a["conv"]), G if a["conv"] >= PROF["min_conv"] else R)
                dist_t = "${:,.0f}".format(abs(a["dist"]))
                out.append(f"{B}{m['ticker'][-14:]}{RST}  {mm:02d}:{ss:02d} left")
                out.append(f" BTC {pos_t} strike by {dist_t}   Lean {lean_t}   Conviction {cv_t}")
                if status == "TRADE":
                    out.append(" " + col(why, G))
                elif status == "WATCH":
                    out.append(" " + col(why, Y))
                else:
                    for fr in fails[:3]:
                        out.append(" " + col("- " + fr, R))
                out.append("")
                continue
            pos_txt = col("ABOVE strike", G) if a["dist"] >= 0 else col("BELOW strike", R)
            out.append(f"{B}{m['ticker']}{RST}  closes in {mm:02d}:{ss:02d}")
            dist_txt = "{:+,.0f}$".format(a["dist"])
            out.append(f" Strike ${a['strike']:,.2f}  {sgn_col(a['dist'], dist_txt)} "
                       f"({a['dist_pct']*100:+.3f}%)  {pos_txt}")
            for s in ("yes", "no"):
                d = a["sides"][s]
                ok = d["edge"] >= PROF["min_edge"]
                edge_txt = "{:+5.1f}%".format(d["edge"] * 100)
                out.append(f" {s.upper():3} ask {d['ask']*100:3.0f}c  model {d['p']*100:5.1f}%  "
                           f"edge {sgn_col(d['edge'], edge_txt)} {dot(ok)}  "
                           f"agree {a['agree'][s]}/3")
            sg = a["sig"]
            out.append(f" Signals: model {arrow(sg['model'])}  mom {arrow(sg['mom'])}  "
                       f"book {arrow(sg['book'])} ({a['imb']:+.2f})  raw model {a['p_model']*100:.1f}%")
            rk = {"TREND": G, "CHOP": R, "MIXED": Y, "WARMING": Y}[a["regime"]]
            er_t = "n/a" if a["er"] is None else "{:.2f}".format(a["er"])
            reg_t = col(a["regime"], rk)
            out.append(f" Regime {reg_t}  eff {er_t}  strike-crosses {a['cross']}  "
                       f"YES swing {a['swing']*100:.0f}c/2m")
            ln_ok = a["persist"] >= PROF["persist"] and a["lean_flips"] <= 1
            lean_t = col(a["lean"].upper(), G if a["lean"] == "yes" else R)
            out.append(f" Lean {lean_t} held {a['persist']:.0f}s  flips {a['lean_flips']}  "
                       f"z {a['z']:+.2f}  {dot(ln_ok)}")
            cv_k = G if a["conv"] >= PROF["min_conv"] else R
            nb = max(0, min(10, int(round(a["conv"] / 10))))
            cv_t = col("{:.0f}/100".format(a["conv"]), cv_k)
            cv_bar = col("█" * nb + "░" * (10 - nb), cv_k)
            out.append(f" Conviction {cv_t} {cv_bar} {D}need {PROF['min_conv']}{RST}")
            fk = R if a["flip"] * 100 >= 85 else Y if a["flip"] * 100 >= 60 else G
            lbl = "very likely a coin flip" if fk == R else "uncertain" if fk == Y else "clear lean"
            flip_txt = "{:.0f}%".format(a["flip"] * 100)
            out.append(f" Coin-flip risk {col(flip_txt, fk)} "
                       f"{flip_bar(a['flip'])} {D}{lbl}{RST}")
            if status == "TRADE":
                act = col(f"BUY {side.upper()}", G)
            elif status == "WATCH":
                act = col("WATCH", Y)
            else:
                act = col("WAIT", R)
            out.append(f" Decision: {act}  {D}{why}{RST}")
            out.append("")
        out.append("─" * 62)
        wr = f"{w/n*100:.0f}%" if n else "n/a"
        pnl_txt = "${:+.2f}".format(self.pnl)
        out.append(f"Session P&L {sgn_col(self.pnl, pnl_txt)}  "
                   f"W/L {col(w, G)}/{col(n-w, R)}  win rate {wr}  "
                   f"open {len(self.open_pos)}/{PROF['max_open']}  "
                   f"bal ${self.bal:,.2f}")
        out.append(f"Loss stop: -${PROF['loss_stop']}   "
                   f"{dot(self.pnl > -PROF['loss_stop'])} within limit")
        out.extend(self.scorecard())
        for p in self.open_pos:
            out.append(f" {col('OPEN', C)} {p['side'].upper()} x{p['count']} @ {p['ask']*100:.0f}c "
                       f"({p['ticker'][-12:]})")
        out.append("─" * 62)
        out.extend(self.events)
        print("\n".join(out), flush=True)

    def run(self):
        while True:
            try:
                now = datetime.now(timezone.utc)
                spot, cb, kr, div = get_spot()
                self.pb.add(time.time(), spot)
                sigma, mom = self.pb.sigma(), self.pb.momentum(time.time())
                if time.time() - self.bal_t > 60:
                    try: self.bal = self.k.balance_usd(); self.bal_t = time.time()
                    except Exception: pass
                self.settle()

                if self.pnl <= -PROF["loss_stop"]:
                    self.log("LOSS STOP HIT -- no new trades", R)
                info = []
                if True:
                    for m in self.k.open_markets()[:2]:
                        if m.get("floor_strike") is None: continue
                        a = self.read_market(m, spot, sigma, mom, self.k.book_imbalance(m["ticker"]), now)
                        side, why, status, fails = decide(a, m["ticker"], self.open_pos,
                                                          self.traded, div, sigma, self.pnl)
                        side, why, status, fails = self.bot_gates(side, why, status, fails)
                        if side: self.enter(m, a, side)
                        info.append((m, a, side, why, status, fails))
                top = info[0][4] if info else "WAIT"
                if top != getattr(self, "last_status", None):
                    self.last_status = top
                    reason = info[0][3] if info else "no market"
                    self.log(f"Status -> {top}: {reason}",
                             G if top == "TRADE" else Y if top == "WATCH" else R)
                if HEADLESS:
                    self.headless(spot, div, sigma, info)
                else:
                    self.render(spot, cb, kr, div, sigma, mom, info)
            except KeyboardInterrupt:
                raise
            except requests.RequestException as e:
                self.log(f"API/network: {e}", R)
            except Exception as e:
                self.log(f"error: {e}", R)
            time.sleep(POLL_SECS)


def paper_record():
    """(settled non-prod trades, total pnl) from the CSV log."""
    n, pnl = 0, 0.0
    try:
        with open(CSV_PATH) as f:
            for r in csv.DictReader(f):
                if r.get("env") != "prod":
                    n += 1; pnl += float(r["pnl"])
    except Exception:
        pass
    return n, pnl


def preflight():
    """Startup self-check. Prints green/red checks and exits if something is wrong."""
    bad = []
    print(f"{B}Startup check{RST}  profile={PROFILE}  view={VIEW}")

    def chk(label, fn):
        try:
            print(f" {col('OK ', G)} {label}  {D}{fn()}{RST}")
        except Exception as e:
            bad.append(label)
            print(f" {col('FAIL', R)} {label}  {col(str(e)[:100], R)}")

    k = {}

    def c_key():
        if not (os.getenv("KALSHI_KEY_ID") and (os.getenv("KALSHI_PRIVATE_KEY")
                                                 or os.getenv("KALSHI_KEY_PATH"))):
            raise RuntimeError("set KALSHI_KEY_ID and KALSHI_PRIVATE_KEY")
        k["c"] = Kalshi()
        return "key loaded"
    chk("API key", c_key)
    if "c" in k:
        chk("Kalshi login", lambda: "balance ${:,.2f} ({})".format(
            k["c"].balance_usd(), "demo" if DEMO else "REAL MONEY"))

        def c_mkt():
            ms = k["c"].open_markets()
            if not ms: raise RuntimeError("no open KXBTC15M market found")
            if ms[0].get("floor_strike") is None:
                raise RuntimeError("market has no floor_strike, check Kalshi API docs")
            return f"{ms[0]['ticker']} strike {ms[0]['floor_strike']}"
        chk("Open BTC 15m market", c_mkt)
    chk("BTC price feeds", lambda: "${:,.0f}".format(get_spot()[0]))

    if not DRY_RUN and not DEMO:
        def c_gate():
            n, pnl = paper_record()
            if os.getenv("FORCE_LIVE") == "yes":
                return "FORCE_LIVE override on"
            if n < MIN_PAPER_TRADES or pnl <= 0:
                raise RuntimeError(f"real money locked: need {MIN_PAPER_TRADES}+ profitable "
                                   f"paper trades (have {n}, P&L ${pnl:+.2f})")
            return f"{n} paper trades, P&L ${pnl:+.2f}"
        chk("Real-money unlock", c_gate)
    if bad:
        print(col("\nFix the red items above, then run again.", R))
        if HEADLESS:
            time.sleep(60)          # avoid a rapid crash-restart loop on Railway
        sys.exit(1)
    print(col("\nAll checks passed. Starting...\n", G))


if __name__ == "__main__":
    preflight()
    bot = Bot()
    try:
        bot.run()
    except KeyboardInterrupt:
        n = len(bot.done); w = sum(1 for p in bot.done if p["won"])
        print(f"\nStopped. {n} settled trades, {w} wins, P&L ${bot.pnl:+.2f}. Log: {CSV_PATH}")
        print("\n".join(bot.scorecard()))
        sys.exit(0)
