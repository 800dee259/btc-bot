#!/usr/bin/env python3
"""
Kalshi 15-minute Bitcoin (KXBTC15M) bot.

What it does
  Every few seconds it finds the open 15-minute "BTC up or down" market, estimates
  the chance Bitcoin finishes above the market's strike (from Coinbase spot, time
  left and recent volatility), and trades only when that estimate beats Kalshi's
  price by a margin after fees.

Modes (safe by default)
  python kalshi_bot.py            DRY RUN: reads markets, logs decisions, places NO orders
  python kalshi_bot.py --demo     sends orders to Kalshi's DEMO environment (fake money)
  python kalshi_bot.py --live     sends REAL orders (asks you to type YES first)
  python kalshi_bot.py --once     run a single check and exit (works with any mode)

Setup
  pip install cryptography
  export KALSHI_KEY_ID="your-api-key-id"
  export KALSHI_KEY_PATH="/path/to/your/private-key.pem"
  (Demo and live use different accounts and different keys.)

Telegram alerts (optional)
  export TELEGRAM_TOKEN="your-bot-token"
  export TELEGRAM_CHAT_ID="your-chat-id"
  Alerts: startup, signals (dry run), orders/fills, errors, loss limit, crash, heartbeat.
  (If these are not set but NTFY_TOPIC is, alerts go through ntfy.sh instead.)

NOT financial advice. The model is simple and has no proven edge. Test in dry-run,
then demo, and use only money you can afford to lose.
"""
import argparse
import base64
import json
import math
import os
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime, timezone

PROD = "https://external-api.kalshi.com/trade-api/v2"
DEMO = "https://external-api.demo.kalshi.co/trade-api/v2"
# (label, Kalshi series, Coinbase product)
ASSETS = [
    ("BTC", "KXBTC15M", "BTC-USD"),
]

# ---- settings you can change ----
STAKE_USD = 5.0            # max spend per trade
MIN_EDGE = 0.00            # model chance must beat price + fee by 8 cents
MAX_EDGE = 0.30            # bigger "edges" are treated as model/data errors and skipped
FEE_RATE = 0.07            # approx. taker fee = FEE_RATE * p * (1 - p) per contract; verify on Kalshi
BASIS_FRAC = 0.00017       # allowance for Coinbase spot differing from Kalshi's reference (about $15 on BTC at 90k)
MIN_SECS_LEFT = 120        # don't trade in the last 2 minutes
MAX_SECS_LEFT = 600        # don't trade in the first 5 minutes
MAX_TRADES_PER_DAY = 20
MAX_DAILY_LOSS_USD = 20.0  # stop trading if cash balance falls this far below the start
POLL_SECS = 10
TRADE_LOG = "kalshi_trades.jsonl"
HEARTBEAT_SECS = 1800      # "still alive" ping every 30 minutes
ERROR_ALERT_COOLDOWN = 900  # send the same kind of error alert at most every 15 minutes


# ---------- Kalshi API ----------
class Kalshi:
    def __init__(self, base, key_id=None, key_path=None):
        self.base, self.key_id, self.key = base, key_id, None
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
        url = self.base + endpoint
        if params:
            url += "?" + urllib.parse.urlencode(params)
        headers = {"Content-Type": "application/json", "User-Agent": "kalshi-bot/1.0"}
        if self.key:
            ts = str(int(time.time() * 1000))
            path = urllib.parse.urlparse(self.base + endpoint).path  # no query string
            headers.update({
                "KALSHI-ACCESS-KEY": self.key_id,
                "KALSHI-ACCESS-TIMESTAMP": ts,
                "KALSHI-ACCESS-SIGNATURE": self._sign(ts, method, path),
            })
        data = json.dumps(body).encode() if body is not None else None
        req = urllib.request.Request(url, data=data, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=15) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            raise RuntimeError(f"{method} {endpoint} -> HTTP {e.code}: {e.read().decode()[:300]}")

    def open_market(self, series):
        res = self.call("GET", "/markets",
                        {"series_ticker": series, "status": "open", "limit": 20})
        now = datetime.now(timezone.utc)
        live = [m for m in res.get("markets", []) if parse_time(m["close_time"]) > now]
        live.sort(key=lambda m: m["close_time"])
        return live[0] if live else None

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


# ---------- market data & model ----------
def parse_time(s):
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def http_json(url):
    req = urllib.request.Request(url, headers={"User-Agent": "kalshi-bot/1.0"})
    with urllib.request.urlopen(req, timeout=15) as r:
        return json.load(r)


def spot_price(product):
    return float(http_json(f"https://api.exchange.coinbase.com/products/{product}/ticker")["price"])


def minute_sigma(spot, product):
    """Std dev of 1-minute price changes in dollars (per sqrt-minute)."""
    try:
        rows = http_json(f"https://api.exchange.coinbase.com/products/{product}/candles?granularity=60")
        closes = [r[4] for r in rows[:45]][::-1]
        d = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
        m = sum(d) / len(d)
        s = math.sqrt(sum((x - m) ** 2 for x in d) / len(d))
    except Exception:
        s = 0.0008 * spot
    return min(max(s, 0.0003 * spot), 0.003 * spot)


def phi(z):
    return 0.5 * (1 + math.erf(z / math.sqrt(2)))


def prob_up(spot, strike, secs_left, sigma):
    sd = math.sqrt(sigma ** 2 * (secs_left / 60.0) + (BASIS_FRAC * spot) ** 2)
    return min(0.95, max(0.05, phi((spot - strike) / sd)))


def fee(p):
    return FEE_RATE * p * (1 - p)


def num(m, key):
    try:
        return float(m.get(key) or 0)
    except (TypeError, ValueError):
        return 0.0


def decide(m, spot, sigma, now):
    """Returns (action, info). action is None or a dict describing the order."""
    strike = m.get("floor_strike")
    if strike is None:
        return None, "market has no strike; skipping"
    secs = (parse_time(m["close_time"]) - now).total_seconds()
    if not (MIN_SECS_LEFT <= secs <= MAX_SECS_LEFT):
        return None, f"outside trading window ({secs:.0f}s left)"
    p = prob_up(spot, float(strike), secs, sigma)
    ya, yb, na = num(m, "yes_ask_dollars"), num(m, "yes_bid_dollars"), num(m, "no_ask_dollars")
    options = []
    if 0 < ya < 1:
        options.append(("UP", "bid", ya, ya, p - ya - fee(ya)))
    if 0 < na < 1 and 0 < yb < 1:
        options.append(("DOWN", "ask", yb, na, (1 - p) - na - fee(na)))
    info = f"model up={p:.0%} yes_ask={ya:.2f} no_ask={na:.2f}"
    if not options:
        return None, info + " | no liquidity"
    name, side, order_price, cost, edge = max(options, key=lambda o: o[4])
    info += f" | best={name} edge={edge:+.2f}"
    if edge < MIN_EDGE:
        return None, info + " | no trade"
    if edge > MAX_EDGE:
        return None, info + " | edge too large, likely bad data; skipping"
    count = int(STAKE_USD // cost)
    if count < 1:
        return None, info + " | stake too small for one contract"
    return {"name": name, "side": side, "price": order_price, "count": count,
            "cost": cost, "edge": edge}, info


# ---------- main loop ----------
def log_trade(rec):
    with open(TRADE_LOG, "a") as f:
        f.write(json.dumps(rec) + "\n")


def stamp():
    return datetime.now().strftime("%H:%M:%S")


STATE_FILE = "kalshi_state.json"
_last_alert = {}


def notify(title, message, key=None, cooldown=0):
    """Phone alert. Uses Telegram if TELEGRAM_TOKEN and TELEGRAM_CHAT_ID are set,
    otherwise ntfy.sh if NTFY_TOPIC is set. Never raises.
    key + cooldown (seconds) rate-limits repeated alerts of the same kind."""
    if key:
        if time.time() - _last_alert.get(key, 0) < cooldown:
            return
        _last_alert[key] = time.time()
    token, chat = os.environ.get("TELEGRAM_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    topic = os.environ.get("NTFY_TOPIC")
    try:
        if token and chat:
            body = json.dumps({"chat_id": chat, "text": f"{title}\n{message}"}).encode("utf-8")
            req = urllib.request.Request(
                f"https://api.telegram.org/bot{token}/sendMessage",
                data=body,
                headers={"Content-Type": "application/json", "User-Agent": "kalshi-bot/1.0"},
                method="POST",
            )
            urllib.request.urlopen(req, timeout=10).close()
        elif topic:
            req = urllib.request.Request(
                "https://ntfy.sh/" + urllib.parse.quote(topic),
                data=message.encode("utf-8"),
                headers={"Title": title, "Priority": "high", "User-Agent": "kalshi-bot/1.0"},
                method="POST",
            )
            urllib.request.urlopen(req, timeout=10).close()
    except Exception as e:
        print(f"[{stamp()}] could not send alert: {e}")


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


def run(api, send_orders, once):
    day = datetime.now(timezone.utc).date()
    st = load_state()
    if st.get("day") != str(day):
        st = {"day": str(day), "traded": [], "trades_today": 0, "start_bal": None}
    traded, trades_today, start_bal = set(st["traded"]), st["trades_today"], st["start_bal"]
    if api.key and start_bal is None:
        try:
            start_bal = api.balance_usd()
            print(f"[{stamp()}] starting balance ${start_bal:,.2f}")
        except Exception as e:
            print(f"[{stamp()}] could not read balance: {e}")
    save_state(day, traded, trades_today, start_bal)
    if send_orders and start_bal is None:
        print("Refusing to send orders without a readable balance (needed for the loss limit).")
        notify("Kalshi bot NOT started", "Could not read balance, so orders are disabled. Check API key.")
        return

    last_heartbeat = time.time()

    while True:
        try:
            today = datetime.now(timezone.utc).date()
            if today != day:
                day, trades_today = today, 0
                traded.clear()
                start_bal = api.balance_usd() if api.key else None
                save_state(day, traded, trades_today, start_bal)

            bal = None
            if send_orders and start_bal is not None:
                bal = api.balance_usd()
                if bal <= start_bal - MAX_DAILY_LOSS_USD:
                    print(f"[{stamp()}] daily loss limit reached (${bal:,.2f}). Stopping.")
                    notify("Kalshi bot STOPPED: daily loss limit",
                           f"Balance ${bal:,.2f} (started ${start_bal:,.2f}). No more trades today.")
                    return

            if not once and time.time() - last_heartbeat >= HEARTBEAT_SECS:
                last_heartbeat = time.time()
                msg = f"{trades_today} trades today"
                if bal is not None:
                    msg += f", balance ${bal:,.2f}"
                notify("Kalshi bot alive", msg)

            for label, series, product in ASSETS:
                try:
                    m = api.open_market(series)
                    if not m:
                        print(f"[{stamp()}] {label}: no open {series} market found")
                        continue
                    spot = spot_price(product)
                    now = datetime.now(timezone.utc)
                    action, info = decide(m, spot, minute_sigma(spot, product), now)
                    print(f"[{stamp()}] {label} {m['ticker']} spot={spot:,.2f} strike={m.get('floor_strike')} | {info}")
                    if action and m["ticker"] not in traded and trades_today < MAX_TRADES_PER_DAY:
                        desc = (f"{label} {action['name']} x{action['count']} @ ~{action['cost']:.2f} "
                                f"(edge {action['edge']:+.2f}) on {m['ticker']}")
                        if send_orders:
                            res = api.place(m["ticker"], action["side"], action["price"], action["count"])
                            print(f"[{stamp()}] ORDER {desc} -> filled {res.get('fill_count')} "
                                  f"of {action['count']}, remaining {res.get('remaining_count')}")
                            log_trade({"t": now.isoformat(), "market": m["ticker"], "action": action,
                                       "spot": spot, "response": res})
                            trades_today += 1
                            notify(f"Kalshi {label} order",
                                   f"{desc}\nFilled {res.get('fill_count')} of {action['count']}, "
                                   f"remaining {res.get('remaining_count')}. "
                                   f"Trades today: {trades_today}")
                        else:
                            print(f"[{stamp()}] DRY RUN would place: {desc}")
                            mins = (parse_time(m["close_time"]) - now).total_seconds() / 60
                            kalshi_side = "YES (price goes UP)" if action["name"] == "UP" else "NO (price goes DOWN)"
                            notify(f"Kalshi {label} signal",
                                   f"Buy {kalshi_side} on the 15-min {label} market. "
                                   f"Price about {action['cost'] * 100:.0f}c, model edge {action['edge'] * 100:+.0f}c. "
                                   f"Closes in {mins:.0f} min. Check the live price in the Kalshi app first; "
                                   f"this alert may be a few minutes old.")
                        traded.add(m["ticker"])
                        save_state(day, traded, trades_today, start_bal)
                except Exception as e:
                    print(f"[{stamp()}] {label} error: {e}")
                    notify(f"Kalshi {label} error", str(e)[:300],
                           key=f"err-{label}", cooldown=ERROR_ALERT_COOLDOWN)
        except Exception as e:
            print(f"[{stamp()}] error: {e}")
            notify("Kalshi bot error", str(e)[:300], key="err-loop", cooldown=ERROR_ALERT_COOLDOWN)
        if once:
            return
        time.sleep(POLL_SECS)


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--demo", action="store_true", help="send orders to the DEMO environment")
    g.add_argument("--live", action="store_true", help="send REAL orders")
    ap.add_argument("--once", action="store_true", help="run one check and exit")
    a = ap.parse_args()

    key_id, key_path = os.environ.get("KALSHI_KEY_ID"), os.environ.get("KALSHI_KEY_PATH")
    if (a.demo or a.live) and not (key_id and key_path):
        raise SystemExit("Set KALSHI_KEY_ID and KALSHI_KEY_PATH first.")
    if a.live and input("LIVE mode places REAL orders. Type YES to continue: ") != "YES":
        return

    api = Kalshi(PROD if not a.demo else DEMO, key_id, key_path)
    mode = "LIVE" if a.live else "DEMO" if a.demo else "DRY RUN (no orders)"
    names = ", ".join(s for _, s, _ in ASSETS)
    print(f"Kalshi bot ({names}) | mode: {mode} | stake ${STAKE_USD:.2f} | min edge {MIN_EDGE:.2f}")
    if not a.once:
        notify("Kalshi bot started", f"Mode: {mode} | stake ${STAKE_USD:.2f} | min edge {MIN_EDGE:.2f}")
    try:
        run(api, send_orders=a.demo or a.live, once=a.once)
    except KeyboardInterrupt:
        notify("Kalshi bot stopped", "Stopped manually (Ctrl+C).")
    except Exception as e:
        notify("Kalshi bot CRASHED", f"{type(e).__name__}: {str(e)[:300]}")
        raise


if __name__ == "__main__":
    main()
