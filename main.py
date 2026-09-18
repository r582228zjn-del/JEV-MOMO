import os
import time
import threading
import traceback
import smtplib
from collections import defaultdict, deque
from datetime import datetime, timezone, timedelta, time as dtime
from email.message import EmailMessage
from zoneinfo import ZoneInfo

import requests
from flask import Flask, jsonify, render_template_string

ET = ZoneInfo("America/New_York")

# ---------- Configuration ----------
ALPACA_API_KEY = os.environ["ALPACA_API_KEY"]
ALPACA_SECRET_KEY = os.environ["ALPACA_SECRET_KEY"]
TYPESAFE_API_KEY = os.environ.get("TYPESAFE_API_KEY", "").strip()

ALPACA_FEED = os.environ.get("ALPACA_FEED", "iex").strip().lower()
SCAN_INTERVAL_SEC = float(os.environ.get("SCAN_INTERVAL_SEC", "7"))
MIN_PRICE = float(os.environ.get("MIN_PRICE", "1"))
MAX_PRICE = float(os.environ.get("MAX_PRICE", "20"))
MIN_CHANGE_PCT = float(os.environ.get("MIN_CHANGE_PCT", "3"))
MIN_RET_1M_PCT = float(os.environ.get("MIN_RET_1M_PCT", "0.12"))
MIN_RET_3M_PCT = float(os.environ.get("MIN_RET_3M_PCT", "0.45"))
MIN_VOLUME_ACCEL = float(os.environ.get("MIN_VOLUME_ACCEL", "1.5"))
MIN_RVOL_PROXY = float(os.environ.get("MIN_RVOL_PROXY", "2.5"))
MIN_DOLLAR_VOLUME = float(os.environ.get("MIN_DOLLAR_VOLUME", "250000"))
MAX_HOD_DISTANCE_PCT = float(os.environ.get("MAX_HOD_DISTANCE_PCT", "2.0"))
MAX_VWAP_EXTENSION_PCT = float(os.environ.get("MAX_VWAP_EXTENSION_PCT", "12.0"))
MAX_SPREAD_PCT = float(os.environ.get("MAX_SPREAD_PCT", "2.5"))
ALERT_SCORE = float(os.environ.get("ALERT_SCORE", "80"))
MAX_CANDIDATES = int(os.environ.get("MAX_CANDIDATES", "15"))

# Optional Gmail SMTP alerting.
GMAIL_USER = os.environ.get("GMAIL_USER", "").strip()
GMAIL_APP_PASSWORD = os.environ.get("GMAIL_APP_PASSWORD", "").strip()
ALERT_EMAIL_TO = os.environ.get("ALERT_EMAIL_TO", GMAIL_USER).strip()

app = Flask(__name__)

status = {
    "started_at": datetime.now(timezone.utc).isoformat(),
    "last_scan": None,
    "last_error": None,
    "engine": "heuristic",
    "feed": ALPACA_FEED,
    "candidates_seen": 0,
    "evaluations": 0,
    "triggers": 0,
}
signals = deque(maxlen=100)
eval_last = defaultdict(lambda: 0.0)
alert_last = defaultdict(lambda: 0.0)
prev_jev = {}


def fnum(v, default=0.0):
    try:
        if v is None or v == "":
            return float(default)
        return float(v)
    except Exception:
        return float(default)


def clip(x, lo=0.0, hi=1.0):
    return max(lo, min(hi, x))


def pct(a, b):
    return ((a / b) - 1.0) * 100.0 if b else 0.0


def parse_iso(ts):
    if not ts:
        return None
    return datetime.fromisoformat(str(ts).replace("Z", "+00:00"))


class AlpacaData:
    DATA = "https://data.alpaca.markets"

    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({
            "APCA-API-KEY-ID": ALPACA_API_KEY,
            "APCA-API-SECRET-KEY": ALPACA_SECRET_KEY,
        })

    def _get(self, url, params=None):
        r = self.s.get(url, params=params or {}, timeout=10)
        r.raise_for_status()
        return r.json()

    def most_actives(self, by="volume", top=120):
        return self._get(
            f"{self.DATA}/v1beta1/screener/stocks/most-actives",
            {"by": by, "top": top},
        )

    def movers(self, top=50):
        return self._get(
            f"{self.DATA}/v1beta1/screener/stocks/movers",
            {"top": top},
        )

    def snapshots(self, symbols):
        if not symbols:
            return {}
        data = self._get(
            f"{self.DATA}/v2/stocks/snapshots",
            {"symbols": ",".join(symbols), "feed": ALPACA_FEED},
        )
        return data.get("snapshots", data)

    def bars(self, symbol, start, end):
        data = self._get(
            f"{self.DATA}/v2/stocks/{symbol}/bars",
            {
                "timeframe": "1Min",
                "start": start.astimezone(timezone.utc).isoformat(),
                "end": end.astimezone(timezone.utc).isoformat(),
                "limit": 1000,
                "adjustment": "raw",
                "feed": ALPACA_FEED,
            },
        )
        return data.get("bars", [])


def extract_symbols(payload):
    out = set()
    if isinstance(payload, dict):
        for key in ("most_actives", "gainers", "losers", "mostActives"):
            items = payload.get(key)
            if isinstance(items, list):
                for x in items:
                    if isinstance(x, dict) and x.get("symbol"):
                        out.add(str(x["symbol"]).upper())
        for v in payload.values():
            if isinstance(v, list):
                for x in v:
                    if isinstance(x, dict) and x.get("symbol"):
                        out.add(str(x["symbol"]).upper())
    return out


def discover_symbols(api):
    symbols = set()
    for by in ("volume", "trades"):
        try:
            symbols |= extract_symbols(api.most_actives(by=by))
        except Exception:
            pass
    try:
        symbols |= extract_symbols(api.movers())
    except Exception:
        pass
    return sorted(symbols)


def session_start_et(now_et):
    return now_et.replace(hour=4, minute=0, second=0, microsecond=0)


def build_features(symbol, snap, bars):
    lt = snap.get("latestTrade") or {}
    lq = snap.get("latestQuote") or {}
    mb = snap.get("minuteBar") or {}
    db = snap.get("dailyBar") or {}
    pd = snap.get("prevDailyBar") or {}

    price = fnum(lt.get("p")) or fnum(mb.get("c")) or fnum(db.get("c"))
    prev_close = fnum(pd.get("c"))
    change_pct = pct(price, prev_close)

    bid = fnum(lq.get("bp"))
    ask = fnum(lq.get("ap"))
    bid_size = fnum(lq.get("bs"))
    ask_size = fnum(lq.get("as"))
    mid = (bid + ask) / 2 if bid and ask else price
    spread_pct = ((ask - bid) / mid * 100) if mid and ask >= bid > 0 else 999.0
    denom = bid_size + ask_size
    imbalance = ((bid_size - ask_size) / denom) if denom else 0.0

    valid = [b for b in bars if fnum(b.get("c")) > 0 and fnum(b.get("v")) > 0]
    closes = [fnum(b.get("c")) for b in valid]
    vols = [fnum(b.get("v")) for b in valid]

    last_close = closes[-1] if closes else price
    prev1 = closes[-2] if len(closes) >= 2 else last_close
    prev3 = closes[-4] if len(closes) >= 4 else (closes[0] if closes else last_close)
    ret_1m_pct = pct(last_close, prev1)
    ret_3m_pct = pct(last_close, prev3)

    last_v = vols[-1] if vols else fnum(mb.get("v"))
    prev_v = vols[-2] if len(vols) >= 2 else max(last_v, 1)
    volume_accel = last_v / prev_v if prev_v > 0 else 0.0

    session_volume = sum(vols)
    session_dollar_volume = sum(
        (fnum(b.get("vw")) or fnum(b.get("c"))) * fnum(b.get("v"))
        for b in valid
    )

    v_sum = sum(vols)
    vwap = (
        sum((fnum(b.get("vw")) or fnum(b.get("c"))) * fnum(b.get("v")) for b in valid) / v_sum
        if v_sum > 0 else fnum(db.get("vw"), price)
    )
    hod = max([fnum(b.get("h")) for b in valid] + [price]) if price else 0.0

    pm_highs = []
    for b in valid:
        dt = parse_iso(b.get("t"))
        if dt and dt.astimezone(ET).time() < dtime(9, 30):
            pm_highs.append(fnum(b.get("h")))
    pm_high = max(pm_highs) if pm_highs else 0.0

    prev_day_volume = fnum(pd.get("v"))
    now_et = datetime.now(timezone.utc).astimezone(ET)
    elapsed_min = max(1.0, (now_et - session_start_et(now_et)).total_seconds() / 60)
    prev_avg_min = prev_day_volume / 390.0 if prev_day_volume > 0 else 0.0
    current_avg_min = session_volume / elapsed_min
    rvol_proxy = current_avg_min / prev_avg_min if prev_avg_min > 0 else 0.0

    return {
        "symbol": symbol,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "price": price,
        "change_pct": change_pct,
        "ret_1m_pct": ret_1m_pct,
        "ret_3m_pct": ret_3m_pct,
        "volume_accel_1m": volume_accel,
        "rvol_proxy": rvol_proxy,
        "session_dollar_volume": session_dollar_volume,
        "vwap": vwap,
        "distance_from_vwap_pct": pct(price, vwap) if vwap else 0.0,
        "hod": hod,
        "distance_from_hod_pct": pct(price, hod) if hod else 0.0,
        "pm_high": pm_high,
        "distance_from_pm_high_pct": pct(price, pm_high) if pm_high else None,
        "spread_pct": spread_pct,
        "book_imbalance": imbalance,
    }


def directional_prefilter(x):
    return (
        MIN_PRICE <= x["price"] <= MAX_PRICE
        and x["change_pct"] >= MIN_CHANGE_PCT
        and x["ret_1m_pct"] >= MIN_RET_1M_PCT
        and x["ret_3m_pct"] >= MIN_RET_3M_PCT
        and x["price"] >= x["vwap"]
        and x["distance_from_hod_pct"] >= -MAX_HOD_DISTANCE_PCT
        and x["distance_from_vwap_pct"] <= MAX_VWAP_EXTENSION_PCT
        and x["session_dollar_volume"] >= MIN_DOLLAR_VOLUME
        and (
            x["volume_accel_1m"] >= MIN_VOLUME_ACCEL
            or x["rvol_proxy"] >= MIN_RVOL_PROXY
        )
        and x["spread_pct"] <= MAX_SPREAD_PCT
    )


class LongOnlyDecisionEngine:
    def __init__(self):
        self.client = None
        self.mode = "heuristic"

        if TYPESAFE_API_KEY:
            os.environ["TYPESAFE_API_KEY"] = TYPESAFE_API_KEY
            try:
                from typesafe_sdk import TypeSafeClient, Noul, Choice
                self.TypeSafeClient = TypeSafeClient
                self.Noul = Noul
                self.Choice = Choice
                self.client = TypeSafeClient()
                self.mode = "jev"
            except Exception as e:
                print("Jev SDK unavailable; heuristic fallback:", e)

        status["engine"] = self.mode

    def heuristic(self, x):
        mom = clip(
            0.25
            + 0.10 * min(x["ret_1m_pct"], 3)
            + 0.06 * min(x["ret_3m_pct"], 8)
            + 0.10 * min(x["volume_accel_1m"], 4)
            + 0.04 * min(x["rvol_proxy"], 10)
            + 0.10 * max(-1, min(1, x["book_imbalance"]))
            - 0.07 * max(0, x["spread_pct"] - 1)
        )
        near_hod = clip(1 - abs(min(0, x["distance_from_hod_pct"])) / 3)
        bo = clip(0.25 + 0.50 * mom + 0.25 * near_hod)
        cont = clip(
            0.20 + 0.45 * mom + 0.20 * bo
            + 0.15 * clip(x["distance_from_vwap_pct"] / 8)
        )
        return mom, bo, cont

    def evaluate(self, x):
        t0 = time.perf_counter()

        if self.mode == "jev":
            state = {
                "symbol": x["symbol"],
                "price": round(x["price"], 4),
                "change_pct": round(x["change_pct"], 3),
                "ret_1m_pct": round(x["ret_1m_pct"], 3),
                "ret_3m_pct": round(x["ret_3m_pct"], 3),
                "volume_accel_1m": round(x["volume_accel_1m"], 3),
                "rvol_proxy": round(x["rvol_proxy"], 3),
                "session_dollar_volume": round(x["session_dollar_volume"], 2),
                "distance_from_vwap_pct": round(x["distance_from_vwap_pct"], 3),
                "distance_from_hod_pct": round(x["distance_from_hod_pct"], 3),
                "distance_from_premarket_high_pct": (
                    None if x["distance_from_pm_high_pct"] is None
                    else round(x["distance_from_pm_high_pct"], 3)
                ),
                "spread_pct": round(x["spread_pct"], 3),
                "book_imbalance": round(x["book_imbalance"], 3),
            }
            questions = {
                "up_momentum": self.Noul(
                    instructions="Using only this structured state, is upside momentum strong and currently accelerating?"
                ),
                "up_breakout": self.Choice(
                    instructions="Classify the long-side upside breakout state.",
                    criteria={
                        "UP_BREAKOUT": "Price and volume support upside breakout or HOD continuation.",
                        "NO_BREAKOUT": "No convincing upside breakout is present.",
                        "UNCLEAR": "Evidence is mixed.",
                    },
                ),
                "continuation": self.Noul(
                    instructions="Is this long-side move likely to continue higher over the next few minutes rather than immediately stall?"
                ),
            }
            resp = self.client.system_one(state=state, questions=questions)
            mom = float(resp.nouls["up_momentum"].noul)
            bo_probs = dict(resp.choices["up_breakout"].probabilities)
            bo = float(bo_probs.get("UP_BREAKOUT", 0.0))
            cont = float(resp.nouls["continuation"].noul)
        else:
            mom, bo, cont = self.heuristic(x)

        vol_component = min(8.0, max(0.0, (x["volume_accel_1m"] - 1.0) * 6.0))
        rvol_component = min(5.0, x["rvol_proxy"] * 1.2)

        structure = 0.0
        if x["distance_from_vwap_pct"] >= 0:
            structure += 2.5
        if x["distance_from_hod_pct"] >= -1.0:
            structure += 2.5

        micro = 0.0
        if x["spread_pct"] <= 0.5:
            micro += 1.2
        elif x["spread_pct"] <= 1.0:
            micro += 0.8
        if x["book_imbalance"] > 0.10:
            micro += 0.8
        micro = min(2.0, micro)

        score = max(0, min(100,
            40 * mom
            + 25 * bo
            + 15 * cont
            + vol_component
            + rvol_component
            + structure
            + micro
        ))

        prev = prev_jev.get(x["symbol"])
        dm = 0.0 if prev is None else mom - prev["mom"]
        db = 0.0 if prev is None else bo - prev["bo"]
        dc = 0.0 if prev is None else cont - prev["cont"]
        prev_jev[x["symbol"]] = {"mom": mom, "bo": bo, "cont": cont}

        return {
            "engine": self.mode,
            "up_momentum_probability": mom,
            "up_breakout_probability": bo,
            "continuation_probability": cont,
            "momentum_delta": dm,
            "breakout_delta": db,
            "continuation_delta": dc,
            "long_momo_score": score,
            "latency_ms": (time.perf_counter() - t0) * 1000,
        }


def send_email(subject, body):
    if not (GMAIL_USER and GMAIL_APP_PASSWORD and ALERT_EMAIL_TO):
        return
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = GMAIL_USER
    msg["To"] = ALERT_EMAIL_TO
    msg.set_content(body)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=10) as smtp:
        smtp.login(GMAIL_USER, GMAIL_APP_PASSWORD)
        smtp.send_message(msg)


def format_trigger(x, d):
    target = x["price"] * 1.10
    pm = "n/a" if x["distance_from_pm_high_pct"] is None else f'{x["distance_from_pm_high_pct"]:+.2f}%'
    return (
        f'LONG MOMO TRIGGER — {x["symbol"]}\n'
        f'Entry ref ${x["price"]:.2f} → TP ${target:.2f} (+10%)\n'
        f'Day {x["change_pct"]:+.1f}% | 1m {x["ret_1m_pct"]:+.2f}% | 3m {x["ret_3m_pct"]:+.2f}%\n'
        f'Score {d["long_momo_score"]:.1f} | '
        f'Mom {d["up_momentum_probability"]:.2f} (Δ{d["momentum_delta"]:+.2f}) | '
        f'BO {d["up_breakout_probability"]:.2f} (Δ{d["breakout_delta"]:+.2f}) | '
        f'Cont {d["continuation_probability"]:.2f}\n'
        f'VolAccel {x["volume_accel_1m"]:.2f}x | RVOLp {x["rvol_proxy"]:.2f}x | '
        f'VWAP {x["distance_from_vwap_pct"]:+.2f}% | HOD {x["distance_from_hod_pct"]:+.2f}% | PMH {pm}\n'
        f'Spread {x["spread_pct"]:.2f}% | Engine {d["engine"]}'
    )


def scanner_loop():
    api = AlpacaData()
    engine = LongOnlyDecisionEngine()

    while True:
        loop_start = time.time()
        try:
            symbols = discover_symbols(api)
            status["candidates_seen"] = len(symbols)

            snapshots = {}
            for i in range(0, len(symbols), 100):
                try:
                    snapshots.update(api.snapshots(symbols[i:i+100]))
                except Exception as e:
                    status["last_error"] = f"snapshot: {e}"

            rough = []
            for sym, snap in snapshots.items():
                lt = snap.get("latestTrade") or {}
                mb = snap.get("minuteBar") or {}
                db = snap.get("dailyBar") or {}
                pd = snap.get("prevDailyBar") or {}
                p = fnum(lt.get("p")) or fnum(mb.get("c")) or fnum(db.get("c"))
                pc = fnum(pd.get("c"))
                ch = pct(p, pc)
                if MIN_PRICE <= p <= MAX_PRICE and ch >= MIN_CHANGE_PCT:
                    rough.append((ch, sym, snap))

            rough.sort(reverse=True, key=lambda z: z[0])
            rough = rough[:MAX_CANDIDATES]

            now_et = datetime.now(timezone.utc).astimezone(ET)
            start = max(session_start_et(now_et), now_et - timedelta(minutes=180))

            for _, sym, snap in rough:
                now_s = time.time()
                if now_s - eval_last[sym] < 10:
                    continue

                try:
                    bars = api.bars(sym, start, now_et)
                    x = build_features(sym, snap, bars)
                except Exception:
                    continue

                if not directional_prefilter(x):
                    continue

                eval_last[sym] = now_s
                d = engine.evaluate(x)
                status["evaluations"] += 1

                trigger = (
                    d["long_momo_score"] >= ALERT_SCORE
                    and d["up_momentum_probability"] >= 0.76
                    and d["up_breakout_probability"] >= 0.70
                    and d["continuation_probability"] >= 0.68
                )

                if trigger and now_s - alert_last[sym] >= 75:
                    alert_last[sym] = now_s
                    body = format_trigger(x, d)
                    signal = {
                        **x,
                        **d,
                        "target_10pct": x["price"] * 1.10,
                        "alert_text": body,
                    }
                    signals.appendleft(signal)
                    status["triggers"] += 1
                    try:
                        send_email(f"[JEV MOMO] {sym} LONG TRIGGER", body)
                    except Exception as e:
                        status["last_error"] = f"email: {e}"
                    print(body, flush=True)

            status["last_scan"] = datetime.now(timezone.utc).isoformat()
            status["last_error"] = None

        except Exception as e:
            status["last_error"] = f"{type(e).__name__}: {e}"
            traceback.print_exc()

        elapsed = time.time() - loop_start
        time.sleep(max(1.0, SCAN_INTERVAL_SEC - elapsed))


DASHBOARD = """
<!doctype html>
<html>
<head>
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>JEV MOMO</title>
<style>
body{font-family:-apple-system,BlinkMacSystemFont,sans-serif;background:#0d1117;color:#e6edf3;margin:16px}
.card{background:#161b22;border:1px solid #30363d;border-radius:12px;padding:14px;margin:10px 0}
.big{font-size:22px;font-weight:700}
.good{color:#3fb950}.muted{color:#8b949e}
pre{white-space:pre-wrap;margin:8px 0 0;font-size:13px}
</style>
<meta http-equiv="refresh" content="15">
</head>
<body>
<h2>JEV MOMO — LONG ONLY +10%</h2>
<div class="card">
<div>Engine: <b>{{status.engine}}</b> · Feed: <b>{{status.feed}}</b></div>
<div class="muted">Last scan: {{status.last_scan}}</div>
<div>Evaluations: {{status.evaluations}} · Triggers: {{status.triggers}}</div>
{% if status.last_error %}<div style="color:#f85149">{{status.last_error}}</div>{% endif %}
</div>
{% for s in signals %}
<div class="card">
<div class="big good">{{s.symbol}} · ${{"%.2f"|format(s.price)}} → ${{"%.2f"|format(s.target_10pct)}}</div>
<div>Score {{"%.1f"|format(s.long_momo_score)}} · Day {{"%+.1f"|format(s.change_pct)}}%</div>
<pre>{{s.alert_text}}</pre>
</div>
{% else %}
<div class="card muted">아직 트리거 없음.</div>
{% endfor %}
</body>
</html>
"""


@app.get("/")
def dashboard():
    return render_template_string(DASHBOARD, status=status, signals=list(signals))


@app.get("/health")
def health():
    return jsonify(status)


@app.get("/api/signals")
def api_signals():
    return jsonify(list(signals))


if __name__ == "__main__":
    t = threading.Thread(target=scanner_loop, daemon=True)
    t.start()

    port = int(os.environ.get("PORT", "10000"))
    app.run(host="0.0.0.0", port=port)
