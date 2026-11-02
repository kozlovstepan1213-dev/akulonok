"""
Телеграм-бот с прогнозами на футбол и теннис.

Что умеет:
  • футбол: исход (П1/Х/П2), двойной шанс, тотал 2.5, «обе забьют», счёт и xG
    (модель Пуассона + форма, общая и дом/гостевая); оценка жёлтых карточек;
  • теннис: вероятность победы по рейтингу и форме;
  • коэффициенты БК рядом с прогнозом (лучший кф среди букмекеров, консенсус рынка,
    «справедливый» кф модели и пометка value) — через The Odds API (необязательно);
  • статистика прогнозов: каждый прогноз фиксируется ДО матча, после матча
    автоматически проверяется — «зашёл / не зашёл», точность, ROI по кф;
  • ежедневная рассылка.

Установка:
    pip install "python-telegram-bot[job-queue]" httpx tzdata

Переменные окружения:
    TELEGRAM_TOKEN   - токен от @BotFather
    FOOTBALL_API_KEY - бесплатный ключ https://www.football-data.org/client/register
    ODDS_API_KEY     - (необязательно) ключ https://the-odds-api.com (бесплатно 500 запросов/мес);
                       без него бот работает, но коэффициенты не показывает
    ODDS_REGIONS     - (необязательно) регионы БК: eu, uk, us, au (по умолчанию eu)
    ODDS_CACHE_TTL   - (необязательно) время жизни кэша кф в секундах (по умолчанию 7200)
    BOT_TZ           - (необязательно) часовой пояс, по умолчанию Europe/Moscow
    DB_FILE          - (необязательно) файл базы статистики, по умолчанию predictions.db

Запуск:
    python bot.py
"""
import os
import re
import json
import math
import time
import html
import sqlite3
import asyncio
import logging
import unicodedata
from contextlib import closing
from difflib import SequenceMatcher
from datetime import date, datetime, timedelta, timezone, time as dtime
from zoneinfo import ZoneInfo

import httpx
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest, Forbidden
from telegram.ext import (
    Application, CallbackQueryHandler, CommandHandler, ContextTypes,
)

TELEGRAM_TOKEN = os.environ["TELEGRAM_TOKEN"]
FOOTBALL_API_KEY = os.environ["FOOTBALL_API_KEY"]
ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "").strip()
ODDS_REGIONS = os.environ.get("ODDS_REGIONS", "eu")
ODDS_CACHE_TTL = int(os.environ.get("ODDS_CACHE_TTL", "7200"))
ODDS_ENABLED = bool(ODDS_API_KEY)
TZ = ZoneInfo(os.environ.get("BOT_TZ", "Europe/Moscow"))
SUBS_FILE = "subscribers.json"
DB_FILE = os.environ.get("DB_FILE", "predictions.db")
DEFAULT_DIGEST_TIME = "09:00"

FOOTBALL_API = "https://api.football-data.org/v4"
ESPN = "https://site.api.espn.com/apis/site/v2/sports/tennis"
ODDS_API = "https://api.the-odds-api.com/v4"

LEAGUES = {
    "CL": "🏆 Лига чемпионов",
    "PL": "🏴 АПЛ",
    "PD": "🇪🇸 Ла Лига",
    "SA": "🇮🇹 Серия A",
    "BL1": "🇩🇪 Бундеслига",
    "FL1": "🇫🇷 Лига 1",
    "ATP": "🎾 Теннис ATP",
    "WTA": "🎾 Теннис WTA",
}
TENNIS = {"ATP": "atp", "WTA": "wta"}

# Ключи спортов в The Odds API
ODDS_SPORT = {
    "CL": "soccer_uefa_champs_league",
    "PL": "soccer_epl",
    "PD": "soccer_spain_la_liga",
    "SA": "soccer_italy_serie_a",
    "BL1": "soccer_germany_bundesliga",
    "FL1": "soccer_france_ligue_one",
}

# Средний тотал жёлтых карточек в матче (оценочно, у бесплатного API статистики нет)
LEAGUE_CARD_AVG = {"CL": 4.1, "PL": 3.8, "PD": 5.0, "SA": 4.5, "BL1": 3.9, "FL1": 3.9}
DEFAULT_CARD_AVG = 4.0
KNOCKOUT_CARD_BONUS = 0.5
GLOBAL_AVG_GOALS = 2.6

FORM_WEIGHT = 0.35
SPLIT_WEIGHT = 0.5
TENNIS_FORM_K = 0.6

VALUE_EDGE = 0.05           # пометка 💎, если ожидаемая выгода (p·кф − 1) ≥ 5%
MAX_MODEL_GAP = 0.20        # модель расходится с рынком больше чем на 20 п.п. — не помечаем value
MIN_SAMPLE_WARN = 30        # меньше стольки прогнозов — предупреждаем о малой выборке

WEEKDAYS = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]
SEP = "\n\n──────────────\n\n"

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("sportbot")


# ======================================================================
# Вспомогательное и оформление
# ======================================================================
def esc(s) -> str:
    return html.escape(str(s), quote=False)


def parse_iso(iso: str):
    try:
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def to_utc_iso(iso: str):
    dt = parse_iso(iso)
    return dt.astimezone(timezone.utc).isoformat(timespec="seconds") if dt else None


def now_utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def local_time(iso: str) -> str:
    dt = parse_iso(iso)
    if not dt:
        return "время н/д"
    dt = dt.astimezone(TZ)
    return f"{WEEKDAYS[dt.weekday()]} {dt:%d.%m}, {dt:%H:%M}"


def _num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def pct(p: float) -> str:
    return f"{p * 100:.0f}%"


def bar(p: float, n: int = 10) -> str:
    k = max(0, min(n, round(p * n)))
    return "█" * k + "░" * (n - k)


def short_name(full: str, width: int = 11) -> str:
    parts = full.split()
    s = f"{parts[0][0]}. {' '.join(parts[1:])}" if len(parts) > 1 else full
    return s if len(s) <= width else s[: width - 1] + "…"


def chunk_messages(header: str, cards: list, limit: int = 3900) -> list:
    """Склеивает карточки в сообщения не длиннее лимита Telegram (4096)."""
    msgs, cur = [], header
    for c in cards:
        add = SEP + c
        if len(cur) + len(add) > limit and cur != header:
            msgs.append(cur)
            cur = c
        else:
            cur += add
    msgs.append(cur)
    return msgs


# ======================================================================
# Футбол: API с кэшем и ограничением частоты (бесплатно 10 запросов/мин)
# ======================================================================
_cache: dict = {}
_lock = asyncio.Lock()
_last_call = 0.0
MIN_INTERVAL = 6.5
CACHE_TTL = 1800


async def api_get(path: str, params: dict | None = None, ttl: int = CACHE_TTL) -> dict:
    global _last_call
    key = (path, tuple(sorted((params or {}).items())))
    hit = _cache.get(key)
    if hit and time.time() - hit[0] < ttl:
        return hit[1]
    async with _lock:
        hit = _cache.get(key)
        if hit and time.time() - hit[0] < ttl:
            return hit[1]
        wait = MIN_INTERVAL - (time.time() - _last_call)
        if wait > 0:
            await asyncio.sleep(wait)
        async with httpx.AsyncClient(timeout=20) as client:
            r = await client.get(
                f"{FOOTBALL_API}{path}",
                headers={"X-Auth-Token": FOOTBALL_API_KEY},
                params=params,
            )
        _last_call = time.time()
        r.raise_for_status()
        data = r.json()
        _cache[key] = (time.time(), data)
        return data


async def get_table(code: str) -> dict:
    """{team_id: строка таблицы}. Для ЛЧ на старте сезона может быть пусто."""
    try:
        data = await api_get(f"/competitions/{code}/standings")
    except httpx.HTTPError:
        return {}
    table = {}
    for s in data.get("standings", []):
        if s["type"] != "TOTAL":
            continue
        for row in s["table"]:
            table[row["team"]["id"]] = row
    return table


async def get_matches(code: str, days: int) -> list:
    today = datetime.now(TZ).date()
    data = await api_get(
        f"/competitions/{code}/matches",
        {
            "dateFrom": today.isoformat(),
            "dateTo": (today + timedelta(days=days)).isoformat(),
            "status": "SCHEDULED,TIMED",
        },
    )
    return data["matches"]


async def get_form(code: str, n: int = 5) -> dict:
    """{team_id: {"all": [(gf, ga), ...], "home": [...], "away": [...]}}"""
    data = await api_get(f"/competitions/{code}/matches", {"status": "FINISHED"})
    teams: dict = {}
    for m in sorted(data["matches"], key=lambda m: m["utcDate"]):
        ft = m["score"]["fullTime"]
        if ft["home"] is None or ft["away"] is None:
            continue
        hid, aid = m["homeTeam"]["id"], m["awayTeam"]["id"]
        for tid, gf, ga, is_home in (
            (hid, ft["home"], ft["away"], True),
            (aid, ft["away"], ft["home"], False),
        ):
            t = teams.setdefault(tid, {"all": [], "home": [], "away": []})
            t["all"].append((gf, ga))
            t["home" if is_home else "away"].append((gf, ga))
    return {tid: {k: v[-n:] for k, v in res.items()} for tid, res in teams.items()}


def form_icons(results) -> str:
    if not results:
        return "н/д"
    return "".join("🟢" if gf > ga else "🟡" if gf == ga else "🔴" for gf, ga in results)


def form_points(results) -> str:
    if not results:
        return "н/д"
    pts = sum(3 if gf > ga else 1 if gf == ga else 0 for gf, ga in results)
    return f"{pts}/{len(results) * 3} очк."


def avg_goals(results) -> tuple:
    if not results:
        return None, None
    return (sum(g for g, _ in results) / len(results),
            sum(c for _, c in results) / len(results))


# ======================================================================
# Футбол: модель Пуассона + форма
# ======================================================================
def poisson(k: int, lam: float) -> float:
    return math.exp(-lam) * lam**k / math.factorial(k)


def _form_rates(f: dict, avg: float):
    all_, home, away = f.get("all", []), f.get("home", []), f.get("away", [])
    if not all_:
        return None
    att = sum(g for g, _ in all_) / len(all_) / avg
    dfn = sum(c for _, c in all_) / len(all_) / avg
    return att, dfn, home, away


KNOCKOUT_MARKS = ("KNOCKOUT", "LAST", "QUARTER", "SEMI", "FINAL", "PLAYOFF")


def predict(home: dict, away: dict, table: dict, form: dict, code: str, stage: str = ""):
    """Возвращает dict с вероятностями или None, если данных совсем нет."""
    hid = home.get("id") or (home.get("team") or {}).get("id")
    aid = away.get("id") or (away.get("team") or {}).get("id")
    fh = form.get(hid)
    fa = form.get(aid)
    if not fh or not fa or len(fh["all"]) < 2 or len(fa["all"]) < 2:
        return None

    total_games = sum(t["playedGames"] for t in table.values())
    use_table = bool(total_games) and home.get("playedGames", 0) >= 3 and away.get("playedGames", 0) >= 3
    avg = sum(t["goalsFor"] for t in table.values()) / total_games if use_table else GLOBAL_AVG_GOALS

    def strength(t, f, is_home_team: bool):
        rates = _form_rates(f, avg)
        if rates is None:
            return None
        f_att, f_dfn, home_f, away_f = rates
        if use_table:
            att = t["goalsFor"] / t["playedGames"] / avg
            dfn = t["goalsAgainst"] / t["playedGames"] / avg
            att = (1 - FORM_WEIGHT) * att + FORM_WEIGHT * f_att
            dfn = (1 - FORM_WEIGHT) * dfn + FORM_WEIGHT * f_dfn
        else:
            att, dfn = f_att, f_dfn
        split = home_f if is_home_team else away_f
        if len(split) >= 3:
            s_att = sum(g for g, _ in split) / len(split) / avg
            s_dfn = sum(c for _, c in split) / len(split) / avg
            att = (1 - SPLIT_WEIGHT) * att + SPLIT_WEIGHT * s_att
            dfn = (1 - SPLIT_WEIGHT) * dfn + SPLIT_WEIGHT * s_dfn
        return att, dfn

    h_att, h_dfn = strength(home, fh, True)
    a_att, a_dfn = strength(away, fa, False)
    xg_home = avg * 1.15 * h_att * a_dfn
    xg_away = avg * 0.90 * a_att * h_dfn

    p_home = p_draw = p_away = p_btts = p_over25 = 0.0
    best, best_p = (0, 0), 0.0
    for h in range(10):
        for a in range(10):
            p = poisson(h, xg_home) * poisson(a, xg_away)
            if h > a:
                p_home += p
            elif h == a:
                p_draw += p
            else:
                p_away += p
            if h >= 1 and a >= 1:
                p_btts += p
            if h + a >= 3:
                p_over25 += p
            if p > best_p:
                best, best_p = (h, a), p
    s = p_home + p_draw + p_away
    p_home, p_draw, p_away = p_home / s, p_draw / s, p_away / s

    # Жёлтые карточки: оценочная модель (статистики карточек в API нет)
    cards = LEAGUE_CARD_AVG.get(code, DEFAULT_CARD_AVG)
    if any(mark in (stage or "").upper() for mark in KNOCKOUT_MARKS):
        cards += KNOCKOUT_CARD_BONUS
    cards += 0.3 * (1 - abs(p_home - p_away))
    cards = max(2.5, min(6.5, cards))
    p_c35 = 1 - sum(poisson(k, cards) for k in range(4))
    p_c45 = 1 - sum(poisson(k, cards) for k in range(5))

    return {
        "home": p_home, "draw": p_draw, "away": p_away,
        "dc_1x": p_home + p_draw, "dc_12": p_home + p_away, "dc_x2": p_draw + p_away,
        "btts": p_btts / s, "over25": p_over25 / s,
        "score": best, "xg": (xg_home, xg_away),
        "cards": cards, "cards_over35": p_c35, "cards_over45": p_c45,
        "table_used": use_table,
    }


# ======================================================================
# Коэффициенты БК (The Odds API)
# ======================================================================
_odds_cache: dict = {}
_odds_remaining: int | None = None
_STOP = {"fc", "afc", "cf", "ac", "as", "sc", "ssc", "rc", "rcd", "cd", "ud", "us", "fk",
         "club", "de", "di", "del", "the", "calcio", "cp", "sv", "ssd"}
_ALIAS = {
    "wolverhampton wanderers": "wolves",
    "internazionale milano": "inter",
    "inter milan": "inter",
    "bayern munchen": "bayern munich",
}


def norm_name(s: str) -> list:
    s = unicodedata.normalize("NFKD", s or "").encode("ascii", "ignore").decode().lower()
    s = re.sub(r"[^a-z0-9 ]+", " ", s.replace("&", " and "))
    toks = [t for t in s.split() if t not in _STOP and not t.isdigit()]
    name = _ALIAS.get(" ".join(toks), " ".join(toks))
    return name.split()


def same_team(a: str, b: str) -> bool:
    ta, tb = norm_name(a), norm_name(b)
    if not ta or not tb:
        return False
    sa, sb = set(ta), set(tb)
    if sa == sb:
        return True
    small, big = (sa, sb) if len(sa) <= len(sb) else (sb, sa)
    if small <= big and any(len(t) >= 4 for t in small):
        return True
    return SequenceMatcher(None, " ".join(ta), " ".join(tb)).ratio() >= 0.85


def same_player(a: str, b: str) -> bool:
    ta, tb = norm_name(a), norm_name(b)
    if not ta or not tb:
        return False
    if set(ta) == set(tb):
        return True
    return ta[-1] == tb[-1] and ta[0][0] == tb[0][0]


async def odds_get(path: str, params: dict):
    """(время_загрузки, данные) или None. Кэш + защита от исчерпания лимита."""
    global _odds_remaining
    if not ODDS_ENABLED:
        return None
    if _odds_remaining is not None and _odds_remaining < 5:
        return None
    key = (path, tuple(sorted(params.items())))
    hit = _odds_cache.get(key)
    if hit and time.time() < hit[0]:
        return (hit[1], hit[2]) if hit[2] is not None else None
    try:
        async with httpx.AsyncClient(timeout=20) as client:
            r = await client.get(f"{ODDS_API}{path}", params={**params, "apiKey": ODDS_API_KEY})
        rem = r.headers.get("x-requests-remaining")
        if rem is not None and rem.isdigit():
            _odds_remaining = int(rem)
            log.info("Odds API: осталось запросов %s", rem)
        r.raise_for_status()
        fetched, data = time.time(), r.json()
        _odds_cache[key] = (fetched + ODDS_CACHE_TTL, fetched, data)
        return fetched, data
    except httpx.HTTPError as e:
        log.warning("Odds API недоступен (%s): %s", path, e)
        _odds_cache[key] = (time.time() + 600, 0, None)  # не долбим API 10 минут
        return None


def _devig(prices: dict) -> dict:
    """Кф -> вероятности без маржи букмекера."""
    inv = {k: 1 / v for k, v in prices.items()}
    s = sum(inv.values())
    return {k: v / s for k, v in inv.items()}


def _take_best(best: dict, title: str, prices: dict) -> None:
    for k, pr in prices.items():
        if k not in best or pr > best[k][0]:
            best[k] = (pr, title)


def extract_odds(ev: dict, side_a: str, side_b: str, matcher, has_draw: bool) -> dict:
    """Лучшие кф (с названием БК) и консенсус-вероятности рынка по событию."""
    best, probs, books = {}, {}, set()
    for bk in ev.get("bookmakers", []):
        title = bk.get("title") or bk.get("key") or "БК"
        for mk in bk.get("markets", []):
            prices = {}
            if mk.get("key") == "h2h":
                for o in mk.get("outcomes", []):
                    nm, pr = o.get("name") or "", _num(o.get("price"))
                    if not pr or pr <= 1:
                        continue
                    if has_draw and nm.lower() == "draw":
                        k = "draw"
                    elif matcher(nm, side_a):
                        k = "home"
                    elif matcher(nm, side_b):
                        k = "away"
                    else:
                        continue
                    prices[k] = pr
                if len(prices) != (3 if has_draw else 2):
                    continue
            elif mk.get("key") == "totals" and has_draw:
                for o in mk.get("outcomes", []):
                    nm, pr = (o.get("name") or "").lower(), _num(o.get("price"))
                    if _num(o.get("point")) == 2.5 and nm in ("over", "under") and pr and pr > 1:
                        prices[nm] = pr
                if len(prices) != 2:
                    continue
            else:
                continue
            _take_best(best, title, prices)
            for k, v in _devig(prices).items():
                probs.setdefault(k, []).append(v)
            books.add(title)
    return {
        "best": best,
        "prob": {k: sum(v) / len(v) for k, v in probs.items()},
        "books": len(books),
    }


def find_event(events: list, a: str, b: str, kickoff_iso: str, matcher,
               ordered: bool = True, tol_h: float = 8):
    kt = parse_iso(kickoff_iso)
    if not kt:
        return None
    for ev in events or []:
        et = parse_iso(ev.get("commence_time", ""))
        if not et or abs((et - kt).total_seconds()) > tol_h * 3600:
            continue
        h, w = ev.get("home_team", ""), ev.get("away_team", "")
        if matcher(h, a) and matcher(w, b):
            return ev
        if not ordered and matcher(h, b) and matcher(w, a):
            return ev
    return None


async def football_odds(code: str, home: str, away: str, kickoff_iso: str):
    sport = ODDS_SPORT.get(code)
    if not sport:
        return None
    got = await odds_get(f"/sports/{sport}/odds", {
        "regions": ODDS_REGIONS, "markets": "h2h,totals",
        "oddsFormat": "decimal", "dateFormat": "iso"})
    if not got:
        return None
    fetched, events = got
    ev = find_event(events, home, away, kickoff_iso, same_team, ordered=True)
    if not ev:
        return None
    res = extract_odds(ev, home, away, same_team, has_draw=True)
    res["fetched"] = fetched
    return res if res["best"] else None


async def tennis_odds_events(tour: str):
    """(время, [события]) по всем активным турнирам тура. Список спортов бесплатный."""
    sports = await odds_get("/sports", {})
    if not sports:
        return None
    keys = [s["key"] for s in sports[1]
            if s.get("active") and s.get("key", "").startswith(f"tennis_{tour}")]
    events, fetched = [], None
    for k in keys[:4]:
        got = await odds_get(f"/sports/{k}/odds", {
            "regions": ODDS_REGIONS, "markets": "h2h",
            "oddsFormat": "decimal", "dateFormat": "iso"})
        if got:
            fetched = got[0]
            events += got[1]
    return (fetched, events) if fetched else None


def tennis_odds(pack, p1: str, p2: str, when: str):
    if not pack:
        return None
    fetched, events = pack
    ev = find_event(events, p1, p2, when, same_player, ordered=False, tol_h=14)
    if not ev:
        return None
    res = extract_odds(ev, p1, p2, same_player, has_draw=False)
    res["fetched"] = fetched
    return res if res["best"] else None


# ======================================================================
# Оформление прогнозов
# ======================================================================
def odd_of(odds, key):
    return odds["best"].get(key) if odds else None


def pick_line(title: str, label: str, prob: float, odd=None, mprob=None) -> str:
    s = f"▸ {title}: <b>{esc(label)}</b> — {pct(prob)}"
    if odd:
        s += f" · кф <b>{odd[0]:.2f}</b> ({esc(odd[1])})"
        notes = []
        if mprob is not None:
            notes.append(f"рынок {pct(mprob)}")
        notes.append(f"справедл. кф {1 / prob:.2f}")
        ev = prob * odd[0] - 1
        if mprob is not None and abs(prob - mprob) > MAX_MODEL_GAP:
            notes.append("⚠️ сильно расходится с рынком — вероятна ошибка модели")
        elif ev >= VALUE_EDGE:
            notes.append(f"💎 value {ev:+.0%}")
        s += "\n    <i>" + " · ".join(notes) + "</i>"
    return s


def odds_footnote(odds) -> str:
    if odds:
        t = datetime.fromtimestamp(odds["fetched"], TZ).strftime("%H:%M")
        return f"<i>кф: лучшие из {odds['books']} БК на {t}, могут измениться</i>"
    if ODDS_ENABLED:
        return "<i>кф: по этому матчу данных нет</i>"
    return ""


def football_card(m: dict, table: dict, form: dict, code: str, odds):
    """-> (текст HTML, список прогнозов для учёта в статистике)."""
    h, a = m["homeTeam"], m["awayTeam"]
    hn, an = h.get("shortName") or h["name"], a.get("shortName") or a["name"]
    lines = [f"⚽ <b>{esc(hn)} — {esc(an)}</b>",
             f"{esc(LEAGUES[code])} · 🕒 {local_time(m['utcDate'])}"]

    fh, fa = form.get(h["id"]), form.get(a["id"])
    if fh and fa:
        hgf, hga = avg_goals(fh["all"])
        agf, aga = avg_goals(fa["all"])
        lines += [
            "", "<b>Форма</b> · последние матчи",
            f"{esc(hn)}: {form_icons(fh['all'])} {form_points(fh['all'])}",
            f"{esc(an)}: {form_icons(fa['all'])} {form_points(fa['all'])}",
            f"Дома │ в гостях: {form_icons(fh['home'])} │ {form_icons(fa['away'])}",
            f"Голы за/пропущ.: {hgf:.1f}/{hga:.1f} │ {agf:.1f}/{aga:.1f}",
        ]
    ht, at = table.get(h["id"]), table.get(a["id"])
    if ht and at:
        lines.append(f"Таблица: #{ht.get('position')} ({ht.get('points')} очк.) │ "
                     f"#{at.get('position')} ({at.get('points')} очк.)")

    p = predict(ht or {"id": h["id"]}, at or {"id": a["id"]}, table, form, code,
                stage=m.get("stage", ""))
    if not p:
        return "\n".join(lines) + "\n\nℹ️ Недостаточно данных для прогноза.", []

    # --- блок вероятностей ---
    rows = (("П1", p["home"], "home"), ("Х", p["draw"], "draw"), ("П2", p["away"], "away"))
    pre = []
    for lab, pr, k in rows:
        o = odd_of(odds, k)
        pre.append(f"{lab:<2} {bar(pr)} {pr * 100:>3.0f}%" + (f"  {o[0]:.2f}" if o else ""))
    head = "<b>Исход</b> · модель" + (" │ лучший кф" if odds else "")

    def with_odd(key):
        o = odd_of(odds, key)
        return f" (кф {o[0]:.2f})" if o else ""

    lines += [
        "", head, "<pre>" + "\n".join(pre) + "</pre>",
        f"Двойной шанс: 1X {pct(p['dc_1x'])} · 12 {pct(p['dc_12'])} · X2 {pct(p['dc_x2'])}",
        f"Тотал 2.5: ТБ {pct(p['over25'])}{with_odd('over')} · "
        f"ТМ {pct(1 - p['over25'])}{with_odd('under')}",
        f"Обе забьют: Да {pct(p['btts'])} · Нет {pct(1 - p['btts'])}",
        f"Счёт: {p['score'][0]}:{p['score'][1]} · xG {p['xg'][0]:.1f}–{p['xg'][1]:.1f}",
        f"Карточки (оценка): ~{p['cards']:.1f} · ТБ 3.5 {pct(p['cards_over35'])} · "
        f"ТБ 4.5 {pct(p['cards_over45'])}",
    ]

    # --- итоговые прогнозы (именно они идут в статистику) ---
    top_key, top_label, top_p = max(
        (("1", "П1", p["home"]), ("X", "Х", p["draw"]), ("2", "П2", p["away"])),
        key=lambda x: x[2])
    odds_key = {"1": "home", "X": "draw", "2": "away"}[top_key]
    over = p["over25"] >= 0.5
    btts = p["btts"] >= 0.5
    tot_p = p["over25"] if over else 1 - p["over25"]
    btts_p = p["btts"] if btts else 1 - p["btts"]
    tot_odd = odd_of(odds, "over" if over else "under")
    mkt = (odds or {}).get("prob", {})

    lines += [
        "", "📌 <b>Прогноз</b>",
        pick_line("Исход", top_label, top_p, odd_of(odds, odds_key), mkt.get(odds_key)),
        pick_line("Тотал", "ТБ 2.5" if over else "ТМ 2.5", tot_p, tot_odd,
                  mkt.get("over" if over else "under")),
        f"▸ Обе забьют: <b>{'Да' if btts else 'Нет'}</b> — {pct(btts_p)}",
    ]
    if not p["table_used"]:
        lines.append("<i>ℹ️ таблицы ещё нет — оценка по форме</i>")
    note = odds_footnote(odds)
    if note:
        lines.append(note)

    picks = [
        dict(market="1X2", pick=top_key, label=top_label, prob=top_p,
             odd=odd_of(odds, odds_key)),
        dict(market="TOTAL25", pick="over" if over else "under",
             label="ТБ 2.5" if over else "ТМ 2.5", prob=tot_p, odd=tot_odd),
        dict(market="BTTS", pick="yes" if btts else "no",
             label="Да" if btts else "Нет", prob=btts_p, odd=None),
    ]
    return "\n".join(lines), picks


async def football_texts(code: str, days: int = 7, limit: int = 6, only_today: bool = False) -> list:
    matches = await get_matches(code, days)
    if only_today:
        today = datetime.now(TZ).date()
        matches = [m for m in matches
                   if parse_iso(m["utcDate"]).astimezone(TZ).date() == today]
    if not matches:
        return []
    table = await get_table(code)
    form = await get_form(code)
    cards = []
    for m in matches[:limit]:
        odds = await football_odds(code, m["homeTeam"]["name"], m["awayTeam"]["name"], m["utcDate"])
        text, picks = football_card(m, table, form, code, odds)
        if picks:
            record_predictions("football", code, str(m["id"]), m["homeTeam"]["name"],
                               m["awayTeam"]["name"], m["utcDate"], picks)
        cards.append(text)
    return cards


# ======================================================================
# Теннис (неофициальный API ESPN, ключ не нужен)
# ======================================================================
async def espn_get(path: str) -> dict:
    async with httpx.AsyncClient(timeout=20) as client:
        r = await client.get(f"{ESPN}{path}")
        r.raise_for_status()
        return r.json()


def _singles(ev: dict) -> list:
    comps = []
    for g in ev.get("groupings", []):
        title = (g.get("grouping") or {}).get("displayName", "").lower()
        if "singles" in title:
            comps += g.get("competitions", [])
    if not ev.get("groupings"):
        comps += ev.get("competitions", [])
    return comps


async def get_tennis_rankings(tour: str) -> dict:
    data = await espn_get(f"/{tour}/rankings")
    ranks = {}
    for block in data.get("rankings", []):
        for row in block.get("ranks", []):
            name = (row.get("athlete") or {}).get("displayName")
            if name:
                ranks[name] = {"rank": row.get("current"), "points": row.get("points")}
    return ranks


async def get_tennis_matches(tour: str) -> list:
    data = await espn_get(f"/{tour}/scoreboard")
    result = []
    for ev in data.get("events", []):
        for c in _singles(ev):
            state = ((c.get("status") or {}).get("type") or {}).get("state")
            if state != "pre":
                continue
            names = [(x.get("athlete") or {}).get("displayName") for x in c.get("competitors", [])]
            if len(names) == 2 and all(names):
                result.append((names[0], names[1], c.get("date") or c.get("startDate") or "",
                               ev.get("name", "")))
    return result


async def get_tennis_form(tour: str, days: int = 14) -> dict:
    today = datetime.now(TZ).date()
    rng = f"{today - timedelta(days=days):%Y%m%d}-{today:%Y%m%d}"
    try:
        data = await espn_get(f"/{tour}/scoreboard?dates={rng}")
    except httpx.HTTPError:
        return {}
    results: dict = {}
    for ev in data.get("events", []):
        for c in _singles(ev):
            state = ((c.get("status") or {}).get("type") or {}).get("state")
            if state != "post":
                continue
            for x in c.get("competitors", []):
                name = (x.get("athlete") or {}).get("displayName")
                if name:
                    results.setdefault(name, []).append(bool(x.get("winner")))
    return results


def predict_tennis(r1, r2, f1=None, f2=None):
    if not r1 or not r2:
        return None
    pts1, pts2 = _num(r1.get("points")), _num(r2.get("points"))
    if pts1 and pts2:
        diff, k = math.log(pts1) - math.log(pts2), 1.1
    else:
        a, b = _num(r1.get("rank")), _num(r2.get("rank"))
        if not a or not b:
            return None
        diff, k = math.log(b) - math.log(a), 0.4
    logit = k * diff
    if f1 and f2 and len(f1) >= 2 and len(f2) >= 2:
        logit += TENNIS_FORM_K * (sum(f1) / len(f1) - sum(f2) / len(f2))
    return 1 / (1 + math.exp(-logit))


def tennis_form_icons(f) -> str:
    return "".join("🟢" if w else "🔴" for w in f[-5:]) if f else "н/д"


def tennis_card(p1, p2, when, tournament, prob, r1, r2, f1, f2, odds, code):
    fav_is_1 = prob >= 0.5
    fav, fav_p = (p1, prob) if fav_is_1 else (p2, 1 - prob)
    fav_key = "home" if fav_is_1 else "away"
    o1, o2 = odd_of(odds, "home"), odd_of(odds, "away")

    pre = []
    for name, pr, o in ((p1, prob, o1), (p2, 1 - prob, o2)):
        pre.append(f"{short_name(name):<11} {bar(pr, 8)} {pr * 100:>3.0f}%"
                   + (f"  {o[0]:.2f}" if o else ""))
    lines = [
        f"🎾 <b>{esc(p1)} — {esc(p2)}</b>",
        f"🏟 {esc(tournament)} · 🕒 {local_time(when)}",
        "",
        f"Рейтинг: #{r1.get('rank')} │ #{r2.get('rank')}",
        f"Форма: {tennis_form_icons(f1)} │ {tennis_form_icons(f2)}",
        "", "<b>Победа</b> · модель" + (" │ лучший кф" if odds else ""),
        "<pre>" + "\n".join(pre) + "</pre>",
        "📌 <b>Прогноз</b>",
        pick_line("Победитель", fav, fav_p, odd_of(odds, fav_key),
                  (odds or {}).get("prob", {}).get(fav_key)),
    ]
    note = odds_footnote(odds)
    if note:
        lines.append(note)
    pick = dict(market="WIN", pick="1" if fav_is_1 else "2", label=fav, prob=fav_p,
                odd=odd_of(odds, fav_key))
    return "\n".join(lines), [pick]


async def tennis_texts(code: str, limit: int = 6) -> list:
    tour = TENNIS[code]
    ranks = await get_tennis_rankings(tour)
    matches = await get_tennis_matches(tour)
    forms = await get_tennis_form(tour)

    rows = []
    for p1, p2, when, tournament in matches:
        r1, r2 = ranks.get(p1), ranks.get(p2)
        prob = predict_tennis(r1, r2, forms.get(p1), forms.get(p2))
        if prob is None:
            continue
        score = (_num(r1.get("rank")) or 999) + (_num(r2.get("rank")) or 999)
        rows.append((score, p1, p2, when, tournament, prob, r1, r2))
    rows.sort(key=lambda x: x[0])
    rows = rows[:limit]
    if not rows:
        return []

    pack = await tennis_odds_events(tour) if ODDS_ENABLED else None
    texts = []
    for _, p1, p2, when, tournament, prob, r1, r2 in rows:
        odds = tennis_odds(pack, p1, p2, when)
        text, picks = tennis_card(p1, p2, when, tournament, prob, r1, r2,
                                  forms.get(p1), forms.get(p2), odds, code)
        record_predictions("tennis", code, f"{(to_utc_iso(when) or '')[:10]}|{p1}|{p2}",
                           p1, p2, when, picks)
        texts.append(text)
    return texts


# ======================================================================
# Учёт прогнозов: хранение и автоматическая проверка результатов
# ======================================================================
def db_exec(sql: str, args=()) -> None:
    with closing(sqlite3.connect(DB_FILE)) as conn, conn:
        conn.execute(sql, args)


def db_all(sql: str, args=()) -> list:
    with closing(sqlite3.connect(DB_FILE)) as conn:
        conn.row_factory = sqlite3.Row
        return [dict(r) for r in conn.execute(sql, args).fetchall()]


def init_db() -> None:
    db_exec("""CREATE TABLE IF NOT EXISTS predictions(
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        sport TEXT NOT NULL, comp TEXT NOT NULL, match_key TEXT NOT NULL,
        home TEXT, away TEXT, kickoff TEXT NOT NULL,
        market TEXT NOT NULL, pick TEXT NOT NULL, pick_label TEXT,
        prob REAL, odds REAL, bookmaker TEXT,
        created_at TEXT, status TEXT DEFAULT 'pending', result TEXT, settled_at TEXT,
        UNIQUE(sport, match_key, market))""")


def record_predictions(sport, comp, match_key, home, away, kickoff_iso, picks) -> None:
    """Фиксирует прогноз при ПЕРВОМ показе и до начала матча. Повторные показы
    (INSERT OR IGNORE) прогноз не перезаписывают — задним числом статистику не подправить."""
    k = to_utc_iso(kickoff_iso)
    if not k or k <= now_utc_iso():
        return
    for p in picks:
        odd = p.get("odd")
        db_exec(
            "INSERT OR IGNORE INTO predictions(sport,comp,match_key,home,away,kickoff,market,"
            "pick,pick_label,prob,odds,bookmaker,created_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (sport, comp, match_key, home, away, k, p["market"], p["pick"], p["label"],
             p["prob"], odd[0] if odd else None, odd[1] if odd else None, now_utc_iso()))


def set_status(row_id: int, status: str, result: str) -> None:
    db_exec("UPDATE predictions SET status=?, result=?, settled_at=? WHERE id=?",
            (status, result, now_utc_iso(), row_id))


def score_90(m: dict):
    """Счёт за основное время (рынки БК считаются по 90 минутам). В API v4 при
    доп. времени/пенальти fullTime включает их, поэтому берём regularTime."""
    sc = m.get("score") or {}
    src = sc.get("fullTime") or {}
    if sc.get("duration") in ("EXTRA_TIME", "PENALTY_SHOOTOUT"):
        src = sc.get("regularTime") or {}
    h, a = src.get("home"), src.get("away")
    return (h, a) if h is not None and a is not None else None


def eval_football(market: str, pick: str, hg: int, ag: int) -> bool:
    if market == "1X2":
        return pick == ("1" if hg > ag else "X" if hg == ag else "2")
    if market == "TOTAL25":
        return (hg + ag >= 3) == (pick == "over")
    return (hg >= 1 and ag >= 1) == (pick == "yes")  # BTTS


def _older_than(kickoff: str, days: int) -> bool:
    dt = parse_iso(kickoff)
    return bool(dt) and datetime.now(timezone.utc) - dt > timedelta(days=days)


async def _settle_football(rows: list) -> None:
    by_comp: dict = {}
    for r in rows:
        by_comp.setdefault(r["comp"], []).append(r)
    for comp, rs in by_comp.items():
        try:
            data = await api_get(f"/competitions/{comp}/matches", {"status": "FINISHED"}, ttl=600)
        except Exception as e:
            log.warning("Проверка результатов %s: %s", comp, e)
            continue
        finished = {str(m["id"]): m for m in data["matches"]}
        for r in rs:
            m = finished.get(r["match_key"])
            if m:
                sc = score_90(m)
                if sc is None:
                    set_status(r["id"], "void", "нет счёта за 90 минут")
                else:
                    win = eval_football(r["market"], r["pick"], *sc)
                    set_status(r["id"], "win" if win else "loss", f"{sc[0]}:{sc[1]}")
            elif _older_than(r["kickoff"], 5):
                set_status(r["id"], "void", "результат не получен (перенос/отмена)")


async def _tennis_results(tour: str, day: datetime) -> list:
    """[(имя1, имя2, имя_победителя)] завершённых матчей вокруг даты."""
    a, b = day - timedelta(days=1), day + timedelta(days=1)
    data = await espn_get(f"/{tour}/scoreboard?dates={a:%Y%m%d}-{b:%Y%m%d}")
    out = []
    for ev in data.get("events", []):
        for c in _singles(ev):
            if ((c.get("status") or {}).get("type") or {}).get("state") != "post":
                continue
            comps = c.get("competitors", [])
            names = [(x.get("athlete") or {}).get("displayName") for x in comps]
            winners = [n for n, x in zip(names, comps) if x.get("winner")]
            if len(names) == 2 and all(names) and len(winners) == 1:
                out.append((names[0], names[1], winners[0]))
    return out


async def _settle_tennis(rows: list) -> None:
    by_comp: dict = {}
    for r in rows:
        by_comp.setdefault(r["comp"], []).append(r)
    for comp, rs in by_comp.items():
        tour = TENNIS[comp]
        cache: dict = {}
        for r in rs[:60]:
            day = parse_iso(r["kickoff"])
            dkey = day.date()
            if dkey not in cache:
                try:
                    cache[dkey] = await _tennis_results(tour, day)
                except Exception as e:
                    log.warning("Проверка тенниса %s: %s", comp, e)
                    cache[dkey] = None
            results = cache[dkey]
            if results is None:
                continue
            hit = next((w for a, b, w in results
                        if (same_player(a, r["home"]) and same_player(b, r["away"]))
                        or (same_player(a, r["away"]) and same_player(b, r["home"]))), None)
            if hit:
                picked = r["home"] if r["pick"] == "1" else r["away"]
                set_status(r["id"], "win" if same_player(hit, picked) else "loss", f"победил {hit}")
            elif _older_than(r["kickoff"], 7):
                set_status(r["id"], "void", "результат не получен (снятие/перенос)")


_settle_lock = asyncio.Lock()
_last_settle = 0.0


async def settle_all(force: bool = False) -> None:
    global _last_settle
    async with _settle_lock:
        if not force and time.time() - _last_settle < 600:
            return
        _last_settle = time.time()
        cutoff = (datetime.now(timezone.utc) - timedelta(hours=2)).isoformat(timespec="seconds")
        rows = db_all("SELECT * FROM predictions WHERE status='pending' AND kickoff <= ?", (cutoff,))
        if not rows:
            return
        await _settle_football([r for r in rows if r["sport"] == "football"])
        await _settle_tennis([r for r in rows if r["sport"] == "tennis"])


async def settle_job(context: ContextTypes.DEFAULT_TYPE):
    try:
        await settle_all(force=True)
    except Exception as e:
        log.warning("Ошибка проверки результатов: %s", e)


# ======================================================================
# Статистика
# ======================================================================
MARKET_NAMES = {"1X2": "Исход 1X2", "TOTAL25": "Тотал 2.5", "BTTS": "Обе забьют",
                "WIN": "Теннис: победитель"}
PERIOD_NAMES = {"7": "7 дней", "30": "30 дней", "all": "всё время"}
SPORT_NAMES = {"all": "всё", "football": "⚽ футбол", "tennis": "🎾 теннис"}


def _rate(rows: list) -> str:
    n = len(rows)
    w = sum(1 for r in rows if r["status"] == "win")
    return f"{w / n * 100:.0f}% ({w}/{n})" if n else "—"


def render_stats(period: str = "all", sport: str = "all") -> str:
    where, args = ["status IN ('win','loss')"], []
    if period != "all":
        since = (datetime.now(timezone.utc) - timedelta(days=int(period))).isoformat(timespec="seconds")
        where.append("kickoff >= ?")
        args.append(since)
    if sport != "all":
        where.append("sport = ?")
        args.append(sport)
    rows = db_all(f"SELECT * FROM predictions WHERE {' AND '.join(where)} ORDER BY kickoff DESC", args)

    sport_sql, sport_args = ("AND sport = ?", [sport]) if sport != "all" else ("", [])
    pending = db_all(f"SELECT COUNT(*) c FROM predictions WHERE status='pending' {sport_sql}", sport_args)[0]["c"]
    void = db_all(f"SELECT COUNT(*) c FROM predictions WHERE status='void' {sport_sql}", sport_args)[0]["c"]

    out = [f"📈 <b>Статистика прогнозов</b>",
           f"<i>{PERIOD_NAMES[period]} · {SPORT_NAMES[sport]}</i>", ""]
    if not rows:
        out.append("Пока нет проверенных прогнозов за этот период.")
        if pending:
            out.append(f"⏳ Ждут результата: {pending}")
        out.append("\nПрогнозы попадают в статистику после первого показа и окончания матча.")
        return "\n".join(out)

    n = len(rows)
    w = sum(1 for r in rows if r["status"] == "win")
    acc = w / n
    ci = 1.96 * math.sqrt(acc * (1 - acc) / n)
    avg_p = sum(r["prob"] for r in rows) / n

    out += [
        f"✅ Зашло: <b>{w}</b>   ❌ Не зашло: <b>{n - w}</b>   (всего {n})",
        f"Точность: <b>{acc * 100:.0f}%</b> ±{ci * 100:.0f} п.п.",
        f"<code>{bar(acc, 20)}</code>",
        f"Средняя уверенность модели: {avg_p * 100:.0f}%",
    ]
    if n < MIN_SAMPLE_WARN:
        out.append(f"⚠️ Выборка мала (меньше {MIN_SAMPLE_WARN}) — выводы пока ненадёжны.")
    elif avg_p - acc > 0.05:
        out.append("↳ модель переоценивает себя: уверенность выше фактической точности.")
    elif acc - avg_p > 0.05:
        out.append("↳ модель осторожна: фактическая точность выше заявленной.")
    else:
        out.append("↳ уверенность модели близка к фактической точности.")

    out += ["", "<b>По рынкам</b>"]
    for mk, name in MARKET_NAMES.items():
        sub = [r for r in rows if r["market"] == mk]
        if sub:
            out.append(f"• {name}: {_rate(sub)}")

    comps = [c for c in LEAGUES if any(r["comp"] == c for r in rows)]
    if len(comps) > 1:
        out += ["", "<b>По турнирам</b>"]
        for c in comps:
            out.append(f"• {esc(LEAGUES[c])}: {_rate([r for r in rows if r['comp'] == c])}")

    out += ["", "<b>По уверенности модели</b>"]
    for lo, hi, name in ((0, .5, "до 50%"), (.5, .6, "50–59%"), (.6, .7, "60–69%"), (.7, 1.01, "70%+")):
        sub = [r for r in rows if lo <= r["prob"] < hi]
        if sub:
            out.append(f"• {name}: {_rate(sub)}")

    with_odds = [r for r in rows if r["odds"]]
    if with_odds:
        profit = sum((r["odds"] - 1) if r["status"] == "win" else -1 for r in with_odds)
        roi = profit / len(with_odds)
        avg_odd = sum(r["odds"] for r in with_odds) / len(with_odds)
        out += ["", "💰 <b>С коэффициентами</b>",
                f"{len(with_odds)} прогнозов с известным кф (средний {avg_odd:.2f}).",
                f"Условно по 1 ед. на каждый: <b>{profit:+.1f} ед.</b>, ROI <b>{roi:+.1%}</b>",
                "<i>кф взяты на момент первого показа прогноза</i>"]

    out += ["", "<b>Последние результаты</b>"]
    for r in rows[:6]:
        icon = "✅" if r["status"] == "win" else "❌"
        out.append(f"{icon} {esc(r['home'])} — {esc(r['away'])} · {esc(r['pick_label'])} · "
                   f"{esc(r['result'])}")

    tail = []
    if pending:
        tail.append(f"⏳ Ждут результата: {pending}")
    if void:
        tail.append(f"Аннулировано (не в статистике): {void}")
    out += [""] + tail + [
        "<i>Прогноз фиксируется при первом показе, до матча, и потом не меняется. "
        "Рынки считаются по основному времени. Карточки не учитываются — нет "
        "проверяемых данных.</i>"]
    return "\n".join(out)


def stats_keyboard(period: str, sport: str) -> InlineKeyboardMarkup:
    def mark(cur, val, label):
        return ("• " if cur == val else "") + label
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(mark(period, p, PERIOD_NAMES[p].capitalize()),
                              callback_data=f"st:{p}:{sport}") for p in ("7", "30", "all")],
        [InlineKeyboardButton(mark(sport, s, SPORT_NAMES[s].capitalize()),
                              callback_data=f"st:{period}:{s}") for s in ("all", "football", "tennis")],
        [InlineKeyboardButton("⬅️ Меню", callback_data="menu")],
    ])


# ======================================================================
# Рассылка: подписчики и ежедневный дайджест
# ======================================================================
def load_subs() -> dict:
    try:
        with open(SUBS_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_subs(subs: dict) -> None:
    with open(SUBS_FILE, "w", encoding="utf-8") as f:
        json.dump(subs, f, ensure_ascii=False, indent=2)


def footer() -> str:
    s = ("ℹ️ Вероятности — статистическая модель, а не гарантия результата.")
    if ODDS_ENABLED:
        s += ("\n💎 value = модель оценивает исход выше рынка (вероятность × кф − 1). "
              "Рынок обычно точнее простой модели — относитесь как к подсказке.")
    s += "\n🔞 18+. Играйте ответственно."
    return s


async def build_digest() -> list:
    messages = []
    for code, name in LEAGUES.items():
        try:
            if code in TENNIS:
                texts = await tennis_texts(code, limit=3)
            elif code == "CL":
                texts = await football_texts(code, days=1, limit=8, only_today=True)
            else:
                texts = await football_texts(code, days=1, limit=3, only_today=True)
        except Exception as e:
            log.warning("Дайджест: ошибка в %s: %s", code, e)
            continue
        if texts:
            messages += chunk_messages(f"<b>{esc(name)}</b>", texts)
    return messages


async def send_digest(bot, chat_id: int) -> None:
    messages = await build_digest()
    if not messages:
        await bot.send_message(chat_id, "Сегодня топ-матчей с прогнозами не нашлось.")
        return
    await bot.send_message(chat_id, "☀️ <b>Прогнозы на сегодня</b>", parse_mode=ParseMode.HTML)
    for text in messages:
        await bot.send_message(chat_id, text, parse_mode=ParseMode.HTML)
    await bot.send_message(chat_id, footer(), reply_markup=main_keyboard())


async def daily_job(context: ContextTypes.DEFAULT_TYPE):
    chat_id = context.job.chat_id
    try:
        await send_digest(context.bot, chat_id)
    except Forbidden:
        subs = load_subs()
        subs.pop(str(chat_id), None)
        save_subs(subs)
        context.job.schedule_removal()
    except Exception as e:
        log.warning("Не удалось отправить дайджест %s: %s", chat_id, e)


def schedule(job_queue, chat_id: int, hhmm: str) -> None:
    for j in job_queue.get_jobs_by_name(str(chat_id)):
        j.schedule_removal()
    h, m = map(int, hhmm.split(":"))
    job_queue.run_daily(daily_job, time=dtime(h, m, tzinfo=TZ), chat_id=chat_id, name=str(chat_id))


async def post_init(app: Application):
    init_db()
    for chat_id, hhmm in load_subs().items():
        schedule(app.job_queue, int(chat_id), hhmm)
    app.job_queue.run_repeating(settle_job, interval=1800, first=90, name="settle")
    await app.bot.set_my_commands([
        BotCommand("start", "Меню"),
        BotCommand("digest", "Прогнозы на сегодня"),
        BotCommand("stats", "Статистика прогнозов"),
        BotCommand("subscribe", "Ежедневная рассылка"),
        BotCommand("unsubscribe", "Отключить рассылку"),
        BotCommand("help", "Справка"),
    ])
    log.info("Восстановлено подписок: %d; кф: %s", len(load_subs()),
             "включены" if ODDS_ENABLED else "выключены (нет ODDS_API_KEY)")


# ======================================================================
# Хендлеры
# ======================================================================
def main_keyboard() -> InlineKeyboardMarkup:
    items = list(LEAGUES.items())
    rows = [[InlineKeyboardButton(n, callback_data=f"lg:{c}") for c, n in items[i:i + 2]]
            for i in range(0, len(items), 2)]
    rows.append([InlineKeyboardButton("☀️ Сегодня", callback_data="dg"),
                 InlineKeyboardButton("📈 Статистика", callback_data="st:all:all")])
    return InlineKeyboardMarkup(rows)


START_TEXT = (
    "👋 <b>Привет! Я даю статистические прогнозы на футбол и теннис.</b>\n\n"
    "⚽ Исход, двойной шанс, тотал 2.5, «обе забьют», счёт и xG\n"
    "🎾 Вероятность победы по рейтингу и форме\n"
    "💰 Коэффициенты БК рядом с прогнозом\n"
    "📈 Честная статистика: сколько прогнозов зашло, а сколько нет\n\n"
    "Выберите турнир или подпишитесь на рассылку: /subscribe"
)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(START_TEXT, reply_markup=main_keyboard(), parse_mode=ParseMode.HTML)


async def menu_cb(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.edit_message_text(START_TEXT, reply_markup=main_keyboard(), parse_mode=ParseMode.HTML)


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    odds_line = (
        "💰 <b>Коэффициенты</b>: берутся из The Odds API, показан лучший кф среди БК и название "
        "букмекера, рядом — консенсус-вероятность рынка без маржи и «справедливый» кф модели. "
        "Есть только для исхода 1X2, тотала 2.5 и победителя в теннисе. Если данных нет — "
        "пишем «н/д», ничего не придумываем."
        if ODDS_ENABLED else
        "💰 Коэффициенты сейчас выключены (не задан ODDS_API_KEY)."
    )
    await update.message.reply_text(
        "<b>Команды</b>\n"
        "/start — меню турниров\n"
        "/digest — прогнозы на сегодня\n"
        "/stats — статистика прогнозов\n"
        "/subscribe 09:00 — рассылка в указанное время\n"
        "/unsubscribe — отключить рассылку\n\n"
        f"Время указывается по поясу {esc(TZ.key)}.\n\n"
        "<b>Как это считается</b>\n"
        "Модель Пуассона + форма (общая и дом/гостевая). Жёлтые карточки — грубая оценка "
        "(у бесплатного API нет статистики), в учёт не идут.\n\n"
        "<b>Как считается статистика</b>\n"
        "Прогноз фиксируется при первом показе, до матча, и потом не меняется. После матча "
        "бот сам сверяет результат (рынки — по основному времени). Мало прогнозов — мало "
        "смысла: бот предупреждает о малой выборке.\n\n"
        f"{odds_line}\n\n"
        "⚠️ Не финансовый совет. 🔞 18+. Играйте ответственно.",
        parse_mode=ParseMode.HTML,
    )


async def subscribe(update: Update, context: ContextTypes.DEFAULT_TYPE):
    hhmm = context.args[0] if context.args else DEFAULT_DIGEST_TIME
    if not re.fullmatch(r"([01]?\d|2[0-3]):[0-5]\d", hhmm):
        await update.message.reply_text("Формат времени: /subscribe 09:00")
        return
    h, m = hhmm.split(":")
    hhmm = f"{int(h):02d}:{m}"
    chat_id = update.effective_chat.id
    subs = load_subs()
    subs[str(chat_id)] = hhmm
    save_subs(subs)
    schedule(context.application.job_queue, chat_id, hhmm)
    await update.message.reply_text(
        f"✅ Готово! Каждый день в <b>{hhmm}</b> ({esc(TZ.key)}) пришлю прогнозы.\n"
        "Отключить: /unsubscribe", parse_mode=ParseMode.HTML)


async def unsubscribe(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    subs = load_subs()
    if subs.pop(str(chat_id), None) is None:
        await update.message.reply_text("Вы не были подписаны.")
        return
    save_subs(subs)
    for j in context.application.job_queue.get_jobs_by_name(str(chat_id)):
        j.schedule_removal()
    await update.message.reply_text("Рассылка отключена.")


async def digest_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("⏳ Собираю прогнозы на сегодня, это может занять до минуты…")
    await send_digest(context.bot, update.effective_chat.id)


async def digest_cb(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    await q.message.reply_text("⏳ Собираю прогнозы на сегодня, это может занять до минуты…")
    await send_digest(context.bot, q.message.chat_id)


async def stats_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        await settle_all()
    except Exception as e:
        log.warning("settle перед статистикой: %s", e)
    await update.message.reply_text(render_stats("all", "all"), parse_mode=ParseMode.HTML,
                                    reply_markup=stats_keyboard("all", "all"))


async def stats_cb(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    _, period, sport = q.data.split(":")
    if period not in PERIOD_NAMES or sport not in SPORT_NAMES:
        return
    try:
        await settle_all()
    except Exception as e:
        log.warning("settle перед статистикой: %s", e)
    try:
        await q.edit_message_text(render_stats(period, sport), parse_mode=ParseMode.HTML,
                                  reply_markup=stats_keyboard(period, sport))
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise


async def league_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    code = q.data.split(":", 1)[1]
    if code not in LEAGUES:
        return
    await q.edit_message_text(f"⏳ Загружаю матчи: {LEAGUES[code]}… (до 30 секунд)")
    try:
        if code in TENNIS:
            texts = await tennis_texts(code, 6)
        elif code == "CL":
            texts = await football_texts(code, days=14, limit=16)
        else:
            texts = await football_texts(code, 7, 6)
    except Exception as e:
        log.warning("Ошибка загрузки %s: %s", code, e)
        await q.edit_message_text(f"😕 Не получилось получить данные: {e}",
                                  reply_markup=main_keyboard())
        return
    if not texts:
        await q.edit_message_text("Ближайших матчей с достаточными данными нет.",
                                  reply_markup=main_keyboard())
        return
    chunks = chunk_messages(f"<b>{esc(LEAGUES[code])}</b> — ближайшие матчи", texts)
    await q.edit_message_text(chunks[0], parse_mode=ParseMode.HTML)
    for c in chunks[1:]:
        await q.message.reply_text(c, parse_mode=ParseMode.HTML)
    await q.message.reply_text(footer(), reply_markup=main_keyboard())


def main():
    app = Application.builder().token(TELEGRAM_TOKEN).post_init(post_init).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("subscribe", subscribe))
    app.add_handler(CommandHandler("unsubscribe", unsubscribe))
    app.add_handler(CommandHandler("digest", digest_cmd))
    app.add_handler(CommandHandler("stats", stats_cmd))
    app.add_handler(CallbackQueryHandler(league_chosen, pattern=r"^lg:"))
    app.add_handler(CallbackQueryHandler(digest_cb, pattern=r"^dg$"))
    app.add_handler(CallbackQueryHandler(stats_cb, pattern=r"^st:"))
    app.add_handler(CallbackQueryHandler(menu_cb, pattern=r"^menu$"))
    app.run_polling()


if __name__ == "__main__":
    main()
