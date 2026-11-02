"""
Телеграм-бот с прогнозами на футбол и теннис: учёт формы + ежедневная рассылка.

Что умеет (футбол):
  • исход (П1/Х/П2) и двойные шансы — модель Пуассона + форма (общая и дом/гостевая);
  • тотал голов 2.5 (ТБ/ТМ), «обе забьют» (да/нет), вероятный счёт и xG;
  • оценка жёлтых карточек (модель по средним лиги и характеру матча —
    у бесплатного API нет статистики карточек, это оценка, не точные данные);
  • Лига чемпионов — все матчи тура в полном объёме, прогнозы даже без
    турнирной таблицы (сила команды оценивается по форме).

Установка:
    pip install "python-telegram-bot[job-queue]" httpx tzdata

Переменные окружения:
    TELEGRAM_TOKEN   - токен от @BotFather
    FOOTBALL_API_KEY - бесплатный ключ с https://www.football-data.org/client/register
    BOT_TZ           - (необязательно) ваш часовой пояс, по умолчанию Europe/Moscow

Запуск:
    python bot.py
"""
import os
import re
import json
import math
import time
import asyncio
import logging
from datetime import date, datetime, timedelta, time as dtime
from zoneinfo import ZoneInfo

import httpx
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.error import Forbidden
from telegram.ext import (
    Application, CallbackQueryHandler, CommandHandler, ContextTypes,
)

TELEGRAM_TOKEN = "9135746215:AAEL7EGJIY4FGIzE0BgCDMZjteizVm4Wb5Q"
FOOTBALL_API_KEY = os.environ["FOOTBALL_API_KEY"]
TZ = ZoneInfo(os.environ.get("BOT_TZ", "Europe/Moscow"))
SUBS_FILE = "subscribers.json"
DEFAULT_DIGEST_TIME = "09:00"

FOOTBALL_API = "https://api.football-data.org/v4"
ESPN = "https://site.api.espn.com/apis/site/v2/sports/tennis"

LEAGUES = {
    "CL": "🏆 Лига чемпионов",
    "PL": "🏴 АПЛ",
    "PD": "🇪🇸 Ла Лига",
    "SA": "🇮🇹 Серия A",
    "BL1": "🇩🇪 Бундеслига",
    "FL1": "🇫🇷 Лига 1",
    "ATP": "🎾 Теннис ATP (мужчины)",
    "WTA": "🎾 Теннис WTA (женщины)",
}
TENNIS = {"ATP": "atp", "WTA": "wta"}

# Средний тотал жёлтых карточек в матче (по лигам, оценочно).
# У бесплатного API football-data.org статистики карточек нет —
# используем как базу оценочной модели.
LEAGUE_CARD_AVG = {"CL": 4.1, "PL": 3.8, "PD": 5.0, "SA": 4.5, "BL1": 3.9, "FL1": 3.9}
DEFAULT_CARD_AVG = 4.0
KNOCKOUT_CARD_BONUS = 0.5   # плей-офф ЛЧ — накал выше
GLOBAL_AVG_GOALS = 2.6      # запасной средний тотал, если таблицы ещё нет (старт сезона/ЛЧ)

FORM_WEIGHT = 0.35          # вклад формы (последние 5 матчей) в оценку силы команды
SPLIT_WEIGHT = 0.5          # вклад домашней/гостевой формы (если есть >=3 матча)
TENNIS_FORM_K = 0.6         # вклад формы теннисиста в логит победы

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("sportbot")


# ======================================================================
# Вспомогательное
# ======================================================================
def local_time(iso: str) -> str:
    try:
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
        return dt.astimezone(TZ).strftime("%d.%m %H:%M") + f" ({TZ.key})"
    except (ValueError, AttributeError):
        return iso[:16].replace("T", " ")


def _num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def ordinal(n) -> str:
    if n is None:
        return "н/д"
    n = int(n)
    if 10 <= n % 100 <= 20:
        suf = "-е"
    else:
        suf = {1: "-е", 2: "-е", 3: "-е", 4: "-е"}.get(n % 10, "-е")
    return f"{n}{suf}"


# ======================================================================
# Футбол: API с кэшем и ограничением частоты (бесплатно 10 запросов/мин)
# ======================================================================
_cache: dict = {}
_lock = asyncio.Lock()
_last_call = 0.0
MIN_INTERVAL = 6.5
CACHE_TTL = 1800


async def api_get(path: str, params: dict | None = None) -> dict:
    global _last_call
    key = (path, tuple(sorted((params or {}).items())))
    hit = _cache.get(key)
    if hit and time.time() - hit[0] < CACHE_TTL:
        return hit[1]
    async with _lock:
        hit = _cache.get(key)
        if hit and time.time() - hit[0] < CACHE_TTL:
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
    today = date.today()
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
    """{team_id: {"all": [(gf, ga), ...], "home": [...], "away": [...]}}
    за последние n сыгранных матчей турнира."""
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
    return f"{pts}/{len(results) * 3}"


def avg_goals(results) -> tuple:
    if not results:
        return None, None
    return (sum(g for g, _ in results) / len(results),
            sum(c for _, c in results) / len(results))


# ======================================================================
# Футбол: модель Пуассона + форма (общая и домашняя/гостевая)
# ======================================================================
def poisson(k: int, lam: float) -> float:
    return math.exp(-lam) * lam**k / math.factorial(k)


def _form_rates(f: dict, avg: float):
    """(атака, защита) из формы относительно среднего по лиге."""
    all_, home, away = f.get("all", []), f.get("home", []), f.get("away", [])
    if not all_:
        return None
    att = sum(g for g, _ in all_) / len(all_) / avg
    dfn = sum(c for _, c in all_) / len(all_) / avg
    return att, dfn, home, away


def predict(home: dict, away: dict, table: dict, form: dict, code: str, stage: str = ""):
    """Возвращает dict с вероятностями или None, если данных совсем нет.

    Если турнирной таблицы ещё нет (старт сезона, ЛЧ) — сила команд
    оценивается только по форме, средний тотал берём глобальный.
    """
    hid = home.get("id") or (home.get("team") or {}).get("id")
    aid = away.get("id") or (away.get("team") or {}).get("id")
    fh = form.get(hid)
    fa = form.get(aid)
    if not fh or not fa or len(fh["all"]) < 2 or len(fa["all"]) < 2:
        return None

    total_games = sum(t["playedGames"] for t in table.values())
    use_table = bool(total_games) and home.get("playedGames", 0) >= 3 and away.get("playedGames", 0) >= 3
    if use_table:
        avg = sum(t["goalsFor"] for t in table.values()) / total_games
    else:
        avg = GLOBAL_AVG_GOALS

    def strength(t, f, is_home_team: bool):
        """(атака, защита) относительно среднего: сезон смешивается с формой;
        домашняя/гостевая сплит-форма добавляет поправку."""
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

    # --- Жёлтые карточки: оценочная модель (статистики карточек в API нет) ---
    cards = LEAGUE_CARD_AVG.get(code, DEFAULT_CARD_AVG)
    if "KNOCKOUT" in (stage or "").upper() or "LAST" in (stage or "").upper() or "QUARTER" in (stage or "").upper() or "SEMI" in (stage or "").upper() or "FINAL" in (stage or "").upper():
        cards += KNOCKOUT_CARD_BONUS
    fav_gap = abs(p_home - p_away)
    cards += 0.3 * (1 - fav_gap)          # равный матч — плотная борьба
    cards = max(2.5, min(6.5, cards))
    p_cards_over35 = 1 - sum(poisson(k, cards) for k in range(4))
    p_cards_over45 = 1 - sum(poisson(k, cards) for k in range(5))

    return {
        "home": p_home, "draw": p_draw, "away": p_away,
        "dc_1x": p_home + p_draw, "dc_12": p_home + p_away, "dc_x2": p_draw + p_away,
        "btts": p_btts / s, "over25": p_over25 / s,
        "score": best, "xg": (xg_home, xg_away),
        "cards": cards, "cards_over35": p_cards_over35, "cards_over45": p_cards_over45,
        "table_used": use_table,
    }


def format_match(m: dict, table: dict, form: dict, code: str) -> str:
    h, a = m["homeTeam"], m["awayTeam"]
    text = f"⚽ *{h['name']} — {a['name']}*\n🕒 {local_time(m['utcDate'])}\n"

    fh, fa = form.get(h["id"]), form.get(a["id"])
    if fh and fa:
        hgf, hga = avg_goals(fh["all"])
        agf, aga = avg_goals(fa["all"])
        text += (
            f"Форма: {form_icons(fh['all'])} ({form_points(fh['all'])}) | "
            f"{form_icons(fa['all'])} ({form_points(fa['all'])})\n"
            f"Дома/в гостях: {form_icons(fh['home'])} | {form_icons(fa['away'])}\n"
            f"Голы (забито/пропущено в среднем): {hgf:.1f}/{hga:.1f} | {agf:.1f}/{aga:.1f}\n"
        )

    ht, at = table.get(h["id"]), table.get(a["id"])
    if ht and at:
        text += (f"Таблица: {ordinal(ht.get('position'))} ({ht.get('points')} очк.) | "
                 f"{ordinal(at.get('position'))} ({at.get('points')} очк.)\n")

    p = predict(ht or {"id": h["id"]}, at or {"id": a["id"]}, table, form, code,
                stage=m.get("stage", ""))
    if not p:
        return text + "Недостаточно данных для прогноза."

    top = max(("П1", p["home"]), ("Х", p["draw"]), ("П2", p["away"]), key=lambda x: x[1])
    btts_pick = "Да" if p["btts"] >= 0.5 else "Нет"
    total_pick = "ТБ 2.5" if p["over25"] >= 0.5 else "ТМ 2.5"
    cards_pick = "ТБ 3.5" if p["cards_over35"] >= 0.5 else "ТМ 3.5"
    text += (
        f"П1: {p['home']:.0%} | Х: {p['draw']:.0%} | П2: {p['away']:.0%}\n"
        f"Двойной шанс: 1X {p['dc_1x']:.0%} | 12 {p['dc_12']:.0%} | X2 {p['dc_x2']:.0%}\n"
        f"Тотал 2.5: ТБ {p['over25']:.0%} / ТМ {1 - p['over25']:.0%} → *{total_pick}*\n"
        f"Обе забьют: Да {p['btts']:.0%} / Нет {1 - p['btts']:.0%} → *{btts_pick}*\n"
        f"Карточки (оценка): ~{p['cards']:.1f}, ТБ 3.5: {p['cards_over35']:.0%}, "
        f"ТБ 4.5: {p['cards_over45']:.0%} → *{cards_pick}*\n"
        f"Вероятный счёт: {p['score'][0]}:{p['score'][1]} "
        f"(xG {p['xg'][0]:.1f}–{p['xg'][1]:.1f})\n"
        f"📌 Прогноз: *{top[0]}*"
    )
    if not p["table_used"]:
        text += "\n_(таблицы ещё нет — оценка по форме)_"
    return text


async def football_texts(code: str, days: int = 7, limit: int = 6, only_today: bool = False) -> list:
    matches = await get_matches(code, days)
    if only_today:
        today = datetime.now(TZ).date()
        matches = [
            m for m in matches
            if datetime.fromisoformat(m["utcDate"].replace("Z", "+00:00")).astimezone(TZ).date() == today
        ]
    if not matches:
        return []
    table = await get_table(code)
    form = await get_form(code)
    return [format_match(m, table, form, code) for m in matches[:limit]]


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
    """{игрок: [True/False, ...]} - победы/поражения в завершённых матчах за последние дни."""
    today = date.today()
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
    """Вероятность победы игрока 1: рейтинг (очки/место) + поправка на форму."""
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

    texts = []
    for _, p1, p2, when, tournament, prob, r1, r2 in rows[:limit]:
        fav, fav_p = (p1, prob) if prob >= 0.5 else (p2, 1 - prob)
        texts.append(
            f"🎾 *{p1}* (#{r1.get('rank')}) — *{p2}* (#{r2.get('rank')})\n"
            f"🏟 {tournament}\n🕒 {local_time(when)}\n"
            f"Форма: {tennis_form_icons(forms.get(p1))} | {tennis_form_icons(forms.get(p2))}\n"
            f"Шансы: {prob:.0%} / {1 - prob:.0%}\n"
            f"📌 Прогноз: *{fav}* ({fav_p:.0%})"
        )
    return texts


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


async def build_digest() -> list:
    """Список сообщений: по одному на турнир, где сегодня есть матчи.
    Лига чемпионов — все матчи дня в полном объёме."""
    messages = []
    for code, name in LEAGUES.items():
        try:
            if code in TENNIS:
                texts = await tennis_texts(code, limit=3)
            elif code == "CL":
                texts = await football_texts(code, days=1, limit=8, only_today=True)
            else:
                texts = await football_texts(code, days=1, limit=3, only_today=True)
        except Exception as e:  # один турнир не должен ломать всю рассылку
            log.warning("Дайджест: ошибка в %s: %s", code, e)
            continue
        if texts:
            messages.append(f"*{name}*\n\n" + "\n\n".join(texts))
    return messages


async def send_digest(bot, chat_id: int) -> None:
    messages = await build_digest()
    if not messages:
        await bot.send_message(chat_id, "Сегодня топ-матчей с прогнозами не нашлось.")
        return
    await bot.send_message(chat_id, "☀️ Прогнозы на сегодня:")
    for text in messages:
        await bot.send_message(chat_id, text, parse_mode="Markdown")
    await bot.send_message(chat_id, "⚠️ Прогнозы статистические, гарантий нет. "
                                    "Оценка карточек — приближённая (у API нет точной статистики).")


async def daily_job(context: ContextTypes.DEFAULT_TYPE):
    chat_id = context.job.chat_id
    try:
        await send_digest(context.bot, chat_id)
    except Forbidden:  # пользователь заблокировал бота
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


async def restore_jobs(app: Application):
    for chat_id, hhmm in load_subs().items():
        schedule(app.job_queue, int(chat_id), hhmm)
    log.info("Восстановлено подписок: %d", len(load_subs()))


# ======================================================================
# Хендлеры
# ======================================================================
def leagues_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[InlineKeyboardButton(name, callback_data=code)] for code, name in LEAGUES.items()]
    )


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Привет! Я даю статистические прогнозы на футбол и теннис с учётом формы.\n\n"
        "По футболу: исход, двойные шансы, тотал 2.5, «обе забьют», вероятный счёт "
        "и оценка жёлтых карточек. Лига чемпионов — все матчи тура.\n\n"
        "Выберите турнир или подпишитесь на ежедневную рассылку: /subscribe",
        reply_markup=leagues_keyboard(),
    )


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "/start — выбрать турнир\n"
        "/digest — прогнозы на сегодня прямо сейчас\n"
        "/subscribe 09:00 — ежедневная рассылка в указанное время\n"
        "/unsubscribe — отключить рассылку\n\n"
        f"Время указывается по поясу {TZ.key}.\n"
        "⚠️ Прогнозы строятся на статистической модели (Пуассон + форма, включая "
        "домашнюю/гостевую) и не гарантируют результат. Это не ставка и не финансовый совет.\n"
        "Жёлтые карточки — оценочная модель: у бесплатного API нет точной статистики "
        "карточек, значения приближённые."
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
        f"✅ Готово! Каждый день в {hhmm} ({TZ.key}) буду присылать прогнозы.\n"
        "Отключить: /unsubscribe"
    )


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
    await update.message.reply_text("Собираю прогнозы на сегодня, это может занять до минуты…")
    await send_digest(context.bot, update.effective_chat.id)


async def league_chosen(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    code = q.data
    await q.edit_message_text(f"Загружаю матчи: {LEAGUES[code]}… (до 30 секунд)")
    try:
        if code in TENNIS:
            texts = await tennis_texts(code, 6)
        elif code == "CL":
            # Лига чемпионов: весь тур в полном объёме (все запланированные матчи)
            texts = await football_texts(code, days=14, limit=16)
        else:
            texts = await football_texts(code, 7, 6)
    except httpx.HTTPError as e:
        await q.edit_message_text(f"Ошибка получения данных: {e}", reply_markup=leagues_keyboard())
        return
    if not texts:
        await q.edit_message_text("Ближайших матчей с достаточными данными нет.",
                                  reply_markup=leagues_keyboard())
        return
    await q.edit_message_text(f"{LEAGUES[code]} — ближайшие матчи:")
    for t in texts:
        await q.message.reply_text(t, parse_mode="Markdown")
    await q.message.reply_text("⚠️ Прогнозы статистические, гарантий нет. "
                               "Оценка карточек — приближённая.",
                               reply_markup=leagues_keyboard())


def main():
    app = Application.builder().token(TELEGRAM_TOKEN).post_init(restore_jobs).build()
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CommandHandler("subscribe", subscribe))
    app.add_handler(CommandHandler("unsubscribe", unsubscribe))
    app.add_handler(CommandHandler("digest", digest_cmd))
    app.add_handler(CallbackQueryHandler(league_chosen))
    app.run_polling()


if __name__ == "__main__":
    main()
