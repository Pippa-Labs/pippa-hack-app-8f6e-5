"""Nearest Sunshine: the nearest day-trip towns with sun in the next few hours.

Somebody asks "where's the nearest sunshine to London?" or "will it be sunny
in Brighton this afternoon?". The app works out where they start from (London
unless they say otherwise) and which hours they mean, asks Open-Meteo for the
hourly sunshine forecast of every town in `towns.json` in ONE request, and
answers with the three nearest towns that should see sun: distance, travel
time, hours of sun and temperature.

The shape never changes, whatever the app does:

    class App:
        manifest  -> the parsed manifest.yaml sitting next to this file
        handle(call) -> Result

Open-Meteo is free and needs no key, so this app has no `app_secrets`. Only
fixed coordinates from `towns.json` go into the request: nothing the person
typed ever leaves the app.
"""

from __future__ import annotations

import concurrent.futures
import difflib
import http.client
import json
import math
import re
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

from pippa_agentapp_sdk import (
    AgentAppError,
    Call,
    Manifest,
    Result,
    load_manifest_file,
    validate_manifest,
)

MANIFEST_PATH = Path(__file__).with_name("manifest.yaml")
#: Beside app.py, not in a folder: only the top level is deployed.
TOWNS_PATH = Path(__file__).with_name("towns.json")

#: The one address the app ever calls, written here in full.
FORECAST_API = "https://api.open-meteo.com/v1/forecast"
USER_AGENT = "pippa-agent-app-nearest-sunshine/0.1 (https://github.com/Pippa-Labs)"
#: One request, one try, six seconds: well inside the 20 seconds Pippa allows.
TIMEOUT_SECONDS = 6

#: Every town is in Great Britain, so "this afternoon" means UK afternoon,
#: wherever the person asking happens to be.
UK = ZoneInfo("Europe/London")

#: Central London (Charing Cross), the default start.
LONDON = {"name": "London", "lat": 51.5074, "lon": -0.1278}
LONDON_NAMES = {"london", "central london", "city of london", "greater london", "ldn", "london town"}
#: Words that mean "where I am" — the app is never told where that is, so
#: they mean the default start, London.
HERE_WORDS = {"me", "here", "near me", "nearby", "my location", "where i am", "home", "my area",
              "around here", "around me", "this area", "local", "my place"}

HOW_MANY = 3
#: "The next few hours".
DEFAULT_HOURS = 5
#: A town counts as sunny with sun for at least a fifth of the window, and at
#: least half an hour, but never more than half the window (25 minutes before
#: sunset, 15 minutes of sun is sunny).
SUNNY_SHARE = 0.2
SUNNY_HOURS_MIN = 0.5
#: An hour with at least this much sun is one of the "best" hours.
GOOD_HOUR_SECONDS = 1800
#: Less daylight than this left in a window, and the window counts as over.
MIN_WINDOW_MINUTES = 20
KM_PER_MILE = 1.609344


# ── Errors: the only text a person ever sees from a failure ─────────────────


class UnknownPlace(AgentAppError):
    """A place the app has no coordinates for."""

    user_message = "I don't know that place. I cover London and about 60 day-trip towns around it."
    retryable = False


class LiveWeatherUnavailable(AgentAppError):
    """Open-Meteo did not answer usefully, and the person picked the app with @.

    Raised only then: Pippa shows "Nearest Sunshine couldn't answer: <this>"
    word for word. When Pippa chose the app herself, a raised error would let
    her answer in her own voice, perhaps with weather nobody looked up, so the
    app returns an honest `live_weather: false` result instead.
    """

    user_message = ("Live weather is unavailable right now: the Open-Meteo forecast service didn't "
                    "answer, so I can't tell you where the sun is. Please try again in a few minutes.")
    retryable = True


# ── The data ────────────────────────────────────────────────────────────────


def _load_towns() -> dict:
    data = json.loads(TOWNS_PATH.read_text(encoding="utf-8"))
    return {"towns": list(data["towns"]), "origins": list(data.get("origins", []))}


DATA = _load_towns()
TOWNS: list[dict] = DATA["towns"]
ORIGINS: list[dict] = DATA["origins"]


def _normalise(text: str) -> str:
    """Lower case ASCII words: "St. Albans" -> "st albans", "King's Cross" -> "kings cross"."""
    text = unicodedata.normalize("NFKD", text or "").encode("ascii", "ignore").decode("ascii")
    text = text.lower().replace("&", " and ")
    text = re.sub(r"['`’]", "", text)
    text = re.sub(r"[^a-z0-9]+", " ", text)
    words = text.split()
    words = ["st" if w in ("saint", "st") else w for w in words]
    leading = {"near", "nearby", "around", "in", "at", "from", "to", "the", "im", "i", "am", "starting", "leaving"}
    trailing = {"uk", "england", "station", "town", "centre", "center", "area", "please", "railway"}
    while len(words) > 1 and words[0] in leading:
        words.pop(0)
    while len(words) > 1 and words[-1] in trailing:
        words.pop()
    return " ".join(words)


def _build_index() -> dict:
    """Every name and alias, normalised, to the place it names."""
    index: dict[str, dict] = {}

    def add(key: str, place: dict) -> None:
        key = _normalise(key)
        if key and key not in index:
            index[key] = place

    london = {"kind": "london", "name": LONDON["name"], "lat": LONDON["lat"], "lon": LONDON["lon"],
              "in_london": True}
    for name in LONDON_NAMES:
        add(name, london)
    for i, town in enumerate(TOWNS):
        place = {"kind": "town", "town": i, "name": town["name"], "lat": town["lat"], "lon": town["lon"],
                 "in_london": False}
        add(town["name"], place)
        for alias in town.get("aliases", []):
            add(alias, place)
    for origin in ORIGINS:
        place = {"kind": "origin", "name": origin["name"], "lat": origin["lat"], "lon": origin["lon"],
                 "in_london": bool(origin.get("in_london"))}
        add(origin["name"], place)
        for alias in origin.get("aliases", []):
            add(alias, place)
    return index


INDEX = _build_index()


#: Words that may sit around a place name without changing which place it is:
#: "Brighton beach", "north London", "Margate seafront".
FILLER = {"beach", "pier", "seafront", "sea", "front", "harbour", "high", "street", "old", "town", "centre",
          "station", "marina", "promenade", "seaside", "castle", "cathedral", "north", "south", "east", "west",
          "central", "upper", "lower", "city", "area", "of", "the", "near", "and", "around"}
#: As a place to visit, a bare "Stratford" is the day trip, not east London.
PLACE_PREFERENCES = {"stratford": "stratford upon avon"}


def resolve(text: str, as_destination: bool = False) -> dict | None:
    """The place `text` names, or None.

    An exact name, then a known name with only filler words around it, then a
    close spelling (a strict cutoff: Ryde is not Rye, Stafford not Stamford).
    """
    key = _normalise(text)
    if not key:
        return None
    if as_destination and key in PLACE_PREFERENCES:
        key = PLACE_PREFERENCES[key]
    if key in INDEX:
        return INDEX[key]
    padded = f" {key} "
    inside = [k for k in INDEX if f" {k} " in padded
              and set(padded.replace(f" {k} ", " ", 1).split()) <= FILLER]
    if inside:
        return INDEX[max(inside, key=len)]
    close = difflib.get_close_matches(key, list(INDEX), n=1, cutoff=0.9)
    return INDEX[close[0]] if close else None


def distance_km(a: dict, b: dict) -> float:
    """Great-circle ("as the crow flies") distance."""
    lat1, lon1, lat2, lon2 = map(math.radians, (a["lat"], a["lon"], b["lat"], b["lon"]))
    h = math.sin((lat2 - lat1) / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin((lon2 - lon1) / 2) ** 2
    return 2 * 6371.0 * math.asin(math.sqrt(h))


def estimated_drive_minutes(km: float) -> int:
    """A rough door-to-door guess from straight-line distance: roads wind (x1.3)
    and average about 70 km/h, plus ten minutes to get going. Rounded to 5."""
    minutes = 10 + km * 1.3 / 70 * 60
    return max(5, int(5 * round(minutes / 5)))


# ── Talking to Open-Meteo ───────────────────────────────────────────────────


class Forecast:
    """One place's hourly forecast, as unix seconds."""

    def __init__(self, times, sun, temps, sunrises, sunsets):
        self.times = times          # each the END of an hour: sunshine is "preceding hour"
        self.sun = sun              # seconds of sun in the hour before times[i]
        self.temps = temps          # °C at times[i]
        self.sunrises = sunrises
        self.sunsets = sunsets

    def sun_seconds(self, start: float, end: float) -> float:
        """Seconds of sun between start and end, weighting hours cut by either edge."""
        total = 0.0
        for t, s in zip(self.times, self.sun):
            overlap = min(t, end) - max(t - 3600, start)
            if overlap > 0 and s:
                total += s * overlap / 3600
        return total

    def best_hours(self, start: float, end: float) -> tuple[float, float] | None:
        """The longest unbroken run of mostly sunny hours inside the window."""
        runs, run = [], []
        for t, s in zip(self.times, self.sun):
            if not (t > start and t - 3600 < end):
                continue
            if s is not None and s >= GOOD_HOUR_SECONDS:
                run.append(t)
            elif run:
                runs.append(run)
                run = []
        if run:
            runs.append(run)
        if not runs:
            return None
        best = max(runs, key=len)
        return max(best[0] - 3600, start), min(best[-1], end)

    def has_gaps(self, start: float, end: float) -> bool:
        """True if any hour overlapping the window has no sunshine figure."""
        return any(s is None for t, s in zip(self.times, self.sun) if t > start and t - 3600 < end)

    def max_temp(self, start: float, end: float) -> float | None:
        inside = [c for t, c in zip(self.times, self.temps) if c is not None and start <= t <= end]
        if inside:
            return max(inside)
        middle = (start + end) / 2
        known = [(abs(t - middle), c) for t, c in zip(self.times, self.temps) if c is not None]
        return min(known)[1] if known else None


class WeatherUnavailable(Exception):
    """Open-Meteo did not answer, or answered with something unusable. Never shown as is."""


def _number_list(values, length, allow_none=True) -> list:
    if not isinstance(values, list) or len(values) != length:
        raise WeatherUnavailable("a forecast series has the wrong length")
    for v in values:
        if v is None and allow_none:
            continue
        if isinstance(v, bool) or not isinstance(v, (int, float)):
            raise WeatherUnavailable("a forecast series holds something that is not a number")
    return values


def parse_forecasts(body, expected: int) -> list[Forecast]:
    """Open-Meteo's answer for `expected` places, checked before anything is believed.

    A 200 that holds an error, too few places or empty series is treated
    exactly like no answer at all: a wrong forecast is worse than none.
    """
    if expected == 1 and isinstance(body, dict):
        body = [body]
    if not isinstance(body, list) or len(body) != expected:
        raise WeatherUnavailable("not one forecast per place")
    forecasts = []
    for item in body:
        if not isinstance(item, dict) or item.get("error"):
            raise WeatherUnavailable("a forecast is missing or an error")
        hourly, daily = item.get("hourly"), item.get("daily")
        if not isinstance(hourly, dict) or not isinstance(daily, dict):
            raise WeatherUnavailable("a forecast has no hourly or daily part")
        times = hourly.get("time")
        if not isinstance(times, list) or not times:
            raise WeatherUnavailable("a forecast has no hours")
        n = len(times)
        _number_list(times, n, allow_none=False)
        sun = _number_list(hourly.get("sunshine_duration"), n)
        temps = _number_list(hourly.get("temperature_2m"), n)
        days = daily.get("time")
        if not isinstance(days, list) or not days:
            raise WeatherUnavailable("a forecast has no days")
        sunrises = _number_list(daily.get("sunrise"), len(days))
        sunsets = _number_list(daily.get("sunset"), len(days))
        if all(s is None for s in sun):
            raise WeatherUnavailable("a forecast has no sunshine figures")
        pairs = [(r, s) for r, s in zip(sunrises, sunsets) if r is not None and s is not None]
        first, last = min(times) - 86400, max(times) + 86400
        if not pairs or any(not (first <= r < s <= last) for r, s in pairs):
            raise WeatherUnavailable("sunrise and sunset do not fit the forecast")
        forecasts.append(Forecast(times, sun, temps, [r for r, _ in pairs], [s for _, s in pairs]))
    return forecasts


# ── Working out which hours they mean ───────────────────────────────────────

PARTS = {
    # name: (from, to) in hours of the local day, before clipping to daylight
    "morning": (0, 12),
    "lunchtime": (12, 14),
    "afternoon": (12, 18),
    "evening": (17, 24),
}
PART_WORDS = {
    "morning": "morning", "am": "morning",
    "lunchtime": "lunchtime", "lunch": "lunchtime", "midday": "lunchtime", "noon": "lunchtime",
    "afternoon": "afternoon", "pm": "afternoon",
    "evening": "evening", "tonight": "evening", "night": "evening", "sunset": "evening",
}
WEEKDAYS = ("monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday")
#: Further ahead than the two days the app asks Open-Meteo for.
LATER_DAYS = {"weekend", "week", "fortnight", "month"}


class Window:
    def __init__(self, start: datetime, end: datetime, label: str, note: str = ""):
        self.start, self.end, self.label, self.note = start, end, label, note

    @property
    def hours(self) -> float:
        return (self.end - self.start).total_seconds() / 3600


def _clock(moment: datetime) -> str:
    return moment.strftime("%H:%M")


def _day_name(day: date, today: date) -> str:
    if day == today:
        return "today"
    if day == today + timedelta(days=1):
        return "tomorrow"
    return f"{day.strftime('%A')} {day.day} {day.strftime('%B')}"


def _daylight(forecast: Forecast, day: date) -> tuple[datetime, datetime] | None:
    for rise, set_ in zip(forecast.sunrises, forecast.sunsets):
        r = datetime.fromtimestamp(rise, UK)
        if r.date() == day:
            return r, datetime.fromtimestamp(set_, UK)
    return None


def choose_window(when: str, now: datetime, forecast: Forecast) -> Window | None:
    """The daylight hours the question is about, or None if the forecast has none left.

    `forecast` is the one nearest the start, for sunrise and sunset. When what
    they asked for has no daylight left (the evening in winter, or any time
    after sunset), the window moves to the next daylight and `note` says so.
    """
    words = set(_normalise(when).split())
    today = now.date()
    tomorrow = today + timedelta(days=1)
    # A weekday name is today or tomorrow if it can be; any other is too far.
    named = {w for w in words if w in WEEKDAYS}
    if WEEKDAYS[tomorrow.weekday()] in named:
        words.add("tomorrow")
    if "weekend" in words:
        if today.weekday() == 4:          # Friday: the weekend starts tomorrow
            words.add("tomorrow")
        if today.weekday() in (4, 5, 6):  # Friday to Sunday: it is in reach
            words.discard("weekend")
    too_far = bool(words & LATER_DAYS) or bool(named - {WEEKDAYS[today.weekday()], WEEKDAYS[tomorrow.weekday()]})
    day = tomorrow if "tomorrow" in words else today
    part = next((PART_WORDS[w] for w in sorted(words) if w in PART_WORDS), None)
    note = ""
    if too_far and "tomorrow" not in words:
        note = "I can only see as far as tomorrow, so this is for the next few hours."
        part = None

    light = _daylight(forecast, day)
    if light is not None:
        rise, set_ = light
        midnight = datetime(day.year, day.month, day.day, tzinfo=UK)
        if part:
            lo, hi = PARTS[part]
            start, end = midnight + timedelta(hours=lo), midnight + timedelta(hours=hi)
            label = f"this {part}" if day == today else f"tomorrow {part}"
        elif day == today:
            start = max(now, rise)
            end = start + timedelta(hours=DEFAULT_HOURS)
            label = "in the next few hours" if now >= rise else "this morning"
            if now < rise and not note:
                note = f"It's still dark, so this is for this morning, from {_clock(rise)}."
        else:
            start, end = rise, set_
            label = "tomorrow"
        start, end = max(start, rise, now), min(end, set_)
        if (end - start).total_seconds() >= MIN_WINDOW_MINUTES * 60:
            return Window(start, end, label, note)

    # Nothing left of what they asked for: say so, and use the next daylight.
    asked = (f"this {part}" if day == today else f"tomorrow {part}") if part else (
        "tomorrow" if day == tomorrow else "")
    light = _daylight(forecast, day)
    if part and light:
        rise, set_ = light
        midnight = datetime(day.year, day.month, day.day, tzinfo=UK)
        if midnight + timedelta(hours=PARTS[part][0]) >= set_:   # e.g. a winter evening
            start = max(now, rise, set_ - timedelta(hours=3))
            if (set_ - start).total_seconds() >= MIN_WINDOW_MINUTES * 60:
                label = "before sunset" if day == today else "tomorrow before sunset"
                return Window(start, set_, label, f"{_why_not(asked, part, day, now, forecast)}, so this is "
                                                  f"for the last of the daylight, from {_clock(start)}.")
    for ahead in (today, tomorrow):
        light = _daylight(forecast, ahead)
        if light is None:
            continue
        rise, set_ = light
        start = max(rise, now)
        end = min(start + timedelta(hours=DEFAULT_HOURS), set_)
        if (end - start).total_seconds() < MIN_WINDOW_MINUTES * 60:
            continue
        if ahead == tomorrow:
            label = "tomorrow morning"
        elif now < rise:
            label = "this morning"
        else:
            label = "in the next few hours"
        reason = _why_not(asked, part, day, now, forecast)
        if now < rise and ahead == today and not part and day == today:
            reason = "It's still dark"
        return Window(start, end, label,
                      f"{reason}, so this is for {label.removeprefix('in ')}, from {_clock(start)}.")
    return None


def _why_not(asked: str, part: str | None, day: date, now: datetime, forecast: Forecast) -> str:
    """Why what they asked for has no daylight, in a few words."""
    light = _daylight(forecast, day)
    if part:
        midnight = datetime(day.year, day.month, day.day, tzinfo=UK)
        part_start, part_end = (midnight + timedelta(hours=h) for h in PARTS[part])
        if part_end <= now:
            return f"{asked[0].upper()}{asked[1:]} is over"
        if light and part_start >= light[1]:
            return f"There's no daylight {asked} (sunset is {_clock(light[1])})"
        return f"There's no daylight left {asked}"
    if asked:
        return f"There's no forecast for {asked} yet"
    if light and now < light[1]:
        return f"The sun sets at {_clock(light[1])}"
    return "The sun has set"


# ── The app ─────────────────────────────────────────────────────────────────


class App:
    """Find the nearest towns with sunshine coming up."""

    def __init__(self) -> None:
        self._manifest = validate_manifest(load_manifest_file(MANIFEST_PATH))

    @property
    def manifest(self) -> Manifest:
        return self._manifest

    def handle(self, call: Call) -> Result:
        if call.outcome_id != "sunshine.find":
            raise AgentAppError(f"this app cannot do {call.outcome_id!r}")

        start_text = (call.inputs.get("start") or "").strip()
        place_text = (call.inputs.get("place") or "").strip()
        when_text = (call.inputs.get("when") or "").strip()

        start = self._start(start_text)
        asked = self._asked_place(place_text, start)
        now = call.context.now.astimezone(UK)

        # One request for every town, plus London itself, plus the place they
        # asked about if it is not a town (Croydon, say): still one request.
        points = [dict(t) for t in TOWNS] + [dict(LONDON)]
        if asked and asked["kind"] == "origin":
            points.append({"name": asked["name"], "lat": asked["lat"], "lon": asked["lon"]})

        try:
            forecasts = parse_forecasts(self._fetch_within_deadline(self._url(points)), len(points))
        except (WeatherUnavailable, urllib.error.URLError, http.client.HTTPException, TimeoutError,
                OSError, ValueError) as exc:
            # HTTPError is a URLError and TimeoutError an OSError: all caught.
            # Never pass on Open-Meteo's own text: say it in our words.
            if getattr(call.context, "explicit", False):
                raise LiveWeatherUnavailable(f"open-meteo: {type(exc).__name__}") from None
            return self._unavailable(start, asked)

        by_name = {p["name"]: f for p, f in zip(points, forecasts)}
        nearest_town = min(range(len(TOWNS)), key=lambda i: distance_km(start, TOWNS[i]))
        window = choose_window(when_text, now, forecasts[nearest_town])
        if window is None:
            return self._unavailable(start, asked, reason="no daylight")
        lo, hi = window.start.timestamp(), window.end.timestamp()
        needed = min(max(SUNNY_HOURS_MIN, SUNNY_SHARE * window.hours), 0.5 * window.hours)

        rows = []
        for i, town in enumerate(TOWNS):
            f = forecasts[i]
            rows.append(self._row(town, f, start, lo, hi))
        # A town with a gap in its forecast is left out rather than called cloudy.
        sunny = sorted((r for r in rows if not r["unknown"] and r["sun_hours"] >= needed),
                       key=lambda r: (r["km"], r["name"]))
        top = sunny[:HOW_MANY]

        asked_row = None
        if asked:
            if asked["kind"] == "town":
                asked_row = rows[asked["town"]]
            else:
                asked_row = self._row({"name": asked["name"], "lat": asked["lat"], "lon": asked["lon"]},
                                      by_name[asked["name"]], start, lo, hi)
            asked_row["sunny"] = asked_row["sun_hours"] >= needed

        return self._answer(start, asked, asked_row, window, top, sunny, rows, needed)

    # ── pieces ──

    @staticmethod
    def _start(text: str) -> dict:
        if not text or _normalise(text) in HERE_WORDS:
            return dict(INDEX[_normalise("london")])
        place = resolve(text)
        if place is None:
            error = UnknownPlace(f"no coordinates for start {text!r}")
            error.user_message = (f"I don't know where {text} is. I can start from London, a London area "
                                  "or one of about 60 towns around it, such as Reading or Guildford.")
            raise error
        return dict(place)

    @staticmethod
    def _asked_place(text: str, start: dict) -> dict | None:
        if not text or _normalise(text) in HERE_WORDS:
            return None
        place = resolve(text, as_destination=True)
        if place is None:
            error = UnknownPlace(f"no coordinates for place {text!r}")
            error.user_message = (f"I don't have {text} on my list of about 60 day-trip towns within "
                                  "2.5 hours of London, so I can't check its sunshine.")
            raise error
        return dict(place)

    @staticmethod
    def _url(points: list[dict]) -> str:
        query = {
            "latitude": ",".join(f"{p['lat']:.4f}" for p in points),
            "longitude": ",".join(f"{p['lon']:.4f}" for p in points),
            "hourly": "sunshine_duration,temperature_2m",
            "daily": "sunrise,sunset",
            "timezone": "Europe/London",
            "forecast_days": "2",
            "timeformat": "unixtime",
        }
        return FORECAST_API + "?" + urllib.parse.urlencode(query, safe=",")

    def _fetch_within_deadline(self, url: str):
        """`_fetch`, abandoned after TIMEOUT_SECONDS in all.

        urlopen's timeout limits each wait on the socket, not the whole
        request: a server trickling a byte every few seconds could hold the
        call past Pippa's 20 seconds. So the fetch runs in a worker thread and
        is given up on at the deadline, whatever it is doing.
        """
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=1)
        try:
            future = pool.submit(self._fetch, url, TIMEOUT_SECONDS)
            try:
                return future.result(timeout=TIMEOUT_SECONDS)
            except concurrent.futures.TimeoutError:
                raise WeatherUnavailable("no complete answer within the deadline") from None
            except (WeatherUnavailable, urllib.error.URLError, http.client.HTTPException, TimeoutError,
                    OSError, ValueError):
                raise
            except Exception as exc:  # anything else the network can throw: still "unavailable"
                raise WeatherUnavailable(f"fetch failed: {type(exc).__name__}") from None
        finally:
            pool.shutdown(wait=False)

    def _fetch(self, url: str, timeout: float = TIMEOUT_SECONDS):
        """The one network call. Tests replace this on the instance."""
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return json.loads(response.read().decode("utf-8"))

    @staticmethod
    def _row(town: dict, f: Forecast, start: dict, lo: float, hi: float) -> dict:
        km = distance_km(start, town)
        sun_hours = round(f.sun_seconds(lo, hi) / 3600, 1)
        temp = f.max_temp(lo, hi)
        best = f.best_hours(lo, hi)
        if start["in_london"] and town.get("train_minutes"):
            minutes = int(town["train_minutes"])
            travel = f"about {_duration(minutes)} by train from {town['london_terminal']}"
        elif km < 1:
            minutes = 0
            travel = "you're already there"
        else:
            minutes = estimated_drive_minutes(km)
            travel = f"roughly {_duration(minutes)} by road (estimate)"
        return {"name": town["name"], "km": km, "minutes": minutes, "travel": travel,
                "sun_hours": sun_hours, "temp": temp, "best": best, "unknown": f.has_gaps(lo, hi)}

    @staticmethod
    def _describe(row: dict, include_distance: bool = True) -> str:
        bits = [row["name"]]
        if include_distance:
            if row["km"] < 1:
                bits.append("where you are")
            else:
                bits.append(f"{row['km']:.0f} km ({row['km'] / KM_PER_MILE:.0f} miles), {row['travel']}")
        span = _sunny_span(row)
        bits.append(f"{span}, {_hours(row['sun_hours'])} of sun in all" if span
                    else f"{_hours(row['sun_hours'])} of sun")
        if row["temp"] is not None:
            bits.append(f"up to {round(row['temp']):.0f}°C")
        return ", ".join(bits[:1]) + ": " + ", ".join(bits[1:]) if len(bits) > 1 else bits[0]

    def _answer(self, start, asked, asked_row, window, top, sunny, rows, needed) -> Result:
        # The clock times are the DAYLIGHT looked at, and are said so: next to
        # train times, a bare "(07:30–16:03)" read as when the trains run.
        window_field = f"{window.label}, daylight hours {_clock(window.start)} to {_clock(window.end)}"
        window_text = window.label
        places = [self._describe(r) for r in top]
        data = {
            "start": start["name"],
            "window": window_field,
            "places": places,
            "sunny_places_found": len(sunny),
            "live_weather": True,
        }
        if top:
            first = top[0]
            data.update({
                "nearest_place": first["name"],
                "nearest_distance_km": round(first["km"], 1),
                "nearest_travel_minutes": int(first["minutes"]),
                "nearest_sunny_hours": float(first["sun_hours"]),
            })
            if first["temp"] is not None:
                data["nearest_temperature_c"] = round(float(first["temp"]), 1)

        parts = []
        if window.note:
            parts.append(window.note)
        if asked_row is not None and asked_row["unknown"]:
            data["asked_place"] = asked_row["name"]
            parts.append(f"I don't have a complete sunshine forecast for {asked_row['name']} {window_text}, "
                         "so I can't say whether it will be sunny.")
            asked_row = {**asked_row, "sunny": False, "skip": True}
        if asked_row is not None and not asked_row.get("skip"):
            data["asked_place"] = asked_row["name"]
            data["asked_place_sunny"] = bool(asked_row["sunny"])
            data["asked_place_forecast"] = self._describe(asked_row, include_distance=False)
            detail = self._describe(asked_row, include_distance=False).split(": ", 1)[-1]
            span = _sunny_span(asked_row)
            temp = f", up to {round(asked_row['temp']):.0f}°C" if asked_row["temp"] is not None else ""
            if asked_row["sunny"]:
                when_sunny = span.replace("sunny ", "", 1) if span else f"with {_hours(asked_row['sun_hours'])} of sun"
                line = f"Yes, {asked_row['name']} should be sunny {window_text}, {when_sunny}{temp}"
                if asked_row["km"] >= 1:
                    line += f"; {asked_row['km']:.0f} km from {start['name']}, {_short_travel(asked_row)}"
                parts.append(line + ".")
            elif asked_row["sun_hours"] > 0:
                parts.append(f"Not really: {asked_row['name']} gets only {_hours(asked_row['sun_hours'])} "
                             f"of sun {window_text}{temp}.")
            else:
                parts.append(f"No, {asked_row['name']} looks cloudy {window_text}"
                             + (f", up to {round(asked_row['temp']):.0f}°C." if asked_row["temp"] is not None else "."))

        if top:
            lead = "Nearest sunshine" if asked_row is None or not asked_row["sunny"] else "Nearest sunshine overall"
            if asked_row is not None and not asked_row["sunny"] and not asked_row.get("skip"):
                lead = "For sun instead, the nearest"
            listing = "; ".join(_short_place(r) for r in top)
            parts.append(f"{lead} to {start['name']} {window_text}: {listing}.")
        else:
            brightest = max((r for r in rows if not r["unknown"]), key=lambda r: (r["sun_hours"], -r["km"]),
                            default={"sun_hours": 0})
            line = f"No proper sunshine is forecast {window_text} in the {len(rows)} towns I check."
            if brightest["sun_hours"] > 0:
                line += (f" The brightest is {brightest['name']}, {brightest['km']:.0f} km away, "
                         f"with {_hours(brightest['sun_hours'])} of sun.")
            parts.append(line)
        parts.append(SOURCE_NOTE)
        return Result(data=data, narrative=one_paragraph(parts))

    @staticmethod
    def _unavailable(start: dict, asked: dict | None, reason: str = "down") -> Result:
        if reason == "no daylight":
            text = ("I can't find any daylight left in the forecast I have, so I can't say where the sun "
                    "will be. Try again in the morning.")
        else:
            text = ("Live weather is unavailable right now: the Open-Meteo forecast service didn't answer "
                    "in time, so I can't tell you where the sun is. Please try again in a few minutes.")
        data = {
            "start": start["name"],
            "window": "",
            "places": [],
            "sunny_places_found": 0,
            "live_weather": reason != "down",
        }
        if asked:
            data["asked_place"] = asked["name"]
        return Result(data=data, narrative=text)


#: Pippa's reply is built from the narrative: one paragraph, never empty,
#: at most this many characters.
NARRATIVE_MAX = 500
SOURCE_NOTE = "Forecast: Open-Meteo; straight-line distances."


def one_paragraph(parts: list[str], limit: int = NARRATIVE_MAX) -> str:
    """Join the sentences into one paragraph of at most `limit` characters.

    The source note goes first if it does not fit; after that the text is cut
    at a word, with an ellipsis. Never empty.
    """
    parts = [" ".join(p.split()) for p in parts if p and p.strip()]
    text = " ".join(parts)
    if len(text) > limit and parts and parts[-1] == SOURCE_NOTE:
        text = " ".join(parts[:-1])
    if len(text) > limit:
        cut = text[: limit - 1]
        cut = cut[: cut.rfind(" ")] if " " in cut else cut
        text = cut.rstrip(" ,;:(") + "…"
    return text or "Nearest Sunshine has no answer for that just now."


def _about(stamp: float) -> str:
    """A clock time rounded to the nearest 5 minutes: 14:39 -> 14:40."""
    moment = datetime.fromtimestamp(round(stamp / 300) * 300, UK)
    return _clock(moment)


def _sunny_span(row: dict) -> str | None:
    """'sunny from about 10:00 to 15:00', from the longest run of mostly sunny hours."""
    if not row.get("best"):
        return None
    a, b = row["best"]
    return f"sunny from about {_about(a)} to {_about(b)}"


def _short_travel(row: dict) -> str:
    travel = row["travel"]
    if " by train from " in travel:
        return travel.split(" from ")[0]          # "about 55 min by train"
    return travel.replace(" (estimate)", ", estimated")


def _short_place(row: dict) -> str:
    bits = ["where you are" if row["km"] < 1 else f"{row['km']:.0f} km, {_short_travel(row)}",
            _sunny_span(row) or f"{_hours(row['sun_hours'])} of sun"]
    if row["temp"] is not None:
        bits.append(f"{round(row['temp']):.0f}°C")
    return f"{row['name']} ({', '.join(bits)})"


def _hours(value: float) -> str:
    if value >= 0.95 and abs(value - round(value)) < 0.05:
        n = int(round(value))
        return f"{n} hour" + ("s" if n != 1 else "")
    if value < 1:
        return f"{int(round(value * 60 / 5) * 5)} minutes"
    return f"{value:.1f} hours"


def _duration(minutes: int) -> str:
    h, m = divmod(int(minutes), 60)
    if not h:
        return f"{m} min"
    return f"{h} h {m:02d} min" if m else f"{h} h"
