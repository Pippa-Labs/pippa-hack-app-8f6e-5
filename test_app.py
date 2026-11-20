"""Tests for Nearest Sunshine. Run them with `pytest`.

Publishing runs them, and a repository whose tests fail does not deploy.
No test touches the network (conftest.py refuses every socket): Open-Meteo is
replaced, on the instance, with a fake built from the request's own
coordinates, so the fake always answers for exactly the places asked about.
"""

from __future__ import annotations

import json
import urllib.parse
from datetime import date, datetime, timedelta, timezone

import pytest
from pippa_agentapp_sdk import LocalRunner

import app as app_module
from app import App, UnknownPlace

UK = app_module.UK
#: Friday 20 November 2026, 14:00 in London (GMT, so also 14:00 UTC).
NOW = datetime(2026, 11, 20, 14, 0, tzinfo=timezone.utc)
SUNRISE, SUNSET = (7, 30), (16, 0)


def town(name):
    return next(t for t in app_module.TOWNS if t["name"] == name)


def names_by_point():
    """(lat, lon) as the URL writes them -> place name."""
    places = list(app_module.TOWNS) + [app_module.LONDON] + list(app_module.ORIGINS)
    return {(f"{p['lat']:.4f}", f"{p['lon']:.4f}"): p["name"] for p in places}


def hours(first, last, seconds=3600, day=0):
    """Sun in the hours STARTING at first..last (local), as Open-Meteo labels
    them: by the hour they END."""
    return {(day, h + 1): seconds for h in range(first, last + 1)}


def open_meteo(url, sun=None, temp=10.0, start=date(2026, 11, 20), sunrise=SUNRISE, sunset=SUNSET):
    """What Open-Meteo answers for the places in `url`.

    `sun` maps a place name to {(day, local hour it ends): seconds}.
    """
    query = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)
    lats, lons = query["latitude"][0].split(","), query["longitude"][0].split(",")
    lookup = names_by_point()
    midnight = datetime(start.year, start.month, start.day, tzinfo=UK)
    first = midnight.astimezone(timezone.utc)
    stamps = [(first + timedelta(hours=h)).astimezone(UK) for h in range(50)]
    stamps = [s for s in stamps if (s.date() - start).days < 2]
    days = [midnight, datetime(start.year, start.month, start.day, tzinfo=UK) + timedelta(days=1)]
    body = []
    for lat, lon in zip(lats, lons):
        name = lookup[(lat, lon)]
        mine = (sun or {}).get(name, {})
        values = []
        for s in stamps:
            day = (s.date() - start).days
            values.append(float(mine.get((day, s.hour), 0.0)))
        temps = temp(name) if callable(temp) else temp
        body.append({
            "latitude": float(lat), "longitude": float(lon), "utc_offset_seconds": 0,
            "timezone": "Europe/London",
            "hourly": {"time": [int(s.timestamp()) for s in stamps], "sunshine_duration": values,
                       "temperature_2m": [temps] * len(stamps)},
            "daily": {"time": [int(d.timestamp()) for d in days],
                      "sunrise": [int((d.replace(hour=sunrise[0], minute=sunrise[1])).timestamp()) for d in days],
                      "sunset": [int((d.replace(hour=sunset[0], minute=sunset[1])).timestamp()) for d in days]},
        })
    return body


def ask(inputs=None, sun=None, now=NOW, explicit=False, fetch=None, **weather):
    """Ask the app, the way Pippa does, with a fake Open-Meteo. Returns (result, urls)."""
    app = App()
    urls = []

    def fake_fetch(url, timeout=6.0):
        urls.append((url, timeout))
        if fetch is not None:
            return fetch(url, timeout)
        return open_meteo(url, sun=sun, **weather)

    app._fetch = fake_fetch
    kwargs = {"explicit": True} if explicit else {}
    result = LocalRunner(app).call("sunshine.find", inputs or {}, granted_secrets={}, now=now,
                                   request_id="test-1", **kwargs).result
    return result, urls


# ── the contract ────────────────────────────────────────────────────────────


def test_the_manifest_is_valid():
    app = App()
    assert app.manifest.app_id == "hack.app_8f6e_5"
    assert [o.id for o in app.manifest.outcomes] == ["sunshine.find"]


def test_the_data_file_has_about_sixty_towns_within_two_and_a_half_hours():
    towns = app_module.TOWNS
    assert 55 <= len(towns) <= 65
    assert len({t["name"] for t in towns}) == len(towns)
    for t in towns:
        assert 0 < t["train_minutes"] <= 150, t["name"]
        assert 49.9 < t["lat"] < 53.5 and -3.5 < t["lon"] < 2.0, t["name"]
        assert t["london_terminal"].startswith("London "), t["name"]


def test_summary_never_says_by():
    import yaml
    manifest = yaml.safe_load(open(app_module.MANIFEST_PATH, encoding="utf-8"))
    assert " by " not in f" {manifest['app']['summary'].lower()} "


def test_example_phrases_avoid_words_other_apps_own():
    reserved = ("today", "tomorrow", "this week", "my calendar", "what's on")
    for outcome in App().manifest.outcomes:
        for phrase in outcome.example_phrases:
            assert not any(word in phrase.lower() for word in reserved), phrase


# ── the one request ─────────────────────────────────────────────────────────


def test_one_request_for_every_town_with_a_six_second_timeout():
    _, urls = ask({}, sun={"Brighton": hours(14, 15)})
    assert len(urls) == 1
    url, timeout = urls[0]
    assert timeout == 6
    assert url.startswith("https://api.open-meteo.com/v1/forecast?")
    query = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)
    # every town plus London itself
    assert len(query["latitude"][0].split(",")) == len(app_module.TOWNS) + 1
    assert query["hourly"] == ["sunshine_duration,temperature_2m"]


def test_nothing_the_person_typed_goes_into_the_request():
    _, urls = ask({"start": "Clapham", "place": "Brighton", "when": "this afternoon"},
                  sun={"Brighton": hours(12, 15)})
    url = urls[0][0].lower()
    for word in ("clapham", "brighton", "afternoon"):
        assert word not in url


def test_a_place_asked_about_that_is_not_a_town_joins_the_same_request():
    result, urls = ask({"place": "Croydon"}, sun={"Croydon": hours(14, 15)})
    query = urllib.parse.parse_qs(urllib.parse.urlsplit(urls[0][0]).query)
    assert len(urls) == 1
    assert len(query["latitude"][0].split(",")) == len(app_module.TOWNS) + 2
    assert result.data["asked_place"] == "Croydon" and result.data["asked_place_sunny"] is True


# ── answers ─────────────────────────────────────────────────────────────────


def test_the_three_nearest_sunny_towns_nearest_first():
    sun = {"Brighton": hours(14, 15), "Margate": hours(14, 15), "Oxford": hours(14, 15),
           "Cambridge": hours(14, 15), "Bath": hours(14, 15)}
    result, _ = ask({}, sun=sun)
    data = result.data
    assert data["start"] == "London"
    assert data["live_weather"] is True
    assert data["sunny_places_found"] == 5
    assert len(data["places"]) == 3
    km = {n: app_module.distance_km(app_module.LONDON, town(n)) for n in sun}
    expected = sorted(sun, key=km.get)[:3]
    assert [p.split(":")[0] for p in data["places"]] == expected
    assert data["nearest_place"] == expected[0]
    assert data["nearest_travel_minutes"] == town(expected[0])["train_minutes"]
    assert data["nearest_sunny_hours"] == 2.0
    assert data["nearest_temperature_c"] == 10.0
    assert "by train from London" in data["places"][0]
    assert result.narrative.startswith("Nearest sunshine to London, in the next few hours (14:00–16:00)")


def test_the_window_stops_at_sunset_and_partial_hours_count_partly():
    now = NOW.replace(minute=30)
    result, _ = ask({}, sun={"Brighton": hours(14, 15)}, now=now)
    assert result.data["window"] == "in the next few hours (14:30–16:00)"
    assert result.data["nearest_sunny_hours"] == 1.5


def test_a_named_town_that_will_be_sunny():
    result, _ = ask({"place": "Brighton", "when": "this afternoon"}, sun={"Brighton": hours(12, 15)})
    assert result.data["asked_place"] == "Brighton"
    assert result.data["asked_place_sunny"] is True
    assert result.narrative.startswith("Yes, Brighton should be sunny this afternoon (14:00–16:00)")


def test_a_named_town_that_will_be_cloudy_gets_alternatives():
    result, _ = ask({"place": "Brighton", "when": "this afternoon"}, sun={"Hastings": hours(14, 15)})
    assert result.data["asked_place_sunny"] is False
    assert result.data["places"][0].startswith("Hastings:")
    assert "No, Brighton looks cloudy" in result.narrative
    assert "For sun instead" in result.narrative


def test_a_start_outside_london_uses_road_estimates():
    result, _ = ask({"start": "Reading"}, sun={"Oxford": hours(14, 15), "Brighton": hours(14, 15)})
    assert result.data["start"] == "Reading"
    assert result.data["nearest_place"] == "Oxford"
    assert "by road (estimate)" in result.data["places"][0]
    assert "train" not in result.data["places"][0]


def test_a_london_area_counts_as_london_for_trains():
    result, _ = ask({"start": "Clapham"}, sun={"Brighton": hours(14, 15)})
    assert result.data["start"] == "Clapham"
    assert "by train from London Victoria" in result.data["places"][0]


def test_nowhere_sunny_is_said_plainly():
    result, _ = ask({}, sun={"Margate": hours(15, 15, seconds=600)})
    assert result.data["places"] == []
    assert result.data["sunny_places_found"] == 0
    assert "nearest_place" not in result.data
    assert "No proper sunshine" in result.narrative
    assert "The brightest is Margate" in result.narrative


def test_after_dark_it_looks_at_tomorrow_morning():
    evening = NOW.replace(hour=19)
    result, _ = ask({}, sun={"Brighton": hours(8, 10, day=1)}, now=evening)
    assert result.data["window"] == "tomorrow morning (07:30–12:30)"
    assert result.data["nearest_place"] == "Brighton"
    assert result.narrative.startswith("The sun has set, so this is for tomorrow morning, from 07:30.")


def test_british_summer_time_is_handled():
    summer = datetime(2026, 7, 15, 9, 0, tzinfo=timezone.utc)   # 10:00 BST
    result, _ = ask({}, sun={"Brighton": hours(10, 12)}, now=summer, start=date(2026, 7, 15),
                    sunrise=(5, 0), sunset=(21, 0))
    assert result.data["window"] == "in the next few hours (10:00–15:00)"
    assert result.data["nearest_sunny_hours"] == 3.0


# ── when it cannot answer ───────────────────────────────────────────────────


@pytest.mark.parametrize("failure", [
    TimeoutError("timed out"),
    app_module.urllib.error.URLError("no route"),
    app_module.urllib.error.HTTPError("https://api.open-meteo.com", 503, "busy", {}, None),
    app_module.urllib.error.HTTPError("https://api.open-meteo.com", 429, "slow down", {}, None),
    ValueError("not json"),
])
def test_when_open_meteo_fails_it_says_live_weather_is_unavailable(failure):
    def broken(url, timeout):
        raise failure

    result, urls = ask({}, fetch=broken)
    assert len(urls) == 1                       # asked once, not again
    assert result.data["live_weather"] is False
    assert result.data["places"] == []
    assert result.narrative.startswith("Live weather is unavailable right now")


def test_picked_by_name_a_failure_is_said_word_for_word():
    def broken(url, timeout):
        raise TimeoutError("timed out")

    with pytest.raises(app_module.LiveWeatherUnavailable) as caught:
        ask({}, fetch=broken, explicit=True)
    assert caught.value.user_message.startswith("Live weather is unavailable right now")
    assert caught.value.retryable is True


@pytest.mark.parametrize("junk", [
    {"error": True, "reason": "Latitude must be in range"},
    [],
    [{"hourly": {}}],
    "<html>",
])
def test_an_answer_that_is_not_a_forecast_is_never_believed(junk):
    result, _ = ask({}, fetch=lambda url, timeout: junk)
    assert result.data["live_weather"] is False
    assert "unavailable" in result.narrative


def test_too_few_forecasts_is_not_believed():
    def short(url, timeout):
        return open_meteo(url, sun={"Brighton": hours(14, 15)})[:-1]

    result, _ = ask({}, fetch=short)
    assert result.data["live_weather"] is False


@pytest.mark.parametrize("inputs", [{"start": "Narnia"}, {"place": "Atlantis"}])
def test_a_place_it_does_not_know_is_named_back(inputs):
    with pytest.raises(UnknownPlace) as caught:
        ask(inputs, sun={})
    assert list(inputs.values())[0] in caught.value.user_message


def test_picked_by_name_answers_the_same():
    result, _ = ask({"place": "Brighton"}, sun={"Brighton": hours(14, 15)}, explicit=True)
    assert result.data["asked_place_sunny"] is True


def test_every_call_fits_inside_pippas_20_seconds():
    """One request of at most 6 s, and the rest takes well under a second."""
    import time

    assert app_module.TIMEOUT_SECONDS == 6
    started = time.monotonic()
    ask({"start": "Reading", "place": "Brighton", "when": "this afternoon"},
        sun={t["name"]: hours(12, 15) for t in app_module.TOWNS})
    assert time.monotonic() - started < 2
    assert app_module.TIMEOUT_SECONDS + 2 < 20


def test_the_real_fetch_sends_a_user_agent_and_a_timeout(monkeypatch):
    seen = {}

    class Response:
        def read(self):
            return json.dumps([]).encode()

        def __enter__(self):
            return self

        def __exit__(self, *exc):
            return False

    def fake_urlopen(request, timeout):
        seen["ua"] = request.get_header("User-agent")
        seen["timeout"] = timeout
        return Response()

    monkeypatch.setattr(app_module.urllib.request, "urlopen", fake_urlopen)
    App()._fetch("https://api.open-meteo.com/v1/forecast?latitude=1&longitude=1", 6)
    assert seen == {"ua": app_module.USER_AGENT, "timeout": 6}


# ── which hours they mean ───────────────────────────────────────────────────


@pytest.mark.parametrize("when, now_hour, window, note", [
    ("", 14, "in the next few hours (14:00–16:00)", ""),
    ("today", 14, "in the next few hours (14:00–16:00)", ""),
    ("now", 14, "in the next few hours (14:00–16:00)", ""),
    ("the next few hours", 14, "in the next few hours (14:00–16:00)", ""),
    ("this morning", 10, "this morning (10:00–12:00)", ""),
    ("this morning", 14, "in the next few hours (14:00–16:00)",
     "This morning is over, so this is for the next few hours, from 14:00."),
    ("this evening", 14, "before sunset (14:00–16:00)",
     "There's no daylight this evening (sunset is 16:00), so this is for the last of the daylight, from 14:00."),
    ("this evening", 5, "before sunset (13:00–16:00)",
     "There's no daylight this evening (sunset is 16:00), so this is for the last of the daylight, from 13:00."),
    ("tomorrow", 14, "tomorrow (07:30–16:00)", ""),
    ("tomorrow afternoon", 14, "tomorrow afternoon (12:00–16:00)", ""),
    ("friday afternoon", 13, "this afternoon (13:00–16:00)", ""),          # today is a Friday
    ("saturday morning", 13, "tomorrow morning (07:30–12:00)", ""),
    ("sunday", 13, "in the next few hours (13:00–16:00)",
     "I can only see as far as tomorrow, so this is for the next few hours."),
    ("this weekend", 13, "tomorrow (07:30–16:00)", ""),                     # Friday: the weekend is tomorrow
    ("next week", 13, "in the next few hours (13:00–16:00)",
     "I can only see as far as tomorrow, so this is for the next few hours."),
    ("", 6, "this morning (07:30–12:30)", "It's still dark, so this is for this morning, from 07:30."),
    ("", 3, "this morning (07:30–12:30)", "It's still dark, so this is for this morning, from 07:30."),
])
def test_which_hours(when, now_hour, window, note):
    now = NOW.replace(hour=now_hour)
    result, _ = ask({"when": when}, sun={"Brighton": hours(7, 15)}, now=now)
    assert result.data["window"] == window
    if note:
        assert result.narrative.startswith(note)
    else:
        assert result.narrative.startswith(("Nearest sunshine", "No proper sunshine"))


def test_ten_minutes_before_sunset_it_looks_at_tomorrow_morning():
    now = NOW.replace(hour=15, minute=50)
    result, _ = ask({}, sun={"Brighton": hours(9, 11, day=1)}, now=now)
    assert result.data["window"] == "tomorrow morning (07:30–12:30)"
    assert result.narrative.startswith("The sun sets at 16:00, so this is for tomorrow morning, from 07:30.")


@pytest.mark.parametrize("typed, name", [
    ("brighton", "Brighton"), ("Brighton & Hove", "Brighton"), ("St. Albans", "St Albans"),
    ("saint albans", "St Albans"), ("kings lynn", "King's Lynn"), ("Southend", "Southend-on-Sea"),
    ("Brigton", "Brighton"), ("Canterbury station", "Canterbury"), ("near Oxford", "Oxford"),
    ("Brighton beach", "Brighton"), ("central London", "London"), ("London Victoria", "Victoria"),
])
def test_places_people_type(typed, name):
    assert app_module.resolve(typed)["name"] == name


def test_walton_on_thames_is_not_walton_on_the_naze():
    assert app_module.resolve("Walton-on-Thames") is None


# ── found in review ─────────────────────────────────────────────────────────


def test_a_slow_trickle_is_cut_off_at_the_deadline(monkeypatch):
    import time as _time

    monkeypatch.setattr(app_module, "TIMEOUT_SECONDS", 0.3)
    app = App()
    app._fetch = lambda url, timeout=6.0: _time.sleep(2) or []
    started = _time.monotonic()
    result = LocalRunner(app).call("sunshine.find", {}, granted_secrets={}, now=NOW, request_id="t").result
    assert _time.monotonic() - started < 1.5
    assert result.data["live_weather"] is False


def test_a_connection_dropped_mid_answer_is_unavailable_not_a_crash():
    import http.client

    def dropped(url, timeout):
        raise http.client.IncompleteRead(b"[{")

    result, _ = ask({}, fetch=dropped)
    assert result.data["live_weather"] is False


def test_twenty_five_minutes_before_sunset_a_sunny_town_still_counts():
    result, _ = ask({}, sun={"Brighton": hours(15, 15)}, now=NOW.replace(hour=15, minute=35))
    assert result.data["window"] == "in the next few hours (15:35–16:00)"
    assert result.data["nearest_place"] == "Brighton"


def test_best_hours_are_one_unbroken_run():
    sun = {"Brighton": {**hours(12, 12), **hours(14, 15)}}
    result, _ = ask({"when": "this afternoon"}, sun=sun, now=NOW.replace(hour=12))
    assert "(best 14:00–16:00)" in result.data["places"][0]


def test_missing_sunshine_figures_are_not_called_cloud():
    def gappy(url, timeout):
        body = open_meteo(url, sun={"Hastings": hours(14, 15)})
        brighton = app_module.TOWNS.index(town("Brighton"))
        body[brighton]["hourly"]["sunshine_duration"][12:18] = [None] * 6
        return body

    result, _ = ask({"place": "Brighton"}, fetch=gappy)
    assert "asked_place_sunny" not in result.data
    assert "I don't have a complete sunshine forecast for Brighton" in result.narrative
    assert "looks cloudy" not in result.narrative


def test_sunrise_and_sunset_stay_paired_when_one_is_missing():
    def holes(url, timeout):
        body = open_meteo(url, sun={"Brighton": hours(8, 10, day=1)})
        for item in body:
            item["daily"]["sunset"][0] = None
        return body

    result, _ = ask({}, fetch=holes, now=NOW.replace(hour=19))
    assert result.data["window"].startswith("tomorrow morning (07:30")


def test_impossible_sunrise_times_are_not_believed():
    def millis(url, timeout):
        body = open_meteo(url)
        for item in body:
            item["daily"]["sunrise"] = [v * 1000 for v in item["daily"]["sunrise"]]
        return body

    result, _ = ask({}, fetch=millis)
    assert result.data["live_weather"] is False


@pytest.mark.parametrize("typed", ["Ryde", "Stafford", "Salford", "Kingston upon Hull",
                                   "Richmond, North Yorkshire", "Leeds", "Manchester"])
def test_places_it_must_not_mistake_for_others(typed):
    assert app_module.resolve(typed) is None


def test_stratford_as_a_day_trip_is_stratford_upon_avon():
    assert app_module.resolve("Stratford", as_destination=True)["name"] == "Stratford-upon-Avon"
    assert app_module.resolve("Stratford")["name"] == "Stratford"     # as a start: east London


def test_a_long_window_needs_more_than_an_hour_of_sun():
    summer = datetime(2026, 7, 15, 9, 0, tzinfo=timezone.utc)
    result, _ = ask({"place": "Brighton", "when": "tomorrow"}, sun={"Brighton": hours(12, 12, day=1)},
                    now=summer, start=date(2026, 7, 15), sunrise=(5, 0), sunset=(21, 0))
    assert result.data["asked_place_sunny"] is False


@pytest.mark.parametrize("day, now_utc", [
    (date(2026, 10, 25), datetime(2026, 10, 25, 11, 0, tzinfo=timezone.utc)),   # clocks went back
    (date(2027, 3, 28), datetime(2027, 3, 28, 11, 0, tzinfo=timezone.utc)),    # clocks went forward
])
def test_days_the_clocks_change(day, now_utc):
    local_noon = datetime(day.year, day.month, day.day, 12, tzinfo=UK)
    sun = {"Brighton": hours(local_noon.hour, local_noon.hour + 1)}
    result, _ = ask({}, sun=sun, now=now_utc, start=day)
    assert result.data["nearest_place"] == "Brighton"
    assert result.data["nearest_sunny_hours"] == 2.0


@pytest.mark.parametrize("inputs, now_hour", [
    ({}, 14), ({"place": "Brighton", "when": "this afternoon"}, 14), ({"place": "Oxford"}, 14),
    ({"start": "Reading"}, 14), ({"start": "Clapham", "when": "this evening"}, 14),
    ({"place": "Croydon", "when": "this weekend"}, 13), ({}, 19), ({}, 3), ({"start": "Kingston upon Thames"}, 15),
])
def test_the_narrative_is_one_short_paragraph_and_never_empty(inputs, now_hour):
    sun = {t["name"]: hours(7, 15) for t in app_module.TOWNS if len(t["name"]) > 12}
    sun.update({t["name"]: hours(8, 11, day=1) for t in app_module.TOWNS})
    for weather in (sun, {}):
        result, _ = ask(inputs, sun=weather, now=NOW.replace(hour=now_hour))
        assert 0 < len(result.narrative) <= 500, result.narrative
        assert "\n" not in result.narrative


def test_one_paragraph_cuts_long_text_at_a_word():
    text = app_module.one_paragraph(["word " * 200, app_module.SOURCE_NOTE])
    assert len(text) <= 500 and text.endswith("…")
    assert app_module.one_paragraph([]) != ""
