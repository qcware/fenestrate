import datetime

import arrow
import pytest
import pytz

from fenestrate import selectors
from fenestrate.fenestrate import (
    ConcreteWindow,
    DailyWindow,
    in_nonexcluded_window,
    in_window,
    next_window,
    windows_at_time,
)


@pytest.mark.parametrize(
    "now,expected,expected_with_exclusions",
    [
        (arrow.get("2020-06-24 00:30:00").replace(tzinfo="US/Eastern"), False, False),
        (arrow.get("2020-06-24 11:05:00").replace(tzinfo="US/Eastern"), True, True),
        (arrow.get("2020-06-24 12:29:00").replace(tzinfo="US/Eastern"), True, True),
        (arrow.get("2020-06-24 12:31:00").replace(tzinfo="US/Eastern"), True, False),
        (arrow.get("2020-06-24 13:01:00").replace(tzinfo="US/Eastern"), False, False),
        (arrow.get("2020-06-24 12:01:00").replace(tzinfo="US/Central"), False, False),
    ],
)
def test_in_window(now, expected, expected_with_exclusions):
    # this can get confusing.  What we'll start with is a daily window
    w = DailyWindow(
        lambda x: True,
        datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
        description="Daily",
    )
    # ..and then an exclusion at the end of the regular daily window
    ex = DailyWindow(
        lambda x: True,
        datetime.time(hour=12, minute=30, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=13, minute=30, tzinfo=pytz.timezone("US/Eastern")),
    )
    assert in_window(now, w) == expected
    cws = windows_at_time(now, {w})
    print(cws)
    assert (list(cws)[0].data[0].ancestors[0] == w) if expected else (cws == set())
    assert in_nonexcluded_window(now, {w}, {ex}) == expected_with_exclusions
    # now test wraparound windows by inverting the sense
    reverse_w = DailyWindow(w.is_active_on_day, w.to_time, w.from_time)
    reverse_ex = DailyWindow(ex.is_active_on_day, ex.to_time, ex.from_time)
    assert in_window(now, reverse_w) != expected
    cws = windows_at_time(now, {reverse_w})
    print(cws)
    assert (
        (list(cws)[0].data[0].ancestors[0] == reverse_w)
        if not expected
        else (cws == set())
    )


# jun 24 is a wednesday
daily = DailyWindow(
    is_active_on_day=selectors.daily(),
    from_time=datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
    to_time=datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
)
weekly = DailyWindow(
    is_active_on_day=selectors.weekly_on(selectors.Weekday.WEDNESDAY),
    from_time=datetime.time(hour=12, tzinfo=pytz.timezone("US/Eastern")),
    to_time=datetime.time(hour=12, minute=30, tzinfo=pytz.timezone("US/Eastern")),
)


@pytest.mark.parametrize(
    "now, expected",
    [
        (
            arrow.get("2020-06-24 12:25:00").replace(tzinfo="US/Eastern"),
            # this one hits the exclusion window so the availability window is reduced
            ConcreteWindow(
                from_time=arrow.get("2020-06-24 12:25:00").replace(tzinfo="US/Eastern"),
                to_time=arrow.get("2020-06-24 13:00:00").replace(tzinfo="US/Eastern"),
            ),
        ),
        (
            arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
            ConcreteWindow(
                from_time=arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
                to_time=arrow.get("2020-06-24 13:00:00").replace(tzinfo="US/Eastern"),
            ),
        ),
        (
            arrow.get("2020-06-24 13:01:00").replace(tzinfo="US/Eastern"),
            daily.reify_on_date(datetime.date(2020, 6, 25)),
        ),
    ],
)
def test_next_window_opening(now, expected):
    assert next_window(now, {daily}, {weekly}).begin == expected.from_time
    assert next_window(now, {daily}, {weekly}).end == expected.to_time
