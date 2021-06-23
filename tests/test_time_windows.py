import datetime

import arrow
import pytest
import pytz

from fenestrate import selectors
from fenestrate.fenestrate import (ConcreteWindow, DailyWindow,
                                   in_nonexcluded_window, in_window,
                                   next_window)


@pytest.mark.parametrize(
    "now,expected",
    [
        (arrow.get("2020-06-24 00:30:00").replace(tzinfo="US/Eastern"), False),
        (arrow.get("2020-06-24 11:05:00").replace(tzinfo="US/Eastern"), True),
        (arrow.get("2020-06-24 12:59:00").replace(tzinfo="US/Eastern"), True),
        (arrow.get("2020-06-24 13:01:00").replace(tzinfo="US/Eastern"), False),
        (arrow.get("2020-06-24 12:01:00").replace(tzinfo="US/Central"), False),
    ],
)
def test_in_window(now, expected):
    w = DailyWindow(
        lambda x: True,
        datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
    )
    assert in_window(now, w) == expected
    # now test wraparound windows by inverting the sense
    reverse_w = DailyWindow(
        lambda x: True,
        datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
    )
    assert in_window(now, reverse_w) != expected


daily = DailyWindow(
    is_active_on_day=selectors.daily(),
    from_time=datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
    to_time=datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
)
weekly = DailyWindow(
    is_active_on_day=selectors.weekly_on(selectors.Weekday.WEDNESDAY),
    from_time=datetime.time(hour=12, tzinfo=pytz.timezone("US/Eastern")),
    to_time=datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
)


@pytest.mark.parametrize(
    "now, expected",
    [
        (
            arrow.get("2020-06-24 00:30:00").replace(tzinfo="US/Eastern"),
            # this one hits the exclusion window so the availability window is reduced
            ConcreteWindow(
                from_time=arrow.get("2020-06-24 11:00:00").replace(tzinfo="US/Eastern"),
                to_time=arrow.get("2020-06-24 12:00:00").replace(tzinfo="US/Eastern"),
                description="",
            ),
        ),
        (
            arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
            daily.reify_on_date(datetime.date(2020, 6, 25)),
        ),
        (
            arrow.get("2020-06-24 13:01:00").replace(tzinfo="US/Eastern"),
            daily.reify_on_date(datetime.date(2020, 6, 25)),
        ),
    ],
)
def test_next_window_opening(now, expected):
    assert next_window(now, {daily}, {weekly}).from_time == expected.from_time
    assert next_window(now, {daily}, {weekly}).to_time == expected.to_time
