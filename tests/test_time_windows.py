import datetime

import arrow
import pytest
import pytz
from hypothesis import assume, given
from hypothesis.strategies import (composite, datetimes, sampled_from, sets,
                                   times)

from fenestrate import selectors
from fenestrate.fenestrate import (ConcreteWindow, DailyWindow,
                                   in_nonexcluded_window, in_window,
                                   next_window, windows_at_time)


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
            # this one hits the exclusion window so the availability window is reduced to
            # start at the end of the exclusion window
            ConcreteWindow(
                from_time=arrow.get("2020-06-24 12:30:00").replace(tzinfo="US/Eastern"),
                to_time=arrow.get("2020-06-24 13:00:00").replace(tzinfo="US/Eastern"),
            ),
        ),
        (
            arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
            # this is also on wednesday, so the availability window ends at the beginning of the
            # exclusion window
            ConcreteWindow(
                from_time=arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
                to_time=arrow.get("2020-06-24 12:00:00").replace(tzinfo="US/Eastern"),
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


# this is a case on 20210920 where a weekday window for IonQ was reified on a Sunday
# with a ViolationError.  The problem derived from windows being reified the day
# prior when checking for wraparounds, but this is incorrect behaviour.  This test attempts
# to capture this issue.
#
# Forge scheduling uses in_nonexcluded_window and next_window, so the forge problem
# came from windows_at_time and thus concrete_windows_on_date
def test_weekday_window_on_weekend():
    weekdays = DailyWindow(
        is_active_on_day=selectors.weekdays(),
        from_time=datetime.time(13, 0, tzinfo=datetime.timezone.utc),
        to_time=datetime.time(2, 0, tzinfo=datetime.timezone.utc),
    )
    # now check to see if this is active on a Sunday
    now = arrow.get("2021-09-19 13:00:00").replace(tzinfo="US/Pacific")
    assert in_nonexcluded_window(now, {weekdays}) == False


@composite
def daily_windows(draw):
    selector = draw(
        sampled_from(
            [
                selectors.daily(),
                selectors.weekdays(),
                selectors.weekends(),
                selectors.weekly_on(draw(sampled_from(selectors.Weekday))),
            ]
        )
    )
    from_time = draw(times())
    to_time = draw(times())
    assume(from_time != to_time)
    return DailyWindow(is_active_on_day=selector, from_time=from_time, to_time=to_time)


@given(
    inclusions=sets(daily_windows(), min_size=0, max_size=5),
    exclusions=sets(daily_windows(), min_size=0, max_size=5),
    now=datetimes(),
)
def test_hypothesis(inclusions, exclusions, now):
    anow = arrow.get(now)
    # first off, smoke test for assertions/contract violations
    assert in_nonexcluded_window(anow, inclusions, exclusions) in {
        True,
        False,
    }
    # now if we reschedule, the rescheduled time should be valid
    if not in_nonexcluded_window(anow, inclusions, exclusions):
        if inclusions != set():
            # we have max_days == 10 so that if the generated availability windows
            # are weekly we'll get a reschedule
            nw = next_window(anow, inclusions, exclusions, max_days=10)
            if nw is not None:
                rescheduled = nw.begin
                assert in_nonexcluded_window(
                    arrow.get(rescheduled), inclusions, exclusions
                )
