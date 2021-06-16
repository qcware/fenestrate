"""A package to handle availability windows in a very generic fashion.
"""

import attr
import arrow
import datetime
from typing import Callable
from icontract import require

Selector = Callable[[datetime.date], bool]


@attr.s(frozen=True)
class Window:
    """A class representing a very abstract "availability window".

    It contains an abstract selector, which is a lambda function taking a date,
    to check whether the window applies on the given date (this allows
    very abstract selections like "weekdays" or "every third day" or anything).

    The time window itself is represented by a start time and an end time.
    The time window *starts* on the current day but can *end* on the next day.
    This means that a time window of 13:00-15:00 would match 14:00,
    but a time window of 22:00-02:00 would *not* match 0100 for *this* day.  It
    would, however, match 01:00 for the *next* day.  So when checking to see if
    a set of windows matches a given time instance, one should check the time
    window for today as well as the time window for yesterday.
    """

    is_active_on_day: Selector = attr.ib(validator=attr.validators.is_callable())
    from_time: datetime.time = attr.ib(
        validator=attr.validators.instance_of(datetime.time)
    )
    to_time: datetime.time = attr.ib(
        validator=attr.validators.instance_of(datetime.time)
    )

    @require(lambda self, d: self.is_active_on_day(d))
    def reify_on_date(self, d: datetime.date) -> dict[str, arrow]:
        if self.from_time <= self.to_time:
            result = dict(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ),
            )
        else:
            result = dict(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ).shift(days=1),
            )
        return result


def in_window(now: arrow, window: Window) -> bool:
    """Whether or not the time represented by 'now' falls in the given window.

    If the window is normally-ordered (from_time < to_time), then just
    check to make sure 'now' is between those two.

    If the window is reverse-ordered, check to see if the time is less than the
    "to" time and if the window was active *yesterday*

    Just comparing hours is problematic given time zones, so to solve
    this, we reify the window for today and yesterday

    """
    today = window.reify_on_date(now.date())
    yesterday = window.reify_on_date(now.shift(days=-1).date())
    return now.is_between(today["from_time"], today["to_time"]) or now.is_between(
        yesterday["from_time"], yesterday["to_time"]
    )


def in_nonexcluded_window(
    now: arrow, windows: set[Window], exclusions: set[Window] = {}
) -> bool:
    """Whether or not 'now' is in a window but not excluded.

    Takes a time, a set of Window objects representing windows of availability and
    a set of windows representing exclusions ("the system is down every Tuesday from 1 to 3")
    and returns whether or not the given time is in an availability window but not
    in an exclusion window
    """
    matching_inclusions = {x for x in windows if in_window(now, x)}
    matching_exclusions = {x for x in exclusions if in_window(now, x)}

    return (any(matching_inclusions)) and (not any(matching_exclusions))
