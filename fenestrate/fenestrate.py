"""A package to handle availability windows in a very generic fashion.
"""
import datetime
import itertools
from abc import ABC, abstractmethod
from functools import reduce
from typing import Callable, Iterator, Optional

import arrow
import attr
from icontract import require
from intervaltree import Interval, IntervalTree

Selector = Callable[[datetime.date], bool]


@attr.s(frozen=True)
class AbstractWindow(ABC):
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
    description: str = attr.ib(default="", kw_only=True)

    @abstractmethod
    def reify_on_date(self, d: datetime.date) -> "ConcreteWindow":
        pass


@attr.s(frozen=True)
class ConcreteWindow:
    """A class representing a very concrete "availability window".

    ...or rather an interval
    between 'from_time' and 'to_time'
    """

    from_time: arrow.Arrow = attr.ib(validator=attr.validators.instance_of(arrow.Arrow))
    to_time: arrow.Arrow = attr.ib(validator=attr.validators.instance_of(arrow.Arrow))
    ancestors: tuple[AbstractWindow, ...] = attr.ib(converter=tuple, default=tuple())


def overlaps(w1: ConcreteWindow, w2: ConcreteWindow) -> bool:
    """Whether or not w1 and w2 overlap in time"""
    return not ((w1.to_time < w2.from_time) or (w2.to_time < w1.from_time))


@attr.s(frozen=True)
class DailyWindow(AbstractWindow):

    from_time: datetime.time = attr.ib(
        validator=attr.validators.instance_of(datetime.time)
    )
    to_time: datetime.time = attr.ib(
        validator=attr.validators.instance_of(datetime.time)
    )

    @require(lambda self, d: self.is_active_on_day(d))
    def reify_on_date(self, d: datetime.date) -> ConcreteWindow:
        if self.from_time <= self.to_time:
            result = ConcreteWindow(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ),
                ancestors=[self],
            )
        else:
            result = ConcreteWindow(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ).shift(days=1),
                ancestors=[self],
            )
        return result


def in_window(now: arrow.Arrow, window: AbstractWindow) -> bool:
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
    return now.is_between(today.from_time, today.to_time) or now.is_between(
        yesterday.from_time, yesterday.to_time
    )


def concrete_windows_on_date(
    d: datetime.date, windows: set[AbstractWindow]
) -> IntervalTree:
    result = IntervalTree()
    for w in windows:
        cw = w.reify_on_date(d)
        result.add(Interval(cw.from_time, cw.to_time, [cw]))
    return result


def windows_at_time(now: arrow.Arrow, windows: set[AbstractWindow]):
    """Returns a set of concrete windows which overlap the given time.

    Keyword Arguments:
    now: arrow.Arrow
    windows: set[AbstractWindow]
    """
    todays_windows = concrete_windows_on_date(now.date(), windows)
    yesterdays_windows = concrete_windows_on_date(now.shift(days=-1).date(), windows)
    all_windows = todays_windows | yesterdays_windows
    return all_windows.at(now)


def in_nonexcluded_window(
    now: arrow.Arrow,
    inclusions: set[AbstractWindow],
    exclusions: set[AbstractWindow] = set(),
) -> bool:
    """Whether or not 'now' is in a window but not excluded.

    Takes a time, a set of Window objects representing windows of availability and
    a set of windows representing exclusions ("the system is down every Tuesday from 1 to 3")
    and returns whether or not the given time is in an availability window but not
    in an exclusion window
    """
    matching_inclusions = windows_at_time(now, inclusions)
    matching_exclusions = windows_at_time(now, exclusions)

    return (any(matching_inclusions)) and (not any(matching_exclusions))


def available_windows_between(
    from_time: arrow.Arrow,
    to_time: arrow.Arrow,
    inclusions: set[AbstractWindow],
    exclusions: set[AbstractWindow],
) -> IntervalTree:
    """
    Returns an intervaltree representing all concrete inclusions minus exclusions.

    Creates an IntervalTree with all inclusions from (from_time.date()-1 day)
    to (to_time.date()), trims intervals before and after those dates,
    and subtracts the exclusions, decorating any inclusions' data with the
    exclusions that affect it.
    """
    all_dates = arrow.Arrow.range(
        "day", from_time.shift(days=-1).datetime, to_time.datetime
    )
    all_inclusions = IntervalTree().union(
        itertools.chain.from_iterable(
            concrete_windows_on_date(d.date(), inclusions) for d in all_dates
        )
    )
    all_exclusions = IntervalTree().union(
        itertools.chain.from_iterable(
            concrete_windows_on_date(d.date(), exclusions) for d in all_dates
        )
    )
    # so now we have two interval trees, one with all the inclusions and one with
    # all the exclusions.  For each exclusion, "chop" the inclusions tree so that
    # the exclusion is removed
    for interval in all_exclusions:
        all_inclusions.chop(
            interval.begin, interval.end, lambda x, islower: x.data + interval.data
        )
    # finally, chop everything from the beginning to from_time and from the end to to_time
    all_inclusions.chop(all_inclusions.begin(), from_time)
    all_inclusions.chop(to_time, all_inclusions.end())
    return all_inclusions


def next_window(
    now: arrow.Arrow,
    inclusions: set[AbstractWindow],
    exclusions: set[AbstractWindow] = set(),
    max_days: int = 2,
) -> Optional[ConcreteWindow]:
    """Finds the next available concrete window that is not excluded.

    "next" here means "if you're in a window, returns that, but if not,
    returns the one that starts after the current time"
    """
    # I had this nice idea about making iterators, but in reality
    # using an intervaltree for a given time period is cleaner.
    concrete_inclusions = available_windows_between(
        now, now.shift(days=max_days), inclusions, exclusions
    )
    sorted_inclusions = sorted(concrete_inclusions)
    return sorted_inclusions[0] if len(sorted_inclusions) > 0 else None
