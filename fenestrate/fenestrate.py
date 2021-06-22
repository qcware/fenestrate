"""A package to handle availability windows in a very generic fashion.
"""

import datetime
from functools import reduce
from typing import Callable, Iterator, Optional

import arrow
import attr
from icontract import require

Selector = Callable[[datetime.date], bool]


@attr.s(frozen=True)
class ConcreteWindow:
    """A class representing a very concrete "availability window".

    ...or rather an interval
    between 'from_time' and 'to_time'
    """

    from_time: arrow.Arrow = attr.ib(validator=attr.validators.instance_of(arrow.Arrow))
    to_time: arrow.Arrow = attr.ib(validator=attr.validators.instance_of(arrow.Arrow))


def overlaps(w1: ConcreteWindow, w2: ConcreteWindow) -> bool:
    """Whether or not w1 and w2 overlap in time"""
    return not ((w1.to_time < w2.from_time) or (w2.to_time < w1.from_time))


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
    def reify_on_date(self, d: datetime.date) -> ConcreteWindow:
        if self.from_time <= self.to_time:
            result = ConcreteWindow(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ),
            )
        else:
            result = ConcreteWindow(
                from_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.from_time)
                ),
                to_time=arrow.Arrow.fromdatetime(
                    datetime.datetime.combine(d, self.to_time)
                ).shift(days=1),
            )
        return result


def in_window(now: arrow.Arrow, window: Window) -> bool:
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


def in_nonexcluded_window(
    now: arrow.Arrow, windows: set[Window], exclusions: set[Window] = set()
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


def merge_window_with(
    w: ConcreteWindow, windows: set[ConcreteWindow]
) -> tuple[ConcreteWindow, set[ConcreteWindow]]:
    """Merges w with every window in windows.

    This merges the given concrete window w with every window in the
    given set of windows that overlaps, and then removes every window
    that overlapped and returns the tuple of

    merged_window, remaining_windows
    """
    # print(w)
    # print(windows)
    result_window = w
    result_remaining_windows: set[ConcreteWindow] = set()
    for window in windows:
        if overlaps(result_window, window):
            result_window = ConcreteWindow(
                from_time=min(result_window.from_time, window.from_time),
                to_time=max(result_window.to_time, window.to_time),
            )
        else:
            result_remaining_windows = result_remaining_windows | {window}
    return result_window, result_remaining_windows


def subtract_exclusion_from_window(
    e: ConcreteWindow, window: ConcreteWindow
) -> set[ConcreteWindow]:
    """Subtracts the exclusion from the window, returning a possibly empty set."""
    result: set[ConcreteWindow] = set()
    # to denote the overlaps below, (..) represents the exclusion and [xx] the window
    if overlaps(e, window):
        if e.from_time < window.from_time:
            if e.to_time < window.to_time:
                # (..[..)xx]
                return {ConcreteWindow(from_time=e.to_time, to_time=window.to_time)}
            else:
                # (..[..]..)
                return set()
        else:
            if e.to_time < window.to_time:
                # [xx(..)xx]
                return {
                    ConcreteWindow(from_time=window.from_time, to_time=e.from_time),
                    ConcreteWindow(from_time=e.to_time, to_time=window.to_time),
                }
            else:
                # [xx(..]..)
                return {ConcreteWindow(from_time=window.from_time, to_time=e.from_time)}
    else:
        return {window}


def subtract_exclusion_from_set(
    e: ConcreteWindow, windows: set[ConcreteWindow]
) -> set[ConcreteWindow]:
    """Subtracts the exclusion from the set of windows, possibly fragmenting them."""
    result: set[ConcreteWindow] = set()
    for w in windows:
        result = result | subtract_exclusion_from_window(e, w)
    return result


def active_windows_on_day(
    d: datetime.date, windows: set[Window]
) -> set[ConcreteWindow]:
    """Concrete windows which start on the given day"""
    return {w.reify_on_date(d) for w in windows if w.is_active_on_day(d)}


def first_window(windows: set[ConcreteWindow]) -> ConcreteWindow:
    """First window in the set."""
    return sorted(windows, key=lambda x: x.from_time)[0]


def concrete_windows(
    today: datetime.date, windows: set[Window], max_days: int = 7
) -> Iterator[ConcreteWindow]:
    """Returns an iterator of ConcreteWindow objects beginning 'today'.

    The concrete windows are made from the given abstract windows and merged
    if any overlap."""
    # trivial case: if there are no windows, just return
    if len(windows) == 0:
        return
    d1: arrow.Arrow = arrow.get(today)
    d2: arrow.Arrow = d1.shift(days=1)
    active_windows = active_windows_on_day(d1.date(), windows) | active_windows_on_day(
        d2.date(), windows
    )
    while (d1 - arrow.get(today)).days < max_days:
        while len(active_windows) > 0 and d1.date() < d2.date():
            # merge the earliest window with others and remove it
            w = first_window(active_windows)
            w, active_windows = merge_window_with(w, active_windows)
            d1 = arrow.get(w.from_time.date())
            yield w
        # We've yielded once, so either we have no windows left or d1 == d2.
        # if we have no windows left, just force the issue
        if len(active_windows) == 0:
            d1 = arrow.get(d2.date())
        while d1.date() >= d2.date():
            d2 = d2.shift(days=1)
            active_windows = active_windows | active_windows_on_day(d2.date(), windows)


def concrete_nonexcluded_windows(
    today: datetime.date,
    windows: set[Window],
    exclusions: set[Window] = set(),
    max_days: int = 7,
) -> Iterator[ConcreteWindow]:
    """A sequence of availability windows minus exclusions.

    Reifies the abstract Windows of the availability windows and
    exclusions and returns a sorted sequence of intervals.  I'd love for this to
    handle infinite sequences, but honestly it hurt my brain, so we just get all
    windows and all exclusions in the two operators and intersect them
    """
    all_windows = set(concrete_windows(today, windows, max_days))
    all_exclusions = set(concrete_windows(today, exclusions, max_days))

    remaining_windows: set[ConcreteWindow] = reduce(
        lambda x, y: subtract_exclusion_from_set(y, x), all_exclusions, all_windows
    )
    return (x for x in sorted(remaining_windows, key=lambda x: x.from_time))


def next_window(
    now: arrow.Arrow,
    windows: set[Window],
    exclusions: set[Window] = set(),
    max_days: int = 7,
) -> Optional[ConcreteWindow]:
    """Finds the next available concrete window that is not excluded.

    "next" here means "with a start time after the given 'now' time", so
    if 'now' is currently *in* a window, this will return the one that
    starts *after* the given time

    Given the set of valid windows and exclusions, finds the next
    window which is not occluded by an exclusion.  Takes the intersection
    of the times to try and provide a concrete window.
    """
    window_iter = concrete_nonexcluded_windows(
        now.date(), windows, exclusions, max_days
    )
    w = next(window_iter)
    while w.from_time < now:
        w = next(window_iter)
    if w.from_time > now:
        return w
    else:
        return None
