"""A collection of common selectors
"""
import datetime
from enum import IntEnum

from fenestrate.fenestrate import Selector


class Weekday(IntEnum):
    MONDAY = (0,)
    TUESDAY = (1,)
    WEDNESDAY = (2,)
    THURSDAY = (3,)
    FRIDAY = (4,)
    SATURDAY = (5,)
    SUNDAY = 6


def daily() -> Selector:
    """Always true"""
    return lambda x: True


def weekdays() -> Selector:
    """True if x falls on a weekday"""
    return lambda x: x.weekday() in {
        Weekday.MONDAY,
        Weekday.TUESDAY,
        Weekday.WEDNESDAY,
        Weekday.THURSDAY,
        Weekday.FRIDAY,
    }


def weekends() -> Selector:
    """True if x falls on a weekend"""
    return lambda x: x.weekday() in {Weekday.SATURDAY, Weekday.SUNDAY}


def weekly_on(d: Weekday) -> Selector:
    """Returns a selector true whenever the day falls on the given weekday"""
    return lambda x: x.weekday() == d
