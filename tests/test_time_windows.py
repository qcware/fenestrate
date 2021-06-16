import datetime

import arrow
import pytz
import pytest
from fenestrate.fenestrate import Window, in_window, in_nonexcluded_window


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
    w = Window(
        lambda x: True,
        datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
    )
    assert in_window(now, w) == expected
    # now test wraparound windows by inverting the sense
    reverse_w = Window(
        lambda x: True,
        datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")),
        datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
        )
    assert in_window(now, reverse_w) != expected


# @pytest.skip
# @pytest.mark.parametrize(
#     "now, expected",
#     [
#         (
#             arrow.get("2020-06-24 00:30:00").replace(tzinfo="US/Eastern"),
#             window_on_day(datetime.date(2020, 6, 24), 11, 13, "US/Eastern"),
#         ),
#         (
#             arrow.get("2020-06-24 11:01:00").replace(tzinfo="US/Eastern"),
#             window_on_day(datetime.date(2020, 6, 25), 11, 13, "US/Eastern"),
#         ),
#         (
#             arrow.get("2020-06-24 13:01:00").replace(tzinfo="US/Eastern"),
#             window_on_day(datetime.date(2020, 6, 25), 11, 13, "US/Eastern"),
#         ),
#     ],
# )
# def test_next_window_opening(now, expected):
#     assert next_window_opening(now, 11, 13, "US/Eastern") == expected
