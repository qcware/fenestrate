Introduction and Concepts
=========================

Fenestrate allows you to create a series of abstract :class:`~fenestrate.Window`
objects representing windows of availability or exclusion on
a given day.  Currently Fenestrate only allows *daily* schedules,
but more abstract windows (such as "from X date/time to X date/time")
may be added in the future.

Window and ConcreteWindow objects
---------------------------------

A :class:`~fenestrate.Window` object represents an abstract availability window,
with a Selector, which is simply a function with the signature

.. code-block:: python

  Selector = Callable[[datetime.date], bool]

and a `from_time` and `to_time`, both of which are `datetime.time` values representing
the time within a day that the window will occur.

This allows one to specify very arbitrary selectors, such as `daily`, `weekdays`,
`weekends`, or `weekly_on` a given day.

A Window can be reified on any day into a :class:`~fenestrate.ConcreteWindow` which has
`from_time` and `to_time` members represented by :class:`arrow.Arrow` objects

Are we in a Window?
-------------------

Generally, we don't need to know if we're within one particular Window on a given
day/time; we have a *set* of availabilities and exclusions and want to know if
we're in one of the availabilities and not one of the exclusions.

This is fairly straightforward using :func:`~fenestrate.in_nonexcluded_window`:

.. code-block:: python

  daily = Window(selectors.daily(),
                 datetime.time(hour=11, tzinfo=pytz.timezone("US/Eastern")),
                 datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")))
  weekly_exclusion = Window(selectors.weekly_on(selectors.Weekday.WEDNESDAY),
                            datetime.time(hour=12, tzinfo=pytz.timezone("US/Eastern")),
                            datetime.time(hour=13, tzinfo=pytz.timezone("US/Eastern")))     

  in_window = in_nonexcluded_window(arrow.now(), windows={daily}, exclusions={weekly_exclusion})


When can I reschedule?
----------------------


