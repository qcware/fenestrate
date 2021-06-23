.. fenestrate documentation master file, created by
   sphinx-quickstart on Tue Jun 22 10:04:01 2021.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

Fenestrate: simple(ish) availability windows and exclusions
===========================================================

    "The mainframe is available every day from 10am EST to 1pm EST, and every
    Tuesday from 1pm CST to 3PM CST.  On even-numbered days there is also
    window from 9am EST to 9am PST, except on the 6th of each month when it
    is down for maintenance 9:30 EST to 10:30 EST.  On prime-numbered days in
    April..."

Fenestrate is a relatively simple library for handling a problem that can get surprisingly
complex: scheduling tasks for availability windows.  It is not complex or optimal--
it simply is used to find out, given an abstract set of availability windows and exclusions,

1. If you are in an availability window, and/or
2. When the next one is.

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   introduction

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
