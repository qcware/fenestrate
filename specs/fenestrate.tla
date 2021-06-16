----------------------------- MODULE fenestrate -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  DAYS, \* here specified by integers
  TIMES, \* here specified by integers as well
  MIN_WINDOWS,
  MIN_EXCLUSIONS

(* Selectors are functions which map each day to a boolean value representing
whether or not a day matches a window *)

SELECTORS == [DAYS -> BOOLEAN]

(*This is the set of all possible windows in tuple form, where each tuple
represents
- A selector, which is whether or not this window is active on a given day
- A start time
- An end time. If the end time is less than the start time, this window
  spans the next day. *)
WINDOWS == SELECTORS \X TIMES \X TIMES

\* All possible datetimes
DATETIMES == DAYS \X TIMES

(*Whether or not the given date/time falls within the window specified by the
given window.  This requires that the window's selector match the given day
and that the datetime's time falls after the start time... and
- If the end time is greater than the start time, then ... and before the end time
- If the end time is less than the start time, representing a window extending
  to the next day, then we can't comment on the end time; we just have to go through
  the end of the day and can't comment on the wraparound, BUT we have to check this
  against the time window of the day before

Note that a window is defined by the day on which its start time exists, so
for example a window (24-hour day) starting at 23 and ending at 2 would NOT
match a time of 1, although the previous day's window might.*)

in_window(window, datetime) ==
  LET
    selector == window[1]
    day == datetime[1]
    time == datetime[2]
    from == window[2]
    to == window[3]
  IN
    /\ selector[day]
    /\ from <= to => /\ from <= time
                     /\ time <= to
    /\ from > to =>  /\ from <= time
                     /\ time <= CHOOSE t \in TIMES : \A t2 \in TIMES: t >= t2

\* this needs to check now against windows for the previous day.                     
in_nonexcluded_windows(windows, exclusions, now) ==
    /\ \E w \in windows : in_window(w, now)
    /\ ~ \E e \in exclusions : in_window(e, now)


(*--algorithm fenestrate

\* test
variables
  now \in DATETIMES,
  windows = CHOOSE w \in SUBSET WINDOWS: Cardinality(w) > MIN_WINDOWS,
  exclusions = CHOOSE e \in SUBSET WINDOWS: Cardinality(e) > MIN_EXCLUSIONS,
  result;
begin
check_in_window:
  result := in_nonexcluded_windows(windows, exclusions, now);
  print <<result, now>>;
end algorithm

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8935074d" /\ chksum(tla) = "7c765564")
CONSTANT defaultInitValue
VARIABLES now, windows, exclusions, result, pc

vars == << now, windows, exclusions, result, pc >>

Init == (* Global variables *)
        /\ now \in DATETIMES
        /\ windows = (CHOOSE w \in SUBSET WINDOWS: Cardinality(w) > MIN_WINDOWS)
        /\ exclusions = (CHOOSE e \in SUBSET WINDOWS: Cardinality(e) > MIN_EXCLUSIONS)
        /\ result = defaultInitValue
        /\ pc = "check_in_window"

check_in_window == /\ pc = "check_in_window"
                   /\ result' = in_nonexcluded_windows(windows, exclusions, now)
                   /\ PrintT(<<result', now>>)
                   /\ pc' = "Done"
                   /\ UNCHANGED << now, windows, exclusions >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == check_in_window
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Wed Jun 16 14:07:27 CDT 2021 by vputz
\* Created Wed Jun 16 10:07:32 CDT 2021 by vputz
