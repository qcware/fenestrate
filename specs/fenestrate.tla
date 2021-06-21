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

(*Whether or not the given datetime matches the window.

They match if 
  the window's from_time < to_time and the datetime,
  the datetime is between those,
  and the selector matches the datetime's date
  
  or
  
  the window's from_time > to_time
  the datetime < to_time
  and the selector matches the day BEFORE the datetime's date
*)

in_window(window, datetime) ==
  LET
    selector == window[1]
    day == datetime[1]
    time == datetime[2]
    from == window[2]
    to == window[3]
  IN
    /\ from <= to => /\ from <= time
                     /\ time <= to
                     /\ selector[day]
    /\ from > to =>  /\ time < to
                     /\ selector[day-1]

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
\* Last modified Mon Jun 21 09:11:40 CDT 2021 by vputz
\* Created Wed Jun 16 10:07:32 CDT 2021 by vputz
