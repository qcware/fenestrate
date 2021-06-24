----------------------------- MODULE nextwindow -----------------------------

(*This is not intended as a proper spec, rather organization of
thoughts when it comes to finding the next window that is not occluded
by an exclusion window.  Here we're skipping past the idea of
selectors for the moment and going straight to reified windows which
are just a start and stop time*)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  TIMES, \* here specified by integers as well
  MIN_WINDOWS,
  MIN_EXCLUSIONS

\* Set of all possible windows
WINDOWS == {<<start, end>> \in TIMES \X TIMES : start <= end}

\* Whether or not two intervals overlap, done with sets
OverlapsSets(w1, w2) ==
  \E t \in w1[1]..w1[2] : t \in w2[1]..w2[2]

\* intervals don't overlap if one is completely before the other
Overlaps(w1, w2) ==
  ~ \/ w1[2] < w2[1]
    \/ w2[2] < w1[1]

\* the set of windows which result when the given exclusion is
\* subtracted from the given window.  Returns a set
WindowMinusExclusion(window, exclusion) ==
  LET subtimes == window[1]..window[2]
  IN { <<start, end>>  \in subtimes \X subtimes :
    /\ ~ Overlaps(<<start, end>>, exclusion)
    /\ start <= end }
    
\* All the windows minus the times which are excluded
WindowsMinusExclusions(windows, exclusions) ==
  UNION { WindowMinusExclusion(w, exclusions) : w \in windows }

\* The next window that is not occluded by an exclusion
NextWindowNoOverlap(now, windows, exclusions) ==
  CHOOSE w \in WindowsMinusExclusions(windows, exclusions):
    /\ w[1] > now
    /\ ~ \E e \in exclusions :
      Overlaps(w, e)

(* --algorithm nextwindow
variables
  now \in TIMES,
  windows = CHOOSE w \in SUBSET WINDOWS: Cardinality(w) > MIN_WINDOWS,
  exclusions = CHOOSE e \in SUBSET WINDOWS: Cardinality(e) > MIN_EXCLUSIONS;
begin
skip
end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "b0fbb533" /\ chksum(tla) = "c99a949c")
VARIABLES now, windows, exclusions, pc

vars == << now, windows, exclusions, pc >>

Init == (* Global variables *)
        /\ now \in TIMES
        /\ windows = (CHOOSE w \in SUBSET WINDOWS: Cardinality(w) > MIN_WINDOWS)
        /\ exclusions = (CHOOSE e \in SUBSET WINDOWS: Cardinality(e) > MIN_EXCLUSIONS)
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << now, windows, exclusions >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Created Mon Jun 21 10:45:43 CDT 2021 by vputz
