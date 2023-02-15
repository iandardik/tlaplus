--------------------------- MODULE SimpleExample ---------------------------

EXTENDS Naturals

VARIABLES i, j

vars == <<i,j>>

Init ==
    \/ /\ i = 0
       /\ j = 0
    \/ /\ i = 2
       /\ j = 0

Next ==
    \/ /\ i < 3
       /\ i' = i + 1
       /\ j' = j
    \/ /\ j < 3
       /\ j' = j + 1
       /\ i' = i

Spec == Init /\ [][Next]_vars


TypeOK ==
    /\ i \in Nat
    /\ j \in Nat

Safety ==
    /\ i <= 6
    /\ j <= 6


=============================================================================
\* Modification History
\* Last modified Wed Nov 02 20:42:19 EDT 2022 by idardik
\* Created Wed Nov 02 20:08:40 EDT 2022 by idardik
