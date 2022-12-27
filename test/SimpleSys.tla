--------------------------- MODULE SimpleSys ---------------------------

EXTENDS Naturals

VARIABLES i, j

vars == <<i,j>>

I ==
    /\ i < 3
    /\ i' = i + 1
    /\ j' = j

J ==
    /\ j < 3
    /\ j' = j + 1
    /\ i' = i


Init ==
    \/ /\ i = 0
       /\ j = 0

Next == I \/ J

Spec == Init /\ [][Next]_vars


TypeOK ==
    /\ i \in Nat
    /\ j \in Nat

Safety ==
    /\ i = 0
    /\ j <= 3


=============================================================================
