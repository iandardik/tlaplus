--------------------------- MODULE CoffeeTeaSmall_ErrPre ---------------------------
EXTENDS Naturals

VARIABLES brewed, temp

vars == <<brewed, temp>>

Init ==
  /\ brewed = {} /\ temp = 70

Next ==
  \/ brewed = {} /\ temp = 70 /\ brewed' = {"tea"} /\ temp' = 225

Spec == Init /\ [][Next]_vars
=============================================================================

