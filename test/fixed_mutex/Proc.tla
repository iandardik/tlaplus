------------------------------- MODULE Proc -------------------------------

VARIABLES pc1, pc2

vars == <<pc1, pc2>>

Init ==
    /\ pc1 = "safe"
    /\ pc2 = "safe"

Down ==
    \/ /\ pc1 = "safe"
       /\ pc1' = "cs"
       /\ UNCHANGED pc2
    \/ /\ pc2 = "safe"
       /\ pc2' = "cs"
       /\ UNCHANGED pc1

Up ==
    \/ /\ pc1 = "cs"
       /\ pc1' = "safe"
       /\ UNCHANGED pc2
    \/ /\ pc2 = "cs"
       /\ pc2' = "safe"
       /\ UNCHANGED pc1

Next ==
    \/ Up
    \/ Down

TypeOK ==
    /\ pc1 \in {"safe", "cs"}
    /\ pc2 \in {"safe", "cs"}

=============================================================================
