------------------------------- MODULE Proc -------------------------------

CONSTANTS ProcSet

VARIABLES pc

vars == <<pc>>

Init == pc = [p \in ProcSet |-> "safe"]

Down ==
    \E p \in ProcSet :
        /\ pc[p] = "safe"
        /\ pc' = [pc EXCEPT![p] = "cs"]

Up ==
    \E p \in ProcSet :
        /\ pc[p] = "cs"
        /\ pc' = [pc EXCEPT![p] = "safe"]

Next ==
    \/ Up
    \/ Down

TypeOK == pc \in [ProcSet -> {"safe", "cs"}]

=============================================================================
