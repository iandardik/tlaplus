----------------------------- MODULE Env -----------------------------

VARIABLES envState

vars == <<envState>>

Init == envState = "chooseMode"

TypeX ==
    /\ envState = "chooseMode"
    /\ envState' = "confirmMode"

TypeE ==
    /\ envState = "chooseMode"
    /\ envState' = "confirmMode"

TypeEnter ==
    /\ envState = "confirmMode"
    /\ envState' = "fireBeam"

TypeB ==
    /\ envState = "fireBeam"
    /\ envState' = "finished"

TypeUp == FALSE

TypeOK == envState \in {"chooseMode", "confirmMode", "fireBeam", "finished"}

=============================================================================
