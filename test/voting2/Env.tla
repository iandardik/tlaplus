----------------------------- MODULE Env -----------------------------

VARIABLES envState

vars == <<envState>>

Init ==
    /\ envState = "enter"

VEnter ==
    /\ envState = "enter"
    /\ envState' = "pw"

EnterPassword ==
    /\ envState = "pw"
    /\ envState' = "select"

SelectCandidate ==
    /\ envState = "select"
    /\ envState' = "vote"

Vote ==
    /\ envState = "vote"
    /\ envState' = "confirm"

Confirm ==
    /\ envState = "confirm"
    /\ envState' = "exit"

VExit ==
    /\ envState = "exit"
    /\ envState' = "done"

Back == FALSE

Next ==
    \/ EnterPassword
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK == envState \in {"enter", "pw", "select", "vote", "confirm", "exit", "done"}

=============================================================================
