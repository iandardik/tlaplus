----------------------------- MODULE DirectionsInterface -----------------------------

VARIABLES state

vars == <<state>>

Init ==
    /\ state = "pw"

EnterPassword ==
    /\ state = "pw"
    /\ state' = "select"

SelectCandidate ==
    /\ state = "select"
    /\ state' = "vote"

Vote ==
    /\ state = "vote"
    /\ state' = "confirm"

Confirm ==
    /\ state = "confirm"
    /\ state' = "done"

Back ==
    \/ /\ state = "vote"
       /\ state' = "select"
    \/ /\ state = "confirm"
       /\ state' = "vote"

EnterDirectionsMenu ==
    /\ state = "pw"
    /\ state' = "directions"

LeaveDirectionsMenu ==
    /\ state = "directions"
    /\ state' = "pw"

Next ==
    \/ EnterPassword
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back
    \/ EnterDirectionsMenu
    \/ LeaveDirectionsMenu

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"pw", "select", "vote", "confirm", "done", "directions"}

=============================================================================
