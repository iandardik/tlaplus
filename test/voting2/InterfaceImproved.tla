----------------------------- MODULE InterfaceImproved -----------------------------

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
    /\ state = "vote"
    /\ state' = "select"

Next ==
    \/ EnterPassword
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"pw", "select", "vote", "confirm", "done"}

=============================================================================

