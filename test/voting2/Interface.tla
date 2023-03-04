----------------------------- MODULE Interface -----------------------------

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

Next ==
    \/ EnterPassword
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"pw", "select", "vote", "confirm", "done"}

=============================================================================
\* Modification History
\* Last modified Wed Feb 22 09:47:34 EST 2023 by idardik
\* Created Tue Feb 21 23:00:49 EST 2023 by idardik

