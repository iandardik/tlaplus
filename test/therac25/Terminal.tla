----------------------------- MODULE Terminal -----------------------------

VARIABLES state

vars == <<state>>

Init == state = "blank"

TypeX ==
    /\ state \in {"blank", "cursorAtTop"}
    /\ state' = "cursorAtTop"

TypeE ==
    /\ state \in {"blank", "cursorAtTop"}
    /\ state' = "cursorAtTop"

TypeUp ==
    \/ /\ state = "cursorAtBottom"
       /\ state' = "cursorAtTop"
    \/ /\ state \in {"blank", "cursorAtTop"}
       /\ UNCHANGED vars

TypeEnter ==
    \/ /\ state = "cursorAtTop"
       /\ state' = "cursorAtBottom"
    \/ /\ state \in {"blank", "cursorAtBottom"}
       /\ UNCHANGED vars

BeamReady ==
    /\ state = "cursorAtBottom"
    /\ state' = "beamReady"

TypeB ==
    /\ state = "beamReady"
    /\ state' = "blank"

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeUp
    \/ TypeEnter
    \/ BeamReady
    \/ TypeB

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"blank", "cursorAtTop", "cursorAtBottom", "beamReady"}

=============================================================================
