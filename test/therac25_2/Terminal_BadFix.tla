----------------------------- MODULE Terminal_BadFix -----------------------------

VARIABLES state

vars == <<state>>

Init == state = "blank"

TypeX ==
    /\ state = "blank"
    /\ state' = "cursorAtTop"

TypeE ==
    /\ state = "blank"
    /\ state' = "cursorAtTop"

TypeUp ==
    \/ /\ state = "cursorAtBottom"
       /\ state' = "blank"
    \/ /\ state \in {"blank", "cursorAtTop"}
       /\ UNCHANGED vars

TypeEnter ==
    \/ /\ state = "cursorAtTop"
       /\ state' = "cursorAtBottom"
    \/ /\ state \in {"blank", "cursorAtBottom"}
       /\ UNCHANGED vars
    \/ /\ state = "cursorAtBottom"
       /\ state' = "readyForBeamReady"

BeamReady ==
    /\ state = "readyForBeamReady"
    /\ state' = "beamReady"

TypeB ==
    /\ state = "beamReady"
    /\ state' = "finished"

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeUp
    \/ TypeEnter
    \/ BeamReady
    \/ TypeB

Spec == Init /\ [][Next]_vars

TypeOK == state \in {"blank", "cursorAtTop", "cursorAtBottom", "readyForBeamReady", "beamReady", "finished"}

=============================================================================
