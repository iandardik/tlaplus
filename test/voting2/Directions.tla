------------------------------- MODULE Directions -------------------------------

VARIABLES dirState

vars == <<dirState>>

Init == dirState = "off"

ToDirectionMenu ==
    /\ dirState = "off"
    /\ dirState' = "on"

LeaveDirectionMenu ==
    /\ dirState = "one"
    /\ dirState' = "off"

TypeOK == dirState \in {"on", "off"}

=============================================================================
