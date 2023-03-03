------------------------------- MODULE Mutex -------------------------------

VARIABLES state

vars == <<state>>

Init == state = "up"

Down == state' = "down"

Up == state' = "up"

Next ==
    \/ Up
    \/ Down

TypeOK == state \in {"up", "down"}

=============================================================================
