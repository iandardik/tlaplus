----------------------------- MODULE BeamInterlock -----------------------------

VARIABLES mode, readyToFire

vars == <<mode, readyToFire>>

Init == mode = "xray" /\ readyToFire = FALSE

TypeX ==
    \/ /\ mode = "electron"
       /\ readyToFire = FALSE
       /\ mode' = "switchToXray"
       /\ UNCHANGED readyToFire
    \/ /\ mode = "xray"
       /\ UNCHANGED vars

TypeE ==
    \/ /\ mode = "xray"
       /\ readyToFire = FALSE
       /\ mode' = "electron"
       /\ UNCHANGED readyToFire
    \/ /\ mode = "electron"
       /\ UNCHANGED vars

TypeB ==
    /\ readyToFire = FALSE
    /\ readyToFire' = TRUE
    /\ UNCHANGED mode

fireXray ==
    /\ mode = "xray"
    /\ readyToFire = TRUE
    /\ readyToFire' = FALSE
    /\ UNCHANGED mode

fireElectron ==
    /\ mode = "electron"
    /\ readyToFire = TRUE
    /\ readyToFire' = FALSE
    /\ UNCHANGED mode

Rotate ==
    /\ mode = "switchToXray"
    /\ mode' = "xray"
    /\ UNCHANGED readyToFire

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeB
    \/ fireXray
    \/ fireElectron
    \/ Rotate

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ mode \in {"electron", "xray", "switchToXray"}
    /\ readyToFire \in BOOLEAN

=============================================================================
