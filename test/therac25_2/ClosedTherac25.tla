----------------------------- MODULE ClosedTherac25 -----------------------------

VARIABLES state, tableState, mode, readyToFire
VARIABLES envState

theracVars == <<state, tableState, mode, readyToFire>>
envVars == <<envState>>
vars == <<state, tableState, mode, readyToFire, envState>>

Therac == INSTANCE Therac25
              WITH state <- state,
                   tableState <- tableState,
                   mode <- mode,
                   readyToFire <- readyToFire

Env == INSTANCE Env
           WITH envState <- envState

Init == Therac!Init /\ Env!Init

TypeX == Therac!TypeX /\ Env!TypeX
TypeE == Therac!TypeE /\ Env!TypeE
TypeUp == Therac!TypeUp /\ Env!TypeUp
TypeEnter == Therac!TypeEnter /\ Env!TypeEnter
BeamReady == Therac!BeamReady /\ UNCHANGED envVars
TypeB == Therac!TypeB /\ Env!TypeB
Rotate == Therac!Rotate /\ UNCHANGED envVars
fireXray == Therac!fireXray /\ UNCHANGED envVars
fireElectron == Therac!fireElectron /\ UNCHANGED envVars

Next ==
    \/ TypeX
    \/ TypeE
    \/ TypeUp
    \/ TypeEnter
    \/ BeamReady
    \/ TypeB
    \/ Rotate
    \/ fireXray
    \/ fireElectron

Spec == Init /\ [][Next]_vars

TypeOK == Therac!TypeOK /\ Env!TypeOK

XrayImpliesFlatMode == Therac!XrayImpliesFlatMode

=============================================================================
