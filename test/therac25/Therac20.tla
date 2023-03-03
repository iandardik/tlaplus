----------------------------- MODULE Therac20 -----------------------------

VARIABLES state, tableState, mode, readyToFire

vars == <<state, tableState, mode, readyToFire>>
terminalVars == <<state>>
turntableVars == <<tableState>>
beamVars == <<mode, readyToFire>>

Terminal == INSTANCE Terminal
            WITH state <- state

Turntable == INSTANCE Turntable
            WITH tableState <- tableState

BeamInterlock == INSTANCE BeamInterlock
            WITH mode <- mode,
                 readyToFire <- readyToFire

Init ==
    /\ Terminal!Init
    /\ Turntable!Init
    /\ BeamInterlock!Init

TypeX ==
    \/ Terminal!TypeX /\ Turntable!TypeX /\ BeamInterlock!TypeX
TypeE ==
    \/ Terminal!TypeE /\ Turntable!TypeE /\ BeamInterlock!TypeE
TypeUp ==
    \/ Terminal!TypeUp /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
TypeEnter ==
    \/ Terminal!TypeEnter /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
BeamReady ==
    \/ Terminal!BeamReady /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
TypeB ==
    \/ Terminal!TypeB /\ UNCHANGED turntableVars /\ BeamInterlock!TypeB
Rotate ==
    \/ UNCHANGED terminalVars /\ Turntable!Rotate /\ BeamInterlock!Rotate
fireXray ==
    \/ UNCHANGED terminalVars /\ UNCHANGED turntableVars /\ BeamInterlock!fireXray
fireElectron ==
    \/ UNCHANGED terminalVars /\ UNCHANGED turntableVars /\ BeamInterlock!fireElectron

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

TypeOK ==
    /\ Terminal!TypeOK
    /\ Turntable!TypeOK
    /\ BeamInterlock!TypeOK

XrayImpliesFlatMode ==
    (mode = "xray" /\ readyToFire = TRUE) => (tableState = "flattener")

=============================================================================
