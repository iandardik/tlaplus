----------------------------- MODULE Therac25 -----------------------------

VARIABLES state, tableState, mode, readyToFire

vars == <<state, tableState, mode, readyToFire>>
terminalVars == <<state>>
turntableVars == <<tableState>>
beamVars == <<mode, readyToFire>>

Terminal == INSTANCE Terminal
            WITH state <- state

Turntable == INSTANCE Turntable
            WITH tableState <- tableState

Beam == INSTANCE Beam
            WITH mode <- mode,
                 readyToFire <- readyToFire

Init == Terminal!Init /\ Turntable!Init /\ Beam!Init

TypeX == Terminal!TypeX /\ Turntable!TypeX /\ Beam!TypeX
TypeE == Terminal!TypeE /\ Turntable!TypeE /\ Beam!TypeE
TypeUp == Terminal!TypeUp /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
TypeEnter == Terminal!TypeEnter /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
BeamReady == Terminal!BeamReady /\ UNCHANGED turntableVars /\ UNCHANGED beamVars
TypeB == Terminal!TypeB /\ UNCHANGED turntableVars /\ Beam!TypeB
Rotate == UNCHANGED terminalVars /\ Turntable!Rotate /\ UNCHANGED beamVars
fireXray == UNCHANGED terminalVars /\ UNCHANGED turntableVars /\ Beam!fireXray
fireElectron == UNCHANGED terminalVars /\ UNCHANGED turntableVars /\ Beam!fireElectron

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
    /\ Beam!TypeOK

XrayImpliesFlatMode ==
    (mode = "xray" /\ readyToFire = TRUE) => (tableState = "flattener")

=============================================================================
