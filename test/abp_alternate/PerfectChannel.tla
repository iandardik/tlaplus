------------------------------- MODULE PerfectChannel -------------------------------

VARIABLES transState, ackState

vars == <<transState, ackState>>
transVars == <<transState>>
ackVars == <<ackState>>

Transmit == INSTANCE PerfectTransmit
            WITH transState <- transState

Ack == INSTANCE PerfectAck
            WITH ackState <- ackState

Init == Transmit!Init /\ Ack!Init

Send0 == Transmit!Send0 /\ UNCHANGED ackVars
Send1 == Transmit!Send1 /\ UNCHANGED ackVars
Receive0 == Transmit!Receive0 /\ UNCHANGED ackVars
Receive1 == Transmit!Receive1 /\ UNCHANGED ackVars

Ack0 == UNCHANGED transVars /\ Ack!Ack0
Ack1 == UNCHANGED transVars /\ Ack!Ack1
GetAck0 == UNCHANGED transVars /\ Ack!GetAck0
GetAck1 == UNCHANGED transVars /\ Ack!GetAck1

Next ==
    \/ Send0
    \/ Send1
    \/ Receive0
    \/ Receive1
    \/ Ack0
    \/ Ack1
    \/ GetAck0
    \/ GetAck1

Spec == Init /\ [][Next]_vars

=============================================================================
