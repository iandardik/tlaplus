------------------------------- MODULE ClosedNaive -------------------------------

VARIABLES inOut
VARIABLES senderState, senderBit, receiverState, receiverBit
VARIABLES transState, ackState

protocolVars == <<senderState, senderBit, receiverState, receiverBit, inOut>>
channelVars == <<transState, ackState>>
vars == <<senderState, senderBit, receiverState, receiverBit, inOut, transState, ackState>>

Protocol == INSTANCE NaiveProtocol
                WITH inOut <- inOut,
                     senderState <- senderState,
                     senderBit <- senderBit,
                     receiverState <- receiverState,
                     receiverBit <- receiverBit

Channel == INSTANCE PerfectChannel
               WITH transState <- transState,
                    ackState <- ackState


Init == Protocol!Init /\ Channel!Init

Input == Protocol!Input /\ UNCHANGED channelVars
Output == Protocol!Output /\ UNCHANGED channelVars

Send0 == Protocol!Send0 /\ Channel!Send0
Send1 == Protocol!Send1 /\ Channel!Send1
Receive0 == Protocol!Receive0 /\ Channel!Receive0
Receive1 == Protocol!Receive1 /\ Channel!Receive1
Ack0 == Protocol!Ack0 /\ Channel!Ack0
Ack1 == Protocol!Ack1 /\ Channel!Ack1
GetAck0 == Protocol!GetAck0 /\ Channel!GetAck0
GetAck1 == Protocol!GetAck1 /\ Channel!GetAck1

Next ==
    \/ Input
    \/ Output
    \/ Send0
    \/ Send1
    \/ GetAck0
    \/ GetAck1
    \/ Receive0
    \/ Receive1
    \/ Ack0
    \/ Ack1

Spec == Init /\ [][Next]_vars

TypeOK == Protocol!TypeOK

Alternate == Protocol!Alternate

MaxTwo == Protocol!MaxTwo

=============================================================================
