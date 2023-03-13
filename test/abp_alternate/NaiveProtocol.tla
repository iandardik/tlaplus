------------------------------- MODULE NaiveProtocol -------------------------------

EXTENDS Naturals

VARIABLES inOut
VARIABLES senderState, senderBit, receiverState, receiverBit

vars == <<senderState, senderBit, receiverState, receiverBit, inOut>>
senderVars == <<senderState, senderBit>>
receiverVars == <<receiverState, receiverBit>>

Sender == INSTANCE NaiveSender
            WITH senderState <- senderState,
                 senderBit <- senderBit

Receiver == INSTANCE NaiveReceiver
            WITH receiverState <- receiverState,
                 receiverBit <- receiverBit

Init == Sender!Init /\ Receiver!Init /\ inOut = 0

Input == Sender!Input /\ UNCHANGED receiverVars /\ inOut' = inOut+1
Send0 == Sender!Send0 /\ UNCHANGED receiverVars /\ UNCHANGED inOut
Send1 == Sender!Send1 /\ UNCHANGED receiverVars /\ UNCHANGED inOut
GetAck0 == Sender!GetAck0 /\ UNCHANGED receiverVars /\ UNCHANGED inOut
GetAck1 == Sender!GetAck1 /\ UNCHANGED receiverVars /\ UNCHANGED inOut

Receive0 == UNCHANGED senderVars /\ Receiver!Receive0 /\ UNCHANGED inOut
Receive1 == UNCHANGED senderVars /\ Receiver!Receive1 /\ UNCHANGED inOut
Output == UNCHANGED senderVars /\ Receiver!Output /\ inOut' = inOut-1
Ack0 == UNCHANGED senderVars /\ Receiver!Ack0 /\ UNCHANGED inOut
Ack1 == UNCHANGED senderVars /\ Receiver!Ack1 /\ UNCHANGED inOut

Next ==
    \/ Input
    \/ Send0
    \/ Send1
    \/ GetAck0
    \/ GetAck1
    \/ Receive0
    \/ Receive1
    \/ Output
    \/ Ack0
    \/ Ack1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ Sender!TypeOK
    /\ Receiver!TypeOK
    /\ inOut \in {0,1,2}

Alternate == inOut \in {0,1}

MaxTwo == inOut <= 2

=============================================================================
