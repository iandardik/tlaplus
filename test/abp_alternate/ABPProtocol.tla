------------------------------- MODULE ABPProtocol -------------------------------

EXTENDS Naturals

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES inOut
VARIABLES senderState, senderBit, input, receiverState, receiverBit, output

vars == <<senderState, senderBit, input, receiverState, receiverBit, output, inOut>>
senderVars == <<senderState, senderBit, input>>
receiverVars == <<receiverState, receiverBit, output>>

Sender == INSTANCE ABPSender
              WITH senderState <- senderState,
                   senderBit <- senderBit,
                   input <- input

Receiver == INSTANCE ABPReceiver
                WITH receiverState <- receiverState,
                     receiverBit <- receiverBit,
                     output <- output

Init == Sender!Init /\ Receiver!Init /\ inOut = 5

Input(m) == Sender!Input(m) /\ UNCHANGED receiverVars /\ inOut' = inOut+1
Send0(m) == Sender!Send0(m) /\ UNCHANGED receiverVars /\ UNCHANGED<<inOut>>
Send1(m) == Sender!Send1(m) /\ UNCHANGED receiverVars /\ UNCHANGED<<inOut>>
GetAck0 == Sender!GetAck0 /\ UNCHANGED receiverVars /\ UNCHANGED<<inOut>>
GetAck1 == Sender!GetAck1 /\ UNCHANGED receiverVars /\ UNCHANGED<<inOut>>

Receive0(m) == UNCHANGED senderVars /\ Receiver!Receive0(m) /\ UNCHANGED<<inOut>>
Receive1(m) == UNCHANGED senderVars /\ Receiver!Receive1(m) /\ UNCHANGED<<inOut>>
Output == UNCHANGED senderVars /\ Receiver!Output /\ inOut' = inOut-1
Ack0 == UNCHANGED senderVars /\ Receiver!Ack0 /\ UNCHANGED<<inOut>>
Ack1 == UNCHANGED senderVars /\ Receiver!Ack1 /\ UNCHANGED<<inOut>>

Next ==
    \E m \in MessageValues :
        \/ Input(m)
        \/ Send0(m)
        \/ Send1(m)
        \/ GetAck0
        \/ GetAck1
        \/ Receive0(m)
        \/ Receive1(m)
        \/ Output
        \/ Ack0
        \/ Ack1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ Sender!TypeOK
    /\ Receiver!TypeOK
    /\ inOut \in {4,5,6,7}

Alternate == inOut \in {5,6}

InOutMaxChange == 4 <= inOut /\ inOut <= 7

=============================================================================
