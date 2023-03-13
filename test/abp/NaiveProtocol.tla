------------------------------- MODULE NaiveProtocol -------------------------------

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES senderState, senderBit, input, receiverState, receiverBit, output

vars == <<senderState, senderBit, input, receiverState, receiverBit, output>>
senderVars == <<senderState, senderBit, input>>
receiverVars == <<receiverState, receiverBit, output>>

Sender == INSTANCE NaiveSender
            WITH senderState <- senderState,
                 senderBit <- senderBit,
                 input <- input

Receiver == INSTANCE NaiveReceiver
            WITH receiverState <- receiverState,
                 receiverBit <- receiverBit,
                 output <- output

Init == Sender!Init /\ Receiver!Init

Input(m) == Sender!Input(m) /\ UNCHANGED receiverVars
Send0(m) == Sender!Send0(m) /\ UNCHANGED receiverVars
Send1(m) == Sender!Send1(m) /\ UNCHANGED receiverVars
GetAck0 == Sender!GetAck0 /\ UNCHANGED receiverVars
GetAck1 == Sender!GetAck1 /\ UNCHANGED receiverVars

Receive0(m) == UNCHANGED senderVars /\ Receiver!Receive0(m)
Receive1(m) == UNCHANGED senderVars /\ Receiver!Receive1(m)
Output == UNCHANGED senderVars /\ Receiver!Output
Ack0 == UNCHANGED senderVars /\ Receiver!Ack0
Ack1 == UNCHANGED senderVars /\ Receiver!Ack1

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

TypeOK == Sender!TypeOK /\ Receiver!TypeOK

MessageReceived == (receiverState = "output") => (output = input)

=============================================================================
