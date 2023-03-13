------------------------------- MODULE ClosedNaive -------------------------------

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES senderState, senderBit, input, receiverState, receiverBit, output
VARIABLES transState, message, ackState

protocolVars == <<senderState, senderBit, input, receiverState, receiverBit, output>>
channelVars == <<transState, message, ackState>>
vars == <<senderState, senderBit, input, receiverState, receiverBit, output, transState, message, ackState>>

Protocol == INSTANCE NaiveProtocol
                WITH senderState <- senderState,
                     senderBit <- senderBit,
                     input <- input,
                     receiverState <- receiverState,
                     receiverBit <- receiverBit,
                     output <- output

Channel == INSTANCE PerfectChannel
               WITH transState <- transState,
                    message <- message,
                    ackState <- ackState


Init == Protocol!Init /\ Channel!Init

Input(m) == Protocol!Input(m) /\ UNCHANGED channelVars
Output == Protocol!Output /\ UNCHANGED channelVars

Send0(m) == Protocol!Send0(m) /\ Channel!Send0(m)
Send1(m) == Protocol!Send1(m) /\ Channel!Send1(m)
Receive0(m) == Protocol!Receive0(m) /\ Channel!Receive0(m)
Receive1(m) == Protocol!Receive1(m) /\ Channel!Receive1(m)
Ack0 == Protocol!Ack0 /\ Channel!Ack0
Ack1 == Protocol!Ack1 /\ Channel!Ack1
GetAck0 == Protocol!GetAck0 /\ Channel!GetAck0
GetAck1 == Protocol!GetAck1 /\ Channel!GetAck1

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

TypeOK == Protocol!TypeOK

MessageReceived == Protocol!MessageReceived

=============================================================================
