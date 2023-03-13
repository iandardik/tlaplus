------------------------------- MODULE PerfectChannel -------------------------------

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES transState, message, ackState

vars == <<transState, message, ackState>>
transVars == <<transState, message>>
ackVars == <<ackState>>

Transmit == INSTANCE PerfectTransmit
            WITH transState <- transState,
                 message <- message

Ack == INSTANCE PerfectAck
            WITH ackState <- ackState

Init == Transmit!Init /\ Ack!Init

Send0(m) == Transmit!Send0(m) /\ UNCHANGED ackVars
Send1(m) == Transmit!Send1(m) /\ UNCHANGED ackVars
Receive0(m) == Transmit!Receive0(m) /\ UNCHANGED ackVars
Receive1(m) == Transmit!Receive1(m) /\ UNCHANGED ackVars

Ack0 == UNCHANGED transVars /\ Ack!Ack0
Ack1 == UNCHANGED transVars /\ Ack!Ack1
GetAck0 == UNCHANGED transVars /\ Ack!GetAck0
GetAck1 == UNCHANGED transVars /\ Ack!GetAck1

Next ==
    \E m \in MessageValues :
        \/ Send0(m)
        \/ Send1(m)
        \/ Receive0(m)
        \/ Receive1(m)
        \/ Ack0
        \/ Ack1
        \/ GetAck0
        \/ GetAck1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ transState \in {"send", "receive"}
    /\ message \in MessageValues
    /\ ackState \in {"ack", "getAck"}

=============================================================================
