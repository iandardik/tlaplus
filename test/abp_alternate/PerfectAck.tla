------------------------------- MODULE PerfectAck -------------------------------

VARIABLES ackState

Init == ackState = "ack"

Ack0 ==
    /\ ackState = "ack"
    /\ ackState' = "getAck0"

Ack1 ==
    /\ ackState = "ack"
    /\ ackState' = "getAck1"

GetAck0 ==
    /\ ackState = "getAck0"
    /\ ackState' = "ack"

GetAck1 ==
    /\ ackState = "getAck1"
    /\ ackState' = "ack"

=============================================================================
