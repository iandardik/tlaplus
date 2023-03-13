------------------------------- MODULE PerfectAck -------------------------------

VARIABLES ackState

Init == ackState = "ack"

Ack0 ==
    /\ ackState = "ack"
    /\ ackState' = "getAck"

Ack1 ==
    /\ ackState = "ack"
    /\ ackState' = "getAck"

GetAck0 ==
    /\ ackState = "getAck"
    /\ ackState' = "ack"

GetAck1 ==
    /\ ackState = "getAck"
    /\ ackState' = "ack"

=============================================================================
