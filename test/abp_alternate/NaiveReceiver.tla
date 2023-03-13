------------------------------- MODULE NaiveReceiver -------------------------------

EXTENDS Naturals

VARIABLES receiverState, receiverBit

vars == <<receiverState, receiverBit>>

MessageValues == {"Ian", "David", "Kevin"}
BitValues == {0,1}

Init ==
    /\ receiverState = "waitRec"
    /\ receiverBit \in BitValues

Receive0 ==
    /\ receiverState = "waitRec"
    /\ receiverState' = "output"
    /\ receiverBit' = 0

Receive1 ==
    /\ receiverState = "waitRec"
    /\ receiverState' = "output"
    /\ receiverBit' = 1

Output ==
    /\ receiverState = "output"
    /\ receiverState' = "ack"
    /\ UNCHANGED<<receiverBit>>

Ack0 ==
    /\ receiverState = "ack"
    /\ receiverBit = 0
    /\ receiverState' = "waitRec"
    /\ UNCHANGED<<receiverBit>>

Ack1 ==
    /\ receiverState = "ack"
    /\ receiverBit = 1
    /\ receiverState' = "waitRec"
    /\ UNCHANGED<<receiverBit>>

TypeOK ==
    /\ receiverState \in {"waitRec", "output", "ack"}
    /\ receiverBit \in {0,1}

=============================================================================
