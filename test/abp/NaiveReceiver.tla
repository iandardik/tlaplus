------------------------------- MODULE NaiveReceiver -------------------------------

VARIABLES receiverState, receiverBit, output

vars == <<receiverState, receiverBit, output>>

MessageValues == {"Ian", "David", "Kevin"}
BitValues == {0,1}

Init ==
    /\ receiverState = "waitRec"
    /\ receiverBit \in BitValues
    /\ output \in MessageValues

Receive0(m) ==
    /\ receiverState = "waitRec"
    /\ receiverState' = "output"
    /\ receiverBit' = 0
    /\ output' = m

Receive1(m) ==
    /\ receiverState = "waitRec"
    /\ receiverState' = "output"
    /\ receiverBit' = 1
    /\ output' = m

Output ==
    /\ receiverState = "output"
    /\ receiverState' = "ack"
    /\ UNCHANGED<<receiverBit, output>>

Ack0 ==
    /\ receiverState = "ack"
    /\ receiverBit = 0
    /\ receiverState' = "waitRec"
    /\ UNCHANGED<<receiverBit, output>>

Ack1 ==
    /\ receiverState = "ack"
    /\ receiverBit = 1
    /\ receiverState' = "waitRec"
    /\ UNCHANGED<<receiverBit, output>>

TypeOK ==
    /\ receiverState \in {"waitRec", "output", "ack"}
    /\ receiverBit \in {0,1}
    /\ output \in MessageValues

=============================================================================
