------------------------------- MODULE ABPReceiver -------------------------------

VARIABLES receiverState, receiverBit, output

vars == <<receiverState, receiverBit, output>>

MessageValues == {"Ian", "David", "Kevin"}
BitValues == {0,1}

Init ==
    /\ receiverState = "waitRec"
    /\ receiverBit \in BitValues
    /\ output \in MessageValues

Receive0(m) ==
    \/ /\ receiverState = "waitRec" \/ receiverState = "ackWaitRec"
       /\ receiverBit = 0
       /\ receiverState' = "output"
       /\ receiverBit' = 1
       /\ output' = m
    \/ /\ receiverState = "ackWaitRec"
       /\ receiverBit = 1
       /\ UNCHANGED vars

Receive1(m) ==
    \/ /\ receiverState = "ackWaitRec"
       /\ receiverBit = 1
       /\ receiverState' = "output"
       /\ receiverBit' = 0
       /\ output' = m
    \/ /\ receiverState = "ackWaitRec"
       /\ receiverBit = 0
       /\ UNCHANGED vars

Output ==
    /\ receiverState = "output"
    /\ receiverState' = "ackWaitRec"
    /\ UNCHANGED<<receiverBit, output>>

Ack0 ==
    /\ receiverState = "ackWaitRec"
    /\ receiverBit = 1
    /\ UNCHANGED vars

Ack1 ==
    /\ receiverState = "ackWaitRec"
    /\ receiverBit = 0
    /\ UNCHANGED vars

TypeOK ==
    /\ receiverState \in {"waitRec", "output", "ackWaitRec"}
    /\ receiverBit \in {0,1}
    /\ output \in MessageValues

=============================================================================
