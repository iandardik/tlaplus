------------------------------- MODULE ABPReceiver -------------------------------

VARIABLES receiverState, receiverBit, output

vars == <<receiverState, receiverBit, output>>

StateValues == {"waitRec", "output", "ackWaitRec"}
BitValues == {0,1}
MessageValues == {"Ian", "David", "Kevin"}

Init ==
    /\ receiverState = "waitRec"
    /\ receiverBit = 0
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

Next ==
    \E m \in MessageValues :
        \/ Receive0(m)
        \/ Receive1(m)
        \/ Output
        \/ Ack0
        \/ Ack1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ receiverState \in StateValues
    /\ receiverBit \in BitValues
    /\ output \in MessageValues

=============================================================================
