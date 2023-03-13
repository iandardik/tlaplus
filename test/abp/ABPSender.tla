------------------------------- MODULE ABPSender -------------------------------

VARIABLES senderState, senderBit, input

vars == <<senderState, senderBit, input>>

StateValues == {"waitInput", "send", "waitAck"}
BitValues == {0,1}
MessageValues == {"Ian", "David", "Kevin"}

Init ==
    /\ senderState = "waitInput"
    /\ senderBit \in BitValues
    /\ input \in MessageValues

Input(m) ==
    /\ senderState = "waitInput"
    /\ senderState' = "send"
    /\ input' = m
    /\ UNCHANGED<<senderBit>>

Send0(m) ==
    /\ senderState = "send"
    /\ input = m
    /\ senderBit = 0
    /\ UNCHANGED vars

Send1(m) ==
    /\ senderState = "send"
    /\ input = m
    /\ senderBit = 1
    /\ UNCHANGED vars

GetAck0 ==
    \/ /\ senderState = "send"
       /\ senderBit = 0
       /\ senderState' = "waitInput"
       /\ senderBit' = 1
       /\ UNCHANGED<<input>>
    \/ /\ senderState = "send"
       /\ senderBit = 1
       /\ UNCHANGED vars

GetAck1 ==
    \/ /\ senderState = "send"
       /\ senderBit = 1
       /\ senderState' = "waitInput"
       /\ senderBit' = 0
       /\ UNCHANGED<<input>>
    \/ /\ senderState = "send"
       /\ senderBit = 0
       /\ UNCHANGED vars

TypeOK ==
    /\ senderState \in {"waitInput", "send"}
    /\ senderBit \in {0,1}
    /\ input \in MessageValues

=============================================================================
