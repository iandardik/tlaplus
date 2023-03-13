------------------------------- MODULE NaiveSender -------------------------------

VARIABLES senderState, senderBit, input

vars == <<senderState, senderBit, input>>

StateValues == {"waitInput", "send", "waitAck"}
BitValues == {0,1}
MessageValues == {"Ian", "David", "Kevin"}

Init ==
    /\ senderState = "waitInput"
    /\ senderBit = 0
    /\ input \in MessageValues

Input(m) ==
    /\ senderState = "waitInput"
    /\ senderState' = "send"
    /\ input' = m
    /\ UNCHANGED<<senderBit>>

Send0(m) ==
    /\ senderState = "send"
    /\ input = m
    /\ senderState' = "waitAck"
    /\ senderBit' = 0
    /\ UNCHANGED<<input>>

Send1(m) ==
    /\ senderState = "send"
    /\ input = m
    /\ senderState' = "waitAck"
    /\ senderBit' = 1
    /\ UNCHANGED<<input>>

GetAck0 ==
    /\ senderState = "waitAck"
    /\ senderBit = 0
    /\ senderState' = "waitInput"
    /\ UNCHANGED<<senderBit, input>>

GetAck1 ==
    /\ senderState = "waitAck"
    /\ senderBit = 1
    /\ senderState' = "waitInput"
    /\ UNCHANGED<<senderBit, input>>

TypeOK ==
    /\ senderState \in {"waitInput", "send", "waitAck"}
    /\ senderBit \in {0,1}
    /\ input \in MessageValues

=============================================================================
