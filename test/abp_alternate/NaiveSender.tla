------------------------------- MODULE NaiveSender -------------------------------

EXTENDS Naturals

VARIABLES senderState, senderBit

vars == <<senderState, senderBit>>

StateValues == {"waitInput", "send", "waitAck"}
BitValues == {0,1}

Init ==
    /\ senderState = "waitInput"
    /\ senderBit \in BitValues

Input ==
    /\ senderState = "waitInput"
    /\ senderState' = "send"
    /\ UNCHANGED<<senderBit>>

Send0 ==
    /\ senderState = "send"
    /\ senderState' = "waitAck"
    /\ senderBit' = 0

Send1 ==
    /\ senderState = "send"
    /\ senderState' = "waitAck"
    /\ senderBit' = 1

GetAck0 ==
    /\ senderState = "waitAck"
    /\ senderBit = 0
    /\ senderState' = "waitInput"
    /\ UNCHANGED<<senderBit>>

GetAck1 ==
    /\ senderState = "waitAck"
    /\ senderBit = 1
    /\ senderState' = "waitInput"
    /\ UNCHANGED<<senderBit>>

TypeOK ==
    /\ senderState \in {"waitInput", "send", "waitAck"}
    /\ senderBit \in {0,1}

=============================================================================
