------------------------------- MODULE ABPSender -------------------------------

VARIABLES senderState, senderBit, input

vars == <<senderState, senderBit, input>>

StateValues == {"waitInput", "send"}
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

Next ==
    \E m \in MessageValues :
        \/ Input(m)
        \/ Send0(m)
        \/ Send1(m)
        \/ GetAck0
        \/ GetAck1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ senderState \in StateValues
    /\ senderBit \in BitValues
    /\ input \in MessageValues

=============================================================================
