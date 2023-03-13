------------------------------- MODULE PerfectTransmit -------------------------------

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES transState, message

Init == transState = "send" /\ message \in MessageValues

Send0(m) ==
    /\ transState = "send"
    /\ transState' = "receive"
    /\ message' = m

Send1(m) ==
    /\ transState = "send"
    /\ transState' = "receive"
    /\ message' = m

Receive0(m) ==
    /\ message = m
    /\ transState = "receive"
    /\ transState' = "send"
    /\ UNCHANGED<<message>>

Receive1(m) ==
    /\ message = m
    /\ transState = "receive"
    /\ transState' = "send"
    /\ UNCHANGED<<message>>

=============================================================================
