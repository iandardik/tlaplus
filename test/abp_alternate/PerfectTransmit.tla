------------------------------- MODULE PerfectTransmit -------------------------------

MessageValues == {"Ian", "David", "Kevin"}

VARIABLES transState, message

Init == transState = "send" /\ message \in MessageValues

Send0(m) ==
    /\ transState = "send"
    /\ transState' = "receive0"
    /\ message' = m

Send1(m) ==
    /\ transState = "send"
    /\ transState' = "receive1"
    /\ message' = m

Receive0(m) ==
    /\ message = m
    /\ transState = "receive0"
    /\ transState' = "send"
    /\ UNCHANGED<<message>>

Receive1(m) ==
    /\ message = m
    /\ transState = "receive1"
    /\ transState' = "send"
    /\ UNCHANGED<<message>>

=============================================================================
