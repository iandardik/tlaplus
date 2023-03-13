------------------------------- MODULE PerfectTransmit -------------------------------

VARIABLES transState

Init == transState = "send"

Send0 ==
    /\ transState = "send"
    /\ transState' = "receive"

Send1 ==
    /\ transState = "send"
    /\ transState' = "receive"

Receive0 ==
    /\ transState = "receive"
    /\ transState' = "send"

Receive1 ==
    /\ transState = "receive"
    /\ transState' = "send"

=============================================================================
