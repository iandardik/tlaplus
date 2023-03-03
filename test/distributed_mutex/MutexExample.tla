------------------------------- MODULE MutexExample -------------------------------

CONSTANTS ProcSet

VARIABLES state, pc

vars == <<state, pc>>
mutexVars == <<state>>
procVars == <<pc>>

Mutex == INSTANCE Mutex
            WITH state <- state

Proc == INSTANCE Proc
            WITH pc <- pc

Init == Mutex!Init /\ Proc!Init

Down == Mutex!Down /\ Proc!Down

Up == Mutex!Up /\ Proc!Up

Next ==
    \/ Up
    \/ Down

Spec == Init /\ [][Next]_vars

TypeOK == Mutex!TypeOK /\ Proc!TypeOK

MutexProperty ==
    \A p,q \in ProcSet :
        (pc[p] = "cs" /\ pc[q] = "cs") => (p = q)

=============================================================================
