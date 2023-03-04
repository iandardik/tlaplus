------------------------------- MODULE MutexExample -------------------------------

VARIABLES state, pc1, pc2

vars == <<state, pc1, pc2>>
mutexVars == <<state>>
procVars == <<pc1, pc2>>

Mutex == INSTANCE Mutex
            WITH state <- state

Proc == INSTANCE Proc
            WITH pc1 <- pc1,
                 pc2 <- pc2

Init == Mutex!Init /\ Proc!Init

Down == Mutex!Down /\ Proc!Down

Up == Mutex!Up /\ Proc!Up

Next ==
    \/ Up
    \/ Down

Spec == Init /\ [][Next]_vars

TypeOK == Mutex!TypeOK /\ Proc!TypeOK

MutexProperty == pc1 # "cs" \/ pc2 # "cs"

=============================================================================
