------------------------------- MODULE TwoPhase ----------------------------- 

VARIABLES rmState, tmState, tmPrepared, msgs

vars == <<rmState, tmState, tmPrepared, msgs>>
tmVars == <<tmState, tmPrepared>>
rmVars == <<rmState>>

RMs == {"rm1", "rm2", "rm3"}
Message == [type : {"Prepared"}, rm : RMs]  \cup  [type : {"Commit", "Abort"}]

TM == INSTANCE TM
          WITH tmState <- tmState,
               tmPrepared <- tmPrepared,
               msgs <- msgs

RM == INSTANCE RM
          WITH rmState <- rmState,
               msgs <- msgs

Init == TM!Init /\ RM!Init

TMRcvPrepared(rm) == TM!TMRcvPrepared(rm) /\ UNCHANGED rmVars
TMCommit == TM!TMCommit /\ UNCHANGED rmVars
TMAbort == TM!TMAbort /\ UNCHANGED rmVars
RMPrepare(rm) == UNCHANGED tmVars /\ RM!RMPrepare(rm)
RMAbort(rm) == UNCHANGED tmVars /\ RM!RMAbort(rm)
RMRcvCommitMsg(rm) == UNCHANGED tmVars /\ RM!RMRcvCommitMsg(rm)
RMRcvAbortMsg(rm) == UNCHANGED tmVars /\ RM!RMRcvAbortMsg(rm)

Next ==
  \/ TMCommit
  \/ TMAbort
  \/ \E rm \in RMs : 
    \/ TMRcvPrepared(rm)
    \/ RMPrepare(rm)
    \/ RMAbort(rm)
    \/ RMRcvCommitMsg(rm)
    \/ RMRcvAbortMsg(rm)

Spec == Init /\ [][Next]_vars

TypeOK == TM!TypeOK /\ RM!TypeOK

Consistent == \A rm1, rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
