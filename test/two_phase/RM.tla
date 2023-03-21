------------------------------- MODULE RM ----------------------------- 

RMs == {"rm1", "rm2", "rm3"}

VARIABLES rmState, msgs

Message ==
  [type : {"Prepared"}, rm : RMs]  \cup  [type : {"Commit", "Abort"}]

Init ==   
  /\ rmState = [rm \in RMs |-> "working"]
  /\ msgs = {}

RMPrepare(rm) == 
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  
RMAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<msgs>>

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<msgs>>

TypeOK ==
  /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
  /\ msgs \subseteq Message

=============================================================================
