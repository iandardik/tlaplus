------------------------------- MODULE TM ----------------------------- 

RMs == {"rm1", "rm2", "rm3"}

VARIABLES tmState, tmPrepared, msgs

Message ==
  [type : {"Prepared"}, rm : RMs]  \cup  [type : {"Commit", "Abort"}]

Init ==   
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<tmState, msgs>>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RMs
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<tmPrepared>>

TypeOK ==  
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RMs
  /\ msgs \subseteq Message

=============================================================================
