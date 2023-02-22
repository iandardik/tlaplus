------------------------------- MODULE Booth -------------------------------

EXTENDS Naturals, FiniteSets

\* choice/ confirm vars are ghost vars
VARIABLES booth, voterChoice, eoChoice, eoConfirm

vars == <<booth, voterChoice, eoChoice, eoConfirm>>

Voters == {"voter", "eofficial"}
Candidates == {"Ian","David","Kevin"}

Init ==
    /\ booth = {}
    /\ voterChoice = "None"
    /\ eoChoice = "None"
    /\ eoConfirm = "None"

VEnter ==
    /\ booth = {}
    /\ booth' = {"voter"}
    /\ UNCHANGED<<voterChoice, eoChoice, eoConfirm>>

VExit ==
    /\ booth = {"voter"}
    /\ booth' = {}
    /\ UNCHANGED<<voterChoice, eoChoice, eoConfirm>>

EOEnter ==
    /\ booth = {}
    /\ booth' = {"eofficial"}
    /\ UNCHANGED<<voterChoice, eoChoice, eoConfirm>>

EOExit ==
    /\ booth = {"eofficial"}
    /\ booth' = {}
    /\ UNCHANGED<<voterChoice, eoChoice, eoConfirm>>

EnterPassword ==
    /\ booth = {"voter"}
    /\ UNCHANGED vars

SelectCandidate ==
    \/ /\ booth = {"voter"}
       /\ voterChoice' \in Candidates
       /\ UNCHANGED<<booth, eoChoice, eoConfirm>>
    \/ /\ booth = {"eofficial"}
       /\ eoChoice' \in Candidates
       /\ UNCHANGED<<booth, voterChoice, eoConfirm>>

Vote ==
    /\ booth # {}
    /\ UNCHANGED vars

Confirm ==
    \/ /\ booth = {"voter"}
       /\ UNCHANGED vars
    \/ /\ booth = {"eofficial"}
       /\ eoConfirm' = eoChoice
       /\ UNCHANGED<<booth, voterChoice, eoChoice>>

Back ==
    /\ booth # {}
    /\ UNCHANGED vars

Next ==
    \/ VEnter
    \/ VExit
    \/ EOEnter
    \/ EOExit
    \/ EnterPassword
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ booth \in SUBSET Voters
    /\ voterChoice \in Candidates \cup {"None"}
    /\ eoChoice \in Candidates \cup {"None"}
    /\ eoConfirm \in Candidates \cup {"None"}
    \*/\ choice \in [Voters -> Candidates]

OnePersonInBooth == Cardinality(booth) <= 1

NoVoteFlip == eoConfirm = "None" \/ eoConfirm = voterChoice
EOCannotConfirm == eoConfirm = "None"

=============================================================================
\* Modification History
\* Last modified Wed Feb 22 09:54:28 EST 2023 by idardik
\* Created Wed Feb 22 08:33:35 EST 2023 by idardik

