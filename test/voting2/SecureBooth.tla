------------------------------- MODULE SecureBooth -------------------------------

EXTENDS Naturals, FiniteSets

\* choice/ confirm vars are ghost vars
VARIABLES booth, voterChoice, eoChoice, confirmed

vars == <<booth, voterChoice, eoChoice, confirmed>>

Voters == {"voter", "eofficial"}
Candidates == {"Ian","David","Kevin"}

Init ==
    /\ booth = {}
    /\ voterChoice = "None"
    /\ eoChoice = "None"
    /\ confirmed = {}

VEnter ==
    /\ booth = {}
    /\ booth' = {"voter"}
    /\ UNCHANGED<<voterChoice, eoChoice, confirmed>>

VExit ==
    /\ booth = {"voter"}
    /\ booth' = {}
    /\ UNCHANGED<<voterChoice, eoChoice, confirmed>>

EOEnter ==
    /\ booth = {}
    /\ booth' = {"eofficial"}
    /\ UNCHANGED<<voterChoice, eoChoice, confirmed>>

EOExit ==
    /\ booth = {"eofficial"}
    /\ booth' = {}
    /\ UNCHANGED<<voterChoice, eoChoice, confirmed>>

SelectCandidate ==
    \/ /\ booth = {"voter"}
       /\ voterChoice' \in Candidates
       /\ UNCHANGED<<booth, eoChoice, confirmed>>
    \/ /\ booth = {"eofficial"}
       /\ eoChoice' \in Candidates
       /\ UNCHANGED<<booth, voterChoice, confirmed>>

Vote ==
    /\ booth # {}
    /\ UNCHANGED vars

\* confirmation requires the pw in the SecureBooth, so only
\* the voter can confirm.
ConfirmPW ==
    /\ booth = {"voter"}
    /\ confirmed' = confirmed \cup {voterChoice}
    /\ UNCHANGED<<booth, voterChoice, eoChoice>>


Back ==
    /\ booth # {}
    /\ UNCHANGED vars

Next ==
    \/ VEnter
    \/ VExit
    \/ EOEnter
    \/ EOExit
    \/ SelectCandidate
    \/ Vote
    \/ ConfirmPW
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ booth \in SUBSET Voters
    /\ voterChoice \in Candidates \cup {"None"}
    /\ eoChoice \in Candidates \cup {"None"}
    /\ confirmed \in SUBSET (Candidates \cup {"None"})
    \*/\ choice \in [Voters -> Candidates]

OnePersonInBooth == Cardinality(booth) <= 1

=============================================================================
\* Modification History
\* Last modified Wed Feb 22 09:54:28 EST 2023 by idardik
\* Created Wed Feb 22 08:33:35 EST 2023 by idardik

