------------------------------- MODULE ClosedVoting -------------------------------

VARIABLES state, booth, voterChoice, eoChoice, confirmed
VARIABLES envState

votingVars == <<state, booth, voterChoice, eoChoice, confirmed>>
envVars == <<envState>>
vars == <<state, booth, voterChoice, eoChoice, confirmed, envState>>

Voting == INSTANCE Voting
              WITH state <- state,
                   booth <- booth,
                   voterChoice <- voterChoice,
                   eoChoice <- eoChoice,
                   confirmed <- confirmed

Env == INSTANCE Env
           WITH envState <- envState

Init == Voting!Init /\ Env!Init

VEnter == Voting!VEnter /\ Env!VEnter
VExit == Voting!VExit /\ Env!VExit
EOEnter == Voting!EOEnter /\ UNCHANGED envVars
EOExit == Voting!EOExit /\ UNCHANGED envVars
EnterPassword == Voting!EnterPassword /\ Env!EnterPassword
SelectCandidate == Voting!SelectCandidate /\ Env!SelectCandidate
Vote == Voting!Vote /\ Env!Vote
Confirm == Voting!Confirm /\ Env!Confirm
Back == Voting!Back /\ Env!Back

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

TypeOK == Voting!TypeOK /\ Env!TypeOK
OnePersonInBooth == Voting!OnePersonInBooth
NoVoteFlip == Voting!NoVoteFlip
EOCannotConfirm == Voting!EOCannotConfirm

=============================================================================
