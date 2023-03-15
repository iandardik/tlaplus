------------------------------- MODULE VotingWithDirections -------------------------------

VARIABLES state, booth, voterChoice, eoChoice, confirmed
VARIABLES dirState

vars == <<state, booth, voterChoice, eoChoice, confirmed, dirState>>
votingVars == <<state, booth, voterChoice, eoChoice, confirmed>>
dirVars == <<dirState>>

Voting == INSTANCE Voting
              WITH state <- state,
                   booth <- booth,
                   voterChoice <- voterChoice,
                   eoChoice <- eoChoice,
                   confirmed <- confirmed

Directions == INSTANCE Directions
                  WITH dirState <- dirState

Init == Voting!Init /\ Directions!Init

VEnter == Voting!VEnter /\ UNCHANGED dirVars
VExit == Voting!VExit /\ UNCHANGED dirVars
EOEnter == Voting!EOEnter /\ UNCHANGED dirVars
EOExit == Voting!EOExit /\ UNCHANGED dirVars
EnterPassword == Voting!EnterPassword /\ UNCHANGED dirVars
SelectCandidate == Voting!SelectCandidate /\ UNCHANGED dirVars
Vote == Voting!Vote /\ UNCHANGED dirVars
Confirm == Voting!Confirm /\ UNCHANGED dirVars
Back == Voting!Back /\ UNCHANGED dirVars

ToDirectionMenu == UNCHANGED votingVars /\ Directions!ToDirectionMenu
LeaveDirectionMenu == UNCHANGED votingVars /\ Directions!LeaveDirectionMenu

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
    \/ ToDirectionMenu
    \/ LeaveDirectionMenu

Spec == Init /\ [][Next]_vars

TypeOK == Voting!TypeOK /\ Directions!TypeOK
OnePersonInBooth == Voting!OnePersonInBooth
NoVoteFlip == Voting!NoVoteFlip
EOCannotConfirm == Voting!EOCannotConfirm

=============================================================================
