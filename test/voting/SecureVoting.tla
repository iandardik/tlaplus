------------------------------- MODULE SecureVoting -------------------------------

VARIABLES state, booth, voterChoice, eoChoice, eoConfirm

vars == <<state, booth, voterChoice, eoChoice, eoConfirm>>
ifaceVars == <<state>>
boothVars == <<booth, eoChoice, eoConfirm>>

Iface == INSTANCE SecureInterface
            WITH state <- state

Booth == INSTANCE SecureBooth
            WITH booth <- booth,
                 voterChoice <- voterChoice,
                 eoChoice <- eoChoice,
                 eoConfirm <- eoConfirm

Init == Iface!Init /\ Booth!Init

VEnter == UNCHANGED ifaceVars /\ Booth!VEnter

VExit == UNCHANGED ifaceVars /\ Booth!VExit

EOEnter == UNCHANGED ifaceVars /\ Booth!EOEnter

EOExit == UNCHANGED ifaceVars /\ Booth!EOExit

SelectCandidate == Iface!SelectCandidate /\ Booth!SelectCandidate

Vote == Iface!Vote /\ Booth!Vote

Confirm == Iface!Confirm /\ Booth!Confirm

Back == Iface!Back /\ Booth!Back

Next ==
    \/ VEnter
    \/ VExit
    \/ EOEnter
    \/ EOExit
    \/ SelectCandidate
    \/ Vote
    \/ Confirm
    \/ Back

Spec == Init /\ [][Next]_vars

TypeOK == Iface!TypeOK /\ Booth!TypeOK
OnePersonInBooth == Booth!OnePersonInBooth
NoVoteFlip == Booth!NoVoteFlip
EOCannotConfirm == Booth!EOCannotConfirm

=============================================================================
\* Modification History
\* Last modified Wed Feb 22 09:56:54 EST 2023 by idardik
\* Created Tue Feb 21 22:59:10 EST 2023 by idardik

