------------------------------- MODULE SecureVoting -------------------------------

VARIABLES state, booth, voterChoice, eoChoice, confirmed

vars == <<state, booth, voterChoice, eoChoice, confirmed>>
ifaceVars == <<state>>
boothVars == <<booth, eoChoice, confirmed>>

Iface == INSTANCE SecureInterface
            WITH state <- state

Booth == INSTANCE SecureBooth
            WITH booth <- booth,
                 voterChoice <- voterChoice,
                 eoChoice <- eoChoice,
                 confirmed <- confirmed

Init == Iface!Init /\ Booth!Init

VEnter == UNCHANGED ifaceVars /\ Booth!VEnter

VExit == UNCHANGED ifaceVars /\ Booth!VExit

EOEnter == UNCHANGED ifaceVars /\ Booth!EOEnter

EOExit == UNCHANGED ifaceVars /\ Booth!EOExit

SelectCandidate == Iface!SelectCandidate /\ Booth!SelectCandidate

Vote == Iface!Vote /\ Booth!Vote

ConfirmPW == Iface!ConfirmPW /\ Booth!ConfirmPW

Back == Iface!Back /\ Booth!Back

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

TypeOK == Iface!TypeOK /\ Booth!TypeOK
OnePersonInBooth == Booth!OnePersonInBooth

NoVoteFlip ==
    \/ confirmed = {"None"}
    \/ \A c \in confirmed : c = voterChoice

=============================================================================
\* Modification History
\* Last modified Wed Feb 22 09:56:54 EST 2023 by idardik
\* Created Tue Feb 21 22:59:10 EST 2023 by idardik

