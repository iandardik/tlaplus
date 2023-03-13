--------------------------- MODULE Env ---------------------------

VARIABLES user, location, coff

vars == <<user, location, coff>>

Init == user = "unhappy" /\ location = "desk" /\ coff = FALSE

GoToCoffeeMachine ==
    /\ user = "unhappy"
    /\ location = "desk"
    /\ location' = "coffeeMachine"
    /\ UNCHANGED<<user, coff>>

BrewCoffee ==
    /\ location = "coffeeMachine"
    /\ coff' = TRUE
    /\ UNCHANGED<<user, location>>

BringCoffeeToDeskAndDrink ==
    /\ location = "coffeeMachine"
    /\ coff = TRUE
    /\ user' = "happy"
    /\ location' = "desk"
    /\ UNCHANGED<<coff>>

BrewTea == FALSE
BrewHotChocolate == FALSE

TypeOK ==
    /\ user \in {"unhappy", "happy"}
    /\ location \in {"desk", "coffeeMachine"}
    /\ coff \in BOOLEAN

=============================================================================
