--------------------------- MODULE ClosedCTH ---------------------------

VARIABLES brewed, temp
VARIABLES user, location, coff

vars == <<brewed, temp, user, location, coff>>
ctsVars == <<brewed, temp>>
envVars == <<user, location, coff>>

CTS == INSTANCE CoffeeTeaSmall
           WITH brewed <- brewed,
                temp <- temp

Env == INSTANCE Env
           WITH user <- user,
                location <- location,
                coff <- coff

Init == CTS!Init /\ Env!Init

GoToCoffeeMachine == UNCHANGED ctsVars /\ Env!GoToCoffeeMachine
BringCoffeeToDeskAndDrink == UNCHANGED ctsVars /\ Env!BringCoffeeToDeskAndDrink
BrewCoffee == CTS!BrewCoffee /\ Env!BrewCoffee
BrewTea == CTS!BrewTea /\ Env!BrewTea
BrewHotChocolate == CTS!BrewHotChocolate /\ Env!BrewHotChocolate

Next ==
    \/ GoToCoffeeMachine
    \/ BringCoffeeToDeskAndDrink
    \/ BrewCoffee
    \/ BrewTea
    \/ BrewHotChocolate

Spec == Init /\ [][Next]_vars

TypeOK == CTS!TypeOK /\ Env!TypeOK

WaterSafeTemp == CTS!WaterSafeTemp

=============================================================================
