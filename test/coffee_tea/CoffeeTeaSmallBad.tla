--------------------------- MODULE CoffeeTeaSmallBad ---------------------------

EXTENDS Naturals

VARIABLES brewed, temp

vars == <<brewed, temp>>

Init == brewed = {} /\ temp = 70

BrewCoffee ==
    /\ brewed = {}
    /\ brewed' = {"coffee"}
    /\ temp' = 212

BrewTea ==
    /\ brewed = {}
    /\ brewed' = {"tea"}
    /\ temp' \in {212, 225, 230}

BrewHotChocolate ==
    /\ brewed = {}
    /\ brewed' = {"hot_chocolate"}
    /\ temp' \in {212, 225}

Next ==
    \/ BrewCoffee
    \/ BrewTea
    \/ BrewHotChocolate
    
Spec == Init /\ [][Next]_vars

WaterSafeTemp == temp <= 220
WaterSafeTempProp == [][WaterSafeTemp]_vars

TypeOK ==
    /\ brewed \in SUBSET {"coffee", "tea", "hot_chocolate"}
    /\ temp \in Nat

BrewOneItem == \A i1,i2 \in brewed : i1 = i2

OnlyErrors == [][~WaterSafeTemp]_vars
OnlyErrorsInv == ~WaterSafeTemp

=============================================================================
\* Modification History
\* Last modified Thu Feb 09 16:05:27 EST 2023 by idardik
\* Created Thu Feb 09 15:03:34 EST 2023 by idardik

