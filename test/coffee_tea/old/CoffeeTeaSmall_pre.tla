--------------------------- MODULE CoffeeTeaSmall_pre ---------------------------

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
    /\ temp' \in {212, 225}

BrewHotChocolate ==
    /\ brewed = {}
    /\ brewed' = {"hot_chocolate"}
    /\ temp' = 212

Next ==
    \/ BrewCoffee
    \/ BrewTea
    \/ BrewHotChocolate

WaterSafeTemp == temp <= 220

Next_pre ==
    /\ Next
    /\ ~(brewed = {"coffee"} /\ temp = 212)'
    /\ ~(brewed = {"tea"} /\ temp = 212)'
    /\ ~(brewed = {"hot_chocolate"} /\ temp = 212)'
    
Spec == Init /\ [][Next_pre]_vars /\ SF_vars(Next_pre)


Next_prime ==
    \/ BrewCoffee
    \/ BrewTea
    \*\/ brewed = {} /\ brewed' = {"ian"} /\ temp' = 600

Next_pre_prime ==
    /\ Next_prime
    /\ ~(brewed = {"coffee"} /\ temp = 212)'
    /\ ~(brewed = {"tea"} /\ temp = 212)'
    
Spec_prime == Init /\ [][Next_pre_prime]_vars /\ SF_vars(Next_pre_prime)


TypeOK ==
    /\ brewed \in SUBSET {"coffee", "tea", "hot_chocolate"}
    /\ temp \in Nat

BrewOneItem == \A i1,i2 \in brewed : i1 = i2

=============================================================================
\* Modification History
\* Last modified Thu Feb 09 16:05:27 EST 2023 by idardik
\* Created Thu Feb 09 15:03:34 EST 2023 by idardik


