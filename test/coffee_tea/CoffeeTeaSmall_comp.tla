--------------------------- MODULE CoffeeTeaSmall_comp ---------------------------

EXTENDS Naturals

VARIABLES brewed, temp

CT == INSTANCE CoffeeTeaSmall
        WITH brewed <- brewed,
             temp <- temp
CTp == INSTANCE CoffeeTeaSmallPrime
        WITH brewed <- brewed,
             temp <- temp

Spec == CT!Spec
Safety == CTp!Spec

=============================================================================
\* Modification History
\* Last modified Thu Feb 09 16:05:27 EST 2023 by idardik
\* Created Thu Feb 09 15:03:34 EST 2023 by idardik


