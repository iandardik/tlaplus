--------------------------- MODULE Combined_ErrPre ---------------------------
VARIABLES brewed, temp

S1 == INSTANCE CoffeeTeaSmall_ErrPre WITH brewed <- brewed, temp <- temp

S2 == INSTANCE CoffeeTeaSmallPrime_ErrPre WITH brewed <- brewed, temp <- temp

Spec == S1!Spec
Safety == S2!Spec
=============================================================================

