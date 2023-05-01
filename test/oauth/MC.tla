---- MODULE MC ----
EXTENDS OAuth, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
TokenAlice, TokenEve
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
CodeAlice, CodeEve
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
SessionX, SessionY
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
CredAlice, CredEve
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
IDAlice, IDEve
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
Alice, Eve
----

\* MV CONSTANT definitions AccessToken
const_1682890301330452000 == 
{TokenAlice, TokenEve}
----

\* MV CONSTANT definitions AuthCode
const_1682890301330453000 == 
{CodeAlice, CodeEve}
----

\* MV CONSTANT definitions Session
const_1682890301330454000 == 
{SessionX, SessionY}
----

\* MV CONSTANT definitions Cred
const_1682890301330455000 == 
{CredAlice, CredEve}
----

\* MV CONSTANT definitions UID
const_1682890301330456000 == 
{IDAlice, IDEve}
----

\* MV CONSTANT definitions Proc
const_1682890301330457000 == 
{Alice, Eve}
----

\* CONSTANT definitions @modelParameterConstants:6AS_creds
const_1682890301330458000 == 
(IDAlice :> CredAlice @@ IDEve :> CredEve)
----

\* CONSTANT definitions @modelParameterConstants:7AS_tokens
const_1682890301330459000 == 
(CodeAlice :> TokenAlice @@ CodeEve :> TokenEve)
----

\* CONSTANT definitions @modelParameterConstants:8AS_codes
const_1682890301330460000 == 
(IDAlice :> CodeAlice @@ IDEve :> CodeEve)
----

\* CONSTANT definitions @modelParameterConstants:10Proc_cred
const_1682890301330461000 == 
(Alice :> CredAlice @@ Eve :> CredEve)
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1682890301330463000 ==
[]\A s \in Session : (client_tokens[s] = TokenAlice) => ~(user_session[Eve] = s)
----
=============================================================================
\* Modification History
\* Created Sun Apr 30 17:31:41 EDT 2023 by eunsukkang
