------------------------------- MODULE OAuthHC_flat -------------------------------

(***************************************************************************)
(*                                                                         *)
(* This module specifies a model of the OAuth 2.0 protocol.                *)
(* Informal explanation of the protocol:                                   *) 
(*   https://eskang.github.io/assets/papers/sead20.pdf                     *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Naturals

\* UID: User ID
\* CRED: User credentials (i.e., passwords)
\* AUTHCODE: Authorization codes
\* ACCESSTOKEN: Access tokens
\* SESSION: Session tokens
None == "None"
UID == { "IDAlice", "IDEve" }
Cred == { "CredAlice", "CredEve" }
AuthCode == { "CodeAlice", "CodeEve" }
AccessToken == { "TokenAlice", "TokenEve" }
Session == { "SessionX", "SessionY" }
Proc == { "Alice", "Eve" }
\* AuthCode -> AccessToken
\* Ugly, but it doesn't let me define it using function notation [ a |-> b...]
AS_tokens(x) == 
    CASE x = "CodeAlice" -> "TokenAlice"
    [] x = "CodeEve" -> "TokenEve"
    [] OTHER -> "None"
\* UID -> AuthCode
AS_codes(x) ==
    CASE x = "IDAlice" -> "CodeAlice"
    [] x = "IDEve" -> "CodeEve"
    [] OTHER -> "None"
\* UID -> Cred
AS_creds(x) == 
    CASE x = "IDAlice" -> "CredAlice"
    [] x = "IDEve" -> "CredEve"
    [] OTHER -> "None"
\* Proc -> Cred
Proc_cred(x) == 
    CASE x = "Alice" -> "CredAlice"
    [] x = "Eve" -> "CredEve"
    [] OTHER -> "None"
    
VARIABLE
    client_sessions, \* Session -> Boolean
    client_codes,    \* Session -> AuthCode
    client_tokens,   \* Session -> AccessToken
    user_session,    \* Proc -> Session
    knows_alice,     \* (AuthCode \cup Cred \cup ...) -> Boolean
    knows_eve        \* (AuthCode \cup Cred \cup ...) -> Boolean
    
TypeOK == /\ client_sessions \in [Session -> BOOLEAN]
          /\ client_codes \in [Session -> AuthCode \cup {None} ]
          /\ client_tokens \in [Session -> AccessToken \cup {None} ]
          /\ user_session \in [Proc -> Session \cup {None}]
          /\ knows_alice \in [(AuthCode \cup Session) -> BOOLEAN]  
          /\ knows_eve \in [(AuthCode \cup Session) -> BOOLEAN]  
          
\* Helper functions
Range(f) == {f[x] : x \in DOMAIN f}        
        
\* Actions
Initiate(proc, session) == 
    /\ client_sessions' = [client_sessions EXCEPT ![session] = TRUE]
    /\ client_sessions[session] = FALSE        \* session created must be a new one
    /\ user_session' = [user_session EXCEPT ![proc] = session]
    /\ IF proc = "Alice" THEN 
        (knows_alice' = [knows_alice EXCEPT ![session] = TRUE] /\
         knows_eve' = knows_eve)
       ELSE   
        (knows_eve' = [knows_eve EXCEPT ![session] = TRUE] /\
         knows_alice' = knows_alice)
    /\ UNCHANGED << client_codes, client_tokens >>

Authorize(proc, uid, cred, code) == 
    /\ AS_creds(uid) = cred     \* correct credential must be provided
    /\ AS_codes(uid) = code     \* return a unique code for the user with "uid"
 \*   /\ IF proc = "Alice" THEN cred = "CredAlice" ELSE cred = "CredEve"
    /\ IF proc = "Alice" THEN 
        (knows_alice' = [knows_alice EXCEPT ![code] = TRUE] /\
         knows_eve' = knows_eve)
       ELSE   
        (knows_eve' = [knows_eve EXCEPT ![code] = TRUE] /\
         knows_alice' = knows_alice)
    /\ UNCHANGED << client_codes, client_tokens, client_sessions, user_session >>

Forward(proc, session, code) ==
    /\ client_sessions[session] = TRUE
    /\ client_codes' = [client_codes EXCEPT ![session] = code]
    /\ user_session[proc] = session
    /\ IF proc = "Alice" THEN knows_alice[code] = TRUE ELSE knows_eve[code] = TRUE
    /\ UNCHANGED << client_tokens, client_sessions, user_session, knows_alice, knows_eve >>
    
GetAccessToken(code, token) ==
    /\ AS_tokens(code) = token 
    /\ \E s \in Session :
        client_codes[s] = code /\
        client_tokens' = [client_tokens EXCEPT ![s] = token]
    /\ UNCHANGED << client_codes, client_sessions, user_session, knows_alice, knows_eve >>
  
  
\* Initial condition
Init == /\ client_sessions = [s \in Session |-> FALSE]
        /\ client_codes = [s \in Session |-> None]
        /\ client_tokens = [s \in Session |-> None]
        /\ user_session = [p \in Proc |-> None]  
        /\ knows_alice = [k \in (AuthCode \cup Session) |-> FALSE]
        /\ knows_eve = [k \in (AuthCode \cup Session) |-> FALSE]
    
\* Transition relation                  
Next == 
    \/ \E p \in Proc, s \in Session : Initiate(p, s)
    \/ \E p \in Proc, u \in UID, cr \in Cred, co \in AuthCode : Authorize(p, u, cr, co)    
    \/ \E p \in Proc, s \in Session, c \in AuthCode : Forward(p, s, c)
    \/ \E c \in AuthCode, t \in AccessToken : GetAccessToken(c, t)

SessionIntegrity ==
    []\A s \in Session : (client_tokens[s] = "TokenAlice") => ~(user_session["Eve"] = s)

=============================================================================
\* Modification History
\* Last modified Tue May 02 23:02:00 EDT 2023 by eunsukkang
\* Created Fri Apr 28 21:00:26 EDT 2023 by eunsukkang


