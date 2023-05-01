------------------------------- MODULE OAuth -------------------------------

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
CONSTANT None, UID, Cred, AuthCode, AccessToken, Session, Proc,
    AS_tokens,  \* AuthCode -> AccessToken
    AS_codes,   \* UID -> AuthCode
    AS_creds,   \* UID -> Cred
    Proc_cred   \* Proc -> Cred
    
VARIABLE
    client_sessions, \* UID -> Session
    client_codes,    \* Session -> AuthCode
    client_tokens,   \* Session -> AccessToken
    user_session,    \* Proc -> Session
    knows            \* Proc -> AuthCode \cup Cred  
    
TypeOK == /\ client_sessions \in SUBSET Session
          /\ client_codes \in [Session -> AuthCode \cup {None} ]
          /\ client_tokens \in [Session -> AccessToken \cup {None} ]
          /\ user_session \in [Proc -> Session \cup {None}]
          /\ knows \in [Proc -> SUBSET (AuthCode \cup Cred \cup Session \cup {None})]  
          
\* Helper functions
Range(f) == {f[x] : x \in DOMAIN f}        
        
\* Actions
Initiate(proc, session) == 
    /\ client_sessions' = client_sessions \cup {session}
    /\ ~(session \in client_sessions)        \* session created must be a new one
    /\ user_session' = [user_session EXCEPT ![proc] = session]
    /\ knows' = [knows EXCEPT ![proc] = knows[proc] \cup {session}] 
    /\ UNCHANGED << client_codes, client_tokens >>

Authorize(proc, uid, cred, code) == 
    /\ AS_creds[uid] = cred     \* correct credential must be provided
    /\ AS_codes[uid] = code     \* return a unique code for the user with "uid"
 \*   /\ cred \in knows[proc]     \* "proc" must know "cred"
    /\ knows' = [knows EXCEPT ![proc] = knows[proc] \cup {code}]
    /\ UNCHANGED << client_codes, client_tokens, client_sessions, user_session >>

Forward(proc, session, code) ==
    /\ session \in client_sessions
    /\ client_codes' = [client_codes EXCEPT ![session] = code]
    /\ user_session[proc] = session
    /\ code \in knows[proc]
    /\ UNCHANGED << client_tokens, client_sessions, user_session, knows >>
    
GetAccessToken(code, token) ==
    /\ AS_tokens[code] = token 
    /\ \E s \in Session :
        client_codes[s] = code /\
        client_tokens' = [client_tokens EXCEPT ![s] = token]
    /\ UNCHANGED << client_codes, client_sessions, user_session, knows >>
  
  
\* Initial condition
Init == /\ client_sessions = {}
        /\ client_codes = [s \in Session |-> None]
        /\ client_tokens = [s \in Session |-> None]
        /\ user_session = [p \in Proc |-> None]  
        /\ knows = [p \in Proc |-> {Proc_cred[p]}]
    
\* Transition relation                  
Next == 
    \/ \E p \in Proc, s \in Session : Initiate(p, s)
    \/ \E p \in Proc, u \in UID, cr \in Cred, co \in AuthCode : Authorize(p, u, cr, co)    
    \/ \E p \in Proc, s \in Session, c \in AuthCode : Forward(p, s, c)
    \/ \E c \in AuthCode, t \in AccessToken : GetAccessToken(c, t)

=============================================================================
\* Modification History
\* Last modified Sun Apr 30 17:30:26 EDT 2023 by eunsukkang
\* Created Fri Apr 28 21:00:26 EDT 2023 by eunsukkang

