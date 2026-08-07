------------------------------ MODULE LeaseTier ------------------------------
(***************************************************************************)
(* The broker lease tier as a state machine: a request may act on a lease  *)
(* iff it presents the bearer key the Registry (LEASE_KEYS) assigns to     *)
(* that lease name. This is the model-checking twin of LeaseTier.lean —    *)
(* same transitions, same invariants. TLC checks them exhaustively over a  *)
(* small finite instance (see MCLeaseTier.cfg) and produces counterexample *)
(* traces when they fail (see MCLeaseTierMisconfig.cfg).                   *)
(***************************************************************************)

CONSTANTS
  Names,      \* lease names
  Keys,       \* provisioned bearer keys (the values we minted)
  BadTokens,  \* tokens an attacker can present (guesses, the empty string)
  Free,       \* marker: nobody holds the lease
  Registry    \* [Names -> Keys \cup BadTokens] — the LEASE_KEYS mapping

Tokens == Keys \cup BadTokens

ASSUME KeysDisjoint == Keys \cap BadTokens = {}
ASSUME FreeFresh    == Free \notin Tokens
ASSUME RegistryType == Registry \in [Names -> Tokens]

VARIABLE holder  \* holder[n] = token currently holding n, or Free

TypeOK == holder \in [Names -> Tokens \cup {Free}]

(* The release check: bearer possession, nothing else — by design. *)
bearerMatches(t, n) == t = Registry[n]

Init == holder = [n \in Names |-> Free]

Acquire(t, n) ==
  /\ bearerMatches(t, n)
  /\ holder[n] = Free
  /\ holder' = [holder EXCEPT ![n] = t]

Release(t, n) ==
  /\ bearerMatches(t, n)
  /\ holder[n] # Free
  /\ holder' = [holder EXCEPT ![n] = Free]

(* Server-side expiry: unauthenticated by design (not client-reachable). *)
Expire(n) ==
  /\ holder[n] # Free
  /\ holder' = [holder EXCEPT ![n] = Free]

(* Failed auth: fail-closed, state unchanged by construction. *)
Deny(t, n) ==
  /\ ~bearerMatches(t, n)
  /\ UNCHANGED holder

Next ==
  \/ \E t \in Tokens, n \in Names : Acquire(t, n) \/ Release(t, n) \/ Deny(t, n)
  \/ \E n \in Names : Expire(n)

Spec == Init /\ [][Next]_holder

-----------------------------------------------------------------------------
(* Invariants — the same claims proved unboundedly in LeaseTier.lean.      *)

(* A lease is only ever held by the exact key its name is registered to.  *)
HeldOnlyByRegisteredKey ==
  \A n \in Names : holder[n] # Free => holder[n] = Registry[n]

(* No attacker-presentable token ever holds a lease.                      *)
(* Holds iff the registry is well-provisioned — the misconfig model       *)
(* violates exactly this one.                                             *)
AttackerNeverHolds == \A n \in Names : holder[n] \notin BadTokens

(* Registry well-formedness: every entry is a provisioned key, and no    *)
(* two names share a key (a shared key = cross-name token replay).       *)
RegistryWellProvisioned == \A n \in Names : Registry[n] \in Keys
RegistryInjective == \A m, n \in Names : Registry[m] = Registry[n] => m = n

(* Action properties (checked over every transition):                    *)

(* Every state change frees a lease or installs the registered key.      *)
GuardedMutation ==
  [][\A n \in Names :
       holder'[n] # holder[n] =>
         (holder'[n] = Free \/ holder'[n] = Registry[n])]_holder

(* A held lease never changes hands in one step.                         *)
NoSilentHandoff ==
  [][\A n \in Names :
       (holder[n] # Free /\ holder'[n] # Free) =>
         holder'[n] = holder[n]]_holder

=============================================================================
