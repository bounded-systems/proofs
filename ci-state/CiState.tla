------------------------------ MODULE CiState ------------------------------
(***************************************************************************)
(* The fleet CI aggregator's reducer as a state machine: GitHub            *)
(* workflow_run observations arrive in ANY order, with redelivery and      *)
(* replay free (the reconcile poll re-covers webhook history), and the     *)
(* newest runId per (repo, workflow) key wins. This is the model-checking  *)
(* twin of CiState.lean — same fold, same claim. Where Lean proves         *)
(* confluence for all instances, TLC checks a small instance over EVERY    *)
(* delivery order and prints a counterexample trace when it fails (see     *)
(* MCCiStateIncoherent.cfg).                                               *)
(*                                                                         *)
(* The claim, stated as an invariant rather than a theorem: at every       *)
(* reachable state, the stored entry per key is a function of WHICH        *)
(* observations have been delivered — never of the order they arrived in.  *)
(* Code: bounded-systems/bounded.tools, src/ci-state.ts                    *)
(* (`applyObservation`); design in .github-private#481.                    *)
(***************************************************************************)

EXTENDS Naturals

CONSTANTS
  Keys,          \* (repo, workflow) map keys — `${repo}::${workflow}` in code
  Payloads,      \* everything the ordering never reads (conclusion, sha, ...)
  Observations,  \* records [key, runId, concluded, payload]
  None           \* marker: no entry stored at a key

ASSUME ObsType ==
  Observations \subseteq
    [key : Keys, runId : Nat, concluded : BOOLEAN, payload : Payloads]
ASSUME NoneFresh == None \notin Observations

VARIABLES
  delivered,  \* the SET of observations that have arrived so far
  state       \* state[k] = the stored observation at key k, or None

TypeOK ==
  /\ delivered \subseteq Observations
  /\ state \in [Keys -> Observations \cup {None}]

(* applyObservation, line for line: unconcluded runs are ignored; an       *)
(* existing entry with runId >= the incoming one is kept (first-wins on    *)
(* ties); otherwise the incoming observation is stored.                    *)
Stored(s, o) ==
  IF ~o.concluded THEN s
  ELSE IF s[o.key] = None THEN [s EXCEPT ![o.key] = o]
  ELSE IF s[o.key].runId < o.runId THEN [s EXCEPT ![o.key] = o]
  ELSE s

Init ==
  /\ delivered = {}
  /\ state = [k \in Keys |-> None]

(* One arrival. o may already be in `delivered`: redelivery and the        *)
(* reconcile poll's replay are the SAME action, and the invariant below    *)
(* must survive them too.                                                  *)
Deliver(o) ==
  /\ o \in Observations
  /\ delivered' = delivered \cup {o}
  /\ state' = Stored(state, o)

Next == \E o \in Observations : Deliver(o)

Spec == Init /\ [][Next]_<<delivered, state>>

----------------------------------------------------------------------------

Concluded(k) == {o \in delivered : o.concluded /\ o.key = k}

(* The canonical answer for a key: the max-runId concluded observation     *)
(* delivered so far. CHOOSE is deterministic, so this is a function of the *)
(* delivered SET alone — which is exactly what makes Confluent an          *)
(* order-insensitivity claim.                                              *)
MaxObs(k) ==
  CHOOSE o \in Concluded(k) : \A o2 \in Concluded(k) : o2.runId <= o.runId

(* THE invariant. If it holds over every reachable state, then no          *)
(* delivery order, redelivery, or replay can make the aggregator's answer  *)
(* depend on arrival order. It is violated exactly when two observations   *)
(* share (key, runId) with different payloads — the incoherent instance —  *)
(* because then first-wins makes the survivor order-dependent while        *)
(* MaxObs, a function of the set, has already committed to one of them.    *)
Confluent ==
  \A k \in Keys :
    IF Concluded(k) = {} THEN state[k] = None ELSE state[k] = MaxObs(k)

=============================================================================
