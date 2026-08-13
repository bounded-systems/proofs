---------------------------- MODULE MCCiState ----------------------------
(* Coherent instance: run ids are unique per key (GitHub's guarantee).    *)
(* TLC checks Confluent over EVERY delivery order, including redelivery   *)
(* and replay — the exhaustive small-instance twin of Lean's              *)
(* `applyAll_perm` + `applyAll_replay`. Includes an unconcluded run,      *)
(* which must be ignored without disturbing the stored verdict.           *)
EXTENDS CiState, TLC

CoherentObs ==
  { [key |-> "a::std", runId |-> 1, concluded |-> TRUE,  payload |-> "success"],
    [key |-> "a::std", runId |-> 2, concluded |-> TRUE,  payload |-> "failure"],
    [key |-> "a::std", runId |-> 3, concluded |-> FALSE, payload |-> "pending"],
    [key |-> "b::rel", runId |-> 1, concluded |-> TRUE,  payload |-> "startup_failure"],
    [key |-> "b::rel", runId |-> 2, concluded |-> TRUE,  payload |-> "success"] }

=============================================================================
