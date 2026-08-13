----------------------- MODULE MCCiStateIncoherent -----------------------
(* Incoherent instance: two observations share (key, runId) with          *)
(* different payloads — a reused run id, the thing GitHub promises never  *)
(* happens. TLC finds the confluence violation automatically: first-wins  *)
(* makes the survivor depend on arrival order, so some order disagrees    *)
(* with MaxObs. The reducer is not wrong — the HYPOTHESIS is load-bearing.*)
(* This is the model-checking shape of Lean's `incoherent_not_confluent`. *)
EXTENDS CiState, TLC

IncoherentObs ==
  { [key |-> "a::std", runId |-> 1, concluded |-> TRUE, payload |-> "success"],
    [key |-> "a::std", runId |-> 1, concluded |-> TRUE, payload |-> "failure"] }

=============================================================================
