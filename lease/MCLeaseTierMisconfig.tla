---------------------- MODULE MCLeaseTierMisconfig ----------------------
(* Poisoned instance: "db" is "protected" by the empty token. TLC finds   *)
(* the attack automatically — the counterexample trace shows an attacker  *)
(* presenting "" and acquiring the lease. The auth guard is not bypassed; *)
(* it passes legitimately. Configuration, not logic, is the failure.      *)
EXTENDS LeaseTier, TLC

MisconfiguredRegistry == ("web" :> "k-web") @@ ("db" :> "")

=============================================================================
