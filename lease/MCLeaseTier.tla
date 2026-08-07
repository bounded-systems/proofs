--------------------------- MODULE MCLeaseTier ---------------------------
(* Well-formed instance: every registry entry is a minted key. TLC        *)
(* proves every invariant and action property over the full state space.  *)
EXTENDS LeaseTier, TLC

WellFormedRegistry == ("web" :> "k-web") @@ ("db" :> "k-db")

=============================================================================
