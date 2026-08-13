# proofs

Formal specification, proved out as a concept — the way a spike repo proves out
OIDC: one small real system, specified twice, checked by machines both times.

## The concept

Describe a system as a **state machine** — initial states plus allowed
transitions — and state **invariants**: properties every reachable state must
satisfy. Then get evidence mechanically instead of by staring:

- A **model checker** (TLA+/TLC) exhaustively explores every reachable state
  of a small finite instance. Near-zero proof effort; when an invariant fails
  you get a concrete step-by-step counterexample trace for free. The evidence
  is "true for 2 names and 4 tokens," not a theorem.
- A **theorem prover** (Lean 4) proves the invariants for *all* instances,
  unbounded. The proof is code your CI re-checks forever. You write every
  proof step by hand.

Same ladder, different rungs. In order of increasing cost and strength:

```
types  →  property-based tests  →  model checking  →  theorem proving
```

Climb only as high as the property deserves. Auth boundaries, consensus,
money, and anything whose failure is silent deserve the top rungs; most code
doesn't.

## The worked example: a bearer-possession lease broker

[`lease/`](./lease) specifies the same system twice — a broker where a request
may act on `/lease/<name>` iff it presents the bearer key a registry
(`LEASE_KEYS`) assigns to that name:

| | TLA+ ([`LeaseTier.tla`](./lease/LeaseTier.tla)) | Lean ([`LeaseTier.lean`](./lease/LeaseTier.lean)) |
|---|---|---|
| A lease is only held by its registered key | invariant, checked over all states of the instance | `held_only_by_registered_key`, proved ∀ |
| Well-provisioned registry ⇒ no foreign token holds | `AttackerNeverHolds` | `attacker_never_holds` |
| Every mutation frees or installs the registered key | `GuardedMutation` (action property) | `guarded_mutation` |
| No takeover without passing through free | `NoSilentHandoff` | `no_silent_handoff` |
| **Poisoned registry defeats perfect guard code** | **found**: TLC emits the attack trace | **constructed**: `misconfig_attack` theorem |

The last row is the lesson twice over. Map a name to the empty token and the
attacker walks in *without any bug in the auth check* — every guard invariant
still holds. TLC discovers this on its own and prints the trace; Lean states
it and proves it. Either way the conclusion is the same and it's one no code
review of the guard function can reach: **bearer auth is exactly as strong as
its registry, so validate the registry.**

Both checkers run in CI on every push — see
[`.github/workflows/check.yml`](./.github/workflows/check.yml). The misconfig
model is asserted to *fail* (exit 12, counterexample found); a green build
means the attack is still found, which is the assertion that matters.

## The second system: the fleet CI aggregator's reducer

[`ci-state/`](./ci-state) applies the same method to a live system —
`bounded-systems/bounded.tools` → `src/ci-state.ts`, the reducer behind the
fleet CI aggregator (`.github-private#481`). GitHub `workflow_run` webhooks
arrive unordered and a reconcile poll replays history; the code's whole
answer is "newest-runId-wins makes that safe":

| | TLA+ ([`CiState.tla`](./ci-state/CiState.tla)) | Lean ([`CiState.lean`](./ci-state/CiState.lean)) |
|---|---|---|
| Delivery order cannot change the answer | `Confluent`, checked over every order incl. redelivery | `applyAll_perm`, proved ∀ |
| Replaying already-delivered history is a no-op | same invariant survives redelivery steps | `applyAll_replay` (needs **no** coherence) |
| **A reused run id defeats a correct reducer** | **found**: TLC emits the order-dependence trace | **constructed**: `incoherent_not_confluent` |

The last row is this system's misconfig twin, and it carries the same lesson:
confluence rests on a **named hypothesis** — `(key, runId)` identifies one
observation — which is a fact about *GitHub* (run ids are unique), not about
the code. Drop it and both checkers show the fold is order-dependent while
every line of the reducer stays "correct". The middle rung for this system
lives with the code: `bounded.tools`' property tests run the same claims
against the shipped TypeScript on every push.

Its stated discharge obligations: **lost updates** (confluence covers
reordering, not racing read-modify-writes — that is the Durable Object's
serialization, `src/ci-do.ts`), adapter policy, and the run-id-uniqueness
hypothesis itself.

## Running locally

```sh
# Lean (any version ≥ 4.32; no dependencies, plain core)
elan default leanprover/lean4:v4.32.2
lean lease/LeaseTier.lean            # silence = all proofs check

# TLC (needs Java 11+)
curl -sSfL -o tla2tools.jar \
  https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
cd lease
java -cp ../tla2tools.jar tlc2.TLC -config MCLeaseTier.cfg MCLeaseTier.tla
java -cp ../tla2tools.jar tlc2.TLC -config MCLeaseTierMisconfig.cfg MCLeaseTierMisconfig.tla
#   ^ expected to end with "Invariant AttackerNeverHolds is violated" + the trace
```

## What a spec cannot do

The model deliberately stops at the state-machine boundary. Timing
side-channels, response-distinguishability oracles, whether the registry file
holds key *material* vs. identifiers, `unsafe*` caller invariants — each of
those is real, unprovable at this level, and discharged by a concrete grep,
probe-pair test, or inspection instead. A spec that doesn't name its
discharge obligations is an alibi, not an artifact.

## Boundary rule

This repo teaches the *method* with worked examples. **Applied** specs — ones
that verify a specific production tier — live next to the code they verify,
and CI there re-checks them. When a spec graduates from here into a codebase,
the copy here becomes the teaching example and stops tracking the code.

## Neighbors worth knowing

- **Quint** — modern typed frontend for the TLA+ ecosystem; same TLC-style checking, friendlier syntax.
- **Alloy** — relational modeling with bounded checking; shines on structural/config problems (schemas, permissions).
- **fast-check / Hypothesis** — property-based testing; the rung below model checking, and the right default for pure functions like diff/plan engines.
- **Dafny / F\*** — SMT-backed verification woven into an implementation language, when you want the proved thing to *be* the program.
- **P** — state-machine language for asynchronous/distributed systems, checked by systematic exploration.
