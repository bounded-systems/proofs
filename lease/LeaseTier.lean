/-!
# Broker lease tier — theorem-proving side of the worked example

The Lean 4 half of this repo's worked example; `LeaseTier.tla` is the
model-checking twin (same transitions, same invariants). Where TLC *checks*
a 2-name/4-token instance exhaustively and prints counterexample traces,
this file *proves* the invariants for all registries, names, and tokens,
unbounded — and the misconfiguration attack becomes a constructed theorem
instead of a found trace.

The system: a bearer-possession lease broker — a request may act on a lease
iff it presents the bearer key that the `LEASE_KEYS` registry assigns to
that lease name. (Applied origin: the `/lease/<name>` broker tier in
`bounded-systems/infra` → `cloudflare/broker/`; the applied copy of this
spec lives in `bdelanghe/infra` `docs/specs/` pending migration next to
that code.)

Mapping to code:

| Spec                    | Code                                        |
|-------------------------|---------------------------------------------|
| `Registry`              | `LEASE_KEYS` (seeded in `wrangler.jsonc`)   |
| `bearerMatches`         | `bearerMatches`                             |
| `Step.acquire/release`  | authorized `/lease/<name>` requests         |
| `Step.deny`             | failed auth on any `/lease/<name>` request  |
| `Step.expire`           | server-side lease expiry (unauthenticated)  |

What is proved (over *all* reachable states, any registry):

* `held_only_by_registered_key` — a lease is only ever held by the exact key
  the registry assigns to it.
* `attacker_never_holds` — if every registry entry is a provisioned key, then
  no unprovisioned token ever holds a lease.
* `guarded_mutation` — every state change either frees a lease or installs
  the registered key; no transition installs an unregistered token.
* `no_silent_handoff` — a held lease never changes hands in a single step;
  it must pass through `free` first.
* `misconfig_attack` — the counterexample: a registry that maps a name to the
  empty token is *provably* attackable, while `held_only_by_registered_key`
  still holds for it. The guard logic is correct against a poisoned registry;
  the failure is configuration. This is the formal shape of the
  "registry misconfiguration paths" attack.

Mutual exclusion (at most one holder per name) is structural: `State` is a
function `Name → Option Token`, so no transition can violate it.
Fail-closed-leaves-state-unchanged is also structural: `Step.deny` relates
`s` to `s` by construction.

Deliberately **not** modeled (see `lease-tier.md` for the discharge
obligations): timing side-channels in `bearerMatches`, response
distinguishability (enumeration oracles), whether `LEASE_KEYS` holds key
material vs. identifiers, `unsafeLeaseEntry` caller invariants, and whether
the expiry path is reachable from a client request.
-/

namespace LeaseTier

abbrev Token := String
abbrev Name  := String

/-- The `LEASE_KEYS` registry: which bearer key controls each lease name.
`none` means the name is not provisioned at all. -/
abbrev Registry := Name → Option Token

/-- Broker state: the token currently holding each lease, if any.
A function representation makes "at most one holder per name" structural —
no transition can express a double-hold. -/
abbrev State := Name → Option Token

/-- The release check: bearer possession, nothing else — by design. -/
def bearerMatches (reg : Registry) (t : Token) (n : Name) : Prop :=
  reg n = some t

/-- All leases free. -/
def initState : State := fun _ => none

/-- One observable transition of the broker: an authorized acquire or
release, a server-side expiry, or a denied request (which, fail-closed,
leaves state unchanged *by construction*). -/
inductive Step (reg : Registry) : State → State → Prop
  | acquire {s : State} {t : Token} {n : Name}
      (auth : bearerMatches reg t n) (free : s n = none) :
      Step reg s (fun m => if m = n then some t else s m)
  | release {s : State} {t : Token} {n : Name}
      (auth : bearerMatches reg t n) (held : s n ≠ none) :
      Step reg s (fun m => if m = n then none else s m)
  | expire {s : State} {n : Name}
      (held : s n ≠ none) :
      Step reg s (fun m => if m = n then none else s m)
  | deny {s : State} {t : Token} {n : Name}
      (noAuth : ¬ bearerMatches reg t n) :
      Step reg s s

/-- States reachable from all-free under a fixed registry. -/
inductive Reachable (reg : Registry) : State → Prop
  | init : Reachable reg initState
  | step {s s' : State} : Reachable reg s → Step reg s s' → Reachable reg s'

/-- **Invariant 1.** A lease is only ever held by the exact key the registry
assigns to its name. -/
theorem held_only_by_registered_key {reg : Registry} {s : State}
    (h : Reachable reg s) : ∀ n t, s n = some t → reg n = some t := by
  induction h with
  | init =>
    intro n t hn
    simp [initState] at hn
  | step _ st ih =>
    intro n t hn
    cases st with
    | @acquire u m auth free =>
      by_cases hnm : n = m
      · subst hnm
        simp at hn
        subst hn
        exact auth
      · simp [hnm] at hn
        exact ih n t hn
    | @release u m auth held =>
      by_cases hnm : n = m
      · subst hnm
        simp at hn
      · simp [hnm] at hn
        exact ih n t hn
    | @expire m held =>
      by_cases hnm : n = m
      · subst hnm
        simp at hn
      · simp [hnm] at hn
        exact ih n t hn
    | deny noAuth =>
      exact ih n t hn

/-- A registry is well-provisioned when every entry is a provisioned key
(the operational content of "`LEASE_KEYS` contains only keys we minted"). -/
def WellProvisioned (reg : Registry) (provisioned : Token → Prop) : Prop :=
  ∀ n k, reg n = some k → provisioned k

/-- **Invariant 2.** Under a well-provisioned registry, no unprovisioned
token (i.e. no attacker-presentable token) ever holds a lease. -/
theorem attacker_never_holds {reg : Registry} {provisioned : Token → Prop}
    (wp : WellProvisioned reg provisioned)
    {s : State} (h : Reachable reg s) :
    ∀ n t, s n = some t → provisioned t :=
  fun n t hn => wp n t (held_only_by_registered_key h n t hn)

/-- **Invariant 3 (guarded mutation).** Every single-step state change at a
name either frees that lease or installs exactly the registered key. No
transition installs an unregistered token. -/
theorem guarded_mutation {reg : Registry} {s s' : State}
    (st : Step reg s s') :
    ∀ n, s' n ≠ s n →
      s' n = none ∨ ∃ t, s' n = some t ∧ bearerMatches reg t n := by
  intro n hne
  cases st with
  | @acquire u m auth free =>
    by_cases hnm : n = m
    · subst hnm
      right
      exact ⟨u, by simp, auth⟩
    · exfalso
      apply hne
      simp [hnm]
  | @release u m auth held =>
    by_cases hnm : n = m
    · subst hnm
      left
      simp
    · exfalso
      apply hne
      simp [hnm]
  | @expire m held =>
    by_cases hnm : n = m
    · subst hnm
      left
      simp
    · exfalso
      apply hne
      simp [hnm]
  | deny noAuth =>
    exact absurd rfl hne

/-- **Invariant 4 (no silent handoff).** A held lease never changes hands in
one step: any transition from `some t` to `some t'` forces `t' = t`. A
takeover must pass through `free`. -/
theorem no_silent_handoff {reg : Registry} {s s' : State}
    (st : Step reg s s') (n : Name) (t t' : Token)
    (before : s n = some t) (after : s' n = some t') : t' = t := by
  cases st with
  | @acquire u m auth free =>
    by_cases hnm : n = m
    · subst hnm
      rw [before] at free
      simp at free
    · simp [hnm] at after
      rw [before] at after
      exact (Option.some.inj after).symm
  | @release u m auth held =>
    by_cases hnm : n = m
    · subst hnm
      simp at after
    · simp [hnm] at after
      rw [before] at after
      exact (Option.some.inj after).symm
  | @expire m held =>
    by_cases hnm : n = m
    · subst hnm
      simp at after
    · simp [hnm] at after
      rw [before] at after
      exact (Option.some.inj after).symm
  | deny noAuth =>
    rw [before] at after
    exact (Option.some.inj after).symm

/-! ## The misconfiguration counterexample

A registry that maps `"db"` to the empty bearer token. Everything above
still holds for it — and that is exactly the point. -/

/-- A poisoned registry: `"db"` is "protected" by the empty token. -/
def badReg : Registry :=
  fun n => if n = "db" then some "" else some ("k-" ++ n)

/-- **The attack.** Against `badReg`, an attacker presenting the empty
bearer token reaches a state where they hold the `"db"` lease. The auth
guard is not bypassed — it passes *legitimately*, because the registry says
`""` is the key. Registry misconfiguration defeats bearer-possession auth
without any bug in the checking code. -/
theorem misconfig_attack :
    ∃ s : State, Reachable badReg s ∧ s "db" = some "" := by
  refine ⟨_, Reachable.step Reachable.init
    (Step.acquire (t := "") (n := "db") ?_ rfl), ?_⟩
  · show badReg "db" = some ""
    simp [badReg]
  · simp

/-- And the guard-correctness invariant *still holds* for `badReg`: the
failure mode is configuration, not logic. A code review of `bearerMatches`
alone cannot catch this class of bug. -/
example {s : State} (h : Reachable badReg s) :
    ∀ n t, s n = some t → badReg n = some t :=
  held_only_by_registered_key h

end LeaseTier
