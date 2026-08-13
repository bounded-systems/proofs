/-!
# CI aggregator reducer — order-insensitivity of the observation fold

The Lean 4 half of this pair; `CiState.tla` is the model-checking twin (same
fold, same invariant, plus a misconfigured instance TLC must refute). The
system under specification is the fleet CI aggregator's reducer
(`bounded-systems/bounded.tools` → `src/ci-state.ts`, design in
`.github-private#481`): GitHub `workflow_run` webhooks arrive **unordered**,
and a reconcile poll **replays** history on top of them; the code's whole
answer is "newest-runId-wins makes that safe". This file proves that answer
for all states, keys, and observation sets, unbounded.

Why this property earns the top rung of this repo's ladder: a reordering bug
here does not crash — it serves a stale success over a live failure. Wrong
green, silently, from the component whose only job is to make silent red
visible. (`startup_failure` sat unnoticed on claude-box for two months,
claude-box#254; the aggregator exists so that cannot recur.)

Mapping to code (`bounded.tools/src/ci-state.ts`):

| Spec              | Code                                                |
|-------------------|-----------------------------------------------------|
| `Key`             | the `${repo}::${workflow}` map key                  |
| `Obs`             | `Observation`                                       |
| `Obs.concluded`   | `conclusion !== null`                               |
| `Obs.payload`     | conclusion/sha/runUrl/observedAt (never ordered on) |
| `State`, `init`   | `CiState.entries`, `emptyState()`                   |
| `apply`, `stores` | `applyObservation` (line for line; `stores` names its decision) |
| `applyAll`        | `applyAll` — webhook arrival and reconcile replay   |
| `Coherent`        | GitHub's guarantee that run ids are unique          |

What is proved:

* `applyAll_perm` — **confluence**: folding any permutation of a `Coherent`
  observation list yields the same state. Webhook reordering cannot change
  the answer.
* `applyAll_replay` — **replay absorption**: folding a list and then
  re-folding any sublist of it (the reconcile poll re-covering webhook
  history) is the same as folding the list alone. Notably this needs **no**
  coherence hypothesis: a stored runId never decreases, so a replayed
  observation is always at-or-below the stored runId and is kept out.
* `incoherent_not_confluent` — the counterexample twin: drop `Coherent` and
  confluence is *provably false*. Two observations sharing `(key, runId)`
  with different payloads fold to different states in different orders. The
  hypothesis is load-bearing, not decorative — it is a fact about **GitHub**
  (run ids are unique), not about the code, which is why it must stay
  stated rather than silently assumed. The property-test generator in
  `bounded.tools` enforces the same hypothesis on its random cases.

Deliberately **not** modeled (the discharge obligations):

* **Lost updates.** Confluence covers *reordering* of whole applications; it
  does not cover two racing read-modify-writes clobbering each other. That
  is a different failure mode, discharged at runtime by the Durable Object's
  per-object serialization (`src/ci-do.ts`), not by this proof. Neither
  subsumes the other.
* **Adapter policy.** `completed`-only and default-branch-only filtering
  (`src/github-events.ts`) are judgement calls, not theorems.
* **`Coherent` itself.** GitHub's run-id uniqueness is assumed and shown
  necessary — not proved.
* Snapshot freshness/coverage arithmetic (property-tested in the code repo).
-/

namespace CiState

/-- One `(repo, workflow)` map key — `${repo}::${workflow}` in code. -/
abbrev Key := String

/-- Everything the ordering logic never reads: conclusion, sha, run URL,
observation time. Opaque on purpose — if the fold's result depended on it
beyond storage, these proofs would not close. -/
abbrev Payload := String

/-- `Observation`. `concluded` is `conclusion !== null` in code. -/
structure Obs where
  key : Key
  runId : Nat
  concluded : Bool
  payload : Payload
deriving DecidableEq

/-- `CiState.entries`: at most one stored observation per key — structural
here, an object-shape invariant in code. -/
abbrev State := Key → Option Obs

/-- `emptyState()`. -/
def init : State := fun _ => none

/-- `applyObservation`, line for line: an unconcluded run is ignored (it
carries no verdict); an existing entry with `runId ≥` the incoming one is
kept (first-wins on ties); otherwise the incoming observation is stored. -/
def apply (s : State) (o : Obs) : State :=
  if o.concluded then
    match s o.key with
    | some e => if o.runId ≤ e.runId then s
                else fun k => if k = o.key then some o else s k
    | none   => fun k => if k = o.key then some o else s k
  else s

/-- `applyAll` — the arrival fold, webhook stream and reconcile poll alike. -/
def applyAll (s : State) (l : List Obs) : State := l.foldl apply s

/-- **The confluence hypothesis, named.** Within the observation set, a
`(key, runId)` pair identifies one observation. -/
def Coherent (l : List Obs) : Prop :=
  ∀ o₁, o₁ ∈ l → ∀ o₂, o₂ ∈ l → o₁.key = o₂.key → o₁.runId = o₂.runId → o₁ = o₂

/-! ## The evaluation lemma

`stores` names the decision `applyObservation` makes; `apply_eval` reduces
every later proof to if/arithmetic reasoning instead of match-unfolding. -/

/-- Does `apply` store the incoming observation? Concluded, and strictly
newer than any existing entry at its key. -/
def stores (s : State) (o : Obs) : Bool :=
  o.concluded && match s o.key with
    | some e => decide (e.runId < o.runId)
    | none => true

theorem apply_eval (s : State) (o : Obs) (k : Key) :
    apply s o k = if stores s o = true ∧ k = o.key then some o else s k := by
  unfold apply stores
  by_cases hc : o.concluded
  · simp only [hc, Bool.true_and, if_true]
    cases he : s o.key with
    | none =>
      by_cases hk : k = o.key <;> simp [hk]
    | some e =>
      by_cases hr : o.runId ≤ e.runId
      · have hlt : ¬ e.runId < o.runId := by omega
        simp [hr, hlt]
      · have hlt : e.runId < o.runId := by omega
        by_cases hk : k = o.key <;> simp [hr, hlt, hk]
  · simp [hc]

theorem stores_true_elim {s : State} {o : Obs} (h : stores s o = true) :
    o.concluded = true ∧ ∀ e, s o.key = some e → e.runId < o.runId := by
  unfold stores at h
  by_cases hc : o.concluded
  · refine ⟨hc, ?_⟩
    intro e he
    rw [he] at h
    simpa [hc] using h
  · simp [hc] at h

theorem stores_false_elim {s : State} {o : Obs} (h : stores s o = false)
    (hc : o.concluded = true) :
    ∃ e, s o.key = some e ∧ o.runId ≤ e.runId := by
  unfold stores at h
  cases he : s o.key with
  | none => rw [he] at h; simp [hc] at h
  | some e =>
    rw [he] at h
    simp [hc] at h
    exact ⟨e, rfl, by omega⟩

theorem stores_congr {s t : State} {o : Obs} (h : s o.key = t o.key) :
    stores s o = stores t o := by
  unfold stores
  rw [h]

/-- `stores = false` means `apply` is the identity — the code's early
`return state`, as a state equality rather than a pointwise one. -/
theorem apply_noop {s : State} {o : Obs} (h : stores s o = false) :
    apply s o = s := by
  funext k
  rw [apply_eval]
  simp [h]

theorem apply_update {s : State} {o : Obs} (h : stores s o = true) :
    apply s o = fun k => if k = o.key then some o else s k := by
  funext k
  rw [apply_eval]
  by_cases hk : k = o.key <;> simp [h, hk]

/-- `apply` touches nothing at other keys. -/
theorem apply_other {s : State} {o : Obs} {k : Key} (h : k ≠ o.key) :
    apply s o k = s k := by
  rw [apply_eval]
  simp [h]

/-! ## Replay absorption

The reconcile poll replays history the webhook stream already delivered.
`Covers o s` says the state already holds a verdict at `o`'s key at least as
new as `o`; folding a list containing `o` establishes it, every later
application preserves it, and a covered observation is a no-op. No coherence
hypothesis anywhere in this section. -/

/-- The state already carries a verdict at `o.key` at least as new as `o`. -/
def Covers (o : Obs) (s : State) : Prop :=
  ∃ e, s o.key = some e ∧ o.runId ≤ e.runId

/-- `apply` never deletes, and the stored runId never decreases. -/
theorem apply_keeps {s : State} {o : Obs} {k : Key} {e : Obs}
    (before : s k = some e) :
    ∃ e', apply s o k = some e' ∧ e.runId ≤ e'.runId := by
  rw [apply_eval]
  by_cases h : stores s o = true ∧ k = o.key
  · refine ⟨o, by simp [h], ?_⟩
    have := (stores_true_elim h.1).2 e (h.2 ▸ before)
    omega
  · exact ⟨e, by simp [h, before], Nat.le_refl _⟩

theorem covers_apply {o : Obs} {s : State} (h : Covers o s) (o' : Obs) :
    Covers o (apply s o') := by
  obtain ⟨e, he, hr⟩ := h
  obtain ⟨e', he', hr'⟩ := apply_keeps (o := o') he
  exact ⟨e', he', by omega⟩

theorem covers_applyAll {o : Obs} {s : State} (h : Covers o s) (l : List Obs) :
    Covers o (applyAll s l) := by
  induction l generalizing s with
  | nil => exact h
  | cons x l ih => exact ih (covers_apply h x)

/-- Applying a concluded observation covers it. -/
theorem apply_covers {s : State} {o : Obs} (hc : o.concluded = true) :
    Covers o (apply s o) := by
  by_cases h : stores s o = true
  · rw [apply_update h]
    exact ⟨o, by simp, Nat.le_refl _⟩
  · rw [apply_noop (by simpa using h)]
    obtain ⟨e, he, hr⟩ := stores_false_elim (by simpa using h) hc
    exact ⟨e, he, hr⟩

/-- After folding a list, every concluded member is covered. -/
theorem applyAll_covers {l : List Obs} {o : Obs} (hm : o ∈ l)
    (hc : o.concluded = true) (s : State) : Covers o (applyAll s l) := by
  induction l generalizing s with
  | nil => cases hm
  | cons x l ih =>
    cases hm with
    | head => exact covers_applyAll (apply_covers hc) l
    | tail _ hm => exact ih hm (apply s x)

/-- A covered observation is a no-op. -/
theorem apply_of_covers {s : State} {o : Obs} (h : Covers o s) :
    apply s o = s := by
  obtain ⟨e, he, hr⟩ := h
  apply apply_noop
  unfold stores
  rw [he]
  by_cases hc : o.concluded <;> simp [hc] <;> omega

/-- **Replay absorption.** Folding `l` and then any sublist of it again is
the same as folding `l` alone: the reconcile poll re-covering webhook
history cannot change the state. -/
theorem applyAll_replay {l r : List Obs} (hsub : ∀ o, o ∈ r → o ∈ l)
    (s : State) : applyAll s (l ++ r) = applyAll s l := by
  have step : ∀ (r' : List Obs), (∀ o, o ∈ r' → o ∈ l) →
      applyAll (applyAll s l) r' = applyAll s l := by
    intro r' hsub'
    induction r' with
    | nil => rfl
    | cons x r' ih =>
      have hx : apply (applyAll s l) x = applyAll s l := by
        by_cases hc : x.concluded
        · exact apply_of_covers (applyAll_covers (hsub' x (by simp)) hc s)
        · apply apply_noop
          unfold stores
          simp [hc]
      show applyAll (apply (applyAll s l) x) r' = applyAll s l
      rw [hx]
      exact ih (fun o ho => hsub' o (by simp [ho]))
  calc applyAll s (l ++ r) = applyAll (applyAll s l) r := by
        unfold applyAll; rw [List.foldl_append]
    _ = applyAll s l := step r hsub

/-! ## Confluence -/

/-- Pairwise commutation, given the coherence hypothesis for this one pair.
The only genuinely interesting case is same key, distinct runIds: whichever
order they arrive, the larger runId wins. -/
theorem apply_comm {s : State} {o₁ o₂ : Obs}
    (h : o₁.key = o₂.key → o₁.runId = o₂.runId → o₁ = o₂) :
    apply (apply s o₁) o₂ = apply (apply s o₂) o₁ := by
  by_cases hc₁ : o₁.concluded
  case neg =>
    have n₁ : ∀ t : State, apply t o₁ = t := fun t =>
      apply_noop (by unfold stores; simp [hc₁])
    rw [n₁, n₁]
  by_cases hc₂ : o₂.concluded
  case neg =>
    have n₂ : ∀ t : State, apply t o₂ = t := fun t =>
      apply_noop (by unfold stores; simp [hc₂])
    rw [n₂, n₂]
  by_cases hk : o₁.key = o₂.key
  case neg =>
    -- Different keys: the applications are independent.
    have s₂ : stores (apply s o₁) o₂ = stores s o₂ :=
      stores_congr (apply_other (fun h' => hk h'.symm))
    have s₁ : stores (apply s o₂) o₁ = stores s o₁ :=
      stores_congr (apply_other hk)
    have hk' : ¬ o₂.key = o₁.key := fun h' => hk h'.symm
    funext k
    rw [apply_eval, apply_eval, apply_eval, apply_eval, s₁, s₂]
    by_cases k₁ : k = o₁.key
    · have k₂ : ¬ k = o₂.key := fun h' => hk (k₁ ▸ h')
      by_cases a₁ : stores s o₁ = true <;> simp [k₁, a₁, hk]
    · by_cases k₂ : k = o₂.key <;>
        by_cases a₁ : stores s o₁ = true <;>
        by_cases a₂ : stores s o₂ = true <;>
        simp [k₁, k₂, a₁, a₂, hk']
  -- Same key.
  by_cases hr : o₁.runId = o₂.runId
  case pos => rw [h hk hr]
  -- Same key, distinct runIds: prove it for r₁ < r₂; symmetry gives the rest.
  have main : ∀ (a b : Obs), a.concluded = true → b.concluded = true →
      a.key = b.key → a.runId < b.runId →
      ∀ (t : State), apply (apply t a) b = apply (apply t b) a := by
    intro a b hca hcb hkab hlt t
    cases he : t a.key with
    | none =>
      -- Both would store from empty; b (larger) wins in either order.
      have sa : stores t a = true := by
        unfold stores; rw [he]; simp [hca]
      have sb : stores t b = true := by
        unfold stores; rw [← hkab, he]; simp [hcb]
      have ea := apply_update sa
      have eb := apply_update sb
      -- After a: entry at the shared key is a; b beats it.
      have sb' : stores (apply t a) b = true := by
        unfold stores
        rw [ea]
        simp [← hkab, hcb]
        omega
      have sa' : stores (apply t b) a = false := by
        unfold stores
        rw [eb]
        simp [hkab, hca]
        omega
      rw [apply_update sb', apply_noop sa', ea, eb]
      funext k
      by_cases hkb : k = b.key
      · simp [hkb]
      · have hka : ¬ k = a.key := by rw [hkab]; exact hkb
        simp [hkb, hka]
    | some e =>
      have heb : t b.key = some e := by rw [← hkab]; exact he
      by_cases h₂ : b.runId ≤ e.runId
      · -- Both absorbed either way; e survives untouched.
        have h₁ : a.runId ≤ e.runId := by omega
        have na : apply t a = t := apply_of_covers ⟨e, he, h₁⟩
        have nb : apply t b = t := apply_of_covers ⟨e, heb, h₂⟩
        rw [na, nb, na]
      · by_cases h₁ : a.runId ≤ e.runId
        · -- a absorbed, b stores — in either order.
          have na : apply t a = t := apply_of_covers ⟨e, he, h₁⟩
          rw [na]
          have sb : stores t b = true := by
            unfold stores; rw [heb]; simp [hcb]; omega
          have sa' : stores (apply t b) a = false := by
            unfold stores
            rw [apply_update sb]
            simp [hkab, hca]
            omega
          rw [apply_noop sa']
        · -- Both beat e; b (larger) wins in either order.
          have sa : stores t a = true := by
            unfold stores; rw [he]; simp [hca]; omega
          have sb : stores t b = true := by
            unfold stores; rw [heb]; simp [hcb]; omega
          have ea := apply_update sa
          have eb := apply_update sb
          have sb' : stores (apply t a) b = true := by
            unfold stores
            rw [ea]
            simp [← hkab, hcb]
            omega
          have sa' : stores (apply t b) a = false := by
            unfold stores
            rw [eb]
            simp [hkab, hca]
            omega
          rw [apply_update sb', apply_noop sa', ea, eb]
          funext k
          by_cases hkb : k = b.key
          · simp [hkb]
          · have hka : ¬ k = a.key := by rw [hkab]; exact hkb
            simp [hkb, hka]
  rcases Nat.lt_or_ge o₁.runId o₂.runId with hlt | hge
  · exact main o₁ o₂ hc₁ hc₂ hk hlt s
  · have hlt' : o₂.runId < o₁.runId := by omega
    exact (main o₂ o₁ hc₂ hc₁ hk.symm hlt' s).symm

theorem Coherent.tail {o : Obs} {l : List Obs} (h : Coherent (o :: l)) :
    Coherent l :=
  fun o₁ h₁ o₂ h₂ => h o₁ (by simp [h₁]) o₂ (by simp [h₂])

theorem Coherent.perm {l l' : List Obs} (h : Coherent l) (p : l.Perm l') :
    Coherent l' :=
  fun o₁ h₁ o₂ h₂ => h o₁ (p.mem_iff.mpr h₁) o₂ (p.mem_iff.mpr h₂)

/-- **Confluence.** Folding any permutation of a coherent observation list
yields the same state: webhook reordering cannot change the answer. -/
theorem applyAll_perm {l l' : List Obs} (hc : Coherent l) (p : l.Perm l')
    (s : State) : applyAll s l = applyAll s l' := by
  induction p generalizing s with
  | nil => rfl
  | cons x _ ih =>
    exact ih (Coherent.tail hc) (apply s x)
  | swap x y l =>
    -- (y :: x :: l).Perm (x :: y :: l)
    show applyAll (apply (apply s y) x) l = applyAll (apply (apply s x) y) l
    rw [apply_comm (hc x (by simp) y (by simp))]
  | trans p₁ _ ih₁ ih₂ =>
    exact (ih₁ hc s).trans (ih₂ (hc.perm p₁) s)

/-! ## The counterexample twin

Without `Coherent`, confluence is false — and the failure is silent: both
orders produce a plausible-looking state; they just disagree about which
verdict is current. This is the formal shape of "the hypothesis is about
GitHub, not the code": if run ids were ever reused with different payloads,
the aggregator's answer would depend on delivery order. -/

/-- Two observations sharing `(key, runId)` with different payloads. -/
def obsA : Obs := ⟨"repo::wf", 1, true, "success"⟩
def obsB : Obs := ⟨"repo::wf", 1, true, "failure"⟩

theorem incoherent_not_confluent :
    applyAll init [obsA, obsB] ≠ applyAll init [obsB, obsA] := by
  intro h
  have h' := congrFun h "repo::wf"
  have first : ∀ (o : Obs), o.key = "repo::wf" → o.concluded = true →
      apply init o = fun k => if k = "repo::wf" then some o else none := by
    intro o hk hc
    have : stores init o = true := by
      unfold stores init; simp [hc]
    rw [apply_update this, hk]
    rfl
  have absorb : ∀ (o o' : Obs), o.key = "repo::wf" → o'.key = "repo::wf" →
      o'.runId ≤ o.runId →
      apply (fun k => if k = "repo::wf" then some o else none) o' =
        fun k => if k = "repo::wf" then some o else none := by
    intro o o' hk hk' hr
    exact apply_of_covers ⟨o, by simp [hk'], hr⟩
  have ha : applyAll init [obsA, obsB] "repo::wf" = some obsA := by
    show apply (apply init obsA) obsB "repo::wf" = some obsA
    rw [first obsA rfl rfl, absorb obsA obsB rfl rfl (Nat.le_refl _)]
    simp
  have hb : applyAll init [obsB, obsA] "repo::wf" = some obsB := by
    show apply (apply init obsB) obsA "repo::wf" = some obsB
    rw [first obsB rfl rfl, absorb obsB obsA rfl rfl (Nat.le_refl _)]
    simp
  rw [ha, hb] at h'
  -- `some obsA = some obsB` forces `obsA = obsB`; their payloads differ.
  have : obsA = obsB := Option.some.inj h'
  simp [obsA, obsB] at this

end CiState
