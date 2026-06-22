/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.WellSynchronized
import Mathlib.Data.Finset.Sort

/-!
# The well-synchronization check (§4.2, Figure 4)

`CheckWellSynchronized` is the executable algorithm of Figure 4 (`WELLSYNC`) of the
Weft paper: given a CTA `T` and *one* concrete complete trace `τ` that runs
`(I, T)` to `done` (Figure 4's `assume τ ≡ (I, T), …, (F, done)`), it returns a
`Bool` that is `true` iff `T` is well-synchronized (Definition 6), together with the
computed happens-before relation (the transitive closure of Figure 4 line 17).

The idea (paper §4.2) is to read the generation map `Gen(τ)` off the *single*
concrete trace, build a static happens-before relation `R` that *every* schedule
must respect, take its transitive closure, and then check that `R` already forces
each later-generation barrier operation to wait for the matching earlier-generation
`sync`. If it does, no alternative schedule could pair the synchronizations up
differently, so all traces share `Gen(τ)` and `T` is well-synchronized.

This is the *checking* side of the development; the `*.WellSynchronized` predicates
of `Weft.WellSynchronized` are the *specification* (Definitions 6–7). We implement
the algorithm faithfully but do not yet prove the paper's soundness/completeness
(Definitions 9–10) linking the two.

## Computable `Gen(τ)` (`pointGen`)

`Gen(τ)` is Definition 5's relation `IsGenOf` turned into a function on program
points. Its two ingredients, time and recycle-counting, are already computable:
`recycleCount` counts recyclings directly from the trace, and the time `t(τ, η)` is
found by `pointTime`. We locate the executing step of `η = ⟨i, k⟩` by program
*length*: thread `i`'s remaining program shrinks only by dropping prefixes (it is
always a suffix of `T.prog i`, by `CTAStep.progOf_suffix`), so a suffix is pinned
down by its length. Instruction `k` executes at the step where thread `i`'s
remaining length falls from `|T.prog i| − k` to `|T.prog i| − k − 1` — for a `sync`
this is the recycle step, exactly as in Definition 3. This matches `IsTimeOf` /
`IsGenOf` on a genuine trace from `(I, T)` (the 1-indexed `+ 1` convention, with `0`
for a command that never executes — see the `IsGenOf` doc).
-/

namespace Weft

-- Decidable equality on program points, needed to manipulate `R` as a list of
-- edges (membership and transitive closure). A `deriving instance` command takes
-- no docstring, hence the line comment.
deriving instance DecidableEq for ProgPoint

/-- The command at program point `η = ⟨i, k⟩`, read from `T`'s static programs:
command `k` of thread `i`, or `none` if out of range. Agrees with `η.cmd` at the
configuration `(I, T)`, since `(Config.run s T).progOf i = T.prog i`. -/
def CTA.cmdAt (T : CTA) (η : ProgPoint) : Option Cmd := (T.prog η.thread)[η.idx]?

/-- All program points of a CTA: every `⟨i, k⟩` with `i ∈ T.ids` and `k` a valid
index into thread `i`'s program. These are the "commands `c`" the algorithm ranges
over. -/
def CTA.progPoints (T : CTA) : List ProgPoint :=
  (T.ids.sort (· ≤ ·)).flatMap fun i =>
    (List.range (T.prog i).length).map fun k => ⟨i, k⟩

/-- The computable time `t(τ, η)` (Definition 3): the 1-indexed step of `τ` at
which `η = ⟨i, k⟩` executes, or `none` if it never does. Found by matching the
remaining-program *length* of thread `i` across consecutive configurations (see the
module doc): the step from `C` to `C'` runs `η` exactly when `C` still has the
`|T.prog i| − k`-length suffix and `C'` has the `(|T.prog i| − k − 1)`-length one. -/
def pointTime (T : CTA) (τ : List Config) (η : ProgPoint) : Option Nat :=
  let L := (T.prog η.thread).length
  if η.idx < L then
    (List.range (τ.length - 1)).findSome? fun j =>
      match τ[j]?, τ[j + 1]? with
      | some C, some C' =>
          if (C.progOf η.thread).length == L - η.idx
              && (C'.progOf η.thread).length == L - η.idx - 1 then
            some (j + 1)
          else
            none
      | _, _ => none
  else
    none

/-- The computable generation `Gen(τ)(cη)` (Definition 5), as a function. Defined
only on synchronization commands (`some b = cη.barrier?`): an executed one gets
`recycleCount b τ (m − 1) + 1 ≥ 1` (recyclings strictly before its step `m`, then
1-indexed), an unexecuted one gets `0`, and a `read`/`write` (not in `Gen`'s
domain) is reported as `0`. -/
def pointGen (T : CTA) (τ : List Config) (η : ProgPoint) : Nat :=
  match (T.cmdAt η).bind Cmd.barrier? with
  | none => 0
  | some b =>
      match pointTime T τ η with
      | none => 0
      | some m => recycleCount b τ (m - 1) + 1

/-! ## Transitive closure of a finite edge relation (Figure 4 line 17)

The relation `R` is a `Finset (ProgPoint × ProgPoint)` of edges; `transClosure R`
is its transitive closure, again a finite set of pairs. -/

/-- The transitive closure of a relation given as a finite set of edges `R`:
repeatedly add a composed edge `(e.1, f.2)` whenever `e ∈ S` and `f ∈ R` meet at
`e.2 = f.1`. Saturating for `R.card` rounds suffices, since a simple path uses at
most `|R|` edges. -/
def transClosure {α : Type*} [DecidableEq α] (R : Finset (α × α)) : Finset (α × α) :=
  let addStep : Finset (α × α) → Finset (α × α) := fun S =>
    S ∪ S.biUnion fun e => (R.filter fun f => e.2 = f.1).image fun f => (e.1, f.2)
  addStep^[R.card] R

-- TODO(proof): prove `transClosure` correct, i.e.
--   `(a, b) ∈ transClosure R ↔ Relation.TransGen (fun x y => (x, y) ∈ R) a b`.
-- This includes justifying the `R.card`-rounds saturation bound (a simple path uses
-- at most `|R|` edges, so the fixpoint is reached within `R.card` rounds). The
-- `Relation.TransGen` direction gives access to its induction API for the eventual
-- soundness proof of `CheckWellSynchronized`.

/-! ## Figure 4 (`WELLSYNC`)

`CheckWellSynchronized` is a direct transcription of Figure 4's three steps: build
the relation `R` from the generation map (lines 4–16), take its transitive closure
(line 17), then run the pairwise check (lines 18–22). -/

/-- Step 1 of Figure 4 (lines 4–16): build the happens-before relation `R` as a
finite set of edges, using the generation map `G = pointGen T τ`.

* **lines 4–6** — intra-thread program order `⟨i, k⟩ → ⟨i, k+1⟩`;
* **lines 7–11** — `arrive b n → sync b n` of equal generation (an `arrive`
  happens-before the same-generation `sync` that closes the round);
* **lines 12–16** — `sync b n ↔ sync b n` of equal generation, both directions
  (syncs of one generation all recycle together, so they are mutually ordered). -/
def initRelation (T : CTA) (τ : List Config) : Finset (ProgPoint × ProgPoint) :=
  let pts := T.progPoints
  let G : ProgPoint → Nat := fun η => pointGen T τ η
  -- lines 4–6: program order `(c1 ; c2)`
  let progOrder : List (ProgPoint × ProgPoint) := pts.filterMap fun c =>
    if c.idx + 1 < (T.prog c.thread).length then some (c, ⟨c.thread, c.idx + 1⟩) else none
  -- lines 7–11: `arrive b n → sync b n` of the same generation
  let arriveSync : List (ProgPoint × ProgPoint) := pts.flatMap fun c1 =>
    match T.cmdAt c1 with
    | some (.arrive b n) =>
        pts.filterMap fun c2 =>
          match T.cmdAt c2 with
          | some (.sync b' n') => if b = b' ∧ n = n' ∧ G c1 = G c2 then some (c1, c2) else none
          | _ => none
    | _ => []
  -- lines 12–16: `sync b n ↔ sync b n` of the same generation
  let syncSync : List (ProgPoint × ProgPoint) := pts.flatMap fun c1 =>
    match T.cmdAt c1 with
    | some (.sync b n) =>
        pts.flatMap fun c2 =>
          match T.cmdAt c2 with
          | some (.sync b' n') => if b = b' ∧ n = n' ∧ G c1 = G c2 then [(c1, c2), (c2, c1)] else []
          | _ => []
    | _ => []
  (progOrder ++ arriveSync ++ syncSync).toFinset

/-- **Figure 4 (`WELLSYNC`).** Returns `(ok, hb)` where `ok = true` iff the CTA `T`
is well-synchronized (Definition 6), and `hb` is the computed happens-before
relation — the transitive closure (Figure 4 line 17) of the static edges built from
`Gen(τ)`. (The relation is returned regardless of `ok`, e.g. for downstream
race-freedom analysis, Definition 8.)

`τ` is a concrete complete trace from `(I, T)` ending in `done` (the algorithm's
standing assumption — e.g. from `CTA.WellSynchronized.exists_successfulTrace`, or a
concrete simulation; a `τ` that deadlocks or errors already witnesses a violation
and need not be checked).

A direct transcription of Figure 4. Step 3 (lines 18–22) checks: for every `sync`
`c1` of generation `k` on barrier `b`, and every barrier-`b` operation `c2` of
generation `k+1` whose in-thread predecessor is `c3`, `hb` must already order `c1`
before `c3` (`(c1, c3) ∈ hb`). If some such ordering is missing, a different
schedule could pair the synchronizations up differently, so `ok = false`. -/
def CheckWellSynchronized (T : CTA) (τ : List Config) :
    Bool × Finset (ProgPoint × ProgPoint) :=
  -- Step 1 (lines 4–16): initialize R from the barrier generation counts.
  let R : Finset (ProgPoint × ProgPoint) := initRelation T τ
  -- Step 2 (line 17): the happens-before relation is the transitive closure of R.
  let hb : Finset (ProgPoint × ProgPoint) := transClosure R
  -- Step 3 (lines 18–22): check each (generation k, generation k+1) barrier pair.
  let ok : Bool := T.progPoints.all fun c1 =>
    match T.cmdAt c1 with
    | some (.sync b _) =>
        let k := pointGen T τ c1
        T.progPoints.all fun c2 =>
          match (T.cmdAt c2).bind Cmd.barrier? with
          | some b' =>
              if b = b' ∧ pointGen T τ c2 = k + 1 ∧ 1 ≤ c2.idx then
                -- `c3 = ⟨c2.thread, c2.idx - 1⟩` is `c2`'s predecessor (`c3 ; c2 ∈ T`).
                decide ((c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∈ hb)
              else
                true
          | none => true
    | _ => true
  (ok, hb)

/-! ## Lemma 1 — the happens-before relation is sound and precise (Definition 4)

Weft's **Lemma 1**: *for well-synchronized configurations the static happens-before
relation as constructed in Figure 4 is sound and precise* (Definition 4,
`Weft.SoundAndPrecise`). That relation is the second component returned by the
algorithm, `(CheckWellSynchronized T τ).2`. Definition 4 is an *iff* between an edge
of `R` and a schedule-independent timing fact; its two directions are the soundness
and preciseness sublemmas below, which assemble into the full lemma. All three are
stubs (proofs are future work, resting on the `transClosure` correctness `TODO`). -/

/-- Soundness half of Lemma 1: every edge `(η₁, η₂)` of the computed happens-before
relation is a *genuine* ordering — in every complete trace from `(I, T)`, `η₁`
executes no later than `η₂`. (Per the paper: direct, because there is no
out-of-order execution within a thread and well-synchronization fixes barrier
generations across all traces.) This is the `→` direction of `SoundAndPrecise`. -/
theorem happensBefore_sound {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hR : (η₁, η₂) ∈ (CheckWellSynchronized T τ).2) :
    ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂ := by
  sorry

/-- Preciseness half of Lemma 1: the computed happens-before relation captures
*every* genuine ordering — if `η₁` executes no later than `η₂` in every complete
trace from `(I, T)`, then `(η₁, η₂)` is an edge of `R`. (Per the paper: by induction
on program size, since the tuples in `R` are the only ordering restrictions the
semantics imposes.) This is the `←` direction of `SoundAndPrecise`. -/
theorem happensBefore_precise {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hle : ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :
    (η₁, η₂) ∈ (CheckWellSynchronized T τ).2 := by
  sorry

/-- **Lemma 1.** For a well-synchronized configuration `(I, T)`, the static
happens-before relation constructed in Figure 4 — `(CheckWellSynchronized T τ).2`,
viewed as a relation on program points — is sound and precise in the sense of
Definition 4 (`Weft.SoundAndPrecise`). Assembled from the two directions
`happensBefore_sound` and `happensBefore_precise`. -/
theorem soundAndPrecise_happensBefore {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    SoundAndPrecise (Config.run State.initial T)
      (fun η₁ η₂ => (η₁, η₂) ∈ (CheckWellSynchronized T τ).2) := by
  intro η₁ η₂
  exact ⟨happensBefore_sound hτ hws, happensBefore_precise hτ hws⟩

/-! ## Theorem 1 — soundness of `CheckWellSynchronized`

The paper's **Theorem 1**: a successful run of the check witnesses
well-synchronization. The paper proves it by induction on the suffixes of the
`done`-reaching execution — *not* via Lemma 1, which would be circular (only
well-synchronized configurations are known to have a sound `R`, yet here `R` is what
we use to conclude well-synchronization). Stated here as a stub. -/

/-- **Theorem 1.** If `τ` is a complete trace from `(I, T)` ending in `done`
(`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns `true`, then `T`
is well-synchronized. -/
theorem wellSynchronized_of_check {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true) :
    T.WellSynchronized := by
  sorry

end Weft
