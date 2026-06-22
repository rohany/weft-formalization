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

/-- `⟨i, k⟩` is a program point of `T` iff `i` is a thread and `k` indexes its
program. -/
theorem mem_progPoints_iff (T : CTA) (x : ProgPoint) :
    x ∈ T.progPoints ↔ x.thread ∈ T.ids ∧ x.idx < (T.prog x.thread).length := by
  unfold CTA.progPoints
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Finset.mem_sort]
  constructor
  · rintro ⟨i, hi, k, hk, rfl⟩; exact ⟨hi, hk⟩
  · rintro ⟨hi, hk⟩; exact ⟨x.thread, hi, x.idx, hk, rfl⟩

/-- A valid command index lands in `T.ids` (outside `ids` the program is empty). -/
theorem mem_ids_of_idx_lt (T : CTA) {i : ThreadId} {k : Nat}
    (h : k < (T.prog i).length) : i ∈ T.ids := by
  by_contra hni; rw [T.nil_outside_ids i hni] at h; simp at h

/-- If `T.cmdAt x` names a command, then `x` is a program point of `T`. -/
theorem mem_progPoints_of_cmdAt (T : CTA) {x : ProgPoint} {c : Cmd}
    (h : T.cmdAt x = some c) : x ∈ T.progPoints := by
  rw [CTA.cmdAt] at h
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  exact (mem_progPoints_iff T x).2 ⟨mem_ids_of_idx_lt T hlt, hlt⟩

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

/-- Soundness direction of the `transClosure` characterization: every pair in the
closure is connected by a nonempty path of `R`-edges, i.e. lies in `Relation.TransGen`
of edge membership. Proved by induction on the saturation rounds (each round only
adds composites of existing reachable pairs with `R`-edges). -/
theorem mem_transClosure_imp_transGen {α : Type*} [DecidableEq α] (R : Finset (α × α)) :
    ∀ {a b : α}, (a, b) ∈ transClosure R → Relation.TransGen (fun x y => (x, y) ∈ R) a b := by
  have key : ∀ (n : ℕ) (a b : α),
      (a, b) ∈ (fun S : Finset (α × α) =>
          S ∪ S.biUnion fun e => (R.filter fun f => e.2 = f.1).image fun f => (e.1, f.2))^[n] R →
      Relation.TransGen (fun x y => (x, y) ∈ R) a b := by
    intro n
    induction n with
    | zero =>
        intro a b h
        simp only [Function.iterate_zero, id_eq] at h
        exact Relation.TransGen.single h
    | succ k ih =>
        intro a b h
        rw [Function.iterate_succ_apply'] at h
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
          Prod.mk.injEq] at h
        rcases h with h | ⟨e, he, f, ⟨hfR, hef⟩, ha, hb⟩
        · exact ih a b h
        · subst ha; subst hb
          have hmem : (e.2, f.2) ∈ R := by
            have heq : (e.2, f.2) = f := Prod.ext_iff.mpr ⟨hef, rfl⟩
            rw [heq]; exact hfR
          exact (ih e.1 e.2 he).tail hmem
  intro a b h
  exact key R.card a b h

-- TODO(proof): the converse `Relation.TransGen … → (a, b) ∈ transClosure R`. This is
-- the `→` half of `happensBefore_iff_mem` (completeness of the executable `Finset`);
-- the `←` half and all of Lemma 1 only use the forward direction above, so nothing
-- currently depends on it. It reduces to showing `addStep^[R.card] R` is a fixpoint,
-- which needs the diameter bound: every `TransGen` pair has a *simple* path, whose
-- edges are distinct elements of `R`, hence `≤ R.card` of them — so `R.card`
-- saturation rounds suffice. Formalizing that bound (minimal-length chain ⟹ `Nodup`
-- ⟹ `≤ R.card` edges) is a self-contained graph-theory lemma, deferred.

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

/-- Classification of `initRelation` edges. Both endpoints are program points, and
either the edge is intra-thread program order (`b = ⟨a.thread, a.idx+1⟩`) or it is a
barrier edge: in every barrier edge — `arrive→sync` *and* both directions of
`sync↔sync` — the target `b` is a `sync` on some barrier `bb`, `a` is a barrier
operation on the same `bb`, and the two share a generation (`pointGen`). -/
theorem initRelation_cases {T : CTA} {τ : List Config} {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) :
    a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
    (b = ⟨a.thread, a.idx + 1⟩ ∨
      ∃ bb n, T.cmdAt b = some (.sync bb n) ∧ (T.cmdAt a).bind Cmd.barrier? = some bb ∧
        pointGen T τ a = pointGen T τ b) := by
  simp only [initRelation, List.mem_toFinset, List.mem_append] at hedge
  rcases hedge with (hpo | has) | hss
  · -- program order
    simp only [List.mem_filterMap] at hpo
    obtain ⟨c, hc, hceq⟩ := hpo
    split at hceq
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hceq
      obtain ⟨rfl, rfl⟩ := hceq
      have hth : c.thread ∈ T.ids := ((mem_progPoints_iff T c).mp hc).1
      exact ⟨hc, (mem_progPoints_iff T _).mpr ⟨hth, hcond⟩, Or.inl rfl⟩
    · exact absurd hceq (by simp)
  · -- arrive → sync
    simp only [List.mem_flatMap] at has
    obtain ⟨c1, hc1, hin⟩ := has
    cases hcmd1 : T.cmdAt c1 with
    | none => simp [hcmd1] at hin
    | some cmd1 =>
      cases cmd1 with
      | read g => simp [hcmd1] at hin
      | write g => simp [hcmd1] at hin
      | sync bb n => simp [hcmd1] at hin
      | arrive bb n =>
        simp only [hcmd1, List.mem_filterMap] at hin
        obtain ⟨c2, hc2, hc2eq⟩ := hin
        cases hcmd2 : T.cmdAt c2 with
        | none => simp [hcmd2] at hc2eq
        | some cmd2 =>
          cases cmd2 with
          | read g => simp [hcmd2] at hc2eq
          | write g => simp [hcmd2] at hc2eq
          | arrive b' n' => simp [hcmd2] at hc2eq
          | sync b' n' =>
            simp only [hcmd2] at hc2eq
            split at hc2eq
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
              obtain ⟨rfl, rfl⟩ := hc2eq
              obtain ⟨hbb, _, hgen⟩ := hcond
              refine ⟨hc1, hc2, Or.inr ⟨b', n', hcmd2, ?_, hgen⟩⟩
              rw [hcmd1]; simp [Cmd.barrier?, hbb]
            · exact absurd hc2eq (by simp)
  · -- sync ↔ sync
    simp only [List.mem_flatMap] at hss
    obtain ⟨c1, hc1, hin⟩ := hss
    cases hcmd1 : T.cmdAt c1 with
    | none => simp [hcmd1] at hin
    | some cmd1 =>
      cases cmd1 with
      | read g => simp [hcmd1] at hin
      | write g => simp [hcmd1] at hin
      | arrive bb n => simp [hcmd1] at hin
      | sync bb n =>
        simp only [hcmd1, List.mem_flatMap] at hin
        obtain ⟨c2, hc2, hin2⟩ := hin
        cases hcmd2 : T.cmdAt c2 with
        | none => simp [hcmd2] at hin2
        | some cmd2 =>
          cases cmd2 with
          | read g => simp [hcmd2] at hin2
          | write g => simp [hcmd2] at hin2
          | arrive b' n' => simp [hcmd2] at hin2
          | sync b' n' =>
            simp only [hcmd2] at hin2
            split at hin2
            · rename_i hcond
              obtain ⟨hbb, _, hgen⟩ := hcond
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
                Prod.mk.injEq] at hin2
              rcases hin2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · refine ⟨hc1, hc2, Or.inr ⟨b', n', hcmd2, ?_, hgen⟩⟩
                rw [hcmd1]; simp [Cmd.barrier?, hbb]
              · refine ⟨hc2, hc1, Or.inr ⟨bb, n, hcmd1, ?_, hgen.symm⟩⟩
                rw [hcmd2]; simp [Cmd.barrier?, hbb]
            · simp at hin2

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

/-- The happens-before relation of Figure 4, as a *relation* on program points (the
object Definition 4 / Lemma 1 talk about), rather than as the executable `Finset`
returned by `CheckWellSynchronized`. It is the **reflexive**-transitive closure of
the static edge set `initRelation T τ`, via the canonical `Relation.ReflTransGen`.

Reflexivity is not cosmetic: Definition 4 (`SoundAndPrecise`) uses `≤`, so at
`η₁ = η₂` the timing side is unconditionally true (`IsTimeOf.unique`) and a
sound-and-precise relation *must* relate every point to itself. The executable
`(CheckWellSynchronized T τ).2 = transClosure (initRelation T τ)` is the irreflexive
`Relation.TransGen` part (a finite set, so it cannot carry the diagonal of the
infinite `ProgPoint`); `happensBefore` adds the diagonal back. The two agree off the
diagonal — see `happensBefore_iff_mem`. -/
def happensBefore (T : CTA) (τ : List Config) : ProgPoint → ProgPoint → Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ initRelation T τ)

/-- `(CheckWellSynchronized T τ).2` is, by definition, the `Finset` transitive closure
of `initRelation T τ`. -/
theorem snd_checkWellSynchronized (T : CTA) (τ : List Config) :
    (CheckWellSynchronized T τ).2 = transClosure (initRelation T τ) := rfl

/-- **Soundness of the executable relation w.r.t. `happensBefore`** (the easy `←`
half of `happensBefore_iff_mem`): every pair the algorithm reports — and every
diagonal pair — is a genuine `happensBefore` pair. The diagonal is
`Relation.ReflTransGen.refl`; an `(a,b) ∈ transClosure` pair is a `Relation.TransGen`
chain (`mem_transClosure_imp_transGen`), hence a `Relation.ReflTransGen` one. The
reverse inclusion (completeness of the `Finset`) is the `transClosure` converse still
open below, and is *not* needed by any result in this file. -/
theorem happensBefore_of_mem {T : CTA} {τ : List Config} {a b : ProgPoint}
    (h : a = b ∨ (a, b) ∈ (CheckWellSynchronized T τ).2) : happensBefore T τ a b := by
  rcases h with rfl | h
  · exact Relation.ReflTransGen.refl
  · rw [snd_checkWellSynchronized] at h
    exact (mem_transClosure_imp_transGen (initRelation T τ) h).to_reflTransGen

/-- `pointTime` computes the time `t(τ, η)`: if `η` executes at step `m` in a
complete trace from `(I, T)`, then `pointTime T τ η = some m`. (The matcher returns
`some` only at genuine execution steps — `hfwd`, by suffix uniqueness of the
remaining program — and there is one, at `m - 1`; uniqueness of time pins the
`findSome?` result to `m`.) -/
theorem pointTime_eq_of_isTimeOf {T : CTA} {τ : List Config} {η : ProgPoint} {m : Nat}
    (hexec : IsTimeOf (Config.run State.initial T) τ η m) : pointTime T τ η = some m := by
  have hτ := hexec.1
  have hidxL : η.idx < (T.prog η.thread).length := hexec.2.1
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hC₀ : (Config.run State.initial T).progOf η.thread = T.prog η.thread := rfl
  set f : Nat → Option Nat := fun j =>
    match τ[j]?, τ[j + 1]? with
    | some C, some C' =>
        if (C.progOf η.thread).length == (T.prog η.thread).length - η.idx
            && (C'.progOf η.thread).length == (T.prog η.thread).length - η.idx - 1 then
          some (j + 1) else none
    | _, _ => none with hf
  have hfwd : ∀ a x, f a = some x → IsTimeOf (Config.run State.initial T) τ η x := by
    intro a x hfa
    simp only [hf] at hfa
    rcases hCa : τ[a]? with _ | C₁
    · simp [hCa] at hfa
    · rcases hCa1 : τ[a + 1]? with _ | C₂
      · simp [hCa, hCa1] at hfa
      · simp only [hCa, hCa1] at hfa
        split at hfa
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨hl1, hl2⟩ := hcond
          rw [Option.some.injEq] at hfa; subst hfa
          refine ⟨hτ, hidxL, a, C₁, C₂, rfl, hCa, hCa1, ?_, ?_⟩
          · have heq := List.IsSuffix.eq_drop
              (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le a) hCa)
            rw [hl1, hC₀] at heq
            rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
              by omega] at heq
          · have heq := List.IsSuffix.eq_drop
              (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le (a + 1)) hCa1)
            rw [hl2, hC₀] at heq
            rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx - 1) = η.idx + 1
              by omega] at heq
        · simp at hfa
  have hex2 := hexec
  obtain ⟨_, _, j, C, C', hm, hCj, hCj1, hCeq, hC'eq⟩ := hex2
  have hj1lt : j + 1 < τ.length := (List.getElem?_eq_some_iff.mp hCj1).1
  have hfj : f j = some (j + 1) := by
    simp only [hf, hCj, hCj1]
    have h1 : (C.progOf η.thread).length = (T.prog η.thread).length - η.idx := by
      rw [hCeq, hC₀, List.length_drop]
    have h2 : (C'.progOf η.thread).length = (T.prog η.thread).length - η.idx - 1 := by
      rw [hC'eq, hC₀, List.length_drop]; omega
    rw [h1, h2]; simp
  have hpt : pointTime T τ η = (List.range (τ.length - 1)).findSome? f := by
    simp only [pointTime, hidxL, if_true, ← hf]
  rw [hpt]
  have hjmem : j ∈ List.range (τ.length - 1) := List.mem_range.mpr (by omega)
  have hne : (List.range (τ.length - 1)).findSome? f ≠ none := by
    rw [Ne, List.findSome?_eq_none_iff]
    push_neg
    exact ⟨j, hjmem, by rw [hfj]; simp⟩
  obtain ⟨m'', hm''⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hm'']
  rw [List.findSome?_eq_some_iff] at hm''
  obtain ⟨_, a, _, _, hfa, _⟩ := hm''
  rw [IsTimeOf.unique (hfwd a m'' hfa) hexec]

/-- **Program order is respected in time** (the "no out-of-order execution within a
thread" fact): in any complete trace, instruction `a` of a thread executes no later
than the next instruction `⟨a.thread, a.idx + 1⟩` of the same thread. Proved from
program-length monotonicity (`progOf_suffix_index_le`): were the successor to run
first, the program would have to grow back. -/
theorem progOrder_time_le {C₀ : Config} {τ' : List Config} {a : ProgPoint} {n₁ n₂ : Nat}
    (h₁ : IsTimeOf C₀ τ' a n₁)
    (h₂ : IsTimeOf C₀ τ' ⟨a.thread, a.idx + 1⟩ n₂) : n₁ ≤ n₂ := by
  obtain ⟨hτ, _, j, C, _C', hm₁, hCj, _, hCeq, _⟩ := h₁
  obtain ⟨_, hlt₂, j', _D, D', hm₂, _, hDj1, _, hD'eq⟩ := h₂
  subst hm₁; subst hm₂
  have hchain := hτ.1.subtrace
  have hCe : C.progOf a.thread = (C₀.progOf a.thread).drop a.idx := hCeq
  have hD'e : D'.progOf a.thread = (C₀.progOf a.thread).drop (a.idx + 1 + 1) := hD'eq
  have hlt₂' : a.idx + 1 < (C₀.progOf a.thread).length := hlt₂
  by_contra hcon
  have hji : j' + 1 ≤ j := by omega
  have hsuf := progOf_suffix_index_le hchain a.thread hDj1 hji hCj
  have hle := suffix_length_le hsuf
  rw [hCe, hD'e, List.length_drop, List.length_drop] at hle
  omega

/-! ## Lemma 1 — the happens-before relation is sound and precise (Definition 4)

Weft's **Lemma 1**: *for well-synchronized configurations the static happens-before
relation as constructed in Figure 4 is sound and precise* (Definition 4,
`Weft.SoundAndPrecise`). That relation is the second component returned by the
algorithm, `(CheckWellSynchronized T τ).2`. Definition 4 is an *iff* between an edge
of `R` and a schedule-independent timing fact; its two directions are the soundness
and preciseness sublemmas below, which assemble into the full lemma. `happensBefore_sound`
is *proved* below by reducing (via `mem_transClosure_imp_transGen` and `Relation.TransGen`
induction) to two per-edge facts, `initRelation_edge_sound` and `initRelation_src_timed`,
which carry the remaining semantic content as stubs; `happensBefore_precise` is still a
full stub. -/

/-- The computable `pointGen` *is* the generation: for a barrier command `a` that
executes in `τ`, `IsGenOf (I, T) τ a (pointGen T τ a)` holds (`pointTime` computes the
time, so `pointGen` computes `recycleCount …`). -/
theorem isGenOf_pointGen {T : CTA} {τ : List Config} {a : ProgPoint} {bb : Barrier} {ma : Nat}
    (hbb : (T.cmdAt a).bind Cmd.barrier? = some bb)
    (hma : IsTimeOf (Config.run State.initial T) τ a ma) :
    IsGenOf (Config.run State.initial T) τ a (pointGen T τ a) := by
  have hpt : pointTime T τ a = some ma := pointTime_eq_of_isTimeOf hma
  have hpg : pointGen T τ a = recycleCount bb τ (ma - 1) + 1 := by
    simp only [pointGen, hbb, hpt]
  exact ⟨hma.1, bb, hbb, Or.inl ⟨ma, hma, hpg⟩⟩

/-- Per-edge soundness (the core semantic content). Each edge of `initRelation T τ`
is a genuine ordering in every complete trace from `(I, T)`:

* **program-order** edges `⟨i,k⟩ → ⟨i,k+1⟩` — sound because there is no out-of-order
  execution within a thread (`progOrder_time_le`);
* **`arrive b n → sync b n`** and **`sync ↔ sync`** edges of equal generation — sound
  because well-synchronization fixes barrier generations across all traces, so the
  target `sync`'s recycle step both pins the generation and orders it after `a`. -/
theorem initRelation_edge_sound {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) :
    ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' a n₁ →
        IsTimeOf (Config.run State.initial T) τ' b n₂ → n₁ ≤ n₂ := by
  intro τ' hτ' n₁ n₂ ht₁ ht₂
  obtain ⟨ha, hb, hcase⟩ := initRelation_cases hedge
  rcases hcase with hpo | ⟨bb, nb, hbsync, habar, hgen⟩
  · -- program order
    subst hpo; exact progOrder_time_le ht₁ ht₂
  · -- barrier edge: `b` is a `sync` on `bb`, `a` is a barrier op on `bb`, same `pointGen`
    obtain ⟨sd, hdone⟩ := hτ.2
    -- `a` and `b` execute in the input trace `τ`
    have hma : ∃ n, IsTimeOf (Config.run State.initial T) τ a n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T a).mp ha).2
    have hmb : ∃ n, IsTimeOf (Config.run State.initial T) τ b n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T b).mp hb).2
    -- `pointGen` computes `IsGenOf` on `τ`
    have hbbar : (T.cmdAt b).bind Cmd.barrier? = some bb := by rw [hbsync]; rfl
    have hgenA : IsGenOf (Config.run State.initial T) τ a (pointGen T τ a) :=
      isGenOf_pointGen habar hma.choose_spec
    have hgenB : IsGenOf (Config.run State.initial T) τ b (pointGen T τ b) :=
      isGenOf_pointGen hbbar hmb.choose_spec
    -- well-synchronization transfers the generation to `τ'`
    obtain ⟨ga, _, hgaτ, hgaτ'⟩ := hws.2 τ τ' hτ.1 hτ' a ⟨bb, habar⟩
    obtain ⟨gb, _, hgbτ, hgbτ'⟩ := hws.2 τ τ' hτ.1 hτ' b ⟨bb, hbbar⟩
    rw [IsGenOf.unique hgaτ hgenA] at hgaτ'
    rw [IsGenOf.unique hgbτ hgenB] at hgbτ'
    rw [hgen] at hgaτ'        -- both `IsGenOf … τ' _ (pointGen T τ b)`
    -- read the generation off in `τ'` at the given times
    have hr1 : pointGen T τ b = recycleCount bb τ' (n₁ - 1) + 1 :=
      isGenOf_recycleCount hgaτ' habar ht₁
    have hr2 : pointGen T τ b = recycleCount bb τ' (n₂ - 1) + 1 :=
      isGenOf_recycleCount hgbτ' hbbar ht₂
    -- `b`'s step recycles `bb`; the recycle count strictly increases past it
    by_contra hcon
    have hn2 : 1 ≤ n₂ := by obtain ⟨_, _, j, _, _, h, _⟩ := ht₂; omega
    obtain ⟨Cb, Cb', hCb, hCb', hrec⟩ := sync_time_recycles ht₂ hbsync
    have hCb2 : τ'[n₂ - 1 + 1]? = some Cb' := by rw [show n₂ - 1 + 1 = n₂ by omega]; exact hCb'
    have hsucc : recycleCount bb τ' n₂ = recycleCount bb τ' (n₂ - 1) + 1 := by
      have h := recycleCount_succ_of_recycle bb τ' hCb hCb2 hrec
      rwa [show n₂ - 1 + 1 = n₂ by omega] at h
    have hmono : recycleCount bb τ' n₂ ≤ recycleCount bb τ' (n₁ - 1) :=
      recycleCount_mono bb τ' (by omega)
    omega

/-- The source of any `initRelation` edge executes in every complete trace from a
well-synchronized `(I, T)`. (Such a trace ends in `done` by `completeTrace_ends_done`,
so every command runs, and edge sources are valid program points.) Used to bridge
intermediate nodes when chaining `Relation.TransGen`. Stub. -/
theorem initRelation_src_timed {T : CTA} {τ : List Config}
    (hws : T.WellSynchronized) {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) {τ' : List Config}
    (hτ' : IsCompleteTraceFrom (Config.run State.initial T) τ') :
    ∃ n, IsTimeOf (Config.run State.initial T) τ' a n := by
  obtain ⟨ha, _, _⟩ := initRelation_cases hedge
  obtain ⟨_, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hτ'
  exact exists_time_of_ends_done hτ' hdone ((mem_progPoints_iff T a).mp ha).2

/-- Soundness half of Lemma 1: every pair `(η₁, η₂)` of the happens-before relation
`happensBefore T τ` is a *genuine* ordering — in every complete trace from `(I, T)`,
`η₁` executes no later than `η₂`. (Per the paper: direct, because there is no
out-of-order execution within a thread and well-synchronization fixes barrier
generations across all traces.) This is the `→` direction of `SoundAndPrecise`.

Proved by induction on the reflexive-transitive chain: the reflexive base is the
trivial `η₁ = η₂` case (equal times, `IsTimeOf.unique`); each appended edge is sound
(`initRelation_edge_sound`), and the intermediate node executes
(`initRelation_src_timed`), so `≤` chains. -/
theorem happensBefore_sound {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hR : happensBefore T τ η₁ η₂) :
    ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂ := by
  intro τ' hτ'
  induction hR with
  | refl => intro n₁ n₂ h1 h2; exact le_of_eq (IsTimeOf.unique h1 h2)
  | tail _hab hbc ih =>
      intro n₁ nc ht₁ htc
      obtain ⟨nb, htb⟩ := initRelation_src_timed hws hbc hτ'
      exact le_trans (ih n₁ nb ht₁ htb)
        (initRelation_edge_sound hτ hws hbc τ' hτ' nb nc htb htc)

/-- Preciseness half of Lemma 1: the happens-before relation captures *every* genuine
ordering — if `η₁` executes no later than `η₂` in every complete trace from `(I, T)`,
then `happensBefore T τ η₁ η₂` holds. (Per the paper: by induction on program size,
since the tuples in `R` are the only ordering restrictions the semantics imposes.)
This is the `←` direction of `SoundAndPrecise`.

The reflexive corner `η₁ = η₂` is `Relation.ReflTransGen.refl`. The genuine content
is the `η₁ ≠ η₂` case: there one must produce an actual `Relation.TransGen` chain of
`initRelation` edges, i.e. show that any ordering *not* forced by `R` is violated by
some schedule (the paper's adversarial-schedule construction). That step is the one
remaining `sorry`. -/
theorem happensBefore_precise {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hle : ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :
    happensBefore T τ η₁ η₂ := by
  by_cases hη : η₁ = η₂
  · -- reflexive corner: every point is happens-before itself
    subst hη; exact Relation.ReflTransGen.refl
  · -- the genuine, schedule-construction content (distinct program points)
    sorry

/-- **Lemma 1.** For a well-synchronized configuration `(I, T)`, the static
happens-before relation constructed in Figure 4 — `happensBefore T τ`, the
reflexive-transitive closure of `initRelation T τ` — is sound and precise in the
sense of Definition 4 (`Weft.SoundAndPrecise`). Assembled from the two directions
`happensBefore_sound` and `happensBefore_precise`. -/
theorem soundAndPrecise_happensBefore {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    SoundAndPrecise (Config.run State.initial T) (happensBefore T τ) := by
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
