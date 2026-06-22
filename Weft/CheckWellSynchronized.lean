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

/-- A program-order edge `⟨i, m⟩ → ⟨i, m+1⟩` belongs to `initRelation T τ` whenever
`m + 1` indexes thread `i`'s program (Figure 4 lines 4–6). -/
theorem mem_initRelation_progOrder {T : CTA} {τ : List Config} {i m : Nat}
    (h : m + 1 < (T.prog i).length) :
    ((⟨i, m⟩ : ProgPoint), (⟨i, m + 1⟩ : ProgPoint)) ∈ initRelation T τ := by
  have hpt : (⟨i, m⟩ : ProgPoint) ∈ T.progPoints := by
    rw [mem_progPoints_iff]
    exact ⟨mem_ids_of_idx_lt T (show m < (T.prog i).length by omega),
      show m < (T.prog i).length by omega⟩
  simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inl ⟨⟨i, m⟩, hpt, by rw [if_pos h]⟩)

/-- **Program order is captured by `happensBefore`.** Within a single thread `i`, any
earlier point is happens-before any later valid point — the program-order edges chain
up through the reflexive-transitive closure. -/
theorem progOrder_happensBefore {T : CTA} {τ : List Config} {i a : Nat} :
    ∀ {b : Nat}, a ≤ b → b < (T.prog i).length → happensBefore T τ ⟨i, a⟩ ⟨i, b⟩ := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact Relation.ReflTransGen.refl
  | succ m hm ih =>
      intro hlt
      exact (ih (by omega)).tail (mem_initRelation_progOrder (by omega))

/-- **Strict monotonicity of time within a thread.** In any complete trace, an earlier
instruction of a thread executes strictly before a later one — the remaining-program
length is non-increasing (`progOf_suffix_index_le`) and strictly larger at the earlier
index. -/
theorem time_lt_of_idx_lt {C₀ : Config} {τ : List Config} {η ξ : ProgPoint} {nη nξ : Nat}
    (hη : IsTimeOf C₀ τ η nη) (hξ : IsTimeOf C₀ τ ξ nξ)
    (hthread : η.thread = ξ.thread) (hidx : η.idx < ξ.idx) : nη < nξ := by
  obtain ⟨hτ, _, jη, Cη, _, rfl, hCjη, _, hCηeq, _⟩ := hη
  obtain ⟨_, hξL, jξ, Cξ, _, rfl, hCjξ, _, hCξeq, _⟩ := hξ
  rw [← hthread] at hCξeq hξL
  have hchain := hτ.1.subtrace
  rcases Nat.lt_or_ge jη jξ with h | h
  · omega
  · exfalso
    have hsuf := progOf_suffix_index_le hchain η.thread hCjξ h hCjη
    have hle := suffix_length_le hsuf
    rw [hCηeq, hCξeq, List.length_drop, List.length_drop] at hle
    omega

section IdealCut
open Classical

/-- The **cut** for thread `i` (relative to `η₁`): the least index of a point that is
happens-before-after `η₁` — an `F`-position — or the program length if none. It splits
thread `i` into the ideal `G`-prefix `[0, cut)` (points *not* after `η₁`) and the `F`-
suffix `[cut, length)`. Down-closure of `G` makes this a genuine prefix; see
`fcut_le_of_hb` / `lt_fcut_of_not_hb`. -/
noncomputable def fcut (T : CTA) (τ : List Config) (η₁ : ProgPoint) (i : ThreadId) : Nat :=
  if h : ∃ k, happensBefore T τ η₁ ⟨i, k⟩ ∧ k < (T.prog i).length
  then Nat.find h else (T.prog i).length

/-- An `F`-point (happens-before-after `η₁`) sits at or beyond its thread's cut — in
particular `η₁` itself does (reflexively), so `η₁ ∉ G`. -/
theorem fcut_le_of_hb {T : CTA} {τ : List Config} {η₁ η : ProgPoint}
    (h : happensBefore T τ η₁ η) (hv : η ∈ T.progPoints) :
    fcut T τ η₁ η.thread ≤ η.idx := by
  have hηeq : (⟨η.thread, η.idx⟩ : ProgPoint) = η := rfl
  have hex : ∃ k, happensBefore T τ η₁ ⟨η.thread, k⟩ ∧ k < (T.prog η.thread).length :=
    ⟨η.idx, by rw [hηeq]; exact h, ((mem_progPoints_iff T η).mp hv).2⟩
  unfold fcut
  rw [dif_pos hex]
  exact Nat.find_le ⟨by rw [hηeq]; exact h, ((mem_progPoints_iff T η).mp hv).2⟩

/-- A `G`-point (not happens-before-after `η₁`) sits strictly below its thread's cut —
in particular `η₂` does, since `¬ happensBefore η₁ η₂`, so `η₂ ∈ G`. -/
theorem lt_fcut_of_not_hb {T : CTA} {τ : List Config} {η₁ η : ProgPoint}
    (h : ¬ happensBefore T τ η₁ η) (hv : η ∈ T.progPoints) :
    η.idx < fcut T τ η₁ η.thread := by
  have hηeq : (⟨η.thread, η.idx⟩ : ProgPoint) = η := rfl
  have hvlt : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hv).2
  by_contra hle
  push_neg at hle
  unfold fcut at hle
  split at hle
  · rename_i hex
    obtain ⟨hhb, _⟩ := Nat.find_spec hex
    exact h (hηeq ▸ hhb.trans (progOrder_happensBefore hle hvlt))
  · omega

/-- The cut never exceeds the program length. -/
theorem fcut_le_length (T : CTA) (τ : List Config) (η₁ : ProgPoint) (i : ThreadId) :
    fcut T τ η₁ i ≤ (T.prog i).length := by
  unfold fcut
  split
  · rename_i h; exact le_of_lt (Nat.find_spec h).2
  · exact le_refl _

end IdealCut

/-- The clean-state invariant for the run-`G` construction: configuration `C` has
executed only the ideal `G` so far. Two clauses:

* **program bound** — each thread's remaining program is `T`'s with at most `cut`
  commands dropped, so no `F`-command (index `≥ cut`) has run;
* **barrier purity** — every *synced* (parked) thread sits at a `G`-`sync` (its
  executed count is strictly below its cut). Without this an `F`-`sync` could park into
  a `G`-round (parking is program-preserving, hence program-bound-preserving) and the
  round's later `recycle` would push that thread past its cut.

Preserved by `G`-steps; the run-`G` recursion stays inside this predicate until `G` is
exhausted. -/
def GBounded (T : CTA) (τ : List Config) (η₁ : ProgPoint) (C : Config) : Prop :=
  ∃ s T_C, C = Config.run s T_C ∧
    (∀ i, ∃ e, e ≤ fcut T τ η₁ i ∧ T_C.prog i = (T.prog i).drop e) ∧
    (∀ b i, i ∈ (s.B b).synced →
      (T.prog i).length - (T_C.prog i).length < fcut T τ η₁ i)

/-- The initial configuration is `G`-bounded: nothing has executed (`e = 0`) and no
thread is synced. -/
theorem GBounded_init (T : CTA) (τ : List Config) (η₁ : ProgPoint) :
    GBounded T τ η₁ (Config.run State.initial T) :=
  ⟨State.initial, T, rfl, fun i => ⟨0, Nat.zero_le _, by simp⟩,
    fun b i hi => by simp [State.initial, BarrierState.unconfigured] at hi⟩

/-- If `η` has *already executed* by configuration index `p` (its remaining program is
short enough at `p`), then its time is `≤ p`. (Programs only shrink, so the transition
that runs `η` cannot be after `p`.) -/
theorem time_le_of_progOf_le {C₀ : Config} {τ' : List Config} {η : ProgPoint} {n p : Nat}
    {C : Config} (ht : IsTimeOf C₀ τ' η n) (hp : τ'[p]? = some C)
    (hlen : (C.progOf η.thread).length ≤ (C₀.progOf η.thread).length - η.idx - 1) :
    n ≤ p := by
  obtain ⟨hcomp, _, j, Cj, _, rfl, hCj, _, hCjeq, _⟩ := ht
  have hchain := hcomp.1.subtrace
  by_contra hlt
  push_neg at hlt
  have hsuf := progOf_suffix_index_le hchain η.thread hp (by omega : p ≤ j) hCj
  have := suffix_length_le hsuf
  rw [hCjeq, List.length_drop] at this
  omega

/-- If `η` has *not yet executed* by configuration index `p` (its remaining program is
still long at `p`), then its time is `> p`. -/
theorem lt_time_of_lt_progOf {C₀ : Config} {τ' : List Config} {η : ProgPoint} {n p : Nat}
    {C : Config} (ht : IsTimeOf C₀ τ' η n) (hp : τ'[p]? = some C)
    (hlen : (C₀.progOf η.thread).length - η.idx - 1 < (C.progOf η.thread).length) :
    p < n := by
  obtain ⟨hcomp, _, j, _, Cj', rfl, _, hCj1, _, hCj1eq⟩ := ht
  have hchain := hcomp.1.subtrace
  by_contra hle
  push_neg at hle
  have hsuf := progOf_suffix_index_le hchain η.thread hCj1 (by omega : j + 1 ≤ p) hp
  have := suffix_length_le hsuf
  rw [hCj1eq, List.length_drop] at this
  omega

/-- Well-formedness propagates to every reachable configuration. -/
theorem WF_of_reaches {T : CTA} {C : Config}
    (h : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) : C.WF := by
  induction h with
  | refl => exact WF_initial
  | tail _ hstep ih => exact CTAStep.WF_preserved hstep ih

/-- The barrier-support invariant propagates to every reachable configuration. -/
theorem barriersWithin_of_reaches {T : CTA} {C : Config}
    (h : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) :
    C.barriersWithin T.barrierSet := by
  induction h with
  | refl => exact barriersWithin_initial
  | tail _ hstep ih => exact inv_preserved T.barrierSet hstep ih

/-- `G` is exhausted at `C`: every (in-domain) thread has run exactly its `fcut`-prefix. -/
def Gdone (T : CTA) (τ : List Config) (η₁ : ProgPoint) (C : Config) : Prop :=
  ∀ i ∈ T.ids, (C.progOf i).length = (T.prog i).length - fcut T τ η₁ i

/-- **Progress** (the operational crux). From a `G`-bounded, reachable configuration at
which `G` is *not* yet exhausted, there is a step that keeps the configuration
`G`-bounded — a `G`-step that makes progress without touching `F`. (Built on the
deadlock-freedom of a well-synchronized CTA: were no `G`-step available, the parked
`G`-threads would form a frozen set the schedule could never complete, so the run could
not reach `done`, contradicting `completeTrace_ends_done`.) -/
theorem gstep {T : CTA} {τ : List Config} {η₁ : ProgPoint} (hws : T.WellSynchronized)
    {C : Config} (hGB : GBounded T τ η₁ C)
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C)
    (hnotdone : ¬ Gdone T τ η₁ C) :
    ∃ C', CTAStep C C' ∧ GBounded T τ η₁ C' := by
  sorry

/-- Run `G` to the cut configuration: from any reachable `G`-bounded `C`, there is a
chain (executing only `G`-steps) to a configuration whose every thread sits exactly at
its cut. By well-founded recursion on `cfgMeasure`, taking a `G`-step (`gstep`) until
`G` is exhausted. -/
theorem reach_cut_aux {T : CTA} {τ : List Config} {η₁ : ProgPoint} (hws : T.WellSynchronized) :
    ∀ n, ∀ C, GBounded T τ η₁ C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C →
      C.cfgMeasure T.barrierSet = n →
      ∃ (pre : List Config) (s_G : State) (T_G : CTA),
        pre.head? = some C ∧ List.IsChain CTAStep pre ∧
        pre.getLast? = some (Config.run s_G T_G) ∧
        (∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i)) ∧
        Relation.ReflTransGen CTAStep (Config.run State.initial T) (Config.run s_G T_G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hGB hreach hmeas
    by_cases hdone : Gdone T τ η₁ C
    · -- cut configuration reached
      obtain ⟨s, T_C, rfl, he, _hpure⟩ := hGB
      refine ⟨[Config.run s T_C], s, T_C, rfl, List.isChain_singleton _, rfl, fun i => ?_, hreach⟩
      obtain ⟨e, hele, hprog⟩ := he i
      by_cases hi : i ∈ T.ids
      · have hd := hdone i hi
        simp only [Config.progOf] at hd
        rw [hprog, List.length_drop] at hd
        have hcl := fcut_le_length T τ η₁ i
        rw [hprog, show e = fcut T τ η₁ i by omega]
      · rw [hprog, T.nil_outside_ids i hi]; simp
    · -- progress: take a `G`-step and recurse
      obtain ⟨C', hstep, hGB'⟩ := gstep hws hGB hreach hdone
      have hbw : C.barriersWithin T.barrierSet := barriersWithin_of_reaches hreach
      have hlt : C'.cfgMeasure T.barrierSet < n := by
        rw [← hmeas]; exact step_decreases T.barrierSet hstep hbw
      obtain ⟨pre', s_G, T_G, hhd', hch', hlast', hcut', hreach'⟩ :=
        ih _ hlt C' hGB' (hreach.tail hstep) rfl
      have hpne : pre' ≠ [] := by intro h; rw [h] at hhd'; simp at hhd'
      refine ⟨C :: pre', s_G, T_G, rfl, ?_, ?_, hcut', hreach'⟩
      · rw [List.isChain_cons]
        exact ⟨fun y hy => by rw [hhd', Option.mem_some_iff] at hy; exact hy ▸ hstep, hch'⟩
      · rw [List.getLast?_cons_of_ne_nil hpne]; exact hlast'

/-- **Run the ideal `G` first.** There is a complete trace `τ'` from `(I, T)` and a
configuration index `p` at which *exactly* the ideal `G` has executed — every thread's
remaining program is `T`'s with its `fcut`-prefix dropped. (This is the operational
core: the schedule runs all `G`-commands, reaching a clean cut configuration, before
running any `F`-command.) -/
theorem run_ideal {T : CTA} {τ : List Config} {η₁ : ProgPoint} (hws : T.WellSynchronized) :
    ∃ (τ' : List Config) (p : Nat) (s_G : State) (T_G : CTA),
      IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      τ'[p]? = some (Config.run s_G T_G) ∧
      ∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i) := by
  -- run `G` to the cut config `C_G`
  obtain ⟨pre, s_G, T_G, hhd, hch, hlast, hcut, hreachG⟩ :=
    reach_cut_aux hws ((Config.run State.initial T).cfgMeasure T.barrierSet)
      (Config.run State.initial T) (GBounded_init T τ η₁) Relation.ReflTransGen.refl rfl
  have hpne : pre ≠ [] := by intro h; rw [h] at hhd; simp at hhd
  have hpos : 0 < pre.length := List.length_pos_of_ne_nil hpne
  have hgl : pre.getLast hpne = Config.run s_G T_G := by
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h; exact (Option.some.injEq _ _).mp h.symm
  -- `C_G` is reachable, so it satisfies the support invariant; complete from it.
  have hbwG : (Config.run s_G T_G).barriersWithin T.barrierSet := barriersWithin_of_reaches hreachG
  obtain ⟨σ, hσIC, hσhead⟩ := exists_completeTrace T.barrierSet (Config.run s_G T_G) hbwG
  obtain ⟨σtail, rfl⟩ : ∃ l, σ = Config.run s_G T_G :: l := by
    cases σ with
    | nil => simp at hσhead
    | cons a l => simp only [List.head?_cons, Option.some.injEq] at hσhead; exact ⟨l, hσhead ▸ rfl⟩
  have hσchain : List.IsChain CTAStep (Config.run s_G T_G :: σtail) := hσIC.subtrace
  rw [List.isChain_cons] at hσchain
  -- glue: `τ' = pre ++ σtail`, with `C_G` at index `pre.length - 1`
  refine ⟨pre ++ σtail, pre.length - 1, s_G, T_G, ⟨⟨?_, ?_⟩, ?_⟩, ?_, hcut⟩
  · -- chain
    refine List.IsChain.append hch hσchain.2 ?_
    intro x hx y hy
    rw [hlast, Option.mem_some_iff] at hx
    subst hx
    exact hσchain.1 y hy
  · -- ends terminal
    obtain ⟨Cₙ, hτlast, hterm⟩ := hσIC.ends
    refine ⟨Cₙ, ?_, hterm⟩
    have hsplit : pre ++ σtail = pre.dropLast ++ (Config.run s_G T_G :: σtail) := by
      conv_lhs => rw [← List.dropLast_concat_getLast hpne, hgl]
      simp
    rw [hsplit]; exact List.mem_getLast?_append_of_mem_getLast? hτlast
  · -- head
    rw [List.head?_append_of_ne_nil _ hpne, hhd]
  · -- `τ'[pre.length - 1] = C_G`
    rw [List.getElem?_append_left (by omega : pre.length - 1 < pre.length)]
    rw [← List.getLast?_eq_getElem?]; exact hlast

/-- **Realizability / reversing-schedule lemma** — the heart of preciseness (the
genuine cross-thread content). If `η₁` is *not* happens-before `η₂`, then some
complete trace from `(I, T)` runs `η₂` strictly before `η₁`.

Construction (strategy C/D, by induction on program size `CTA.numCmds`): the set
`G = {η | ¬ happensBefore T τ η₁ η}` is *down-closed* under `initRelation` edges — it
is a per-thread program **prefix** (program order), and it contains whole barrier
rounds (same-generation `sync`s are mutually related, so a round is wholly in or
wholly out of `G`). Run `G` to completion first — reaching a clean configuration with
exactly the complement `F` remaining — then finish with `exists_completeTrace`. Since
`η₂ ∈ G` (`¬ happensBefore η₁ η₂`, reflexively `η₂ ≠ η₁`) and `η₁ ∉ G` (`happensBefore`
is reflexive), `η₂` executes in the `G`-prefix and `η₁` in the `F`-suffix, so
`t(η₂) < t(η₁)`.

This is the one remaining `sorry`; the contrapositive wrapper (`happensBefore_precise`,
different-threads case) is complete. -/
theorem exists_reversing_trace {T : CTA} {τ : List Config} (hws : T.WellSynchronized)
    {η₁ η₂ : ProgPoint} (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hcon : ¬ happensBefore T τ η₁ η₂) :
    ∃ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      ∃ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ ∧
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ ∧ n₂ < n₁ := by
  -- Run `G` first: a complete trace `τ'` and a cut index `p` where exactly `G` is done.
  obtain ⟨τ', p, s_G, T_G, hcomp, hpcfg, hGdone⟩ := run_ideal (T := T) (τ := τ) (η₁ := η₁) hws
  -- The trace ends in `done`, so both (valid) points execute.
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hv₁L : η₁.idx < (T.prog η₁.thread).length := ((mem_progPoints_iff T η₁).mp hv₁).2
  have hv₂L : η₂.idx < (T.prog η₂.thread).length := ((mem_progPoints_iff T η₂).mp hv₂).2
  obtain ⟨n₁, ht₁⟩ := exists_time_of_ends_done hcomp hdone (η := η₁) hv₁L
  obtain ⟨n₂, ht₂⟩ := exists_time_of_ends_done hcomp hdone (η := η₂) hv₂L
  refine ⟨τ', hcomp, n₁, n₂, ht₁, ht₂, ?_⟩
  -- `(run s_G T_G).progOf i = T_G.prog i = (T.prog i).drop (cut i)`.
  have hcut₁ : fcut T τ η₁ η₁.thread ≤ η₁.idx := fcut_le_of_hb Relation.ReflTransGen.refl hv₁
  have hcut₂ : η₂.idx < fcut T τ η₁ η₂.thread := lt_fcut_of_not_hb hcon hv₂
  -- `η₂ ∈ G` is already executed at `p` ⟹ `n₂ ≤ p`.
  have hn₂ : n₂ ≤ p := by
    refine time_le_of_progOf_le ht₂ hpcfg ?_
    show (T_G.prog η₂.thread).length ≤ _
    rw [hGdone η₂.thread, List.length_drop]
    show (T.prog η₂.thread).length - fcut T τ η₁ η₂.thread
      ≤ ((Config.run State.initial T).progOf η₂.thread).length - η₂.idx - 1
    show _ ≤ (T.prog η₂.thread).length - η₂.idx - 1
    omega
  -- `η₁ ∈ F` is not yet executed at `p` ⟹ `p < n₁`.
  have hn₁ : p < n₁ := by
    refine lt_time_of_lt_progOf ht₁ hpcfg ?_
    show ((Config.run State.initial T).progOf η₁.thread).length - η₁.idx - 1 < (T_G.prog η₁.thread).length
    rw [hGdone η₁.thread, List.length_drop]
    show (T.prog η₁.thread).length - η₁.idx - 1 < (T.prog η₁.thread).length - fcut T τ η₁ η₁.thread
    omega
  omega

/-- Preciseness half of Lemma 1: the happens-before relation captures *every* genuine
ordering — if `η₁` executes no later than `η₂` in every complete trace from `(I, T)`,
then `happensBefore T τ η₁ η₂` holds. (Per the paper: by induction on program size,
since the tuples in `R` are the only ordering restrictions the semantics imposes.)
This is the `←` direction of `SoundAndPrecise`.

The `η₁, η₂ ∈ T.progPoints` hypotheses are **necessary**: a non-executing point has no
`IsTimeOf`, so `hle` would hold vacuously while `happensBefore` (whose edges only touch
program points, `initRelation_cases`) cannot relate it — the same vacuous-timing defect
that forced reflexivity, now for invalid indices.

Cases on the two points:
* `η₁ = η₂` — `Relation.ReflTransGen.refl`.
* same thread, `η₁ ≠ η₂` — `hle` forces `η₁.idx < η₂.idx` (`time_lt_of_idx_lt`), and the
  program-order edges chain `η₁` to `η₂` (`progOrder_happensBefore`). **Proved.**
* different threads — the genuine content: an inter-thread ordering must run through a
  barrier, and one must exhibit the `Relation.TransGen` chain witnessing it (the paper's
  argument that the `initRelation` tuples are the *only* restrictions the semantics
  imposes). This is the one remaining `sorry`. -/
theorem happensBefore_precise {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hle : ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :
    happensBefore T τ η₁ η₂ := by
  -- TODO (rohany): This theorem is not making much progress by claude,
  --  which is mostly spinning and creating new lemmas to solve the problem
  --  and sticking sorries in those. A different approach will be required,
  --  probably one that gives more help to claude in the form of proof strategy
  --  and/or helper lemmas.
  sorry
  -- by_cases hη : η₁ = η₂
  -- · -- reflexive corner: every point is happens-before itself
  --   subst hη; exact Relation.ReflTransGen.refl
  -- · by_cases hthread : η₁.thread = η₂.thread
  --   · -- same thread: forced order is program order
  --     obtain ⟨i₁, k₁⟩ := η₁
  --     obtain ⟨i₂, k₂⟩ := η₂
  --     replace hthread : i₁ = i₂ := hthread
  --     subst hthread
  --     replace hη : k₁ ≠ k₂ := fun h => hη (by rw [h])
  --     obtain ⟨hcomplete, sd, hdone⟩ := hτ
  --     have hv₁' : (⟨i₁, k₁⟩ : ProgPoint).idx <
  --         ((Config.run State.initial T).progOf (⟨i₁, k₁⟩ : ProgPoint).thread).length :=
  --       ((mem_progPoints_iff T _).mp hv₁).2
  --     have hv₂' : (⟨i₁, k₂⟩ : ProgPoint).idx <
  --         ((Config.run State.initial T).progOf (⟨i₁, k₂⟩ : ProgPoint).thread).length :=
  --       ((mem_progPoints_iff T _).mp hv₂).2
  --     obtain ⟨n₁, ht₁⟩ := exists_time_of_ends_done hcomplete hdone hv₁'
  --     obtain ⟨n₂, ht₂⟩ := exists_time_of_ends_done hcomplete hdone hv₂'
  --     have hn : n₁ ≤ n₂ := hle τ hcomplete n₁ n₂ ht₁ ht₂
  --     have hidx : k₁ < k₂ := by
  --       rcases Nat.lt_trichotomy k₁ k₂ with h | h | h
  --       · exact h
  --       · exact absurd h hη
  --       · exact absurd (time_lt_of_idx_lt ht₂ ht₁ rfl h) (by omega)
  --     exact progOrder_happensBefore (le_of_lt hidx) ((mem_progPoints_iff T _).mp hv₂).2
  --   · -- different threads: contrapositive via the reversing-schedule lemma
  --     by_contra hcon
  --     obtain ⟨τ', hτ'c, n₁, n₂, ht₁, ht₂, hlt⟩ := exists_reversing_trace hws hv₁ hv₂ hcon
  --     exact absurd (hle τ' hτ'c n₁ n₂ ht₁ ht₂) (by omega)

/-- **Lemma 1.** For a well-synchronized configuration `(I, T)`, the static
happens-before relation constructed in Figure 4 — `happensBefore T τ`, the
reflexive-transitive closure of `initRelation T τ` — is sound and precise in the
sense of Definition 4 (`Weft.SoundAndPrecise`), **on program points**.

The valid-point restriction (`η₁ η₂ ∈ T.progPoints`) is required: the unrestricted
`SoundAndPrecise` is false, because for a never-executing point the timing side is
vacuously true while `happensBefore` cannot relate it (see `happensBefore_precise`).
Assembled from the two directions `happensBefore_sound` and `happensBefore_precise`. -/
theorem soundAndPrecise_happensBefore {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    ∀ η₁ η₂ : ProgPoint, η₁ ∈ T.progPoints → η₂ ∈ T.progPoints →
      (happensBefore T τ η₁ η₂ ↔
        ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
          ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
            IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) := by
  intro η₁ η₂ hv₁ hv₂
  exact ⟨happensBefore_sound hτ hws, happensBefore_precise hτ hws hv₁ hv₂⟩

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

/-! ## Theorem 2 — completeness of `CheckWellSynchronized`

The paper's **Theorem 2**, the converse of Theorem 1: the check never rejects a
genuinely well-synchronized CTA. Equivalently — the form stated below — *if the check
returns `false`, the CTA is not well-synchronized*. "Completeness of WELLSYNC follows
because well-synchronized programs have a precise `R`": this `false → ¬WS` form is the
contrapositive of `T.WellSynchronized → (CheckWellSynchronized T τ).1 = true`, and it is
that contrapositive's `hws : T.WellSynchronized` hypothesis (introduced by
`by_contra`) that makes the preciseness half of Lemma 1 (`happensBefore_precise`)
available — preciseness needs well-synchronization, so only this direction can use it
(the converse `¬WS → false` is the contrapositive of Theorem 1's *soundness*, proved
there by induction, *not* via Lemma 1).

Proof route. Assume `T.WellSynchronized`; show the Step-3 check passes (so it cannot be
`false`). For each flagged pair — a generation-`k` `sync` `c1` on `b` and a
generation-`k+1` barrier op `c2` on `b` with in-thread predecessor `c3` — we must show
`(c1, c3) ∈ (CheckWellSynchronized T τ).2 = transClosure (initRelation T τ)`. Beyond
`happensBefore_precise`, this rests on two facts not yet available in this file:

  * **a per-thread generation lemma** — a thread that reaches a generation-`k+1` op on
    `b` has a generation-`k` `sync` on `b` at an *earlier* index; that earlier `sync`
    executes at the unique `k`-th recycle of `b` (simultaneously with `c1`) and, by
    program order, sits at or before `c3`. This yields `c1 ≤ c3` in *every* complete
    trace — exactly the hypothesis `happensBefore_precise` consumes to deliver
    `happensBefore T τ c1 c3`.
  * **the `Prop`→`Finset` converse** of `mem_transClosure_imp_transGen` (the open TODO
    above) — to turn that `happensBefore T τ c1 c3` into the `Finset` membership the
    `decide` in Step 3 tests.

Stated here as a stub. -/

/-- **Theorem 2 (completeness).** If `τ` is a complete trace from `(I, T)` ending in
`done` (`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns `false`,
then `T` is *not* well-synchronized. -/
theorem not_wellSynchronized_of_check_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    ¬ T.WellSynchronized := by
  sorry

end Weft
