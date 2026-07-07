/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftNamedBarriers.WellSynchronized
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
`IsGenOf` on a genuine trace from `(I, T)` (the 1-indexed `+ 1` convention; the
relational `IsGenOf` marks a command that never executes with `none`, while the
`Nat`-valued `pointGen` uses `0` — see the `IsGenOf` doc).
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

/-- One saturation round: add a composed edge `(e.1, f.2)` whenever `e ∈ S` and
`f ∈ R` meet at `e.2 = f.1`. -/
def transClosureStep {α : Type*} [DecidableEq α] (R S : Finset (α × α)) : Finset (α × α) :=
  S ∪ S.biUnion fun e => (R.filter fun f => e.2 = f.1).image fun f => (e.1, f.2)

/-- The transitive closure of a relation given as a finite set of edges `R`:
repeatedly add a composed edge `(e.1, f.2)` whenever `e ∈ S` and `f ∈ R` meet at
`e.2 = f.1`. Saturating for `R.card` rounds suffices, since a simple path uses at
most `|R|` edges. -/
def transClosure {α : Type*} [DecidableEq α] (R : Finset (α × α)) : Finset (α × α) :=
  (transClosureStep R)^[R.card] R

/-- Soundness direction of the `transClosure` characterization: every pair in the
closure is connected by a nonempty path of `R`-edges, i.e. lies in `Relation.TransGen`
of edge membership. Proved by induction on the saturation rounds (each round only
adds composites of existing reachable pairs with `R`-edges). -/
theorem mem_transClosure_imp_transGen {α : Type*} [DecidableEq α] (R : Finset (α × α)) :
    ∀ {a b : α}, (a, b) ∈ transClosure R → Relation.TransGen (fun x y => (x, y) ∈ R) a b := by
  have key : ∀ (n : ℕ) (a b : α),
      (a, b) ∈ (transClosureStep R)^[n] R →
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
        simp only [transClosureStep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter, Prod.mk.injEq] at h
        rcases h with h | ⟨e, he, f, ⟨hfR, hef⟩, ha, hb⟩
        · exact ih a b h
        · subst ha; subst hb
          have hmem : (e.2, f.2) ∈ R := by
            have heq : (e.2, f.2) = f := Prod.ext_iff.mpr ⟨hef, rfl⟩
            rw [heq]; exact hfR
          exact (ih e.1 e.2 he).tail hmem
  intro a b h
  exact key R.card a b h

/-! ### Converse of `mem_transClosure_imp_transGen`

Every `Relation.TransGen` pair lands in the executable `transClosure`. The argument is
the diameter bound: a `TransGen` pair has a *shortest* `R`-chain, whose vertices are
distinct (a repeat could be cut, contradicting minimality), so its edges are distinct
elements of `R` — at most `R.card` of them — and a `k`-edge chain is reached after
`k - 1 ≤ R.card` saturation rounds. -/

section TransClosureConverse
variable {α : Type*} [DecidableEq α]

/-- One round only grows the accumulator. -/
theorem subset_transClosureStep (R S : Finset (α × α)) : S ⊆ transClosureStep R S :=
  Finset.subset_union_left

/-- Saturation is monotone in the accumulator. -/
theorem transClosureStep_mono (R : Finset (α × α)) {S S' : Finset (α × α)} (h : S ⊆ S') :
    transClosureStep R S ⊆ transClosureStep R S' :=
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

/-- The base relation sits inside every iterate. -/
theorem subset_iterate_transClosureStep (R : Finset (α × α)) (n : ℕ) :
    R ⊆ (transClosureStep R)^[n] R := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (subset_transClosureStep R _)

/-- Iterating more rounds only grows the set. -/
theorem iterate_transClosureStep_mono (R : Finset (α × α)) {m n : ℕ} (h : m ≤ n) :
    (transClosureStep R)^[m] R ⊆ (transClosureStep R)^[n] R := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply']
      exact ih.trans (subset_transClosureStep R _)

/-- Membership in one saturation round: either already present, or a pair extended by
one `R`-edge. -/
theorem mem_transClosureStep_iff (R S : Finset (α × α)) {a b : α} :
    (a, b) ∈ transClosureStep R S ↔ (a, b) ∈ S ∨ ∃ d, (a, d) ∈ S ∧ (d, b) ∈ R := by
  rw [transClosureStep, Finset.mem_union]
  refine or_congr_right ?_
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨e1, e2⟩, he, hmem⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨⟨f1, f2⟩, hf, hef⟩ := hmem
    rw [Finset.mem_filter] at hf
    obtain ⟨hfR, he2f1⟩ := hf
    dsimp only at he2f1 hef
    rw [Prod.mk.injEq] at hef
    obtain ⟨ha, hb⟩ := hef
    subst ha; subst hb; subst he2f1
    exact ⟨e2, he, hfR⟩
  · rintro ⟨d, had, hdb⟩
    refine ⟨(a, d), had, ?_⟩
    rw [Finset.mem_image]
    exact ⟨(d, b), by rw [Finset.mem_filter]; exact ⟨hdb, rfl⟩, rfl⟩

/-- Append one `R`-edge to a pair already accumulated, advancing one round. -/
theorem mem_transClosureStep_of_mem_R (R S : Finset (α × α)) {a d c : α}
    (hS : (a, d) ∈ S) (hR : (d, c) ∈ R) : (a, c) ∈ transClosureStep R S := by
  rw [mem_transClosureStep_iff]; exact Or.inr ⟨d, hS, hR⟩

/-- Prepend one `R`-edge to a pair in the `n`-th iterate, advancing one round. -/
theorem mem_iterate_prepend (R : Finset (α × α)) {a x : α} :
    ∀ {n : ℕ} {b : α}, (a, x) ∈ R → (x, b) ∈ (transClosureStep R)^[n] R →
      (a, b) ∈ (transClosureStep R)^[n + 1] R := by
  intro n
  induction n with
  | zero =>
      intro b hax hxb
      simp only [Function.iterate_zero, id_eq] at hxb
      rw [zero_add, Function.iterate_one]
      exact mem_transClosureStep_of_mem_R R R hax hxb
  | succ k ih =>
      intro b hax hxb
      rw [Function.iterate_succ_apply', mem_transClosureStep_iff] at hxb
      rcases hxb with hxb | ⟨d, hxd, hdb⟩
      · exact iterate_transClosureStep_mono R (Nat.le_succ _) (ih hax hxb)
      · rw [Function.iterate_succ_apply']
        exact mem_transClosureStep_of_mem_R R _ (ih hax hxd) hdb

/-- A chain of `R`-edges `a :: l` (with `l ≠ []`) lands in the `(|l|-1)`-th iterate. -/
theorem mem_iterate_of_isChain (R : Finset (α × α)) :
    ∀ {l : List α} {a b : α}, List.IsChain (fun x y => (x, y) ∈ R) (a :: l) →
      (a :: l).getLast? = some b → l ≠ [] →
      (a, b) ∈ (transClosureStep R)^[l.length - 1] R := by
  intro l
  induction l with
  | nil => intro a b _ _ hne; exact absurd rfl hne
  | cons x rest ih =>
      intro a b hchain hlast _
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hax, hchain'⟩ := hchain
      cases rest with
      | nil =>
          rw [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          simpa using hax
      | cons y rest' =>
          have hlast' : (x :: y :: rest').getLast? = some b := by
            rw [List.getLast?_cons_cons] at hlast; exact hlast
          have hxb := ih hchain' hlast' (by simp)
          have hlen : (y :: rest').length - 1 + 1 = (x :: y :: rest').length - 1 := by
            simp only [List.length_cons]; omega
          rw [← hlen]
          exact mem_iterate_prepend R hax hxb

omit [DecidableEq α] in
/-- A nodup `R`-chain has at most `R.card` edges (its distinct consecutive pairs are
distinct elements of `R`). -/
theorem nodup_chain_length_le (R : Finset (α × α)) {a : α} {l : List α}
    (hchain : List.IsChain (fun x y => (x, y) ∈ R) (a :: l)) (hnd : (a :: l).Nodup) :
    l.length ≤ R.card := by
  have key : (Finset.range l.length).card ≤ R.card := by
    refine Finset.card_le_card_of_injOn
      (fun i => ((a :: l)[i]?.getD a, (a :: l)[i + 1]?.getD a)) ?_ ?_
    · intro i hi
      rw [Finset.coe_range, Set.mem_Iio] at hi
      have h1 : i < (a :: l).length := by simp only [List.length_cons]; omega
      have h2 : i + 1 < (a :: l).length := by simp only [List.length_cons]; omega
      simp only [Finset.mem_coe, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
        Option.getD_some]
      exact (List.isChain_iff_getElem.mp hchain) i h2
    · intro i hi j hj hij
      rw [Finset.coe_range, Set.mem_Iio] at hi hj
      have h1 : i < (a :: l).length := by simp only [List.length_cons]; omega
      have h2 : j < (a :: l).length := by simp only [List.length_cons]; omega
      simp only [Prod.mk.injEq, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
        Option.getD_some] at hij
      exact (List.Nodup.getElem_inj_iff hnd).mp hij.1
  rwa [Finset.card_range] at key

omit [DecidableEq α] in
/-- Loop-cutting: any nonempty `R`-chain contains a *nodup* `R`-chain with the same
head and last (drawn from the same vertices). -/
theorem exists_nodup_isChain (R : Finset (α × α)) :
    ∀ (vs : List α), vs ≠ [] → List.IsChain (fun x y => (x, y) ∈ R) vs →
      ∃ ws, ws ≠ [] ∧ List.IsChain (fun x y => (x, y) ∈ R) ws ∧
        ws.head? = vs.head? ∧ ws.getLast? = vs.getLast? ∧ ws.Nodup ∧ ∀ x ∈ ws, x ∈ vs := by
  suffices H : ∀ n (vs : List α), vs.length = n → vs ≠ [] →
      List.IsChain (fun x y => (x, y) ∈ R) vs →
      ∃ ws, ws ≠ [] ∧ List.IsChain (fun x y => (x, y) ∈ R) ws ∧
        ws.head? = vs.head? ∧ ws.getLast? = vs.getLast? ∧ ws.Nodup ∧ ∀ x ∈ ws, x ∈ vs by
    intro vs hne hchain; exact H vs.length vs rfl hne hchain
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro vs hlen hne hchain
    -- last element of a `cons` with a nonempty tail
    have hg : ∀ (w : α) (zs : List α), zs ≠ [] → (w :: zs).getLast? = zs.getLast? := by
      intro w zs hzs
      obtain ⟨u, zs', rfl⟩ := List.exists_cons_of_ne_nil hzs
      rw [List.getLast?_cons_cons]
    by_cases hnd : vs.Nodup
    · exact ⟨vs, hne, hchain, rfl, rfl, hnd, fun x hx => hx⟩
    · obtain ⟨v, rest, rfl⟩ : ∃ v rest, vs = v :: rest := by
        cases vs with
        | nil => exact absurd rfl hne
        | cons v rest => exact ⟨v, rest, rfl⟩
      by_cases hvr : v ∈ rest
      · obtain ⟨pre, post, hrest⟩ := List.append_of_mem hvr
        have hcons : v :: rest = (v :: pre) ++ (v :: post) := by rw [hrest, List.cons_append]
        have hsuf : (v :: post) <:+ (v :: rest) := ⟨v :: pre, hcons.symm⟩
        have hchain' : List.IsChain (fun x y => (x, y) ∈ R) (v :: post) := hchain.suffix hsuf
        have hlt : (v :: post).length < n := by
          rw [← hlen, hcons]; simp only [List.length_append, List.length_cons]; omega
        obtain ⟨ws, hwne, hwc, hwh, hwl, hwnd, hwsub⟩ :=
          IH (v :: post).length hlt (v :: post) rfl (by simp) hchain'
        have hglast : (v :: rest).getLast? = (v :: post).getLast? := by
          rw [hcons]; exact List.getLast?_append_cons (v :: pre) v post
        refine ⟨ws, hwne, hwc, by simp only [hwh, List.head?_cons], ?_, hwnd,
          fun x hx => hsuf.subset (hwsub x hx)⟩
        rw [hwl, hglast]
      · have hrne : rest ≠ [] := by
          rintro rfl; exact hnd (by simp)
        have hrc : List.IsChain (fun x y => (x, y) ∈ R) rest := hchain.tail
        obtain ⟨ws, hwne, hwc, hwh, hwl, hwnd, hwsub⟩ :=
          IH rest.length (by rw [← hlen]; simp) rest rfl hrne hrc
        refine ⟨v :: ws, by simp, ?_, by simp only [List.head?_cons], ?_, ?_, ?_⟩
        · exact hwc.cons (fun b hb => hchain.rel_head? (hwh ▸ hb))
        · rw [hg v ws hwne, hwl, hg v rest hrne]
        · exact List.nodup_cons.2 ⟨fun hv => hvr (hwsub v hv), hwnd⟩
        · intro x hx
          rw [List.mem_cons] at hx ⊢
          exact hx.imp_right (hwsub x)

/-- **Converse of `mem_transClosure_imp_transGen`.** Every (off-diagonal) `TransGen`
pair lands in the executable transitive closure. -/
theorem mem_transClosure_of_transGen (R : Finset (α × α)) {a b : α} (hne : a ≠ b)
    (h : Relation.TransGen (fun x y => (x, y) ∈ R) a b) : (a, b) ∈ transClosure R := by
  -- a chain from `a` to `b` with at least one edge
  rw [Relation.TransGen.head'_iff] at h
  obtain ⟨c, hac, hcb⟩ := h
  obtain ⟨l', hchain', hlast'⟩ := List.exists_isChain_cons_of_relationReflTransGen hcb
  have hchain : List.IsChain (fun x y => (x, y) ∈ R) (a :: c :: l') :=
    hchain'.cons (by intro z hz; rw [List.head?_cons, Option.mem_some_iff] at hz; exact hz ▸ hac)
  have hlast : (a :: c :: l').getLast? = some b := by
    rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (l := c :: l') (by simp), hlast']
  -- cut to a nodup chain with the same endpoints
  obtain ⟨ws, hwne, hwc, hwh, hwl, hwnd, _⟩ :=
    exists_nodup_isChain R (a :: c :: l') (by simp) hchain
  rw [List.head?_cons] at hwh
  -- `ws = a :: m`
  obtain ⟨m, rfl⟩ : ∃ m, ws = a :: m := by
    cases ws with
    | nil => exact absurd hwh (by simp)
    | cons w m => rw [List.head?_cons, Option.some.injEq] at hwh; exact ⟨m, by rw [hwh]⟩
  rw [hlast] at hwl
  have hm : m ≠ [] := by
    rintro rfl
    rw [List.getLast?_singleton, Option.some.injEq] at hwl
    exact hne hwl
  -- the nodup chain has `≤ R.card` edges, so it is reached within `R.card` rounds
  have hbound : m.length ≤ R.card := nodup_chain_length_le R hwc hwnd
  have hmem := mem_iterate_of_isChain R hwc hwl hm
  rw [transClosure]
  exact iterate_transClosureStep_mono R (by omega) hmem

end TransClosureConverse

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
              simp only [List.mem_cons, List.not_mem_nil, or_false,
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
  -- The source `c1` ranges over *every* barrier operation (`sync` *and* `arrive`),
  -- not just `sync`s: an `arrive` of generation `k` must likewise happen-before any
  -- generation-`k+1` operation on the same barrier.
  let ok : Bool := T.progPoints.all fun c1 =>
    match (T.cmdAt c1).bind Cmd.barrier? with
    | some b =>
        let k := pointGen T τ c1
        T.progPoints.all fun c2 =>
          match (T.cmdAt c2).bind Cmd.barrier? with
          | some b' =>
              if b = b' ∧ pointGen T τ c2 = k + 1 then
                if 1 ≤ c2.idx then
                  -- `c3 = ⟨c2.thread, c2.idx - 1⟩` is `c2`'s predecessor (`c3 ; c2 ∈ T`).
                  -- The required ordering is the reflexive `c1 ≤ c3`: the `c1 = c3`
                  -- disjunct accounts for reflexivity directly (the finite `hb` carries
                  -- only the irreflexive part), so a source that *is* `c2`'s predecessor
                  -- — e.g. an `arrive` closing its round just before `c2` — is not
                  -- spuriously flagged.
                  decide (c1 = (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∨
                    (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∈ hb)
                else
                  -- `c2` is a generation-`(k+1)` barrier operation that is the *first*
                  -- instruction of its thread (`c2.idx = 0`), so it has no in-thread
                  -- predecessor `c3` on which to anchor the `c1 ≤ c3` happens-before.
                  -- Nothing forces it to wait for generation `k`: a schedule that runs
                  -- `c2` first lands it in an earlier generation, so the CTA is *not*
                  -- well-synchronized. Reject.
                  false
              else
                true
          | none => true
    | none => true
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
reverse inclusion (completeness of the `Finset`) is the `transClosure` converse
`mem_transClosure_of_transGen`, now proved above (used by `not_happensBefore_of_not_mem`). -/
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
theorem pointTime_eq_of_isTimeOf {T : CTA} {s : State} {τ : List Config} {η : ProgPoint} {m : Nat}
    (hexec : IsTimeOf (Config.run s T) τ η m) : pointTime T τ η = some m := by
  have hτ := hexec.1
  have hidxL : η.idx < (T.prog η.thread).length := hexec.2.1
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run s T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hC₀ : (Config.run s T).progOf η.thread = T.prog η.thread := rfl
  set f : Nat → Option Nat := fun j =>
    match τ[j]?, τ[j + 1]? with
    | some C, some C' =>
        if (C.progOf η.thread).length == (T.prog η.thread).length - η.idx
            && (C'.progOf η.thread).length == (T.prog η.thread).length - η.idx - 1 then
          some (j + 1) else none
    | _, _ => none with hf
  have hfwd : ∀ a x, f a = some x → IsTimeOf (Config.run s T) τ η x := by
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
    push Not
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
executes in `τ`, `IsGenOf (I, T) τ a (some (pointGen T τ a))` holds (`pointTime` computes the
time, so `pointGen` computes `recycleCount …`). -/
theorem isGenOf_pointGen {T : CTA} {τ : List Config} {a : ProgPoint} {bb : Barrier} {ma : Nat}
    (hbb : (T.cmdAt a).bind Cmd.barrier? = some bb)
    (hma : IsTimeOf (Config.run State.initial T) τ a ma) :
    IsGenOf (Config.run State.initial T) τ a (some (pointGen T τ a)) := by
  have hpt : pointTime T τ a = some ma := pointTime_eq_of_isTimeOf hma
  have hpg : pointGen T τ a = recycleCount bb τ (ma - 1) + 1 := by
    simp only [pointGen, hbb, hpt]
  exact ⟨hma.1, bb, hbb, Or.inl ⟨ma, hma, by rw [hpg]⟩⟩

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
    have hgenA : IsGenOf (Config.run State.initial T) τ a (some (pointGen T τ a)) :=
      isGenOf_pointGen habar hma.choose_spec
    have hgenB : IsGenOf (Config.run State.initial T) τ b (some (pointGen T τ b)) :=
      isGenOf_pointGen hbbar hmb.choose_spec
    -- well-synchronization transfers the generation to `τ'`
    obtain ⟨ga, hgaτ, hgaτ'⟩ := hws.2 τ τ' hτ.1 hτ' a ⟨bb, habar⟩
    obtain ⟨gb, hgbτ, hgbτ'⟩ := hws.2 τ τ' hτ.1 hτ' b ⟨bb, hbbar⟩
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
(`initRelation_src_timed`), so `≤` chains.
NOTE (rohany): This is a top-level theorem.
-/
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

/-- **Full membership characterization of `initRelation`** (the converse-complete form of
`initRelation_cases`, retaining the arrival count `n` that `initRelation_cases` drops). An
edge `(a, b)` of `initRelation T τ` is exactly one of:
* a program-order edge `b = ⟨a.thread, a.idx + 1⟩` (with `a.idx + 1` in range);
* an `arrive bb n → sync bb n` edge of equal generation (Figure 4 lines 7–11);
* a `sync bb n ↔ sync bb n` edge of equal generation (lines 12–16) — symmetric, so the
  same shape covers both endpoints being `sync`.

Keeping `n` is what lets `second_batch_hb_within` *reconstruct* the shifted edge in the
neighbouring batch (the generation offset is by-barrier, so equal generations stay equal). -/
theorem mem_initRelation_iff {T : CTA} {τ : List Config} {a b : ProgPoint} :
    (a, b) ∈ initRelation T τ ↔
      (a ∈ T.progPoints ∧ a.idx + 1 < (T.prog a.thread).length ∧ b = ⟨a.thread, a.idx + 1⟩)
      ∨ (∃ bb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.arrive bb n) ∧ T.cmdAt b = some (.sync bb n) ∧
          pointGen T τ a = pointGen T τ b)
      ∨ (∃ bb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.sync bb n) ∧ T.cmdAt b = some (.sync bb n) ∧
          pointGen T τ a = pointGen T τ b) := by
  constructor
  · intro hedge
    simp only [initRelation, List.mem_toFinset, List.mem_append] at hedge
    rcases hedge with (hpo | has) | hss
    · -- program order
      simp only [List.mem_filterMap] at hpo
      obtain ⟨c, hc, hceq⟩ := hpo
      split at hceq
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hceq
        obtain ⟨rfl, rfl⟩ := hceq
        exact Or.inl ⟨hc, hcond, rfl⟩
      · exact absurd hceq (by simp)
    · -- arrive → sync
      simp only [List.mem_flatMap] at has
      obtain ⟨c1, hc1, hin⟩ := has
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | sync bb n => simp [hcmd1] at hin
        | arrive bb n =>
          simp only [hcmd1, List.mem_filterMap] at hin
          obtain ⟨c2, hc2, hc2eq⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hc2eq
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hc2eq
            | write g => simp [hcmd2] at hc2eq
            | arrive b' n' => simp [hcmd2] at hc2eq
            | sync b' n' =>
              simp only [hcmd2] at hc2eq
              split at hc2eq
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
                obtain ⟨rfl, rfl⟩ := hc2eq
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                exact Or.inr (Or.inl ⟨bb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩)
              · exact absurd hc2eq (by simp)
    · -- sync ↔ sync
      simp only [List.mem_flatMap] at hss
      obtain ⟨c1, hc1, hin⟩ := hss
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | arrive bb n => simp [hcmd1] at hin
        | sync bb n =>
          simp only [hcmd1, List.mem_flatMap] at hin
          obtain ⟨c2, hc2, hin2⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hin2
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hin2
            | write g => simp [hcmd2] at hin2
            | arrive b' n' => simp [hcmd2] at hin2
            | sync b' n' =>
              simp only [hcmd2] at hin2
              split at hin2
              · rename_i hcond
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                simp only [List.mem_cons, List.not_mem_nil, or_false,
                  Prod.mk.injEq] at hin2
                rcases hin2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr (Or.inr ⟨bb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩)
                · exact Or.inr (Or.inr ⟨bb, n, hc2, hc1, hcmd2, hcmd1, hgen.symm⟩)
              · simp at hin2
  · intro h
    rcases h with ⟨hapts, hlt, hbeq⟩ | ⟨bb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
        | ⟨bb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
    · -- program order
      obtain ⟨at', ai⟩ := a
      subst hbeq
      exact mem_initRelation_progOrder hlt
    · -- arrive → sync
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap,
        List.mem_filterMap]
      refine Or.inl (Or.inr ⟨a, hapts, ?_⟩)
      simp only [hcmda, List.mem_filterMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩
    · -- sync ↔ sync
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap]
      refine Or.inr ⟨a, hapts, ?_⟩
      simp only [hcmda, List.mem_flatMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩

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

open Classical in
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
  classical
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
  classical
  have hηeq : (⟨η.thread, η.idx⟩ : ProgPoint) = η := rfl
  have hvlt : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hv).2
  by_contra hle
  push Not at hle
  unfold fcut at hle
  split at hle
  · rename_i hex
    obtain ⟨hhb, _⟩ := Nat.find_spec hex
    exact h (hηeq ▸ hhb.trans (progOrder_happensBefore hle hvlt))
  · omega

/-- The cut never exceeds the program length. -/
theorem fcut_le_length (T : CTA) (τ : List Config) (η₁ : ProgPoint) (i : ThreadId) :
    fcut T τ η₁ i ≤ (T.prog i).length := by
  classical
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
  push Not at hlt
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
  push Not at hle
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

/-! ### Operational support for the competing-sync sub-case

A thread parked in a barrier's synced list stays there until that barrier recycles —
the engine of the competing-sync contradiction. -/

/-- **Only a `b`-recycle removes a thread from `b`'s synced list.** If `t` is synced at `b`
in `C` and the step `C ⤳ C'` is *not* a recycle of `b`, then `t` is still synced at `b` in
`C'`. (A recycle of another barrier, or an `arrive`/`sync`/no-op interleaving, only *adds*
to `b`'s lists; the thread `t` itself is disabled — `BlockInv` — so cannot step.) -/
theorem synced_persists {C C' : Config} (hstep : CTAStep C C') {b : Barrier} {t : ThreadId}
    {s : State} (hCs : C.state? = some s) (hBI : s.BlockInv) (ht : t ∈ (s.B b).synced)
    (hnorec : stepRecyclesBarrier b C C' = false) {s' : State} (hCs' : C'.state? = some s') :
    t ∈ (s'.B b).synced := by
  cases hstep with
  | @interleave s₀ s'' T i P' hi hbar hth =>
    simp only [Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact ht
    | write_noop => exact ht
    | arrive_configure he hb0 =>
      rename_i b₀ n
      by_cases hbb : b = b₀
      · subst hbb; rw [hb0] at ht; simp [BarrierState.unconfigured] at ht
      · simpa only [Function.update_of_ne hbb] using ht
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      by_cases hbb : b = b₀
      · subst hbb; simp only [Function.update_self]; rw [hb0] at ht; exact ht
      · simpa only [Function.update_of_ne hbb] using ht
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb; rw [hb0] at ht; simp [BarrierState.unconfigured] at ht
      · simpa only [Function.update_of_ne hbb] using ht
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      by_cases hbb : b = b₀
      · subst hbb; simp only [Function.update_self]; rw [hb0] at ht
        exact List.mem_cons_of_mem _ ht
      · simpa only [Function.update_of_ne hbb] using ht
  | @recycle s₀ T b₀ I A n hb hfull hpark =>
    simp only [Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    by_cases hbb : b = b₀
    · subst hbb
      exfalso
      revert hnorec
      simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self, BarrierState.unconfigured]
    · simpa only [Function.update_of_ne hbb] using ht
  | @done s₀ T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'; exact ht
  | @error s₀ T i P' _ hth =>
    exact absurd hCs' (by simp [Config.state?])

/-- A full barrier is never unconfigured, so a step that leaves `b` unchanged does not
recycle it. -/
theorem isFull_and_unconfigured_false (β : BarrierState) :
    (β.isFull && decide (β = BarrierState.unconfigured)) = false := by
  unfold BarrierState.isFull
  cases hc : β.count with
  | none => simp
  | some n =>
    have hne : β ≠ BarrierState.unconfigured := by
      intro h; rw [h] at hc; simp [BarrierState.unconfigured] at hc
    simp [decide_eq_false hne]

/-- **A `b`-recycle advances every thread parked at `b`.** If `t` is synced at `b` in `C`
and the step `C ⤳ C'` *is* a recycle of `b`, then `t`'s remaining program drops its parked
`sync b` head. (Only `CTAStep.recycle` can reset `b` to unconfigured, and it wakes the
whole synced list.) -/
theorem recycle_advances_synced {C C' : Config} (hstep : CTAStep C C') {b : Barrier}
    {t : ThreadId} {s : State} (hCs : C.state? = some s) (ht : t ∈ (s.B b).synced)
    (hrec : stepRecyclesBarrier b C C' = true) :
    C'.progOf t = (C.progOf t).tail := by
  cases hstep with
  | @interleave s₀ s'' T i P' hi hbar hth =>
    exfalso
    have hnf : (s₀.B b).isFull = false := by
      rcases hbar b with h | ⟨I, A, n, hbn, hlt⟩
      · rw [h]; simp [BarrierState.isFull, BarrierState.unconfigured]
      · rw [hbn]; simp only [BarrierState.isFull, beq_eq_false_iff_ne]; omega
    simp [stepRecyclesBarrier, Config.state?, hnf] at hrec
  | @recycle s₀ T b₀ I A n hb hfull hpark =>
    by_cases hbb : b = b₀
    · subst hbb
      have htI : t ∈ I := by
        obtain rfl : s₀ = s := by simpa [Config.state?] using hCs
        rw [hb] at ht; exact ht
      simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake, if_pos htI]
    · exfalso
      simp [stepRecyclesBarrier, Config.state?, Function.update_of_ne hbb,
        isFull_and_unconfigured_false] at hrec
  | @done s₀ T hdone hnofull =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?, isFull_and_unconfigured_false] at hrec
  | @error s₀ T i P' _ hth =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?] at hrec

/-- **A `sync`'s thread is parked in `b.synced` just before its recycle.** At the configuration
preceding `η`'s execution time, `η.thread` is in `b`'s synced list (its sync head is dropped
only by the recycle that wakes the synced list). -/
theorem synced_before_recycle {C₀ : Config} {τ : List Config} {b : Barrier} {t : ThreadId}
    {η : ProgPoint} {nn : ℕ+} {n : Nat} (hm : IsTimeOf C₀ τ η n) (hηt : η.thread = t)
    (hcmd : η.cmd C₀ = some (Cmd.sync b nn)) {sm : State} {Tm : CTA}
    (hCm : τ[n - 1]? = some (Config.run sm Tm)) : t ∈ (sm.B b).synced := by
  obtain ⟨hτ, hidxL, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := hm
  subst hn
  simp only [Nat.add_sub_cancel] at hCm
  rw [hCm, Option.some.injEq] at hCj
  subst hCj
  have hstep : CTAStep (Config.run sm Tm) C' := chain_step hτ.1.subtrace hCm hCj1
  have hhead : (C₀.progOf η.thread)[η.idx]'hidxL = Cmd.sync b nn := by
    have hc := hcmd; simp only [ProgPoint.cmd] at hc
    rw [List.getElem?_eq_getElem hidxL, Option.some.injEq] at hc; exact hc
  have hCsync : (Config.run sm Tm).progOf t = Cmd.sync b nn :: C'.progOf t := by
    rw [← hηt]; rw [hCeq, hC'eq, List.drop_eq_getElem_cons hidxL, hhead]
  have hsmprog : Tm.prog t = Cmd.sync b nn :: C'.progOf t := hCsync
  have hrec : stepRecyclesBarrier b (Config.run sm Tm) C' = true :=
    sync_drop_recycles hstep hCsync rfl
  cases hstep with
  | @interleave _ s'' _ i P' hi hbar hth =>
    exfalso
    have hnf : (sm.B b).isFull = false := by
      rcases hbar b with h | ⟨I, A, n, hbn, hlt⟩
      · rw [h]; simp [BarrierState.isFull, BarrierState.unconfigured]
      · rw [hbn]; simp only [BarrierState.isFull, beq_eq_false_iff_ne]; omega
    simp [stepRecyclesBarrier, Config.state?, hnf] at hrec
  | @recycle _ _ b₀ I A m hb hfull hpark =>
    by_cases hit : t ∈ I
    · have hp := hpark t hit
      rw [hsmprog] at hp
      simp only [List.head?_cons, Option.some.injEq, Cmd.sync.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [hb]; exact hit
    · exfalso
      simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, hit] at hsmprog
  | @done _ _ hdone hnofull =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?, isFull_and_unconfigured_false] at hrec
  | @error _ _ i P' _ hth =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?] at hrec

/-- **A thread joining a synced list witnesses `hbar`.** If `t` is *not* synced at `b` in
`C` but *is* in `C'`, the step `C ⤳ C'` is an `interleave` (only a `sync` adds to a synced
list), so its `hbar` premise holds at `C`. This is the formal content of "if `c1` can take
its step, `c2` can take its step too." -/
theorem hbar_of_joins_synced {C C' : Config} (hstep : CTAStep C C') {b : Barrier} {t : ThreadId}
    {s : State} (hCs : C.state? = some s) {s' : State} (hCs' : C'.state? = some s')
    (hnotin : t ∉ (s.B b).synced) (hin : t ∈ (s'.B b).synced) :
    ∀ b', s.B b' = BarrierState.unconfigured ∨
          ∃ I A n, s.B b' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
  cases hstep with
  | @interleave s₀ s'' T i P' hi hbar hth =>
    simp only [Config.state?, Option.some.injEq] at hCs; subst hCs; exact hbar
  | @recycle s₀ T b₀ I A n hb hfull hpark =>
    exfalso
    simp only [Config.state?, Option.some.injEq] at hCs hCs'; subst hCs; subst hCs'
    by_cases hbb : b = b₀
    · subst hbb; simp [Function.update_self, BarrierState.unconfigured] at hin
    · simp only [Function.update_of_ne hbb] at hin; exact hnotin hin
  | @done s₀ T hdone hnofull =>
    exfalso
    simp only [Config.state?, Option.some.injEq] at hCs hCs'; subst hCs; subst hCs'
    exact hnotin hin
  | @error s₀ T i P' _ hth =>
    exact absurd hCs' (by simp [Config.state?])

/-- **A parked thread's `sync` recycles at the next `b`-recycle.** If `t` is parked at its
`sync b` head (synced at `b`, head `= η`) at config `p`, and `η` executes at time `n > p`,
then `b` does not recycle between `p` and `n`: the recycle count is unchanged. (By
`synced_persists`/`recycle_advances_synced`: the first `b`-recycle after `p` would wake `t`
and *be* `η`'s step, so any earlier one is impossible.) -/
theorem parked_sync_recycleCount {C₀ : Config} {τ : List Config}
    (hBI : ∀ C ∈ τ, ∀ s, C.state? = some s → s.BlockInv)
    {b : Barrier} {t : ThreadId} {η : ProgPoint} {p n : Nat}
    (hηt : η.thread = t) (hη : IsTimeOf C₀ τ η n)
    {sp : State} {Tp : CTA} (hCp : τ[p]? = some (Config.run sp Tp))
    (hpark : t ∈ (sp.B b).synced)
    (hprog : Tp.prog t = (C₀.progOf t).drop η.idx) (hpn : p < n) :
    recycleCount b τ (n - 1) = recycleCount b τ p := by
  obtain ⟨hcomplete, hidxL, j₀, Cn1, Cn, hn, hCn1, hCn, hCn1prog, hCnprog⟩ := hη
  have hchain := hcomplete.1.subtrace
  subst hn
  rw [hηt] at hCn1prog
  simp only [Nat.add_sub_cancel]
  -- program at each config in `[p, j₀]` is `drop η.idx`
  have hprogj : ∀ j, p ≤ j → j ≤ j₀ → ∀ Cj, τ[j]? = some Cj →
      Cj.progOf t = (C₀.progOf t).drop η.idx := by
    intro j hpj hjj Cj hCj
    have hsuf1 : Cj.progOf t <:+ (C₀.progOf t).drop η.idx := by
      have := progOf_suffix_index_le hchain t hCp hpj hCj
      rwa [show (Config.run sp Tp).progOf t = (C₀.progOf t).drop η.idx from hprog] at this
    have hsuf2 : (C₀.progOf t).drop η.idx <:+ Cj.progOf t := by
      have := progOf_suffix_index_le hchain t hCj hjj hCn1
      rwa [hCn1prog] at this
    have hle1 := suffix_length_le hsuf1
    have hle2 := suffix_length_le hsuf2
    exact (hsuf1.sublist.eq_of_length (by omega))
  -- by induction, `t` stays synced and the recycle count is unchanged up to each `j ∈ [p,j₀]`
  have hQ : ∀ d, p + d ≤ j₀ →
      (∃ s' T', τ[p + d]? = some (Config.run s' T') ∧ t ∈ (s'.B b).synced) ∧
        recycleCount b τ (p + d) = recycleCount b τ p := by
    intro d
    induction d with
    | zero => intro _; exact ⟨⟨sp, Tp, hCp, hpark⟩, rfl⟩
    | succ e ih =>
        intro hle
        obtain ⟨⟨s', T', hCe, hsync⟩, hrc⟩ := ih (by omega)
        have hj₀lt : j₀ + 1 < τ.length := (List.getElem?_eq_some_iff.mp hCn).1
        obtain ⟨Cnext, hCnext⟩ : ∃ C, τ[p + e + 1]? = some C :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hstep : CTAStep (Config.run s' T') Cnext := chain_step hchain hCe hCnext
        have hpe : (Config.run s' T').progOf t = (C₀.progOf t).drop η.idx :=
          hprogj (p + e) (by omega) (by omega) _ hCe
        -- this step does not recycle `b` (else it would be `η`'s step at `p+e+1 < j₀+1`)
        have hnr : stepRecyclesBarrier b (Config.run s' T') Cnext = false := by
          by_contra hrec
          rw [Bool.not_eq_false] at hrec
          have hadv : Cnext.progOf t = ((C₀.progOf t).drop η.idx).tail := by
            rw [← hpe]; exact recycle_advances_synced hstep rfl hsync hrec
          rw [List.tail_drop] at hadv
          have htime : IsTimeOf C₀ τ η (p + e + 1) :=
            ⟨hcomplete, hidxL, p + e, _, _, rfl, hCe, hCnext,
              by rw [hηt]; exact hpe, by rw [hηt]; exact hadv⟩
          have huniq := IsTimeOf.unique htime
            ⟨hcomplete, hidxL, j₀, Cn1, Cn, rfl, hCn1, hCn, by rw [hηt]; exact hCn1prog, hCnprog⟩
          omega
        -- `Cnext` is a `run` config (it has a successor, since `p+e+1 < j₀+1`)
        obtain ⟨s'', T'', rfl⟩ : ∃ s'' T'', Cnext = Config.run s'' T'' := by
          obtain ⟨Cnn, hCnn⟩ : ∃ C, τ[p + e + 1 + 1]? = some C :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          cases chain_step hchain hCnext hCnn <;> exact ⟨_, _, rfl⟩
        refine ⟨⟨s'', T'', hCnext, synced_persists hstep rfl ?_ hsync hnr rfl⟩, ?_⟩
        · exact hBI _ (List.mem_of_getElem? hCe) s' rfl
        · have hidx : p + (e + 1) = (p + e) + 1 := rfl
          have hrc' : recycleCount b τ ((p + e) + 1) = recycleCount b τ (p + e) := by
            unfold recycleCount
            rw [List.range_succ, List.countP_append]
            simp [hCe, hCnext, hnr]
          rw [hidx, hrc', hrc]
  obtain ⟨_, hfin⟩ := hQ (j₀ - p) (by omega)
  rw [show p + (j₀ - p) = j₀ from by omega] at hfin
  exact hfin

/-- `recycleCount` over the first `M` steps depends only on the first `M+1` configurations:
two traces that agree on configurations `0 … M` have the same `recycleCount … M`. -/
theorem recycleCount_prefix_eq (bb : Barrier) {τ₁ τ₂ : List Config} :
    ∀ M, (∀ j, j ≤ M → τ₁[j]? = τ₂[j]?) → recycleCount bb τ₁ M = recycleCount bb τ₂ M := by
  intro M
  induction M with
  | zero => intro _; simp [recycleCount]
  | succ M ih =>
    intro h
    unfold recycleCount
    rw [List.range_succ, List.countP_append, List.countP_append]
    congr 1
    · have hih := ih (fun j hj => h j (by omega))
      unfold recycleCount at hih; exact hih
    · have e1 := h M (by omega)
      have e2 := h (M + 1) (by omega)
      simp only [List.countP_cons, List.countP_nil, Nat.zero_add, e1, e2]

/-- A step that does not recycle `bb` leaves `recycleCount bb` unchanged. -/
theorem recycleCount_succ_of_not_recycle (bb : Barrier) {τ : List Config} {M : Nat}
    {C C' : Config} (hC : τ[M]? = some C) (hC' : τ[M + 1]? = some C')
    (hrec : stepRecyclesBarrier bb C C' = false) :
    recycleCount bb τ (M + 1) = recycleCount bb τ M := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
  simp [hC, hC', hrec]

/-- A reachability witness `C₀ ⤳* C` is realized by an actual chain (subtrace) from
`C₀` ending at `C`. -/
theorem exists_chain_of_reaches {C₀ C : Config}
    (h : Relation.ReflTransGen CTAStep C₀ C) :
    ∃ l : List Config, List.IsChain CTAStep l ∧ l.head? = some C₀ ∧ l.getLast? = some C := by
  induction h with
  | refl => exact ⟨[C₀], List.isChain_singleton _, rfl, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, hchain, hhd, hlast⟩ := ih
    have hne : l ≠ [] := by intro hl; rw [hl] at hhd; simp at hhd
    refine ⟨l ++ [c], ?_, ?_, ?_⟩
    · refine List.IsChain.append hchain (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [hlast, Option.mem_some_iff] at hx; subst hx
      rw [List.head?_cons, Option.mem_some_iff] at hy; subst hy
      exact hbc
    · rw [List.head?_append_of_ne_nil _ hne]; exact hhd
    · simp

/-- From a reachable configuration of a well-synchronized CTA, no thread step produces
`err`: such a step would extend the reaching trace to a complete trace ending in `err`,
contradicting `completeTrace_ends_done`. -/
theorem no_err_of_reach {T : CTA} (hws : T.WellSynchronized) {C : Config}
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) :
    ¬ ∃ T', CTAStep C (Config.err T') := by
  rintro ⟨T', herr⟩
  obtain ⟨l, hchain, hhd, hlast⟩ := exists_chain_of_reaches (hreach.tail herr)
  obtain ⟨sd, hd⟩ := CTA.WellSynchronized.completeTrace_ends_done hws
    ⟨⟨hchain, Config.err T', hlast, Or.inr (Or.inl ⟨T', rfl⟩)⟩, hhd⟩
  rw [hlast] at hd; simp at hd

/-- **Progress** (the operational crux). From a `G`-bounded, reachable configuration at
which `G` is *not* yet exhausted, there is a step that keeps the configuration
`G`-bounded — a `G`-step that makes progress without touching `F`. (Built on the
deadlock-freedom of a well-synchronized CTA: were no `G`-step available, the parked
`G`-threads would form a frozen set the schedule could never complete, so the run could
not reach `done`, contradicting `completeTrace_ends_done`.) -/
theorem gstep {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {C : Config} (hGB : GBounded T τ η₁ C)
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C)
    (hnotdone : ¬ Gdone T τ η₁ C) :
    ∃ C', CTAStep C C' ∧ GBounded T τ η₁ C' := by
  classical
  obtain ⟨s, T_C, rfl, hbound, hpurity⟩ := hGB
  have hwf : (Config.WF (Config.run s T_C)) := WF_of_reaches hreach
  -- a `G`-thread `i₀` still has commands below its cut (`¬ Gdone`)
  simp only [Gdone, not_forall] at hnotdone
  obtain ⟨i₀, hi₀ids, hi₀ne⟩ := hnotdone
  obtain ⟨e₀, he₀le, he₀prog⟩ := hbound i₀
  have hi₀G : e₀ < fcut T τ η₁ i₀ := by
    simp only [WeftCommon.Config.progOf] at hi₀ne
    rw [he₀prog, List.length_drop] at hi₀ne
    have hcl := fcut_le_length T τ η₁ i₀
    omega
  by_cases hfull : ∃ b I A n, s.B b = (⟨I, A, some n⟩ : BarrierState) ∧ I.length + A = (n : Nat)
  · -- **Case A**: a barrier is full — recycle it (its synced threads are `G` by purity).
    obtain ⟨b, I, A, n, hbeq, hbfull⟩ := hfull
    have hpark : ∀ j ∈ I, (T_C.prog j).head? = some (Cmd.sync b n) := (hwf.1 b I A n hbeq).2.1
    refine ⟨_, CTAStep.recycle hbeq hbfull hpark, _, _, rfl, ?_, ?_⟩
    · intro j
      obtain ⟨e, hele, heprog⟩ := hbound j
      by_cases hjI : j ∈ I
      · have hpj := hpurity b j (by rw [hbeq]; exact hjI)
        rw [heprog, List.length_drop] at hpj
        have hcl := fcut_le_length T τ η₁ j
        refine ⟨e + 1, by omega, ?_⟩
        simp only [WeftCommon.CTA.wake, hjI, if_true]
        rw [heprog, List.tail_drop]
      · exact ⟨e, hele, by simp only [WeftCommon.CTA.wake, hjI, if_false]; exact heprog⟩
    · intro b' j hj'
      by_cases hb'b : b' = b
      · subst hb'b
        simp only [Function.update_self, BarrierState.unconfigured] at hj'
        exact absurd hj' (by simp)
      · have hjsynced : j ∈ (s.B b').synced := by
          simpa only [Function.update_of_ne hb'b] using hj'
        have hjnotI : j ∉ I := by
          intro hjI
          exact hb'b (hwf.2.2.2.2 b' b j hjsynced (by rw [hbeq]; exact hjI))
        have hpj := hpurity b' j hjsynced
        simpa only [WeftCommon.CTA.wake, hjnotI, if_false] using hpj
  · -- **Case B**: no barrier is full, so `hbar` holds (every barrier unconfigured/under-full).
    push Not at hfull
    have hbar : ∀ bb, s.B bb = BarrierState.unconfigured ∨
        ∃ I A n, s.B bb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
      intro bb
      obtain ⟨bI, bA, bcnt, hbc⟩ : ∃ bI bA bcnt, s.B bb = ⟨bI, bA, bcnt⟩ := ⟨_, _, _, rfl⟩
      cases bcnt with
      | none => obtain ⟨rfl, rfl⟩ := hwf.2.1 bb bI bA hbc; exact Or.inl hbc
      | some n =>
        obtain ⟨hle, _, _⟩ := hwf.1 bb bI bA n hbc
        exact Or.inr ⟨bI, bA, n, hbc, lt_of_le_of_ne hle (hfull bb bI bA n hbc)⟩
    by_cases hen : ∃ i e, e < fcut T τ η₁ i ∧ T_C.prog i = (T.prog i).drop e ∧ s.E i = true
    · -- **Case B1**: an enabled `G`-thread can step (read/write/arrive advance; sync parks).
      obtain ⟨i, e, helt, heprog, hen⟩ := hen
      have hi_len : e < (T.prog i).length := lt_of_lt_of_le helt (fcut_le_length T τ η₁ i)
      have hiids : i ∈ T_C.ids := by
        by_contra hni
        have h0 := T_C.nil_outside_ids i hni
        rw [heprog, List.drop_eq_nil_iff] at h0; omega
      have hhead : T_C.prog i = (T.prog i)[e]'hi_len :: (T.prog i).drop (e + 1) := by
        rw [heprog, List.drop_eq_getElem_cons hi_len]
      have gbAdvance : ∀ s', (∀ b'', (s'.B b'').synced = (s.B b'').synced) →
          GBounded T τ η₁ (Config.run s' (T_C.set i hiids ((T.prog i).drop (e + 1)))) := by
        intro s' hsyn
        refine ⟨s', _, rfl, ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst hji; exact ⟨e + 1, by omega, by simp [WeftCommon.CTA.set, Function.update_self]⟩
          · obtain ⟨ej, hjle, hjprog⟩ := hbound j
            exact ⟨ej, hjle, by
              simp only [WeftCommon.CTA.set, Function.update_of_ne hji]; exact hjprog⟩
        · intro b'' j hj
          rw [hsyn] at hj
          have hjnoti : j ≠ i := by
            intro hji; subst hji
            exact absurd hen (by rw [hwf.2.2.2.1 b'' j hj]; simp)
          have hpj := hpurity b'' j hj
          simp only [WeftCommon.CTA.set, Function.update_of_ne hjnoti]; exact hpj
      cases hcmd : (T.prog i)[e]'hi_len with
      | read g =>
        exact ⟨_, CTAStep.interleave hiids hbar (by rw [hhead, hcmd]; exact ThreadStep.read_noop),
          gbAdvance s (fun _ => rfl)⟩
      | write g =>
        exact ⟨_, CTAStep.interleave hiids hbar (by rw [hhead, hcmd]; exact ThreadStep.write_noop),
          gbAdvance s (fun _ => rfl)⟩
      | arrive b n =>
        rcases hbar b with hbu | ⟨I, A, n', hbcfg, hlt⟩
        · refine ⟨_, CTAStep.interleave hiids hbar
            (by rw [hhead, hcmd]; exact ThreadStep.arrive_configure hen hbu), gbAdvance _ ?_⟩
          intro b''
          by_cases hb''b : b'' = b
          · subst hb''b; rw [hbu]; simp [Function.update_self, BarrierState.unconfigured]
          · simp [Function.update_of_ne hb''b]
        · by_cases hn : n = n'
          · subst hn
            have hApos : 0 < I.length + A := (hwf.1 b I A n hbcfg).2.2
            refine ⟨_, CTAStep.interleave hiids hbar
              (by rw [hhead, hcmd]; exact ThreadStep.arrive_register hen hbcfg hApos hlt),
              gbAdvance _ ?_⟩
            intro b''
            by_cases hb''b : b'' = b
            · subst hb''b; rw [hbcfg]; simp [Function.update_self]
            · simp [Function.update_of_ne hb''b]
          · exact absurd ⟨_, CTAStep.error hbar
              (by rw [hhead, hcmd]; exact ThreadStep.arrive_err_count hen hbcfg (Ne.symm hn))⟩
              (no_err_of_reach hws hreach)
      | sync b n =>
        have gbPark : ∀ (s' : State) (T' : CTA), (∀ j, T'.prog j = T_C.prog j) →
            (∀ b'' j, j ∈ (s'.B b'').synced → j = i ∨ j ∈ (s.B b'').synced) →
            GBounded T τ η₁ (Config.run s' T') := by
          intro s' T' hprogeq hsyn
          refine ⟨s', T', rfl, fun j => ?_, ?_⟩
          · obtain ⟨ej, hjle, hjprog⟩ := hbound j
            exact ⟨ej, hjle, by rw [hprogeq]; exact hjprog⟩
          · intro b'' j hj
            rw [hprogeq]
            rcases hsyn b'' j hj with rfl | hjold
            · rw [heprog, List.length_drop]
              have hcl := fcut_le_length T τ η₁ j; omega
            · exact hpurity b'' j hjold
        have hprogeq : ∀ j, (T_C.set i hiids
            (Cmd.sync b n :: (T.prog i).drop (e + 1))).prog j = T_C.prog j := by
          intro j
          by_cases hj : j = i
          · subst hj; simp only [WeftCommon.CTA.set, Function.update_self]; rw [hhead, hcmd]
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hj]
        rcases hbar b with hbu | ⟨I, A, n', hbcfg, hlt⟩
        · refine ⟨_, CTAStep.interleave hiids hbar
            (by rw [hhead, hcmd]; exact ThreadStep.sync_configure hen hbu), gbPark _ _ hprogeq ?_⟩
          intro b'' j hj
          by_cases hb''b : b'' = b
          · subst hb''b
            simp only [Function.update_self, List.mem_singleton] at hj; exact Or.inl hj
          · simp only [Function.update_of_ne hb''b] at hj; exact Or.inr hj
        · by_cases hn : n = n'
          · subst hn
            have hApos : 0 < I.length + A := (hwf.1 b I A n hbcfg).2.2
            refine ⟨_, CTAStep.interleave hiids hbar
              (by rw [hhead, hcmd]; exact ThreadStep.sync_block hen hbcfg hApos hlt),
              gbPark _ _ hprogeq ?_⟩
            intro b'' j hj
            by_cases hb''b : b'' = b
            · subst hb''b
              simp only [Function.update_self, List.mem_cons] at hj
              rcases hj with rfl | hj
              · exact Or.inl rfl
              · exact Or.inr (by rw [hbcfg]; exact hj)
            · simp only [Function.update_of_ne hb''b] at hj; exact Or.inr hj
          · exact absurd ⟨_, CTAStep.error hbar
              (by rw [hhead, hcmd]; exact ThreadStep.sync_err_count hen hbcfg (Ne.symm hn))⟩
              (no_err_of_reach hws hreach)
    · -- **Case B2**: every `G`-thread is parked — impossible by round-purity / deadlock-freedom.
      exfalso
      -- `i₀` is a `G`-thread, so by `hen` it is disabled, hence parked (`EnabledInv`).
      have hi₀dis : s.E i₀ = false := by
        by_contra h
        rw [Bool.not_eq_false] at h
        exact hen ⟨i₀, e₀, hi₀G, he₀prog, h⟩
      obtain ⟨lc, hlchain, hlhd, hllast⟩ := exists_chain_of_reaches hreach
      have hei : ∀ C ∈ lc, ∀ s', C.state? = some s' → s'.EnabledInv :=
        enabledInv_chain hlchain hlhd (by
          intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
          exact State.EnabledInv.initial)
      have hCmem : Config.run s T_C ∈ lc := List.mem_of_mem_getLast? hllast
      obtain ⟨b₁, hi₀b₁⟩ := hei _ hCmem s rfl i₀ hi₀dis
      -- Build the full trace `Σ` from `initial` through `C` to `done` (glue prefix + completion).
      have hbwC : (Config.barriersWithin T.barrierSet (Config.run s T_C)) :=
        barriersWithin_of_reaches hreach
      obtain ⟨σ, hσIC, hσhd⟩ := exists_completeTrace T.barrierSet (Config.run s T_C) hbwC
      obtain ⟨σtail, rfl⟩ : ∃ l, σ = Config.run s T_C :: l := by
        cases σ with
        | nil => simp at hσhd
        | cons a l => simp only [List.head?_cons, Option.some.injEq] at hσhd; exact ⟨l, hσhd ▸ rfl⟩
      have hlne : lc ≠ [] := by intro h; rw [h] at hlhd; simp at hlhd
      have hσchain : List.IsChain CTAStep (Config.run s T_C :: σtail) := hσIC.subtrace
      rw [List.isChain_cons] at hσchain
      set tr := lc ++ σtail with htrdef
      have htrIC : IsCompleteTraceFrom (Config.run State.initial T) tr := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · refine List.IsChain.append hlchain hσchain.2 ?_
          intro x hx y hy
          rw [hllast, Option.mem_some_iff] at hx; subst hx
          exact hσchain.1 y hy
        · obtain ⟨Cₙ, hτlast, hterm⟩ := hσIC.ends
          refine ⟨Cₙ, ?_, hterm⟩
          have hgl : lc.getLast hlne = Config.run s T_C := by
            have h := List.getLast?_eq_some_getLast hlne
            rw [hllast] at h; exact (Option.some.injEq _ _).mp h.symm
          have hsplit : lc ++ σtail = lc.dropLast ++ (Config.run s T_C :: σtail) := by
            conv_lhs => rw [← List.dropLast_concat_getLast hlne, hgl]; simp
          rw [htrdef, hsplit]; exact List.mem_getLast?_append_of_mem_getLast? hτlast
        · rw [htrdef, List.head?_append_of_ne_nil _ hlne]; exact hlhd
      obtain ⟨sdone, htrdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrIC
      -- `C` sits at index `pc := lc.length - 1` of `tr`.
      set pc := lc.length - 1 with hpcdef
      have htrpc : tr[pc]? = some (Config.run s T_C) := by
        rw [htrdef, List.getElem?_append_left (by have := List.length_pos_of_ne_nil hlne; omega),
          ← List.getLast?_eq_getElem?]; exact hllast
      -- `i₀`'s parked command is `sync b₁ n₁`; it executes at some time `m₀` in `tr`.
      have hb₁cfg : ∃ I A n, s.B b₁ = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
        rcases hbar b₁ with h | h
        · rw [h] at hi₀b₁; simp [BarrierState.unconfigured] at hi₀b₁
        · exact h
      obtain ⟨I₁, A₁, n₁, hb₁eq, hb₁lt⟩ := hb₁cfg
      have hi₀head : (T_C.prog i₀).head? = some (Cmd.sync b₁ n₁) :=
        (hwf.1 b₁ I₁ A₁ n₁ hb₁eq).2.1 i₀ (by rw [hb₁eq] at hi₀b₁; exact hi₀b₁)
      have hi₀L : e₀ < (T.prog i₀).length := lt_of_lt_of_le hi₀G (fcut_le_length T τ η₁ i₀)
      have hi₀cmd : (T.prog i₀)[e₀]'hi₀L = Cmd.sync b₁ n₁ := by
        have hdr : T_C.prog i₀ = (T.prog i₀)[e₀]'hi₀L :: (T.prog i₀).drop (e₀ + 1) := by
          rw [he₀prog, List.drop_eq_getElem_cons hi₀L]
        rw [hdr, List.head?_cons, Option.some.injEq] at hi₀head; exact hi₀head
      have hci₀cmd : T.cmdAt (⟨i₀, e₀⟩ : ProgPoint) = some (Cmd.sync b₁ n₁) := by
        simp only [CTA.cmdAt]; rw [List.getElem?_eq_getElem hi₀L, hi₀cmd]
      have hci₀L : (⟨i₀, e₀⟩ : ProgPoint).idx <
          ((Config.run State.initial T).progOf (⟨i₀, e₀⟩ : ProgPoint).thread).length := hi₀L
      obtain ⟨m₀, hm₀⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨i₀, e₀⟩) hci₀L
      have hpcm₀ : pc < m₀ := by
        refine lt_time_of_lt_progOf hm₀ htrpc ?_
        change ((Config.run State.initial T).progOf i₀).length - e₀ - 1 < (T_C.prog i₀).length
        rw [he₀prog, List.length_drop]
        change (T.prog i₀).length - e₀ - 1 < (T.prog i₀).length - e₀
        omega
      -- The step `m₀-1 → m₀` recycles `b₁` (waking `i₀`).
      obtain ⟨Cm, Cm', hCm, hCm', hrecm⟩ := sync_time_recycles hm₀ hci₀cmd
      -- `dw` = first recycle (after `pc`) of a barrier holding a parked-at-`C` thread.
      have hPex : ∃ d, pc ≤ d ∧ ∃ b C C', (s.B b).synced ≠ [] ∧
          tr[d]? = some C ∧ tr[d + 1]? = some C' ∧ stepRecyclesBarrier b C C' = true := by
        refine ⟨m₀ - 1, by omega, b₁, Cm, Cm', ?_, hCm, ?_, hrecm⟩
        · intro h; rw [h] at hi₀b₁; simp at hi₀b₁
        · rw [show m₀ - 1 + 1 = m₀ from by omega]; exact hCm'
      set dw := Nat.find hPex with hdwdef
      obtain ⟨hpcdw, b'', Cd, Cd', hb''ne, hCd, hCd', hrecd⟩ := Nat.find_spec hPex
      -- no barrier-with-a-parked-`C`-thread recycles strictly before `dw`
      have hnorec : ∀ d, pc ≤ d → d < dw → ∀ b, (s.B b).synced ≠ [] → ∀ C C',
          tr[d]? = some C → tr[d + 1]? = some C' → stepRecyclesBarrier b C C' = false := by
        intro d hpcd hddw b hbne C C' hC hC'
        by_contra hrec
        rw [Bool.not_eq_false] at hrec
        exact Nat.find_min hPex hddw ⟨hpcd, b, C, C', hbne, hC, hC', hrec⟩
      -- a concrete parked-at-`C` thread `t''` of `b''`
      obtain ⟨t'', ht''⟩ : ∃ t, t ∈ (s.B b'').synced := by
        rcases h : (s.B b'').synced with _ | ⟨a, l⟩
        · exact absurd h hb''ne
        · exact ⟨a, by simp⟩
      -- `recycleCount b''` is frozen across `[pc, dw]` (no `b''`-recycle there).
      have htrlen : dw + 1 < tr.length := (List.getElem?_eq_some_iff.mp hCd').1
      have htrget : ∀ d, d ≤ dw + 1 → ∃ C, tr[d]? = some C :=
        fun d hd => ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hrcc : ∀ d, pc ≤ d → d ≤ dw → recycleCount b'' tr d = recycleCount b'' tr pc := by
        intro d hpcd
        induction d, hpcd using Nat.le_induction with
        | base => intro _; rfl
        | succ d hpcd ih =>
          intro hsucc
          obtain ⟨Cd0, hCd0⟩ := htrget d (by omega)
          obtain ⟨Cd1, hCd1⟩ := htrget (d + 1) (by omega)
          have hnor := hnorec d hpcd (by omega) b'' hb''ne Cd0 Cd1 hCd0 hCd1
          rw [recycleCount_succ_of_not_recycle b'' hCd0 hCd1 hnor, ih (by omega)]
      -- `BlockInv` on `tr`, and `pointGen = recycleCount` in `tr` (WS transfer).
      have hBItr : ∀ C ∈ tr, ∀ s', C.state? = some s' → s'.BlockInv :=
        blockInv_chain htrIC.1.subtrace htrIC.2 (by
          intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
          exact State.BlockInv.initial)
      have hgenTr : ∀ (c : ProgPoint) (bb : Barrier) (mc : Nat),
          (T.cmdAt c).bind Cmd.barrier? = some bb → c ∈ T.progPoints →
          IsTimeOf (Config.run State.initial T) tr c mc →
          pointGen T τ c = recycleCount bb tr (mc - 1) + 1 := by
        intro c bb mc hcbar hcpt hmc
        obtain ⟨sdτ, hdτ⟩ := hτ.2
        obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdτ ((mem_progPoints_iff T c).mp hcpt).2
        obtain ⟨g, hg1, hg2⟩ := hws.2 τ tr hτ.1 htrIC c ⟨bb, hcbar⟩
        rw [IsGenOf.unique hg1 (isGenOf_pointGen hcbar hmτ)] at hg2
        exact isGenOf_recycleCount hg2 hcbar hmc
      -- `c_{t''} = ⟨t'', et⟩`, a `sync` on `b''`, with generation `= recycleCount b'' tr pc + 1`.
      obtain ⟨I₂, A₂, n₂, hb''eq, hb''lt⟩ :
          ∃ I A n, s.B b'' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
        rcases hbar b'' with h | h
        · rw [h] at ht''; simp [BarrierState.unconfigured] at ht''
        · exact h
      obtain ⟨et, hetle, hetprog⟩ := hbound t''
      have hetG : et < fcut T τ η₁ t'' := by
        have hp := hpurity b'' t'' ht''
        rw [hetprog, List.length_drop] at hp
        have := fcut_le_length T τ η₁ t''; omega
      have htL : et < (T.prog t'').length := lt_of_lt_of_le hetG (fcut_le_length T τ η₁ t'')
      have hthead : (T_C.prog t'').head? = some (Cmd.sync b'' n₂) :=
        (hwf.1 b'' I₂ A₂ n₂ hb''eq).2.1 t'' (by rw [hb''eq] at ht''; exact ht'')
      have htcmd : (T.prog t'')[et]'htL = Cmd.sync b'' n₂ := by
        have hdr : T_C.prog t'' = (T.prog t'')[et]'htL :: (T.prog t'').drop (et + 1) := by
          rw [hetprog, List.drop_eq_getElem_cons htL]
        rw [hdr, List.head?_cons, Option.some.injEq] at hthead; exact hthead
      have hctcmd : T.cmdAt (⟨t'', et⟩ : ProgPoint) = some (Cmd.sync b'' n₂) := by
        simp only [CTA.cmdAt]; rw [List.getElem?_eq_getElem htL, htcmd]
      have hctbar : (T.cmdAt (⟨t'', et⟩ : ProgPoint)).bind Cmd.barrier? = some b'' := by
        rw [hctcmd]; rfl
      have hctpt : (⟨t'', et⟩ : ProgPoint) ∈ T.progPoints := mem_progPoints_of_cmdAt T hctcmd
      obtain ⟨mt, hmt⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨t'', et⟩)
        (show et < ((Config.run State.initial T).progOf t'').length from htL)
      have hpcmt : pc < mt := by
        refine lt_time_of_lt_progOf hmt htrpc ?_
        change ((Config.run State.initial T).progOf t'').length - et - 1 < (T_C.prog t'').length
        rw [hetprog, List.length_drop]
        change (T.prog t'').length - et - 1 < (T.prog t'').length - et
        omega
      have hrct'' : recycleCount b'' tr (mt - 1) = recycleCount b'' tr pc :=
        parked_sync_recycleCount hBItr rfl hmt htrpc ht'' hetprog hpcmt
      have hgent'' : pointGen T τ (⟨t'', et⟩ : ProgPoint) = recycleCount b'' tr pc + 1 := by
        rw [hgenTr _ b'' mt hctbar hctpt hmt, hrct'']
      -- Every config in `[pc, dw]` is a `run`, and a parked-at-`C` thread stays synced there.
      have hrunC : ∀ d, pc ≤ d → d ≤ dw → ∃ sd Td, tr[d]? = some (Config.run sd Td) := by
        intro d hpcd hddw
        obtain ⟨C, hC⟩ := htrget d (by omega)
        obtain ⟨Cn, hCn⟩ := htrget (d + 1) (by omega)
        have hstep := chain_step htrIC.1.subtrace hC hCn
        obtain ⟨sd, Td, rfl⟩ : ∃ sd Td, C = Config.run sd Td := by cases hstep <;> exact ⟨_, _, rfl⟩
        exact ⟨sd, Td, hC⟩
      have hpers : ∀ (b : Barrier) (t : ThreadId), t ∈ (s.B b).synced →
          ∀ d, pc ≤ d → d ≤ dw → ∀ sd Td, tr[d]? = some (Config.run sd Td) →
          t ∈ (sd.B b).synced := by
        intro b t ht d hpcd
        induction d, hpcd using Nat.le_induction with
        | base =>
          intro _ sd Td hsd
          rw [htrpc, Option.some.injEq, Config.run.injEq] at hsd
          obtain ⟨rfl, rfl⟩ := hsd; exact ht
        | succ d hpcd ih =>
          intro hd1dw sd' Td' hsd'
          obtain ⟨sd, Td, hsd⟩ := hrunC d hpcd (by omega)
          have htd : t ∈ (sd.B b).synced := ih (by omega) sd Td hsd
          have hbne : (s.B b).synced ≠ [] := fun h => by rw [h] at ht; exact absurd ht (by simp)
          have hstep := chain_step htrIC.1.subtrace hsd hsd'
          exact synced_persists hstep rfl (hBItr _ (List.mem_of_getElem? hsd) sd rfl) htd
            (hnorec d hpcd (by omega) b hbne _ _ hsd hsd') rfl
      -- The `count` field of `b''` is frozen across `[pc, dw]`, so its capacity stays `n₂`.
      have hcount_step : ∀ {C C' : Config}, CTAStep C C' → ∀ {sa : State}, C.state? = some sa →
          ∀ {nc : ℕ+}, (sa.B b'').count = some nc → stepRecyclesBarrier b'' C C' = false →
          ∀ {sa' : State}, C'.state? = some sa' → (sa'.B b'').count = some nc := by
        intro C C' hstep sa hCs nc hcnt hnorec sa' hCs'
        cases hstep with
        | @interleave s₀ s'' T i P' hi hbar hth =>
          simp only [Config.state?, Option.some.injEq] at hCs hCs'
          subst hCs; subst hCs'
          generalize hpi : T.prog i = Pi at hth
          cases hth with
          | read_noop => exact hcnt
          | write_noop => exact hcnt
          | arrive_configure he hb0 =>
            rename_i b₀ nn
            by_cases hbb : b'' = b₀
            · subst hbb; rw [hb0] at hcnt; simp [BarrierState.unconfigured] at hcnt
            · simpa only [Function.update_of_ne hbb] using hcnt
          | arrive_register he hb0 hpos hlt =>
            rename_i b₀ nn I A
            by_cases hbb : b'' = b₀
            · subst hbb; simp only [Function.update_self]; rw [hb0] at hcnt; exact hcnt
            · simpa only [Function.update_of_ne hbb] using hcnt
          | sync_configure he hb0 =>
            rename_i b₀ nn c
            by_cases hbb : b'' = b₀
            · subst hbb; rw [hb0] at hcnt; simp [BarrierState.unconfigured] at hcnt
            · simpa only [Function.update_of_ne hbb] using hcnt
          | sync_block he hb0 hpos hlt =>
            rename_i b₀ nn c I A
            by_cases hbb : b'' = b₀
            · subst hbb; simp only [Function.update_self]; rw [hb0] at hcnt; exact hcnt
            · simpa only [Function.update_of_ne hbb] using hcnt
        | @recycle s₀ T b₀ I A n hb hfull hpark =>
          simp only [Config.state?, Option.some.injEq] at hCs hCs'
          subst hCs; subst hCs'
          by_cases hbb : b'' = b₀
          · subst hbb; exfalso; revert hnorec
            simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
              Function.update_self, BarrierState.unconfigured]
          · simpa only [Function.update_of_ne hbb] using hcnt
        | @done s₀ T hdone hnofull =>
          simp only [Config.state?, Option.some.injEq] at hCs hCs'
          subst hCs; subst hCs'; exact hcnt
        | @error s₀ T i P' _ hth => exact absurd hCs' (by simp [Config.state?])
      have hcountconst : ∀ d, pc ≤ d → d ≤ dw → ∀ sd Td, tr[d]? = some (Config.run sd Td) →
          (sd.B b'').count = some n₂ := by
        intro d hpcd
        induction d, hpcd using Nat.le_induction with
        | base =>
          intro _ sd Td hsd
          rw [htrpc, Option.some.injEq, Config.run.injEq] at hsd
          obtain ⟨rfl, rfl⟩ := hsd; rw [hb''eq]
        | succ d hpcd ih =>
          intro hd1dw sd' Td' hsd'
          obtain ⟨sd, Td, hsd⟩ := hrunC d hpcd (by omega)
          have hstep := chain_step htrIC.1.subtrace hsd hsd'
          exact hcount_step hstep rfl (ih (by omega) sd Td hsd)
            (hnorec d hpcd (by omega) b'' hb''ne _ _ hsd hsd') rfl
      -- `b''` is full at `dw` (`synced + arrived = n₂`), but under-full at `pc`.
      obtain ⟨sdw, Tdw, hsdw⟩ := hrunC dw hpcdw le_rfl
      have hCdeq : Cd = Config.run sdw Tdw := Option.some_injective _ (hCd.symm.trans hsdw)
      have hfullaux : ∀ {C C' : Config} {b : Barrier} {sc : State}, C.state? = some sc →
          stepRecyclesBarrier b C C' = true → (sc.B b).isFull = true := by
        intro C C' b sc hsc hrec
        rcases hc' : C'.state? with _ | sc'
        · simp [stepRecyclesBarrier, hsc, hc'] at hrec
        · simp only [stepRecyclesBarrier, hsc, hc', Bool.and_eq_true] at hrec; exact hrec.1
      have hfulldw : (sdw.B b'').synced.length + (sdw.B b'').arrived = (n₂ : Nat) := by
        have hcnt := hcountconst dw hpcdw le_rfl sdw Tdw hsdw
        have hisfull := hfullaux (C := Config.run sdw Tdw) rfl (hCdeq ▸ hrecd)
        simp only [BarrierState.isFull, hcnt, beq_iff_eq] at hisfull
        exact hisfull
      -- Hence some step in `[pc, dw)` increases `b''`'s registration count.
      have hinc : ∃ d sd Td sd' Td', pc ≤ d ∧ d < dw ∧ tr[d]? = some (Config.run sd Td) ∧
          tr[d + 1]? = some (Config.run sd' Td') ∧
          (sd.B b'').synced.length + (sd.B b'').arrived <
            (sd'.B b'').synced.length + (sd'.B b'').arrived := by
        by_contra hcon
        push Not at hcon
        have hmono : ∀ e, pc ≤ e → e ≤ dw → ∀ se Te, tr[e]? = some (Config.run se Te) →
            (se.B b'').synced.length + (se.B b'').arrived ≤
              (s.B b'').synced.length + (s.B b'').arrived := by
          intro e hpce
          induction e, hpce using Nat.le_induction with
          | base =>
            intro _ se Te hse
            rw [htrpc, Option.some.injEq, Config.run.injEq] at hse
            obtain ⟨rfl, rfl⟩ := hse; exact le_rfl
          | succ e hpce ih =>
            intro he1 se' Te' hse'
            obtain ⟨se, Te, hse⟩ := hrunC e hpce (by omega)
            exact le_trans (hcon e se Te se' Te' hpce (by omega) hse hse') (ih (by omega) se Te hse)
        have hdwle := hmono dw hpcdw le_rfl sdw Tdw hsdw
        rw [hb''eq] at hdwle
        simp only [hfulldw] at hdwle
        omega
      obtain ⟨d, sd, Td, sd', Td', hpcd, hd_dw, hsd, hsd', hcntlt⟩ := hinc
      have htr0 : tr[0]? = some (Config.run State.initial T) := by
        rw [← List.head?_eq_getElem?]; exact htrIC.2
      -- A thread registering a `b''`-op (of `b''`'s round generation) at config `d`, while
      -- enabled, would be a frozen `G`-thread — impossible.
      have hregfalse : ∀ (i : ThreadId) (ed : Nat),
          (T.cmdAt (⟨i, ed⟩ : ProgPoint) = some (Cmd.arrive b'' n₂) ∨
            T.cmdAt (⟨i, ed⟩ : ProgPoint) = some (Cmd.sync b'' n₂)) →
          pointGen T τ (⟨i, ed⟩ : ProgPoint) = recycleCount b'' tr pc + 1 →
          Td.prog i = (T.prog i).drop ed → sd.E i = true → False := by
        intro i ed hcicmd hgenci hedprog hien
        have hcipt : (⟨i, ed⟩ : ProgPoint) ∈ T.progPoints := by
          rcases hcicmd with h | h <;> exact mem_progPoints_of_cmdAt T h
        have hedge : (⟨i, ed⟩, (⟨t'', et⟩ : ProgPoint)) ∈ initRelation T τ := by
          rw [mem_initRelation_iff]
          rcases hcicmd with h | h
          · exact Or.inr (Or.inl ⟨b'', n₂, hcipt, hctpt, h, hctcmd, by rw [hgenci, hgent'']⟩)
          · exact Or.inr (Or.inr ⟨b'', n₂, hcipt, hctpt, h, hctcmd, by rw [hgenci, hgent'']⟩)
        have hnotht : ¬ happensBefore T τ η₁ (⟨t'', et⟩ : ProgPoint) := fun hhb =>
          absurd (fcut_le_of_hb hhb hctpt) (not_le.mpr hetG)
        have hnothi : ¬ happensBefore T τ η₁ (⟨i, ed⟩ : ProgPoint) := fun hhb =>
          hnotht (hhb.trans (Relation.ReflTransGen.single hedge))
        have hedfcut : ed < fcut T τ η₁ i := lt_fcut_of_not_hb hnothi hcipt
        obtain ⟨ep, heple, hepprog⟩ := hbound i
        have hsuf : (Config.run sd Td).progOf i <:+ (Config.run s T_C).progOf i :=
          progOf_suffix_index_le htrIC.1.subtrace i htrpc hpcd hsd
        have hepled : ep ≤ ed := by
          have hle : (Td.prog i).length ≤ (T_C.prog i).length := suffix_length_le hsuf
          rw [hedprog, hepprog, List.length_drop, List.length_drop] at hle
          have hedlen : ed ≤ (T.prog i).length :=
            le_of_lt (lt_of_lt_of_le hedfcut (fcut_le_length _ _ _ _))
          have heplen : ep ≤ (T.prog i).length := le_trans heple (fcut_le_length _ _ _ _)
          omega
        have hepfcut : ep < fcut T τ η₁ i := lt_of_le_of_lt hepled hedfcut
        have hidisC : s.E i = false := by
          by_contra h; rw [Bool.not_eq_false] at h
          exact hen ⟨i, ep, hepfcut, hepprog, h⟩
        obtain ⟨bi, hibi⟩ := hei (Config.run s T_C) hCmem s rfl i hidisC
        have hidsync : i ∈ (sd.B bi).synced := hpers bi i hibi d hpcd (le_of_lt hd_dw) sd Td hsd
        have hidisd : sd.E i = false :=
          (hBItr (Config.run sd Td) (List.mem_of_getElem? hsd) sd rfl).2.1 bi i hidsync
        rw [hien] at hidisd; exact absurd hidisd (by decide)
      -- A count-increasing step at `d` must register into `b''`; analyse it.
      have hstepd := chain_step htrIC.1.subtrace hsd hsd'
      cases hstepd with
      | @interleave s₀ s₀' T₀ ii P' hii hbar hth =>
        generalize hpi : Td.prog ii = Pi at hth
        cases hth with
        | read_noop => omega
        | write_noop => omega
        | @arrive_configure _ _ b₀ nn c he hb0 =>
          by_cases hbb : b'' = b₀
          · subst hbb
            have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
            rw [hb0] at hc; simp [BarrierState.unconfigured] at hc
          · simp only [Function.update_of_ne hbb] at hcntlt; omega
        | @sync_configure _ _ b₀ nn c he hb0 =>
          by_cases hbb : b'' = b₀
          · subst hbb
            have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
            rw [hb0] at hc; simp [BarrierState.unconfigured] at hc
          · simp only [Function.update_of_ne hbb] at hcntlt; omega
        | @arrive_register _ _ b₀ nn _ I A he hb0 hpos hlt =>
          by_cases hbb : b'' = b₀
          · subst hbb
            have hsuf0 := progOf_suffix_index_le htrIC.1.subtrace ii htr0 (Nat.zero_le d) hsd
            have hedprog :
                Td.prog ii = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) :=
              List.IsSuffix.eq_drop hsuf0
            have hn2 : nn = n₂ := by
              have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
              rw [hb0] at hc; exact Option.some.inj hc
            subst hn2
            have hcicmd : T.cmdAt (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) =
                some (Cmd.arrive b'' nn) := cmd_at_last hsuf0 hpi
            have htdlen : 0 < (Td.prog ii).length := by rw [hpi]; simp
            have hsuflen : (Td.prog ii).length ≤ (T.prog ii).length := suffix_length_le hsuf0
            have hLcfg : (T.prog ii).length - (Td.prog ii).length < (T.prog ii).length := by omega
            have hC'eq : (Td.set ii hii P').prog ii =
                (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length + 1) := by
              simp only [WeftCommon.CTA.set, Function.update_self]
              rw [← List.drop_drop, ← hedprog, hpi, List.drop_one, List.tail_cons]
            have hmi : IsTimeOf (Config.run State.initial T) tr
                (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) (d + 1) :=
              ⟨htrIC, hLcfg, d, _, _, rfl, hsd, hsd', hedprog, hC'eq⟩
            have hgenci :
                pointGen T τ (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) =
                recycleCount b'' tr pc + 1 := by
              rw [hgenTr _ b'' (d + 1) (by rw [hcicmd]; rfl)
                (mem_progPoints_of_cmdAt T hcicmd) hmi, Nat.add_sub_cancel,
                hrcc d hpcd (le_of_lt hd_dw)]
            exact hregfalse ii _ (Or.inl hcicmd) hgenci hedprog he
          · simp only [Function.update_of_ne hbb] at hcntlt; omega
        | @sync_block _ _ b₀ nn c I A he hb0 hpos hlt =>
          by_cases hbb : b'' = b₀
          · subst hbb
            have hsuf0 := progOf_suffix_index_le htrIC.1.subtrace ii htr0 (Nat.zero_le d) hsd
            have hedprog :
                Td.prog ii = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) :=
              List.IsSuffix.eq_drop hsuf0
            have hn2 : nn = n₂ := by
              have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
              rw [hb0] at hc; exact Option.some.inj hc
            subst hn2
            have hcicmd : T.cmdAt (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) =
                some (Cmd.sync b'' nn) := cmd_at_last hsuf0 hpi
            have hii_syncd :
                ii ∈ ((Function.update sd.B b'' ⟨ii :: I, A, some nn⟩) b'').synced := by
              rw [Function.update_self]; exact List.mem_cons_self
            have hprog' : (Td.set ii hii (Cmd.sync b'' nn :: c)).prog ii =
                (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) := by
              rw [← hedprog]; simp only [WeftCommon.CTA.set, Function.update_self]; exact hpi.symm
            have htdlen : 0 < (Td.prog ii).length := by rw [hpi]; simp
            have hsuflen : (Td.prog ii).length ≤ (T.prog ii).length := suffix_length_le hsuf0
            have hLcfg : (T.prog ii).length - (Td.prog ii).length < (T.prog ii).length := by omega
            obtain ⟨mi, hmi⟩ := exists_time_of_ends_done htrIC htrdone
              (η := ⟨ii, (T.prog ii).length - (Td.prog ii).length⟩) hLcfg
            have hd1mi : d + 1 < mi := by
              refine lt_time_of_lt_progOf hmi hsd' ?_
              change ((Config.run State.initial T).progOf ii).length -
                  ((T.prog ii).length - (Td.prog ii).length) - 1 <
                  ((Td.set ii hii (Cmd.sync b'' nn :: c)).prog ii).length
              rw [hprog', List.length_drop]
              change (T.prog ii).length - ((T.prog ii).length - (Td.prog ii).length) - 1 <
                (T.prog ii).length - ((T.prog ii).length - (Td.prog ii).length)
              omega
            have hrcmi : recycleCount b'' tr (mi - 1) = recycleCount b'' tr pc := by
              rw [parked_sync_recycleCount hBItr rfl hmi hsd' hii_syncd hprog' hd1mi,
                hrcc (d + 1) (by omega) (by omega)]
            have hgenci :
                pointGen T τ (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) =
                recycleCount b'' tr pc + 1 := by
              rw [hgenTr _ b'' mi (by rw [hcicmd]; rfl) (mem_progPoints_of_cmdAt T hcicmd) hmi,
                hrcmi]
            exact hregfalse ii _ (Or.inr hcicmd) hgenci hedprog he
          · simp only [Function.update_of_ne hbb] at hcntlt; omega
      | @recycle s₀ T₀ b₀ I A nn hb hfull hpark =>
        by_cases hbb : b'' = b₀
        · subst hbb
          simp only [Function.update_self, BarrierState.unconfigured] at hcntlt; simp at hcntlt
        · simp only [Function.update_of_ne hbb] at hcntlt; omega


/-- Run `G` to the cut configuration: from any reachable `G`-bounded `C`, there is a
chain (executing only `G`-steps) to a configuration whose every thread sits exactly at
its cut. By well-founded recursion on `cfgMeasure`, taking a `G`-step (`gstep`) until
`G` is exhausted. -/
theorem reach_cut_aux {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized) :
    ∀ n, ∀ C, GBounded T τ η₁ C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C →
      C.cfgMeasure T.barrierSet = n →
      ∃ (pre : List Config) (s_G : State) (T_G : CTA),
        pre.head? = some C ∧ List.IsChain CTAStep pre ∧
        pre.getLast? = some (Config.run s_G T_G) ∧
        (∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i)) ∧
        Relation.ReflTransGen CTAStep (Config.run State.initial T) (Config.run s_G T_G) ∧
        (∀ b i, i ∉ (s_G.B b).synced) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hGB hreach hmeas
    by_cases hdone : Gdone T τ η₁ C
    · -- cut configuration reached
      obtain ⟨s, T_C, rfl, he, hpure⟩ := hGB
      refine ⟨[Config.run s T_C], s, T_C, rfl, List.isChain_singleton _, rfl, fun i => ?_, hreach,
        fun b i hmem => ?_⟩
      · obtain ⟨e, hele, hprog⟩ := he i
        by_cases hi : i ∈ T.ids
        · have hd := hdone i hi
          simp only [WeftCommon.Config.progOf] at hd
          rw [hprog, List.length_drop] at hd
          have hcl := fcut_le_length T τ η₁ i
          rw [hprog, show e = fcut T τ η₁ i by omega]
        · rw [hprog, T.nil_outside_ids i hi]; simp
      · -- synced empty: barrier purity contradicts the cut's exact `fcut` execution
        have hp := hpure b i hmem
        obtain ⟨e, hele, hprog⟩ := he i
        have heq : (T.prog i).length - (T_C.prog i).length = fcut T τ η₁ i := by
          by_cases hi : i ∈ T.ids
          · have hd := hdone i hi
            simp only [WeftCommon.Config.progOf] at hd
            rw [hprog, List.length_drop] at hd ⊢
            have hcl := fcut_le_length T τ η₁ i
            omega
          · have hnil := T.nil_outside_ids i hi
            have h0 : fcut T τ η₁ i = 0 := by
              have := fcut_le_length T τ η₁ i; rw [hnil] at this; simpa using this
            simp [hprog, hnil, h0]
        omega
    · -- progress: take a `G`-step and recurse
      obtain ⟨C', hstep, hGB'⟩ := gstep hτ hws hGB hreach hdone
      have hbw : C.barriersWithin T.barrierSet := barriersWithin_of_reaches hreach
      have hlt : C'.cfgMeasure T.barrierSet < n := by
        rw [← hmeas]; exact step_decreases T.barrierSet hstep hbw
      obtain ⟨pre', s_G, T_G, hhd', hch', hlast', hcut', hreach', hsempty⟩ :=
        ih _ hlt C' hGB' (hreach.tail hstep) rfl
      have hpne : pre' ≠ [] := by intro h; rw [h] at hhd'; simp at hhd'
      refine ⟨C :: pre', s_G, T_G, rfl, ?_, ?_, hcut', hreach', hsempty⟩
      · rw [List.isChain_cons]
        exact ⟨fun y hy => by rw [hhd', Option.mem_some_iff] at hy; exact hy ▸ hstep, hch'⟩
      · rw [List.getLast?_cons_of_ne_nil hpne]; exact hlast'


/-- **Run the ideal `G` first.** There is a complete trace `τ'` from `(I, T)` and a
configuration index `p` at which *exactly* the ideal `G` has executed — every thread's
remaining program is `T`'s with its `fcut`-prefix dropped. (This is the operational
core: the schedule runs all `G`-commands, reaching a clean cut configuration, before
running any `F`-command.) -/
theorem run_ideal {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized) :
    ∃ (τ' : List Config) (p : Nat) (s_G : State) (T_G : CTA),
      IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      τ'[p]? = some (Config.run s_G T_G) ∧
      (∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i)) ∧
      (∀ b i, i ∉ (s_G.B b).synced) := by
  -- run `G` to the cut config `C_G`
  obtain ⟨pre, s_G, T_G, hhd, hch, hlast, hcut, hreachG, hsempty⟩ :=
    reach_cut_aux hτ hws ((Config.cfgMeasure T.barrierSet (Config.run State.initial T)))
      (Config.run State.initial T) (GBounded_init T τ η₁) Relation.ReflTransGen.refl rfl
  have hpne : pre ≠ [] := by intro h; rw [h] at hhd; simp at hhd
  have hpos : 0 < pre.length := List.length_pos_of_ne_nil hpne
  have hgl : pre.getLast hpne = Config.run s_G T_G := by
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h; exact (Option.some.injEq _ _).mp h.symm
  -- `C_G` is reachable, so it satisfies the support invariant; complete from it.
  have hbwG : (Config.barriersWithin T.barrierSet (Config.run s_G T_G)) :=
    barriersWithin_of_reaches hreachG
  obtain ⟨σ, hσIC, hσhead⟩ := exists_completeTrace T.barrierSet (Config.run s_G T_G) hbwG
  obtain ⟨σtail, rfl⟩ : ∃ l, σ = Config.run s_G T_G :: l := by
    cases σ with
    | nil => simp at hσhead
    | cons a l => simp only [List.head?_cons, Option.some.injEq] at hσhead; exact ⟨l, hσhead ▸ rfl⟩
  have hσchain : List.IsChain CTAStep (Config.run s_G T_G :: σtail) := hσIC.subtrace
  rw [List.isChain_cons] at hσchain
  -- glue: `τ' = pre ++ σtail`, with `C_G` at index `pre.length - 1`
  refine ⟨pre ++ σtail, pre.length - 1, s_G, T_G, ⟨⟨?_, ?_⟩, ?_⟩, ?_, hcut, hsempty⟩
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

The contrapositive wrapper (`happensBefore_precise`,
different-threads case) is complete. -/
theorem exists_reversing_trace {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {η₁ η₂ : ProgPoint} (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hcon : ¬ happensBefore T τ η₁ η₂) :
    ∃ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      ∃ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ ∧
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ ∧ n₂ < n₁ := by
  -- Run `G` first: a complete trace `τ'` and a cut index `p` where exactly `G` is done.
  obtain ⟨τ', p, s_G, T_G, hcomp, hpcfg, hGdone, _⟩ := run_ideal (T := T) (τ := τ) (η₁ := η₁) hτ hws
  -- The trace ends in `done`, so both (valid) points execute.
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hv₁L : η₁.idx < (T.prog η₁.thread).length := ((mem_progPoints_iff T η₁).mp hv₁).2
  have hv₂L : η₂.idx < (T.prog η₂.thread).length := ((mem_progPoints_iff T η₂).mp hv₂).2
  obtain ⟨n₁, ht₁⟩ := exists_time_of_ends_done hcomp hdone (η := η₁) hv₁L
  obtain ⟨n₂, ht₂⟩ := exists_time_of_ends_done hcomp hdone (η := η₂) hv₂L
  refine ⟨τ', hcomp, n₁, n₂, ht₁, ht₂, ?_⟩
  have hcut₁ : fcut T τ η₁ η₁.thread ≤ η₁.idx := fcut_le_of_hb Relation.ReflTransGen.refl hv₁
  have hcut₂ : η₂.idx < fcut T τ η₁ η₂.thread := lt_fcut_of_not_hb hcon hv₂
  -- `η₂ ∈ G` is already executed at `p` ⟹ `n₂ ≤ p`.
  have hn₂ : n₂ ≤ p := by
    refine time_le_of_progOf_le ht₂ hpcfg ?_
    change (T_G.prog η₂.thread).length ≤ _
    rw [hGdone η₂.thread, List.length_drop]
    change _ ≤ (T.prog η₂.thread).length - η₂.idx - 1
    omega
  -- `η₁ ∈ F` is not yet executed at `p` ⟹ `p < n₁`.
  have hn₁ : p < n₁ := by
    refine lt_time_of_lt_progOf ht₁ hpcfg ?_
    change ((Config.run State.initial T).progOf η₁.thread).length - η₁.idx - 1 <
      (T_G.prog η₁.thread).length
    rw [hGdone η₁.thread, List.length_drop]
    change (T.prog η₁.thread).length - η₁.idx - 1 <
      (T.prog η₁.thread).length - fcut T τ η₁ η₁.thread
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
  imposes).
NOTE (rohany): This is a top-level theorem. -/
theorem happensBefore_precise {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hle : ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :
    happensBefore T τ η₁ η₂ := by
  by_cases hη : η₁ = η₂
  · -- reflexive corner: every point is happens-before itself
    subst hη; exact Relation.ReflTransGen.refl
  · by_cases hthread : η₁.thread = η₂.thread
    · -- same thread: forced order is program order
      obtain ⟨i₁, k₁⟩ := η₁
      obtain ⟨i₂, k₂⟩ := η₂
      replace hthread : i₁ = i₂ := hthread
      subst hthread
      replace hη : k₁ ≠ k₂ := fun h => hη (by rw [h])
      obtain ⟨hcomplete, sd, hdone⟩ := hτ
      obtain ⟨n₁, ht₁⟩ :=
        exists_time_of_ends_done hcomplete hdone ((mem_progPoints_iff T _).mp hv₁).2
      obtain ⟨n₂, ht₂⟩ :=
        exists_time_of_ends_done hcomplete hdone ((mem_progPoints_iff T _).mp hv₂).2
      have hn : n₁ ≤ n₂ := hle τ hcomplete n₁ n₂ ht₁ ht₂
      have hidx : k₁ < k₂ := by
        rcases Nat.lt_trichotomy k₁ k₂ with h | h | h
        · exact h
        · exact absurd h hη
        · exact absurd (time_lt_of_idx_lt ht₂ ht₁ rfl h) (by omega)
      exact progOrder_happensBefore (le_of_lt hidx) ((mem_progPoints_iff T _).mp hv₂).2
    · -- different threads: contrapositive via the reversing-schedule lemma
      by_contra hcon
      obtain ⟨τ', hτ'c, n₁, n₂, ht₁, ht₂, hlt⟩ := exists_reversing_trace hτ hws hv₁ hv₂ hcon
      exact absurd (hle τ' hτ'c n₁ n₂ ht₁ ht₂) (by omega)

/-- **Lemma 1.** For a well-synchronized configuration `(I, T)`, the static
happens-before relation constructed in Figure 4 — `happensBefore T τ`, the
reflexive-transitive closure of `initRelation T τ` — is sound and precise in the
sense of Definition 4 (`Weft.SoundAndPrecise`), **on program points**.

The valid-point restriction (`η₁ η₂ ∈ T.progPoints`) is required: the unrestricted
`SoundAndPrecise` is false, because for a never-executing point the timing side is
vacuously true while `happensBefore` cannot relate it (see `happensBefore_precise`).
Assembled from the two directions `happensBefore_sound` and `happensBefore_precise`.

Implementation of the top-level `Weft.soundAndPrecise_happensBefore` (in `Weft.lean`). -/
theorem soundAndPrecise_happensBefore_impl {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    ∀ η₁ η₂ : ProgPoint, η₁ ∈ T.progPoints → η₂ ∈ T.progPoints →
      (happensBefore T τ η₁ η₂ ↔
        ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
          ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
            IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) := by
  intro η₁ η₂ hv₁ hv₂
  exact ⟨happensBefore_sound hτ hws, happensBefore_precise hτ hws hv₁ hv₂⟩

/-! ### Pieces of the completeness proof (Theorem 2)

These support `not_wellSynchronized_of_check_false` below. -/

/-- **`Finset` non-membership ⇒ no `happensBefore`** (uses Pillar A, the `transClosure`
converse). If `a ≠ b` and the algorithm's relation does not contain `(a, b)`, then `a`
does not happen-before `b`. -/
theorem not_happensBefore_of_not_mem {T : CTA} {τ : List Config} {a b : ProgPoint}
    (hne : a ≠ b) (hnotmem : (a, b) ∉ (CheckWellSynchronized T τ).2) :
    ¬ happensBefore T τ a b := by
  intro hhb
  apply hnotmem
  rw [snd_checkWellSynchronized]
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hhb with heq | htg
  · exact absurd heq.symm hne
  · exact mem_transClosure_of_transGen (initRelation T τ) hne htg

/-- **Generation contradiction** (the heart of completeness, the paper's argument). In a
well-synchronized CTA, two barrier operations `c1, ca` on the same barrier `b` whose
generations differ by one (`ca` is one *higher*) must be ordered `c1` before `ca`: if not
(`¬ happensBefore c1 ca`), the realizability lemma `exists_reversing_trace` produces a
complete trace running `ca` *before* `c1`, where `ca` would see strictly fewer recyclings
of `b`, hence generation `≤ G(c1) < G(ca)` — contradicting the schedule-independence of
generations (`hws`). -/
theorem reverse_barrier_contradiction {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 ca : ProgPoint} {b : Barrier}
    (hc1 : c1 ∈ T.progPoints) (hca : ca ∈ T.progPoints)
    (hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b)
    (hcabar : (T.cmdAt ca).bind Cmd.barrier? = some b)
    (hgen : pointGen T τ ca = pointGen T τ c1 + 1)
    (hnothb : ¬ happensBefore T τ c1 ca) : False := by
  obtain ⟨τ', hτ'c, n1, n2, ht1, ht2, hlt⟩ := exists_reversing_trace hτ hws hc1 hca hnothb
  obtain ⟨sd, hdone⟩ := hτ.2
  obtain ⟨m1, hm1⟩ := exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨m2, hm2⟩ := exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T ca).mp hca).2
  have hgenc1 : IsGenOf (Config.run State.initial T) τ c1 (some (pointGen T τ c1)) :=
    isGenOf_pointGen hc1bar hm1
  have hgenca : IsGenOf (Config.run State.initial T) τ ca (some (pointGen T τ ca)) :=
    isGenOf_pointGen hcabar hm2
  obtain ⟨g1, hg1τ, hg1τ'⟩ := hws.2 τ τ' hτ.1 hτ'c c1 ⟨b, hc1bar⟩
  obtain ⟨g2, hg2τ, hg2τ'⟩ := hws.2 τ τ' hτ.1 hτ'c ca ⟨b, hcabar⟩
  rw [IsGenOf.unique hg1τ hgenc1] at hg1τ'
  rw [IsGenOf.unique hg2τ hgenca] at hg2τ'
  have hr1 : pointGen T τ c1 = recycleCount b τ' (n1 - 1) + 1 :=
    isGenOf_recycleCount hg1τ' hc1bar ht1
  have hr2 : pointGen T τ ca = recycleCount b τ' (n2 - 1) + 1 :=
    isGenOf_recycleCount hg2τ' hcabar ht2
  have hmono : recycleCount b τ' (n2 - 1) ≤ recycleCount b τ' (n1 - 1) :=
    recycleCount_mono b τ' (by omega)
  omega

/-- A `sync` program point has a `self-loop` in `initRelation` (the `sync ↔ sync` clause of
Figure 4 lines 12–16, taken with both endpoints equal: same barrier, same `n`, same
generation). Used to rule out the diagonal in the completeness extraction. -/
theorem mem_initRelation_syncSelf {T : CTA} {τ : List Config} {c : ProgPoint}
    {b : Barrier} {n : ℕ+} (hc : c ∈ T.progPoints) (hcmd : T.cmdAt c = some (.sync b n)) :
    (c, c) ∈ initRelation T τ := by
  simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨c, hc, ?_⟩
  simp only [hcmd, List.mem_flatMap]
  exact ⟨c, hc, by simp [hcmd]⟩

/-- **Only program order enters an `arrive`.** If `c2` is an `arrive` and `c1`
happens-before `c2`, then either `c1 = c2` or `c1` already happens-before `c2`'s in-thread
predecessor — because the *only* `initRelation` edge into an `arrive` is the program-order
edge from its predecessor (every barrier edge of Figure 4 targets a `sync`,
`initRelation_cases`). -/
theorem happensBefore_arrive {T : CTA} {τ : List Config} {c1 c2 : ProgPoint}
    {b : Barrier} {m : ℕ+} (hc2 : T.cmdAt c2 = some (.arrive b m)) (hidx : 1 ≤ c2.idx)
    (h : happensBefore T τ c1 c2) :
    c1 = c2 ∨ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ := by
  rw [happensBefore] at h
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨d, hd, hdc2⟩
  · exact Or.inl heq.symm
  · refine Or.inr ?_
    obtain ⟨_, _, hcase⟩ := initRelation_cases hdc2
    rcases hcase with hpo | ⟨bb, n, hsync, _, _⟩
    · have hdeq : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) = d := by
        have h1 : c2.thread = d.thread := by rw [hpo]
        have h2 : c2.idx = d.idx + 1 := by rw [hpo]
        obtain ⟨dt, di⟩ := d
        simp only [ProgPoint.mk.injEq] at h1 h2 ⊢
        exact ⟨h1, by omega⟩
      rw [hdeq]; exact hd
    · rw [hc2] at hsync; exact absurd hsync (by simp)

/-- `(CheckWellSynchronized T τ).1` is, by definition, the Step-3 pairwise check
expressed as a nested `List.all`. -/
theorem fst_checkWellSynchronized (T : CTA) (τ : List Config) :
    (CheckWellSynchronized T τ).1 = T.progPoints.all (fun c1 =>
      match (T.cmdAt c1).bind Cmd.barrier? with
      | some b =>
          T.progPoints.all fun c2 =>
            match (T.cmdAt c2).bind Cmd.barrier? with
            | some b' =>
                if b = b' ∧ pointGen T τ c2 = pointGen T τ c1 + 1 then
                  if 1 ≤ c2.idx then
                    decide (c1 = (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∨
                      (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∈
                        transClosure (initRelation T τ))
                  else false
                else true
            | none => true
      | none => true) := rfl

/-- **Extract a failing pair from `check = false`.** Unwinding the two nested
`List.all`s and the `match`/`if` of Step 3 (Figure 4 lines 18–22): a `false` result
exhibits a generation-`k` **barrier op** `c1` on `b` (a `sync` *or* an `arrive`) and a
generation-`k+1` barrier op `c2` on `b` (with `1 ≤ c2.idx`) whose predecessor `c3` the
relation fails to order after `c1`. The reflexive disjunct of the Step-3 check means a
genuine failure also delivers `c1 ≠ c3` (a flagged pair with `c1 = c3` would have passed
via reflexivity). -/
theorem exists_failing_pair {T : CTA} {τ : List Config}
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    ∃ c1 ∈ T.progPoints, ∃ b, (T.cmdAt c1).bind Cmd.barrier? = some b ∧
      ∃ c2 ∈ T.progPoints, (T.cmdAt c2).bind Cmd.barrier? = some b ∧
        pointGen T τ c2 = pointGen T τ c1 + 1 ∧
        ((1 ≤ c2.idx ∧
            c1 ≠ (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∧
            (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∉ (CheckWellSynchronized T τ).2) ∨
          c2.idx = 0) := by
  rw [fst_checkWellSynchronized] at hcheck
  obtain ⟨c1, hc1, hf1⟩ := List.all_eq_false.mp hcheck
  refine ⟨c1, hc1, ?_⟩
  -- decode `c1`'s barrier (`read`/`write` give `none`, contradicting `hf1`)
  obtain ⟨b, hbar1⟩ : ∃ b, (T.cmdAt c1).bind Cmd.barrier? = some b := by
    cases hb : (T.cmdAt c1).bind Cmd.barrier? with
    | none => simp [hb] at hf1
    | some b => exact ⟨b, rfl⟩
  refine ⟨b, hbar1, ?_⟩
  simp only [hbar1, Bool.not_eq_true] at hf1
  obtain ⟨c2, hc2, hf2⟩ := List.all_eq_false.mp hf1
  refine ⟨c2, hc2, ?_⟩
  rw [snd_checkWellSynchronized]
  obtain ⟨b', hbar2⟩ : ∃ b', (T.cmdAt c2).bind Cmd.barrier? = some b' := by
    cases hb : (T.cmdAt c2).bind Cmd.barrier? with
    | none => simp [hb] at hf2
    | some b' => exact ⟨b', rfl⟩
  simp only [hbar2] at hf2
  by_cases hcond : b = b' ∧ pointGen T τ c2 = pointGen T τ c1 + 1
  · rw [if_pos hcond] at hf2
    obtain ⟨hbb, hgen⟩ := hcond
    subst hbb
    by_cases hidx : 1 ≤ c2.idx
    · rw [if_pos hidx] at hf2
      simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or] at hf2
      exact ⟨hbar2, hgen, Or.inl ⟨hidx, hf2.1, hf2.2⟩⟩
    · exact ⟨hbar2, hgen, Or.inr (by omega)⟩
  · rw [if_neg hcond] at hf2; exact absurd hf2 (by simp)

/-- **Dual of `exists_failing_pair`.** From `check = true`, *every* flagged line-18 pair is
ordered: given a **barrier op** `c1` on `b'` (a `sync` *or* an `arrive`) and a same-barrier
op `c2` (with `1 ≤ c2.idx`) of generation `pointGen c1 + 1`, the predecessor
`c3 = ⟨c2.thread, c2.idx - 1⟩` satisfies `happensBefore T τ c1 c3`. This unwinds the two
nested `List.all`s of `fst_checkWellSynchronized` at the witnesses `c1, c2`, then reads off
the reflexive-or-`transClosure` `decide` in the `if`-`then` branch (whose guard holds by
hypothesis): the `c1 = c3` disjunct is reflexivity, the membership disjunct is a
`transClosure` path (`mem_transClosure_imp_transGen`). -/
theorem happensBefore_of_check {T : CTA} {τ : List Config}
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b' : Barrier}
    (hbar1 : (T.cmdAt c1).bind Cmd.barrier? = some b')
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hbar2 : (T.cmdAt c2).bind Cmd.barrier? = some b')
    (hgen : pointGen T τ c2 = pointGen T τ c1 + 1) (hidx : 1 ≤ c2.idx) :
    happensBefore T τ c1 (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) := by
  rw [fst_checkWellSynchronized] at hcheck
  have hf1 := List.all_eq_true.mp hcheck c1 hc1
  simp only [hbar1] at hf1
  have hf2 := List.all_eq_true.mp hf1 c2 hc2
  simp only [hbar2] at hf2
  rw [if_pos ⟨True.intro, hgen⟩, if_pos hidx, decide_eq_true_eq] at hf2
  rcases hf2 with heq | hmem
  · rw [heq]; exact Relation.ReflTransGen.refl
  · exact (mem_transClosure_imp_transGen _ hmem).to_reflTransGen

/-- **Companion of `happensBefore_of_check` for the strengthened idx-0 check.** From
`check = true`, no flagged line-18 pair has a first-instruction target: given a barrier op
`c1` on `b'` and a same-barrier op `c2` of generation `pointGen c1 + 1`, necessarily
`1 ≤ c2.idx` (a flagged pair with `c2.idx = 0` returns `false` outright). Same unfolding
as `happensBefore_of_check`, reading the `else false` branch instead. -/
theorem idx_pos_of_check {T : CTA} {τ : List Config}
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b' : Barrier}
    (hbar1 : (T.cmdAt c1).bind Cmd.barrier? = some b')
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hbar2 : (T.cmdAt c2).bind Cmd.barrier? = some b')
    (hgen : pointGen T τ c2 = pointGen T τ c1 + 1) : 1 ≤ c2.idx := by
  by_contra hidx
  rw [fst_checkWellSynchronized] at hcheck
  have hf1 := List.all_eq_true.mp hcheck c1 hc1
  simp only [hbar1] at hf1
  have hf2 := List.all_eq_true.mp hf1 c2 hc2
  simp only [hbar2] at hf2
  rw [if_pos ⟨True.intro, hgen⟩, if_neg hidx] at hf2
  exact absurd hf2 (by simp)

/-! ## Trace conformance — the soundness invariant (weft++ theorems doc §5.2.6)

Machinery for **Theorem 1** (`wellSynchronized_of_check`), following the paper proof in
§5.2.6 of the weft++ theorems document and the repo plan `soundness-theorem1-plan.md`.
The paper's suffix induction is replaced by a *forward* induction over an arbitrary
(possibly incomplete) challenger trace `τ'`, carrying the `Conforms T τ τ'` invariant:

* **clause 0** (`no_err`) — `τ'` has not errored;
* **clause 1** (`gen_eq`) — every instruction executed in `τ'` has its reference
  generation: `pointGen T τ' η = pointGen T τ η`;
* **clause 2** (`state`, via `BarrierConforms`) — each barrier's state is the image of
  the *current fiber's* progress: the configured count is the fiber parameter, the
  arrival count counts the fiber's executed `arrive`s, and the parked list is exactly
  the threads of the fiber's parked `sync`s;
* **clause 3** (`edge_sound`) — every `initRelation` edge whose target has executed in
  `τ'` has an executed source, no later. Stated on the *generating* edges and lifted to
  `happensBefore` paths once (`Conforms.happensBefore_sound`), so that the invariant's
  per-step maintenance stays local.

The layers, bottom-up: **L0** — fiber structure of the reference trace (`genFiber`,
parameter agreement, size = capacity, partial round is all-`arrive`s); **L1** — checker
extraction (`happensBefore_of_check`, `idx_pos_of_check` above); **L2** — the invariant
and its preservation (`conforms_snoc`, whose registration cases funnel through the
round-targeting lemma `conforms_reg_round` and the fullness pigeonhole
`conforms_full_fiber`); **L3** — the endgame (`conforms_complete_done`, the paper's
Theorem 7, via the minimal-τ-time descent) and the assembly (Theorem 8 = Theorem 1). -/

/-- The expected-count parameter of a synchronization command (`arrive b n`/`sync b n`
carry `n`); `none` for the memory commands. -/
def Cmd.count? : Cmd → Option ℕ+
  | .arrive _ n => some n
  | .sync _ n => some n
  | .read _ => none
  | .write _ => none

/-- The **generation fiber** `F_g(b)` of the reference trace: the barrier operations on
`b` to which `τ` assigns generation `g` (`pointGen`). The rounds of `b` in any conforming
challenger trace consume exactly these, one fiber per recycle. -/
def genFiber (T : CTA) (τ : List Config) (b : Barrier) (g : Nat) : List ProgPoint :=
  T.progPoints.filter fun η =>
    decide ((T.cmdAt η).bind Cmd.barrier? = some b) && decide (pointGen T τ η = g)

/-- Fiber membership, unfolded. -/
theorem mem_genFiber {T : CTA} {τ : List Config} {b : Barrier} {g : Nat} {η : ProgPoint} :
    η ∈ genFiber T τ b g ↔
      η ∈ T.progPoints ∧ (T.cmdAt η).bind Cmd.barrier? = some b ∧ pointGen T τ η = g := by
  simp [genFiber, List.mem_filter]

/-! ### Layer-0 helpers — locating recycles and decoding the steps behind them -/

/-- `pointGen` read off at a known execution time. -/
theorem pointGen_eq_of_time {T : CTA} {τ : List Config} {η : ProgPoint} {b : Barrier}
    (hbar : (T.cmdAt η).bind Cmd.barrier? = some b) {m : Nat}
    (hm : IsTimeOf (Config.run State.initial T) τ η m) :
    pointGen T τ η = recycleCount b τ (m - 1) + 1 := by
  simp only [pointGen, hbar, pointTime_eq_of_isTimeOf hm]

/-- Configuration `j` of a chain is reachable from the chain's start — bridges trace
indices to the `WF_of_reaches` machinery. -/
theorem reaches_of_chain_getElem {τ : List Config} (hchain : List.IsChain CTAStep τ)
    {C₀ : Config} (h0 : τ[0]? = some C₀) :
    ∀ (j : Nat) (C : Config), τ[j]? = some C → Relation.ReflTransGen CTAStep C₀ C := by
  intro j
  induction j with
  | zero =>
    intro C hC
    rw [h0] at hC
    obtain rfl := Option.some.inj hC
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro C hC
    have hlt : k + 1 < τ.length := (List.getElem?_eq_some_iff.mp hC).1
    have hklt : k < τ.length := by omega
    have hCk : τ[k]? = some τ[k] := List.getElem?_eq_getElem hklt
    exact (ih _ hCk).tail (chain_step hchain hCk hC)

/-- Each step adds at most one recycle of `b`. -/
theorem recycleCount_le_succ (b : Barrier) (τ : List Config) (j : Nat) :
    recycleCount b τ (j + 1) ≤ recycleCount b τ j + 1 := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append]
  exact Nat.add_le_add_left (List.countP_le_length.trans (by simp)) _

/-- Locate the `g`-th recycle of `b`: if at least `g ≥ 1` recycles occur within the
first `M` steps, some step `p < M` is the `g`-th — the count is `g - 1` before it and
`g` after. (The `g`-th recycle step is unique: any other index with count `g - 1`
before and `g` after would put `g` recycles strictly before it.) -/
theorem recycleCount_hits (b : Barrier) (τ : List Config) {g M : Nat} (hg : 1 ≤ g)
    (hM : g ≤ recycleCount b τ M) :
    ∃ p, p < M ∧ recycleCount b τ p = g - 1 ∧ recycleCount b τ (p + 1) = g := by
  induction M with
  | zero =>
    exfalso
    have h0 : recycleCount b τ 0 = 0 := by unfold recycleCount; simp
    omega
  | succ k ih =>
    by_cases hk : g ≤ recycleCount b τ k
    · obtain ⟨p, hp, h1, h2⟩ := ih hk
      exact ⟨p, by omega, h1, h2⟩
    · have hle := recycleCount_le_succ b τ k
      exact ⟨k, by omega, by omega, by omega⟩

/-- Extract the recycling step at a `recycleCount` increase. -/
theorem recycle_step_of_count_lt {b : Barrier} {τ : List Config} {p : Nat}
    (h : recycleCount b τ p < recycleCount b τ (p + 1)) :
    ∃ C C', τ[p]? = some C ∧ τ[p + 1]? = some C' ∧ stepRecyclesBarrier b C C' = true := by
  obtain ⟨C, hC⟩ : ∃ C, τ[p]? = some C := by
    rcases hex : τ[p]? with _ | C
    · exfalso
      have heq : recycleCount b τ (p + 1) = recycleCount b τ p := by
        unfold recycleCount
        rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
        simp [hex]
      omega
    · exact ⟨C, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C', τ[p + 1]? = some C' := by
    rcases hex : τ[p + 1]? with _ | C'
    · exfalso
      have heq : recycleCount b τ (p + 1) = recycleCount b τ p := by
        unfold recycleCount
        rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
        simp [hC, hex]
      omega
    · exact ⟨C', rfl⟩
  refine ⟨C, C', hC, hC', ?_⟩
  by_contra hf
  rw [Bool.not_eq_true] at hf
  have := recycleCount_succ_of_not_recycle b hC hC' hf
  omega

/-- **Decode a recycling step.** The `CTAStep` behind `stepRecyclesBarrier b` is
necessarily `CTAStep.recycle` *of `b`*: `interleave`'s guard keeps every barrier
under-full, `done` keeps the state (a full barrier is not unconfigured), `error` has no
target state, and a recycle of another barrier leaves `b` untouched. Exposes the full
pre-step barrier state — full, with every parked thread's head at the matching
`sync b n` — and the exact post-step configuration. -/
theorem stepRecyclesBarrier_elim {C C' : Config} (hstep : CTAStep C C') {b : Barrier}
    (hrec : stepRecyclesBarrier b C C' = true) :
    ∃ s Tc I A n, C = Config.run s Tc ∧ s.B b = ⟨I, A, some n⟩ ∧
      I.length + A = (n : ℕ) ∧ (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.sync b n)) ∧
      C' = Config.run
                      ({ E := updateMapOn s.E I true,
                         B := Function.update s.B b BarrierState.unconfigured } : State)
             (Tc.wake I) := by
  cases hstep with
  | @interleave s s' Tc i P' hi hbar hth =>
    exfalso
    have hnf : (s.B b).isFull = false := by
      rcases hbar b with hu | ⟨I, A, n, hcfg, hlt⟩
      · rw [hu]; rfl
      · rw [hcfg]; simp only [BarrierState.isFull]
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp [stepRecyclesBarrier, Config.state?, hnf] at hrec
  | @recycle s Tc b' I A n hb hfull hpark =>
    by_cases hbb : b' = b
    · subst hbb
      exact ⟨s, Tc, I, A, n, rfl, hb, hfull, hpark, rfl⟩
    · exfalso
      have hupd : (Function.update s.B b' BarrierState.unconfigured) b = s.B b :=
        Function.update_of_ne (Ne.symm hbb) _ _
      simp only [stepRecyclesBarrier, Config.state?, Bool.and_eq_true, hupd,
        decide_eq_true_eq] at hrec
      obtain ⟨hfl, hunc⟩ := hrec
      rw [hunc] at hfl
      simp [BarrierState.isFull, BarrierState.unconfigured] at hfl
  | done hdone hnofull =>
    exfalso
    simp only [stepRecyclesBarrier, Config.state?, Bool.and_eq_true,
      decide_eq_true_eq] at hrec
    obtain ⟨hfl, hunc⟩ := hrec
    rw [hunc] at hfl
    simp [BarrierState.isFull, BarrierState.unconfigured] at hfl
  | error hbar hth =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?] at hrec

/-- `findSome?` respects pointwise-equal functions. -/
theorem findSome?_congr {α : Type*} {β : Type*} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.findSome?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some b => rfl

/-- `recycleCount` ignores an appended configuration while the bound stays within the
original trace. -/
theorem recycleCount_append (b : Barrier) (τ' : List Config) (C' : Config) {j : Nat}
    (hj : j + 1 ≤ τ'.length) :
    recycleCount b (τ' ++ [C']) j = recycleCount b τ' j := by
  unfold recycleCount
  refine List.countP_congr fun i hi => ?_
  rw [List.mem_range] at hi
  have h1 : (τ' ++ [C'])[i]? = τ'[i]? := List.getElem?_append_left (by omega)
  have h2 : (τ' ++ [C'])[i + 1]? = τ'[i + 1]? := List.getElem?_append_left (by omega)
  rw [h1, h2]

/-- A computed time survives appending a configuration. -/
theorem pointTime_append_some {T : CTA} {τ' : List Config} {C' : Config}
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m) :
    pointTime T (τ' ++ [C']) η = some m := by
  have hne : τ' ≠ [] := by
    intro h
    rw [h] at hpt
    simp [pointTime] at hpt
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime, if_pos hidx] at hpt ⊢
    have hlen : (τ' ++ [C']).length - 1 = (τ'.length - 1) + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlen, List.range_succ, List.findSome?_append]
    have hcongr : List.findSome? (fun j =>
        match (τ' ++ [C'])[j]?, (τ' ++ [C'])[j + 1]? with
        | some C, some C'' =>
            if (C.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx &&
                (C''.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx - 1 then
              some (j + 1) else none
        | _, _ => none) (List.range (τ'.length - 1)) = some m := by
      rw [findSome?_congr (g := fun j =>
        match τ'[j]?, τ'[j + 1]? with
        | some C, some C'' =>
            if (C.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx &&
                (C''.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx - 1 then
              some (j + 1) else none
        | _, _ => none) ?_]
      · exact hpt
      · intro a ha
        rw [List.mem_range] at ha
        have h1 : (τ' ++ [C'])[a]? = τ'[a]? := List.getElem?_append_left (by omega)
        have h2 : (τ' ++ [C'])[a + 1]? = τ'[a + 1]? := List.getElem?_append_left (by omega)
        rw [h1, h2]
    rw [hcongr]
    rfl
  · simp only [pointTime, if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- A computed time on `τ' ++ [C']` is either an old time of `τ'` or the appended step
itself. -/
theorem pointTime_append_cases {T : CTA} {τ' : List Config} {C' : Config}
    (hne : τ' ≠ []) {η : ProgPoint} {m : Nat}
    (hpt : pointTime T (τ' ++ [C']) η = some m) :
    pointTime T τ' η = some m ∨ (pointTime T τ' η = none ∧ m = τ'.length) := by
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  cases hptτ : pointTime T τ' η with
  | some m' =>
    have hσ := pointTime_append_some (C' := C') hptτ
    rw [hpt, Option.some.injEq] at hσ
    subst hσ
    exact Or.inl rfl
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    by_cases hidx : η.idx < (T.prog η.thread).length
    · simp only [pointTime, if_pos hidx] at hpt hptτ
      have hlen : (τ' ++ [C']).length - 1 = (τ'.length - 1) + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hlen, List.range_succ, List.findSome?_append] at hpt
      have hcongr : List.findSome? (fun j =>
          match (τ' ++ [C'])[j]?, (τ' ++ [C'])[j + 1]? with
          | some C, some C'' =>
              if (C.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx &&
                  (C''.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx - 1 then
                some (j + 1) else none
          | _, _ => none) (List.range (τ'.length - 1)) = none := by
        rw [findSome?_congr (g := fun j =>
          match τ'[j]?, τ'[j + 1]? with
          | some C, some C'' =>
              if (C.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx &&
                  (C''.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx - 1 then
                some (j + 1) else none
          | _, _ => none) ?_]
        · exact hptτ
        · intro a ha
          rw [List.mem_range] at ha
          have h1 : (τ' ++ [C'])[a]? = τ'[a]? := List.getElem?_append_left (by omega)
          have h2 : (τ' ++ [C'])[a + 1]? = τ'[a + 1]? :=
            List.getElem?_append_left (by omega)
          rw [h1, h2]
      rw [hcongr, Option.none_or, List.findSome?_cons] at hpt
      split at hpt
      · rename_i b₀ hb₀
        rw [Option.some.injEq] at hpt
        -- the matcher value is `some (τ'.length - 1 + 1)`
        split at hb₀
        · rename_i C₁ C₂ hC₁ hC₂
          split at hb₀
          · rw [Option.some.injEq] at hb₀
            omega
          · simp at hb₀
        · simp at hb₀
      · simp at hpt
    · simp only [pointTime, if_neg hidx] at hpt
      exact absurd hpt (by simp)

/-- Counting forces pointwise agreement: if `p` implies `q` on `l` and `q`'s count does
not exceed `p`'s, then `q` implies `p` on `l`. -/
theorem countP_eq_all {α : Type*} : ∀ {l : List α} {p q : α → Bool},
    (∀ x ∈ l, p x = true → q x = true) → l.countP q ≤ l.countP p →
    ∀ x ∈ l, q x = true → p x = true := by
  intro l
  induction l with
  | nil => intro p q _ _ x hx; simp at hx
  | cons a t ih =>
    intro p q himp hle x hx hqx
    have himpt : ∀ y ∈ t, p y = true → q y = true :=
      fun y hy => himp y (List.mem_cons_of_mem _ hy)
    have hmt : t.countP p ≤ t.countP q := List.countP_mono_left himpt
    simp only [List.countP_cons] at hle
    rcases List.mem_cons.mp hx with rfl | hxt
    · by_contra hpx
      rw [Bool.not_eq_true] at hpx
      rw [hqx, hpx] at hle
      simp at hle
      omega
    · refine ih himpt ?_ x hxt hqx
      by_cases hpa : p a = true
      · rw [hpa, himp a (List.mem_cons_self ..) hpa] at hle
        simpa using hle
      · rw [Bool.not_eq_true] at hpa
        rw [hpa] at hle
        cases hqa : q a
        · rw [hqa] at hle
          simpa using hle
        · rw [hqa] at hle
          simp at hle
          omega

/-- **Lift a head-dropping step to a static program point.** If at step `j → j+1` thread
`i`'s remaining program goes from `c :: rest` to `rest`, then the static point
`⟨i, |T.prog i| - |C.progOf i|⟩` executes at time `j + 1`, and its static command is
`c`. -/
theorem exec_step_time {T : CTA} {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ)
    {j : Nat} {C C' : Config} (hCj : τ[j]? = some C) (hCj1 : τ[j + 1]? = some C')
    {i : ThreadId} {c : Cmd} {rest : Prog}
    (hC : C.progOf i = c :: rest) (hC' : C'.progOf i = rest) :
    IsTimeOf (Config.run State.initial T) τ
        ⟨i, (T.prog i).length - (C.progOf i).length⟩ (j + 1) ∧
      T.cmdAt ⟨i, (T.prog i).length - (C.progOf i).length⟩ = some c := by
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hsuf : C.progOf i <:+ (Config.run State.initial T).progOf i :=
    progOf_suffix_index_le hchain i h0 (Nat.zero_le j) hCj
  have hlen : (C.progOf i).length ≤ (T.prog i).length := suffix_length_le hsuf
  have hpos : 0 < (C.progOf i).length := by rw [hC]; simp
  have hdropk : C.progOf i = (T.prog i).drop ((T.prog i).length - (C.progOf i).length) :=
    List.IsSuffix.eq_drop hsuf
  have hkL : (T.prog i).length - (C.progOf i).length < (T.prog i).length := by omega
  have hdropk1 : C'.progOf i =
      (T.prog i).drop ((T.prog i).length - (C.progOf i).length + 1) := by
    rw [hC', ← List.tail_drop, ← hdropk, hC, List.tail_cons]
  exact ⟨⟨hτ, hkL, j, C, C', rfl, hCj, hCj1, hdropk, hdropk1⟩, cmd_at_last hsuf hC⟩

/-- Classify a step's effect on `b`'s arrival count: unchanged, an `arrive b _` execution
(head dropped), or a recycle of `b`. -/
theorem arrived_step {C C' : Config} (hstep : CTAStep C C') {b : Barrier}
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s') :
    (s'.B b).arrived = (s.B b).arrived ∨
    (∃ (i : ThreadId) (n' : ℕ+) (rest : Prog),
      C.progOf i = Cmd.arrive b n' :: rest ∧ C'.progOf i = rest) ∨
    stepRecyclesBarrier b C C' = true := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hth =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPi] at hth
    cases hth with
    | read_noop => exact Or.inl rfl
    | write_noop => exact Or.inl rfl
    | @arrive_configure _ _ ba na _ he hb =>
      by_cases hbb : b = ba
      · subst hbb
        refine Or.inr (Or.inl ⟨t, na, P', hPi, ?_⟩)
        simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self]
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @arrive_register _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : b = ba
      · subst hbb
        refine Or.inr (Or.inl ⟨t, na, P', hPi, ?_⟩)
        simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self]
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @sync_configure _ _ ba na _ he hb =>
      by_cases hbb : b = ba
      · subst hbb
        exact Or.inl (by
          simp [Function.update_self, hb, BarrierState.unconfigured])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @sync_block _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : b = ba
      · subst hbb
        exact Or.inl (by simp [Function.update_self, hb])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    by_cases hbb : ba = b
    · subst hbb
      refine Or.inr (Or.inr ?_)
      simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self]
    · exact Or.inl (by simp only [Function.update_of_ne (Ne.symm hbb)])
  | done hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact Or.inl rfl
  | error hbar hth =>
    simp [Config.state?] at hs'

/-- **Decode an `arrive` execution.** A step that drops a thread's `arrive b n'` head is
an `interleave` running that `arrive`; the rule premise ties `n'` to the barrier — it
either configures `b` or registers into a count-`n'` state — and afterwards `b` is
configured with count `n'` and one more arrival. -/
theorem arrive_exec_decode {C C' : Config} (hstep : CTAStep C C') {i : ThreadId}
    {b : Barrier} {n' : ℕ+} {rest : Prog}
    (hC : C.progOf i = Cmd.arrive b n' :: rest) (hC' : C'.progOf i = rest) :
    ∃ s s', C.state? = some s ∧ C'.state? = some s' ∧
      (s.B b = BarrierState.unconfigured ∨ (s.B b).count = some n') ∧
      (s'.B b).count = some n' ∧ (s'.B b).arrived = (s.B b).arrived + 1 := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hth =>
    by_cases hti : t = i
    · subst hti
      obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
      rw [hPi] at hth
      have hC0 : Pi = Cmd.arrive b n' :: rest := by rw [← hPi]; exact hC
      subst hC0
      cases hth with
      | arrive_configure he hb =>
        refine ⟨s₀, _, rfl, rfl, Or.inl hb, ?_, ?_⟩
        · simp [Function.update_self]
        · rw [hb]; simp [Function.update_self, BarrierState.unconfigured]
      | @arrive_register _ _ _ _ _ I A he hb hpos hlt =>
        refine ⟨s₀, _, rfl, rfl, Or.inr (by rw [hb]), ?_, ?_⟩
        · simp [Function.update_self]
        · rw [hb]; simp [Function.update_self]
    · exfalso
      have hCc : Tc.prog i = Cmd.arrive b n' :: rest := hC
      have hsame : (Tc.set t ht P').prog i = Tc.prog i := by
        simp [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hti)]
      have hC'' : Tc.prog i = rest := by rw [← hsame]; exact hC'
      rw [hC''] at hCc
      have hlen := congrArg List.length hCc
      simp at hlen
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    exfalso
    have hCc : Tc.prog i = Cmd.arrive b n' :: rest := hC
    by_cases hi : i ∈ I
    · have hhd := hpark i hi
      rw [hCc] at hhd
      simp at hhd
    · have hsame : (Tc.wake I).prog i = Tc.prog i := by simp [WeftCommon.CTA.wake, if_neg hi]
      have hCw : (Tc.wake I).prog i = rest := hC'
      rw [hsame, hCc] at hCw
      have hlen := congrArg List.length hCw
      simp at hlen
  | @done s₀ Tc hdone hnofull =>
    exfalso
    have hCc : Tc.prog i = Cmd.arrive b n' :: rest := hC
    have hnil : Tc.prog i = [] := by
      by_cases hi : i ∈ Tc.ids
      · exact hdone i hi
      · exact Tc.nil_outside_ids i hi
    rw [hnil] at hCc
    simp at hCc
  | @error s₀ Tc t P' hbar hth =>
    exfalso
    have hCc : Tc.prog i = Cmd.arrive b n' :: rest := hC
    have hC'' : Tc.prog i = rest := hC'
    rw [hC''] at hCc
    have hlen := congrArg List.length hCc
    simp at hlen

/-- A step preserves a configured count unless it recycles the barrier. -/
theorem count_step {C C' : Config} (hstep : CTAStep C C') {b : Barrier} {n : ℕ+}
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s')
    (hn : (s.B b).count = some n) (hnorec : stepRecyclesBarrier b C C' = false) :
    (s'.B b).count = some n := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hth =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPi] at hth
    cases hth with
    | read_noop => exact hn
    | write_noop => exact hn
    | @arrive_configure _ _ ba na _ he hb =>
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hn; simp [BarrierState.unconfigured] at hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @arrive_register _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : b = ba
      · subst hbb
        rw [hb] at hn
        simp only [Function.update_self]
        simpa using hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @sync_configure _ _ ba na _ he hb =>
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hn; simp [BarrierState.unconfigured] at hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @sync_block _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : b = ba
      · subst hbb
        rw [hb] at hn
        simp only [Function.update_self]
        simpa using hn
      · simpa only [Function.update_of_ne hbb] using hn
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    by_cases hbb : ba = b
    · subst hbb
      exfalso
      simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self] at hnorec
    · simpa only [Function.update_of_ne (Ne.symm hbb)] using hn
  | done hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact hn
  | error hbar hth =>
    simp [Config.state?] at hs'

/-- **Count persistence.** Over a recycle-free stretch of the trace (equal
`recycleCount` at both ends), a configured count survives. -/
theorem count_persists {τ : List Config} (hchain : List.IsChain CTAStep τ) {b : Barrier}
    {n : ℕ+} :
    ∀ (k j : Nat), j ≤ k → recycleCount b τ j = recycleCount b τ k →
    ∀ {C : Config} {s : State}, τ[j]? = some C → C.state? = some s →
      (s.B b).count = some n →
    ∀ {C' : Config} {s' : State}, τ[k]? = some C' → C'.state? = some s' →
      (s'.B b).count = some n := by
  intro k
  induction k with
  | zero =>
    intro j hjk _ C s hC hs hn C' s' hC' hs'
    obtain rfl : j = 0 := by omega
    rw [hC] at hC'
    obtain rfl := Option.some.inj hC'
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    exact hn
  | succ k ih =>
    intro j hjk hrc C s hC hs hn C' s' hC' hs'
    by_cases hje : j = k + 1
    · subst hje
      rw [hC] at hC'
      obtain rfl := Option.some.inj hC'
      rw [hs] at hs'
      obtain rfl := Option.some.inj hs'
      exact hn
    · have hjk' : j ≤ k := by omega
      have hklt : k < τ.length := by
        have := (List.getElem?_eq_some_iff.mp hC').1
        omega
      have hCk : τ[k]? = some τ[k] := List.getElem?_eq_getElem hklt
      have hstepk := chain_step hchain hCk hC'
      obtain ⟨sk, hsk⟩ : ∃ sk, (τ[k]).state? = some sk := by
        rcases hkc : τ[k] with ⟨s₁, T₁⟩ | s₁ | T₁
        · exact ⟨s₁, rfl⟩
        · rw [hkc] at hstepk; cases hstepk
        · rw [hkc] at hstepk; cases hstepk
      have hm1 := recycleCount_mono b τ hjk'
      have hm2 := recycleCount_mono b τ (show k ≤ k + 1 by omega)
      have hrcjk : recycleCount b τ j = recycleCount b τ k := by omega
      have hnorec : stepRecyclesBarrier b τ[k] C' = false := by
        by_contra hrec
        rw [Bool.not_eq_false] at hrec
        have := recycleCount_succ_of_recycle b τ hCk hC' hrec
        omega
      exact count_step hstepk hsk hs' (ih j hjk' hrcjk hC hs hn hCk hsk) hnorec

/-- Discrete search: a `ℕ`-valued function that grows over an interval increases at some
step inside it. -/
theorem exists_step_increase (f : Nat → Nat) :
    ∀ (hi lo : Nat), lo ≤ hi → f lo < f hi →
      ∃ j, lo ≤ j ∧ j < hi ∧ f j < f (j + 1) := by
  intro hi
  induction hi with
  | zero =>
    intro lo hle hlt
    obtain rfl : lo = 0 := Nat.le_zero.mp hle
    exact absurd hlt (lt_irrefl _)
  | succ k ih =>
    intro lo hle hlt
    by_cases hlo : lo ≤ k
    · by_cases hk : f k < f (k + 1)
      · exact ⟨k, hlo, Nat.lt_succ_self k, hk⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih lo hlo (by omega)
        exact ⟨j, h1, by omega, h3⟩
    · obtain rfl : lo = k + 1 := by omega
      exact absurd hlt (lt_irrefl _)

/-- `progPoints` enumerates each program point exactly once. -/
theorem progPoints_nodup (T : CTA) : T.progPoints.Nodup := by
  unfold CTA.progPoints
  rw [List.nodup_flatMap]
  constructor
  · intro i _
    exact List.nodup_range.map fun a b hab => by simpa using congrArg ProgPoint.idx hab
  · refine (Finset.sort_nodup T.ids (· ≤ ·)).imp ?_
    intro i i' hne x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨k', -, hkk⟩ := hx'
    exact hne (by simpa using congrArg ProgPoint.thread hkk.symm)

/-- Fibers inherit `Nodup` from `progPoints`. -/
theorem genFiber_nodup (T : CTA) (τ : List Config) (b : Barrier) (g : Nat) :
    (genFiber T τ b g).Nodup :=
  (progPoints_nodup T).filter _

/-- Counting after enlarging a predicate at exactly one list element. -/
theorem countP_succ_of_unique {α : Type*} {l : List α} (hnd : l.Nodup)
    {p q : α → Bool} {a₀ : α} (ha₀ : a₀ ∈ l) (hqa : q a₀ = true) (hpa : p a₀ = false)
    (hpq : ∀ x ∈ l, x ≠ a₀ → q x = p x) :
    l.countP q = l.countP p + 1 := by
  induction l with
  | nil => simp at ha₀
  | cons a t ih =>
    obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha₀ with rfl | hmem
    · have htail : t.countP q = t.countP p :=
        List.countP_congr fun x hx => by
          rw [hpq x (List.mem_cons_of_mem _ hx) (fun h => hna (h ▸ hx))]
      simp [htail, hqa, hpa]
    · have hne : a ≠ a₀ := fun h => hna (h ▸ hmem)
      have hqp := hpq a (List.mem_cons_self ..) hne
      have iht := ih hndt hmem fun x hx hxne => hpq x (List.mem_cons_of_mem _ hx) hxne
      simp only [List.countP_cons, iht, hqp]
      omega

/-- A computed `pointTime` is a genuine `IsTimeOf` (converse of
`pointTime_eq_of_isTimeOf`). -/
theorem isTimeOf_of_pointTime {T : CTA} {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ)
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ η = some m) :
    IsTimeOf (Config.run State.initial T) τ η m := by
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hC₀ : (Config.run State.initial T).progOf η.thread = T.prog η.thread := rfl
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime] at hpt
    rw [if_pos hidx] at hpt
    rw [List.findSome?_eq_some_iff] at hpt
    obtain ⟨l₁, a, l₂, -, hfa, -⟩ := hpt
    split at hfa
    · rename_i C C' hCa hCa1
      split at hfa
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hl1, hl2⟩ := hcond
        rw [Option.some.injEq] at hfa
        subst hfa
        refine ⟨hτ, hidx, a, C, C', rfl, hCa, hCa1, ?_, ?_⟩
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le a) hCa)
          rw [hl1, hC₀] at heq
          rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
            from by omega] at heq
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le (a + 1)) hCa1)
          rw [hl2, hC₀] at heq
          rwa [show (T.prog η.thread).length -
              ((T.prog η.thread).length - η.idx - 1) = η.idx + 1
            from by omega] at heq
      · simp at hfa
    · simp at hfa
  · simp only [pointTime] at hpt
    rw [if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- `pointGen` read off a computed `pointTime` (works on partial traces). -/
theorem pointGen_eq_of_pointTime {T : CTA} {τ' : List Config} {η : ProgPoint}
    {b : Barrier} (hbar : (T.cmdAt η).bind Cmd.barrier? = some b) {m : Nat}
    (hpt : pointTime T τ' η = some m) :
    pointGen T τ' η = recycleCount b τ' (m - 1) + 1 := by
  simp only [pointGen, hbar, hpt]

/-- Unpack a computed `pointTime` on a *partial* trace into the executing step's drop
facts. (`IsTimeOf` requires a complete trace; this is the raw content, available on any
chain from the initial configuration.) -/
theorem pointTime_spec {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m) :
    1 ≤ m ∧ m < τ'.length ∧ η.idx < (T.prog η.thread).length ∧
    ∃ C C', τ'[m - 1]? = some C ∧ τ'[m]? = some C' ∧
      C.progOf η.thread = (T.prog η.thread).drop η.idx ∧
      C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) := by
  have h0' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact h0
  have hC₀ : (Config.run State.initial T).progOf η.thread = T.prog η.thread := rfl
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime] at hpt
    rw [if_pos hidx] at hpt
    rw [List.findSome?_eq_some_iff] at hpt
    obtain ⟨l₁, a, l₂, -, hfa, -⟩ := hpt
    split at hfa
    · rename_i C C' hCa hCa1
      split at hfa
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hl1, hl2⟩ := hcond
        rw [Option.some.injEq] at hfa
        subst hfa
        have hmlt : a + 1 < τ'.length := (List.getElem?_eq_some_iff.mp hCa1).1
        refine ⟨by omega, hmlt, hidx, C, C',
          by rw [show a + 1 - 1 = a by omega]; exact hCa, hCa1, ?_, ?_⟩
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0' (Nat.zero_le a) hCa)
          rw [hl1, hC₀] at heq
          rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
            from by omega] at heq
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0' (Nat.zero_le (a + 1)) hCa1)
          rw [hl2, hC₀] at heq
          rwa [show (T.prog η.thread).length -
              ((T.prog η.thread).length - η.idx - 1) = η.idx + 1
            from by omega] at heq
      · simp at hfa
    · simp at hfa
  · simp only [pointTime] at hpt
    rw [if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- A `sync`'s computed time on a partial trace is a recycle of its barrier
(`sync_time_recycles` without the completeness packaging). -/
theorem pointTime_sync_recycles {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m)
    {bb : Barrier} {nn : ℕ+} (hcm : T.cmdAt η = some (.sync bb nn)) :
    ∃ C C', τ'[m - 1]? = some C ∧ τ'[m]? = some C' ∧
      stepRecyclesBarrier bb C C' = true := by
  obtain ⟨hm1, hmlt, hidx, C, C', hC, hC', hCdrop, hC'drop⟩ := pointTime_spec hchain h0 hpt
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm
  have hcons : C.progOf η.thread =
      Cmd.sync bb nn :: (T.prog η.thread).drop (η.idx + 1) := by
    rw [hCdrop, List.drop_eq_getElem_cons hidx, hget0]
  have hCC' : τ'[m - 1 + 1]? = some C' := by
    rw [show m - 1 + 1 = m by omega]; exact hC'
  have hstep := chain_step hchain hC hCC'
  exact ⟨C, C', hC, hC', sync_drop_recycles hstep hcons hC'drop⟩

/-- **A passed instruction has executed** (partial-trace variant of
`exists_time_of_ends_done`): if the last configuration's remaining program for thread
`i` has length at most `|T.prog i| - (k + 1)`, the pointer moved past instruction `k`,
so point `⟨i, k⟩` has a computed time. Intermediate-value argument on program lengths. -/
theorem exists_pointTime_of_passed {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {C : Config} (hlast : τ'.getLast? = some C) {i : ThreadId} {k : Nat}
    (hk : k < (T.prog i).length)
    (hpassed : (C.progOf i).length + (k + 1) ≤ (T.prog i).length) :
    ∃ m, pointTime T τ' ⟨i, k⟩ = some m := by
  have h0' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact h0
  have hlastidx : τ'[τ'.length - 1]? = some C := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlen1 : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at h0
    | cons a l => simp
  have hsuffix : ∀ {j} {D : Config}, τ'[j]? = some D →
      D.progOf i <:+ (Config.run State.initial T).progOf i :=
    fun {j D} hD => progOf_suffix_index_le hchain i h0' (Nat.zero_le j) hD
  have hQlast : ((τ'[τ'.length - 1]?).map (fun D => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := by
    rw [hlastidx]
    change (C.progOf i).length < (T.prog i).length - k
    omega
  have hex : ∃ j, ((τ'[j]?).map (fun (D : Config) => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := ⟨τ'.length - 1, hQlast⟩
  have hQj0 := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ τ'.length - 1 := Nat.find_le hQlast
  have hQ0 : ¬ ((τ'[0]?).map (fun D => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := by
    rw [h0']
    change ¬ (T.prog i).length < (T.prog i).length - k
    omega
  have hj0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hQj0; exact absurd hQj0 hQ0
    · exact h
  have hminj := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have hj0lt : Nat.find hex < τ'.length := by omega
  obtain ⟨D, hD⟩ : ∃ D, τ'[Nat.find hex - 1]? = some D :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨D', hD'⟩ : ∃ D', τ'[Nat.find hex]? = some D' :=
    ⟨_, List.getElem?_eq_getElem hj0lt⟩
  have hDD' : τ'[Nat.find hex - 1 + 1]? = some D' := by
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hD'
  have hub : (D.progOf i).length ≤ (D'.progOf i).length + 1 :=
    (chain_step hchain hD hDD').progOf_length_le_succ i
  have e1 : ((τ'[Nat.find hex - 1]?).map (fun D => (D.progOf i).length)).getD 0
      = (D.progOf i).length := by rw [hD]; rfl
  have e2 : ((τ'[Nat.find hex]?).map (fun D => (D.progOf i).length)).getD 0
      = (D'.progOf i).length := by rw [hD']; rfl
  rw [e1] at hminj
  rw [e2] at hQj0
  have hlenD : (D.progOf i).length = (T.prog i).length - k := by omega
  have hlenD' : (D'.progOf i).length = (T.prog i).length - k - 1 := by omega
  have hne : pointTime T τ' ⟨i, k⟩ ≠ none := by
    intro hnone
    simp only [pointTime] at hnone
    rw [if_pos hk] at hnone
    rw [List.findSome?_eq_none_iff] at hnone
    have hjmem : Nat.find hex - 1 ∈ List.range (τ'.length - 1) :=
      List.mem_range.mpr (by omega)
    have hmatch := hnone _ hjmem
    simp only [hD, hDD', hlenD, hlenD'] at hmatch
    simp at hmatch
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨m, hm⟩

/-- Two `arrive`-head drops at the same step happen on the same thread: only a single
`interleave` thread advances past an `arrive` (recycles drop only parked `sync`s). -/
theorem arrive_drop_thread_unique {C C' : Config} (hstep : CTAStep C C')
    {i₁ i₂ : ThreadId} {b₁ b₂ : Barrier} {n₁ n₂ : ℕ+} {r₁ r₂ : Prog}
    (h1 : C.progOf i₁ = Cmd.arrive b₁ n₁ :: r₁) (h1' : C'.progOf i₁ = r₁)
    (h2 : C.progOf i₂ = Cmd.arrive b₂ n₂ :: r₂) (h2' : C'.progOf i₂ = r₂) :
    i₁ = i₂ := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hth =>
    by_cases hti : i₁ = t
    · by_cases hti2 : i₂ = t
      · rw [hti, hti2]
      · exfalso
        have hsame : (Tc.set t ht P').prog i₂ = Tc.prog i₂ := by
          simp [WeftCommon.CTA.set, Function.update_of_ne hti2]
        have hc : Tc.prog i₂ = Cmd.arrive b₂ n₂ :: r₂ := h2
        have hc' : Tc.prog i₂ = r₂ := by rw [← hsame]; exact h2'
        rw [hc'] at hc
        have hlen := congrArg List.length hc
        simp at hlen
    · exfalso
      have hsame : (Tc.set t ht P').prog i₁ = Tc.prog i₁ := by
        simp [WeftCommon.CTA.set, Function.update_of_ne hti]
      have hc : Tc.prog i₁ = Cmd.arrive b₁ n₁ :: r₁ := h1
      have hc' : Tc.prog i₁ = r₁ := by rw [← hsame]; exact h1'
      rw [hc'] at hc
      have hlen := congrArg List.length hc
      simp at hlen
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    exfalso
    have hc : Tc.prog i₁ = Cmd.arrive b₁ n₁ :: r₁ := h1
    by_cases hi : i₁ ∈ I
    · have hhd := hpark i₁ hi
      rw [hc] at hhd
      simp at hhd
    · have hsame : (Tc.wake I).prog i₁ = Tc.prog i₁ := by simp [WeftCommon.CTA.wake, if_neg hi]
      have hc' : (Tc.wake I).prog i₁ = r₁ := h1'
      rw [hsame, hc] at hc'
      have hlen := congrArg List.length hc'
      simp at hlen
  | @done s₀ Tc hdone hnofull =>
    exfalso
    have hc : Tc.prog i₁ = Cmd.arrive b₁ n₁ :: r₁ := h1
    have hnil : Tc.prog i₁ = [] := by
      by_cases hi : i₁ ∈ Tc.ids
      · exact hdone i₁ hi
      · exact Tc.nil_outside_ids i₁ hi
    rw [hnil] at hc
    simp at hc
  | @error s₀ Tc t P' hbar hth =>
    exfalso
    have hc : Tc.prog i₁ = Cmd.arrive b₁ n₁ :: r₁ := h1
    have hc' : Tc.prog i₁ = r₁ := h1'
    rw [hc'] at hc
    have hlen := congrArg List.length hc
    simp at hlen

/-- **L0d — the partial round is all-`arrive`s.** The fiber of the round after the last
completed one (ops the reference trace ran in a round that never recycled) contains no
`sync`: a `sync`'s execution step *is* a recycle of its barrier, which would push the
recycle count past the total. -/
theorem genFiber_partial_no_sync {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {η : ProgPoint}
    (hη : η ∈ genFiber T τ b (recycleCount b τ (τ.length - 1) + 1)) :
    ∀ n : ℕ+, T.cmdAt η ≠ some (.sync b n) := by
  intro n hcmd
  obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  have hpg := pointGen_eq_of_time hbar hm
  have hm1 : 1 ≤ m := by
    obtain ⟨-, -, j, -, -, hj, -, -, -, -⟩ := hm
    omega
  have hcmd' : η.cmd (Config.run State.initial T) = some (Cmd.sync b n) := hcmd
  obtain ⟨C, C', hC, hC', hrec⟩ := sync_time_recycles hm hcmd'
  have hC'' : τ[m - 1 + 1]? = some C' := by
    rw [show m - 1 + 1 = m by omega]; exact hC'
  have hsucc := recycleCount_succ_of_recycle b τ hC hC'' hrec
  have hmlt : m < τ.length := (List.getElem?_eq_some_iff.mp hC').1
  have hmono : recycleCount b τ (m - 1 + 1) ≤ recycleCount b τ (τ.length - 1) :=
    recycleCount_mono b τ (by omega)
  omega

/-- An `arrive` member of a fiber leaves `b` configured with *its own parameter* right
after its execution step: at index `m` (its time), the count is `some na`, and the
recycle count strictly before it is `g - 1`. The seed of every parameter-agreement
argument (persist the count forward to the round's recycle, or to the trace end). -/
theorem genFiber_arrive_post_count {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} {η : ProgPoint} (hη : η ∈ genFiber T τ b g)
    {na : ℕ+} (hcm : T.cmdAt η = some (.arrive b na)) :
    ∃ (m : Nat) (C' : Config) (s' : State),
      1 ≤ m ∧ m < τ.length ∧ pointTime T τ η = some m ∧ τ[m]? = some C' ∧
      C'.state? = some s' ∧
      (s'.B b).count = some na ∧ recycleCount b τ (m - 1) = g - 1 ∧ 1 ≤ g := by
  obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  have hpg := pointGen_eq_of_time hbar hm
  have hptm := pointTime_eq_of_isTimeOf hm
  obtain ⟨-, -, j, D, D', hjm, hD, hD', hDdrop, hD'drop⟩ := hm
  subst hjm
  simp only [Nat.add_sub_cancel] at hpg
  have hcm' : ((Config.run State.initial T).progOf η.thread)[η.idx]? =
      some (Cmd.arrive b na) := hcm
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm'
  have hDcons : D.progOf η.thread =
      Cmd.arrive b na :: ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := by
    rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
  have hD'rest : D'.progOf η.thread =
      ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := hD'drop
  have hstepD := chain_step hτ.1.1.subtrace hD hD'
  obtain ⟨s₁, s₂, hs₁, hs₂, hpre, hpost, hinc⟩ := arrive_exec_decode hstepD hDcons hD'rest
  have hjlen : j + 1 < τ.length := (List.getElem?_eq_some_iff.mp hD').1
  refine ⟨j + 1, D', s₂, by omega, hjlen, hptm, hD', hs₂, hpost, ?_, by omega⟩
  simp only [Nat.add_sub_cancel]
  omega

/-- **The round data of a completed generation.** For `1 ≤ g ≤` the total recycles of
`b`, locate the `g`-th recycle: at step `p` the barrier holds a full round
`⟨I, A, some n⟩` whose parked threads sit at `sync b n` heads, the recycle wakes them —
and, the fiber-parameter fact, every member of `F_g(b)` carries the count `n`
(`sync`s read it off `hpark`; `arrive`s configure/match it at their own step, and it
persists through the recycle-free window to `p`). -/
theorem genFiber_round_data {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g)
    (hcomplete : g ≤ recycleCount b τ (τ.length - 1)) :
    ∃ (p : Nat) (s : State) (Tc : CTA) (I : List ThreadId) (A : Nat) (n : ℕ+),
      recycleCount b τ p = g - 1 ∧ recycleCount b τ (p + 1) = g ∧
      τ[p]? = some (Config.run s Tc) ∧ s.B b = ⟨I, A, some n⟩ ∧
      I.length + A = (n : ℕ) ∧
      (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.sync b n)) ∧
      τ[p + 1]? = some (Config.run
        ({ E := updateMapOn s.E I true,
           B := Function.update s.B b BarrierState.unconfigured } : State) (Tc.wake I)) ∧
      (∀ η ∈ genFiber T τ b g, (T.cmdAt η).bind Cmd.count? = some n) ∧
      (∀ η ∈ genFiber T τ b g, ∀ nn : ℕ+, T.cmdAt η = some (.sync b nn) →
        η.thread ∈ I ∧ Tc.prog η.thread = (T.prog η.thread).drop η.idx) ∧
      (∀ i ∈ I, ∃ η ∈ genFiber T τ b g, η.thread = i ∧
        ∃ nn : ℕ+, T.cmdAt η = some (.sync b nn)) := by
  obtain ⟨p, hpM, hrc1, hrc2⟩ := recycleCount_hits b τ hg hcomplete
  obtain ⟨C, C', hC, hC', hrecb⟩ := recycle_step_of_count_lt (b := b) (τ := τ) (p := p)
    (by omega)
  have hstep := chain_step hτ.1.1.subtrace hC hC'
  obtain ⟨s, Tc, I, A, n, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
    stepRecyclesBarrier_elim hstep hrecb
  subst hCeq; subst hC'eq
  -- sync members are parked in `I`, control at the member
  have hsync_data : ∀ η ∈ genFiber T τ b g, ∀ nn : ℕ+, T.cmdAt η = some (.sync b nn) →
      η.thread ∈ I ∧ Tc.prog η.thread = (T.prog η.thread).drop η.idx := by
    intro η hη nn hcmd
    obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
    obtain ⟨sd, hdone⟩ := hτ.2
    have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
    obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
    have hpg := pointGen_eq_of_time hbar hm
    obtain ⟨E, E', hE, hE', hrecE⟩ := sync_time_recycles hm hcmd
    have hm1 : 1 ≤ m := by
      obtain ⟨-, -, j', -, -, hj', -, -, -, -⟩ := hm
      omega
    have hEsucc : recycleCount b τ (m - 1 + 1) = recycleCount b τ (m - 1) + 1 := by
      refine recycleCount_succ_of_recycle b τ hE ?_ hrecE
      rw [show m - 1 + 1 = m by omega]; exact hE'
    have hup : m - 1 = p := by
      rcases Nat.lt_trichotomy (m - 1) p with hlt | heq | hgt
      · exfalso
        have := recycleCount_mono b τ (show m - 1 + 1 ≤ p by omega)
        omega
      · exact heq
      · exfalso
        have := recycleCount_mono b τ (show p + 1 ≤ m - 1 by omega)
        omega
    obtain ⟨-, -, j', D, D', hj'm, hD, hD', hDdrop, hD'drop⟩ := hm
    have hj'p : j' = p := by omega
    subst hj'p
    have hDeq : D = Config.run s Tc := by
      rw [hD] at hC
      exact Option.some.inj hC
    subst hDeq
    have hD'eq : D' = Config.run
        ({ E := updateMapOn s.E I true,
           B := Function.update s.B b BarrierState.unconfigured } : State) (Tc.wake I) := by
      rw [hD'] at hC'
      exact Option.some.inj hC'
    subst hD'eq
    have htI : η.thread ∈ I := by
      by_contra htn
      have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
        simp [WeftCommon.CTA.wake, if_neg htn]
      have h1 : Tc.prog η.thread =
          ((Config.run State.initial T).progOf η.thread).drop η.idx := hDdrop
      have h2 : (Tc.wake I).prog η.thread =
          ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := hD'drop
      rw [hsame, h1] at h2
      have hlen := congrArg List.length h2
      simp only [List.length_drop] at hlen
      have hidx0 : η.idx < ((Config.run State.initial T).progOf η.thread).length := hidx
      omega
    exact ⟨htI, hDdrop⟩
  -- every parked thread contributes a sync member
  have hsurj : ∀ i ∈ I, ∃ η ∈ genFiber T τ b g, η.thread = i ∧
      ∃ nn : ℕ+, T.cmdAt η = some (.sync b nn) := by
    intro i hi
    have hhead := hpark i hi
    obtain ⟨rest, hrest⟩ : ∃ rest, Tc.prog i = Cmd.sync b n :: rest := by
      cases hTt : Tc.prog i with
      | nil => rw [hTt] at hhead; simp at hhead
      | cons a l =>
        rw [hTt] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨l, by rw [hhead]⟩
    have hCprog : (Config.run s Tc).progOf i = Cmd.sync b n :: rest := hrest
    have hC'prog : (Config.run
        ({ E := updateMapOn s.E I true,
           B := Function.update s.B b BarrierState.unconfigured } : State)
        (Tc.wake I)).progOf i = rest := by
      simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake, if_pos hi, hrest, List.tail_cons]
    obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hC hC' hCprog hC'prog
    refine ⟨_, mem_genFiber.mpr ⟨mem_progPoints_of_cmdAt T hcmd, ?_, ?_⟩, rfl, n, hcmd⟩
    · rw [hcmd]; rfl
    · rw [pointGen_eq_of_time (by rw [hcmd]; rfl) htime]
      simp only [Nat.add_sub_cancel]
      omega
  refine ⟨p, s, Tc, I, A, n, hrc1, hrc2, hC, hbst, hfull, hpark, hC', ?_,
    hsync_data, hsurj⟩
  intro η hη
  obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
  cases hcmd : T.cmdAt η with
  | none => rw [hcmd] at hbar; exact absurd hbar (by simp)
  | some cmd =>
    cases cmd with
    | read g₀ => rw [hcmd] at hbar; simp [Cmd.barrier?] at hbar
    | write g₀ => rw [hcmd] at hbar; simp [Cmd.barrier?] at hbar
    | arrive bb na =>
      have hbb : b = bb := by
        rw [hcmd] at hbar
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar
        exact hbar.symm
      subst hbb
      obtain ⟨m, D', s₂, hm1, hmlen, -, hD', hs₂, hpost, hrcm, -⟩ :=
        genFiber_arrive_post_count hτ hη hcmd
      -- `m ≠ p + 1`: the post-arrive state is configured, the post-recycle one is not
      have hmp : m ≠ p + 1 := by
        intro hmeq
        subst hmeq
        rw [hD'] at hC'
        obtain rfl := Option.some.inj hC'
        simp only [Config.state?, Option.some.injEq] at hs₂
        subst hs₂
        simp [Function.update_self, BarrierState.unconfigured] at hpost
      -- `m ≤ p`: a later registration would sit past the `g`-th recycle
      have hmle : m ≤ p := by
        by_contra hcon
        have hple : p + 1 ≤ m - 1 := by omega
        have := recycleCount_mono b τ hple
        omega
      -- the window `[m, p]` is recycle-free: persist the count to the recycle
      have hrcmp : recycleCount b τ m = recycleCount b τ p := by
        have h1 := recycleCount_mono b τ (show m - 1 ≤ m by omega)
        have h2 := recycleCount_mono b τ hmle
        omega
      have hcount := count_persists hτ.1.1.subtrace p m hmle hrcmp hD' hs₂ hpost hC rfl
      rw [hbst] at hcount
      simpa [Cmd.count?] using hcount.symm
    | sync bb na =>
      have hbb : b = bb := by
        rw [hcmd] at hbar
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar
        exact hbar.symm
      subst hbb
      obtain ⟨htI, hpt⟩ := hsync_data η hη na hcmd
      have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
      have hhd := hpark η.thread htI
      rw [hpt, List.drop_eq_getElem_cons hidx, List.head?_cons] at hhd
      have hcm2 : (T.prog η.thread)[η.idx]? = some (Cmd.sync b na) := hcmd
      obtain ⟨hlt2, hget⟩ := List.getElem?_eq_some_iff.mp hcm2
      rw [hget] at hhd
      simp only [Option.some.injEq, Cmd.sync.injEq] at hhd
      simp [Cmd.count?, hhd.2]

/-- **L0b — fiber parameter agreement.** Any two members of a fiber of the successful
reference trace carry the same count parameter: all of `F_g(b)` registered into `τ`'s
round `g` of `b`, whose configured count every registration matched without error.
Completed rounds read the common count off `genFiber_round_data`; the partial round is
all-`arrive`s (L0d), each of whose parameters persists to the final configuration. -/
theorem genFiber_count_eq {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g) {η₁ η₂ : ProgPoint}
    (h₁ : η₁ ∈ genFiber T τ b g) (h₂ : η₂ ∈ genFiber T τ b g) :
    (T.cmdAt η₁).bind Cmd.count? = (T.cmdAt η₂).bind Cmd.count? := by
  by_cases hcomp : g ≤ recycleCount b τ (τ.length - 1)
  · obtain ⟨p, s, Tc, I, A, n, -, -, -, -, -, -, -, hall, -, -⟩ :=
      genFiber_round_data hτ hg hcomp
    rw [hall η₁ h₁, hall η₂ h₂]
  · obtain ⟨sd, hdone⟩ := hτ.2
    have hR : g = recycleCount b τ (τ.length - 1) + 1 := by
      obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp h₁
      have hidx : η₁.idx < (T.prog η₁.thread).length :=
        ((mem_progPoints_iff T η₁).mp hmem).2
      obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
      have hpg := pointGen_eq_of_time hbar hm
      have hmlt : m < τ.length := by
        obtain ⟨-, -, j, C₁, C₂, hj, -, hCj1, -, -⟩ := hm
        have := (List.getElem?_eq_some_iff.mp hCj1).1
        omega
      have := recycleCount_mono b τ (show m - 1 ≤ τ.length - 1 by omega)
      omega
    have hkey : ∀ η' ∈ genFiber T τ b g, ∃ na : ℕ+,
        (T.cmdAt η').bind Cmd.count? = some na ∧ (sd.B b).count = some na := by
      intro η' hη'
      obtain ⟨hmem', hbar', -⟩ := mem_genFiber.mp hη'
      cases hcmd : T.cmdAt η' with
      | none => rw [hcmd] at hbar'; exact absurd hbar' (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcmd] at hbar'; simp [Cmd.barrier?] at hbar'
        | write g₀ => rw [hcmd] at hbar'; simp [Cmd.barrier?] at hbar'
        | sync bb na =>
          exfalso
          have hbb : b = bb := by
            rw [hcmd] at hbar'
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar'
            exact hbar'.symm
          subst hbb
          exact genFiber_partial_no_sync hτ (hR ▸ hη') na hcmd
        | arrive bb na =>
          have hbb : b = bb := by
            rw [hcmd] at hbar'
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar'
            exact hbar'.symm
          subst hbb
          obtain ⟨m, D', s₂, hm1, hmlen, -, hD', hs₂, hpost, hrcm, -⟩ :=
            genFiber_arrive_post_count hτ hη' hcmd
          have hlast : τ[τ.length - 1]? = some (Config.done sd) := by
            rw [← List.getLast?_eq_getElem?]; exact hdone
          have hrcend : recycleCount b τ m = recycleCount b τ (τ.length - 1) := by
            have hmn1 := recycleCount_mono b τ (show m - 1 ≤ m by omega)
            have hmn2 := recycleCount_mono b τ (show m ≤ τ.length - 1 by omega)
            omega
          have hcount := count_persists hτ.1.1.subtrace (τ.length - 1) m
            (by omega) hrcend hD' hs₂ hpost hlast rfl
          exact ⟨na, by simp [Cmd.count?], hcount⟩
    obtain ⟨n₁, hc₁, he₁⟩ := hkey η₁ h₁
    obtain ⟨n₂, hc₂, he₂⟩ := hkey η₂ h₂
    rw [hc₁, hc₂, ← he₁, he₂]

/-- **L0 — lower fibers are inhabited.** If some op has generation `g + 1` on `b` in the
reference trace, then `b` recycled at least `g ≥ 1` times before it, and the `g`-th
recycle consumed at least one registration — an op of generation `g`. Supplies the
checker pair's source `c1` in the "early" contradiction. -/
theorem genFiber_nonempty_of_succ {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g) {η : ProgPoint}
    (hη : η ∈ genFiber T τ b (g + 1)) :
    ∃ η', η' ∈ genFiber T τ b g := by
  obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  have hpg := pointGen_eq_of_time hbar hm
  -- locate the `g`-th recycle of `b` (η's generation `g + 1` puts `g` recycles before it)
  obtain ⟨p, hpm, hrc1, hrc2⟩ :=
    recycleCount_hits b τ hg (show g ≤ recycleCount b τ (m - 1) by omega)
  obtain ⟨C, C', hC, hC', hrecb⟩ := recycle_step_of_count_lt (b := b) (τ := τ) (p := p)
    (by omega)
  have hstep := chain_step hτ.1.1.subtrace hC hC'
  obtain ⟨s, Tc, I, A, n, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
    stepRecyclesBarrier_elim hstep hrecb
  subst hCeq; subst hC'eq
  rcases hI : I with _ | ⟨t, I'⟩
  · -- the round was all-`arrive`s: trace one arrival back through the window
    subst hI
    have hA : A = (n : ℕ) := by simpa using hfull
    -- a window start `w ≤ p` with zero arrivals and recycle count `g - 1`
    obtain ⟨w, hwp, hw0, hwrc⟩ :
        ∃ w, w ≤ p ∧
          (∃ Cw sw, τ[w]? = some Cw ∧ Cw.state? = some sw ∧ (sw.B b).arrived = 0) ∧
          recycleCount b τ w = g - 1 := by
      rcases Nat.eq_or_lt_of_le hg with hg1 | hg2
      · refine ⟨0, by omega, ⟨Config.run State.initial T, State.initial, ?_, rfl, rfl⟩, ?_⟩
        · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
          rw [hgen0]; exact hτ.1.2
        · have h0 : recycleCount b τ 0 = 0 := by unfold recycleCount; simp
          omega
      · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits b τ
          (show 1 ≤ g - 1 by omega) (show g - 1 ≤ recycleCount b τ p by omega)
        obtain ⟨D, D', hD, hD', hrecD⟩ := recycle_step_of_count_lt (b := b) (τ := τ)
          (p := q) (by omega)
        have hstepD := chain_step hτ.1.1.subtrace hD hD'
        obtain ⟨sD, TD, ID, AD, nD, hDeq, -, -, -, hD'eq⟩ :=
          stepRecyclesBarrier_elim hstepD hrecD
        subst hD'eq
        refine ⟨q + 1, by omega, ⟨_, _, hD', rfl, ?_⟩, by omega⟩
        simp [Function.update_self, BarrierState.unconfigured]
    obtain ⟨Cw, sw, hCw, hsw, hw0'⟩ := hw0
    -- the arrival counter, as a function of the trace index
    set f : Nat → Nat := fun l =>
      (((τ[l]?).bind Config.state?).map fun st => (st.B b).arrived).getD 0 with hf
    have hfw : f w = 0 := by simp [hf, hCw, hsw, hw0']
    have hfp : f p = (n : ℕ) := by
      simp [hf, hC, Config.state?, hbst, hA]
    obtain ⟨j, hjw, hjp, hjlt⟩ := exists_step_increase f p w hwp
      (by have := n.pos; omega)
    have hjlen : j + 1 < τ.length := by
      have := (List.getElem?_eq_some_iff.mp hC).1
      omega
    have hCj : τ[j]? = some τ[j] := List.getElem?_eq_getElem (by omega)
    have hCj1 : τ[j + 1]? = some τ[j + 1] := List.getElem?_eq_getElem (by omega)
    have hstepj := chain_step hτ.1.1.subtrace hCj hCj1
    obtain ⟨sj, hsj⟩ : ∃ sj, (τ[j]).state? = some sj := by
      rcases hj : τ[j] with ⟨s₁, T₁⟩ | s₁ | T₁
      · exact ⟨s₁, rfl⟩
      · rw [hj] at hstepj; cases hstepj
      · rw [hj] at hstepj; cases hstepj
    obtain ⟨sj1, hsj1⟩ : ∃ sj1, (τ[j + 1]).state? = some sj1 := by
      rcases hj1 : τ[j + 1] with ⟨s₁, T₁⟩ | s₁ | T₁
      · exact ⟨s₁, rfl⟩
      · exact ⟨s₁, rfl⟩
      · exfalso
        have hzero : f (j + 1) = 0 := by simp [hf, hCj1, hj1, Config.state?]
        omega
    have hlt' : (sj.B b).arrived < (sj1.B b).arrived := by
      have h1 : f j = (sj.B b).arrived := by simp [hf, hCj, hsj]
      have h2 : f (j + 1) = (sj1.B b).arrived := by simp [hf, hCj1, hsj1]
      omega
    rcases arrived_step (b := b) hstepj hsj hsj1 with heq | ⟨i, n', rest, hCi, hC'i⟩ | hrecj
    · exfalso; omega
    · -- the arrival's static point has generation `g`
      obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hCj hCj1 hCi hC'i
      refine ⟨_, mem_genFiber.mpr ⟨mem_progPoints_of_cmdAt T hcmd, ?_, ?_⟩⟩
      · rw [hcmd]; rfl
      · rw [pointGen_eq_of_time (by rw [hcmd]; rfl) htime]
        simp only [Nat.add_sub_cancel]
        have hm1 := recycleCount_mono b τ hjw
        have hm2 := recycleCount_mono b τ (Nat.le_of_lt hjp)
        omega
    · -- a recycle of `b` strictly inside the window is impossible
      exfalso
      have hsucc := recycleCount_succ_of_recycle b τ hCj hCj1 hrecj
      have hm1 := recycleCount_mono b τ hjw
      have hm2 := recycleCount_mono b τ (show j + 1 ≤ p by omega)
      omega
  · -- a parked sync: woken at this recycle, generation `g`
    subst hI
    have hhead := hpark t (List.mem_cons_self ..)
    obtain ⟨rest, hrest⟩ : ∃ rest, Tc.prog t = Cmd.sync b n :: rest := by
      cases hTt : Tc.prog t with
      | nil => rw [hTt] at hhead; simp at hhead
      | cons a l =>
        rw [hTt] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨l, by rw [hhead]⟩
    have hCprog : (Config.run s Tc).progOf t = Cmd.sync b n :: rest := hrest
    have hC'prog : (Config.run
        ({ E := updateMapOn s.E (t :: I') true,
           B := Function.update s.B b BarrierState.unconfigured } : State)
        (Tc.wake (t :: I'))).progOf t = rest := by
      simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake,
        if_pos (List.mem_cons_self ..), hrest,
        List.tail_cons]
    obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hC hC' hCprog hC'prog
    refine ⟨_, mem_genFiber.mpr ⟨mem_progPoints_of_cmdAt T hcmd, ?_, ?_⟩⟩
    · rw [hcmd]; rfl
    · rw [pointGen_eq_of_time (by rw [hcmd]; rfl) htime]
      simp only [Nat.add_sub_cancel]
      omega

/-- `arrive`-command classifier (top-level, so its `match` auxiliary is shared between
the census lemma and its consumers). -/
def isArriveCmd (T : CTA) (η : ProgPoint) : Bool :=
  match T.cmdAt η with | some (.arrive _ _) => true | _ => false

/-- `sync`-command classifier; see `isArriveCmd`. -/
def isSyncCmd (T : CTA) (η : ProgPoint) : Bool :=
  match T.cmdAt η with | some (.sync _ _) => true | _ => false

/-- The census predicate: an `arrive` member already executed by step `j`. -/
def arriveBy (T : CTA) (τ : List Config) (j : Nat) (η : ProgPoint) : Bool :=
  isArriveCmd T η &&
    (match pointTime T τ η with | some m => decide (m ≤ j) | none => false)

/-- **The window census.** From the start `w` of `b`'s round `g` (arrival counter zero,
`g - 1` recycles done, every fiber time still ahead) to any index `j` still inside the
round, `b`'s arrival counter equals the number of fiber `arrive`s executed by `j`: each
counter increment is an `arrive` execution whose static point is a fresh fiber member,
and nothing else moves the counter (recycles of `b` lie outside the window). -/
theorem arrived_census {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g)
    {w : Nat} {Cw : Config} {sw : State} (hCw : τ[w]? = some Cw)
    (hsw : Cw.state? = some sw) (hw0 : (sw.B b).arrived = 0)
    (hwrc : recycleCount b τ w = g - 1)
    (hlate : ∀ η ∈ genFiber T τ b g, ∀ m, pointTime T τ η = some m → w < m) :
    ∀ (j : Nat), w ≤ j → recycleCount b τ j = g - 1 →
    ∀ (Cj : Config) (sj : State), τ[j]? = some Cj → Cj.state? = some sj →
    (sj.B b).arrived = (genFiber T τ b g).countP (arriveBy T τ j) := by
  intro j hwj
  induction j, hwj using Nat.le_induction with
  | base =>
    intro _ Cj sj hCj hsj
    rw [hCw] at hCj
    obtain rfl := Option.some.inj hCj
    rw [hsw] at hsj
    obtain rfl := Option.some.inj hsj
    rw [hw0]
    symm
    rw [List.countP_eq_zero]
    intro η hη
    simp only [arriveBy, Bool.and_eq_true, not_and]
    intro _
    cases hpt : pointTime T τ η with
    | none => simp
    | some m =>
      have := hlate η hη m hpt
      simp only [decide_eq_true_eq]
      omega
  | succ j hwj ih =>
    intro hrcj1 Cj1 sj1 hCj1 hsj1
    have hjlt : j < τ.length := by
      have := (List.getElem?_eq_some_iff.mp hCj1).1
      omega
    obtain ⟨Dj, hCj⟩ : ∃ Dj, τ[j]? = some Dj :=
      ⟨τ[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
    have hstepj := chain_step hτ.1.1.subtrace hCj hCj1
    obtain ⟨sj, hsj⟩ : ∃ sj, (Dj).state? = some sj := by
      rcases hjc : Dj with ⟨s₁, T₁⟩ | s₁ | T₁
      · exact ⟨s₁, rfl⟩
      · rw [hjc] at hstepj; cases hstepj
      · rw [hjc] at hstepj; cases hstepj
    have hrcj : recycleCount b τ j = g - 1 := by
      have h1 := recycleCount_mono b τ hwj
      have h2 := recycleCount_mono b τ (show j ≤ j + 1 by omega)
      omega
    have hprev := ih hrcj Dj sj hCj hsj
    -- executing a fiber `arrive b` at this very step bumps the counter
    have hexec_inc : ∀ η ∈ genFiber T τ b g, ∀ nn : ℕ+,
        T.cmdAt η = some (.arrive b nn) → pointTime T τ η = some (j + 1) →
        (sj1.B b).arrived = (sj.B b).arrived + 1 := by
      intro η hη nn hcm hpt
      have htime := isTimeOf_of_pointTime hτ.1 hpt
      obtain ⟨-, hidxlt, j₀, D, D', hj₀, hD, hD', hDdrop, hD'drop⟩ := htime
      have hj₀j : j₀ = j := by omega
      subst hj₀j
      have hDeq : Dj = D := by
        have h := hD
        rw [hCj] at h
        exact Option.some.inj h
      subst hDeq
      have hD'eq : D' = Cj1 := by
        have h := hD'
        rw [hCj1] at h
        exact (Option.some.inj h).symm
      subst hD'eq
      have hcm' : ((Config.run State.initial T).progOf η.thread)[η.idx]? =
          some (Cmd.arrive b nn) := hcm
      obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm'
      have hDcons : (Dj).progOf η.thread = Cmd.arrive b nn ::
          ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := by
        rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
      obtain ⟨s₁', s₂', hs₁', hs₂', -, -, hinc⟩ :=
        arrive_exec_decode hstepj hDcons hD'drop
      rw [hsj] at hs₁'
      obtain rfl := Option.some.inj hs₁'
      rw [hsj1] at hs₂'
      obtain rfl := Option.some.inj hs₂'
      exact hinc
    rcases arrived_step (b := b) hstepj hsj hsj1 with
      heq | ⟨i, n', rest, hCi, hC'i⟩ | hrecj
    · -- counter unchanged: no fiber `arrive` executed at `j + 1`
      rw [heq, hprev]
      refine List.countP_congr fun η hη => ?_
      simp only [arriveBy, isArriveCmd]
      cases hcm : T.cmdAt η with
      | none => simp
      | some cmd =>
        cases cmd with
        | read g₀ => simp
        | write g₀ => simp
        | sync bb nn => simp
        | arrive bb nn =>
          simp only [Bool.true_and]
          cases hpt : pointTime T τ η with
          | none => simp
          | some m =>
            simp only [decide_eq_true_eq]
            constructor
            · intro hmj
              omega
            · intro hmj1
              rcases Nat.lt_or_ge m (j + 1) with hlt | hge
              · omega
              · exfalso
                have hmeq : m = j + 1 := by omega
                subst hmeq
                have hbb : bb = b := by
                  obtain ⟨-, hbar, -⟩ := mem_genFiber.mp hη
                  rw [hcm] at hbar
                  simpa [Cmd.barrier?] using hbar
                subst hbb
                have := hexec_inc η hη nn hcm hpt
                omega
    · -- the counter grew: exactly one fresh census member, the executed `arrive`
      obtain ⟨htimeN, hcmdN⟩ := exec_step_time hτ.1 hCj hCj1 hCi hC'i
      obtain ⟨s₁', s₂', hs₁', hs₂', -, -, hinc⟩ := arrive_exec_decode hstepj hCi hC'i
      rw [hsj] at hs₁'
      obtain rfl := Option.some.inj hs₁'
      rw [hsj1] at hs₂'
      obtain rfl := Option.some.inj hs₂'
      have hηmem : (⟨i, (T.prog i).length - ((Dj).progOf i).length⟩ : ProgPoint) ∈
          genFiber T τ b g := by
        refine mem_genFiber.mpr ⟨mem_progPoints_of_cmdAt T hcmdN, ?_, ?_⟩
        · rw [hcmdN]; rfl
        · rw [pointGen_eq_of_time (by rw [hcmdN]; rfl) htimeN]
          simp only [Nat.add_sub_cancel]
          omega
      have hptN : pointTime T τ ⟨i, (T.prog i).length - ((Dj).progOf i).length⟩ =
          some (j + 1) := pointTime_eq_of_isTimeOf htimeN
      rw [hinc, hprev]
      symm
      refine countP_succ_of_unique (genFiber_nodup T τ b g) hηmem ?_ ?_ ?_
      · simp only [arriveBy, isArriveCmd, hcmdN, hptN, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨trivial, le_refl _⟩
      · simp only [arriveBy, isArriveCmd, hcmdN, hptN]
        simp
      · intro x hx hxne
        simp only [arriveBy, isArriveCmd]
        cases hcm : T.cmdAt x with
        | none => rfl
        | some cmd =>
          cases cmd with
          | read g₀ => rfl
          | write g₀ => rfl
          | sync bb nn => rfl
          | arrive bb nn =>
            cases hpt : pointTime T τ x with
            | none => rfl
            | some m =>
              rcases Nat.lt_or_ge m (j + 1) with hlt | hge
              · have h1 : decide (m ≤ j + 1) = true := by
                  simp only [decide_eq_true_eq]; omega
                have h2 : decide (m ≤ j) = true := by
                  simp only [decide_eq_true_eq]; omega
                simp only [h1, h2]
              · rcases Nat.lt_or_ge (j + 1) m with hlt2 | hge2
                · have h1 : decide (m ≤ j + 1) = false := by
                    simp only [decide_eq_false_iff_not]; omega
                  have h2 : decide (m ≤ j) = false := by
                    simp only [decide_eq_false_iff_not]; omega
                  simp only [h1, h2]
                · exfalso
                  have hmeq : m = j + 1 := by omega
                  subst hmeq
                  have htimeX := isTimeOf_of_pointTime hτ.1 hpt
                  obtain ⟨-, hidxX, j₀, D, D', hj₀, hD, hD', hXdrop, hX'drop⟩ := htimeX
                  have hj₀j : j₀ = j := by omega
                  subst hj₀j
                  have hDeq : Dj = D := by
                    have h := hD
                    rw [hCj] at h
                    exact Option.some.inj h
                  subst hDeq
                  have hD'eq : D' = Cj1 := by
                    have h := hD'
                    rw [hCj1] at h
                    exact (Option.some.inj h).symm
                  subst hD'eq
                  have hcm' : ((Config.run State.initial T).progOf x.thread)[x.idx]? =
                      some (Cmd.arrive bb nn) := hcm
                  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm'
                  have hXcons : (Dj).progOf x.thread = Cmd.arrive bb nn ::
                      ((Config.run State.initial T).progOf x.thread).drop (x.idx + 1) := by
                    rw [hXdrop, List.drop_eq_getElem_cons hlt0, hget0]
                  have hthread : x.thread = i :=
                    arrive_drop_thread_unique hstepj hXcons hX'drop hCi hC'i
                  have hidxeq : x.idx = (T.prog i).length - ((Dj).progOf i).length := by
                    have hXdrop' : (Dj).progOf i =
                        ((Config.run State.initial T).progOf i).drop x.idx := by
                      rw [← hthread]; exact hXdrop
                    have hlenX := congrArg List.length hXdrop'
                    have hidxX' : x.idx <
                        ((Config.run State.initial T).progOf i).length := by
                      rw [← hthread]; exact hidxX
                    have hTlen : ((Config.run State.initial T).progOf i).length =
                        (T.prog i).length := rfl
                    simp only [List.length_drop] at hlenX
                    omega
                  exact hxne (by
                    have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                    rw [hxeta, hthread, hidxeq])
    · exfalso
      have := recycleCount_succ_of_recycle b τ hCj hCj1 hrecj
      omega

/-- **L0c — fiber size = round capacity.** If `b`'s round `g` completes in the reference
trace (`g ≤` its total recycles), the fiber `F_g(b)` has exactly `n` members, `n` the
(common, L0b) parameter of its members: the round consumed exactly `n` registrations,
each a distinct program point, and every fiber member was among them. The pigeonhole
that powers both the "late" contradiction and the fullness lemma. -/
theorem genFiber_length {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g)
    (hcomplete : g ≤ recycleCount b τ (τ.length - 1))
    {η : ProgPoint} (hη : η ∈ genFiber T τ b g) {n : ℕ+}
    (hn : (T.cmdAt η).bind Cmd.count? = some n) :
    (genFiber T τ b g).length = (n : Nat) := by
  obtain ⟨p, s, Tc, I, A, n₀, hrc1, hrc2, hCp, hbst, hfull, hpark, hCp1, hall,
    hsyncD, hsurj⟩ := genFiber_round_data hτ hg hcomplete
  -- the given member pins `n` to the round count
  have hnn : n = n₀ := by
    have h := hall η hη
    rw [hn] at h
    exact Option.some.inj h
  subst hnn
  -- decoding `sync` members off the fiber
  have hdecode_sync : ∀ x ∈ genFiber T τ b g, isSyncCmd T x = true →
      ∃ nx : ℕ+, T.cmdAt x = some (.sync b nx) := by
    intro x hxF hxs
    obtain ⟨-, hbar', -⟩ := mem_genFiber.mp hxF
    simp only [isSyncCmd] at hxs
    cases hcm : T.cmdAt x with
    | none => rw [hcm] at hxs; simp at hxs
    | some cmd =>
      cases cmd with
      | read g₀ => rw [hcm] at hxs; simp at hxs
      | write g₀ => rw [hcm] at hxs; simp at hxs
      | arrive bb nn => rw [hcm] at hxs; simp at hxs
      | sync bb nn =>
        have hbb : b = bb := by
          rw [hcm] at hbar'
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar'
          exact hbar'.symm
        subst hbb
        exact ⟨nn, rfl⟩
  -- window start `w`: zero arrivals, `g - 1` recycles, all member times ahead
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ p ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ (sw.B b).arrived = 0 ∧
        recycleCount b τ w = g - 1 ∧
        (w = 0 ∨ (2 ≤ g ∧ recycleCount b τ (w - 1) = g - 2)) := by
    rcases Nat.eq_or_lt_of_le hg with hg1 | hg2
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · have h0 : recycleCount b τ 0 = 0 := by unfold recycleCount; simp
        omega
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits b τ
        (show 1 ≤ g - 1 by omega) (show g - 1 ≤ recycleCount b τ p by omega)
      obtain ⟨D, D', hD, hD', hrecD⟩ := recycle_step_of_count_lt (b := b) (τ := τ)
        (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hD'
      obtain ⟨sD, TD, ID, AD, nD, hDeq, -, -, -, hD'eq⟩ :=
        stepRecyclesBarrier_elim hstepD hrecD
      subst hD'eq
      refine ⟨q + 1, by omega, _, _, hD', rfl, ?_, by omega,
        Or.inr ⟨by omega, ?_⟩⟩
      · simp [Function.update_self, BarrierState.unconfigured]
      · simp only [Nat.add_sub_cancel]
        omega
  -- fiber times lie strictly beyond `w`
  have hlate : ∀ η' ∈ genFiber T τ b g, ∀ m, pointTime T τ η' = some m → w < m := by
    intro η' hη' m hpt
    have htime := isTimeOf_of_pointTime hτ.1 hpt
    obtain ⟨-, hbar', hgen'⟩ := mem_genFiber.mp hη'
    have hpg := pointGen_eq_of_time hbar' htime
    have hm1 : 1 ≤ m := by
      obtain ⟨-, -, j₀, -, -, hj₀, -, -, -, -⟩ := htime
      omega
    by_contra hcon
    rcases hwlow with rfl | ⟨hg2, hw2⟩
    · omega
    · have hmono : recycleCount b τ (m - 1) ≤ recycleCount b τ (w - 1) :=
        recycleCount_mono b τ (by omega)
      omega
  -- the census at the recycle instant: `A` counts the executed fiber `arrive`s
  have hcensus := arrived_census hτ hg hCw hsw hw0 hwrc hlate p hwp hrc1
    (Config.run s Tc) s hCp rfl
  have hA : A = (genFiber T τ b g).countP (arriveBy T τ p) := by
    rw [hbst] at hcensus
    simpa using hcensus
  -- every fiber `arrive` has executed by `p`
  have harr : (genFiber T τ b g).countP (arriveBy T τ p) =
      (genFiber T τ b g).countP (isArriveCmd T) := by
    refine List.countP_congr fun η' hη' => ?_
    simp only [arriveBy, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, -⟩
      exact h1
    · intro h1
      refine ⟨h1, ?_⟩
      obtain ⟨bb, nn, hcm⟩ : ∃ (bb : Barrier) (nn : ℕ+),
          T.cmdAt η' = some (.arrive bb nn) := by
        simp only [isArriveCmd] at h1
        cases hcm : T.cmdAt η' with
        | none => rw [hcm] at h1; simp at h1
        | some cmd =>
          cases cmd with
          | read g₀ => rw [hcm] at h1; simp at h1
          | write g₀ => rw [hcm] at h1; simp at h1
          | sync bb nn => rw [hcm] at h1; simp at h1
          | arrive bb nn => exact ⟨bb, nn, rfl⟩
      have hbb : b = bb := by
        obtain ⟨-, hbar', -⟩ := mem_genFiber.mp hη'
        rw [hcm] at hbar'
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar'
        exact hbar'.symm
      subst hbb
      obtain ⟨m₀, D', s₂, hm₀1, hm₀len, hptm₀, hD', hs₂, hpost, hrcm₀, -⟩ :=
        genFiber_arrive_post_count hτ hη' hcm
      rw [hptm₀]
      -- `m₀ ≠ p + 1`: post-arrive is configured, post-recycle is not
      have hmp : m₀ ≠ p + 1 := by
        intro hmeq
        subst hmeq
        rw [hD'] at hCp1
        obtain rfl := Option.some.inj hCp1
        simp only [Config.state?, Option.some.injEq] at hs₂
        subst hs₂
        simp [Function.update_self, BarrierState.unconfigured] at hpost
      have hm₀le : m₀ ≤ p := by
        by_contra hcon
        have hple : p + 1 ≤ m₀ - 1 := by omega
        have := recycleCount_mono b τ hple
        omega
      simp only [decide_eq_true_eq]
      omega
  -- the `sync` members are exactly the parked threads
  have hsync_len : (genFiber T τ b g).countP (isSyncCmd T) = I.length := by
    have hndF : ((genFiber T τ b g).filter (isSyncCmd T)).Nodup :=
      (genFiber_nodup T τ b g).filter _
    have hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T)
        (Config.run s Tc) := by
      refine reaches_of_chain_getElem hτ.1.1.subtrace ?_ p _ hCp
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact hτ.1.2
    have hwf := WF_of_reaches hreach
    have hndI : I.Nodup := by
      have h := hwf.2.2.1 b
      rw [hbst] at h
      exact h
    rw [List.countP_eq_length_filter]
    rw [← List.toFinset_card_of_nodup hndF, ← List.toFinset_card_of_nodup hndI]
    refine Finset.card_bij (fun η' _ => η'.thread) ?_ ?_ ?_
    · intro η' hη'
      simp only [List.mem_toFinset, List.mem_filter] at hη'
      obtain ⟨hmemF, hsync⟩ := hη'
      obtain ⟨nx, hcm⟩ := hdecode_sync η' hmemF hsync
      exact List.mem_toFinset.mpr ((hsyncD η' hmemF nx hcm).1)
    · intro x hx y hy hxy
      simp only [List.mem_toFinset, List.mem_filter] at hx hy
      obtain ⟨hxF, hxs⟩ := hx
      obtain ⟨hyF, hys⟩ := hy
      obtain ⟨nx, hcmx⟩ := hdecode_sync x hxF hxs
      obtain ⟨ny, hcmy⟩ := hdecode_sync y hyF hys
      obtain ⟨-, hptx⟩ := hsyncD x hxF nx hcmx
      obtain ⟨-, hpty⟩ := hsyncD y hyF ny hcmy
      have hxi : x.idx < (T.prog x.thread).length :=
        ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
      have hyi : y.idx < (T.prog y.thread).length :=
        ((mem_progPoints_iff T y).mp (mem_genFiber.mp hyF).1).2
      rw [hxy] at hptx hxi
      have hdd := hptx.symm.trans hpty
      have hlen := congrArg List.length hdd
      simp only [List.length_drop] at hlen
      have hxid : x.idx = y.idx := by omega
      have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
      have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
      rw [hxeta, hyeta, hxy, hxid]
    · intro i hi
      obtain ⟨η', hη'F, hth, nn, hcm⟩ := hsurj i (List.mem_toFinset.mp hi)
      refine ⟨η', ?_, hth⟩
      simp only [List.mem_toFinset, List.mem_filter]
      refine ⟨hη'F, ?_⟩
      simp [isSyncCmd, hcm]
  -- partition the fiber into `sync`s and `arrive`s
  have hpartition : (genFiber T τ b g).length =
      (genFiber T τ b g).countP (isSyncCmd T) +
      (genFiber T τ b g).countP (isArriveCmd T) := by
    rw [List.length_eq_countP_add_countP (isSyncCmd T)]
    congr 1
    refine List.countP_congr fun η' hη' => ?_
    obtain ⟨-, hbar', -⟩ := mem_genFiber.mp hη'
    cases hcm : T.cmdAt η' with
    | none => rw [hcm] at hbar'; exact absurd hbar' (by simp)
    | some cmd =>
      cases cmd with
      | read g₀ => rw [hcm] at hbar'; simp [Cmd.barrier?] at hbar'
      | write g₀ => rw [hcm] at hbar'; simp [Cmd.barrier?] at hbar'
      | sync bb nn => simp [isSyncCmd, isArriveCmd, hcm]
      | arrive bb nn => simp [isSyncCmd, isArriveCmd, hcm]
  rw [hpartition, hsync_len, ← harr, ← hA]
  exact hfull

/-- Sync members of a completed round's fiber have pairwise-distinct threads: both are
woken by the same recycle with control at themselves, so equal threads force equal
positions. -/
theorem genFiber_sync_thread_inj {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {g : Nat} (hg : 1 ≤ g)
    (hcomplete : g ≤ recycleCount b τ (τ.length - 1))
    {x y : ProgPoint} (hx : x ∈ genFiber T τ b g) (hy : y ∈ genFiber T τ b g)
    {nx ny : ℕ+} (hcx : T.cmdAt x = some (.sync b nx))
    (hcy : T.cmdAt y = some (.sync b ny))
    (hthread : x.thread = y.thread) : x = y := by
  obtain ⟨p, s, Tc, I, A, n, -, -, -, -, -, -, -, -, hsyncD, -⟩ :=
    genFiber_round_data hτ hg hcomplete
  obtain ⟨-, hpx⟩ := hsyncD x hx nx hcx
  obtain ⟨-, hpy⟩ := hsyncD y hy ny hcy
  have hxi : x.idx < (T.prog x.thread).length :=
    ((mem_progPoints_iff T x).mp (mem_genFiber.mp hx).1).2
  have hyi : y.idx < (T.prog y.thread).length :=
    ((mem_progPoints_iff T y).mp (mem_genFiber.mp hy).1).2
  rw [hthread] at hpx hxi
  have hdd := hpx.symm.trans hpy
  have hlen := congrArg List.length hdd
  simp only [List.length_drop] at hlen
  have hxid : x.idx = y.idx := by omega
  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
  have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
  rw [hxeta, hyeta, hthread, hxid]

/-- **L0e — the partial round is under-full.** The fiber of the round past the last
completed one has strictly fewer members than its count parameter: all its members are
executed `arrive`s (the trace ends `done`), the census equates their number with the
final arrival counter, and the `done` step's premise keeps every configured barrier
strictly under-full. -/
theorem genFiber_partial_length_lt {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : Barrier} {η : ProgPoint}
    (hη : η ∈ genFiber T τ b (recycleCount b τ (τ.length - 1) + 1)) {n : ℕ+}
    (hn : (T.cmdAt η).bind Cmd.count? = some n) :
    (genFiber T τ b (recycleCount b τ (τ.length - 1) + 1)).length < (n : ℕ) := by
  obtain ⟨sd, hdone⟩ := hτ.2
  set R := recycleCount b τ (τ.length - 1) with hR
  obtain ⟨hmem, hbar, hgen⟩ := mem_genFiber.mp hη
  -- η is an `arrive` (L0d) with parameter `n`
  obtain ⟨nn, hcm⟩ : ∃ nn : ℕ+, T.cmdAt η = some (.arrive b nn) := by
    cases hcm : T.cmdAt η with
    | none => rw [hcm] at hbar; exact absurd hbar (by simp)
    | some cmd =>
      cases cmd with
      | read g₀ => rw [hcm] at hbar; simp [Cmd.barrier?] at hbar
      | write g₀ => rw [hcm] at hbar; simp [Cmd.barrier?] at hbar
      | sync bb nx =>
        exfalso
        have hbb : b = bb := by
          rw [hcm] at hbar
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar
          exact hbar.symm
        subst hbb
        exact genFiber_partial_no_sync hτ hη nx hcm
      | arrive bb nx =>
        have hbb : b = bb := by
          rw [hcm] at hbar
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar
          exact hbar.symm
        subst hbb
        exact ⟨nx, rfl⟩
  have hnn : nn = n := by
    rw [hcm] at hn
    simpa [Cmd.count?] using hn
  -- the configured count at the end of τ is `some nn`
  obtain ⟨m, D', s₂, hm1, hmlen, hptm, hD', hs₂, hpost, hrcm, -⟩ :=
    genFiber_arrive_post_count hτ hη hcm
  have hlast : τ[τ.length - 1]? = some (Config.done sd) := by
    rw [← List.getLast?_eq_getElem?]; exact hdone
  have hrcend : recycleCount b τ m = recycleCount b τ (τ.length - 1) := by
    have h1 := recycleCount_mono b τ (show m - 1 ≤ m by omega)
    have h2 := recycleCount_mono b τ (show m ≤ τ.length - 1 by omega)
    omega
  have hcount := count_persists hτ.1.1.subtrace (τ.length - 1) m (by omega) hrcend
    hD' hs₂ hpost hlast rfl
  -- the final `done` step keeps every configured barrier strictly under-full
  have hlen2 : 2 ≤ τ.length := by
    by_contra hcon
    have hne : τ ≠ [] := fun h => by rw [h] at hdone; simp at hdone
    have hlen1 : τ.length = 1 := by
      have h1 : 1 ≤ τ.length := by
        cases τ with
        | nil => simp at hne
        | cons _ _ => simp
      omega
    have h0 : τ[0]? = some (Config.run State.initial T) := by
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact hτ.1.2
    rw [hlen1] at hlast
    rw [show (1 : ℕ) - 1 = 0 from rfl, h0] at hlast
    simp at hlast
  obtain ⟨Cpre, hCpre⟩ : ∃ Cpre, τ[τ.length - 2]? = some Cpre :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hClast : τ[τ.length - 2 + 1]? = some (Config.done sd) := by
    rw [show τ.length - 2 + 1 = τ.length - 1 by omega]; exact hlast
  have hstepd := chain_step hτ.1.1.subtrace hCpre hClast
  have hnofull : ∀ (b' : Barrier) (I : List ThreadId) (A : Nat) (n' : ℕ+),
      sd.B b' = ⟨I, A, some n'⟩ → I.length + A < (n' : ℕ) := by
    cases hstepd with
    | done hdone' hnofull' => exact hnofull'
  obtain ⟨Id, Ad, hsb⟩ : ∃ Id Ad, sd.B b = ⟨Id, Ad, some nn⟩ := by
    rcases hsb : sd.B b with ⟨Id, Ad, cnt⟩
    rw [hsb] at hcount
    have hcnt : cnt = some nn := hcount
    exact ⟨Id, Ad, by rw [hcnt]⟩
  have hAd := hnofull b Id Ad nn hsb
  -- the census at the final index counts the whole fiber
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ τ.length - 1 ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ (sw.B b).arrived = 0 ∧
        recycleCount b τ w = R ∧
        (w = 0 ∨ (1 ≤ R ∧ recycleCount b τ (w - 1) = R - 1)) := by
    rcases Nat.eq_zero_or_pos R with hR0 | hRpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · have h00 : recycleCount b τ 0 = 0 := by unfold recycleCount; simp
        omega
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits b τ hRpos
        (show R ≤ recycleCount b τ (τ.length - 1) by omega)
      obtain ⟨D, Dn, hD, hDn, hrecD⟩ := recycle_step_of_count_lt (b := b) (τ := τ)
        (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hDn
      obtain ⟨sD, TD, ID, AD, nD, hDeq, -, -, -, hDneq⟩ :=
        stepRecyclesBarrier_elim hstepD hrecD
      subst hDneq
      refine ⟨q + 1, by omega, _, _, hDn, rfl, ?_, by omega, Or.inr ⟨hRpos, ?_⟩⟩
      · simp [Function.update_self, BarrierState.unconfigured]
      · simp only [Nat.add_sub_cancel]
        omega
  have hlate : ∀ η' ∈ genFiber T τ b (R + 1), ∀ m', pointTime T τ η' = some m' →
      w < m' := by
    intro η' hη' m' hpt
    have htime := isTimeOf_of_pointTime hτ.1 hpt
    obtain ⟨-, hbar', hgen'⟩ := mem_genFiber.mp hη'
    have hpg := pointGen_eq_of_time hbar' htime
    have hm'1 : 1 ≤ m' := by
      obtain ⟨-, -, j₀, -, -, hj₀, -, -, -, -⟩ := htime
      omega
    by_contra hcon
    rcases hwlow with rfl | ⟨hRpos, hw2⟩
    · omega
    · have hmono : recycleCount b τ (m' - 1) ≤ recycleCount b τ (w - 1) :=
        recycleCount_mono b τ (by omega)
      omega
  have hcensus := arrived_census hτ (show 1 ≤ R + 1 by omega) hCw hsw hw0 hwrc hlate
    (τ.length - 1) hwp (by omega) (Config.done sd) sd hlast rfl
  have hfilterall : (genFiber T τ b (R + 1)).countP (arriveBy T τ (τ.length - 1)) =
      (genFiber T τ b (R + 1)).length := by
    conv_rhs => rw [← List.countP_true]
    refine List.countP_congr fun x hx => ?_
    obtain ⟨hxmem, hxbar, -⟩ := mem_genFiber.mp hx
    have hxidx : x.idx < (T.prog x.thread).length :=
      ((mem_progPoints_iff T x).mp hxmem).2
    obtain ⟨mx, hmx⟩ := exists_time_of_ends_done hτ.1 hdone hxidx
    have hptx := pointTime_eq_of_isTimeOf hmx
    have hmxlt : mx < τ.length := by
      obtain ⟨-, -, j₀, -, C₂, hj₀, -, hC₂, -, -⟩ := hmx
      have := (List.getElem?_eq_some_iff.mp hC₂).1
      omega
    obtain ⟨nx, hcmx⟩ : ∃ nx : ℕ+, T.cmdAt x = some (.arrive b nx) := by
      cases hcmx : T.cmdAt x with
      | none => rw [hcmx] at hxbar; exact absurd hxbar (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcmx] at hxbar; simp [Cmd.barrier?] at hxbar
        | write g₀ => rw [hcmx] at hxbar; simp [Cmd.barrier?] at hxbar
        | sync bb nx =>
          exfalso
          have hbb : b = bb := by
            rw [hcmx] at hxbar
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hxbar
            exact hxbar.symm
          subst hbb
          exact genFiber_partial_no_sync hτ hx nx hcmx
        | arrive bb nx =>
          have hbb : b = bb := by
            rw [hcmx] at hxbar
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hxbar
            exact hxbar.symm
          subst hbb
          exact ⟨nx, rfl⟩
    have hmx' : mx ≤ τ.length - 1 := by omega
    simp [arriveBy, isArriveCmd, hcmx, hptx, hmx']
  rw [hsb] at hcensus
  have hAd' : Ad = (genFiber T τ b (R + 1)).length := by
    rw [hfilterall] at hcensus
    exact hcensus
  have hnncast : (nn : ℕ) = (n : ℕ) := by rw [hnn]
  omega

/-- Thread `η.thread`'s control sits exactly *at* instruction `η` in configuration `C`:
its remaining program is the suffix of its initial program starting at `η.idx`
(length-based, matching the repo's program-position idiom). For a registered `sync` this
is where the pointer stays parked until the recycle. -/
def pointerAt (T : CTA) (η : ProgPoint) (C : Config) : Prop :=
  (C.progOf η.thread).length = (T.prog η.thread).length - η.idx

/-- A point whose thread's control still sits *at* it in the trace's last configuration
has no computed time. -/
theorem pointTime_none_of_pointerAt {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {C : Config} (hlast : τ'.getLast? = some C)
    {η : ProgPoint} (hat : pointerAt T η C) :
    pointTime T τ' η = none := by
  cases hpt : pointTime T τ' η with
  | none => rfl
  | some m =>
    exfalso
    obtain ⟨hm1, hmlt, hidx, C₁, C₂, hC₁, hC₂, -, hdrop2⟩ := pointTime_spec hchain h0 hpt
    have hlastidx : τ'[τ'.length - 1]? = some C := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    have hsuf := progOf_suffix_index_le hchain η.thread hC₂
      (show m ≤ τ'.length - 1 by omega) hlastidx
    have hle := suffix_length_le hsuf
    rw [hdrop2] at hle
    simp only [List.length_drop] at hle
    have hat' : (C.progOf η.thread).length = (T.prog η.thread).length - η.idx := hat
    omega


/-- **Clause 2 of `Conforms`** (paper §5.2.6, the state clause), for one barrier `b`: in
the last configuration `C` (state `s`) of the challenger trace `τ'`, with `r` recycles of
`b` so far and `F := genFiber T τ b (r+1)` the current fiber,

* `count` — if `b` is configured, its count is the parameter of every member of `F`;
* `arrived` — the arrival count is the number of `arrive`s of `F` already executed;
* `synced` — the parked list holds exactly the threads of `F`'s `sync`s whose control is
  parked at them *and which are disabled*: `pointerAt` alone cannot distinguish an
  enabled thread that has merely reached a `sync` (e.g. an idx-0 `sync` in the initial
  configuration) from one that has registered and parked — the enabled bit does;
* `unconfigured` — a `⊥` count means the pristine unconfigured state.

(The paper phrases this as dominance against `S_g`, the reference state before round
`g`'s recycle; the fiber-image form is equivalent — dominance tightens to equality at the
recycle — and avoids indexing states of `τ`.) -/
def BarrierConforms (T : CTA) (τ τ' : List Config) (C : Config) (s : State) (b : Barrier) :
    Prop :=
  (∀ n : ℕ+, (s.B b).count = some n →
    ∀ η ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
      (T.cmdAt η).bind Cmd.count? = some n) ∧
  ((s.B b).arrived =
    ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter fun η =>
      isArriveCmd T η && (pointTime T τ' η).isSome).length) ∧
  (∀ i, i ∈ (s.B b).synced ↔
    ∃ η ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
      η.thread = i ∧ (∃ n : ℕ+, T.cmdAt η = some (.sync b n)) ∧ pointerAt T η C ∧
        s.E i = false) ∧
  ((s.B b).count = none → s.B b = BarrierState.unconfigured)

/-- **The conformance invariant** `Conforms(τ, τ')` (paper §5.2.6): the challenger trace
`τ'` agrees with the successful reference trace `τ`. Clause 0: `τ'` has not errored.
Clause 1: executed instructions carry their reference generations. Clause 2: each
barrier's state is the image of its current fiber's progress (`BarrierConforms`).
Clause 3: `initRelation` edges with an executed target have an executed source, no later
— stated on generating edges; `Conforms.happensBefore_sound` lifts it to paths. -/
structure Conforms (T : CTA) (τ τ' : List Config) : Prop where
  /-- Clause 0: the challenger trace has not reached the error configuration. -/
  no_err : ∀ T'', τ'.getLast? ≠ some (Config.err T'')
  /-- Clause 1: generation agreement for every executed instruction. -/
  gen_eq : ∀ η ∈ T.progPoints, ∀ m, pointTime T τ' η = some m →
    pointGen T τ' η = pointGen T τ η
  /-- Clause 2: each barrier's state is the image of its current fiber's progress. -/
  state : ∀ C, τ'.getLast? = some C → ∀ s, C.state? = some s →
    ∀ b, BarrierConforms T τ τ' C s b
  /-- Clause 3: generating-edge soundness inside `τ'`. The conclusion asserts the
  *existence* of the source's time — the counting argument forces execution, not merely
  an ordering. -/
  edge_sound : ∀ x y, (x, y) ∈ initRelation T τ →
    ∀ m, pointTime T τ' y = some m → ∃ m' ≤ m, pointTime T τ' x = some m'
  /-- Clause 4: **closed rounds are complete** — once `b` has recycled `g` times in
  `τ'`, every member of the reference fiber `F_g(b)` has executed. Maintained at each
  recycle by the clause-2 census (the closing round was full, so it had consumed the
  entire fiber); consumed by the "late" direction of `conforms_reg_round`. -/
  rounds_complete : ∀ (b : Barrier) (g : Nat), 1 ≤ g →
    g ≤ recycleCount b τ' (τ'.length - 1) →
    ∀ η ∈ genFiber T τ b g, ∃ m, pointTime T τ' η = some m

/-- **The closure lift** (clause 3 for `happensBefore` paths): walking an `R`-path
backward from an executed endpoint pulls every node on it — in particular the source —
into the executed part of `τ'`, no later. The one place a path decomposition happens;
each `conforms_snoc` case only ever re-establishes clause 3 on generating edges. -/
theorem Conforms.happensBefore_sound {T : CTA} {τ τ' : List Config}
    (h : Conforms T τ τ') {x y : ProgPoint} (hxy : happensBefore T τ x y) :
    ∀ m, pointTime T τ' y = some m → ∃ m' ≤ m, pointTime T τ' x = some m' := by
  induction hxy with
  | refl => exact fun m hy => ⟨m, le_rfl, hy⟩
  | tail _hab hbc ih =>
    intro m hy
    obtain ⟨mb, hmb_le, hmb⟩ := h.edge_sound _ _ hbc _ hy
    obtain ⟨mx, hmx_le, hmx⟩ := ih _ hmb
    exact ⟨mx, hmx_le.trans hmb_le, hmx⟩

/-- **Base case of Theorem 6**: the singleton initial trace conforms — nothing has
executed (`pointTime` on a one-element trace is `none`), no recycles have happened, and
every barrier is unconfigured. -/
theorem conforms_init (T : CTA) (τ : List Config) :
    Conforms T τ [Config.run State.initial T] := by
  have hpt : ∀ η, pointTime T [Config.run State.initial T] η = none := by
    intro η; simp [pointTime]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- clause 0: the singleton's last configuration is `run`, not `err`
    intro T'' h
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    exact absurd h (by simp)
  · -- clause 1: vacuous — nothing has a time yet
    intro η _ m hm
    rw [hpt η] at hm
    exact absurd hm (by simp)
  · -- clause 2: the initial state is pristine and the fiber has no progress
    intro C hC s hs b
    simp only [List.getLast?_singleton, Option.some.injEq] at hC
    subst hC
    simp only [Config.state?, Option.some.injEq] at hs
    subst hs
    refine ⟨?_, ?_, ?_, fun _ => rfl⟩
    · -- `count`: unconfigured, so the premise `count = some n` is absurd
      intro n hn
      exact absurd hn (by simp [State.initial, BarrierState.unconfigured])
    · -- `arrived`: 0 = the length of an empty filter (no op has a time)
      simp only [hpt, Option.isSome_none, Bool.and_false, List.filter_false, List.length_nil]
      rfl
    · -- `synced`: `[]` on the left; on the right every thread is still enabled
      intro i
      simp only [State.initial, BarrierState.unconfigured, List.not_mem_nil, false_iff]
      rintro ⟨η, -, rfl, -, -, hE⟩
      simp at hE
  · -- clause 3: vacuous — no target has a time yet
    intro x y _ m hm
    rw [hpt y] at hm
    exact absurd hm (by simp)
  · -- clause 4: vacuous — nothing has recycled yet
    intro b g hg1 hgle η hη
    exfalso
    have h0 : recycleCount b [Config.run State.initial T]
        ([Config.run State.initial T].length - 1) = 0 := by
      unfold recycleCount; simp
    omega

/-- **The round-targeting lemma** — the `k = g` core of Theorem 6's induction step: in a
conforming trace whose last configuration satisfies the all-barriers-under-full guard, a
thread whose control sits at a barrier op `η` on `b` can only be facing round
`pointGen T τ η` (the open round index `k := r + 1` equals `η`'s reference generation
`g`). The guard is essential: without it the open round can sit *transiently full* —
an all-`arrive` round `g - 1` fully registered but not yet recycled — with `k = g - 1`.

* `k > g` ("late") is impossible: round `g` closed, so clause 4 (`rounds_complete`) says
  `η` itself executed — but then its pointer moved past `η`, contradicting `pointerAt`.
* `k < g` ("early") is impossible: `g ≥ 2`, the checker supplies `η.idx ≥ 1`
  (`idx_pos_of_check`) and, for every `c1 ∈ F_{g-1}`, a path `c1 ⤳ pred(η)`
  (`happensBefore_of_check`); `pred(η)` executed (the pointer passed it), so the closure
  lift forces each `c1` executed at τ'-generation `g - 1` (clause 1). A `sync` among
  them would have recycled `b` to depth `g - 1 > r` already; so `F_{g-1}` is
  all-`arrive`s, `r = g - 2`, and clause 2's census makes the open round hold all
  `n_{g-1} = |F_{g-1}|` of them — full, contradicting the guard.

Feeds every registration case of `conforms_snoc` and refutes the mismatch-error cases
(whose under-fullness is exactly the `CTAStep.error` guard). -/
theorem conforms_reg_round {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    (hguard : ∀ b', s.B b' = BarrierState.unconfigured ∨
      ∃ I A n, s.B b' = ⟨I, A, some n⟩ ∧ I.length + A < (n : ℕ))
    {η : ProgPoint} (hmem : η ∈ T.progPoints) {b : Barrier}
    (hbar : (T.cmdAt η).bind Cmd.barrier? = some b)
    (hat : pointerAt T η (Config.run s Tc)) :
    pointGen T τ η = recycleCount b τ' (τ'.length - 1) + 1 := by
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidxL : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hidxL
  have hgτ := pointGen_eq_of_time hbar hmτ
  have hmτlt : mτ < τ.length := by
    obtain ⟨-, -, j₀, -, C₂, hj₀, -, hC₂, -, -⟩ := hmτ
    have := (List.getElem?_eq_some_iff.mp hC₂).1
    omega
  have hchain' := htr.1
  have h0' := htr.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hat' : (Tc.prog η.thread).length = (T.prog η.thread).length - η.idx := hat
  have hηfib : η ∈ genFiber T τ b (pointGen T τ η) :=
    mem_genFiber.mpr ⟨hmem, hbar, rfl⟩
  set g := pointGen T τ η with hgdef
  set r := recycleCount b τ' (τ'.length - 1) with hrdef
  rcases Nat.lt_trichotomy g (r + 1) with hlt | heq | hgt
  · -- LATE: `g ≤ r` — the closed round consumed `η`, but its pointer is still at `η`
    exfalso
    have hg1 : 1 ≤ g := by omega
    obtain ⟨m, hpt⟩ := hconf.rounds_complete b g hg1 (by omega) η hηfib
    obtain ⟨hm1, hmlt, -, C₁, C₂, hC₁, hC₂, -, hdrop2⟩ := pointTime_spec hchain' h0' hpt
    have hsuf := progOf_suffix_index_le hchain' η.thread hC₂
      (show m ≤ τ'.length - 1 by omega) hlastidx
    have hle := suffix_length_le hsuf
    rw [hdrop2] at hle
    simp only [List.length_drop] at hle
    have hcast : ((Config.run s Tc).progOf η.thread).length =
        (Tc.prog η.thread).length := rfl
    omega
  · exact heq
  · -- EARLY: `r + 1 < g`
    exfalso
    have hg2 : 2 ≤ g := by omega
    obtain ⟨c0, hc0⟩ := genFiber_nonempty_of_succ hτ (show 1 ≤ g - 1 by omega)
      (show η ∈ genFiber T τ b (g - 1 + 1) from by
        rw [show g - 1 + 1 = g by omega]; exact hηfib)
    obtain ⟨hc0mem, hc0bar, hc0gen⟩ := mem_genFiber.mp hc0
    have hidx1 : 1 ≤ η.idx := idx_pos_of_check hcheck hc0mem hc0bar hmem hbar (by omega)
    -- `pred(η)` has executed in `τ'` (the pointer moved past it)
    obtain ⟨m3, hptc3⟩ : ∃ m3, pointTime T τ' ⟨η.thread, η.idx - 1⟩ = some m3 := by
      refine exists_pointTime_of_passed hchain' h0' hlast (by omega) ?_
      change (Tc.prog η.thread).length + (η.idx - 1 + 1) ≤ (T.prog η.thread).length
      omega
    -- every `F_{g-1}` member executed in `τ'`, at τ'-generation `g - 1`
    have hall : ∀ c1 ∈ genFiber T τ b (g - 1), ∃ m1, m1 ≤ m3 ∧
        pointTime T τ' c1 = some m1 ∧ recycleCount b τ' (m1 - 1) = g - 2 := by
      intro c1 hc1
      obtain ⟨hc1mem, hc1bar, hc1gen⟩ := mem_genFiber.mp hc1
      have hpath := happensBefore_of_check hcheck hc1mem hc1bar hmem hbar (by omega) hidx1
      obtain ⟨m1, hm1le, hm1⟩ := hconf.happensBefore_sound hpath m3 hptc3
      refine ⟨m1, hm1le, hm1, ?_⟩
      have hgen1 : pointGen T τ' c1 = pointGen T τ c1 := hconf.gen_eq c1 hc1mem m1 hm1
      have hunf := pointGen_eq_of_pointTime hc1bar hm1
      omega
    -- a `sync` in `F_{g-1}` would already have recycled `b` to depth `g - 1 > r`
    have hnosync : ∀ c1 ∈ genFiber T τ b (g - 1), ∀ nn : ℕ+,
        T.cmdAt c1 ≠ some (.sync b nn) := by
      intro c1 hc1 nn hcm
      obtain ⟨m1, hm1le, hm1, hrc1⟩ := hall c1 hc1
      obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ := pointTime_sync_recycles hchain' h0' hm1 hcm
      obtain ⟨hm1a, hm1lt, -⟩ := pointTime_spec hchain' h0' hm1
      have hCC' : τ'[m1 - 1 + 1]? = some C₂ := by
        rw [show m1 - 1 + 1 = m1 by omega]; exact hC₂
      have hsucc := recycleCount_succ_of_recycle b τ' hC₁ hCC' hrec
      have hmono := recycleCount_mono b τ' (show m1 - 1 + 1 ≤ τ'.length - 1 by omega)
      omega
    -- so the open round is exactly `g - 1` …
    have hrg : r = g - 2 := by
      obtain ⟨m1, -, hm1, hrc1⟩ := hall c0 hc0
      have hm1lt : m1 < τ'.length := (pointTime_spec hchain' h0' hm1).2.1
      have hmono := recycleCount_mono b τ' (show m1 - 1 ≤ τ'.length - 1 by omega)
      omega
    -- … and clause 2's census says it already holds the entire fiber
    have hfilter : (genFiber T τ b (g - 1)).filter (fun η' =>
        isArriveCmd T η' && (pointTime T τ' η').isSome) = genFiber T τ b (g - 1) := by
      rw [List.filter_eq_self]
      intro c1 hc1
      obtain ⟨hc1mem, hc1bar, -⟩ := mem_genFiber.mp hc1
      obtain ⟨m1, -, hm1, -⟩ := hall c1 hc1
      cases hcm : T.cmdAt c1 with
      | none => rw [hcm] at hc1bar; exact absurd hc1bar (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcm] at hc1bar; simp [Cmd.barrier?] at hc1bar
        | write g₀ => rw [hcm] at hc1bar; simp [Cmd.barrier?] at hc1bar
        | sync bb nn =>
          exfalso
          have hbb : b = bb := by
            rw [hcm] at hc1bar
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hc1bar
            exact hc1bar.symm
          subst hbb
          exact hnosync c1 hc1 nn hcm
        | arrive bb nn =>
          simp [isArriveCmd, hcm, hm1]
    -- `c0` is an `arrive` with some parameter, pinning the fiber's size
    obtain ⟨nn₀, hcm₀⟩ : ∃ nn₀ : ℕ+, T.cmdAt c0 = some (.arrive b nn₀) := by
      cases hcm : T.cmdAt c0 with
      | none => rw [hcm] at hc0bar; exact absurd hc0bar (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcm] at hc0bar; simp [Cmd.barrier?] at hc0bar
        | write g₀ => rw [hcm] at hc0bar; simp [Cmd.barrier?] at hc0bar
        | sync bb nn =>
          exfalso
          have hbb : b = bb := by
            rw [hcm] at hc0bar
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hc0bar
            exact hc0bar.symm
          subst hbb
          exact hnosync c0 hc0 nn hcm
        | arrive bb nn =>
          have hbb : b = bb := by
            rw [hcm] at hc0bar
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hc0bar
            exact hc0bar.symm
          subst hbb
          exact ⟨nn, rfl⟩
    have hτcomplete : g - 1 ≤ recycleCount b τ (τ.length - 1) := by
      have hmono := recycleCount_mono b τ (show mτ - 1 ≤ τ.length - 1 by omega)
      omega
    have hlen := genFiber_length hτ (show 1 ≤ g - 1 by omega) hτcomplete hc0
      (show (T.cmdAt c0).bind Cmd.count? = some nn₀ from by rw [hcm₀]; rfl)
    -- clause 2 at the last configuration
    obtain ⟨hcount, harr, -, -⟩ := hconf.state _ hlast s rfl b
    have hfib_idx : r + 1 = g - 1 := by omega
    rw [hfib_idx] at harr hcount
    rw [hfilter, hlen] at harr
    -- the guard at `b` is violated: the open round is full
    rcases hguard b with hbu | ⟨I', A', n', hbeq, hltn⟩
    · rw [hbu] at harr
      have hpos := nn₀.pos
      simp [BarrierState.unconfigured] at harr
      omega
    · have hn' : (T.cmdAt c0).bind Cmd.count? = some n' :=
        hcount n' (by rw [hbeq]) c0 hc0
      rw [hcm₀] at hn'
      simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hn'
      rw [hbeq] at harr
      have harr' : A' = (nn₀ : ℕ) := harr
      have hn'' : (nn₀ : ℕ) = (n' : ℕ) := by rw [hn']
      omega

/-- **The fullness pigeonhole**: in a conforming trace whose last configuration holds a
*full* round of `b`, the round has consumed the entire current fiber — every `arrive`
member has executed, and every `sync` member is parked (its thread in the synced list,
control at the member). Counting: clause 2 bounds the parked threads by the fiber's
`sync`s (thread-image) and the arrival counter by its executed `arrive`s; fullness plus
`|F| = n₀` (L0c) forces both bounds tight. A full *partial* round is impossible outright
(L0d makes it all-`arrive`s and L0e keeps it strictly under-full). -/
theorem conforms_full_fiber {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    {b : Barrier} {I : List ThreadId} {A : Nat} {n₀ : ℕ+}
    (hb : s.B b = ⟨I, A, some n₀⟩) (hfull : I.length + A = (n₀ : ℕ)) :
    ∀ η ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
      ((∃ (bb : Barrier) (nn : ℕ+), T.cmdAt η = some (.arrive bb nn)) →
        ∃ m, pointTime T τ' η = some m) ∧
      (∀ nn : ℕ+, T.cmdAt η = some (.sync b nn) →
        η.thread ∈ I ∧ pointerAt T η (Config.run s Tc)) := by
  obtain ⟨hcount, harr, hsync, -⟩ := hconf.state _ hlast s rfl b
  have hparam : ∀ x ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
      (T.cmdAt x).bind Cmd.count? = some n₀ :=
    fun x hx => hcount n₀ (by rw [hb]) x hx
  have harr' : A = ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
      fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
    rw [hb] at harr
    exact harr
  -- the fiber is nonempty (the full round has registrants, all of them members)
  obtain ⟨x₀, hx₀⟩ :
      ∃ x₀, x₀ ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1) := by
    by_contra hno
    push Not at hno
    have hFnil : genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1) = [] := by
      cases hFcase : genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1) with
      | nil => rfl
      | cons a l => exact absurd (hFcase ▸ List.mem_cons_self ..) (hno a)
    have hI0 : I = [] := by
      cases hI : I with
      | nil => rfl
      | cons t I'' =>
        exfalso
        have htI : t ∈ (s.B b).synced := by
          rw [hb, hI]; exact List.mem_cons_self ..
        obtain ⟨x, hxF, -, -, -, -⟩ := (hsync t).mp htI
        rw [hFnil] at hxF
        simp at hxF
    rw [hFnil] at harr'
    simp at harr'
    have hpos := n₀.pos
    rw [hI0] at hfull
    simp at hfull
    omega
  by_cases hcomp : recycleCount b τ' (τ'.length - 1) + 1 ≤
      recycleCount b τ (τ.length - 1)
  case neg =>
    -- a full partial round is impossible: all-`arrive`s (L0d) yet strictly under-full
    -- in the reference (L0e)
    exfalso
    have hRge : recycleCount b τ' (τ'.length - 1) ≤ recycleCount b τ (τ.length - 1) := by
      obtain ⟨hx₀mem, hx₀bar, -⟩ := mem_genFiber.mp hx₀
      obtain ⟨sd, hdone⟩ := hτ.2
      have hidx : x₀.idx < (T.prog x₀.thread).length :=
        ((mem_progPoints_iff T x₀).mp hx₀mem).2
      obtain ⟨mx, hmx⟩ := exists_time_of_ends_done hτ.1 hdone hidx
      have hpg := pointGen_eq_of_time hx₀bar hmx
      have hgen := (mem_genFiber.mp hx₀).2.2
      have hmxlt : mx < τ.length := by
        obtain ⟨-, -, j₀, -, C₂, hj₀, -, hC₂, -, -⟩ := hmx
        have := (List.getElem?_eq_some_iff.mp hC₂).1
        omega
      have := recycleCount_mono b τ (show mx - 1 ≤ τ.length - 1 by omega)
      omega
    have hreq : recycleCount b τ' (τ'.length - 1) = recycleCount b τ (τ.length - 1) := by
      omega
    rw [hreq] at hx₀ harr' hparam
    have hlt := genFiber_partial_length_lt hτ hx₀ (hparam x₀ hx₀)
    have hI0 : I = [] := by
      cases hI : I with
      | nil => rfl
      | cons t I'' =>
        exfalso
        have htI : t ∈ (s.B b).synced := by
          rw [hb, hI]; exact List.mem_cons_self ..
        obtain ⟨x, hxF, -, hsx, -, -⟩ := (hsync t).mp htI
        obtain ⟨nx, hcx⟩ := hsx
        rw [hreq] at hxF
        exact genFiber_partial_no_sync hτ hxF nx hcx
    have hAle : A ≤ (genFiber T τ b (recycleCount b τ (τ.length - 1) + 1)).length := by
      rw [harr']
      exact List.length_filter_le _ _
    rw [hI0] at hfull
    simp at hfull
    omega
  case pos =>
    -- the complete round: `|F| = n₀`, and the two counting bounds are tight
    have hg1 : 1 ≤ recycleCount b τ' (τ'.length - 1) + 1 := by omega
    have hlen := genFiber_length hτ hg1 hcomp hx₀ (hparam x₀ hx₀)
    have hndF : ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
        (isSyncCmd T)).Nodup :=
      (genFiber_nodup T τ b _).filter _
    have h0 : τ'[0]? = some (Config.run State.initial T) := by
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact htr.2
    have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    have hreach := reaches_of_chain_getElem htr.1 h0 (τ'.length - 1) _ hlastidx
    have hwf := WF_of_reaches hreach
    have hndI : I.Nodup := by
      have h := hwf.2.2.1 b
      rw [hb] at h
      exact h
    have hcardI : I.toFinset.card = I.length := List.toFinset_card_of_nodup hndI
    have hcardsync : ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
        (isSyncCmd T)).toFinset.card =
        (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP (isSyncCmd T) := by
      rw [List.toFinset_card_of_nodup hndF]
      exact List.countP_eq_length_filter.symm
    have hIsub : I.toFinset ⊆
        (((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
          (isSyncCmd T)).toFinset.image ProgPoint.thread) := by
      intro i hi
      have hiI : i ∈ (s.B b).synced := by
        rw [hb]; exact List.mem_toFinset.mp hi
      obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hiI
      rw [Finset.mem_image]
      refine ⟨x, ?_, hthx⟩
      rw [List.mem_toFinset, List.mem_filter]
      obtain ⟨nx, hcx⟩ := hsx
      exact ⟨hxF, by simp [isSyncCmd, hcx]⟩
    have hIle : I.length ≤
        (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP (isSyncCmd T) := by
      calc I.length = I.toFinset.card := hcardI.symm
        _ ≤ _ := Finset.card_le_card hIsub
        _ ≤ _ := Finset.card_image_le
        _ = _ := hcardsync
    have harrc : A = (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP
        (fun η => isArriveCmd T η && (pointTime T τ' η).isSome) := by
      rw [List.countP_eq_length_filter]
      exact harr'
    have hAle : A ≤ (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP
        (isArriveCmd T) := by
      rw [harrc]
      exact List.countP_mono_left fun x hx h => by
        simp only [Bool.and_eq_true] at h
        exact h.1
    have hpartition : (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).length =
        (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP (isSyncCmd T) +
        (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP
          (isArriveCmd T) := by
      rw [List.length_eq_countP_add_countP (isSyncCmd T)]
      congr 1
      refine List.countP_congr fun x hx => ?_
      obtain ⟨-, hxbar, -⟩ := mem_genFiber.mp hx
      cases hcmx : T.cmdAt x with
      | none => rw [hcmx] at hxbar; exact absurd hxbar (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcmx] at hxbar; simp [Cmd.barrier?] at hxbar
        | write g₀ => rw [hcmx] at hxbar; simp [Cmd.barrier?] at hxbar
        | sync bb nx => simp [isSyncCmd, isArriveCmd, hcmx]
        | arrive bb nx => simp [isSyncCmd, isArriveCmd, hcmx]
    have hIeq : I.length =
        (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP (isSyncCmd T) := by
      omega
    have hAeq : A = (genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).countP
        (isArriveCmd T) := by
      omega
    intro η hη
    refine ⟨?_, ?_⟩
    · rintro ⟨bb, nn, hcm⟩
      have hqp := countP_eq_all
        (l := genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1))
        (p := fun x => isArriveCmd T x && (pointTime T τ' x).isSome)
        (q := isArriveCmd T)
        (fun x hx h => by
          simp only [Bool.and_eq_true] at h
          exact h.1)
        (by omega) η hη (by simp [isArriveCmd, hcm])
      simp only [Bool.and_eq_true] at hqp
      obtain ⟨-, hsome⟩ := hqp
      exact Option.isSome_iff_exists.mp hsome
    · intro nn hcm
      have himg : (((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
          (isSyncCmd T)).toFinset.image ProgPoint.thread) = I.toFinset := by
        symm
        refine Finset.eq_of_subset_of_card_le hIsub ?_
        calc (((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
              (isSyncCmd T)).toFinset.image ProgPoint.thread).card
            ≤ _ := Finset.card_image_le
          _ = _ := hcardsync
          _ = I.length := hIeq.symm
          _ = I.toFinset.card := hcardI.symm
      have hηimg : η.thread ∈
          (((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
            (isSyncCmd T)).toFinset.image ProgPoint.thread) := by
        rw [Finset.mem_image]
        refine ⟨η, ?_, rfl⟩
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨hη, by simp [isSyncCmd, hcm]⟩
      have hηI : η.thread ∈ I := by
        rw [himg] at hηimg
        exact List.mem_toFinset.mp hηimg
      refine ⟨hηI, ?_⟩
      have hηsy : η.thread ∈ (s.B b).synced := by rw [hb]; exact hηI
      obtain ⟨x, hxF, hthx, hsx, hpx, -⟩ := (hsync η.thread).mp hηsy
      obtain ⟨nx, hcx⟩ := hsx
      have hxη : x = η :=
        genFiber_sync_thread_inj hτ hg1 hcomp hxF hη hcx hcm hthx
      rw [← hxη]
      exact hpx

/-- **Theorem 6, induction step** (paper §5.2.6): extending a conforming trace by one CTA
step preserves conformance. Case analysis on `hstep`:

* `interleave`/`read_noop`,`write_noop` — no barrier effect; clause 3's new target
  receives only its program-order edge.
* `interleave`/registration (`arrive_configure`, `arrive_register`, `sync_configure`,
  `sync_block`) — `conforms_reg_round` pins the round to the op's reference generation;
  clauses 1/2 update mechanically; an `arrive`'s only incoming generating edge is
  program order.
* `recycle` — the round was full, so `conforms_full_fiber` identifies the woken syncs
  with the fiber's syncs and the counted arrives with the fiber's arrives; the completing
  syncs get their times (= this step), satisfying their program-order, `arrive→sync`,
  and (mutually, at equal time) `sync↔sync` edges; the barrier resets, and the *next*
  fiber has no executed members yet (clause 1), re-establishing clause 2.
* `done` — state and times unchanged.
* `error` — impossible: the guard supplies all-barriers-under-full, `conforms_reg_round`
  pins the erroring op's round to its reference generation, and clause 2's `count` says
  the configured count is that fiber's parameter — matching the op's own (L0b), so
  neither `*_err_count` premise can hold. -/
theorem conforms_snoc {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {C C' : Config} (hlast : τ'.getLast? = some C) (hstep : CTAStep C C') :
    Conforms T τ (τ' ++ [C']) := by
  -- ## Preamble: the appended trace and its bookkeeping
  have hne : τ' ≠ [] := fun h => by rw [h] at hlast; simp at hlast
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  have hchain : List.IsChain CTAStep τ' := htr.1
  have h0 : τ'.head? = some (Config.run State.initial T) := htr.2
  have h0idx : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact h0
  have hchainσ : List.IsChain CTAStep (τ' ++ [C']) := by
    refine List.IsChain.append hchain (List.isChain_singleton _) ?_
    intro x hx y hy
    rw [Option.mem_def, hlast, Option.some.injEq] at hx
    rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hy
    rw [← hx, ← hy]
    exact hstep
  have h0σ : (τ' ++ [C']).head? = some (Config.run State.initial T) := by
    rw [List.head?_append_of_ne_nil _ hne]; exact h0
  have hlastidx : τ'[τ'.length - 1]? = some C := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hσlast : (τ' ++ [C']).length - 1 = τ'.length := by simp
  have hσN1 : (τ' ++ [C'])[τ'.length - 1]? = some C := by
    rw [List.getElem?_append_left (by omega)]; exact hlastidx
  have hσN : (τ' ++ [C'])[τ'.length]? = some C' := List.getElem?_concat_length
  obtain ⟨s, Tc, rfl⟩ : ∃ sx Tcx, C = Config.run sx Tcx := by
    cases hstep <;> exact ⟨_, _, rfl⟩
  have hreach := reaches_of_chain_getElem hchain h0idx (τ'.length - 1) _ hlastidx
  have hwf := WF_of_reaches hreach
  have hei : s.EnabledInv := by
    have hall := enabledInv_chain hchain h0 (by
      intro sx hsx
      simp only [Config.state?, Option.some.injEq] at hsx
      subst hsx
      exact State.EnabledInv.initial)
    exact hall _ (List.mem_of_mem_getLast? hlast) s rfl
  -- new-time decomposition
  have htime_cases : ∀ (η : ProgPoint) (m : Nat),
      pointTime T (τ' ++ [C']) η = some m →
      pointTime T τ' η = some m ∨
      (pointTime T τ' η = none ∧ m = τ'.length ∧
        η.idx < (T.prog η.thread).length ∧
        Tc.prog η.thread = (T.prog η.thread).drop η.idx ∧
        C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1)) := by
    intro η m hpt
    rcases pointTime_append_cases hne hpt with h | ⟨hnone, hm⟩
    · exact Or.inl h
    · subst hm
      obtain ⟨hm1, hmlt, hidx, C₁, C₂, hC₁, hC₂, hd1, hd2⟩ :=
        pointTime_spec hchainσ h0σ hpt
      rw [hσN1] at hC₁
      obtain rfl := Option.some.inj hC₁
      rw [hσN] at hC₂
      obtain rfl := Option.some.inj hC₂
      exact Or.inr ⟨hnone, rfl, hidx, hd1, hd2⟩
  -- old times keep their generations
  have hgen_old : ∀ (η : ProgPoint) (m : Nat), pointTime T τ' η = some m →
      pointGen T (τ' ++ [C']) η = pointGen T τ η := by
    intro η m hpt
    have hmem : η ∈ T.progPoints := by
      obtain ⟨-, -, hidx, -⟩ := pointTime_spec hchain h0 hpt
      exact (mem_progPoints_iff T η).mpr ⟨mem_ids_of_idx_lt T hidx, hidx⟩
    have hold := hconf.gen_eq η hmem m hpt
    have hσpt := pointTime_append_some (C' := C') hpt
    have hmlt : m < τ'.length := (pointTime_spec hchain h0 hpt).2.1
    cases hbar : (T.cmdAt η).bind Cmd.barrier? with
    | none =>
      simp only [pointGen, hbar]
    | some b =>
      have h1 := pointGen_eq_of_pointTime hbar hσpt
      have h2 := pointGen_eq_of_pointTime hbar hpt
      have hrc : recycleCount b (τ' ++ [C']) (m - 1) = recycleCount b τ' (m - 1) :=
        recycleCount_append b τ' C' (by omega)
      rw [h1, hrc, ← h2]
      exact hold
  -- old edges keep their soundness
  have hedge_old : ∀ x y, (x, y) ∈ initRelation T τ → ∀ (m : Nat),
      pointTime T τ' y = some m →
      ∃ mx ≤ m, pointTime T (τ' ++ [C']) x = some mx := by
    intro x y hxy m hpt
    obtain ⟨mx, hle, hx⟩ := hconf.edge_sound x y hxy m hpt
    exact ⟨mx, hle, pointTime_append_some hx⟩
  -- a newly executed instruction's program-order predecessor already executed
  have hedge_new_po : ∀ (y : ProgPoint), 1 ≤ y.idx →
      y.idx < (T.prog y.thread).length →
      Tc.prog y.thread = (T.prog y.thread).drop y.idx →
      ∃ mx ≤ τ'.length,
        pointTime T (τ' ++ [C']) ⟨y.thread, y.idx - 1⟩ = some mx := by
    intro y hidx1 hidxL hdrop
    obtain ⟨mx, hmx⟩ : ∃ mx, pointTime T τ' ⟨y.thread, y.idx - 1⟩ = some mx := by
      refine exists_pointTime_of_passed hchain h0 hlast (i := y.thread)
        (k := y.idx - 1) (by omega) ?_
      change (Tc.prog y.thread).length + (y.idx - 1 + 1) ≤ (T.prog y.thread).length
      rw [hdrop]
      simp only [List.length_drop]
      omega
    have hmlt : mx < τ'.length := (pointTime_spec hchain h0 hmx).2.1
    exact ⟨mx, by omega, pointTime_append_some hmx⟩
  -- per-barrier recycle-count bookkeeping across the appended step
  have hrc_same : ∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = false →
      recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) =
      recycleCount b τ' (τ'.length - 1) := by
    intro b hnr
    rw [hσlast, show τ'.length = (τ'.length - 1) + 1 by omega]
    have hσN' : (τ' ++ [C'])[τ'.length - 1 + 1]? = some C' := by
      rw [show τ'.length - 1 + 1 = τ'.length by omega]; exact hσN
    rw [recycleCount_succ_of_not_recycle b hσN1 hσN' hnr]
    exact recycleCount_append b τ' C' (by omega)
  have hrc_incr : ∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = true →
      recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) =
      recycleCount b τ' (τ'.length - 1) + 1 := by
    intro b hr
    rw [hσlast, show τ'.length = (τ'.length - 1) + 1 by omega]
    have hσN' : (τ' ++ [C'])[τ'.length - 1 + 1]? = some C' := by
      rw [show τ'.length - 1 + 1 = τ'.length by omega]; exact hσN
    rw [recycleCount_succ_of_recycle b (τ' ++ [C']) hσN1 hσN' hr]
    exact congrArg (· + 1) (recycleCount_append b τ' C' (by omega))
  -- assemblers for the invariant's clauses
  have hgen_all :
      (∀ (η : ProgPoint), pointTime T τ' η = none →
        η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) →
        pointGen T (τ' ++ [C']) η = pointGen T τ η) →
      ∀ η ∈ T.progPoints, ∀ m, pointTime T (τ' ++ [C']) η = some m →
        pointGen T (τ' ++ [C']) η = pointGen T τ η := by
    intro hnew η _ m hpt
    rcases htime_cases η m hpt with hold | ⟨hnone, -, hidx, hd1, hd2⟩
    · exact hgen_old η m hold
    · exact hnew η hnone hidx hd1 hd2
  have hedge_all :
      (∀ (y : ProgPoint) (bb : Barrier) (nb : ℕ+), T.cmdAt y = some (.sync bb nb) →
        y.idx < (T.prog y.thread).length →
        Tc.prog y.thread = (T.prog y.thread).drop y.idx →
        C'.progOf y.thread = (T.prog y.thread).drop (y.idx + 1) →
        ∀ x, x ∈ T.progPoints → (T.cmdAt x).bind Cmd.barrier? = some bb →
          pointGen T τ x = pointGen T τ y →
          ∃ mx ≤ τ'.length, pointTime T (τ' ++ [C']) x = some mx) →
      ∀ x y, (x, y) ∈ initRelation T τ → ∀ m,
        pointTime T (τ' ++ [C']) y = some m →
        ∃ mx ≤ m, pointTime T (τ' ++ [C']) x = some mx := by
    intro hbarnew x y hxy m hpt
    rcases htime_cases y m hpt with hold | ⟨hnone, hm, hidx, hd1, hd2⟩
    · exact hedge_old x y hxy m hold
    · subst hm
      obtain ⟨hxpts, hypts, hcase⟩ := initRelation_cases hxy
      rcases hcase with hpo | ⟨bb, nb, hysync, hxbar, hgenxy⟩
      · subst hpo
        exact hedge_new_po ⟨x.thread, x.idx + 1⟩ (by simp) hidx hd1
      · exact hbarnew y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
  have hrounds_all :
      (∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = true →
        ∀ η ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
          ∃ m, pointTime T (τ' ++ [C']) η = some m) →
      ∀ (b : Barrier) (g : Nat), 1 ≤ g →
        g ≤ recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) →
        ∀ η ∈ genFiber T τ b g, ∃ m, pointTime T (τ' ++ [C']) η = some m := by
    intro hnew b g hg1 hgle η hη
    cases hrb : stepRecyclesBarrier b (Config.run s Tc) C' with
    | false =>
      rw [hrc_same b hrb] at hgle
      obtain ⟨m, hm⟩ := hconf.rounds_complete b g hg1 hgle η hη
      exact ⟨m, pointTime_append_some hm⟩
    | true =>
      rw [hrc_incr b hrb] at hgle
      rcases Nat.lt_or_ge g (recycleCount b τ' (τ'.length - 1) + 1) with hlt | hge
      · obtain ⟨m, hm⟩ := hconf.rounds_complete b g hg1 (by omega) η hη
        exact ⟨m, pointTime_append_some hm⟩
      · have hgeq : g = recycleCount b τ' (τ'.length - 1) + 1 := by omega
        subst hgeq
        exact hnew b hrb η hη
  -- the arrival-census filter is stable when the step executes no `arrive` on `b`
  have hfilter_same : ∀ (b : Barrier) (g : Nat),
      (∀ η ∈ genFiber T τ b g, ∀ (bb : Barrier) (nn : ℕ+),
        T.cmdAt η = some (.arrive bb nn) →
        pointTime T (τ' ++ [C']) η = some τ'.length → False) →
      ((genFiber T τ b g).filter fun η =>
        isArriveCmd T η && (pointTime T (τ' ++ [C']) η).isSome).length =
      ((genFiber T τ b g).filter fun η =>
        isArriveCmd T η && (pointTime T τ' η).isSome).length := by
    intro b g hnonew
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    refine List.countP_congr fun η hη => ?_
    cases hcm : T.cmdAt η with
    | none => simp [isArriveCmd, hcm]
    | some cmd =>
      cases cmd with
      | read g₀ => simp [isArriveCmd, hcm]
      | write g₀ => simp [isArriveCmd, hcm]
      | sync bb nn => simp [isArriveCmd, hcm]
      | arrive bb nn =>
        simp only [isArriveCmd, hcm, Bool.true_and]
        constructor
        · intro hsome
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
          rcases pointTime_append_cases hne hm with hold | ⟨-, hmN⟩
          · rw [hold]; rfl
          · exfalso
            subst hmN
            exact hnonew η hη bb nn hcm hm
        · intro hsome
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
          rw [pointTime_append_some (C' := C') hm]
          rfl
  -- ## The step analysis
  cases hstep with
  | @interleave _ sn _ t P' ht hbar hth =>
    -- the guard keeps every barrier under-full: this step recycles nothing
    have hnorec : ∀ b, stepRecyclesBarrier b (Config.run s Tc)
        (Config.run sn (Tc.set t ht P')) = false := by
      intro b
      have hnf : (s.B b).isFull = false := by
        rcases hbar b with hu | ⟨I, A, n, hcfg, hlt⟩
        · rw [hu]; rfl
        · rw [hcfg]; simp only [BarrierState.isFull]
          exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
      simp [stepRecyclesBarrier, Config.state?, hnf]
    -- a dropped head belongs to the stepping thread
    have hident_thread : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        (Config.run sn (Tc.set t ht P')).progOf η.thread =
          (T.prog η.thread).drop (η.idx + 1) →
        η.thread = t := by
      intro η hidx hd1 hd2
      by_contra hηt
      have hsame : (Tc.set t ht P').prog η.thread = Tc.prog η.thread := by
        simp [WeftCommon.CTA.set, Function.update_of_ne hηt]
      have hd2' : (Tc.set t ht P').prog η.thread =
          (T.prog η.thread).drop (η.idx + 1) := hd2
      rw [hsame, hd1] at hd2'
      have hlen := congrArg List.length hd2'
      simp only [List.length_drop] at hlen
      omega
    -- ... and is the thread's static head command
    have hident_cmd : ∀ (η : ProgPoint) (c₀ : Cmd) (rest : Prog), η.thread = t →
        Tc.prog t = c₀ :: rest →
        η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        T.cmdAt η = some c₀ := by
      intro η c₀ rest hηt hcons hidx hd1
      rw [hηt] at hd1 hidx
      have hdd : (T.prog t).drop η.idx =
          (T.prog t)[η.idx]'hidx :: (T.prog t).drop (η.idx + 1) :=
        List.drop_eq_getElem_cons hidx
      rw [← hd1, hcons] at hdd
      injection hdd with hhead htail
      have hgoal : (T.prog η.thread)[η.idx]? = some c₀ := by
        rw [hηt, List.getElem?_eq_getElem hidx, ← hhead]
      exact hgoal
    -- the executing point is pinned to the head position
    have huniq : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        (Config.run sn (Tc.set t ht P')).progOf η.thread =
          (T.prog η.thread).drop (η.idx + 1) →
        η = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
      intro η hidx hd1 hd2
      have hηt := hident_thread η hidx hd1 hd2
      rw [hηt] at hd1 hidx
      have hlen := congrArg List.length hd1
      simp only [List.length_drop] at hlen
      have hidxeq : η.idx = (T.prog t).length - (Tc.prog t).length := by omega
      have hηeta : η = ⟨η.thread, η.idx⟩ := rfl
      rw [hηeta, hηt, hidxeq]
    -- a thread whose head is not a `sync` is enabled
    have ht_enabled_of_head : ∀ (c₀ : Cmd) (rest : Prog), Tc.prog t = c₀ :: rest →
        (∀ bx (nx : ℕ+), c₀ ≠ Cmd.sync bx nx) → s.E t = true := by
      intro c₀ rest hcons hnsync
      by_contra hf
      rw [Bool.not_eq_true] at hf
      obtain ⟨b', hib'⟩ := hei t hf
      rcases hsb' : s.B b' with ⟨I', A', cnt'⟩
      cases cnt' with
      | none =>
        obtain ⟨hI0, -⟩ := hwf.2.1 b' I' A' hsb'
        rw [hsb'] at hib'
        have hib'' : t ∈ I' := hib'
        rw [hI0] at hib''
        simp at hib''
      | some n' =>
        have hpk := (hwf.1 b' I' A' n' hsb').2.1 t (by rw [hsb'] at hib'; exact hib')
        rw [hcons] at hpk
        simp only [List.head?_cons, Option.some.injEq] at hpk
        exact hnsync b' n' hpk
    -- pointer positions of other threads are untouched
    have hpointer_ne : ∀ (x : ProgPoint) (sl : State) (P₂ : Prog) (htx : t ∈ Tc.ids),
        x.thread ≠ t →
        (pointerAt T x (Config.run sl (Tc.set t htx P₂)) ↔
          pointerAt T x (Config.run s Tc)) := by
      intro x sl P₂ htx hxt
      have hsame : (Tc.set t htx P₂).prog x.thread = Tc.prog x.thread := by
        simp [WeftCommon.CTA.set, Function.update_of_ne hxt]
      simp [pointerAt, WeftCommon.Config.progOf, hsame]
    obtain ⟨Pt, hPt⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPt] at hth
    cases hth with
    | @read_noop _ _ g₀ _ =>
      have hte : s.E t = true := ht_enabled_of_head _ _ hPt (by intro bx nx h; cases h)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hcm := hident_cmd η _ _ hηt hPt hidx hd1
        have hbarn : (T.cmdAt η).bind Cmd.barrier? = none := by rw [hcm]; rfl
        simp only [pointGen, hbarn]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same b (hnorec b)]
          exact hcount
        · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
          · exact harr
          · intro η hη bb nn hcm hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              exact absurd (Option.some.inj hcm') (by simp)
        · intro i
          rw [hrc_same b (hnorec b)]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exfalso
        have hηt := hident_thread y hidx hd1 hd2
        have hcm' := hident_cmd y _ _ hηt hPt hidx hd1
        rw [hysync] at hcm'
        exact absurd (Option.some.inj hcm') (by simp)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
    | @write_noop _ _ g₀ _ =>
      have hte : s.E t = true := ht_enabled_of_head _ _ hPt (by intro bx nx h; cases h)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hcm := hident_cmd η _ _ hηt hPt hidx hd1
        have hbarn : (T.cmdAt η).bind Cmd.barrier? = none := by rw [hcm]; rfl
        simp only [pointGen, hbarn]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same b (hnorec b)]
          exact hcount
        · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
          · exact harr
          · intro η hη bb nn hcm hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              exact absurd (Option.some.inj hcm') (by simp)
        · intro i
          rw [hrc_same b (hnorec b)]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exfalso
        have hηt := hident_thread y hidx hd1 hd2
        have hcm' := hident_cmd y _ _ hηt hPt hidx hd1
        rw [hysync] at hcm'
        exact absurd (Option.some.inj hcm') (by simp)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
    | @arrive_configure _ _ ba na _ he hbcfg =>
      -- the newly executing point: `t`'s head `arrive ba na`
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive ba na :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hbarN : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [hcmdN']
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmemN hbarN hatN
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmemN, hbarN, hrr⟩
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T
          (τ' ++ [Config.run
            { s with B := Function.update s.B ba ⟨[], 1, some na⟩ } (Tc.set t ht P')])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hbarN hmN
          rw [hpgσ, hrr]
          have hrca := recycleCount_append ba τ'
            (Config.run { s with B := Function.update s.B ba ⟨[], 1, some na⟩ }
              (Tc.set t ht P'))
            (j := τ'.length - 1) (by omega)
          omega
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            have hna : na = n := by
              have h : (Function.update s.B b ⟨[], 1, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ
              (show 1 ≤ recycleCount b τ' (τ'.length - 1) + 1 by omega) hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same b (hnorec b)]
            have harr0 : (0 : ℕ) =
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              have h := harr
              rw [hbcfg] at h
              exact h
            have hLHS : ((Function.update s.B b ⟨[], 1, some na⟩) b).arrived = 1 := by
              rw [Function.update_self]
            have hcnt_new :
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η &&
                    (pointTime T (τ' ++ [Config.run
                      { s with B := Function.update s.B b ⟨[], 1, some na⟩ }
                      (Tc.set t ht P')]) η).isSome).length =
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length + 1 := by
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              refine countP_succ_of_unique (genFiber_nodup T τ b _) hfibN ?_ ?_ ?_
              · obtain ⟨mN, hmN⟩ := hσNt
                simp [isArriveCmd, hcmdN', hmN]
              · simp [isArriveCmd, hcmdN', hτ'N]
              · intro x hx hxne
                cases hcmx : T.cmdAt x with
                | none => simp [isArriveCmd, hcmx]
                | some cmd =>
                  cases cmd with
                  | read g₀ => simp [isArriveCmd, hcmx]
                  | write g₀ => simp [isArriveCmd, hcmx]
                  | sync bbx nnx => simp [isArriveCmd, hcmx]
                  | arrive bbx nnx =>
                    simp only [isArriveCmd, hcmx, Bool.true_and]
                    cases hptx : pointTime T
                        (τ' ++ [Config.run
                          { s with B := Function.update s.B b ⟨[], 1, some na⟩ }
                          (Tc.set t ht P')]) x with
                    | none =>
                      cases hptx' : pointTime T τ' x with
                      | none => rfl
                      | some mx =>
                        have h := pointTime_append_some
                          (C' := Config.run
                            { s with B := Function.update s.B b ⟨[], 1, some na⟩ }
                            (Tc.set t ht P')) hptx'
                        rw [hptx] at h
                        exact absurd h (by simp)
                    | some mx =>
                      rcases htime_cases x mx hptx with hold | ⟨-, -, hidx, hd1, hd2⟩
                      · rw [hold]
                      · exact absurd (huniq x hidx hd1 hd2) hxne
            rw [hLHS, hcnt_new, ← harr0]
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              exfalso
              have h : i ∈ (Function.update s.B b ⟨[], 1, some na⟩ b).synced := hi
              rw [Function.update_self] at h
              simp at h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              exfalso
              have hex' : s.E i = false := hex
              by_cases hxt : x.thread = t
              · rw [← hthx, hxt, he] at hex'
                exact absurd hex' (by simp)
              · have hpx' := (hpointer_ne x _ _ ht hxt).mp hpx
                have hi' : i ∈ (s.B b).synced :=
                  (hsync i).mpr ⟨x, hxF, hthx, hsx, hpx', hex'⟩
                rw [hbcfg] at hi'
                have hi'' : i ∈ ([] : List ThreadId) := hi'
                simp at hi''
          · intro hcnone
            exfalso
            have h : (Function.update s.B b ⟨[], 1, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.B ba ⟨[], 1, some na⟩) b = s.B b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.B ba ⟨[], 1, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B ba ⟨[], 1, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hη
                rw [hbarN] at hbarx
                exact hbba (Option.some.inj hbarx).symm
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (s.B b).synced := by
                have h : i ∈ (Function.update s.B ba ⟨[], 1, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have hgoal : i ∈ (Function.update s.B ba ⟨[], 1, some na⟩ b).synced := by
                rw [hBb]
                exact hi'
              exact hgoal
          · intro hcnone
            have h : (Function.update s.B ba ⟨[], 1, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.B ba ⟨[], 1, some na⟩) b =
                BarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rw [hysync] at hcmdN'
        exact absurd (Option.some.inj hcmdN') (by simp)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
    | @arrive_register _ _ ba na _ I A he hbcfg hpos hlt =>
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive ba na :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hbarN : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [hcmdN']
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmemN hbarN hatN
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmemN, hbarN, hrr⟩
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T
          (τ' ++ [Config.run
            { s with B := Function.update s.B ba ⟨I, A + 1, some na⟩ } (Tc.set t ht P')])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hbarN hmN
          rw [hpgσ, hrr]
          have hrca := recycleCount_append ba τ'
            (Config.run { s with B := Function.update s.B ba ⟨I, A + 1, some na⟩ }
              (Tc.set t ht P'))
            (j := τ'.length - 1) (by omega)
          omega
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            have hna : na = n := by
              have h : (Function.update s.B b ⟨I, A + 1, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ
              (show 1 ≤ recycleCount b τ' (τ'.length - 1) + 1 by omega) hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same b (hnorec b)]
            have harrA : A =
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              have h := harr
              rw [hbcfg] at h
              exact h
            have hLHS : ((Function.update s.B b ⟨I, A + 1, some na⟩) b).arrived =
                A + 1 := by
              rw [Function.update_self]
            have hcnt_new :
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η &&
                    (pointTime T (τ' ++ [Config.run
                      { s with B := Function.update s.B b ⟨I, A + 1, some na⟩ }
                      (Tc.set t ht P')]) η).isSome).length =
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length + 1 := by
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              refine countP_succ_of_unique (genFiber_nodup T τ b _) hfibN ?_ ?_ ?_
              · obtain ⟨mN, hmN⟩ := hσNt
                simp [isArriveCmd, hcmdN', hmN]
              · simp [isArriveCmd, hcmdN', hτ'N]
              · intro x hx hxne
                cases hcmx : T.cmdAt x with
                | none => simp [isArriveCmd, hcmx]
                | some cmd =>
                  cases cmd with
                  | read g₀ => simp [isArriveCmd, hcmx]
                  | write g₀ => simp [isArriveCmd, hcmx]
                  | sync bbx nnx => simp [isArriveCmd, hcmx]
                  | arrive bbx nnx =>
                    simp only [isArriveCmd, hcmx, Bool.true_and]
                    cases hptx : pointTime T
                        (τ' ++ [Config.run
                          { s with B := Function.update s.B b ⟨I, A + 1, some na⟩ }
                          (Tc.set t ht P')]) x with
                    | none =>
                      cases hptx' : pointTime T τ' x with
                      | none => rfl
                      | some mx =>
                        have h := pointTime_append_some
                          (C' := Config.run
                            { s with B := Function.update s.B b ⟨I, A + 1, some na⟩ }
                            (Tc.set t ht P')) hptx'
                        rw [hptx] at h
                        exact absurd h (by simp)
                    | some mx =>
                      rcases htime_cases x mx hptx with hold | ⟨-, -, hidx, hd1, hd2⟩
                      · rw [hold]
                      · exact absurd (huniq x hidx hd1 hd2) hxne
            rw [hLHS, hcnt_new, ← harrA]
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (s.B b).synced := by
                have h : i ∈ (Function.update s.B b ⟨I, A + 1, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                rw [hbcfg]
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have h : i ∈ (Function.update s.B b ⟨I, A + 1, some na⟩ b).synced := by
                rw [Function.update_self]
                rw [hbcfg] at hi'
                exact hi'
              exact h
          · intro hcnone
            exfalso
            have h : (Function.update s.B b ⟨I, A + 1, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.B ba ⟨I, A + 1, some na⟩) b = s.B b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.B ba ⟨I, A + 1, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B ba ⟨I, A + 1, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hη
                rw [hbarN] at hbarx
                exact hbba (Option.some.inj hbarx).symm
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (s.B b).synced := by
                have h : i ∈ (Function.update s.B ba ⟨I, A + 1, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have hgoal : i ∈ (Function.update s.B ba ⟨I, A + 1, some na⟩ b).synced := by
                rw [hBb]
                exact hi'
              exact hgoal
          · intro hcnone
            have h : (Function.update s.B ba ⟨I, A + 1, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.B ba ⟨I, A + 1, some na⟩) b =
                BarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rw [hysync] at hcmdN'
        exact absurd (Option.some.inj hcmdN') (by simp)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
    | @sync_configure _ _ ba na cc he hbcfg =>
      -- the `sync` parks: nothing executes, `t` enters `ba`'s synced list
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync ba na :: cc := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hbarN : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [hcmdN']
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmemN hbarN hatN
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmemN, hbarN, hrr⟩
      -- the stepping thread's program is unchanged (control stays at the `sync`)
      have hsetsame : (Tc.set t ht (Cmd.sync ba na :: cc)).prog t = Tc.prog t := by
        simp only [WeftCommon.CTA.set, Function.update_self]
        rw [hPt]
      have hnodrop : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          Tc.prog η.thread = (T.prog η.thread).drop η.idx →
          (Config.run
            ({ E := Function.update s.E t false,
               B := Function.update s.B ba ⟨[t], 0, some na⟩ } : State)
            (Tc.set t ht (Cmd.sync ba na :: cc))).progOf η.thread =
            (T.prog η.thread).drop (η.idx + 1) → False := by
        intro η hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hd2' : (Tc.set t ht (Cmd.sync ba na :: cc)).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hηt] at hd2' hd1
        rw [hsetsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        rw [hηt] at hidx
        omega
      -- pointer transfer for every thread (t's program is unchanged too)
      have hpointer_all : ∀ (x : ProgPoint),
          (pointerAt T x (Config.run
            ({ E := Function.update s.E t false,
               B := Function.update s.B ba ⟨[t], 0, some na⟩ } : State)
            (Tc.set t ht (Cmd.sync ba na :: cc))) ↔
            pointerAt T x (Config.run s Tc)) := by
        intro x
        by_cases hxt : x.thread = t
        · have hsame : (Tc.set t ht (Cmd.sync ba na :: cc)).prog x.thread =
              Tc.prog x.thread := by
            rw [hxt, hsetsame]
          simp [pointerAt, WeftCommon.Config.progOf, hsame]
        · exact hpointer_ne x _ _ ht hxt
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        exact absurd hd2 (fun h => hnodrop η hidx hd1 h)
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        have hEeq : ∀ i, i ≠ t →
            (Function.update s.E t false) i = s.E i := fun i hi =>
          Function.update_of_ne hi _ _
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            have hna : na = n := by
              have h : (Function.update s.B b ⟨[t], 0, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ
              (show 1 ≤ recycleCount b τ' (τ'.length - 1) + 1 by omega) hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B b ⟨[t], 0, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ ([t] : List ThreadId) := by
                have h : i ∈ (Function.update s.B b ⟨[t], 0, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                exact h
              have hit : i = t := by simpa using hi'
              refine ⟨⟨t, (T.prog t).length - (Tc.prog t).length⟩, hfibN, hit.symm,
                ⟨na, hcmdN'⟩, ?_, ?_⟩
              · exact (hpointer_all _).mpr hatN
              · rw [hit]
                exact Function.update_self ..
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · have h : i ∈ (Function.update s.B b ⟨[t], 0, some na⟩ b).synced := by
                  rw [Function.update_self, hit]
                  simp
                exact h
              · exfalso
                have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hxt : x.thread ≠ t := by
                  intro h
                  rw [h] at hthx
                  exact hit hthx.symm
                have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                rw [hbcfg] at hi'
                have hi'' : i ∈ ([] : List ThreadId) := hi'
                simp at hi''
          · intro hcnone
            exfalso
            have h : (Function.update s.B b ⟨[t], 0, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.B ba ⟨[t], 0, some na⟩) b = s.B b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.B ba ⟨[t], 0, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B ba ⟨[t], 0, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (s.B b).synced := by
                have h : i ∈ (Function.update s.B ba ⟨[t], 0, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hit : i ≠ t := by
                intro h
                rw [h, he] at hex
                exact absurd hex (by simp)
              refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
              have h : (Function.update s.E t false) i = false := by
                rw [hEeq i hit]
                exact hex
              exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · exfalso
                -- `x` sits at `t`'s head, a `sync` on `ba`, yet lies in `b ≠ ba`'s fiber
                have hxt : x.thread = t := hthx.trans hit
                have hpx' := (hpointer_all x).mp hpx
                have hpxlen : (Tc.prog x.thread).length =
                    (T.prog x.thread).length - x.idx := hpx'
                rw [hxt] at hpxlen
                have hidxx : x.idx < (T.prog x.thread).length :=
                  ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
                rw [hxt] at hidxx
                have hxidx : x.idx = (T.prog t).length - (Tc.prog t).length := by
                  omega
                have hxeq : x = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  rw [hxeta, hxt, hxidx]
                obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hxF
                rw [hxeq, hbarN] at hbarx
                exact hbba (Option.some.inj hbarx).symm
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.B ba ⟨[t], 0, some na⟩ b).synced := by
                  rw [hBb]
                  exact hi'
                exact hgoal
          · intro hcnone
            have h : (Function.update s.B ba ⟨[t], 0, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.B ba ⟨[t], 0, some na⟩) b =
                BarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exact absurd hd2 (fun h => hnodrop y hidx hd1 h)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
    | @sync_block _ _ ba na cc I A he hbcfg hpos hlt =>
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync ba na :: cc := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hbarN : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [hcmdN']
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmemN hbarN hatN
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmemN, hbarN, hrr⟩
      have hsetsame : (Tc.set t ht (Cmd.sync ba na :: cc)).prog t = Tc.prog t := by
        simp only [WeftCommon.CTA.set, Function.update_self]
        rw [hPt]
      have hnodrop : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          Tc.prog η.thread = (T.prog η.thread).drop η.idx →
          (Config.run
            ({ E := Function.update s.E t false,
               B := Function.update s.B ba ⟨t :: I, A, some na⟩ } : State)
            (Tc.set t ht (Cmd.sync ba na :: cc))).progOf η.thread =
            (T.prog η.thread).drop (η.idx + 1) → False := by
        intro η hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hd2' : (Tc.set t ht (Cmd.sync ba na :: cc)).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hηt] at hd2' hd1
        rw [hsetsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        rw [hηt] at hidx
        omega
      have hpointer_all : ∀ (x : ProgPoint),
          (pointerAt T x (Config.run
            ({ E := Function.update s.E t false,
               B := Function.update s.B ba ⟨t :: I, A, some na⟩ } : State)
            (Tc.set t ht (Cmd.sync ba na :: cc))) ↔
            pointerAt T x (Config.run s Tc)) := by
        intro x
        by_cases hxt : x.thread = t
        · have hsame : (Tc.set t ht (Cmd.sync ba na :: cc)).prog x.thread =
              Tc.prog x.thread := by
            rw [hxt, hsetsame]
          simp [pointerAt, WeftCommon.Config.progOf, hsame]
        · exact hpointer_ne x _ _ ht hxt
      have htnI : t ∉ I := by
        intro htI
        have hib : t ∈ (s.B ba).synced := by rw [hbcfg]; exact htI
        have hef := hwf.2.2.2.1 ba t hib
        rw [he] at hef
        exact absurd hef (by simp)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        exact absurd hd2 (fun h => hnodrop η hidx hd1 h)
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        have hEeq : ∀ i, i ≠ t →
            (Function.update s.E t false) i = s.E i := fun i hi =>
          Function.update_of_ne hi _ _
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            have hna : na = n := by
              have h : (Function.update s.B b ⟨t :: I, A, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ
              (show 1 ≤ recycleCount b τ' (τ'.length - 1) + 1 by omega) hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B b ⟨t :: I, A, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (t :: I) := by
                have h : i ∈ (Function.update s.B b ⟨t :: I, A, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                exact h
              rcases List.mem_cons.mp hi' with hit | hiI
              · refine ⟨⟨t, (T.prog t).length - (Tc.prog t).length⟩, hfibN, hit.symm,
                  ⟨na, hcmdN'⟩, ?_, ?_⟩
                · exact (hpointer_all _).mpr hatN
                · rw [hit]
                  exact Function.update_self ..
              · have hiI' : i ∈ (s.B b).synced := by rw [hbcfg]; exact hiI
                obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hiI'
                have hit : i ≠ t := fun h => htnI (h ▸ hiI)
                refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
                have h : (Function.update s.E t false) i = false := by
                  rw [hEeq i hit]
                  exact hex
                exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · have h : i ∈ (Function.update s.B b ⟨t :: I, A, some na⟩ b).synced := by
                  rw [Function.update_self, hit]
                  exact List.mem_cons_self ..
                exact h
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.B b ⟨t :: I, A, some na⟩ b).synced := by
                  rw [Function.update_self]
                  rw [hbcfg] at hi'
                  exact List.mem_cons_of_mem _ hi'
                exact hgoal
          · intro hcnone
            exfalso
            have h : (Function.update s.B b ⟨t :: I, A, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.B ba ⟨t :: I, A, some na⟩) b = s.B b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same b (hnorec b)] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.B ba ⟨t :: I, A, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same b (hnorec b), hfilter_same b _ ?_]
            · have hgoal : ((Function.update s.B ba ⟨t :: I, A, some na⟩) b).arrived =
                  ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη bb nn hcm hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same b (hnorec b)]
            constructor
            · intro hi
              have hi' : i ∈ (s.B b).synced := by
                have h : i ∈ (Function.update s.B ba ⟨t :: I, A, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hit : i ≠ t := by
                intro h
                rw [h, he] at hex
                exact absurd hex (by simp)
              refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
              have h : (Function.update s.E t false) i = false := by
                rw [hEeq i hit]
                exact hex
              exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · exfalso
                have hxt : x.thread = t := hthx.trans hit
                have hpx' := (hpointer_all x).mp hpx
                have hpxlen : (Tc.prog x.thread).length =
                    (T.prog x.thread).length - x.idx := hpx'
                rw [hxt] at hpxlen
                have hidxx : x.idx < (T.prog x.thread).length :=
                  ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
                rw [hxt] at hidxx
                have hxidx : x.idx = (T.prog t).length - (Tc.prog t).length := by
                  omega
                have hxeq : x = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  rw [hxeta, hxt, hxidx]
                obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hxF
                rw [hxeq, hbarN] at hbarx
                exact hbba (Option.some.inj hbarx).symm
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.B b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.B ba ⟨t :: I, A, some na⟩ b).synced := by
                  rw [hBb]
                  exact hi'
                exact hgoal
          · intro hcnone
            have h : (Function.update s.B ba ⟨t :: I, A, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.B ba ⟨t :: I, A, some na⟩) b =
                BarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · refine hedge_all ?_
        intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
        exact absurd hd2 (fun h => hnodrop y hidx hd1 h)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
  | @recycle _ _ b₀ I A n₀ hb hfull hpark =>
    -- this step is exactly a recycle of `b₀`
    have hrecb : stepRecyclesBarrier b₀ (Config.run s Tc) (Config.run
        ({ E := updateMapOn s.E I true,
             B := Function.update s.B b₀ BarrierState.unconfigured } : State)
          (Tc.wake I)) = true := by
      simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self]
    have hnorecb : ∀ b, b ≠ b₀ → stepRecyclesBarrier b (Config.run s Tc) (Config.run
        ({ E := updateMapOn s.E I true,
             B := Function.update s.B b₀ BarrierState.unconfigured } : State)
          (Tc.wake I)) = false := by
      intro b hbne
      have hupd : (Function.update s.B b₀ BarrierState.unconfigured) b = s.B b :=
        Function.update_of_ne hbne _ _
      simp only [stepRecyclesBarrier, Config.state?]
      cases hfl : (s.B b).isFull
      · simp
      · simp only [Bool.true_and, hupd, decide_eq_false_iff_not]
        intro hunc
        rw [hunc] at hfl
        simp [BarrierState.isFull, BarrierState.unconfigured] at hfl
    -- the fullness pigeonhole: the round holds its entire fiber
    have hff := conforms_full_fiber hτ htr hconf hlast hb hfull
    -- a disabled thread after the wake was disabled before and is not woken
    have hEfalse : ∀ i, updateMapOn s.E I true i = false → i ∉ I ∧ s.E i = false := by
      intro i hEi
      rw [updateMapOn_apply] at hEi
      by_cases hiI : i ∈ I
      · rw [if_pos hiI] at hEi
        exact absurd hEi (by simp)
      · rw [if_neg hiI] at hEi
        exact ⟨hiI, hEi⟩
    -- a pointer sitting at a thread's head names the head command
    have hhead_cmd : ∀ (x : ProgPoint), pointerAt T x (Config.run s Tc) →
        x.idx < (T.prog x.thread).length →
        ∀ (c₀ : Cmd), (Tc.prog x.thread).head? = some c₀ → T.cmdAt x = some c₀ := by
      intro x hpx hidx c₀ hhd
      have hsufx : (Config.run s Tc).progOf x.thread <:+
          (Config.run State.initial T).progOf x.thread :=
        progOf_suffix_index_le hchain x.thread h0idx (Nat.zero_le _) hlastidx
      have hdrop : Tc.prog x.thread =
          (T.prog x.thread).drop
            ((T.prog x.thread).length - (Tc.prog x.thread).length) :=
        List.IsSuffix.eq_drop hsufx
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hidxeq : (T.prog x.thread).length - (Tc.prog x.thread).length = x.idx := by
        omega
      rw [hidxeq] at hdrop
      have hdd : (T.prog x.thread).drop x.idx =
          (T.prog x.thread)[x.idx]'hidx :: (T.prog x.thread).drop (x.idx + 1) :=
        List.drop_eq_getElem_cons hidx
      rw [hdrop, hdd] at hhd
      simp only [List.head?_cons, Option.some.injEq] at hhd
      have hg : (T.prog x.thread)[x.idx]? = some c₀ := by
        rw [List.getElem?_eq_getElem hidx, hhd]
      exact hg
    -- the appended step's drops are exactly the woken parked syncs
    have hnew_char : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        (Config.run
          ({ E := updateMapOn s.E I true,
             B := Function.update s.B b₀ BarrierState.unconfigured } : State)
          (Tc.wake I)).progOf η.thread = (T.prog η.thread).drop (η.idx + 1) →
        η.thread ∈ I ∧ T.cmdAt η = some (Cmd.sync b₀ n₀) ∧
          pointerAt T η (Config.run s Tc) := by
      intro η hidx hd1 hd2
      by_cases hηI : η.thread ∈ I
      · have hhd := hpark η.thread hηI
        have hdd : (T.prog η.thread).drop η.idx =
            (T.prog η.thread)[η.idx]'hidx :: (T.prog η.thread).drop (η.idx + 1) :=
          List.drop_eq_getElem_cons hidx
        rw [hd1, hdd] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        refine ⟨hηI, ?_, ?_⟩
        · have hg : (T.prog η.thread)[η.idx]? = some (Cmd.sync b₀ n₀) := by
            rw [List.getElem?_eq_getElem hidx, hhd]
          exact hg
        · have hg : (Tc.prog η.thread).length =
              (T.prog η.thread).length - η.idx := by
            rw [hd1]
            simp [List.length_drop]
          exact hg
      · exfalso
        have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
          simp [WeftCommon.CTA.wake, if_neg hηI]
        have hd2' : (Tc.wake I).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        omega
    -- a woken parked sync executes in the appended trace
    have hnewtime : ∀ (x : ProgPoint), x.thread ∈ I →
        pointerAt T x (Config.run s Tc) → x.idx < (T.prog x.thread).length →
        ∃ m, pointTime T (τ' ++ [Config.run
          ({ E := updateMapOn s.E I true,
             B := Function.update s.B b₀ BarrierState.unconfigured } : State)
          (Tc.wake I)]) x = some m := by
      intro x hxI hpx hidx
      refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
        (i := x.thread) (k := x.idx) hidx ?_
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hposx : 0 < (Tc.prog x.thread).length := by
        have hhd := hpark x.thread hxI
        cases hTt : Tc.prog x.thread with
        | nil => rw [hTt] at hhd; simp at hhd
        | cons a l => simp
      have hwake : (Tc.wake I).prog x.thread = (Tc.prog x.thread).tail := by
        simp [WeftCommon.CTA.wake, if_pos hxI]
      change ((Tc.wake I).prog x.thread).length + (x.idx + 1) ≤
        (T.prog x.thread).length
      rw [hwake]
      have htl : ((Tc.prog x.thread).tail).length = (Tc.prog x.thread).length - 1 := by
        simp [List.length_tail]
      omega
    -- a parked sync of the closing round is a fiber member
    have hgen_of_park : ∀ (η : ProgPoint), η.thread ∈ I →
        pointerAt T η (Config.run s Tc) → η.idx < (T.prog η.thread).length →
        η ∈ genFiber T τ b₀ (recycleCount b₀ τ' (τ'.length - 1) + 1) := by
      intro η hηI hpη hidx
      obtain ⟨hcount, harr, hsync, -⟩ := hconf.state _ hlast s rfl b₀
      have hiI : η.thread ∈ (s.B b₀).synced := by rw [hb]; exact hηI
      obtain ⟨x, hxF, hthx, hsx, hpx', hex⟩ := (hsync η.thread).mp hiI
      have hxeq : x = η := by
        have hpxlen : (Tc.prog x.thread).length =
            (T.prog x.thread).length - x.idx := hpx'
        have hηlen : (Tc.prog η.thread).length =
            (T.prog η.thread).length - η.idx := hpη
        have hidxx : x.idx < (T.prog x.thread).length :=
          ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
        rw [hthx] at hpxlen hidxx
        have hxidx : x.idx = η.idx := by omega
        have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
        have hηeta : η = ⟨η.thread, η.idx⟩ := rfl
        rw [hxeta, hηeta, hthx, hxidx]
      rw [hxeq] at hxF
      exact hxF
    -- clause 4's fresh round: everything in the closing fiber has now executed
    have hround_new : ∀ b, stepRecyclesBarrier b (Config.run s Tc) (Config.run
        ({ E := updateMapOn s.E I true,
           B := Function.update s.B b₀ BarrierState.unconfigured } : State) (Tc.wake I)) = true →
        ∀ η ∈ genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1),
          ∃ m, pointTime T (τ' ++ [Config.run
            ({ E := updateMapOn s.E I true,
               B := Function.update s.B b₀ BarrierState.unconfigured } : State)
            (Tc.wake I)]) η = some m := by
      intro b hrb η hη
      have hbb : b = b₀ := by
        by_contra hne'
        rw [hnorecb b hne'] at hrb
        exact absurd hrb (by simp)
      subst hbb
      obtain ⟨hmem, hbarη, hgenη⟩ := mem_genFiber.mp hη
      have hidx : η.idx < (T.prog η.thread).length :=
        ((mem_progPoints_iff T η).mp hmem).2
      obtain ⟨harr_ex, hsyn_park⟩ := hff η hη
      cases hcm : T.cmdAt η with
      | none => rw [hcm] at hbarη; exact absurd hbarη (by simp)
      | some cmd =>
        cases cmd with
        | read g₀ => rw [hcm] at hbarη; simp [Cmd.barrier?] at hbarη
        | write g₀ => rw [hcm] at hbarη; simp [Cmd.barrier?] at hbarη
        | arrive bb nn =>
          obtain ⟨m, hm⟩ := harr_ex ⟨bb, nn, hcm⟩
          exact ⟨m, pointTime_append_some hm⟩
        | sync bb nn =>
          have hbb2 : b = bb := by
            rw [hcm] at hbarη
            simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbarη
            exact hbarη.symm
          subst hbb2
          obtain ⟨hI, hpx⟩ := hsyn_park nn hcm
          exact hnewtime η hI hpx hidx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro Te h
      rw [List.getLast?_concat, Option.some.injEq] at h
      exact absurd h (by simp)
    · -- gen_eq: the new executions are the woken syncs, whose generation the old
      -- clause 2 already pinned to the closing round
      refine hgen_all ?_
      intro η hnone hidx hd1 hd2
      obtain ⟨hηI, hcm, hpη⟩ := hnew_char η hidx hd1 hd2
      have hηF := hgen_of_park η hηI hpη hidx
      have hgenη : pointGen T τ η = recycleCount b₀ τ' (τ'.length - 1) + 1 :=
        (mem_genFiber.mp hηF).2.2
      obtain ⟨m, hm⟩ := hnewtime η hηI hpη hidx
      rcases pointTime_append_cases hne hm with hold | ⟨-, hmN⟩
      · rw [hnone] at hold
        exact absurd hold (by simp)
      · subst hmN
        have hbarη : (T.cmdAt η).bind Cmd.barrier? = some b₀ := by rw [hcm]; rfl
        have hpgσ := pointGen_eq_of_pointTime hbarη hm
        rw [hpgσ, hgenη]
        have hrca := recycleCount_append b₀ τ'
          (Config.run
          ({ E := updateMapOn s.E I true,
             B := Function.update s.B b₀ BarrierState.unconfigured } : State) (Tc.wake I))
          (j := τ'.length - 1) (by omega)
        omega
    · -- state
      intro Cl hCl sl hsl b
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      simp only [Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
      by_cases hbb : b = b₀
      · subst hbb
        -- the barrier resets: unconfigured, empty round of the *next* fiber
        have hBb : (Function.update s.B b BarrierState.unconfigured) b =
            BarrierState.unconfigured := Function.update_self ..
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n hn
          exfalso
          have h : (Function.update s.B b BarrierState.unconfigured b).count =
              some n := hn
          rw [hBb] at h
          simp [BarrierState.unconfigured] at h
        · -- arrived 0: nothing of the next fiber has executed
          have hLHS : ((Function.update s.B b BarrierState.unconfigured) b).arrived =
              0 := by
            rw [hBb]
            rfl
          rw [hrc_incr b hrecb, hLHS]
          symm
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro x hx
          simp only [Bool.and_eq_true, not_and]
          intro hxarr hxsome
          obtain ⟨mx, hmx⟩ := Option.isSome_iff_exists.mp hxsome
          obtain ⟨hxmem, hxbar, hxgen⟩ := mem_genFiber.mp hx
          rcases pointTime_append_cases hne hmx with hold | ⟨-, hmN⟩
          · -- an executed member of the *next* round outruns the recycle count
            have hgx := hconf.gen_eq x hxmem mx hold
            have hpg := pointGen_eq_of_pointTime hxbar hold
            have hmlt : mx < τ'.length := (pointTime_spec hchain h0 hold).2.1
            have hmono := recycleCount_mono b τ'
              (show mx - 1 ≤ τ'.length - 1 by omega)
            omega
          · -- the new executions are syncs, not arrives
            subst hmN
            obtain ⟨hspec1, hspec2, hidxx, C₁, C₂, hC₁, hC₂, hdx1, hdx2⟩ :=
              pointTime_spec hchainσ h0σ hmx
            rw [hσN1] at hC₁
            obtain rfl := Option.some.inj hC₁
            rw [hσN] at hC₂
            obtain rfl := Option.some.inj hC₂
            obtain ⟨-, hcmx, -⟩ := hnew_char x hidxx hdx1 hdx2
            simp only [isArriveCmd, hcmx] at hxarr
            exact absurd hxarr (by simp)
        · -- synced: empty, and nothing of the next fiber can be parked
          intro i
          rw [hrc_incr b hrecb]
          constructor
          · intro hi
            exfalso
            have h : i ∈ (Function.update s.B b BarrierState.unconfigured b).synced :=
              hi
            rw [hBb] at h
            simp [BarrierState.unconfigured] at h
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            exfalso
            obtain ⟨hiI, hex'⟩ := hEfalse i hex
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            have hpxC : pointerAt T x (Config.run s Tc) := by
              have hpx' : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              rw [hsame] at hpx'
              exact hpx'
            have hidxx : x.idx < (T.prog x.thread).length :=
              ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
            -- `i` is disabled, so it is parked somewhere, at its head — which is `x`
            obtain ⟨b', hib'⟩ := hei i hex'
            rcases hsb' : s.B b' with ⟨I', A', cnt'⟩
            cases cnt' with
            | none =>
              obtain ⟨hI0, -⟩ := hwf.2.1 b' I' A' hsb'
              rw [hsb'] at hib'
              have hib'' : i ∈ I' := hib'
              rw [hI0] at hib''
              simp at hib''
            | some n' =>
              have hpk := (hwf.1 b' I' A' n' hsb').2.1 i
                (by rw [hsb'] at hib'; exact hib')
              have hcmx : T.cmdAt x = some (Cmd.sync b' n') := by
                refine hhead_cmd x hpxC hidxx _ ?_
                rw [hthx]
                exact hpk
              obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hxF
              rw [hcmx] at hbarx
              simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbarx
              rw [hbarx] at hib'
              have hiI' : i ∈ I := by
                rw [hb] at hib'
                exact hib'
              exact hiI hiI'
        · intro hcnone
          have hg : (Function.update s.B b BarrierState.unconfigured) b =
              BarrierState.unconfigured := hBb
          exact hg
      · -- b ≠ b₀: state untouched, times untouched (the new executions live on b₀)
        have hBb : (Function.update s.B b₀ BarrierState.unconfigured) b = s.B b :=
          Function.update_of_ne hbb _ _
        have hrcs := hrc_same b (hnorecb b hbb)
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n hn η hη
          rw [hrcs] at hη
          refine hcount n ?_ η hη
          have h : (Function.update s.B b₀ BarrierState.unconfigured b).count =
              some n := hn
          rw [hBb] at h
          exact h
        · rw [hrcs, hfilter_same b _ ?_]
          · have hgoal : ((Function.update s.B b₀ BarrierState.unconfigured) b).arrived =
                ((genFiber T τ b (recycleCount b τ' (τ'.length - 1) + 1)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              rw [hBb]
              exact harr
            exact hgoal
          · intro η hη bb nn hcm hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · obtain ⟨-, hcmη, -⟩ := hnew_char η hidx hd1 hd2
              rw [hcm] at hcmη
              exact absurd (Option.some.inj hcmη) (by simp)
        · intro i
          rw [hrcs]
          constructor
          · intro hi
            have hi' : i ∈ (s.B b).synced := by
              have h : i ∈ (Function.update s.B b₀ BarrierState.unconfigured b).synced :=
                hi
              rw [hBb] at h
              exact h
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
            -- `i` is not woken: it is parked on `b ≠ b₀` (one list per thread)
            have hiI : i ∉ I := by
              intro hiI
              have hib₀ : i ∈ (s.B b₀).synced := by rw [hb]; exact hiI
              have := hwf.2.2.2.2 b b₀ i hi' hib₀
              exact hbb this
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            refine ⟨x, hxF, hthx, hsx, ?_, ?_⟩
            · have hpx' : (Tc.prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              have hg : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := by
                rw [hsame]
                exact hpx'
              exact hg
            · have hg : updateMapOn s.E I true i = false := by
                rw [updateMapOn_apply, if_neg hiI]
                exact hex
              exact hg
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            obtain ⟨hiI, hex'⟩ := hEfalse i hex
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            have hpxC : pointerAt T x (Config.run s Tc) := by
              have hpx' : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              rw [hsame] at hpx'
              exact hpx'
            have hi' : i ∈ (s.B b).synced :=
              (hsync i).mpr ⟨x, hxF, hthx, hsx, hpxC, hex'⟩
            have hgoal : i ∈
                (Function.update s.B b₀ BarrierState.unconfigured b).synced := by
              rw [hBb]
              exact hi'
            exact hgoal
        · intro hcnone
          have h : (s.B b).count = none := by
            have hg : (Function.update s.B b₀ BarrierState.unconfigured b).count =
                none := hcnone
            rw [hBb] at hg
            exact hg
          have hg : (Function.update s.B b₀ BarrierState.unconfigured) b =
              BarrierState.unconfigured := by
            rw [hBb]
            exact hunc h
          exact hg
    · -- edge_sound: a new sync target's whole fiber has executed (clause 4)
      refine hedge_all ?_
      intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
      obtain ⟨hyI, hcmy, hpy⟩ := hnew_char y hidx hd1 hd2
      rw [hysync] at hcmy
      have hinj := Option.some.inj hcmy
      injection hinj with hbbeq hnbeq
      have hbbeq' : b₀ = bb := hbbeq.symm
      subst hbbeq'
      have hyF := hgen_of_park y hyI hpy hidx
      have hygen : pointGen T τ y = recycleCount b₀ τ' (τ'.length - 1) + 1 :=
        (mem_genFiber.mp hyF).2.2
      have hxF : x ∈ genFiber T τ b₀ (recycleCount b₀ τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hxpts, hxbar, by rw [hgenxy, hygen]⟩
      obtain ⟨mx, hmx⟩ := hround_new b₀ hrecb x hxF
      have hmxlt := (pointTime_spec hchainσ h0σ hmx).2.1
      have hmxle : mx ≤ τ'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hmxlt
        omega
      exact ⟨mx, hmxle, hmx⟩
    · exact hrounds_all hround_new
  | @done _ _ hdone hnofull =>
    have hnonew : ∀ (η : ProgPoint) (m : Nat),
        pointTime T (τ' ++ [Config.done s]) η = some m →
        pointTime T τ' η = some m := by
      intro η m hpt
      rcases htime_cases η m hpt with h | ⟨-, -, hidx, hd1, -⟩
      · exact h
      · exfalso
        have hnil : Tc.prog η.thread = [] := by
          by_cases hi : η.thread ∈ Tc.ids
          · exact hdone η.thread hi
          · exact Tc.nil_outside_ids η.thread hi
        rw [hnil] at hd1
        have hlen := congrArg List.length hd1
        simp only [List.length_nil, List.length_drop] at hlen
        omega
    have hnorec : ∀ b,
        stepRecyclesBarrier b (Config.run s Tc) (Config.done s) = false := by
      intro b
      simp only [stepRecyclesBarrier, Config.state?]
      cases hfl : (s.B b).isFull
      · simp
      · simp only [Bool.true_and]
        rw [decide_eq_false_iff_not]
        intro hunc
        rw [hunc] at hfl
        simp [BarrierState.isFull, BarrierState.unconfigured] at hfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro Te h
      rw [List.getLast?_concat, Option.some.injEq] at h
      exact absurd h (by simp)
    · refine hgen_all ?_
      intro η hnone hidx hd1 hd2
      exfalso
      have hnil : Tc.prog η.thread = [] := by
        by_cases hi : η.thread ∈ Tc.ids
        · exact hdone η.thread hi
        · exact Tc.nil_outside_ids η.thread hi
      rw [hnil] at hd1
      have hlen := congrArg List.length hd1
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    · intro Cl hCl sl hsl b
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      simp only [Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
      have hrc := hrc_same b (hnorec b)
      refine ⟨?_, ?_, ?_, hunc⟩
      · rw [hrc]
        exact hcount
      · rw [hrc, hfilter_same b _ ?_]
        · exact harr
        · intro η hη bb nn hcm hpt
          have hpt' := hnonew η _ hpt
          have hlt := (pointTime_spec hchain h0 hpt').2.1
          omega
      · intro i
        rw [hrc]
        constructor
        · intro hi
          obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
          exfalso
          have hpx' : (Tc.prog x.thread).length =
              (T.prog x.thread).length - x.idx := hpx
          have hidxx : x.idx < (T.prog x.thread).length :=
            ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
          have hnil : Tc.prog x.thread = [] := by
            by_cases hxi : x.thread ∈ Tc.ids
            · exact hdone x.thread hxi
            · exact Tc.nil_outside_ids x.thread hxi
          rw [hnil] at hpx'
          simp only [List.length_nil] at hpx'
          omega
        · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
          exfalso
          have hpx' : ((Config.done s).progOf x.thread).length =
              (T.prog x.thread).length - x.idx := hpx
          have hidxx : x.idx < (T.prog x.thread).length :=
            ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
          simp only [WeftCommon.Config.progOf, List.length_nil] at hpx'
          omega
    · refine hedge_all ?_
      intro y bb nb hysync hidx hd1 hd2 x hxpts hxbar hgenxy
      exfalso
      have hnil : Tc.prog y.thread = [] := by
        by_cases hi : y.thread ∈ Tc.ids
        · exact hdone y.thread hi
        · exact Tc.nil_outside_ids y.thread hi
      rw [hnil] at hd1
      have hlen := congrArg List.length hd1
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    · refine hrounds_all ?_
      intro b hrb
      exact absurd hrb (by rw [hnorec b]; simp)
  | @error _ _ t P' hbar hth =>
    exfalso
    obtain ⟨Pt, hPt⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPt] at hth
    have hsuf : (Config.run s Tc).progOf t <:+
        (Config.run State.initial T).progOf t :=
      progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
    have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
    cases hth with
    | @sync_err_count _ _ ba mm nn cc II AA he hbcfg hnem =>
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync ba mm :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hat : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have hbarη : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [show T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync ba mm) from hcmdη]
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmem hbarη hat
      obtain ⟨hcount, -, -, -⟩ := hconf.state _ hlast s rfl ba
      have hηfib : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmem, hbarη, hrr⟩
      have hcnt := hcount nn (by rw [hbcfg]) _ hηfib
      rw [show T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
        some (Cmd.sync ba mm) from hcmdη] at hcnt
      simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hcnt
      exact hnem hcnt.symm
    | @arrive_err_count _ _ ba mm nn cc II AA he hbcfg hnem =>
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive ba mm :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hat : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have hbarη : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.barrier? = some ba := by
        rw [show T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive ba mm) from hcmdη]
        rfl
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmem hbarη hat
      obtain ⟨hcount, -, -, -⟩ := hconf.state _ hlast s rfl ba
      have hηfib : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ ba (recycleCount ba τ' (τ'.length - 1) + 1) :=
        mem_genFiber.mpr ⟨hmem, hbarη, hrr⟩
      have hcnt := hcount nn (by rw [hbcfg]) _ hηfib
      rw [show T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
        some (Cmd.arrive ba mm) from hcmdη] at hcnt
      simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hcnt
      exact hnem hcnt.symm

/-- **Theorem 6** (paper §5.2.6): if the reference trace is successful and the check
passes, *every* partial trace of `T` conforms to the reference. Reverse-list induction
from `conforms_init` via `conforms_snoc`. -/
theorem conforms_of_traceFrom {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    {τ' : List Config} (htr : IsTraceFrom (Config.run State.initial T) τ') :
    Conforms T τ τ' := by
  revert htr
  induction τ' using List.reverseRecOn with
  | nil =>
    intro htr
    exact absurd htr.2 (by simp)
  | append_singleton l c ih =>
    intro htr
    obtain ⟨hchain, hhead⟩ := htr
    by_cases hl : l = []
    · subst hl
      simp only [List.nil_append] at hhead ⊢
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact conforms_init T τ
    · have hchain' : List.IsChain CTAStep (l ++ [c]) := hchain
      rw [List.isChain_append] at hchain'
      obtain ⟨hchain_l, -, hconn⟩ := hchain'
      have hhead_l : l.head? = some (Config.run State.initial T) := by
        rwa [List.head?_append_of_ne_nil _ hl] at hhead
      have htr_l : IsTraceFrom (Config.run State.initial T) l := ⟨hchain_l, hhead_l⟩
      obtain ⟨x, hx⟩ : ∃ x, l.getLast? = some x := by
        cases hgl : l.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hgl) hl
        | some x => exact ⟨x, rfl⟩
      have hstep : CTAStep x c :=
        hconn x (Option.mem_def.mpr hx) c (Option.mem_def.mpr rfl)
      exact conforms_snoc hτ hcheck htr_l (ih htr_l) hx hstep

/-- **Theorem 7** (paper §5.2.6): a conforming *complete* trace ends in `done`. `err` is
clause 0. For a deadlock: every unfinished thread is parked (an enabled thread always has
a step under the recycle-priority semantics), so take the parked sync `u` of **minimal
τ-time**: its open round (= `pointGen T τ u` by conformance) is missing a fiber member
`d` (clause 2 + L0c), whose thread is parked at a sync `e` strictly before `d` — and
`t_τ(e) < t_τ(d) ≤ t_τ(u)` breaks minimality. (The extremal pick is essential: the
analysis of an arbitrary parked sync yields only a locally-consistent pointer to another
parked sync — see the plan's §4½ visualization.) -/
theorem conforms_complete_done {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {σ : List Config} (hσ : IsCompleteTraceFrom (Config.run State.initial T) σ)
    (hconf : Conforms T τ σ) :
    ∃ s, σ.getLast? = some (Config.done s) := by
  obtain ⟨hct, h0⟩ := hσ
  obtain ⟨Cn, hlast, hends⟩ := hct.ends
  rcases hends with ⟨sd, rfl⟩ | ⟨Te, rfl⟩ | hstuck
  · exact ⟨sd, hlast⟩
  · exact absurd hlast (hconf.no_err Te)
  · cases Cn with
    | done sd => exact ⟨sd, hlast⟩
    | err Te => exact absurd hlast (hconf.no_err Te)
    | run s Tc =>
      exfalso
      -- ## trace facts
      have hchain : List.IsChain CTAStep σ := hct.subtrace
      have h0idx : σ[0]? = some (Config.run State.initial T) := by
        have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen]; exact h0
      have hlastidx : σ[σ.length - 1]? = some (Config.run s Tc) := by
        rw [← List.getLast?_eq_getElem?]; exact hlast
      have hreach := reaches_of_chain_getElem hchain h0idx _ _ hlastidx
      have hwf : (Config.WF (Config.run s Tc)) := WF_of_reaches hreach
      have hei : s.EnabledInv :=
        enabledInv_chain hchain h0
          (fun s₀ hs₀ => by
            simp only [Config.state?, Option.some.injEq] at hs₀
            subst hs₀
            exact State.EnabledInv.initial)
          _ (List.mem_of_mem_getLast? hlast) s rfl
      have hchainτ : List.IsChain CTAStep τ := hτ.1.1.subtrace
      have h0τ : τ.head? = some (Config.run State.initial T) := hτ.1.2
      obtain ⟨sdτ, hdτ⟩ := hτ.2
      -- every valid point executes in the successful reference trace
      have hτtime : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          ∃ m, pointTime T τ η = some m := by
        intro η hidx
        have hidx' : η.idx < ((Config.run State.initial T).progOf η.thread).length := hidx
        obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdτ hidx'
        exact ⟨m, pointTime_eq_of_isTimeOf hm⟩
      -- ## the stuck configuration: no barrier full, every unfinished thread parked
      have hguard : ∀ b, s.B b = BarrierState.unconfigured ∨
          ∃ I A n, s.B b = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
        intro b
        rcases hsb : s.B b with ⟨I, A, cnt⟩
        cases cnt with
        | none =>
          obtain ⟨hI, hA⟩ := hwf.2.1 b I A hsb
          left
          rw [hI, hA]
          rfl
        | some n =>
          right
          obtain ⟨hle, hpark, -⟩ := hwf.1 b I A n hsb
          refine ⟨I, A, n, rfl, ?_⟩
          rcases Nat.lt_or_ge (I.length + A) (n : Nat) with h | h
          · exact h
          · exact absurd ⟨_, CTAStep.recycle hsb (by omega) hpark⟩ hstuck
      have hstep_of_enabled : ∀ (i : ThreadId) (c₀ : Cmd) (rest : Prog),
          Tc.prog i = c₀ :: rest → s.E i = true → False := by
        intro i c₀ rest hcons he
        have hi : i ∈ Tc.ids := by
          by_contra hni
          rw [Tc.nil_outside_ids i hni] at hcons
          exact absurd hcons (by simp)
        apply hstuck
        cases c₀ with
        | read g =>
          exact ⟨_, CTAStep.interleave hi hguard
            (by rw [hcons]; exact ThreadStep.read_noop)⟩
        | write g =>
          exact ⟨_, CTAStep.interleave hi hguard
            (by rw [hcons]; exact ThreadStep.write_noop)⟩
        | arrive b' n' =>
          rcases hguard b' with hu | ⟨I', A', m', hcfg, hlt⟩
          · exact ⟨_, CTAStep.interleave hi hguard
              (by rw [hcons]; exact ThreadStep.arrive_configure he hu)⟩
          · by_cases hmn : m' = n'
            · subst hmn
              have hpos : 0 < I'.length + A' := (hwf.1 b' I' A' m' hcfg).2.2
              exact ⟨_, CTAStep.interleave hi hguard
                (by rw [hcons]; exact ThreadStep.arrive_register he hcfg hpos hlt)⟩
            · exact ⟨_, CTAStep.error hguard
                (by rw [hcons]; exact ThreadStep.arrive_err_count he hcfg hmn)⟩
        | sync b' n' =>
          rcases hguard b' with hu | ⟨I', A', m', hcfg, hlt⟩
          · exact ⟨_, CTAStep.interleave hi hguard
              (by rw [hcons]; exact ThreadStep.sync_configure he hu)⟩
          · by_cases hmn : m' = n'
            · subst hmn
              have hpos : 0 < I'.length + A' := (hwf.1 b' I' A' m' hcfg).2.2
              exact ⟨_, CTAStep.interleave hi hguard
                (by rw [hcons]; exact ThreadStep.sync_block he hcfg hpos hlt)⟩
            · exact ⟨_, CTAStep.error hguard
                (by rw [hcons]; exact ThreadStep.sync_err_count he hcfg hmn)⟩
      -- ## program order in the reference trace
      have hpo : ∀ (x y : ProgPoint), x.thread = y.thread → x.idx < y.idx →
          ∀ mx my, pointTime T τ x = some mx → pointTime T τ y = some my →
          mx < my := by
        intro x y hth hidx mx my hmx hmy
        by_contra hge
        obtain ⟨hx1, hxlt, hxidx, C₁, C₂, hC₁, hC₂, hdropx, -⟩ :=
          pointTime_spec hchainτ h0τ hmx
        obtain ⟨hy1, hylt, hyidx, D₁, D₂, hD₁, hD₂, hdropy, -⟩ :=
          pointTime_spec hchainτ h0τ hmy
        have hsuf := progOf_suffix_index_le hchainτ x.thread hD₁
          (show my - 1 ≤ mx - 1 by omega) hC₁
        have hle := suffix_length_le hsuf
        rw [← hth] at hdropy hyidx
        rw [hdropx, hdropy] at hle
        simp only [List.length_drop] at hle
        omega
      -- ## a disabled unfinished thread is parked at its head `sync`, a member of
      -- its barrier's open round
      have hparked_point : ∀ (i : ThreadId), Tc.prog i ≠ [] → s.E i = false →
          ∃ (x : ProgPoint) (bx : Barrier) (nx : ℕ+),
            T.cmdAt x = some (.sync bx nx) ∧
            x ∈ genFiber T τ bx (recycleCount bx σ (σ.length - 1) + 1) ∧
            pointerAt T x (Config.run s Tc) ∧ s.E x.thread = false ∧
            x.thread = i ∧
            x.idx = (T.prog i).length - (Tc.prog i).length := by
        intro i hne hE
        obtain ⟨b_e, hdsy⟩ := hei i hE
        rcases hsb_e : s.B b_e with ⟨I_e, A_e, cnt_e⟩
        cases cnt_e with
        | none =>
          exfalso
          obtain ⟨hI0, -⟩ := hwf.2.1 b_e I_e A_e hsb_e
          rw [hsb_e] at hdsy
          have hdsy' : i ∈ I_e := hdsy
          rw [hI0] at hdsy'
          simp at hdsy'
        | some n_e =>
          have hpk := (hwf.1 b_e I_e A_e n_e hsb_e).2.1 i
            (by rw [hsb_e] at hdsy; exact hdsy)
          -- the head sits at the static pointer position
          have hsufi : (Config.run s Tc).progOf i <:+
              (Config.run State.initial T).progOf i :=
            progOf_suffix_index_le hchain i h0idx (Nat.zero_le _) hlastidx
          have hlen_le : (Tc.prog i).length ≤ (T.prog i).length :=
            suffix_length_le hsufi
          have hlen_pos : 0 < (Tc.prog i).length := by
            cases hTt : Tc.prog i with
            | nil => exact absurd hTt hne
            | cons a l => simp
          have hidxe : (T.prog i).length - (Tc.prog i).length < (T.prog i).length := by
            omega
          have hdropi : Tc.prog i =
              (T.prog i).drop ((T.prog i).length - (Tc.prog i).length) := by
            have h := List.IsSuffix.eq_drop hsufi
            exact h
          have hdd : (T.prog i).drop ((T.prog i).length - (Tc.prog i).length) =
              (T.prog i)[(T.prog i).length - (Tc.prog i).length]'hidxe ::
                (T.prog i).drop ((T.prog i).length - (Tc.prog i).length + 1) :=
            List.drop_eq_getElem_cons hidxe
          rw [hdropi, hdd] at hpk
          simp only [List.head?_cons, Option.some.injEq] at hpk
          have hcme : T.cmdAt ⟨i, (T.prog i).length - (Tc.prog i).length⟩ =
              some (Cmd.sync b_e n_e) := by
            have hg : (T.prog i)[(T.prog i).length - (Tc.prog i).length]? =
                some (Cmd.sync b_e n_e) := by
              rw [List.getElem?_eq_getElem hidxe, hpk]
            exact hg
          have hate : pointerAt T ⟨i, (T.prog i).length - (Tc.prog i).length⟩
              (Config.run s Tc) := by
            change (Tc.prog i).length =
              (T.prog i).length - ((T.prog i).length - (Tc.prog i).length)
            omega
          -- clause 2 produces the fiber member; pin it to the head point
          obtain ⟨-, -, hsync_e, -⟩ := hconf.state _ hlast s rfl b_e
          obtain ⟨x, hxF, hthx, ⟨n_x, hcmx⟩, hpx, hEx⟩ :=
            (hsync_e i).mp (by rw [hsb_e]; rw [hsb_e] at hdsy; exact hdsy)
          have hxidx : x.idx < (T.prog x.thread).length :=
            ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
          have hpx' : (Tc.prog x.thread).length =
              (T.prog x.thread).length - x.idx := hpx
          rw [hthx] at hpx' hxidx
          have hxid : x.idx = (T.prog i).length - (Tc.prog i).length := by omega
          have hxeq : x = ⟨i, (T.prog i).length - (Tc.prog i).length⟩ := by
            have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
            rw [hxeta, hthx, hxid]
          refine ⟨x, b_e, n_x, hcmx, hxF, hpx, ?_, hthx, hxid⟩
          rw [hthx]
          exact hE
      -- ## the descent: no parked sync has a τ-time (strong induction on that time)
      have hdescend : ∀ (nt : Nat) (u : ProgPoint) (b : Barrier) (n_u : ℕ+),
          T.cmdAt u = some (.sync b n_u) →
          u ∈ genFiber T τ b (recycleCount b σ (σ.length - 1) + 1) →
          pointerAt T u (Config.run s Tc) →
          s.E u.thread = false →
          pointTime T τ u = some nt → False := by
        intro nt
        induction nt using Nat.strong_induction_on with
        | _ nt ih =>
          intro u b n_u hcmu hufib hupt huE htu
          obtain ⟨hcount, harr, hsyncb, -⟩ := hconf.state _ hlast s rfl b
          have huI : u.thread ∈ (s.B b).synced :=
            (hsyncb u.thread).mpr ⟨u, hufib, rfl, ⟨n_u, hcmu⟩, hupt, huE⟩
          rcases hguard b with hu | ⟨I, A, n, hcfg, hlt⟩
          · rw [hu] at huI
            simp [BarrierState.unconfigured] at huI
          -- the open round completes in τ: `u`'s sync time is its recycle
          have hbaru : (T.cmdAt u).bind Cmd.barrier? = some b := by rw [hcmu]; rfl
          have hspecu := pointTime_spec hchainτ h0τ htu
          have hgenu : pointGen T τ u =
              recycleCount b σ (σ.length - 1) + 1 := (mem_genFiber.mp hufib).2.2
          have hpgu := pointGen_eq_of_pointTime hbaru htu
          have hsucc : recycleCount b τ nt =
              recycleCount b σ (σ.length - 1) + 1 := by
            obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ :=
              pointTime_sync_recycles hchainτ h0τ htu hcmu
            have h := recycleCount_succ_of_recycle b τ hC₁
              (by rw [show nt - 1 + 1 = nt by omega]; exact hC₂) hrec
            rw [show nt - 1 + 1 = nt by omega] at h
            omega
          have hcomplete : recycleCount b σ (σ.length - 1) + 1 ≤
              recycleCount b τ (τ.length - 1) := by
            have hmono := recycleCount_mono b τ
              (show nt ≤ τ.length - 1 by omega)
            omega
          -- the fiber has exactly `n` members, `A` of them executed arrives
          have hcnt : ∀ η ∈ genFiber T τ b (recycleCount b σ (σ.length - 1) + 1),
              (T.cmdAt η).bind Cmd.count? = some n := fun η hη =>
            hcount n (by rw [hcfg]) η hη
          have hg1 : 1 ≤ recycleCount b σ (σ.length - 1) + 1 := by omega
          have hlen : (genFiber T τ b (recycleCount b σ (σ.length - 1) + 1)).length =
              (n : Nat) := genFiber_length hτ hg1 hcomplete hufib (hcnt u hufib)
          have harrA : A = ((genFiber T τ b
              (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                isArriveCmd T η && (pointTime T σ η).isSome).length := by
            have h := harr
            rw [hcfg] at h
            exact h
          -- ## pigeonhole: some member is neither an executed arrive nor a parked sync
          have hsplitF : (genFiber T τ b
              (recycleCount b σ (σ.length - 1) + 1)).length =
              ((genFiber T τ b (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                isArriveCmd T η && (pointTime T σ η).isSome).length +
              ((genFiber T τ b (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                !(isArriveCmd T η && (pointTime T σ η).isSome)).length :=
            List.length_eq_length_filter_add _
          by_cases hex_d : ∃ d ∈ (genFiber T τ b
              (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                !(isArriveCmd T η && (pointTime T σ η).isSome),
              ¬(isSyncCmd T d = true ∧ pointerAt T d (Config.run s Tc) ∧
                s.E d.thread = false)
          case neg =>
            -- all unexecuted members parked: they inject into `I`, but there are
            -- more than `|I|` of them
            have hallp : ∀ x ∈ (genFiber T τ b
                (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                  !(isArriveCmd T η && (pointTime T σ η).isSome),
                isSyncCmd T x = true ∧ pointerAt T x (Config.run s Tc) ∧
                  s.E x.thread = false := by
              intro x hx
              by_contra hnx
              exact hex_d ⟨x, hx, hnx⟩
            have hmapsub : ∀ a ∈ ((genFiber T τ b
                (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                  !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                    ProgPoint.thread, a ∈ I := by
              intro a ha
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
              obtain ⟨hxsy, hxpt, hxE⟩ := hallp x hx
              have hxF := (List.mem_filter.mp hx).1
              obtain ⟨-, hbarx, -⟩ := mem_genFiber.mp hxF
              obtain ⟨n_x, hcmx⟩ : ∃ n_x : ℕ+, T.cmdAt x = some (.sync b n_x) := by
                cases hcm : T.cmdAt x with
                | none => rw [hcm] at hbarx; simp at hbarx
                | some cmd =>
                  cases cmd with
                  | read g₀ => rw [hcm] at hbarx; simp [Cmd.barrier?] at hbarx
                  | write g₀ => rw [hcm] at hbarx; simp [Cmd.barrier?] at hbarx
                  | arrive bb nn =>
                    simp [isSyncCmd, hcm] at hxsy
                  | sync bb nn =>
                    rw [hcm] at hbarx
                    simp only [Option.bind_some, Cmd.barrier?,
                      Option.some.injEq] at hbarx
                    exact ⟨nn, by rw [hbarx]⟩
              have hmem : x.thread ∈ (s.B b).synced :=
                (hsyncb x.thread).mpr ⟨x, hxF, rfl, ⟨n_x, hcmx⟩, hxpt, hxE⟩
              rw [hcfg] at hmem
              exact hmem
            have hmapnodup : (((genFiber T τ b
                (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                  !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                    ProgPoint.thread).Nodup := by
              refine List.Nodup.map_on ?_
                (List.Nodup.filter _ (genFiber_nodup T τ b _))
              intro x hx y hy hxy
              obtain ⟨-, hxpt, -⟩ := hallp x hx
              obtain ⟨-, hypt, -⟩ := hallp y hy
              have hxidx : x.idx < (T.prog x.thread).length :=
                ((mem_progPoints_iff T x).mp
                  (mem_genFiber.mp (List.mem_filter.mp hx).1).1).2
              have hyidx : y.idx < (T.prog y.thread).length :=
                ((mem_progPoints_iff T y).mp
                  (mem_genFiber.mp (List.mem_filter.mp hy).1).1).2
              have hxpt' : (Tc.prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hxpt
              have hypt' : (Tc.prog y.thread).length =
                  (T.prog y.thread).length - y.idx := hypt
              rw [hxy] at hxpt' hxidx
              have hid : x.idx = y.idx := by omega
              have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
              have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
              rw [hxeta, hyeta, hxy, hid]
            have hcard1 : (((genFiber T τ b
                (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                  !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                    ProgPoint.thread).toFinset.card =
                ((genFiber T τ b (recycleCount b σ (σ.length - 1) + 1)).filter
                  fun η => !(isArriveCmd T η && (pointTime T σ η).isSome)).length := by
              rw [List.toFinset_card_of_nodup hmapnodup, List.length_map]
            have hcard2 : (((genFiber T τ b
                (recycleCount b σ (σ.length - 1) + 1)).filter fun η =>
                  !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                    ProgPoint.thread).toFinset ⊆ I.toFinset := by
              intro a ha
              rw [List.mem_toFinset] at ha ⊢
              exact hmapsub a ha
            have hcard3 := Finset.card_le_card hcard2
            have hcard4 := List.toFinset_card_le I
            omega
          case pos =>
            obtain ⟨d, hdF2, hdnp⟩ := hex_d
            have hdF := (List.mem_filter.mp hdF2).1
            have hdcen : (isArriveCmd T d && (pointTime T σ d).isSome) = false := by
              have h := (List.mem_filter.mp hdF2).2
              cases hb : (isArriveCmd T d && (pointTime T σ d).isSome) with
              | false => rfl
              | true => rw [hb] at h; simp at h
            obtain ⟨hdmem, hdbar, hdgen⟩ := mem_genFiber.mp hdF
            have hdidx : d.idx < (T.prog d.thread).length :=
              ((mem_progPoints_iff T d).mp hdmem).2
            -- `d` has no σ-time
            have hdtime : pointTime T σ d = none := by
              cases hcmd : T.cmdAt d with
              | none => rw [hcmd] at hdbar; simp at hdbar
              | some cmd =>
                cases cmd with
                | read g₀ => rw [hcmd] at hdbar; simp [Cmd.barrier?] at hdbar
                | write g₀ => rw [hcmd] at hdbar; simp [Cmd.barrier?] at hdbar
                | arrive bb nn =>
                  cases hpt : pointTime T σ d with
                  | none => rfl
                  | some m =>
                    exfalso
                    simp [isArriveCmd, hcmd, hpt] at hdcen
                | sync bb nn =>
                  cases hpt : pointTime T σ d with
                  | none => rfl
                  | some m =>
                    exfalso
                    -- an executed sync of the *open* round out-runs the recycle count
                    have hbb : bb = b := by
                      rw [hcmd] at hdbar
                      simp only [Option.bind_some, Cmd.barrier?,
                        Option.some.injEq] at hdbar
                      exact hdbar
                    subst hbb
                    obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ :=
                      pointTime_sync_recycles hchain h0 hpt hcmd
                    have hspecd := pointTime_spec hchain h0 hpt
                    have hsuccd := recycleCount_succ_of_recycle bb σ hC₁
                      (by rw [show m - 1 + 1 = m by omega]; exact hC₂) hrec
                    rw [show m - 1 + 1 = m by omega] at hsuccd
                    have hpgd := pointGen_eq_of_pointTime hdbar hpt
                    have hgeq := hconf.gen_eq d hdmem m hpt
                    have hmono := recycleCount_mono bb σ
                      (show m ≤ σ.length - 1 by omega)
                    omega
            -- so `d` has not been passed: its thread is unfinished
            have hnpassed : (T.prog d.thread).length - d.idx ≤
                (Tc.prog d.thread).length := by
              by_contra hlt'
              obtain ⟨m, hm⟩ := exists_pointTime_of_passed hchain h0 hlast hdidx
                (by change (Tc.prog d.thread).length + (d.idx + 1) ≤ _; omega)
              have hm' : pointTime T σ d = some m := hm
              rw [hdtime] at hm'
              exact absurd hm' (by simp)
            have hdne : Tc.prog d.thread ≠ [] := by
              intro h0'
              rw [h0'] at hnpassed
              simp at hnpassed
              omega
            -- ... and disabled (else it could step)
            have hdE : s.E d.thread = false := by
              cases hE : s.E d.thread with
              | false => rfl
              | true =>
                obtain ⟨c₀, rest, hcons⟩ : ∃ c₀ rest,
                    Tc.prog d.thread = c₀ :: rest := by
                  cases hTt : Tc.prog d.thread with
                  | nil => exact absurd hTt hdne
                  | cons a l => exact ⟨a, l, rfl⟩
                exact (hstep_of_enabled d.thread c₀ rest hcons hE).elim
            -- parked at its head sync `e`, strictly before `d`
            obtain ⟨e, b_e, n_e, hcme, heF, hept, heE, heth, heidx⟩ :=
              hparked_point d.thread hdne hdE
            have hlt_idx : e.idx < d.idx := by
              have hle_idx : e.idx ≤ d.idx := by
                rw [heidx]
                omega
              rcases Nat.lt_or_ge e.idx d.idx with h | h
              · exact h
              · exfalso
                -- at equality `e = d`, so `d` is a parked sync — excluded
                have hed : e = d := by
                  have heeta : e = ⟨e.thread, e.idx⟩ := rfl
                  have hdeta : d = ⟨d.thread, d.idx⟩ := rfl
                  rw [heeta, hdeta, heth, show e.idx = d.idx by omega]
                rw [hed] at hcme hept
                exact hdnp ⟨by simp [isSyncCmd, hcme], hept, hdE⟩
            -- τ-times and the descent
            obtain ⟨m_d, hmd⟩ := hτtime d hdidx
            have heidx' : e.idx < (T.prog e.thread).length :=
              ((mem_progPoints_iff T e).mp (mem_genFiber.mp heF).1).2
            obtain ⟨m_e, hme⟩ := hτtime e heidx'
            -- program order: `e` runs strictly before `d` in τ
            have hlt_time : m_e < m_d := hpo e d heth hlt_idx m_e m_d hme hmd
            -- fiber bound: `d` runs no later than the recycle that is `u`'s time
            have hle_time : m_d ≤ nt := by
              have hpgd := pointGen_eq_of_pointTime hdbar hmd
              have hspecd := pointTime_spec hchainτ h0τ hmd
              rcases Nat.lt_or_ge nt m_d with h | h
              · exfalso
                have hmono := recycleCount_mono b τ
                  (show nt ≤ m_d - 1 by omega)
                omega
              · omega
            exact ih m_e (by omega) e b_e n_e hcme heF hept heE hme
      -- ## seed the descent: the stuck non-`done` configuration has a parked sync
      have hndone : ¬ CTA.IsDone Tc := by
        intro hdone
        refine hstuck ⟨_, CTAStep.done hdone ?_⟩
        intro b I A n hb
        rcases hguard b with hu | ⟨I', A', n', hcfg, hlt⟩
        · rw [hu] at hb
          exact absurd (congrArg BarrierState.count hb) (by simp [BarrierState.unconfigured])
        · rw [hcfg] at hb
          have hI : I' = I := congrArg BarrierState.synced hb
          have hA : A' = A := congrArg BarrierState.arrived hb
          have hn : (some n' : Option ℕ+) = some n := congrArg BarrierState.count hb
          obtain rfl := Option.some.inj hn
          have hIlen : I'.length = I.length := congrArg List.length hI
          omega
      obtain ⟨i₀, hi₀ne⟩ : ∃ i, Tc.prog i ≠ [] := by
        by_contra hall
        apply hndone
        intro i hi
        by_contra hne'
        exact hall ⟨i, hne'⟩
      have hE₀ : s.E i₀ = false := by
        cases hE : s.E i₀ with
        | false => rfl
        | true =>
          obtain ⟨c₀, rest, hcons⟩ : ∃ c₀ rest, Tc.prog i₀ = c₀ :: rest := by
            cases hTt : Tc.prog i₀ with
            | nil => exact absurd hTt hi₀ne
            | cons a l => exact ⟨a, l, rfl⟩
          exact (hstep_of_enabled i₀ c₀ rest hcons hE).elim
      obtain ⟨x₀, b₀, n₀, hcm₀, hF₀, hpt₀, hE₀', -, -⟩ :=
        hparked_point i₀ hi₀ne hE₀
      have hx₀idx : x₀.idx < (T.prog x₀.thread).length :=
        ((mem_progPoints_iff T x₀).mp (mem_genFiber.mp hF₀).1).2
      obtain ⟨n_t, hnt⟩ := hτtime x₀ hx₀idx
      exact hdescend n_t x₀ b₀ n₀ hcm₀ hF₀ hpt₀ hE₀' hnt

/-! ## Theorem 1 — soundness of `CheckWellSynchronized`

The paper's **Theorem 1**: a successful run of the check witnesses
well-synchronization. Assembled (the paper's Theorem 8) from Theorem 6
(`conforms_of_traceFrom`) and Theorem 7 (`conforms_complete_done`): every complete
challenger trace conforms and ends `done`, so every barrier op executes in it with its
reference generation — the common, nonzero witness `Config.WellSynchronized` asks for.
*Not* via Lemma 1, which would be circular (only well-synchronized configurations are
known to have a sound `R`); clause 3 of `Conforms` is the non-circular, time-indexed
replacement. -/

/-- **Theorem 1.** If `τ` is a complete trace from `(I, T)` ending in `done`
(`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns `true`, then `T`
is well-synchronized.

Note (rohany): This is a top-level theorem.
-/
theorem wellSynchronized_of_check {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true) :
    T.WellSynchronized := by
  refine ⟨⟨State.initial, T, rfl⟩, ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₂ η hbar
  obtain ⟨b, hbarb⟩ := hbar
  have hbar' : (T.cmdAt η).bind Cmd.barrier? = some b := hbarb
  have hmem : η ∈ T.progPoints := by
    cases hc : T.cmdAt η with
    | none => rw [hc] at hbar'; simp at hbar'
    | some c => exact mem_progPoints_of_cmdAt T hc
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  -- both challenger traces conform (Theorem 6) and end `done` (Theorem 7)
  have hc₁ : Conforms T τ τ₁ := conforms_of_traceFrom hτ hcheck ⟨hτ₁.1.subtrace, hτ₁.2⟩
  have hc₂ : Conforms T τ τ₂ := conforms_of_traceFrom hτ hcheck ⟨hτ₂.1.subtrace, hτ₂.2⟩
  obtain ⟨s₁, hd₁⟩ := conforms_complete_done hτ hτ₁ hc₁
  obtain ⟨s₂, hd₂⟩ := conforms_complete_done hτ hτ₂ hc₂
  -- `η` executes in each, and clause 1 transports the reference generation
  obtain ⟨m₁, hm₁⟩ := exists_time_of_ends_done hτ₁ hd₁ hidx
  obtain ⟨m₂, hm₂⟩ := exists_time_of_ends_done hτ₂ hd₂ hidx
  have hg₁ : pointGen T τ₁ η = pointGen T τ η :=
    hc₁.gen_eq η hmem m₁ (pointTime_eq_of_isTimeOf hm₁)
  have hg₂ : pointGen T τ₂ η = pointGen T τ η :=
    hc₂.gen_eq η hmem m₂ (pointTime_eq_of_isTimeOf hm₂)
  refine ⟨pointGen T τ η, ?_, ?_⟩
  · have h := isGenOf_pointGen hbar' hm₁; rwa [hg₁] at h
  · have h := isGenOf_pointGen hbar' hm₂; rwa [hg₂] at h

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

Proof (`not_wellSynchronized_of_check_false`, §5.2.7). Assume `T.WellSynchronized` and
`check = false`; derive `False`. `exists_failing_pair` extracts a flagged pair — a
generation-`k` `sync` `c1` on `b` and a generation-`k+1` barrier op `c2` on `b` with
in-thread predecessor `c3` — with `(c1, c3) ∉ (CheckWellSynchronized T τ).2`. The `sync`
self-loop forces `c1 ≠ c3`, so the `transClosure` converse (`mem_transClosure_of_transGen`,
the now-proved Pillar A) gives `¬ happensBefore T τ c1 c3`. Then, by the command of `c2`:

  * `c2` an **arrive** — the only edge into an `arrive` is program order from `c3`
    (`happensBefore_arrive`), so `¬ happensBefore c1 c2`; the realizability lemma runs
    `c2` before `c1`, where it would observe generation `≤ k ≠ k+1` — contradiction
    (`reverse_barrier_contradiction`).
  * `c2` a **sync** — split on `happensBefore c1 c2`. If `¬ happensBefore c1 c2`, `c2`
    runs before `c1` exactly as above. Otherwise `c2` is forced after `c1`, and the
    *operational* competing-sync reversal (`competing_sync_false`) runs the ideal `G`
    to a configuration where `c1` and `c2` both head their threads poised to `sync b`,
    then fires `c2` into `c1`'s round (generation `≤ k`, or `err`) — again contradicting
    schedule-independence of generations.

All of this is *proved* here except `competing_sync_false` (the one operational stub) and
the realizability/preciseness input (`exists_reversing_trace` / `happensBefore_precise`,
which `reverse_barrier_contradiction` consumes). Pillar A (`mem_transClosure_of_transGen`),
the bridge, the arrive case, and the failing-pair extraction are complete. -/


/-- **Competing-sync reversal** — the `sync` sub-case of completeness, in the situation
where `c2` *is* forced after `c1` (`happensBefore c1 c2`). Two `sync`s, `c1` (generation
`k`) and `c2` (generation `k+1`), on the same barrier `b`, with `c2`'s in-thread
predecessor `c3` *not* ordered after `c1` (`¬ happensBefore c1 c3`).

Argument (per §5.2.7, the named-barrier case): run the ideal `G = {η | ¬ happensBefore c1 η}`
to its cut configuration. There `c1` heads its thread (`c1 ∈ F`) and `c2` heads its thread
(`c3 ∈ G` is `c2`'s predecessor, `c2 ∈ F`) — two threads both poised to `sync b`. Step
`c2` *instead of* `c1`: `c2` registers in `b`'s current round (so generation `≤ k`), or, if
that over-fills / mismatches the barrier, steps to `err`. Completing the trace gives a
complete trace in which `c2` does **not** have generation `k+1` — contradicting `hws`
(which fixes every `sync`'s generation across all complete traces).

This uses the *direct* run-`G`-then-step-`c2` construction; it does **not** factor through
the matching-arrive idea (false: `sync_configure` registers a thread directly, with no prior
`arrive`). It is built on the (sorried) `run_ideal` cut and `hws`-driven generation transfer. -/
theorem competing_sync_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 c2 : ProgPoint} {b : Barrier} {nn mm : ℕ+}
    (hc1 : c1 ∈ T.progPoints) (hc2 : c2 ∈ T.progPoints)
    (hcmd1 : T.cmdAt c1 = some (.sync b nn)) (hcmd2 : T.cmdAt c2 = some (.sync b mm))
    (hgen : pointGen T τ c2 = pointGen T τ c1 + 1) (hidx : 1 ≤ c2.idx)
    (hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩)
    (hhb : happensBefore T τ c1 c2) : False := by
  -- `c3 = pred(c2)` is a valid program point
  have hc3mem : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T c2).mp hc2
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- the ideal cut splits `c2`'s thread *exactly* at `c2` (`c3 ∈ G`, `c2 ∈ F`)
  have hfcut : fcut T τ c1 c2.thread = c2.idx := by
    have h1 : fcut T τ c1 c2.thread ≤ c2.idx := fcut_le_of_hb hhb hc2
    have h2 := lt_fcut_of_not_hb hnothb3 hc3mem
    simp only at h2
    omega
  -- run `G` to the cut configuration; `c2` heads its thread there
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ := run_ideal (τ := τ) (η₁ := c1) hτ hws
  have hc2head : T_G.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    rw [hcutprog c2.thread, hfcut]
  -- in `τ'`, `c1` executes (recycles `b`) at some time `n1`
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hc1L : c1.idx < ((Config.run State.initial T).progOf c1.thread).length :=
    ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨n1, hn1⟩ := exists_time_of_ends_done hcomp hdone hc1L
  classical
  have hchain := hcomp.1.subtrace
  -- `c1` executes strictly after the cut (`c1 ∈ F`)
  have hfcutc1 : fcut T τ c1 c1.thread ≤ c1.idx := fcut_le_of_hb Relation.ReflTransGen.refl hc1
  have hpn1 : p < n1 := by
    refine lt_time_of_lt_progOf hn1 hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog c1.thread, List.length_drop]
    have : c1.idx < (T.prog c1.thread).length := hc1L
    omega
  -- `c1` is parked in `b.synced` at the configuration just before its recycle
  obtain ⟨s1, T1, hC1, hc1synced⟩ :
      ∃ s1 T1, τ'[n1 - 1]? = some (Config.run s1 T1) ∧ c1.thread ∈ (s1.B b).synced := by
    have hn1' := hn1
    obtain ⟨_, _, jj, C, C', hjj, hCj, hCj1, _, _⟩ := hn1'
    obtain rfl : jj = n1 - 1 := by omega
    obtain ⟨s1, T1, rfl⟩ : ∃ s T, C = Config.run s T := by
      cases chain_step hchain hCj hCj1 <;> exact ⟨_, _, rfl⟩
    exact ⟨s1, T1, hCj, synced_before_recycle hn1 rfl hcmd1 hCj⟩
  -- so there is a first configuration after the cut with a nonempty synced list
  have hwit : ∃ s T, τ'[p + (n1 - 1 - p)]? = some (Config.run s T) ∧
      ∃ b' t', t' ∈ (s.B b').synced :=
    ⟨s1, T1, by rw [show p + (n1 - 1 - p) = n1 - 1 from by omega]; exact hC1,
      b, c1.thread, hc1synced⟩
  have hPex : ∃ d, ∃ s T, τ'[p + d]? = some (Config.run s T) ∧ ∃ b' t', t' ∈ (s.B b').synced :=
    ⟨n1 - 1 - p, hwit⟩
  set d₀ := Nat.find hPex with hd₀
  have hd₀spec := Nat.find_spec hPex
  rw [← hd₀] at hd₀spec
  obtain ⟨sq', Tq', hCq', b', t', hjoin⟩ := hd₀spec
  -- `d₀ > 0` since synced lists are empty at the cut
  have hd₀pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · exfalso
      rw [h, Nat.add_zero, hcut, Option.some.injEq, Config.run.injEq] at hCq'
      obtain ⟨rfl, rfl⟩ := hCq'; exact hsempty b' t' hjoin
    · exact h
  -- at the firing config `q-1 = p + (d₀-1)`, synced lists are still empty
  have hq1 : ¬ (∃ s T, τ'[p + (d₀ - 1)]? = some (Config.run s T) ∧ ∃ b' t', t' ∈ (s.B b').synced) :=
    Nat.find_min hPex (by omega)
  -- the firing happens within `c1`'s round: `q = p + d₀ ≤ n1 - 1 < n1`
  have hqn1 : p + d₀ ≤ n1 - 1 := by
    have hle : d₀ ≤ n1 - 1 - p := hd₀ ▸ Nat.find_le hwit
    omega
  have hqlen : p + d₀ < τ'.length := (List.getElem?_eq_some_iff.mp hCq').1
  have hget : ∀ j, j ≤ p + d₀ → ∃ C, τ'[j]? = some C :=
    fun j hj => ⟨_, List.getElem?_eq_getElem (show j < τ'.length by omega)⟩
  -- shared chain invariants
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have hwfAll : ∀ C ∈ τ', C.WF := WF_chain hchain hC₀head WF_initial
  have hei0 : ∀ s, (Config.state? (Config.run State.initial T)) = some s → s.EnabledInv := by
    intro s hs
    simp only [Config.state?, Option.some.injEq] at hs; subst hs; exact State.EnabledInv.initial
  have heiAll : ∀ C ∈ τ', ∀ s, C.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hC₀head hei0
  -- `c2`'s static facts
  have hc1L_c2 : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
  have hcmd2_get : (T.prog c2.thread)[c2.idx]'hc1L_c2 = Cmd.sync b mm := by
    have h := hcmd2; simp only [CTA.cmdAt] at h
    rw [List.getElem?_eq_getElem hc1L_c2, Option.some.injEq] at h; exact h
  have hdrop2 : (T.prog c2.thread).drop c2.idx
      = Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [List.drop_eq_getElem_cons hc1L_c2, hcmd2_get]
  -- **Program invariance**: while synced stays empty (configs `p … q-1`), `c2` cannot
  -- step (a `sync` step would join a synced list), so it stays poised at its head.
  have hinv : ∀ e, e ≤ d₀ - 1 → ∃ s' T', τ'[p + e]? = some (Config.run s' T') ∧
      T'.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    intro e
    induction e with
    | zero => intro _; exact ⟨s_G, T_G, by simpa using hcut, hc2head⟩
    | succ e ih =>
      intro he
      obtain ⟨s', T', hCe, hprog⟩ := ih (by omega)
      obtain ⟨C'', hCe1⟩ := hget (p + (e + 1)) (by omega)
      have hstep : CTAStep (Config.run s' T') C'' :=
        chain_step hchain (show τ'[p + e]? = some _ from hCe) (show τ'[(p + e) + 1]? = _ from hCe1)
      -- `C''` is a run: it is not the last config (`< q`), so it has a successor
      obtain ⟨Cnext, hCnext⟩ := hget (p + (e + 1) + 1) (by omega)
      obtain ⟨s'', T'', rfl⟩ : ∃ s T, C'' = Config.run s T := by
        cases chain_step hchain (show τ'[p + (e + 1)]? = _ from hCe1)
          (show τ'[p + (e + 1) + 1]? = _ from hCnext) <;> exact ⟨_, _, rfl⟩
      refine ⟨s'', T'', hCe1, ?_⟩
      -- synced is empty at `p+e` and at `p+(e+1)` (both `< d₀`)
      have hsemp_e1 : ∀ bb tt, tt ∉ (s''.B bb).synced := fun bb tt htt =>
        Nat.find_min hPex (show e + 1 < d₀ by omega) ⟨s'', T'', hCe1, bb, tt, htt⟩
      have hsemp_e : ∀ bb tt, tt ∉ (s'.B bb).synced := fun bb tt htt =>
        Nat.find_min hPex (show e < d₀ by omega) ⟨s', T', hCe, bb, tt, htt⟩
      cases hstep with
      | @interleave _ _ _ i P' hi hbar hth =>
        by_cases hic2 : i = c2.thread
        · exfalso
          subst hic2
          rw [hprog, hdrop2] at hth
          cases hth with
          | sync_configure he hb => exact hsemp_e1 b c2.thread (by simp [Function.update_self])
          | sync_block he hb _ _ => exact hsemp_e1 b c2.thread (by simp [Function.update_self])
        · simp only [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hic2)]; exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e bb x (by rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
  -- **Firing config** `q-1`: `c2` poised at head, enabled, with `hbar` holding.
  have hmem : ∀ {j C}, τ'[j]? = some C → C ∈ τ' := fun hj => List.mem_of_getElem? hj
  obtain ⟨sm, Tm, hCq1, hprogm⟩ := hinv (d₀ - 1) (le_refl _)
  have hsemp_q1 : ∀ bb tt, tt ∉ (sm.B bb).synced := fun bb tt htt =>
    hq1 ⟨sm, Tm, hCq1, bb, tt, htt⟩
  have hheadm : Tm.prog c2.thread = Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [hprogm, hdrop2]
  have hc2ids : c2.thread ∈ Tm.ids := by
    by_contra hni
    rw [Tm.nil_outside_ids c2.thread hni] at hheadm
    exact (List.cons_ne_nil _ _) hheadm.symm
  have hc2en : sm.E c2.thread = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    obtain ⟨bb, hbb⟩ := heiAll _ (hmem hCq1) sm rfl c2.thread hne
    exact hsemp_q1 bb c2.thread hbb
  have hCq'' : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run sq' Tq') := by
    rw [show (p + (d₀ - 1)) + 1 = p + d₀ from by omega]; exact hCq'
  have hstepq : CTAStep (Config.run sm Tm) (Config.run sq' Tq') := chain_step hchain hCq1 hCq''
  have hbarq : ∀ b'', sm.B b'' = BarrierState.unconfigured ∨
      ∃ I A n, sm.B b'' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) :=
    hbar_of_joins_synced hstepq rfl rfl (hsemp_q1 b' t') hjoin
  have hwfq : (Config.WF (Config.run sm Tm)) := hwfAll _ (hmem hCq1)
  -- reachability of the firing config (for `barriersWithin`)
  have hreach : ∀ j, j ≤ p + d₀ → ∀ C, τ'[j]? = some C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C := by
    intro j
    induction j with
    | zero =>
      intro _ C hC
      rw [← List.head?_eq_getElem?, hC₀head, Option.some.injEq] at hC
      subst hC; exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj C hC
      obtain ⟨Cj, hCj⟩ := hget j (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega) Cj hCj) (chain_step hchain hCj hC)
  have hreachq1 : Relation.ReflTransGen CTAStep (Config.run State.initial T) (Config.run sm Tm) :=
    hreach (p + (d₀ - 1)) (by omega) _ hCq1
  -- shared prefix facts: `pre = τ'.take (p+d₀)` ends at the firing config `q-1`
  have hprelen : (τ'.take (p + d₀)).length = p + d₀ := by rw [List.length_take]; omega
  have hpne : τ'.take (p + d₀) ≠ [] := by
    intro h; rw [h, List.length_nil] at hprelen; omega
  have hprechain : List.IsChain CTAStep (τ'.take (p + d₀)) := hchain.take _
  have hpre_get : ∀ i, i < p + d₀ → (τ'.take (p + d₀))[i]? = τ'[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hprehead : (τ'.take (p + d₀)).head? = some (Config.run State.initial T) := by
    rw [List.head?_eq_getElem?, hpre_get 0 (by omega), ← List.head?_eq_getElem?]; exact hC₀head
  have hprelast : (τ'.take (p + d₀)).getLast? = some (Config.run sm Tm) := by
    rw [List.getLast?_eq_getElem?, hprelen, hpre_get (p + d₀ - 1) (by omega),
      show p + d₀ - 1 = p + (d₀ - 1) from by omega]
    exact hCq1
  -- gluing: a complete trace from any successor of the firing config extends `pre`
  have glue : ∀ (σ : List Config) (Cstart : Config), IsCompleteTraceFrom Cstart σ →
      CTAStep (Config.run sm Tm) Cstart →
      IsCompleteTraceFrom (Config.run State.initial T) (τ'.take (p + d₀) ++ σ) := by
    intro σ Cstart hσ hcon
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.IsChain.append hprechain hσ.1.subtrace ?_
      intro x hx y hy
      rw [hprelast, Option.mem_some_iff] at hx; subst hx
      rw [hσ.2, Option.mem_some_iff] at hy; subst hy
      exact hcon
    · obtain ⟨Cn, hCnlast, hterm⟩ := hσ.1.ends
      exact ⟨Cn, List.mem_getLast?_append_of_mem_getLast? hCnlast, hterm⟩
    · rw [List.head?_append_of_ne_nil _ hpne]; exact hprehead
  -- **Fire `c2` early.** From the firing config it either joins `synced b` or errors.
  have hc2step : (∃ sN, CTAStep (Config.run sm Tm)
        (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) ∧
        c2.thread ∈ (sN.B b).synced) ∨ CTAStep (Config.run sm Tm) (Config.err Tm) := by
    rcases hbarq b with hbu | ⟨I, A, n', hbcfg, hltn⟩
    · -- unconfigured → `sync_configure`
      have hcta := CTAStep.interleave hc2ids hbarq
        (by rw [hheadm]; exact ThreadStep.sync_configure hc2en hbu)
      exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
    · have hI : I = [] := by
        rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
        · exact h
        · exact absurd (hsemp_q1 b x (by rw [hbcfg]; simp)) (by simp)
      subst hI
      have hApos : 0 < A := by simpa using (hwfq.1 b [] A n' hbcfg).2.2
      by_cases hmm : n' = mm
      · rw [hmm] at hbcfg hltn
        have hcta := CTAStep.interleave hc2ids hbarq
          (by rw [hheadm];
              exact ThreadStep.sync_block hc2en hbcfg (by simpa using hApos) (by simpa using hltn))
        exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
      · exact Or.inr (CTAStep.error hbarq
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmm))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced b`: complete the trace, then read off a generation clash
    have hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b := by rw [hcmd1]; rfl
    have hc2bar : (T.cmdAt c2).bind Cmd.barrier? = some b := by rw [hcmd2]; rfl
    have hbne : sN.B b ≠ BarrierState.unconfigured := by
      intro hcon; rw [hcon] at hsync; simp [BarrierState.unconfigured] at hsync
    have hbwN : (Config.barriersWithin T.barrierSet (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1))))) :=
      inv_preserved T.barrierSet hcstep (barriersWithin_of_reaches hreachq1)
    obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
    set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
    have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' := glue σ _ hσ hcstep
    obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
    obtain ⟨m2, hm2⟩ := exists_time_of_ends_done htrace hdone'' (η := c2) hc1L_c2
    -- `c2` is parked in `synced b` at index `p+d₀` of `τ''`, poised at its `sync`
    have hCpark : τ''[p + d₀]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
        ← List.head?_eq_getElem?]
      exact hσ.2
    have hprogpark : (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1))).prog c2.thread
        = ((Config.run State.initial T).progOf c2.thread).drop c2.idx := by
      change (Function.update Tm.prog c2.thread _) c2.thread = _
      rw [Function.update_self]; exact hdrop2.symm
    have hBI'' : ∀ C ∈ τ'', ∀ s, C.state? = some s → s.BlockInv := by
      refine blockInv_chain htrace.1.subtrace htrace.2 ?_
      intro s hs; simp only [Config.state?, Option.some.injEq] at hs; subst hs
      exact State.BlockInv.initial
    have hpn : p + d₀ < m2 := by
      refine lt_time_of_lt_progOf hm2 hCpark ?_
      rw [show (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))).progOf c2.thread
          = ((Config.run State.initial T).progOf c2.thread).drop c2.idx from hprogpark,
        List.length_drop]
      have hX : c2.idx < ((Config.run State.initial T).progOf c2.thread).length := hc1L_c2
      omega
    -- parked ⟹ `recycleCount` is unchanged between parking and recycle
    have heq3 : recycleCount b τ'' (m2 - 1) = recycleCount b τ'' (p + d₀) :=
      parked_sync_recycleCount hBI'' rfl hm2 hCpark hsync hprogpark hpn
    -- `τ''` agrees with `τ'` on configs `0 … p+d₀-1`
    have hshare : ∀ j, j < p + d₀ → τ''[j]? = τ'[j]? := by
      intro j hj
      rw [hτ''def, List.getElem?_append_left (by rw [hprelen]; exact hj)]
      exact hpre_get j hj
    -- the firing step itself does not recycle `b` (it joins `synced b`)
    have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
      rw [hshare (p + (d₀ - 1)) (by omega)]; exact hCq1
    have hCpark'' : τ''[p + (d₀ - 1) + 1]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]; exact hCpark
    have hstepfalse : stepRecyclesBarrier b (Config.run sm Tm) (Config.run sN
        (Tm.set c2.thread hc2ids (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) =
        false := by
      simp [stepRecyclesBarrier, Config.state?, hbne]
    have heq4 : recycleCount b τ'' (p + d₀) = recycleCount b τ' (p + (d₀ - 1)) := by
      have hsucc : recycleCount b τ'' (p + d₀) = recycleCount b τ'' (p + (d₀ - 1)) := by
        rw [show p + d₀ = (p + (d₀ - 1)) + 1 from by omega]
        exact recycleCount_succ_of_not_recycle b hCq1'' hCpark'' hstepfalse
      rw [hsucc]
      exact recycleCount_prefix_eq b (p + (d₀ - 1)) (fun j hj => hshare j (by omega))
    -- transfer generations across traces via well-synchronization
    obtain ⟨sτ, hdoneτ⟩ := hτ.2
    obtain ⟨m1τ, hm1τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c1) hc1L
    obtain ⟨m2τ, hm2τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c2) hc1L_c2
    have gen_in : ∀ (σ' : List Config) (η : ProgPoint) (bb : Barrier),
        IsCompleteTraceFrom (Config.run State.initial T) σ' →
        (T.cmdAt η).bind Cmd.barrier? = some bb →
        (∃ mτ, IsTimeOf (Config.run State.initial T) τ η mτ) →
        IsGenOf (Config.run State.initial T) σ' η (some (pointGen T τ η)) := by
      intro σ' η bb hσ' hbar hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (some (pointGen T τ η)) :=
        isGenOf_pointGen hbar hmτ
      obtain ⟨g, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η ⟨bb, hbar⟩
      rwa [IsGenOf.unique hgτ hgenτ] at hgσ
    have hgenc1 : pointGen T τ c1 = recycleCount b τ' (n1 - 1) + 1 :=
      isGenOf_recycleCount (gen_in τ' c1 b hcomp hc1bar ⟨m1τ, hm1τ⟩) hc1bar hn1
    have hgenc2 : pointGen T τ c2 = recycleCount b τ'' (m2 - 1) + 1 :=
      isGenOf_recycleCount (gen_in τ'' c2 b htrace hc2bar ⟨m2τ, hm2τ⟩) hc2bar hm2
    have hmono : recycleCount b τ' (p + (d₀ - 1)) ≤ recycleCount b τ' (n1 - 1) :=
      recycleCount_mono b τ' (show p + (d₀ - 1) ≤ n1 - 1 from by omega)
    omega
  · -- count-mismatch: the spliced trace ends in `err`, impossible for a WS CTA
    exfalso
    have herrtrace : IsCompleteTraceFrom (Config.err Tm) [Config.err Tm] :=
      ⟨⟨List.isChain_singleton _, Config.err Tm, by simp, Or.inr (Or.inl ⟨Tm, rfl⟩)⟩, by simp⟩
    obtain ⟨sd2, hdone2⟩ :=
      CTA.WellSynchronized.completeTrace_ends_done hws (glue _ _ herrtrace herr)
    have hgl : (τ'.take (p + d₀) ++ [Config.err Tm]).getLast? = some (Config.err Tm) := by simp
    rw [hgl] at hdone2; simp at hdone2

/-- **Competing arrive/sync reversal** — the operational analog of `competing_sync_false`
for an `arrive` *source*. The flagged source `c1` is an `arrive b` of generation `k`; `c2`
is a `sync b` of generation `k+1` whose in-thread predecessor `c3` is *not* ordered after
`c1` (`¬ happensBefore c1 c3`), yet `c2` *is* forced after `c1` (`happensBefore c1 c2`).

This is the new obligation introduced by extending Step 3's generation check to `arrive`
sources (not just `sync`s). The intended argument mirrors `competing_sync_false`: run the
ideal `G = {η | ¬ happensBefore c1 η}` to its cut, where `c1` heads its thread poised to
`arrive b` and `c2` heads its thread poised to `sync b`; step `c2` into `b`'s still-open
round (generation `≤ k`, or `err` on over-fill), contradicting `hws`. Unlike the `sync`
case, the source `c1` parks in `b.arrived` (not `b.synced`) when it executes, so the
firing-configuration witness (`synced_before_recycle` in `competing_sync_false`) must be
re-derived from the `arrived` list. Stated here as the single isolated operational stub for
the `arrive`-source path; it rests on the same `run_ideal` cut as `competing_sync_false`. -/
theorem competing_arrive_sync_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 c2 : ProgPoint} {b : Barrier} {nn mm : ℕ+}
    (hc1 : c1 ∈ T.progPoints) (hc2 : c2 ∈ T.progPoints)
    (hcmd1 : T.cmdAt c1 = some (.arrive b nn)) (hcmd2 : T.cmdAt c2 = some (.sync b mm))
    (hgen : pointGen T τ c2 = pointGen T τ c1 + 1) (hidx : 1 ≤ c2.idx)
    (hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩)
    (hhb : happensBefore T τ c1 c2) : False := by
  -- `c3 = pred(c2)` is a valid program point
  have hc3mem : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T c2).mp hc2
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- the ideal cut splits `c2`'s thread *exactly* at `c2` (`c3 ∈ G`, `c2 ∈ F`)
  have hfcut : fcut T τ c1 c2.thread = c2.idx := by
    have h1 : fcut T τ c1 c2.thread ≤ c2.idx := fcut_le_of_hb hhb hc2
    have h2 := lt_fcut_of_not_hb hnothb3 hc3mem
    simp only at h2
    omega
  -- run `G` to the cut configuration; `c2` heads its thread there
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ := run_ideal (τ := τ) (η₁ := c1) hτ hws
  have hc2head : T_G.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    rw [hcutprog c2.thread, hfcut]
  -- in `τ'`, `c1` executes (arrives at `b`, an *interleave* step) at some time `n1`
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hc1L : c1.idx < ((Config.run State.initial T).progOf c1.thread).length :=
    ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨n1, hn1⟩ := exists_time_of_ends_done hcomp hdone hc1L
  classical
  have hchain := hcomp.1.subtrace
  -- `c1` executes strictly after the cut (`c1 ∈ F`)
  have hfcutc1 : fcut T τ c1 c1.thread ≤ c1.idx := fcut_le_of_hb Relation.ReflTransGen.refl hc1
  have hpn1 : p < n1 := by
    refine lt_time_of_lt_progOf hn1 hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog c1.thread, List.length_drop]
    have : c1.idx < (T.prog c1.thread).length := hc1L
    omega
  -- `c1`'s arrive step `n1-1 → n1` advances `c1`; in particular the config at `n1` is a `run`.
  obtain ⟨hcomp', hidxL1, j1, C1a, C1a', hj1eq, hC1a, hC1a', hC1aprog, hC1a'prog⟩ := id hn1
  have hC1aget : τ'[n1]? = some C1a' := by rw [hj1eq]; exact hC1a'
  have hC1astep : CTAStep C1a C1a' := chain_step hchain hC1a hC1a'
  -- `C1a`'s `c1`-program is `drop c1.idx` (head `= arrive b nn`), so the advancing step is an
  -- `interleave`/`recycle` (target a `run`); `done`/`error` are ruled out (head is not `return`,
  -- and `error`/`done` would leave `c1`'s program unchanged/empty, not advanced).
  obtain ⟨s1n, T1n, rfl⟩ : ∃ s T, C1a' = Config.run s T := by
    have hc1ne : ((Config.run State.initial T).progOf c1.thread).drop c1.idx ≠ [] := by
      intro h; have hl := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at hl
      simp only [WeftCommon.Config.progOf] at hc1L; omega
    cases hC1astep with
    | @interleave _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @recycle _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @done sa Ta hdone hnofull =>
      exfalso
      have hc1prog : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop c1.idx := hC1aprog
      have hc1ids : c1.thread ∈ Ta.ids := by
        by_contra hni; rw [Ta.nil_outside_ids c1.thread hni] at hc1prog
        exact hc1ne hc1prog.symm
      exact hc1ne (hc1prog ▸ hdone c1.thread hc1ids)
    | @error sa Ta i P' _ hth =>
      exfalso
      have h1 : Ta.prog c1.thread = ((Config.run State.initial T).progOf c1.thread).drop c1.idx :=
        hC1aprog
      have h2 : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop (c1.idx + 1) := hC1a'prog
      rw [h1] at h2; have hl := congrArg List.length h2
      simp only [List.length_drop] at hl
      simp only [WeftCommon.Config.progOf] at hc1L; omega
  -- **Search for the firing config**: the first config (after the cut) whose successor either
  -- joins a `synced` list, *or* is `c1`'s arrive at `n1`.  `c1`'s arrive witnesses it (`p+d=n1`).
  have hPex : ∃ d, ∃ s T, τ'[p + d]? = some (Config.run s T) ∧
      ((∃ b' t', t' ∈ (s.B b').synced) ∨ p + d = n1) :=
    ⟨n1 - p, s1n, T1n,
      by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget, Or.inr (by omega)⟩
  set d₀ := Nat.find hPex with hd₀
  have hd₀spec := Nat.find_spec hPex
  rw [← hd₀] at hd₀spec
  obtain ⟨sq', Tq', hCq', hdisj⟩ := hd₀spec
  -- `d₀ > 0` since synced lists are empty at the cut and `p ≠ n1`
  have hd₀pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · exfalso
      rw [h, Nat.add_zero, hcut, Option.some.injEq, Config.run.injEq] at hCq'
      obtain ⟨rfl, rfl⟩ := hCq'
      rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
      · exact hsempty b' t' hjoin
      · omega
    · exact h
  -- at the firing config `q-1 = p + (d₀-1)`, synced lists are empty and `p + (d₀-1) ≠ n1`
  have hq1 : ¬ (∃ s T, τ'[p + (d₀ - 1)]? = some (Config.run s T) ∧
      ((∃ b' t', t' ∈ (s.B b').synced) ∨ p + (d₀ - 1) = n1)) := Nat.find_min hPex (by omega)
  -- the firing happens at or before `c1`'s arrive: `q = p + d₀ ≤ n1`
  have hqn1 : p + d₀ ≤ n1 := by
    have hle : d₀ ≤ n1 - p := hd₀ ▸ Nat.find_le (n := n1 - p)
      ⟨s1n, T1n, by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget, Or.inr (by omega)⟩
    omega
  have hqlen : p + d₀ < τ'.length := (List.getElem?_eq_some_iff.mp hCq').1
  have hget : ∀ j, j ≤ p + d₀ → ∃ C, τ'[j]? = some C :=
    fun j hj => ⟨_, List.getElem?_eq_getElem (show j < τ'.length by omega)⟩
  -- shared chain invariants
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have hwfAll : ∀ C ∈ τ', C.WF := WF_chain hchain hC₀head WF_initial
  have hei0 : ∀ s, (Config.state? (Config.run State.initial T)) = some s → s.EnabledInv := by
    intro s hs
    simp only [Config.state?, Option.some.injEq] at hs; subst hs; exact State.EnabledInv.initial
  have heiAll : ∀ C ∈ τ', ∀ s, C.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hC₀head hei0
  -- `c2`'s static facts
  have hc1L_c2 : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
  have hcmd2_get : (T.prog c2.thread)[c2.idx]'hc1L_c2 = Cmd.sync b mm := by
    have h := hcmd2; simp only [CTA.cmdAt] at h
    rw [List.getElem?_eq_getElem hc1L_c2, Option.some.injEq] at h; exact h
  have hdrop2 : (T.prog c2.thread).drop c2.idx
      = Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [List.drop_eq_getElem_cons hc1L_c2, hcmd2_get]
  -- **Program invariance**: while synced stays empty (configs `p … q-1`), `c2` cannot
  -- step (a `sync` step would join a synced list), so it stays poised at its head.
  have hinv : ∀ e, e ≤ d₀ - 1 → ∃ s' T', τ'[p + e]? = some (Config.run s' T') ∧
      T'.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    intro e
    induction e with
    | zero => intro _; exact ⟨s_G, T_G, by simpa using hcut, hc2head⟩
    | succ e ih =>
      intro he
      obtain ⟨s', T', hCe, hprog⟩ := ih (by omega)
      obtain ⟨C'', hCe1⟩ := hget (p + (e + 1)) (by omega)
      have hstep : CTAStep (Config.run s' T') C'' :=
        chain_step hchain (show τ'[p + e]? = some _ from hCe) (show τ'[(p + e) + 1]? = _ from hCe1)
      obtain ⟨Cnext, hCnext⟩ := hget (p + (e + 1) + 1) (by omega)
      obtain ⟨s'', T'', rfl⟩ : ∃ s T, C'' = Config.run s T := by
        cases chain_step hchain (show τ'[p + (e + 1)]? = _ from hCe1)
          (show τ'[p + (e + 1) + 1]? = _ from hCnext) <;> exact ⟨_, _, rfl⟩
      refine ⟨s'', T'', hCe1, ?_⟩
      have hsemp_e1 : ∀ bb tt, tt ∉ (s''.B bb).synced := fun bb tt htt =>
        Nat.find_min hPex (show e + 1 < d₀ by omega) ⟨s'', T'', hCe1, Or.inl ⟨bb, tt, htt⟩⟩
      have hsemp_e : ∀ bb tt, tt ∉ (s'.B bb).synced := fun bb tt htt =>
        Nat.find_min hPex (show e < d₀ by omega) ⟨s', T', hCe, Or.inl ⟨bb, tt, htt⟩⟩
      cases hstep with
      | @interleave _ _ _ i P' hi hbar hth =>
        by_cases hic2 : i = c2.thread
        · exfalso
          subst hic2
          rw [hprog, hdrop2] at hth
          cases hth with
          | sync_configure he hb => exact hsemp_e1 b c2.thread (by simp [Function.update_self])
          | sync_block he hb _ _ => exact hsemp_e1 b c2.thread (by simp [Function.update_self])
        · simp only [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hic2)]; exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e bb x (by rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
  -- **Firing config** `q-1`: `c2` poised at head, enabled, with `hbar` holding.
  have hmem : ∀ {j C}, τ'[j]? = some C → C ∈ τ' := fun hj => List.mem_of_getElem? hj
  obtain ⟨sm, Tm, hCq1, hprogm⟩ := hinv (d₀ - 1) (le_refl _)
  have hsemp_q1 : ∀ bb tt, tt ∉ (sm.B bb).synced := fun bb tt htt =>
    hq1 ⟨sm, Tm, hCq1, Or.inl ⟨bb, tt, htt⟩⟩
  have hheadm : Tm.prog c2.thread = Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [hprogm, hdrop2]
  have hc2ids : c2.thread ∈ Tm.ids := by
    by_contra hni
    rw [Tm.nil_outside_ids c2.thread hni] at hheadm
    exact (List.cons_ne_nil _ _) hheadm.symm
  have hc2en : sm.E c2.thread = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    obtain ⟨bb, hbb⟩ := heiAll _ (hmem hCq1) sm rfl c2.thread hne
    exact hsemp_q1 bb c2.thread hbb
  have hCq'' : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run sq' Tq') := by
    rw [show (p + (d₀ - 1)) + 1 = p + d₀ from by omega]; exact hCq'
  have hstepq : CTAStep (Config.run sm Tm) (Config.run sq' Tq') := chain_step hchain hCq1 hCq''
  -- `hbar` holds at the firing config: the step `q-1 → q` is an `interleave` — it either joins a
  -- synced list (left disjunct) or *is* `c1`'s arrive (right disjunct, `p + d₀ = n1`).
  have hbarq : ∀ b'', sm.B b'' = BarrierState.unconfigured ∨
      ∃ I A n, sm.B b'' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
    rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
    · -- a thread joins a synced list at the step `q-1 → q`: it is an `interleave`
      exact hbar_of_joins_synced hstepq rfl rfl (hsemp_q1 b' t') hjoin
    · -- `p + d₀ = n1`: the step `q-1 → q` is `c1`'s arrive (an `interleave`); a `recycle` here
      -- would wake nobody (synced empty ⟹ `I = []`), leaving `c1`'s program unchanged, yet `c1`
      -- advances one step — contradiction.
      cases hstepq with
      | @interleave _ _ _ i P' hi hbar hth => exact hbar
      | @recycle _ _ bb I A n hb hfull hpark =>
        exfalso
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_q1 bb x (by rw [hb]; simp)) (by simp)
        subst hI
        have hj1 : j1 = p + (d₀ - 1) := by omega
        -- `c1`'s program at `n1-1` is `drop c1.idx` (config there is `run sm Tm`)
        have e1 : C1a = Config.run sm Tm := by
          rw [hj1, hCq1] at hC1a; exact (Option.some.injEq _ _).mp hC1a.symm
        rw [e1] at hC1aprog; simp only [WeftCommon.Config.progOf] at hC1aprog
        -- the config at `n1` (`= run s1n T1n`) is the recycle target, so `T1n = Tm.wake []`;
        -- a recycle wakes nobody (`I = []`), leaving `c1`'s program unchanged — but it advanced.
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]; exact hC1a'
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [Config.run.injEq] at h; exact h.2.symm
        simp only [WeftCommon.Config.progOf] at hC1a'prog
        rw [hTeq] at hC1a'prog
        simp only [WeftCommon.CTA.wake, List.not_mem_nil, if_false] at hC1a'prog
        rw [hC1aprog] at hC1a'prog
        have hl := congrArg List.length hC1a'prog
        simp only [List.length_drop] at hl
        simp only [WeftCommon.Config.progOf] at hc1L; omega
  have hwfq : (Config.WF (Config.run sm Tm)) := hwfAll _ (hmem hCq1)
  -- reachability of the firing config (for `barriersWithin`)
  have hreach : ∀ j, j ≤ p + d₀ → ∀ C, τ'[j]? = some C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C := by
    intro j
    induction j with
    | zero =>
      intro _ C hC
      rw [← List.head?_eq_getElem?, hC₀head, Option.some.injEq] at hC
      subst hC; exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj C hC
      obtain ⟨Cj, hCj⟩ := hget j (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega) Cj hCj) (chain_step hchain hCj hC)
  have hreachq1 : Relation.ReflTransGen CTAStep (Config.run State.initial T) (Config.run sm Tm) :=
    hreach (p + (d₀ - 1)) (by omega) _ hCq1
  -- shared prefix facts: `pre = τ'.take (p+d₀)` ends at the firing config `q-1`
  have hprelen : (τ'.take (p + d₀)).length = p + d₀ := by rw [List.length_take]; omega
  have hpne : τ'.take (p + d₀) ≠ [] := by
    intro h; rw [h, List.length_nil] at hprelen; omega
  have hprechain : List.IsChain CTAStep (τ'.take (p + d₀)) := hchain.take _
  have hpre_get : ∀ i, i < p + d₀ → (τ'.take (p + d₀))[i]? = τ'[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hprehead : (τ'.take (p + d₀)).head? = some (Config.run State.initial T) := by
    rw [List.head?_eq_getElem?, hpre_get 0 (by omega), ← List.head?_eq_getElem?]; exact hC₀head
  have hprelast : (τ'.take (p + d₀)).getLast? = some (Config.run sm Tm) := by
    rw [List.getLast?_eq_getElem?, hprelen, hpre_get (p + d₀ - 1) (by omega),
      show p + d₀ - 1 = p + (d₀ - 1) from by omega]
    exact hCq1
  -- gluing: a complete trace from any successor of the firing config extends `pre`
  have glue : ∀ (σ : List Config) (Cstart : Config), IsCompleteTraceFrom Cstart σ →
      CTAStep (Config.run sm Tm) Cstart →
      IsCompleteTraceFrom (Config.run State.initial T) (τ'.take (p + d₀) ++ σ) := by
    intro σ Cstart hσ hcon
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.IsChain.append hprechain hσ.1.subtrace ?_
      intro x hx y hy
      rw [hprelast, Option.mem_some_iff] at hx; subst hx
      rw [hσ.2, Option.mem_some_iff] at hy; subst hy
      exact hcon
    · obtain ⟨Cn, hCnlast, hterm⟩ := hσ.1.ends
      exact ⟨Cn, List.mem_getLast?_append_of_mem_getLast? hCnlast, hterm⟩
    · rw [List.head?_append_of_ne_nil _ hpne]; exact hprehead
  -- **Fire `c2` early.** From the firing config it either joins `synced b` or errors.
  have hc2step : (∃ sN, CTAStep (Config.run sm Tm)
        (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) ∧
        c2.thread ∈ (sN.B b).synced) ∨ CTAStep (Config.run sm Tm) (Config.err Tm) := by
    rcases hbarq b with hbu | ⟨I, A, n', hbcfg, hltn⟩
    · have hcta := CTAStep.interleave hc2ids hbarq
        (by rw [hheadm]; exact ThreadStep.sync_configure hc2en hbu)
      exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
    · have hI : I = [] := by
        rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
        · exact h
        · exact absurd (hsemp_q1 b x (by rw [hbcfg]; simp)) (by simp)
      subst hI
      have hApos : 0 < A := by simpa using (hwfq.1 b [] A n' hbcfg).2.2
      by_cases hmm : n' = mm
      · rw [hmm] at hbcfg hltn
        have hcta := CTAStep.interleave hc2ids hbarq
          (by rw [hheadm];
              exact ThreadStep.sync_block hc2en hbcfg (by simpa using hApos) (by simpa using hltn))
        exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
      · exact Or.inr (CTAStep.error hbarq
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmm))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced b`: complete the trace, then read off a generation clash
    have hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b := by rw [hcmd1]; rfl
    have hc2bar : (T.cmdAt c2).bind Cmd.barrier? = some b := by rw [hcmd2]; rfl
    have hbne : sN.B b ≠ BarrierState.unconfigured := by
      intro hcon; rw [hcon] at hsync; simp [BarrierState.unconfigured] at hsync
    have hbwN : (Config.barriersWithin T.barrierSet (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1))))) :=
      inv_preserved T.barrierSet hcstep (barriersWithin_of_reaches hreachq1)
    obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
    set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
    have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' := glue σ _ hσ hcstep
    obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
    obtain ⟨m2, hm2⟩ := exists_time_of_ends_done htrace hdone'' (η := c2) hc1L_c2
    have hCpark : τ''[p + d₀]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
        ← List.head?_eq_getElem?]
      exact hσ.2
    have hprogpark : (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1))).prog c2.thread
        = ((Config.run State.initial T).progOf c2.thread).drop c2.idx := by
      change (Function.update Tm.prog c2.thread _) c2.thread = _
      rw [Function.update_self]; exact hdrop2.symm
    have hBI'' : ∀ C ∈ τ'', ∀ s, C.state? = some s → s.BlockInv := by
      refine blockInv_chain htrace.1.subtrace htrace.2 ?_
      intro s hs; simp only [Config.state?, Option.some.injEq] at hs; subst hs
      exact State.BlockInv.initial
    have hpn : p + d₀ < m2 := by
      refine lt_time_of_lt_progOf hm2 hCpark ?_
      rw [show (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))).progOf c2.thread
          = ((Config.run State.initial T).progOf c2.thread).drop c2.idx from hprogpark,
        List.length_drop]
      have hX : c2.idx < ((Config.run State.initial T).progOf c2.thread).length := hc1L_c2
      omega
    have heq3 : recycleCount b τ'' (m2 - 1) = recycleCount b τ'' (p + d₀) :=
      parked_sync_recycleCount hBI'' rfl hm2 hCpark hsync hprogpark hpn
    have hshare : ∀ j, j < p + d₀ → τ''[j]? = τ'[j]? := by
      intro j hj
      rw [hτ''def, List.getElem?_append_left (by rw [hprelen]; exact hj)]
      exact hpre_get j hj
    have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
      rw [hshare (p + (d₀ - 1)) (by omega)]; exact hCq1
    have hCpark'' : τ''[p + (d₀ - 1) + 1]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]; exact hCpark
    have hstepfalse : stepRecyclesBarrier b (Config.run sm Tm) (Config.run sN
        (Tm.set c2.thread hc2ids (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))) =
        false := by
      simp [stepRecyclesBarrier, Config.state?, hbne]
    have heq4 : recycleCount b τ'' (p + d₀) = recycleCount b τ' (p + (d₀ - 1)) := by
      have hsucc : recycleCount b τ'' (p + d₀) = recycleCount b τ'' (p + (d₀ - 1)) := by
        rw [show p + d₀ = (p + (d₀ - 1)) + 1 from by omega]
        exact recycleCount_succ_of_not_recycle b hCq1'' hCpark'' hstepfalse
      rw [hsucc]
      exact recycleCount_prefix_eq b (p + (d₀ - 1)) (fun j hj => hshare j (by omega))
    obtain ⟨sτ, hdoneτ⟩ := hτ.2
    obtain ⟨m1τ, hm1τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c1) hc1L
    obtain ⟨m2τ, hm2τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c2) hc1L_c2
    have gen_in : ∀ (σ' : List Config) (η : ProgPoint) (bb : Barrier),
        IsCompleteTraceFrom (Config.run State.initial T) σ' →
        (T.cmdAt η).bind Cmd.barrier? = some bb →
        (∃ mτ, IsTimeOf (Config.run State.initial T) τ η mτ) →
        IsGenOf (Config.run State.initial T) σ' η (some (pointGen T τ η)) := by
      intro σ' η bb hσ' hbar hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (some (pointGen T τ η)) :=
        isGenOf_pointGen hbar hmτ
      obtain ⟨g, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η ⟨bb, hbar⟩
      rwa [IsGenOf.unique hgτ hgenτ] at hgσ
    have hgenc1 : pointGen T τ c1 = recycleCount b τ' (n1 - 1) + 1 :=
      isGenOf_recycleCount (gen_in τ' c1 b hcomp hc1bar ⟨m1τ, hm1τ⟩) hc1bar hn1
    have hgenc2 : pointGen T τ c2 = recycleCount b τ'' (m2 - 1) + 1 :=
      isGenOf_recycleCount (gen_in τ'' c2 b htrace hc2bar ⟨m2τ, hm2τ⟩) hc2bar hm2
    have hmono : recycleCount b τ' (p + (d₀ - 1)) ≤ recycleCount b τ' (n1 - 1) :=
      recycleCount_mono b τ' (show p + (d₀ - 1) ≤ n1 - 1 from by omega)
    omega
  · exfalso
    have herrtrace : IsCompleteTraceFrom (Config.err Tm) [Config.err Tm] :=
      ⟨⟨List.isChain_singleton _, Config.err Tm, by simp, Or.inr (Or.inl ⟨Tm, rfl⟩)⟩, by simp⟩
    obtain ⟨sd2, hdone2⟩ :=
      CTA.WellSynchronized.completeTrace_ends_done hws (glue _ _ herrtrace herr)
    have hgl : (τ'.take (p + d₀) ++ [Config.err Tm]).getLast? = some (Config.err Tm) := by simp
    rw [hgl] at hdone2; simp at hdone2

/-- A thread parked in barrier `b`'s synced list stays parked across any single step that is
*not* a recycle of `b`. Every `interleave` step only ever *grows* synced lists (`sync_block`
prepends, the configuring/arriving rules touch other fields), and a `recycle` of a *different*
barrier leaves `b`'s synced list untouched; a recycle of `b` itself is exactly
`stepRecyclesBarrier b = true`, which is excluded by hypothesis. -/
theorem synced_mem_preserved {C C' : Config} (hstep : CTAStep C C') (b : Barrier)
    (t : ThreadId) :
    ∀ s s' T T', C = Config.run s T → C' = Config.run s' T' →
      stepRecyclesBarrier b C C' = false → t ∈ (s.B b).synced → t ∈ (s'.B b).synced := by
  cases hstep with
  | @interleave s₀ sn T₀ i P' hi hbar hts =>
    intro s s' T T' hC hC' _ hmem
    injection hC with hs0 _; subst hs0
    obtain ⟨Pi, hPi⟩ : ∃ P, T₀.prog i = P := ⟨_, rfl⟩
    rw [hPi] at hts
    revert hC'
    cases hts with
    | read_noop => intro hC'; injection hC' with h _; subst h; exact hmem
    | write_noop => intro hC'; injection hC' with h _; subst h; exact hmem
    | @arrive_configure _ _ ba _ _ _ hb =>
      intro hC'; injection hC' with h _; subst h
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hmem; simp [BarrierState.unconfigured] at hmem
      · simpa only [Function.update_of_ne hbb] using hmem
    | @arrive_register _ _ ba _ _ I _ _ hb _ _ =>
      intro hC'; injection hC' with h _; subst h
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hmem; simpa [Function.update_self] using hmem
      · simpa only [Function.update_of_ne hbb] using hmem
    | @sync_configure _ _ ba _ _ _ hb =>
      intro hC'; injection hC' with h _; subst h
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hmem; simp [BarrierState.unconfigured] at hmem
      · simpa only [Function.update_of_ne hbb] using hmem
    | @sync_block _ _ ba _ _ I _ _ hb _ _ =>
      intro hC'; injection hC' with h _; subst h
      by_cases hbb : b = ba
      · subst hbb; rw [hb] at hmem; simp only [Function.update_self]
        exact List.mem_cons_of_mem _ hmem
      · simpa only [Function.update_of_ne hbb] using hmem
  | @recycle s₀ T₀ ba I A n hb hfull _ =>
    intro s s' T T' hC hC' hnorec hmem
    injection hC with hs0 _; subst hs0
    injection hC' with hsn _; subst hsn
    by_cases hbb : b = ba
    · subst hbb
      simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self] at hnorec
    · simpa only [Function.update_of_ne hbb] using hmem
  | done hdone hnofull => intro _ _ _ _ _ hC' _ _; simp at hC'
  | error hts => intro _ _ _ _ _ hC' _ _; simp at hC'

/-- A step that *recycles* barrier `b` wakes every thread parked in `b`'s synced list: such a
thread's program advances past its parked `sync` (its head is dropped). An `interleave` step
can never recycle a barrier (its guard keeps every barrier strictly under-full), and a
`recycle` of a *different* barrier fails `stepRecyclesBarrier b`, so the recycling step is
necessarily a `recycle` of `b`, which wakes exactly `b`'s synced list. -/
theorem recycle_wakes_synced {C C' : Config} (hstep : CTAStep C C') (b : Barrier)
    (t : ThreadId) :
    ∀ s s' T T', C = Config.run s T → C' = Config.run s' T' →
      stepRecyclesBarrier b C C' = true → t ∈ (s.B b).synced →
      T'.prog t = (T.prog t).tail := by
  cases hstep with
  | @interleave s₀ sn T₀ i P' hi hbar hts =>
    intro _ _ _ _ _ _ hrec _
    exfalso
    have hnf : (s₀.B b).isFull = false := by
      rcases hbar b with h | ⟨I, A, n, hbn, hlt⟩
      · rw [h]; simp [BarrierState.isFull, BarrierState.unconfigured]
      · rw [hbn]; simp only [BarrierState.isFull]
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp [stepRecyclesBarrier, Config.state?, hnf] at hrec
  | @recycle s₀ T₀ ba I A n hb hfull hpark =>
    intro s s' T T' hC hC' hrec hmem
    injection hC with hs0 hT0; subst hs0; subst hT0
    injection hC' with _ hTw; subst hTw
    by_cases hbb : ba = b
    · subst hbb
      have htI : t ∈ I := by rw [hb] at hmem; exact hmem
      simp [WeftCommon.CTA.wake, htI]
    · exfalso
      have hne : s₀.B b ≠ BarrierState.unconfigured := by
        intro h; rw [h] at hmem; simp [BarrierState.unconfigured] at hmem
      simp [stepRecyclesBarrier, Config.state?, Function.update_of_ne (Ne.symm hbb), hne] at hrec
  | done hdone hnofull => intro _ _ _ _ _ hC' _ _; simp at hC'
  | error hts => intro _ _ _ _ _ hC' _ _; simp at hC'

/-- A single CTA step between two `run` configurations advances each thread's program by
*at most one* command (`d ≤ 1`): `interleave` runs one thread for one (`d ≤ 1`) thread step,
and `recycle` drops the parked `sync` head of each woken thread (`d = 1`) or leaves others
unchanged (`d = 0`). (The `done` step, with its `d = |prog|`, only fires once programs are
empty — excluded here since the target is a `run`.) -/
theorem CTAStep.progOf_drop_run {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    ∀ s s' T T', C = Config.run s T → C' = Config.run s' T' →
      ∃ d, d ≤ 1 ∧ T'.prog t = (T.prog t).drop d := by
  cases hstep with
  | @interleave s₀ sn T₀ i P' hi hbar hts =>
    intro _ _ _ _ hC hC'
    injection hC with _ hT0; injection hC' with _ hT'; subst hT0; subst hT'
    by_cases h : t = i
    · subst h; obtain ⟨d, hd1, hd⟩ := hts.run_drop_le_one
      exact ⟨d, hd1, by simp [WeftCommon.CTA.set, Function.update_self, hd]⟩
    · exact ⟨0, by omega, by simp [WeftCommon.CTA.set, Function.update_of_ne h]⟩
  | @recycle s₀ T₀ ba I A n hb hfull hpark =>
    intro _ _ _ _ hC hC'
    injection hC with _ hT0; injection hC' with _ hT'; subst hT0; subst hT'
    by_cases h : t ∈ I
    · exact ⟨1, le_refl 1, by simp [WeftCommon.CTA.wake, if_pos h, List.drop_one]⟩
    · exact ⟨0, by omega, by simp [WeftCommon.CTA.wake, if_neg h]⟩
  | done hdone hnofull => intro _ _ _ _ _ hC'; simp at hC'
  | error hts => intro _ _ _ _ _ hC'; simp at hC'

/-- **A first-instruction `sync` lands in its barrier's first generation.** If, in a complete
trace `τ` from `(I, T)`, thread `t`'s very first instruction is `sync b m` and `t` registers
into `b`'s synced list at the first step (`hC1`/`hsync1`/`hprog1`), and that `sync` executes
at time `m'`, then no recycle of `b` happens strictly before `m'`: `recycleCount b τ (m'-1) = 0`.

`t` stays parked in `b`'s synced list from step `1` until its wake at `m'`
(`synced_mem_preserved`, its program frozen at `sync b m :: tail` via `progOf_drop_run` +
`sync_drop_recycles`); any *earlier* recycle of `b` would wake `t` (`recycle_wakes_synced`),
making its `sync` execute before `m'` — impossible by `IsTimeOf.unique`. -/
theorem firstSync_recycleCount_zero {T : CTA} {τ : List Config} {t : ThreadId} {b : Barrier}
    {m : ℕ+} {tail : Prog} {m' : Nat} {s1 : State} {T1 : CTA}
    (hcomp : IsCompleteTraceFrom (Config.run State.initial T) τ)
    (hprogT : T.prog t = Cmd.sync b m :: tail)
    (hC1 : τ[1]? = some (Config.run s1 T1))
    (hsync1 : t ∈ (s1.B b).synced) (hprog1 : T1.prog t = T.prog t)
    (hm' : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ m') :
    recycleCount b τ (m' - 1) = 0 := by
  have hchain := hcomp.1.subtrace
  have hhead : τ[0]? = some (Config.run State.initial T) := by
    have h0 : τ[0]? = τ.head? := by cases τ <;> rfl
    rw [h0]; exact hcomp.2
  have hm'len : m' < τ.length := by
    obtain ⟨_, _, _, _, _C', _, _, hCj1, _, _⟩ := hm'
    have := (List.getElem?_eq_some_iff.mp hCj1).1; omega
  have hrun : ∀ j, j < m' → ∃ s T2, τ[j]? = some (Config.run s T2) := by
    intro j hj
    obtain ⟨Cj, hCj⟩ : ∃ C, τ[j]? = some C :=
      ⟨_, List.getElem?_eq_getElem (show j < τ.length by omega)⟩
    obtain ⟨Cj1, hCj1⟩ : ∃ C, τ[j+1]? = some C :=
      ⟨_, List.getElem?_eq_getElem (show j+1 < τ.length by omega)⟩
    obtain ⟨s, T2, heq⟩ := CTAStep.source_run (chain_step hchain hCj hCj1)
    exact ⟨s, T2, by rw [hCj, heq]⟩
  have P : ∀ j, 1 ≤ j → j ≤ m' - 1 → ∃ sj Tj, τ[j]? = some (Config.run sj Tj) ∧
      t ∈ (sj.B b).synced ∧ Tj.prog t = T.prog t := by
    intro j
    induction j with
    | zero => intro h _; omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; exact ⟨s1, T1, hC1, hsync1, hprog1⟩
      · obtain ⟨sk, Tk, hCk, hsk, hpk⟩ := ih hkpos (by omega)
        obtain ⟨sk1, Tk1, hCk1⟩ := hrun (k+1) (by omega)
        have hst : CTAStep (Config.run sk Tk) (Config.run sk1 Tk1) := chain_step hchain hCk hCk1
        have hnorec : stepRecyclesBarrier b (Config.run sk Tk) (Config.run sk1 Tk1) = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have hwake := recycle_wakes_synced hst b t sk sk1 Tk Tk1 rfl rfl hc hsk
          have htime : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ (k+1) := by
            refine ⟨hcomp, ?_, k, _, _, rfl, hCk, hCk1, ?_, ?_⟩
            · change 0 < (T.prog t).length; rw [hprogT]; simp
            · change Tk.prog t = (T.prog t).drop 0; rw [List.drop_zero]; exact hpk
            · change Tk1.prog t = (T.prog t).drop 1; rw [hwake, hpk, hprogT]; rfl
          have := IsTimeOf.unique htime hm'; omega
        refine ⟨sk1, Tk1, hCk1,
          synced_mem_preserved hst b t sk sk1 Tk Tk1 rfl rfl hnorec hsk, ?_⟩
        obtain ⟨d, hd1, hd⟩ := hst.progOf_drop_run t sk sk1 Tk Tk1 rfl rfl
        obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
        · rw [hd, List.drop_zero]; exact hpk
        · exfalso
          have hrec := sync_drop_recycles hst
            (show (Config.run sk Tk).progOf t = Cmd.sync b m :: tail by
              change Tk.prog t = _; rw [hpk, hprogT])
            (show (Config.run sk1 Tk1).progOf t = tail by
              change Tk1.prog t = _; rw [hd, hpk, hprogT]; rfl)
          rw [hrec] at hnorec; exact absurd hnorec (by simp)
  rw [recycleCount, List.countP_eq_zero]
  intro j hjmem
  rw [List.mem_range] at hjmem
  rw [Bool.not_eq_true]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [hhead, hC1]
    simp [stepRecyclesBarrier, Config.state?, State.initial, BarrierState.isFull,
      BarrierState.unconfigured]
  · obtain ⟨sj, Tj, hCj, hsj, hpj⟩ := P j hjpos (by omega)
    obtain ⟨sj1, Tj1, hCj1⟩ := hrun (j+1) (by omega)
    rw [hCj, hCj1]
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hst : CTAStep (Config.run sj Tj) (Config.run sj1 Tj1) := chain_step hchain hCj hCj1
    have hwake := recycle_wakes_synced hst b t sj sj1 Tj Tj1 rfl rfl hc hsj
    have htime : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ (j+1) := by
      refine ⟨hcomp, ?_, j, _, _, rfl, hCj, hCj1, ?_, ?_⟩
      · change 0 < (T.prog t).length; rw [hprogT]; simp
      · change Tj.prog t = (T.prog t).drop 0; rw [List.drop_zero]; exact hpj
      · change Tj1.prog t = (T.prog t).drop 1; rw [hwake, hpj, hprogT]; rfl
    have := IsTimeOf.unique htime hm'; omega

/-- Complete a trace after a chosen first step. Given a single CTA step from `(I, T)` to
`C₁ = (s₁, T₁)`, there is a complete trace `(I, T) :: τr` from `(I, T)` whose *second*
configuration is `C₁` (`exists_completeTrace` finishes the run from `C₁`). -/
theorem exists_firstStep_complete {T : CTA} {s1 : State} {T1 : CTA}
    (hstep01 : CTAStep (Config.run State.initial T) (Config.run s1 T1)) :
    ∃ τr, IsCompleteTraceFrom (Config.run State.initial T) (Config.run State.initial T :: τr) ∧
      (Config.run State.initial T :: τr)[1]? = some (Config.run s1 T1) := by
  obtain ⟨τr, hτr⟩ := exists_completeTrace T.barrierSet (Config.run s1 T1)
    (barriersWithin_of_reaches (Relation.ReflTransGen.single hstep01))
  have hτrne : τr ≠ [] := by
    intro h; rw [h] at hτr; obtain ⟨_, hl, _⟩ := hτr.1.ends; simp at hl
  refine ⟨τr, ⟨⟨?_, ?_⟩, by simp⟩, ?_⟩
  · change List.IsChain CTAStep (Config.run State.initial T :: τr)
    rw [List.isChain_cons]
    exact ⟨fun y hy => by rw [hτr.2, Option.mem_some_iff] at hy; subst hy; exact hstep01,
      hτr.1.subtrace⟩
  · obtain ⟨Cn, hlast, hterm⟩ := hτr.1.ends
    exact ⟨Cn, by rw [List.getLast?_cons_of_ne_nil hτrne]; exact hlast, hterm⟩
  · have h1 : (Config.run State.initial T :: τr)[1]? = τr[0]? := rfl
    have h0 : τr[0]? = τr.head? := by cases τr <;> rfl
    rw [h1, h0]; exact hτr.2

/-- The shared `hws`-contradiction tail of the predecessor-less case. If `c2` is a barrier op
on `b` whose witness generation is `≥ 2` (`hge2`), but some complete trace `τ''` from `(I, T)`
assigns `c2` generation `1` — formally, every time `m'` of `c2` in `τ''` sees no prior recycle
of `b` (`recycleCount b τ'' (m'-1) = 0`) — then the two traces disagree on `c2`'s generation,
contradicting `hws`. -/
theorem firstInstr_contradiction {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints) {b : Barrier}
    (hbar2 : (T.cmdAt c2).bind Cmd.barrier? = some b)
    (hge2 : 2 ≤ pointGen T τ c2) {τ'' : List Config}
    (hcomp'' : IsCompleteTraceFrom (Config.run State.initial T) τ'')
    (hrc : ∀ m', IsTimeOf (Config.run State.initial T) τ'' c2 m' →
      recycleCount b τ'' (m' - 1) = 0) : False := by
  obtain ⟨sd, hdone⟩ := hτ.2
  have hc2L : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
  obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hc2L
  obtain ⟨g, hgτ, hgτ''⟩ := hws.2 τ τ'' hτ.1 hcomp'' c2 ⟨b, hbar2⟩
  have hgeq : g = pointGen T τ c2 :=
    Option.some.inj (IsGenOf.unique hgτ (isGenOf_pointGen hbar2 hmτ))
  rw [hgeq] at hgτ''
  obtain ⟨_, b', hb'cmd, hcase⟩ := hgτ''
  rcases hcase with ⟨mm, hmm, hgenrec⟩ | ⟨h0eq, _⟩
  · have hbb' : b' = b := by
      have hh : (T.cmdAt c2).bind Cmd.barrier? = some b' := hb'cmd
      rw [hbar2] at hh; exact (Option.some.inj hh).symm
    subst hbb'
    have hgenrec' := Option.some.inj hgenrec
    rw [hrc mm hmm] at hgenrec'; omega
  · exact nomatch h0eq

/-- **`2 ≤ pointGen` core of the predecessor-less case.** A barrier op `c2` that is its
thread's first instruction (`c2.idx = 0`) but is assigned generation `≥ 2` by the witness
trace cannot belong to a well-synchronized CTA: a schedule that steps `c2`'s thread first
registers `c2` into generation `1`. The `arrive` case runs `c2` immediately (generation `1`,
no recycle precedes step `1`); the `sync` case parks `c2` in `b`'s first round
(`firstSync_recycleCount_zero`). Both route through `firstInstr_contradiction`. -/
theorem firstInstr_highGen_not_wellSynchronized' {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints) {b : Barrier}
    (hbar2 : (T.cmdAt c2).bind Cmd.barrier? = some b)
    (hge2 : 2 ≤ pointGen T τ c2) (hidx0 : c2.idx = 0) : False := by
  have hi : c2.thread ∈ T.ids := ((mem_progPoints_iff T c2).mp hc2).1
  have hc2eq : c2 = ⟨c2.thread, 0⟩ := by rw [← hidx0]
  cases hcmd2 : T.cmdAt c2 with
  | none => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
  | some cmd2 =>
    cases cmd2 with
    | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | arrive bb m =>
      have hbe : b = bb := by
        have h := hbar2; rw [hcmd2] at h; simp [Cmd.barrier?] at h; exact h.symm
      subst hbe
      have hhead0 : (T.prog c2.thread)[0]? = some (Cmd.arrive b m) := by
        have h := hcmd2; simp only [CTA.cmdAt, hidx0] at h; exact h
      obtain ⟨tl, hprogT⟩ : ∃ tl, T.prog c2.thread = Cmd.arrive b m :: tl := by
        have hne : T.prog c2.thread ≠ [] := by intro h; rw [h] at hhead0; simp at hhead0
        obtain ⟨hd, tl, hp⟩ := List.exists_cons_of_ne_nil hne
        rw [hp] at hhead0; simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead0
        exact ⟨tl, by rw [hp, hhead0]⟩
      set s1 : State :=
        { State.initial with B := Function.update State.initial.B b ⟨[], 1, some m⟩ } with hs1def
      set T1 : CTA := T.set c2.thread hi tl with hT1def
      have hts : ThreadStep (ThreadConfig.run State.initial c2.thread (T.prog c2.thread))
          (ThreadConfig.run s1 c2.thread tl) := by
        rw [hprogT]; exact ThreadStep.arrive_configure rfl rfl
      have hstep01 : CTAStep (Config.run State.initial T) (Config.run s1 T1) :=
        CTAStep.interleave hi (fun _ => Or.inl rfl) hts
      obtain ⟨τr, hcomp'', hC1''⟩ := exists_firstStep_complete hstep01
      have htime1 : IsTimeOf (Config.run State.initial T)
          (Config.run State.initial T :: τr) ⟨c2.thread, 0⟩ 1 := by
        refine ⟨hcomp'', ?_, 0, _, _, rfl, rfl, hC1'', ?_, ?_⟩
        · change 0 < (T.prog c2.thread).length; rw [hprogT]; simp
        · change T.prog c2.thread = (T.prog c2.thread).drop 0; rw [List.drop_zero]
        · change T1.prog c2.thread = (T.prog c2.thread).drop 1
          rw [hT1def, hprogT]; simp [WeftCommon.CTA.set, Function.update_self]
      refine firstInstr_contradiction hτ hws hc2 hbar2 hge2 hcomp'' ?_
      intro m' hm'; rw [hc2eq] at hm'
      rw [IsTimeOf.unique hm' htime1]; simp [recycleCount]
    | sync bb m =>
      have hbe : b = bb := by
        have h := hbar2; rw [hcmd2] at h; simp [Cmd.barrier?] at h; exact h.symm
      subst hbe
      have hhead0 : (T.prog c2.thread)[0]? = some (Cmd.sync b m) := by
        have h := hcmd2; simp only [CTA.cmdAt, hidx0] at h; exact h
      obtain ⟨tl, hprogT⟩ : ∃ tl, T.prog c2.thread = Cmd.sync b m :: tl := by
        have hne : T.prog c2.thread ≠ [] := by intro h; rw [h] at hhead0; simp at hhead0
        obtain ⟨hd, tl, hp⟩ := List.exists_cons_of_ne_nil hne
        rw [hp] at hhead0; simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead0
        exact ⟨tl, by rw [hp, hhead0]⟩
      set s1 : State :=
        { E := Function.update State.initial.E c2.thread false,
          B := Function.update State.initial.B b ⟨[c2.thread], 0, some m⟩ } with hs1def
      set T1 : CTA := T.set c2.thread hi (T.prog c2.thread) with hT1def
      have hts : ThreadStep (ThreadConfig.run State.initial c2.thread (T.prog c2.thread))
          (ThreadConfig.run s1 c2.thread (T.prog c2.thread)) := by
        rw [hprogT]; exact ThreadStep.sync_configure rfl rfl
      have hstep01 : CTAStep (Config.run State.initial T) (Config.run s1 T1) :=
        CTAStep.interleave hi (fun _ => Or.inl rfl) hts
      obtain ⟨τr, hcomp'', hC1''⟩ := exists_firstStep_complete hstep01
      have hsync1 : c2.thread ∈ (s1.B b).synced := by rw [hs1def]; simp [Function.update_self]
      have hprog1 : T1.prog c2.thread = T.prog c2.thread := by
        rw [hT1def]; simp [WeftCommon.CTA.set]
      refine firstInstr_contradiction hτ hws hc2 hbar2 hge2 hcomp'' ?_
      intro m' hm'; rw [hc2eq] at hm'
      exact firstSync_recycleCount_zero hcomp'' hprogT hC1'' hsync1 hprog1 hm'

/-- **Completeness, the predecessor-less (`c2.idx = 0`) case.** A barrier operation `c2`
that is the *first instruction of its thread* (`c2.idx = 0`) yet is assigned generation
`≥ 2` by the witness trace `τ` — here `pointGen T τ c2 = pointGen T τ c1 + 1` for a barrier
op `c1`, whose generation is `≥ 1` on the `done`-reaching `τ` — cannot belong to a
well-synchronized CTA: `c2` has no in-thread predecessor to anchor it after generation `k`,
so a schedule that steps `c2`'s thread first registers `c2` into an *earlier* generation
(generation `1`), making `c2`'s generation schedule-dependent. This is the formal version of
the 4-thread counterexample (`arrive 0 2 ‖ arrive 0 2 ‖ sync 0 2 ‖ sync 0 2`) that motivates
the `c2.idx = 0 ⇒ reject` clause of Step 3 in `CheckWellSynchronized`.

TODO (rohany): construct the reordered complete trace `τ''` in which `c2`'s thread steps
first and read off `pointGen T τ'' c2 = 1 ≠ pointGen T τ c2`, contradicting `hws`. -/
theorem firstInstr_highGen_not_wellSynchronized {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b : Barrier}
    (hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b)
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hbar2 : (T.cmdAt c2).bind Cmd.barrier? = some b)
    (hgen : pointGen T τ c2 = pointGen T τ c1 + 1) (hidx0 : c2.idx = 0) : False := by
  cases hcmd2 : T.cmdAt c2 with
  | none => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
  | some cmd2 =>
    cases cmd2 with
    | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | arrive bb m =>
      -- `c2` is an `arrive` at index `0`: the *only* `initRelation` edge into an `arrive`
      -- is program order from its predecessor (`initRelation_cases`), which an index-`0`
      -- point has none of — so nothing happens-before `c2`, and the generic
      -- reversing-trace argument (`reverse_barrier_contradiction`) applies.
      have hnothb : ¬ happensBefore T τ c1 c2 := by
        intro h
        rcases Relation.ReflTransGen.cases_tail h with heq | ⟨d, _, hdc2⟩
        · rw [heq] at hgen; omega
        · obtain ⟨_, _, hcase⟩ := initRelation_cases hdc2
          rcases hcase with hpo | ⟨bb', n', hsync, _, _⟩
          · have hii : c2.idx = d.idx + 1 := by rw [hpo]
            omega
          · rw [hcmd2] at hsync; simp at hsync
      exact reverse_barrier_contradiction hτ hws hc1 hc2 hc1bar hbar2 hgen hnothb
    | sync bb m =>
      -- `c2` is a `sync` at index `0`: it *can* carry same-generation incoming edges, so
      -- `¬ happensBefore` is not free. Instead build a complete trace `τ''` whose first step
      -- runs `c2`'s thread (`sync_configure b`), registering `c2` into `b`'s first round;
      -- then `c2` has generation `1` (or never executes), contradicting `hws`, which forces
      -- generation `pointGen T τ c2 = pointGen T τ c1 + 1 ≥ 2`.
      have hbb : b = bb := by
        have h := hbar2; rw [hcmd2] at h; simp [Cmd.barrier?] at h; exact h.symm
      subst hbb
      have hi : c2.thread ∈ T.ids := ((mem_progPoints_iff T c2).mp hc2).1
      have hc2eq : c2 = ⟨c2.thread, 0⟩ := by rw [← hidx0]
      have hhead0 : (T.prog c2.thread)[0]? = some (Cmd.sync b m) := by
        have h := hcmd2; simp only [CTA.cmdAt, hidx0] at h; exact h
      obtain ⟨tl, hprogT⟩ : ∃ tl, T.prog c2.thread = Cmd.sync b m :: tl := by
        have hne : T.prog c2.thread ≠ [] := by
          intro h; rw [h] at hhead0; simp at hhead0
        obtain ⟨hd, tl, hp⟩ := List.exists_cons_of_ne_nil hne
        rw [hp] at hhead0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead0
        exact ⟨tl, by rw [hp, hhead0]⟩
      -- first step: `sync_configure` of thread `c2.thread`, then complete the trace
      set s1 : State :=
        { E := Function.update State.initial.E c2.thread false,
          B := Function.update State.initial.B b ⟨[c2.thread], 0, some m⟩ } with hs1def
      set T1 : CTA := T.set c2.thread hi (T.prog c2.thread) with hT1def
      have hts : ThreadStep (ThreadConfig.run State.initial c2.thread (T.prog c2.thread))
          (ThreadConfig.run s1 c2.thread (T.prog c2.thread)) := by
        rw [hprogT]; exact ThreadStep.sync_configure rfl rfl
      have hstep01 : CTAStep (Config.run State.initial T) (Config.run s1 T1) :=
        CTAStep.interleave hi (fun _ => Or.inl rfl) hts
      have hinv1 : (Config.barriersWithin T.barrierSet (Config.run s1 T1)) :=
        barriersWithin_of_reaches (Relation.ReflTransGen.single hstep01)
      obtain ⟨τr, hτr⟩ := exists_completeTrace T.barrierSet (Config.run s1 T1) hinv1
      have hτrne : τr ≠ [] := by
        intro h; rw [h] at hτr; obtain ⟨_, hl, _⟩ := hτr.1.ends; simp at hl
      have hcomp'' : IsCompleteTraceFrom (Config.run State.initial T)
          (Config.run State.initial T :: τr) := by
        refine ⟨⟨?_, ?_⟩, by simp⟩
        · change List.IsChain CTAStep (Config.run State.initial T :: τr)
          rw [List.isChain_cons]
          refine ⟨fun y hy => ?_, hτr.1.subtrace⟩
          rw [hτr.2, Option.mem_some_iff] at hy; subst hy; exact hstep01
        · obtain ⟨Cn, hlast, hterm⟩ := hτr.1.ends
          exact ⟨Cn, by rw [List.getLast?_cons_of_ne_nil hτrne]; exact hlast, hterm⟩
      have hC1'' : (Config.run State.initial T :: τr)[1]? = some (Config.run s1 T1) := by
        have h1 : (Config.run State.initial T :: τr)[1]? = τr[0]? := rfl
        have h0 : τr[0]? = τr.head? := by cases τr <;> rfl
        rw [h1, h0]; exact hτr.2
      have hsync1 : c2.thread ∈ (s1.B b).synced := by
        rw [hs1def]; simp [Function.update_self]
      have hprog1 : T1.prog c2.thread = T.prog c2.thread := by
        rw [hT1def]; simp [WeftCommon.CTA.set]
      -- read off generations from `hws`; the witness forces `pointGen T τ c2 ≥ 2`
      obtain ⟨sd, hdone⟩ := hτ.2
      have hc2L : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
      obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hc2L
      have hgenc2 : IsGenOf (Config.run State.initial T) τ c2 (some (pointGen T τ c2)) :=
        isGenOf_pointGen hbar2 hmτ
      have hc1L : c1.idx < (T.prog c1.thread).length := ((mem_progPoints_iff T c1).mp hc1).2
      obtain ⟨mτ1, hmτ1⟩ := exists_time_of_ends_done hτ.1 hdone hc1L
      have hpc1 : 1 ≤ pointGen T τ c1 := by
        have hh := isGenOf_recycleCount (isGenOf_pointGen hc1bar hmτ1) hc1bar hmτ1; omega
      have hge2 : 2 ≤ pointGen T τ c2 := by omega
      obtain ⟨g, hgτ, hgτ''⟩ :=
        hws.2 τ (Config.run State.initial T :: τr) hτ.1 hcomp'' c2 ⟨b, hbar2⟩
      have hgeq : g = pointGen T τ c2 := Option.some.inj (IsGenOf.unique hgτ hgenc2)
      rw [hgeq] at hgτ''
      obtain ⟨_, b', hb'cmd, hcase⟩ := hgτ''
      rcases hcase with ⟨mm, hmm, hgenrec⟩ | ⟨h0eq, _⟩
      · have hbb' : b' = b := by
          simp only [ProgPoint.cmd, WeftCommon.Config.progOf, hidx0] at hb'cmd
          rw [hprogT] at hb'cmd
          simp only [List.getElem?_cons_zero, Option.bind_some, Cmd.barrier?,
            Option.some.injEq] at hb'cmd
          exact hb'cmd.symm
        subst hbb'
        rw [hc2eq] at hmm
        have hrc0 := firstSync_recycleCount_zero hcomp'' hprogT hC1'' hsync1 hprog1 hmm
        have hgenrec' := Option.some.inj hgenrec
        rw [hrc0] at hgenrec'; omega
      · exact nomatch h0eq

/-- **Theorem 2 (completeness).** If `τ` is a complete trace from `(I, T)` ending in
`done` (`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns `false`,
then `T` is *not* well-synchronized.
NOTE (rohany): This is a top-level theorem.
-/
theorem not_wellSynchronized_of_check_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    ¬ T.WellSynchronized := by
  intro hws
  obtain ⟨c1, hc1, b, hc1bar, c2, hc2, hbar2, hgen, hfail⟩ :=
    exists_failing_pair hcheck
  -- The new `c2.idx = 0` failure mode is the predecessor-less counterexample; the remaining
  -- (`1 ≤ c2.idx`) case is the original happens-before reversal that follows.
  obtain ⟨hidx, hc1ne3, hnotmem⟩ :
      1 ≤ c2.idx ∧ c1 ≠ (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∧
        (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∉ (CheckWellSynchronized T τ).2 := by
    rcases hfail with h | hidx0
    · exact h
    · exact (firstInstr_highGen_not_wellSynchronized hτ hws hc1 hc1bar hc2 hbar2 hgen hidx0).elim
  -- the predecessor `c3` of `c2` is a valid program point
  have hc3 : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T c2).mp hc2
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- `c1 ≠ c3` is delivered by `exists_failing_pair` (the reflexive disjunct of the check):
  -- combined with `(c1, c3) ∉ R` it rules out `happensBefore c1 c3`.
  have hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ :=
    not_happensBefore_of_not_mem hc1ne3 hnotmem
  cases hcmd2 : T.cmdAt c2 with
  | none => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
  | some cmd2 =>
    cases cmd2 with
    | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
    | arrive bb m =>
      -- `c2` is an `arrive`: reverse `(c1, c2)` directly (its only in-edge is from `c3`)
      have hbbeq : bb = b := by rw [hcmd2] at hbar2; simpa [Cmd.barrier?] using hbar2
      subst hbbeq
      have hnothb2 : ¬ happensBefore T τ c1 c2 := by
        intro h
        rcases happensBefore_arrive hcmd2 hidx h with heq | h3
        · -- `c1 = c2` is impossible: `gen c2 = gen c1 + 1`
          rw [heq] at hgen; omega
        · exact hnothb3 h3
      exact reverse_barrier_contradiction hτ hws hc1 hc2 hc1bar hbar2 hgen hnothb2
    | sync bb m =>
      -- `c2` is a `sync`: if it is not forced after `c1`, reverse `(c1, c2)` directly;
      -- otherwise it competes with `c1` for `b`'s round (`competing_sync_false`).
      have hbbeq : bb = b := by rw [hcmd2] at hbar2; simpa [Cmd.barrier?] using hbar2
      subst hbbeq
      by_cases hhb : happensBefore T τ c1 c2
      · -- `c2` is forced after `c1`. Split on `c1`'s kind: a `sync` source is the original
        -- competing-sync reversal; an `arrive` source is its operational analog.
        cases hcmd1 : T.cmdAt c1 with
        | none => rw [hcmd1] at hc1bar; simp [Cmd.barrier?] at hc1bar
        | some cmd1 =>
          cases cmd1 with
          | read g => rw [hcmd1] at hc1bar; simp [Cmd.barrier?] at hc1bar
          | write g => rw [hcmd1] at hc1bar; simp [Cmd.barrier?] at hc1bar
          | sync b1 n1 =>
            have hbeq : b1 = bb := by rw [hcmd1] at hc1bar; simpa [Cmd.barrier?] using hc1bar
            subst hbeq
            exact competing_sync_false hτ hws hc1 hc2 hcmd1 hcmd2 hgen hidx hnothb3 hhb
          | arrive b1 n1 =>
            have hbeq : b1 = bb := by rw [hcmd1] at hc1bar; simpa [Cmd.barrier?] using hc1bar
            subst hbeq
            exact competing_arrive_sync_false hτ hws hc1 hc2 hcmd1 hcmd2 hgen hidx hnothb3 hhb
      · exact reverse_barrier_contradiction hτ hws hc1 hc2 hc1bar hbar2 hgen hhb

/-- **Correctness of `CheckWellSynchronized`** (Theorems 1 and 2 combined). For a CTA `T`
with a successful trace `τ`, the checker accepts iff `T` is well-synchronized. This
aggregates soundness (`wellSynchronized_of_check`, the `check = true → WS` direction) and
completeness (`not_wellSynchronized_of_check_false`, the `check = false → ¬WS` direction).

Implementation of the top-level `Weft.checkWellSynchronized_correct` (in `Weft.lean`). -/
theorem checkWellSynchronized_correct_impl {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) :
    (CheckWellSynchronized T τ).1 = true ↔ T.WellSynchronized := by
  refine ⟨wellSynchronized_of_check hτ, fun hws => ?_⟩
  by_contra hne
  rw [Bool.not_eq_true] at hne
  exact not_wellSynchronized_of_check_false hτ hne hws

/-- A configured-and-full barrier is incompatible with the `interleave` guard (which requires
every barrier under-full): the two cannot both hold of the same state. Used to discharge every
`recycle`/`interleave` cross-case — when a recycle can fire, no `interleave` (or `done`) can. -/
theorem interleaveGuard_full_absurd {S : State} {b : Barrier} {I : List ThreadId}
    {A : ℕ} {n : ℕ+} (hb : S.B b = ⟨I, A, some n⟩) (hfull : I.length + A = (n : ℕ))
    (hbar : ∀ b, S.B b = BarrierState.unconfigured ∨
      ∃ I A n, S.B b = ⟨I, A, some n⟩ ∧ I.length + A < (n : ℕ)) : False := by
  rcases hbar b with h | ⟨I', A', n', hb', hlt⟩
  · rw [hb] at h; exact absurd h (by simp [BarrierState.unconfigured])
  · rw [hb] at hb'
    simp only [BarrierState.mk.injEq, Option.some.injEq] at hb'
    obtain ⟨rfl, rfl, rfl⟩ := hb'
    omega


end Weft
