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
  | @error s₀ T i P' hth =>
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
      simp only [Config.progOf, CTA.wake, if_pos htI]
    · exfalso
      simp [stepRecyclesBarrier, Config.state?, Function.update_of_ne hbb,
        isFull_and_unconfigured_false] at hrec
  | @done s₀ T hdone hnofull =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?, isFull_and_unconfigured_false] at hrec
  | @error s₀ T i P' hth =>
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
      simp [Config.progOf, CTA.wake, hit] at hsmprog
  | @done _ _ hdone hnofull =>
    exfalso
    simp [stepRecyclesBarrier, Config.state?, isFull_and_unconfigured_false] at hrec
  | @error _ _ i P' hth =>
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
  | @error s₀ T i P' hth =>
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
  have hwf : (Config.run s T_C).WF := WF_of_reaches hreach
  -- a `G`-thread `i₀` still has commands below its cut (`¬ Gdone`)
  simp only [Gdone, not_forall] at hnotdone
  obtain ⟨i₀, hi₀ids, hi₀ne⟩ := hnotdone
  obtain ⟨e₀, he₀le, he₀prog⟩ := hbound i₀
  have hi₀G : e₀ < fcut T τ η₁ i₀ := by
    simp only [Config.progOf] at hi₀ne
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
        simp only [CTA.wake, hjI, if_true]
        rw [heprog, List.tail_drop]
      · exact ⟨e, hele, by simp only [CTA.wake, hjI, if_false]; exact heprog⟩
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
        simpa only [CTA.wake, hjnotI, if_false] using hpj
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
          · subst hji; exact ⟨e + 1, by omega, by simp [CTA.set, Function.update_self]⟩
          · obtain ⟨ej, hjle, hjprog⟩ := hbound j
            exact ⟨ej, hjle, by
              simp only [CTA.set, Function.update_of_ne hji]; exact hjprog⟩
        · intro b'' j hj
          rw [hsyn] at hj
          have hjnoti : j ≠ i := by
            intro hji; subst hji
            exact absurd hen (by rw [hwf.2.2.2.1 b'' j hj]; simp)
          have hpj := hpurity b'' j hj
          simp only [CTA.set, Function.update_of_ne hjnoti]; exact hpj
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
          · exact absurd ⟨_, CTAStep.error
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
          · subst hj; simp only [CTA.set, Function.update_self]; rw [hhead, hcmd]
          · simp only [CTA.set, Function.update_of_ne hj]
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
          · exact absurd ⟨_, CTAStep.error
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
      have hbwC : (Config.run s T_C).barriersWithin T.barrierSet := barriersWithin_of_reaches hreach
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
        obtain ⟨g, _, hg1, hg2⟩ := hws.2 τ tr hτ.1 htrIC c ⟨bb, hcbar⟩
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
        | @error s₀ T i P' hth => exact absurd hCs' (by simp [Config.state?])
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
              simp only [CTA.set, Function.update_self]
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
              rw [← hedprog]; simp only [CTA.set, Function.update_self]; exact hpi.symm
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
          simp only [Config.progOf] at hd
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
            simp only [Config.progOf] at hd
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
    reach_cut_aux hτ hws ((Config.run State.initial T).cfgMeasure T.barrierSet)
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
  have hgenc1 : IsGenOf (Config.run State.initial T) τ c1 (pointGen T τ c1) :=
    isGenOf_pointGen hc1bar hm1
  have hgenca : IsGenOf (Config.run State.initial T) τ ca (pointGen T τ ca) :=
    isGenOf_pointGen hcabar hm2
  obtain ⟨g1, _, hg1τ, hg1τ'⟩ := hws.2 τ τ' hτ.1 hτ'c c1 ⟨b, hc1bar⟩
  obtain ⟨g2, _, hg2τ, hg2τ'⟩ := hws.2 τ τ' hτ.1 hτ'c ca ⟨b, hcabar⟩
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

/-! ## The determined prefix `P` (machinery for Theorem 1)

The soundness direction `wellSynchronized_of_check` cannot call Lemma 1
(`soundAndPrecise_happensBefore`), which assumes the very `WellSynchronized` it must
*conclude*. The way around the circularity is to feed the soundness argument its own
determinacy as it goes: an edge of `initRelation` is sound as soon as its endpoints are
known to be *determined* (every complete trace assigns them the same generation as the
reference trace `τ`), with no global well-synchronization — see `initRelation_edge_sound`,
which only ever uses `hws` pointwise at an edge's two endpoints.

`Determined` is the pointwise notion; `determinedPrefix` (the object `P`) collects the
points whose entire `happensBefore`-past is determined. Membership is phrased as "every
ancestor is determined" precisely so that *path-containment* is definitional
(`determinedPrefix_ancestors_determined`): a soundness induction along any `initRelation`
path into a point of `P` sees only determined nodes. `P` is, equivalently, the largest
`happensBefore`-down-closed set of determined points
(`determinedPrefix_subset_determined`, `determinedPrefix_downClosed`,
`determinedPrefix_greatest`). -/

/-- A program point `η` is **determined** by the reference trace `τ` when every complete
trace from `(I, T)` agrees with `τ` about it: `η` executes, and — when `η` is a barrier op
— at the very same generation `pointGen T τ η`.

For a barrier op the generation clause is the content (and since the checker's `τ` ends in
`done`, `pointGen T τ η ≠ 0`, so it already forces "executes"); for a memory op the
generation clause is vacuous (`0 = 0`) and the executing clause carries the content.
Keeping both clauses makes `Determined` uniform over *all* program points, which the
soundness chain needs because program-order edges run through memory ops. -/
def Determined (T : CTA) (τ : List Config) (η : ProgPoint) : Prop :=
  ∀ σ, IsCompleteTraceFrom (Config.run State.initial T) σ →
    (∃ n, IsTimeOf (Config.run State.initial T) σ η n) ∧
      pointGen T σ η = pointGen T τ η

/-- The **determined prefix** `P` (relative to `τ`): the program points all of whose
`happensBefore`-ancestors are determined. Equivalently, the largest
`happensBefore`-down-closed set of determined points. -/
def determinedPrefix (T : CTA) (τ : List Config) : Set ProgPoint :=
  { η | η ∈ T.progPoints ∧ ∀ a, happensBefore T τ a η → Determined T τ a }

/-- Every point of `P` is itself determined (`a = η`, via `ReflTransGen.refl`). -/
theorem determinedPrefix_subset_determined {T : CTA} {τ : List Config} {η : ProgPoint}
    (h : η ∈ determinedPrefix T τ) : Determined T τ η :=
  h.2 η Relation.ReflTransGen.refl

/-- **Path-containment, definitionally.** Every `happensBefore`-ancestor of a point of `P`
is determined — the fact the bounded soundness chain consumes along a path. -/
theorem determinedPrefix_ancestors_determined {T : CTA} {τ : List Config} {a c : ProgPoint}
    (hc : c ∈ determinedPrefix T τ) (hac : happensBefore T τ a c) : Determined T τ a :=
  hc.2 a hac

/-- `P` is down-closed under `initRelation` predecessors: if `b ∈ P` and `a → b` is an
edge, then `a ∈ P`. -/
theorem determinedPrefix_downClosed {T : CTA} {τ : List Config} {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) (hb : b ∈ determinedPrefix T τ) :
    a ∈ determinedPrefix T τ := by
  refine ⟨(initRelation_cases hedge).1, ?_⟩
  intro x hxa
  exact hb.2 x (Relation.ReflTransGen.trans hxa (Relation.ReflTransGen.single hedge))

/-- `P` is the **greatest** `happensBefore`-down-closed set of determined program points:
any such `Q` is contained in `P`. -/
theorem determinedPrefix_greatest {T : CTA} {τ : List Config} (Q : Set ProgPoint)
    (hQpp : ∀ η ∈ Q, η ∈ T.progPoints)
    (hQdet : ∀ η ∈ Q, Determined T τ η)
    (hQdc : ∀ a b, (a, b) ∈ initRelation T τ → b ∈ Q → a ∈ Q) :
    Q ⊆ determinedPrefix T τ := by
  intro η hη
  refine ⟨hQpp η hη, ?_⟩
  intro a haη
  apply hQdet a
  -- `Q`, closed under single-step predecessors, is closed under `happensBefore`-predecessors.
  have key : ∀ x, happensBefore T τ a x → x ∈ Q → a ∈ Q := by
    intro x hax
    induction hax with
    | refl => exact fun h => h
    | @tail b c _hab hbc ih => exact fun hcQ => ih (hQdc b c hbc hcQ)
  exact key η haη hη

/-! ## Theorem 1 — soundness of `CheckWellSynchronized`

The paper's **Theorem 1**: a successful run of the check witnesses
well-synchronization. The paper proves it by induction on the suffixes of the
`done`-reaching execution — *not* via Lemma 1, which would be circular (only
well-synchronized configurations are known to have a sound `R`, yet here `R` is what
we use to conclude well-synchronization). Stated here as a stub. -/

/-- **Theorem 1.** If `τ` is a complete trace from `(I, T)` ending in `done`
(`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns `true`, then `T`
is well-synchronized.

Note (rohany): This is a top-level theorem.
-/
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
    simp only [Config.progOf]
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
  have hei0 : ∀ s, (Config.run State.initial T).state? = some s → s.EnabledInv := by
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
        · simp only [CTA.set, Function.update_of_ne (Ne.symm hic2)]; exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e bb x (by rw [hb]; simp)) (by simp)
        subst hI
        simpa [CTA.wake] using hprog
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
  have hwfq : (Config.run sm Tm).WF := hwfAll _ (hmem hCq1)
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
      · exact Or.inr (CTAStep.error
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmm))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced b`: complete the trace, then read off a generation clash
    have hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b := by rw [hcmd1]; rfl
    have hc2bar : (T.cmdAt c2).bind Cmd.barrier? = some b := by rw [hcmd2]; rfl
    have hbne : sN.B b ≠ BarrierState.unconfigured := by
      intro hcon; rw [hcon] at hsync; simp [BarrierState.unconfigured] at hsync
    have hbwN : (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))).barriersWithin T.barrierSet :=
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
        IsGenOf (Config.run State.initial T) σ' η (pointGen T τ η) := by
      intro σ' η bb hσ' hbar hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
        isGenOf_pointGen hbar hmτ
      obtain ⟨g, _, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η ⟨bb, hbar⟩
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
    simp only [Config.progOf]
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
      simp only [Config.progOf] at hc1L; omega
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
    | @error sa Ta i P' hth =>
      exfalso
      have h1 : Ta.prog c1.thread = ((Config.run State.initial T).progOf c1.thread).drop c1.idx :=
        hC1aprog
      have h2 : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop (c1.idx + 1) := hC1a'prog
      rw [h1] at h2; have hl := congrArg List.length h2
      simp only [List.length_drop] at hl
      simp only [Config.progOf] at hc1L; omega
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
  have hei0 : ∀ s, (Config.run State.initial T).state? = some s → s.EnabledInv := by
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
        · simp only [CTA.set, Function.update_of_ne (Ne.symm hic2)]; exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e bb x (by rw [hb]; simp)) (by simp)
        subst hI
        simpa [CTA.wake] using hprog
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
        rw [e1] at hC1aprog; simp only [Config.progOf] at hC1aprog
        -- the config at `n1` (`= run s1n T1n`) is the recycle target, so `T1n = Tm.wake []`;
        -- a recycle wakes nobody (`I = []`), leaving `c1`'s program unchanged — but it advanced.
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]; exact hC1a'
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [Config.run.injEq] at h; exact h.2.symm
        simp only [Config.progOf] at hC1a'prog
        rw [hTeq] at hC1a'prog
        simp only [CTA.wake, List.not_mem_nil, if_false] at hC1a'prog
        rw [hC1aprog] at hC1a'prog
        have hl := congrArg List.length hC1a'prog
        simp only [List.length_drop] at hl
        simp only [Config.progOf] at hc1L; omega
  have hwfq : (Config.run sm Tm).WF := hwfAll _ (hmem hCq1)
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
      · exact Or.inr (CTAStep.error
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmm))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced b`: complete the trace, then read off a generation clash
    have hc1bar : (T.cmdAt c1).bind Cmd.barrier? = some b := by rw [hcmd1]; rfl
    have hc2bar : (T.cmdAt c2).bind Cmd.barrier? = some b := by rw [hcmd2]; rfl
    have hbne : sN.B b ≠ BarrierState.unconfigured := by
      intro hcon; rw [hcon] at hsync; simp [BarrierState.unconfigured] at hsync
    have hbwN : (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync b mm :: (T.prog c2.thread).drop (c2.idx + 1)))).barriersWithin T.barrierSet :=
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
        IsGenOf (Config.run State.initial T) σ' η (pointGen T τ η) := by
      intro σ' η bb hσ' hbar hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
        isGenOf_pointGen hbar hmτ
      obtain ⟨g, _, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η ⟨bb, hbar⟩
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
      simp [CTA.wake, htI]
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
      exact ⟨d, hd1, by simp [CTA.set, Function.update_self, hd]⟩
    · exact ⟨0, by omega, by simp [CTA.set, Function.update_of_ne h]⟩
  | @recycle s₀ T₀ ba I A n hb hfull hpark =>
    intro _ _ _ _ hC hC'
    injection hC with _ hT0; injection hC' with _ hT'; subst hT0; subst hT'
    by_cases h : t ∈ I
    · exact ⟨1, le_refl 1, by simp [CTA.wake, if_pos h, List.drop_one]⟩
    · exact ⟨0, by omega, by simp [CTA.wake, if_neg h]⟩
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
  obtain ⟨g, _, hgτ, hgτ''⟩ := hws.2 τ τ'' hτ.1 hcomp'' c2 ⟨b, hbar2⟩
  have hgeq : g = pointGen T τ c2 := IsGenOf.unique hgτ (isGenOf_pointGen hbar2 hmτ)
  rw [hgeq] at hgτ''
  obtain ⟨_, b', hb'cmd, hcase⟩ := hgτ''
  rcases hcase with ⟨mm, hmm, hgenrec⟩ | ⟨h0eq, _⟩
  · have hbb' : b' = b := by
      have hh : (T.cmdAt c2).bind Cmd.barrier? = some b' := hb'cmd
      rw [hbar2] at hh; exact (Option.some.inj hh).symm
    subst hbb'
    rw [hrc mm hmm] at hgenrec; omega
  · rw [h0eq] at hge2; omega

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
          rw [hT1def, hprogT]; simp [CTA.set, Function.update_self]
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
        rw [hT1def]; simp [CTA.set]
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
      have hinv1 : (Config.run s1 T1).barriersWithin T.barrierSet :=
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
        rw [hT1def]; simp [CTA.set]
      -- read off generations from `hws`; the witness forces `pointGen T τ c2 ≥ 2`
      obtain ⟨sd, hdone⟩ := hτ.2
      have hc2L : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
      obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hc2L
      have hgenc2 : IsGenOf (Config.run State.initial T) τ c2 (pointGen T τ c2) :=
        isGenOf_pointGen hbar2 hmτ
      have hc1L : c1.idx < (T.prog c1.thread).length := ((mem_progPoints_iff T c1).mp hc1).2
      obtain ⟨mτ1, hmτ1⟩ := exists_time_of_ends_done hτ.1 hdone hc1L
      have hpc1 : 1 ≤ pointGen T τ c1 := by
        have hh := isGenOf_recycleCount (isGenOf_pointGen hc1bar hmτ1) hc1bar hmτ1; omega
      have hge2 : 2 ≤ pointGen T τ c2 := by omega
      obtain ⟨g, _, hgτ, hgτ''⟩ :=
        hws.2 τ (Config.run State.initial T :: τr) hτ.1 hcomp'' c2 ⟨b, hbar2⟩
      have hgeq : g = pointGen T τ c2 := IsGenOf.unique hgτ hgenc2
      rw [hgeq] at hgτ''
      obtain ⟨_, b', hb'cmd, hcase⟩ := hgτ''
      rcases hcase with ⟨mm, hmm, hgenrec⟩ | ⟨h0eq, _⟩
      · have hbb' : b' = b := by
          simp only [ProgPoint.cmd, Config.progOf, hidx0] at hb'cmd
          rw [hprogT] at hb'cmd
          simp only [List.getElem?_cons_zero, Option.bind_some, Cmd.barrier?,
            Option.some.injEq] at hb'cmd
          exact hb'cmd.symm
        subst hbb'
        rw [hc2eq] at hmm
        have hrc0 := firstSync_recycleCount_zero hcomp'' hprogT hC1'' hsync1 hprog1 hmm
        rw [hrc0] at hgenrec; omega
      · rw [h0eq] at hge2; omega

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

/-- *(Stated, not yet proved.)* **Local confluence with generation agreement for a
well-synchronized continuation.** From a configuration `(S, T)`, suppose:

* `σ₁` is a step `(S, T) → C'` (`hσ₁`), the continuation `C'` is well-synchronized
  (`hWS`) and has a successful trace `τ` (`hτ`);
* a second first step `σ₂`, namely `(S, T) → C''` (`hσ₂`) — *not* required to differ
  from `σ₁` (so `C''` may equal `C'`).

Then the two divergences reconverge — there are CTA-step *paths* `C' ⤳* Cd` and
`C'' ⤳* Cd` into a common configuration `Cd`, given as config lists `C' :: p'` and
`C'' :: p''` (each an `IsSubtrace` ending at `Cd`) — and the recovered generations agree:
for every complete trace `τ'` from `Cd` and every barrier instruction `η` of `(S, T)`, the
two reconverged traces — route through `C'` then follow `τ'`, vs. route through `C''` then
follow `τ'` — assign `η` a *common, nonzero* generation. The `(C' :: p').dropLast ++ τ'`
splice drops the shared `Cd` (contributed by `τ'`) so the glued list is a genuine trace.
The conclusion is phrased with `IsGenOf` in the shape of the `Config.WellSynchronized` body
(`∃ g, g ≠ 0 ∧ IsGenOf … ∧ IsGenOf …`), so it is a drop-in when discharging
well-synchronization of `(S, T)`.

Multi-step legs (vs. a one-step `σ₃ : C' → Cd`) are forced: when `σ₁` *completes* a barrier
(e.g. `arrive b n` with `n = 1`, or any `arrive`/`sync` that fills its barrier), the
post-`σ₁` state has a full barrier, so the `interleave` guard blocks every replay of `σ₂`
and no single-step `Cd` exists; the join then routes through a `recycle` leg. A single step
is the special case `p' = [Cd]` (then `(C' :: p').dropLast ++ τ' = C' :: τ'`), and `p' = []`
the degenerate `C' = Cd` leg.

(`σ₂` need not differ from `σ₁`: if `C'' = C'` the two reconverged traces coincide and the
claim is immediate. A natural witness for the common generation `g` is `pointGen T … η`,
related to `IsGenOf` by `isGenOf_pointGen`.)

Rohan notes: This is a (multi-step) diamond / local-confluence property that may be useful
for proving the soundness of the well-sync algorithm.
-/
theorem soundness_lemma_diamond
    {S : State} {T : CTA} {C' C'' : Config}
    (hσ₁ : CTAStep (Config.run S T) C')
    {τ : List Config} (hτ : IsSuccessfulTraceFrom C' τ)
    (hWS : C'.WellSynchronized)
    -- TODO (rohany): Can we get rid of this premise?
    -- (hcheck : (CheckWellSynchronized T (Config.run S T :: τ)).1 = true)
    (hσ₂ : CTAStep (Config.run S T) C'') :
    ∃ (Cd : Config) (p' p'' : List Config),
      IsSubtrace (C' :: p') ∧ (C' :: p').getLast? = some Cd ∧
      IsSubtrace (C'' :: p'') ∧ (C'' :: p'').getLast? = some Cd ∧
      ∀ τ', IsCompleteTraceFrom Cd τ' →
        ∀ η : ProgPoint, (∃ b, (η.cmd (Config.run S T)).bind Cmd.barrier? = some b) →
          ∃ g, g ≠ 0 ∧
            IsGenOf (Config.run S T)
              (Config.run S T :: (C' :: p').dropLast ++ τ') η g ∧
            IsGenOf (Config.run S T)
              (Config.run S T :: (C'' :: p'').dropLast ++ τ') η g := by
  -- Case on both first steps. A `CTAStep` is `interleave` (a thread takes a `ThreadStep`),
  -- `recycle`, `done`, or `error`; on `interleave` we further case the `ThreadStep` rule
  -- (only the six non-error rules produce a `run` target, after generalizing the
  -- stepping thread's opaque program `T.prog i`). State-preserving no-op steps
  -- (`read`/`write`) commute with everything and change no generation, so they are
  -- discharged uniformly without a sub-split. `done`/`error` of σ₁ are impossible
  -- (`C'` is well-synchronized, hence `run`); `done` of σ₂ is impossible too.
  --
  -- σ₂-error note: σ₂ = `error` (`C''` an `err` config) is left open. It *should*
  -- contradict `hWS`: an erroring competing step from `(S, T)` would let the sibling
  -- `C'` reach `err`/deadlock too, which a WS config forbids
  -- (`Config.WellSynchronized.completeTrace_ends_done`). The missing piece is that the
  -- error/deadlock *persists to `C'`* across σ₁'s step (plus `C'.WF`) — not available yet.
  cases hσ₁ with
  | @interleave _ _ _ i₁ P'₁ hi₁ _ hstep₁ =>
    generalize hP₁ : T.prog i₁ = P₁ at hstep₁
    cases hstep₁ with
    | read_noop | write_noop =>
      -- σ₁ is a state-preserving no-op (`read`/`write`): `C' = run S (T.set i₁ _ P'₁)`,
      -- thread `i₁` advanced past its non-barrier head, state `(E, B)` untouched. Case σ₂.
      -- For σ₂ ∈ {interleave, recycle} reconverge at `Cd` = "σ₂ applied to `C'`": σ₃ replays
      -- σ₂ from `C'` (legal — same state `S`, σ₂'s thread/barrier untouched by the no-op),
      -- σ₄ replays the no-op from `C''` (legal — reads/writes have no premises). The two
      -- conclusion traces then differ only at index 1; since the no-op recycles nothing and
      -- never executes a barrier (`η.idx ≥ 1` on `i₁`), the generations agree, and `WS(C')`
      -- (`Cd` is a descendant of `C'`) makes them nonzero.
      cases hσ₂ with
      | @interleave _ _ _ i₂ _ _hi₂ _hbar₂ _hstep₂ =>
        -- commute (σ₃ = σ₂ from `C'`, σ₄ = no-op from `C''`) then generation agreement
        sorry
      | @recycle _ _ b₂ I₂ A₂ n₂ hb₂ hfull₂ _ =>
        -- σ₂ = recycle needs barrier `b₂` *full*, but σ₁ = interleave's guard requires every
        -- barrier under-full — impossible.
        exact (interleaveGuard_full_absurd hb₂ hfull₂ (by assumption)).elim
      | done hdone _ =>
        -- σ₂ = done: `T.IsDone` ⇒ `T.prog i₁ = []`, contradicting σ₁'s read/write head.
        simp [hdone i₁ hi₁] at hP₁
      | @error _ _ i₂ P'₂ hstep₂ =>
        -- σ₂ = error: σ₁ is state-preserving and leaves thread `i₂` untouched, so the
        -- erroring step replays verbatim from `C'`, giving `C' ⤳ err`. That complete trace
        -- from `C'` ends in `err`, contradicting `hWS` (no WS config has an unexecuted sync:
        -- `err_has_unexec_sync` + `wellSync_no_unexec_sync`).
        exfalso
        have hne : i₂ ≠ i₁ := by rintro rfl; rw [hP₁] at hstep₂; cases hstep₂
        have hprog : (T.set i₁ hi₁ P'₁).prog i₂ = T.prog i₂ := by
          change Function.update T.prog i₁ P'₁ i₂ = T.prog i₂
          exact Function.update_of_ne hne P'₁ T.prog
        have hC'err : CTAStep (Config.run S (T.set i₁ hi₁ P'₁))
            (Config.err (T.set i₁ hi₁ P'₁)) := by
          refine CTAStep.error (i := i₂) (P' := P'₂) ?_
          rw [hprog]; exact hstep₂
        have hcomplete : IsCompleteTraceFrom (Config.run S (T.set i₁ hi₁ P'₁))
            [Config.run S (T.set i₁ hi₁ P'₁), Config.err (T.set i₁ hi₁ P'₁)] :=
          ⟨⟨List.isChain_pair.mpr hC'err, Config.err (T.set i₁ hi₁ P'₁), by simp,
            Or.inr (Or.inl ⟨T.set i₁ hi₁ P'₁, rfl⟩)⟩, by simp⟩
        obtain ⟨η, hηbar, hηno⟩ :=
          err_has_unexec_sync hcomplete ⟨S, T.set i₁ hi₁ P'₁, rfl⟩ rfl
        exact wellSync_no_unexec_sync hWS hcomplete hηbar hηno
    | arrive_configure _ _ =>
      cases hσ₂ with
      | @interleave _ _ _ i₂ _ _ _ hstep₂ =>
        generalize _hP₂ : T.prog i₂ = P₂ at hstep₂
        cases hstep₂ with
        | read_noop | write_noop =>
          -- σ₁ arrive/configure, σ₂ read/write no-op (state-preserving; trivial, symmetric)
          sorry
        | arrive_configure _ _ =>
          -- σ₁ arrive/configure, σ₂ arrive/configure
          sorry
        | arrive_register _ _ _ _ =>
          -- σ₁ arrive/configure, σ₂ arrive/register
          sorry
        | sync_configure _ _ =>
          -- σ₁ arrive/configure, σ₂ sync/configure
          sorry
        | sync_block _ _ _ _ =>
          -- σ₁ arrive/configure, σ₂ sync/block
          sorry
      | @recycle _ _ b₂ I₂ A₂ n₂ hb₂ hfull₂ _ =>
        -- σ₂ = recycle needs a full barrier, contradicting σ₁ = interleave's guard.
        exact (interleaveGuard_full_absurd hb₂ hfull₂ (by assumption)).elim
      | done hdone _ =>
        -- σ₁ arrive/configure, σ₂ done: `T.IsDone` forces `T.prog i₁ = []`, but σ₁ stepped `i₁`
        simp [hdone i₁ hi₁] at hP₁
      | error _ =>
        -- σ₁ arrive/configure, σ₂ error: open — should contradict `hWS` (see σ₂-error note above).
        sorry
    | arrive_register _ _ _ _ =>
      cases hσ₂ with
      | @interleave _ _ _ i₂ _ _ _ hstep₂ =>
        generalize _hP₂ : T.prog i₂ = P₂ at hstep₂
        cases hstep₂ with
        | read_noop | write_noop =>
          -- σ₁ arrive/register, σ₂ read/write no-op (state-preserving; trivial, symmetric)
          sorry
        | arrive_configure _ _ =>
          -- σ₁ arrive/register, σ₂ arrive/configure
          sorry
        | arrive_register _ _ _ _ =>
          -- σ₁ arrive/register, σ₂ arrive/register
          sorry
        | sync_configure _ _ =>
          -- σ₁ arrive/register, σ₂ sync/configure
          sorry
        | sync_block _ _ _ _ =>
          -- σ₁ arrive/register, σ₂ sync/block
          sorry
      | @recycle _ _ b₂ I₂ A₂ n₂ hb₂ hfull₂ _ =>
        -- σ₂ = recycle needs a full barrier, contradicting σ₁ = interleave's guard.
        exact (interleaveGuard_full_absurd hb₂ hfull₂ (by assumption)).elim
      | done hdone _ =>
        -- σ₁ arrive/register, σ₂ done: `T.IsDone` forces `T.prog i₁ = []`, but σ₁ stepped `i₁`
        simp [hdone i₁ hi₁] at hP₁
      | error _ =>
        -- σ₁ arrive/register, σ₂ error: open — should contradict `hWS` (see σ₂-error note above).
        sorry
    | sync_configure _ _ =>
      cases hσ₂ with
      | @interleave _ _ _ i₂ _ _ _ hstep₂ =>
        generalize _hP₂ : T.prog i₂ = P₂ at hstep₂
        cases hstep₂ with
        | read_noop | write_noop =>
          -- σ₁ sync/configure, σ₂ read/write no-op (state-preserving; trivial, symmetric)
          sorry
        | arrive_configure _ _ =>
          -- σ₁ sync/configure, σ₂ arrive/configure
          sorry
        | arrive_register _ _ _ _ =>
          -- σ₁ sync/configure, σ₂ arrive/register
          sorry
        | sync_configure _ _ =>
          -- σ₁ sync/configure, σ₂ sync/configure
          sorry
        | sync_block _ _ _ _ =>
          -- σ₁ sync/configure, σ₂ sync/block
          sorry
      | @recycle _ _ b₂ I₂ A₂ n₂ hb₂ hfull₂ _ =>
        -- σ₂ = recycle needs a full barrier, contradicting σ₁ = interleave's guard.
        exact (interleaveGuard_full_absurd hb₂ hfull₂ (by assumption)).elim
      | done hdone _ =>
        -- σ₁ sync/configure, σ₂ done: `T.IsDone` forces `T.prog i₁ = []`, but σ₁ stepped `i₁`
        simp [hdone i₁ hi₁] at hP₁
      | error _ =>
        -- σ₁ sync/configure, σ₂ error: open — should contradict `hWS` (see σ₂-error note above).
        sorry
    | sync_block _ _ _ _ =>
      cases hσ₂ with
      | @interleave _ _ _ i₂ _ _ _ hstep₂ =>
        generalize _hP₂ : T.prog i₂ = P₂ at hstep₂
        cases hstep₂ with
        | read_noop | write_noop =>
          -- σ₁ sync/block, σ₂ read/write no-op (state-preserving; trivial, symmetric)
          sorry
        | arrive_configure _ _ =>
          -- σ₁ sync/block, σ₂ arrive/configure
          sorry
        | arrive_register _ _ _ _ =>
          -- σ₁ sync/block, σ₂ arrive/register
          sorry
        | sync_configure _ _ =>
          -- σ₁ sync/block, σ₂ sync/configure
          sorry
        | sync_block _ _ _ _ =>
          -- σ₁ sync/block, σ₂ sync/block
          sorry
      | @recycle _ _ b₂ I₂ A₂ n₂ hb₂ hfull₂ _ =>
        -- σ₂ = recycle needs a full barrier, contradicting σ₁ = interleave's guard.
        exact (interleaveGuard_full_absurd hb₂ hfull₂ (by assumption)).elim
      | done hdone _ =>
        -- σ₁ sync/block, σ₂ done: `T.IsDone` forces `T.prog i₁ = []`, but σ₁ stepped `i₁`
        simp [hdone i₁ hi₁] at hP₁
      | error _ =>
        -- σ₁ sync/block, σ₂ error: open — should contradict `hWS` (see σ₂-error note above).
        sorry
  | recycle hb₁ hfull₁ _ =>
    cases hσ₂ with
    | @interleave _ _ _ _ _ _ hbar₂ _ =>
      -- σ₂ = interleave's guard requires every barrier under-full, but σ₁ = recycle
      -- leaves barrier `b₁` full — impossible.
      exact (interleaveGuard_full_absurd hb₁ hfull₁ hbar₂).elim
    | recycle _ _ _ =>
      -- σ₁ recycle, σ₂ recycle
      sorry
    | done _ hnofull =>
      -- σ₁ recycle, σ₂ done: `done` needs no full barrier, but σ₁ recycled a full one
      exact absurd hfull₁ (by have := hnofull _ _ _ _ hb₁; omega)
    | error _ =>
      -- σ₁ recycle, σ₂ error: open — should contradict `hWS` (see σ₂-error note above).
      sorry
  | done _ _ =>
    -- σ₁ = done: `C'` is `done`, but `hWS` forces it to be a `run` configuration — impossible.
    exact absurd hWS.1 (by rintro ⟨_, _, h⟩; exact absurd h (by simp))
  | error _ =>
    -- σ₁ = error: `C'` is `err`, but `hWS` forces it to be a `run` configuration — impossible.
    exact absurd hWS.1 (by rintro ⟨_, _, h⟩; exact absurd h (by simp))

end Weft
