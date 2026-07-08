/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Traces
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union

/-!
# Well-synchronization (Definitions 6–7, §4.1), language-independently

The *well-synchronized* property is the same statement for every language of
the Weft family: any two complete executions assign every synchronization
command the same, nonzero generation. What varies between languages is

* the step relation `R` (through `IsCompleteTraceFrom`),
* which commands are synchronization commands and which barrier they operate
  on — the classifier `barrier? : Cmd → Option β`, where the barrier name type
  `β` is also the language's (for the mbarrier-extended language, the sum
  `NamedBarrier ⊕ SharedBarrier` of its two name spaces), and
* the *generation* relation `GenOf C₀ τ η g` — Definition 5 — whose counting
  is genuinely language-specific (named barriers count recycles-to-unconfigured;
  mbarriers count phase flips, with the phase-corrected observation of §5.2.3),
  as is the generation *value type* `γ` itself.

`WellSynchronized` here is Definition 7 parameterized by exactly those three;
each language instantiates it under its usual name with its own `CTAStep`,
`Cmd.barrier?`, and `IsGenOf` (Definition 6 — the CTA-level property at the
language's initial state — stays language-side, since the initial state does
too).

**`Option`-valued generations.** `GenOf C₀ τ η g` relates a command to
`g : Option γ`: `some n` when the command executes in `τ` with generation `n`,
and `none` when it never executes (deadlock). Well-synchronization then simply
demands a *shared `some`* — no sentinel value is reserved, so the generation
value type `γ` is completely abstract here: the named-barrier language
instantiates `γ := ℕ` (1-indexed, aligning with its computable `pointGen`),
while the mbarrier language is free to use `γ := ℤ`, where the phase-corrected
observation of §5.2.3 makes generations `−1` and `0` legitimately observable.
A deadlocked command still refutes well-synchronization: it relates only to
`none`, and `GenOf`'s functionality leaves no `some` witness.
-/

namespace WeftCommon

variable {State Cmd β : Type}

/-- Definition 7 (§4.1), parameterized by the language: a configuration `C₀` is
*well-synchronized* (with respect to a step relation `R`, a synchronization
classifier `barrier?`, and a generation relation `GenOf`) if it is a `run`
configuration and any two complete traces from it assign every synchronization
command the same generation `some g` — in particular the command executes in
both.

The first conjunct requires `C₀` to be a `run` configuration (Def 7's
`(s, T)`). Without it, a terminal `err` configuration with no synchronization
commands would satisfy the rest vacuously and be "well-synchronized" while not
even able to make progress. -/
def WellSynchronized {γ : Type} (R : Config State Cmd → Config State Cmd → Prop)
    (barrier? : Cmd → Option β)
    (GenOf : Config State Cmd → List (Config State Cmd) → ProgPoint → Option γ → Prop)
    (C₀ : Config State Cmd) : Prop :=
  (∃ s T, C₀ = Config.run s T) ∧
  ∀ τ₁ τ₂, IsCompleteTraceFrom R C₀ τ₁ → IsCompleteTraceFrom R C₀ τ₂ →
    ∀ η : ProgPoint, (∃ b, (η.cmd C₀).bind barrier? = some b) →
      ∃ g : γ, GenOf C₀ τ₁ η (some g) ∧ GenOf C₀ τ₂ η (some g)

/-! ## Transitive closure of a finite edge relation

The checking algorithms (Figure 4 line 17, Algorithm 2 line 17) close their
finite edge relation `R` under transitivity; the construction is generic. -/

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

end WeftCommon
