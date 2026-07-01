/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Traces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Find

/-!
# Generations and well-synchronization (§4.1)

This file continues Section 4.1 of the Weft paper with Definition 5 (generations),
Definition 6 (well-synchronized CTA), and Definition 7 (well-synchronized
configuration). They build on the traces and time of `Weft.Traces`.

## Definition 5 — generations

`Gen(τ)(cη)` tags a synchronization command `cη` (on some barrier `b`) with *which
generation* of `b` it used; unexecuted commands have generation `0`.

The paper's verbatim Def 5 reads `Gen(τ)(cη) = n` where `t(τ, η) = m` and the
first `m` steps of `τ` contain `n` recyclings of `b`. Taken literally this is
inconsistent: by Def 3 (`Weft.Traces`) `t` is the *registration* step for an
`arrive` but the *recycle* step for a `sync`, so a `sync` counts the recycle that
closes its round while a co-registering `arrive` does not. They would then get
different generations, and a first-generation `arrive` would get `0` — conflicting
both with "executed ⟹ nonzero" and with the `≠ 0` of Definitions 6–7.

We therefore use the consistent, evidently-intended **1-indexed** reading:
`Gen(τ)(cη) = (recyclings of b strictly before t(τ, η)) + 1`. For a `sync` this
equals the verbatim count (the closing recycle sits exactly at `t`, so "strictly
before, then `+1`" = "up to and including"); for an `arrive` it is the verbatim
count `+ 1`. Under it, an `arrive` and a `sync` that synchronize on the same round
get the *same* generation, and every executed synchronization command has
generation `≥ 1`.

To count recyclings of `b` from a trace (a `List Config`, which records configs
but not the rule that fired), we use that **only `CTAStep.recycle` ever resets a
barrier to unconfigured** — every thread step on `b` configures it or extends its
lists, never unconfigures it. So a step `C ⤳ C'` recycles `b` exactly when `b` is
configured-and-full in `C` and unconfigured in `C'` (`stepRecyclesBarrier`).

We model `Gen(τ)(cη) = n` as the relation `IsGenOf C₀ τ η n`. It is total on
synchronization commands: an executed sync command gets generation `≥ 1`, and one
that never executes in `τ` (e.g. blocked by a deadlock) gets `0` — the paper's
convention that unexecuted commands have generation `0`. On the memory commands
`read`/`write` it is undefined (they are not in `Gen`'s domain).

## Definitions 6 and 7 — well-synchronization

A configuration `(s, T)` is *well-synchronized* (Def 7) if it is a `run`
configuration and any two complete traces from it agree on the generation of every
synchronization command, that common generation being nonzero — i.e. every sync
command executes, at a schedule-independent generation. The `run` requirement is
essential: without it a terminal `err` configuration with no synchronization
commands would be *vacuously* well-synchronized despite making no progress at all.
A CTA `T` is well-synchronized (Def 6) when the configuration `(I, T)` is, where
`I` is the initial state — the special case of Def 7 at `State.initial`.
-/

namespace Weft

/-- The barrier a command operates on: `some b` for the synchronization commands
`sync b _` and `arrive b _`, and `none` for the memory operations. -/
def Cmd.barrier? : Cmd → Option Barrier
  | .sync b _ => some b
  | .arrive b _ => some b
  | .read _ => none
  | .write _ => none

/-- The state component `(E, B)` of a configuration, if it has one. `run` and
`done` carry a state; the error configuration `err` does not. -/
def Config.state? : Config → Option State
  | .run s _ => some s
  | .done s => some s
  | .err _ => none

/-- A barrier state is *full* when it is configured (count `some n`) and exactly
`n` threads have registered (`|I| + A = n`) — the situation in which
`CTAStep.recycle` fires. -/
def BarrierState.isFull (β : BarrierState) : Bool :=
  match β.count with
  | some n => β.synced.length + β.arrived == (n : Nat)
  | none => false

/-- The step `C ⤳ C'` recycles barrier `b`: `b` is configured-and-full in `C` and
reset to unconfigured in `C'`. Since only `CTAStep.recycle` resets a barrier, this
detects exactly the recycle steps for `b` along a trace. -/
def stepRecyclesBarrier (b : Barrier) (C C' : Config) : Bool :=
  match C.state?, C'.state? with
  | some s, some s' => (s.B b).isFull && decide (s'.B b = BarrierState.unconfigured)
  | _, _ => false

/-- The number of recyclings of barrier `b` among the first `m` steps of `τ`
(the transitions from config index `j` to `j+1` for `j < m`). -/
def recycleCount (b : Barrier) (τ : List Config) (m : Nat) : Nat :=
  (List.range m).countP fun j =>
    match τ[j]?, τ[j + 1]? with
    | some C, some C' => stepRecyclesBarrier b C C'
    | _, _ => false

/-- Definition 5 (§4.1), in the consistent 1-indexed reading (see the module
doc). The generation `Gen(τ)(cη) = n` of a synchronization command at program
point `η`, in a complete trace `τ` from `C₀`. If `cη` operates on barrier `b` and
executes at time `t(τ, η) = m`, then `n` is one more than the number of recyclings
of `b` strictly before step `m` (`recycleCount b τ (m - 1)` counts the recyclings
in the first `m - 1` steps); if `cη` is a synchronization command that never
executes in `τ` (e.g. blocked by a deadlock), then `n = 0`. Like `IsTimeOf`, it
carries `IsCompleteTraceFrom C₀ τ` so it is meaningful used on its own. As a
function of `(C₀, τ, η)` it is total on synchronization commands (`≥ 1` when
executed, `0` when not) and undefined on the memory commands `read`/`write` (not
in `Gen`'s domain).

Note (rohany): The (m-1) + 1 thing is a bit odd, but it has to deal with some
ambiguity in the Weft paper. Definition 5 in the weft paper should should be that
there are n recyclings strictly before m. However, the time definition is inclusive
of the instruction that executes at m. So the m-1 is needed to get to "strictly-before".
And then the plus 1 is because we want barrier generations to be 1-indexed rather than
0-indexed, because the formalization uses a 0 generation for an operation to represent
when the operation has not executed at all in the trace (i.e. deadlocks).
-/
def IsGenOf (C₀ : Config) (τ : List Config) (η : ProgPoint) (n : Nat) : Prop :=
  IsCompleteTraceFrom C₀ τ ∧
  ∃ b, (η.cmd C₀).bind Cmd.barrier? = some b ∧
    ((∃ m, IsTimeOf C₀ τ η m ∧ n = recycleCount b τ (m - 1) + 1) ∨
      (n = 0 ∧ ¬ ∃ m, IsTimeOf C₀ τ η m))

/-- Definition 7 (§4.1). A configuration `C₀ = (s, T)` is *well-synchronized* if it
is a `run` configuration and any two complete traces from it assign every
synchronization command the same, nonzero generation: for all complete traces
`τ₁ τ₂` from `C₀` and every program point `η` that is a synchronization command,
there is a common `g ≠ 0` with `Gen(τ₁)(cη) = Gen(τ₂)(cη) = g`.

The first conjunct requires `C₀` to be a `run` configuration (Def 7's `(s, T)`).
Without it, a terminal `err` configuration with no synchronization commands would
satisfy the rest vacuously and be "well-synchronized" while not even able to
make progress. -/
def Config.WellSynchronized (C₀ : Config) : Prop :=
  (∃ s T, C₀ = Config.run s T) ∧
  ∀ τ₁ τ₂, IsCompleteTraceFrom C₀ τ₁ → IsCompleteTraceFrom C₀ τ₂ →
    ∀ η : ProgPoint, (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) →
      ∃ g, g ≠ 0 ∧ IsGenOf C₀ τ₁ η g ∧ IsGenOf C₀ τ₂ η g

/-- Definition 6 (§4.1). A CTA `T` is *well-synchronized* if the configuration
`(I, T)` is — i.e. Definition 7 at the initial state `I = State.initial`. -/
def CTA.WellSynchronized (T : CTA) : Prop :=
  Config.WellSynchronized (Config.run State.initial T)

/-- `τ` *successfully runs `C₀` to completion*: it is a complete trace from `C₀`
(Definition 2) whose final configuration is `done`. This bundles the two facts that
a successful execution needs: that `τ` is a genuine complete trace *starting at
`C₀`* (`IsCompleteTraceFrom`, so `τ.head? = some C₀`), and that it terminates in
`done` — reaching the goal without deadlocking (a stuck `run`) or erroring (`err`). -/
def IsSuccessfulTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  IsCompleteTraceFrom C₀ τ ∧ ∃ s, τ.getLast? = some (Config.done s)

/- THESE ARE HELPER FUNCTIONS / LEMMAS GENERATED BY CLAUDE TO HELP PROVE THE
    REAL THEOREMS BELOW -/

/-- A non-error thread step changes the program only by dropping a prefix of its
commands: `P' = P.drop d` for some `d` (in fact `d ∈ {0, 1}`). `read`/`write`/
`arrive` advance by one command (`d = 1`); `sync` parks, leaving control unchanged
(`d = 0`). -/
theorem ThreadStep.run_drop {s s' : State} {i : ThreadId} {P P' : Prog}
    (hstep : ThreadStep (.run s i P) (.run s' i P')) : ∃ d, P' = P.drop d := by
  cases hstep with
  | read_noop => exact ⟨1, rfl⟩
  | write_noop => exact ⟨1, rfl⟩
  | arrive_configure => exact ⟨1, rfl⟩
  | arrive_register => exact ⟨1, rfl⟩
  | sync_configure => exact ⟨0, rfl⟩
  | sync_block => exact ⟨0, rfl⟩

/-- One CTA step changes each thread's program only by dropping a prefix:
`C'.progOf t = (C.progOf t).drop d` for some `d`. (`interleave`/`recycle` drop `0`
or `1`; `done` drops the whole program; `error` keeps it.) -/
theorem CTAStep.progOf_drop {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    ∃ d, C'.progOf t = (C.progOf t).drop d := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hstep =>
      by_cases h : t = i
      · subst h
        obtain ⟨d, hd⟩ := hstep.run_drop
        exact ⟨d, by simp [Config.progOf, CTA.set, Function.update_self, hd]⟩
      · exact ⟨0, by simp [Config.progOf, CTA.set, Function.update_of_ne h]⟩
  | @recycle s T b I A n hb hfull hpark =>
      by_cases h : t ∈ I
      · exact ⟨1, by simp [Config.progOf, CTA.wake, h, List.drop_one]⟩
      · exact ⟨0, by simp [Config.progOf, CTA.wake, h]⟩
  | @done s T hdone _ =>
      exact ⟨(T.prog t).length, by simp [Config.progOf, List.drop_length]⟩
  | @error s T i P' _ hstep =>
      exact ⟨0, by simp [Config.progOf]⟩

/-- One CTA step makes each thread's program a suffix of its previous program. -/
theorem CTAStep.progOf_suffix {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    C'.progOf t <:+ C.progOf t := by
  obtain ⟨d, hd⟩ := hstep.progOf_drop t
  rw [hd]
  exact ⟨(C.progOf t).take d, List.take_append_drop d (C.progOf t)⟩

/-- Along a (sub)trace, the *last* configuration's program for a thread is a suffix
of every configuration's program for that thread — programs only shrink. -/
theorem CTAStep.suffix_last (t : ThreadId) :
    ∀ {l : List Config} {Cₙ : Config}, List.IsChain CTAStep l → l.getLast? = some Cₙ →
      ∀ C ∈ l, Cₙ.progOf t <:+ C.progOf t := by
  intro l
  induction l with
  | nil => intro Cₙ _ hlast; simp at hlast
  | cons a rest ih =>
    intro Cₙ hchain hlast C hC
    cases rest with
    | nil =>
      simp only [List.mem_singleton] at hC
      subst hC
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact List.suffix_refl _
    | cons b t' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.getLast?_cons_cons] at hlast
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact (ih hbt hlast b (by simp)).trans (hab.progOf_suffix t)
      · exact ih hbt hlast C hC'

/-- A suffix `s` of `l` is `l.drop (|l| - |s|)`. -/
theorem List.IsSuffix.eq_drop {α} {s l : List α} (h : s <:+ l) :
    s = l.drop (l.length - s.length) := by
  obtain ⟨p, rfl⟩ := h
  rw [List.length_append, Nat.add_sub_cancel, List.drop_left]

/-- A suffix is no longer than the list. -/
theorem suffix_length_le {α} {s l : List α} (h : s <:+ l) : s.length ≤ l.length := by
  obtain ⟨p, rfl⟩ := h
  simp [List.length_append]

/-- Consecutive configurations of a trace step: from a chain with `τ[j]? = some C` and
`τ[j+1]? = some C'`, the single CTA step `C ⤳ C'`. -/
theorem chain_step {τ : List Config} (hchain : List.IsChain CTAStep τ) {j : Nat}
    {C C' : Config} (hC : τ[j]? = some C) (hC' : τ[j + 1]? = some C') : CTAStep C C' := by
  obtain ⟨_hj, rfl⟩ := List.getElem?_eq_some_iff.mp hC
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.mp hC'
  exact (List.isChain_iff_getElem.mp hchain) j hj1

/-- Programs only shrink: at a later trace index a thread's remaining program is a
suffix of its program at an earlier index. -/
theorem progOf_suffix_index_le {τ : List Config} (hchain : List.IsChain CTAStep τ)
    (t : ThreadId) {p : Nat} {Cp : Config} (hp : τ[p]? = some Cp) :
    ∀ {q : Nat}, p ≤ q → ∀ {Cq : Config}, τ[q]? = some Cq → Cq.progOf t <:+ Cp.progOf t := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base =>
      intro Cq hq
      rw [hp, Option.some.injEq] at hq
      subst hq; exact List.suffix_refl _
  | succ q _hpq ih =>
      intro Cq hq
      have hqlt : q < τ.length := by
        have h1 : q + 1 < τ.length := (List.getElem?_eq_some_iff.mp hq).1
        omega
      have hD : τ[q]? = some τ[q] := List.getElem?_eq_getElem hqlt
      exact ((chain_step hchain hD hq).progOf_suffix t).trans (ih hD)

/-- `IsTimeOf` is a partial function: an instruction executes at most once in a trace. -/
theorem IsTimeOf.unique {C₀ : Config} {τ : List Config} {η : ProgPoint} {m m' : Nat}
    (h : IsTimeOf C₀ τ η m) (h' : IsTimeOf C₀ τ η m') : m = m' := by
  obtain ⟨hτ, hlt, j, C, C', hm, hCj, hCj1, hCeq, hC'eq⟩ := h
  obtain ⟨_, _, j', D, D', hm', hDj, hDj1, hDeq, hD'eq⟩ := h'
  subst hm; subst hm'
  have hchain := hτ.1.subtrace
  rcases Nat.lt_trichotomy j j' with hlt' | heq | hgt
  · exfalso
    have hsuf := progOf_suffix_index_le hchain η.thread hCj1 (show j + 1 ≤ j' by omega) hDj
    have hle := suffix_length_le hsuf
    rw [hDeq, hC'eq, List.length_drop, List.length_drop] at hle
    omega
  · omega
  · exfalso
    have hsuf := progOf_suffix_index_le hchain η.thread hDj1 (show j' + 1 ≤ j by omega) hCj
    have hle := suffix_length_le hsuf
    rw [hCeq, hD'eq, List.length_drop, List.length_drop] at hle
    omega

/-- A non-error thread step drops at most one command (`d ≤ 1`). -/
theorem ThreadStep.run_drop_le_one {s s' : State} {i : ThreadId} {P P' : Prog}
    (hstep : ThreadStep (.run s i P) (.run s' i P')) : ∃ d, d ≤ 1 ∧ P' = P.drop d := by
  cases hstep with
  | read_noop => exact ⟨1, by omega, rfl⟩
  | write_noop => exact ⟨1, by omega, rfl⟩
  | arrive_configure => exact ⟨1, by omega, rfl⟩
  | arrive_register => exact ⟨1, by omega, rfl⟩
  | sync_configure => exact ⟨0, by omega, rfl⟩
  | sync_block => exact ⟨0, by omega, rfl⟩

/-- A single CTA step shortens a thread's remaining program by at most one command:
the program never jumps down by more than 1 (the `done` step only fires once every
program is already empty). -/
theorem CTAStep.progOf_length_le_succ {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    (C.progOf t).length ≤ (C'.progOf t).length + 1 := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
      simp only [Config.progOf]
      by_cases h : t = i
      · subst h
        obtain ⟨d, hd1, hd⟩ := hth.run_drop_le_one
        simp only [CTA.set, Function.update_self, hd, List.length_drop]
        omega
      · simp only [CTA.set, Function.update_of_ne h]; omega
  | @recycle s T b I A n hb hfull hpark =>
      simp only [Config.progOf]
      by_cases h : t ∈ I
      · simp only [CTA.wake, if_pos h]
        cases T.prog t with
        | nil => simp
        | cons x xs => simp
      · simp only [CTA.wake, if_neg h]; omega
  | @done s T hdone _ =>
      have hnil : T.prog t = [] := by
        by_cases ht : t ∈ T.ids
        · exact hdone t ht
        · exact T.nil_outside_ids t ht
      simp only [Config.progOf, hnil]; simp
  | @error s T i P' _ hth =>
      simp only [Config.progOf]; omega

/-- Every command runs in a successful execution: in a complete trace from `C₀` that
ends in `done`, every valid program point `η` (`η.idx <` its program length) has a
time. Found by an integer intermediate-value argument — the program length falls from
`|C₀.progOf i|` to `0` in steps of at most one (`progOf_length_le_succ`), so it passes
through the transition `|drop η.idx| → |drop (η.idx+1)|`; lengths pin down the suffix
(`progOf_suffix_index_le`), giving the exact `drop`s. -/
theorem exists_time_of_ends_done {C₀ : Config} {τ' : List Config} {sd : State}
    (hτ : IsCompleteTraceFrom C₀ τ') (hlast : τ'.getLast? = some (Config.done sd))
    {η : ProgPoint} (hk : η.idx < (C₀.progOf η.thread).length) :
    ∃ n, IsTimeOf C₀ τ' η n := by
  have hchain : List.IsChain CTAStep τ' := hτ.1.subtrace
  set i := η.thread with hidef
  have h0 : τ'[0]? = some C₀ := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.done sd) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hsuffix : ∀ {j} {C : Config}, τ'[j]? = some C → C.progOf i <:+ C₀.progOf i :=
    fun {j C} hCj => progOf_suffix_index_le hchain i h0 (Nat.zero_le j) hCj
  have hQlast : ((τ'[τ'.length - 1]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [hlastidx]; change (0 : Nat) < (C₀.progOf i).length - η.idx; omega
  have hex : ∃ j, ((τ'[j]?).map (fun (C : Config) => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := ⟨τ'.length - 1, hQlast⟩
  have hQj0 := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ τ'.length - 1 := Nat.find_le hQlast
  have hQ0 : ¬ ((τ'[0]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [h0]; change ¬ (C₀.progOf i).length < (C₀.progOf i).length - η.idx; omega
  have hj0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hQj0; exact absurd hQj0 hQ0
    · exact h
  have hminj := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have hj0lt : Nat.find hex < τ'.length := by omega
  obtain ⟨C, hC⟩ : ∃ C, τ'[Nat.find hex - 1]? = some C :=
    ⟨_, List.getElem?_eq_getElem (show Nat.find hex - 1 < τ'.length by omega)⟩
  obtain ⟨C', hC'⟩ : ∃ C', τ'[Nat.find hex]? = some C' :=
    ⟨_, List.getElem?_eq_getElem hj0lt⟩
  have hCC' : τ'[Nat.find hex - 1 + 1]? = some C' := by
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hC'
  have hub : (C.progOf i).length ≤ (C'.progOf i).length + 1 :=
    (chain_step hchain hC hCC').progOf_length_le_succ i
  have e1 : ((τ'[Nat.find hex - 1]?).map (fun C => (C.progOf i).length)).getD 0
      = (C.progOf i).length := by rw [hC]; rfl
  have e2 : ((τ'[Nat.find hex]?).map (fun C => (C.progOf i).length)).getD 0
      = (C'.progOf i).length := by rw [hC']; rfl
  rw [e1] at hminj
  rw [e2] at hQj0
  have hlenC : (C.progOf i).length = (C₀.progOf i).length - η.idx := by omega
  have hlenC' : (C'.progOf i).length = (C₀.progOf i).length - η.idx - 1 := by omega
  have hCdrop : C.progOf i = (C₀.progOf i).drop η.idx := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC)
    rw [hlenC] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx) = η.idx by omega] at heq
  have hC'drop : C'.progOf i = (C₀.progOf i).drop (η.idx + 1) := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC')
    rw [hlenC'] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx - 1) = η.idx + 1 by omega] at heq
  exact ⟨Nat.find hex, hτ, hk, Nat.find hex - 1, C, C', by omega, hC, hCC', hCdrop, hC'drop⟩

/-- `IsGenOf` is a partial function: a command has at most one generation in a trace. -/
theorem IsGenOf.unique {C₀ : Config} {τ : List Config} {η : ProgPoint} {g g' : Nat}
    (h : IsGenOf C₀ τ η g) (h' : IsGenOf C₀ τ η g') : g = g' := by
  obtain ⟨_, b, hb, hcase⟩ := h
  obtain ⟨_, b', hb', hcase'⟩ := h'
  rw [hb] at hb'; obtain rfl := Option.some.inj hb'
  rcases hcase with ⟨m, hm, hg⟩ | ⟨hg0, hno⟩
  · rcases hcase' with ⟨m', hm', hg'⟩ | ⟨hg0', hno'⟩
    · have hmm : m = m' := IsTimeOf.unique hm hm'
      rw [hg, hg', hmm]
    · exact absurd ⟨m, hm⟩ hno'
  · rcases hcase' with ⟨m', hm', _⟩ | ⟨hg0', _⟩
    · exact absurd ⟨m', hm'⟩ hno
    · rw [hg0, hg0']

/-- One more recycle of `b` between steps `p` and `p+1` raises the recycle count by
exactly one. -/
theorem recycleCount_succ_of_recycle (b : Barrier) (τ : List Config) {p : Nat} {C C' : Config}
    (hp : τ[p]? = some C) (hp1 : τ[p + 1]? = some C') (hrec : stepRecyclesBarrier b C C' = true) :
    recycleCount b τ (p + 1) = recycleCount b τ p + 1 := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append]
  congr 1
  simp [hp, hp1, hrec]

/-- The recycle count is monotone in the step bound. -/
theorem recycleCount_mono (b : Barrier) (τ : List Config) : Monotone (recycleCount b τ) :=
  monotone_nat_of_le_succ fun p => by
    unfold recycleCount; rw [List.range_succ, List.countP_append]; exact Nat.le_add_right _ _

/-- A step that drops a thread's parked `sync bb nn` head is a recycle of `bb`: only
`CTAStep.recycle` can advance past a `sync`, and it resets `bb` to unconfigured, so
`stepRecyclesBarrier bb` holds. -/
theorem sync_drop_recycles {C C' : Config} (hstep : CTAStep C C') {t : ThreadId}
    {bb : Barrier} {nn : ℕ+} {rest : Prog}
    (hC : C.progOf t = Cmd.sync bb nn :: rest) (hC' : C'.progOf t = rest) :
    stepRecyclesBarrier bb C C' = true := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
      exfalso
      simp only [Config.progOf] at hC hC'
      by_cases h : t = i
      · subst h
        simp only [CTA.set, Function.update_self] at hC'
        subst hC'
        rw [hC] at hth
        cases hth
      · simp only [CTA.set, Function.update_of_ne h] at hC'
        rw [hC] at hC'; simp at hC'
  | @recycle s T b I A n hb hfull hpark =>
      simp only [Config.progOf] at hC hC'
      by_cases h : t ∈ I
      · have hpk := hpark t h
        rw [hC] at hpk; simp only [List.head?_cons, Option.some.injEq, Cmd.sync.injEq] at hpk
        obtain ⟨rfl, rfl⟩ := hpk
        simp [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
          Function.update_self, BarrierState.unconfigured]
      · exfalso
        simp only [CTA.wake, if_neg h] at hC'
        rw [hC] at hC'; simp at hC'
  | @done s T hdone _ =>
      exfalso
      simp only [Config.progOf] at hC
      have hnil : T.prog t = [] := by
        by_cases ht : t ∈ T.ids
        · exact hdone t ht
        · exact T.nil_outside_ids t ht
      rw [hnil] at hC; simp at hC
  | @error s T i P' _ hth =>
      exfalso
      simp only [Config.progOf] at hC hC'
      rw [hC] at hC'; simp at hC'

/-- Reading a generation off `IsGenOf` at a known time: if `η` is a `bb`-command that
executes at `m`, its generation is `recycleCount bb τ (m-1) + 1`. -/
theorem isGenOf_recycleCount {C₀ : Config} {τ : List Config} {η : ProgPoint} {g : Nat}
    {bb : Barrier} {m : Nat} (hgen : IsGenOf C₀ τ η g)
    (hbb : (η.cmd C₀).bind Cmd.barrier? = some bb) (hm : IsTimeOf C₀ τ η m) :
    g = recycleCount bb τ (m - 1) + 1 := by
  obtain ⟨_, bb', hbb', hcase⟩ := hgen
  rw [hbb] at hbb'; obtain rfl := Option.some.inj hbb'
  rcases hcase with ⟨m', hm', hg⟩ | ⟨_, hno⟩
  · rw [hg, IsTimeOf.unique hm hm']
  · exact absurd ⟨m, hm⟩ hno

/-- A `sync`'s execution step *is* a recycle of its barrier: at the step `n` where a
`sync bb nn` command runs, the transition `τ[n-1] ⤳ τ[n]` recycles `bb`. -/
theorem sync_time_recycles {C₀ : Config} {τ : List Config} {η : ProgPoint} {n : Nat}
    {bb : Barrier} {nn : ℕ+} (hm : IsTimeOf C₀ τ η n)
    (hcmd : η.cmd C₀ = some (Cmd.sync bb nn)) :
    ∃ C C', τ[n - 1]? = some C ∧ τ[n]? = some C' ∧ stepRecyclesBarrier bb C C' = true := by
  obtain ⟨hτ, hidxL, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := hm
  subst hn
  refine ⟨C, C', by rw [show j + 1 - 1 = j by omega]; exact hCj, hCj1, ?_⟩
  have hstep : CTAStep C C' := chain_step hτ.1.subtrace hCj hCj1
  have hhead : (C₀.progOf η.thread)[η.idx]'hidxL = Cmd.sync bb nn := by
    have hc := hcmd
    simp only [ProgPoint.cmd] at hc
    rw [List.getElem?_eq_getElem hidxL, Option.some.injEq] at hc
    exact hc
  have hCsync : C.progOf η.thread = Cmd.sync bb nn :: C'.progOf η.thread := by
    rw [hCeq, hC'eq, List.drop_eq_getElem_cons hidxL, hhead]
  exact sync_drop_recycles hstep hCsync rfl

/-- The program point at index `|C₀.progOf t| - |Cₙ.progOf t|` names the command at
the head of `Cₙ.progOf t`, when the latter is a suffix of `C₀.progOf t`. -/
theorem cmd_at_last {C₀ Cₙ : Config} {t : ThreadId} {cmd : Cmd} {c : Prog}
    (hsuf : Cₙ.progOf t <:+ C₀.progOf t) (hCn : Cₙ.progOf t = cmd :: c) :
    (ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length)).cmd C₀ = some cmd := by
  have hk : (C₀.progOf t).drop ((C₀.progOf t).length - (Cₙ.progOf t).length) = cmd :: c := by
    rw [← List.IsSuffix.eq_drop hsuf]; exact hCn
  change (C₀.progOf t)[(C₀.progOf t).length - (Cₙ.progOf t).length]? = some cmd
  rw [← Nat.add_zero ((C₀.progOf t).length - (Cₙ.progOf t).length), ← List.getElem?_drop, hk]
  rfl

/-- The command at the head of the *last* configuration's program never executes:
the program never gets shorter than at the end, so it never advances past that
command. -/
theorem noTime_at_last {C₀ Cₙ : Config} {τ : List Config} {t : ThreadId}
    (hτ : IsCompleteTraceFrom C₀ τ) (hlast : τ.getLast? = some Cₙ)
    (hpos : 0 < (Cₙ.progOf t).length) (hle : (Cₙ.progOf t).length ≤ (C₀.progOf t).length) :
    ¬ ∃ m, IsTimeOf C₀ τ (ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length)) m := by
  rintro ⟨m, _, _, j, C, C', _, _, hCj1, _, hC'eq⟩
  have hC'mem : C' ∈ τ := List.mem_of_getElem? hCj1
  have hsuf : Cₙ.progOf t <:+ C'.progOf t :=
    CTAStep.suffix_last t hτ.1.subtrace hlast C' hC'mem
  have hlen := suffix_length_le hsuf
  simp only at hC'eq
  rw [hC'eq, List.length_drop] at hlen
  omega

/-- In a chain, the last element is either the head (singleton) or has a
predecessor that steps to it. -/
theorem step_into_getLast : ∀ {l : List Config} {x : Config}, List.IsChain CTAStep l →
    l.getLast? = some x → l.head? = some x ∨ ∃ y, CTAStep y x := by
  intro l
  induction l with
  | nil => intro x _ hlast; simp at hlast
  | cons a rest ih =>
    intro x h hlast
    cases rest with
    | nil => left; rw [List.getLast?_singleton] at hlast; simpa using hlast
    | cons b t' =>
      rw [List.isChain_cons_cons] at h
      obtain ⟨hab, hbt⟩ := h
      rw [List.getLast?_cons_cons] at hlast
      rcases ih hbt hlast with hhead | hstep
      · right
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨a, hhead ▸ hab⟩
      · exact Or.inr hstep

/-- The shared core of the `err`/deadlock cases: a thread `t` whose program at the
last configuration is headed by a synchronization command yields a sync program
point that never executes. -/
theorem unexec_sync_of_last {C₀ Cₙ : Config} {τ : List Config} {t : ThreadId}
    {cmd : Cmd} {c : Prog} {b : Barrier}
    (hτ : IsCompleteTraceFrom C₀ τ) (hlast : τ.getLast? = some Cₙ) (hC₀mem : C₀ ∈ τ)
    (hCn : Cₙ.progOf t = cmd :: c) (hb : cmd.barrier? = some b) :
    ∃ η : ProgPoint, (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) ∧ ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hsuf : Cₙ.progOf t <:+ C₀.progOf t :=
    CTAStep.suffix_last t hτ.1.subtrace hlast C₀ hC₀mem
  refine ⟨ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length), ⟨b, ?_⟩, ?_⟩
  · rw [cmd_at_last hsuf hCn]; exact hb
  · refine noTime_at_last hτ hlast ?_ (suffix_length_le hsuf)
    rw [hCn]; simp

/-- A complete trace from a `run` configuration that ends in `err` contains a
synchronization command that never executes (the one that triggered the error). -/
theorem err_has_unexec_sync {C₀ : Config} {τ : List Config} {T : CTA}
    (hτ : IsCompleteTraceFrom C₀ τ) (hrun : ∃ s T₀, C₀ = Config.run s T₀)
    (hlast : τ.getLast? = some (Config.err T)) :
    ∃ η : ProgPoint, (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) ∧ ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hC₀mem : C₀ ∈ τ := List.mem_of_mem_head? hτ.2
  obtain ⟨y, hstep⟩ : ∃ y, CTAStep y (Config.err T) := by
    rcases step_into_getLast hτ.1.subtrace hlast with hhead | h
    · exfalso
      rw [hτ.2] at hhead
      obtain ⟨s, T₀, rfl⟩ := hrun
      simp at hhead
    · exact h
  cases hstep with
  | @error s _ i P' _ hth =>
    generalize hp : T.prog i = P at hth
    cases hth with
    | sync_err_count _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | arrive_err_count _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl

/-- Well-synchronization rules out an unexecuted synchronization command: it
assigns every sync command a nonzero generation, but an unexecuted one has
generation `0`. -/
theorem wellSync_no_unexec_sync {C₀ : Config} (h : C₀.WellSynchronized)
    {τ : List Config} (hτ : IsCompleteTraceFrom C₀ τ) {η : ProgPoint}
    (hηsync : ∃ b, (η.cmd C₀).bind Cmd.barrier? = some b)
    (hηnoexec : ¬ ∃ m, IsTimeOf C₀ τ η m) : False := by
  obtain ⟨g, hg0, hgen, _⟩ := h.2 τ τ hτ hτ η hηsync
  obtain ⟨_, b, _, hcase⟩ := hgen
  rcases hcase with ⟨m, hm, _⟩ | ⟨hg, _⟩
  · exact hηnoexec ⟨m, hm⟩
  · exact hg0 hg

/-- `updateMapOn f Y x` sends `a` to `x` if `a ∈ Y`, else to `f a`. -/
theorem updateMapOn_apply {α β} [DecidableEq α] (f : α → β) (Y : List α) (x : β) (a : α) :
    updateMapOn f Y x a = if a ∈ Y then x else f a := by
  induction Y with
  | nil => simp [updateMapOn]
  | cons y ys ih =>
    change Function.update (updateMapOn f ys x) y x a = _
    rw [Function.update_apply, ih]
    by_cases h : a = y
    · subst h; simp
    · simp [h, List.mem_cons]

/-! ### The blocking invariant

A part of well-formedness, separated out because its three clauses support each other
inductively. To turn "a recycle clears a *full* barrier" into "a recycle consumes exactly
its arrival count", the synced list at a recycle must be duplicate-free: `recycle`'s
`hfull` premise is in list length, but the actual command/registration drop is the number
of *distinct* woken ids. There may be duplicate *arrivers* on a barrier, but never
duplicate *syncers*: a thread is disabled the instant it syncs (`synced ⟹ disabled`) and
re-enabled only by the recycle that clears it, so it cannot re-sync (`Nodup`) nor be synced
at two barriers at once (`uniqueness`). -/

/-- The blocking invariant on a state: every barrier's synced list is duplicate-free
(`Nodup`), every synced thread is disabled, and no thread is synced at two distinct
barriers simultaneously. -/
def State.BlockInv (s : State) : Prop :=
  (∀ b, (s.B b).synced.Nodup) ∧
  (∀ b i, i ∈ (s.B b).synced → s.E i = false) ∧
  (∀ b b' i, i ∈ (s.B b).synced → i ∈ (s.B b').synced → b = b')

/-- `BlockInv` holds at the initial state: every synced list is empty. -/
theorem State.BlockInv.initial : State.initial.BlockInv :=
  ⟨fun b => by simp [State.initial, BarrierState.unconfigured],
   fun b i hi => by simp [State.initial, BarrierState.unconfigured] at hi,
   fun b b' i hi _ => by simp [State.initial, BarrierState.unconfigured] at hi⟩

/-- `BlockInv` is preserved by every step. The interesting cases: a `sync` adds an
enabled thread to a synced list (fresh by `synced ⟹ disabled`, keeping `Nodup` and
uniqueness), and a `recycle` of `b₀` re-enables exactly `synced(b₀)`, which by uniqueness
is disjoint from every other synced list, so the `disabled` clause survives elsewhere. -/
theorem blockInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.BlockInv) :
    ∀ s', C'.state? = some s' → s'.BlockInv := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hth =>
    obtain ⟨hnd, hdis, hone⟩ := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact ⟨hnd, hdis, hone⟩
    | write_noop => exact ⟨hnd, hdis, hone⟩
    | arrive_configure he hb0 =>
      rename_i b₀ n
      refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
      · by_cases hbb : b = b₀
        · subst hbb; simp [Function.update_self]
        · simp only [Function.update_of_ne hbb]; exact hnd b
      · by_cases hbb : b = b₀
        · subst hbb; simp [Function.update_self] at hj
        · simp only [Function.update_of_ne hbb] at hj; exact hdis b j hj
      · by_cases hbb : b = b₀
        · subst hbb; simp [Function.update_self] at h1
        · by_cases hbb' : b' = b₀
          · subst hbb'; simp [Function.update_self] at h2
          · simp only [Function.update_of_ne hbb] at h1
            simp only [Function.update_of_ne hbb'] at h2
            exact hone b b' j h1 h2
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self]; have h := hnd b; rw [hb0] at h; exact h
        · simp only [Function.update_of_ne hbb]; exact hnd b
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self] at hj
          exact hdis b j (by rw [hb0]; exact hj)
        · simp only [Function.update_of_ne hbb] at hj; exact hdis b j hj
      · refine hone b b' j ?_ ?_
        · by_cases hbb : b = b₀
          · subst hbb; simp only [Function.update_self] at h1; rw [hb0]; exact h1
          · simp only [Function.update_of_ne hbb] at h1; exact h1
        · by_cases hbb' : b' = b₀
          · subst hbb'; simp only [Function.update_self] at h2; rw [hb0]; exact h2
          · simp only [Function.update_of_ne hbb'] at h2; exact h2
    | sync_configure he hb0 =>
      rename_i b₀ n c
      refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
      · by_cases hbb : b = b₀
        · subst hbb; simp [Function.update_self]
        · simp only [Function.update_of_ne hbb]; exact hnd b
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self] at hj
          rw [List.mem_singleton] at hj; subst hj; simp [Function.update_self]
        · simp only [Function.update_of_ne hbb] at hj
          by_cases hji : j = i
          · subst hji; simp [Function.update_self]
          · simp only [Function.update_of_ne hji]; exact hdis b j hj
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self] at h1
          rw [List.mem_singleton] at h1; subst h1
          by_cases hbb' : b' = b
          · exact hbb'.symm
          · simp only [Function.update_of_ne hbb'] at h2
            exact absurd (hdis b' j h2) (by rw [he]; simp)
        · by_cases hbb' : b' = b₀
          · subst hbb'; simp only [Function.update_self] at h2
            rw [List.mem_singleton] at h2; subst h2
            simp only [Function.update_of_ne hbb] at h1
            exact absurd (hdis b j h1) (by rw [he]; simp)
          · simp only [Function.update_of_ne hbb] at h1
            simp only [Function.update_of_ne hbb'] at h2
            exact hone b b' j h1 h2
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self, List.nodup_cons]
          refine ⟨fun hii => ?_, by have h := hnd b; rw [hb0] at h; exact h⟩
          have := hdis b i (by rw [hb0]; exact hii); rw [he] at this; exact absurd this (by simp)
        · simp only [Function.update_of_ne hbb]; exact hnd b
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self] at hj
          rw [List.mem_cons] at hj
          rcases hj with rfl | hjI
          · simp [Function.update_self]
          · by_cases hji : j = i
            · subst hji; simp [Function.update_self]
            · simp only [Function.update_of_ne hji]; exact hdis b j (by rw [hb0]; exact hjI)
        · simp only [Function.update_of_ne hbb] at hj
          by_cases hji : j = i
          · subst hji; simp [Function.update_self]
          · simp only [Function.update_of_ne hji]; exact hdis b j hj
      · by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self] at h1
          rw [List.mem_cons] at h1
          by_cases hbb' : b' = b
          · exact hbb'.symm
          · simp only [Function.update_of_ne hbb'] at h2
            rcases h1 with rfl | h1I
            · exact absurd (hdis b' j h2) (by rw [he]; simp)
            · exact hone b b' j (by rw [hb0]; exact h1I) h2
        · by_cases hbb' : b' = b₀
          · subst hbb'; simp only [Function.update_self] at h2
            rw [List.mem_cons] at h2
            simp only [Function.update_of_ne hbb] at h1
            rcases h2 with rfl | h2I
            · exact absurd (hdis b j h1) (by rw [he]; simp)
            · exact hone b b' j h1 (by rw [hb0]; exact h2I)
          · simp only [Function.update_of_ne hbb] at h1
            simp only [Function.update_of_ne hbb'] at h2
            exact hone b b' j h1 h2
  | @recycle s T b₀ I₀ A₀ n₀ hb hfullr hpark =>
    obtain ⟨hnd, hdis, hone⟩ := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
    · by_cases hbb : b = b₀
      · subst hbb; simp [Function.update_self, BarrierState.unconfigured]
      · simp only [Function.update_of_ne hbb]; exact hnd b
    · by_cases hbb : b = b₀
      · subst hbb; simp [Function.update_self, BarrierState.unconfigured] at hj
      · simp only [Function.update_of_ne hbb] at hj
        have hjnotI : j ∉ I₀ := by
          intro hjI
          exact hbb (hone b b₀ j hj (by rw [hb]; exact hjI))
        change updateMapOn s.E I₀ true j = false
        rw [updateMapOn_apply, if_neg hjnotI]; exact hdis b j hj
    · by_cases hbb : b = b₀
      · subst hbb; simp [Function.update_self, BarrierState.unconfigured] at h1
      · by_cases hbb' : b' = b₀
        · subst hbb'; simp [Function.update_self, BarrierState.unconfigured] at h2
        · simp only [Function.update_of_ne hbb] at h1
          simp only [Function.update_of_ne hbb'] at h2
          exact hone b b' j h1 h2
  | @done s T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    exact hC s rfl
  | @error s T i P' _ hth => simp [Config.state?] at hs'

/-- `BlockInv` holds at every configuration of a chain whose head satisfies it. -/
theorem blockInv_chain : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → (∀ s, C₀.state? = some s → s.BlockInv) →
    ∀ C ∈ τ, ∀ s, C.state? = some s → s.BlockInv := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ s, b₁.state? = some s → s.BlockInv := blockInv_step hstep hC₀
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 C hC'

/-- The converse of `BlockInv`'s "synced ⟹ disabled" clause: every **disabled** thread is
parked at some barrier, i.e. it appears in some synced list. Together with `BlockInv` this
gives "disabled ⟺ synced somewhere". A thread is disabled exactly by a `sync` (which puts
it in that barrier's synced list) and re-enabled exactly by the matching `recycle` (which
removes it), so this is invariant. It is what restores the enabled map to all-`true` at a
`done` configuration (no syncers parked ⇒ no disabled threads). -/
def State.EnabledInv (s : State) : Prop :=
  ∀ i, s.E i = false → ∃ b, i ∈ (s.B b).synced

/-- `EnabledInv` holds at the initial state: every thread is enabled, so the implication
is vacuous. -/
theorem State.EnabledInv.initial : State.initial.EnabledInv := by
  intro i hi; simp [State.initial] at hi

/-- `EnabledInv` is preserved by every step. A `sync` that disables thread `i` simultaneously
adds it to a synced list; a `recycle` re-enables exactly the threads it removes from a synced
list; every other step touches neither the enabled map nor any synced list relevantly. -/
theorem enabledInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.EnabledInv) :
    ∀ s', C'.state? = some s' → s'.EnabledInv := by
  intro s' hs' i hi
  cases hstep with
  | @interleave s s'' T j P' hj hbar hth =>
    have hinv := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    generalize hpj : T.prog j = Pj at hth
    cases hth with
    | read_noop => exact hinv i hi
    | write_noop => exact hinv i hi
    | arrive_configure he hb =>
      rename_i b₀ n
      obtain ⟨b, hb'⟩ := hinv i hi
      refine ⟨b, ?_⟩
      by_cases hbb : b = b₀
      · subst hbb; rw [hb] at hb'; simp [BarrierState.unconfigured] at hb'
      · simpa only [Function.update_of_ne hbb] using hb'
    | arrive_register he hb hpos hlt =>
      rename_i b₀ n I A
      obtain ⟨b, hb'⟩ := hinv i hi
      refine ⟨b, ?_⟩
      by_cases hbb : b = b₀
      · subst hbb; simp only [Function.update_self]; rw [hb] at hb'; exact hb'
      · simpa only [Function.update_of_ne hbb] using hb'
    | sync_configure he hb =>
      rename_i b₀ n c
      by_cases hji : i = j
      · exact ⟨b₀, by subst hji; simp [Function.update_self]⟩
      · have hiold : s.E i = false := by
          have h : Function.update s.E j false i = false := hi
          rwa [Function.update_of_ne hji] at h
        obtain ⟨b, hb'⟩ := hinv i hiold
        refine ⟨b, ?_⟩
        by_cases hbb : b = b₀
        · subst hbb; rw [hb] at hb'; simp [BarrierState.unconfigured] at hb'
        · simpa only [Function.update_of_ne hbb] using hb'
    | sync_block he hb hpos hlt =>
      rename_i b₀ n c I A
      by_cases hji : i = j
      · exact ⟨b₀, by subst hji; simp [Function.update_self]⟩
      · have hiold : s.E i = false := by
          have h : Function.update s.E j false i = false := hi
          rwa [Function.update_of_ne hji] at h
        obtain ⟨b, hb'⟩ := hinv i hiold
        refine ⟨b, ?_⟩
        by_cases hbb : b = b₀
        · subst hbb; simp only [Function.update_self]; rw [hb] at hb'
          exact List.mem_cons_of_mem _ hb'
        · simpa only [Function.update_of_ne hbb] using hb'
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    have hinv := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    have hi' : updateMapOn s.E I₀ true i = false := hi
    rw [updateMapOn_apply] at hi'
    split at hi'
    · simp at hi'
    · rename_i hni
      obtain ⟨b, hb'⟩ := hinv i hi'
      refine ⟨b, ?_⟩
      by_cases hbb : b = b₀
      · subst hbb; rw [hb] at hb'; exact absurd hb' hni
      · simpa only [Function.update_of_ne hbb] using hb'
  | @done s T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    exact hC s rfl i hi
  | @error s T j P' _ hth => simp [Config.state?] at hs'

/-- `EnabledInv` holds at every configuration of a chain whose head satisfies it. -/
theorem enabledInv_chain : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → (∀ s, C₀.state? = some s → s.EnabledInv) →
    ∀ C ∈ τ, ∀ s, C.state? = some s → s.EnabledInv := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ s, b₁.state? = some s → s.EnabledInv := enabledInv_step hstep hC₀
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 C hC'

/-- The source of any step is a `run` configuration (every `CTAStep` rule fires from
`run`). Lets a step's source state be read off for invariant-extraction. -/
theorem CTAStep.source_run {C C' : Config} (h : CTAStep C C') :
    ∃ s T, C = Config.run s T := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- The well-formedness invariant for a `run` configuration, a single predicate
covering every barrier. For each barrier `b`:

* if it is **configured** (`s.B b = ⟨I, A, some n⟩`), registration is non-empty
  (`0 < |I|+A`) and does not over-fill (`|I|+A ≤ n`), and every synced thread is
  *parked* at `sync b n` (its program is headed by exactly that command) — note the
  non-emptiness rules out the unreachable degenerate state `⟨[], 0, some n⟩`
  (configured yet with nothing registered), which the `≤ n` bound alone permits; and
* if it is **unconfigured** (`s.B b = ⟨I, A, none⟩`), its synced list is empty and
  its arrived count is zero (ruling out a malformed `⟨I, A, none⟩` with threads registered).

Additionally `s.BlockInv` holds: the **syncer** lists are duplicate-free (a thread can be
a duplicate *arriver* but never a duplicate *syncer* — syncing disables it until the next
recycle), every synced thread is disabled, and no thread is synced at two barriers at once.
The count `n : ℕ+` is positive by construction, so — unlike the earlier `Nat`-count
formulation — no separate "valid counts" side condition is needed. Vacuously true for
`done`/`err`. -/
def Config.WF : Config → Prop
  | .run s T =>
      (∀ b I A n, s.B b = ⟨I, A, some n⟩ →
          I.length + A ≤ (n : Nat) ∧ (∀ i ∈ I, (T.prog i).head? = some (Cmd.sync b n)) ∧
            0 < I.length + A) ∧
      (∀ b I A, s.B b = ⟨I, A, none⟩ → I = [] ∧ A = 0) ∧
      s.BlockInv
  | .done _ => True
  | .err _ => True

/-- `WF` holds at the initial configuration: no barrier is configured, so the
configured-barrier condition is vacuous and every barrier is the empty unconfigured
state. -/
theorem WF_initial {T : CTA} : (Config.run State.initial T).WF := by
  refine ⟨fun b I A n hB => ?_, fun b I A hB => ?_, State.BlockInv.initial⟩
  · simp [State.initial, BarrierState.unconfigured] at hB
  · simp only [State.initial, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
    exact ⟨hB.1.symm, hB.2.1.symm⟩

/-- A command in a tail/`drop` of a program was in the program. -/
theorem mem_of_mem_drop {α} {a : α} {l : List α} {d : Nat} (h : a ∈ l.drop d) : a ∈ l :=
  List.mem_of_mem_drop h

/-- `WF` is preserved by every step — the main invariant-preservation lemma. All three
conjuncts (the configured-barrier and unconfigured-barrier conditions, and the blocking
invariant `s.BlockInv`) are re-established after each step; the last uniformly via
`blockInv_step`. -/
theorem CTAStep.WF_preserved {C C' : Config} (hstep : CTAStep C C') (hwf : C.WF) : C'.WF := by
  -- the blocking-invariant conjunct is preserved uniformly via `blockInv_step`
  have hBIpres : ∀ s', C'.state? = some s' → s'.BlockInv := by
    apply blockInv_step hstep
    obtain ⟨ss, TT, hCeq⟩ := hstep.source_run
    intro s hs
    rw [hCeq] at hwf hs
    simp only [Config.state?, Option.some.injEq] at hs
    subst hs
    exact hwf.2.2
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
    obtain ⟨hcond, hcondn, _⟩ := hwf
    generalize hpi : T.prog i = Pi at hth
    refine ⟨?_, ?_, hBIpres _ rfl⟩
    · cases hth with
      | read_noop =>
        intro b I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | write_noop =>
        intro b I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | arrive_configure he hb =>
        intro b I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · simp only [BarrierState.mk.injEq, Option.some.injEq] at hB
          have hpos := n.pos
          obtain ⟨rfl, rfl, rfl⟩ := hB
          exact ⟨by simp; omega, (fun i' hi' => by simp at hi'), by simp⟩
        · obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
          simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | arrive_register he hb hpos hlt =>
        intro b I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [BarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl⟩ := hB
          obtain ⟨_, hcpark, _⟩ := hcond _ _ _ _ hb
          subst hbq
          refine ⟨by omega, (fun i' hi' => ?_), by omega⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hcpark i' hi'; rw [hpi] at this; simp at this
          simp only [CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
          simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | sync_configure he hb =>
        intro b I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [BarrierState.mk.injEq, Option.some.injEq] at hB
          have hpos := n.pos
          obtain ⟨rfl, rfl, rfl⟩ := hB
          subst hbq
          refine ⟨by simp; omega, (fun i' hi' => ?_), by simp⟩
          simp only [List.mem_singleton] at hi'; subst hi'
          simp only [CTA.set, Function.update_self, List.head?_cons]
        · obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos⟩
          by_cases hne : i' = i
          · subst hne; simp only [CTA.set, Function.update_self]; rw [← hpi]; exact hpark _ hi'
          · simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | sync_block he hb hpos hlt =>
        intro b I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [BarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl⟩ := hB
          obtain ⟨_, hcpark, _⟩ := hcond _ _ _ _ hb
          subst hbq
          refine ⟨by simp only [List.length_cons]; omega, (fun i' hi' => ?_),
            by simp only [List.length_cons]; omega⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · simp only [CTA.set, Function.update_self, List.head?_cons]
          · by_cases hne : i' = i
            · subst hne; simp only [CTA.set, Function.update_self, List.head?_cons]
            · simp only [CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          by_cases hne : i' = i
          · subst hne; simp only [CTA.set, Function.update_self]; rw [← hpi]; exact hpark _ hi'
          · simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
    · cases hth with
      | read_noop => exact hcondn
      | write_noop => exact hcondn
      | arrive_configure he hb =>
        intro b I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn b I A hB
      | arrive_register he hb hpos hlt =>
        intro b I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn b I A hB
      | sync_configure he hb =>
        intro b I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn b I A hB
      | sync_block he hb hpos hlt =>
        intro b I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn b I A hB
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    obtain ⟨hcond, hcondn, _⟩ := hwf
    refine ⟨?_, ?_, hBIpres _ rfl⟩
    · intro b I A n hB
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
        exact absurd hB.2.2 (by simp)
      · simp only [Function.update_of_ne hbb] at hB
        obtain ⟨hle, hpk, hpos⟩ := hcond b I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hni : i' ∉ I₀ := by
          intro hmem
          have h1 := hpark i' hmem
          have h2 := hpk i' hi'
          rw [h1] at h2; simp only [Option.some.injEq, Cmd.sync.injEq] at h2; exact hbb h2.1.symm
        simp only [CTA.wake, if_neg hni]; exact hpk i' hi'
    · intro b I A hB
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
        exact ⟨hB.1.symm, hB.2.1.symm⟩
      · simp only [Function.update_of_ne hbb] at hB; exact hcondn b I A hB
  | @done s T hdone _ => trivial
  | @error s T i P' _ hth => trivial

/-- `WF` propagates along a chain from a well-formed head to every configuration. -/
theorem WF_chain : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → C₀.WF → ∀ C ∈ τ, C.WF := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead _ _ _; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hwf C hC
    rw [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hwf
    | cons b t' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hwf
      · exact ih hbt rfl (hab.WF_preserved hwf) C hC'

/-- A stuck `run` configuration (well-formed) has a thread headed by a
synchronization command — a thread parked at a `sync`, or one about to register. -/
theorem stuck_has_sync_head {s : State} {T : CTA}
    (hwf : (Config.run s T).WF)
    (hstuck : Config.Stuck (Config.run s T)) :
    ∃ t cmd c b, T.prog t = cmd :: c ∧ cmd.barrier? = some b := by
  by_contra hcon
  push Not at hcon
  -- No barrier is left *full*: every barrier is unconfigured or strictly under-full.
  -- A full barrier would either let `recycle` fire (its synced list empty, or its
  -- parked threads are `sync`-headed — both contradict stuckness/`hcon`).
  have hbar : ∀ bb, s.B bb = BarrierState.unconfigured ∨
      ∃ I A n, s.B bb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
    intro bb
    obtain ⟨bI, bA, bcnt, hbc⟩ : ∃ bI bA bcnt, s.B bb = ⟨bI, bA, bcnt⟩ := ⟨_, _, _, rfl⟩
    cases bcnt with
    | none => obtain ⟨rfl, rfl⟩ := hwf.2.1 bb bI bA hbc; exact Or.inl hbc
    | some n =>
      obtain ⟨hle, hpark, _⟩ := hwf.1 bb bI bA n hbc
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr ⟨bI, bA, n, hbc, hlt⟩
      · exfalso
        cases bI with
        | nil => exact hstuck ⟨_, CTAStep.recycle hbc heq (by simp)⟩
        | cons i₀ rest =>
          have hpk := hpark i₀ (by simp)
          cases hp : T.prog i₀ with
          | nil => rw [hp] at hpk; simp at hpk
          | cons x t =>
            rw [hp] at hpk
            simp only [List.head?_cons, Option.some.injEq] at hpk
            exact hcon i₀ x t bb hp (by rw [hpk]; rfl)
  -- Since no barrier is full, the `done` rule's premise `hnofull` holds.
  have hnofull : ∀ b I A n, s.B b = ⟨I, A, some n⟩ → I.length + A < (n : Nat) := by
    intro b I A n hb
    rcases hbar b with hu | ⟨I', A', n', hb', hlt⟩
    · rw [hb] at hu; simp [BarrierState.unconfigured] at hu
    · rw [hb] at hb'
      simp only [BarrierState.mk.injEq, Option.some.injEq] at hb'
      obtain ⟨rfl, rfl, rfl⟩ := hb'
      exact hlt
  -- If the CTA is done, `done` fires; otherwise a thread is headed by a
  -- (non-barrier, by `hcon`) command, so `interleave` fires. Either contradicts
  -- stuckness.
  by_cases hd : CTA.IsDone T
  · exact hstuck ⟨_, CTAStep.done hd hnofull⟩
  · rw [CTA.IsDone] at hd
    push Not at hd
    obtain ⟨t₀, ht₀ids, ht₀ne⟩ := hd
    obtain ⟨cmd₀, c₀, hcmd₀⟩ := List.exists_cons_of_ne_nil ht₀ne
    have hbar0 : cmd₀.barrier? = none := by
      cases hb : cmd₀.barrier? with
      | none => rfl
      | some b => exact absurd hb (hcon t₀ cmd₀ c₀ b hcmd₀)
    apply hstuck
    cases cmd₀ with
    | read g =>
      exact ⟨_, CTAStep.interleave ht₀ids hbar (by rw [hcmd₀]; exact ThreadStep.read_noop)⟩
    | write g =>
      exact ⟨_, CTAStep.interleave ht₀ids hbar (by rw [hcmd₀]; exact ThreadStep.write_noop)⟩
    | sync b n => simp [Cmd.barrier?] at hbar0
    | arrive b n => simp [Cmd.barrier?] at hbar0

/-- A complete trace from a *well-formed* `run` configuration that ends in a deadlock
(a stuck `run` configuration) contains a synchronization command that never executes
— some thread is blocked at a `sync` that is never recycled. The well-formedness of
the start configuration (`hC₀wf`) propagates along the trace (`WF_chain`) to the stuck
last configuration, which then exposes a `sync`-headed thread
(`stuck_has_sync_head`). -/
theorem deadlock_has_unexec_sync {C₀ : Config} {τ : List Config} {s : State} {T : CTA}
    (hτ : IsCompleteTraceFrom C₀ τ) (hC₀wf : C₀.WF)
    (hlast : τ.getLast? = some (Config.run s T)) (hstuck : Config.Stuck (Config.run s T)) :
    ∃ η : ProgPoint,
      (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) ∧
      ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hwf := WF_chain hτ.1.subtrace hτ.2 hC₀wf _ (List.mem_of_mem_getLast? hlast)
  obtain ⟨t, cmd, c, b, hTprog, hbb⟩ := stuck_has_sync_head hwf hstuck
  exact unexec_sync_of_last hτ hlast (List.mem_of_mem_head? hτ.2) hTprog hbb

/- THE HELPER FUNCTIONS ARE DONE AND THE REAL THEOREMS ARE BELOW -/

/- ### IMPORTANT THEOREMs: Well Synchronized Configurations Terminate Cleanly -/

/-- Definition 6 (§4.1), the main correctness result, for an arbitrary *well-formed*
start configuration: every complete trace from a well-synchronized, well-formed `run`
configuration `(s₀, T₀)` ends in `done`.

The well-formedness hypothesis `hwf` is essential — without it a malformed barrier
state can deadlock with no `sync`-headed thread, and the conclusion fails. It holds
for free at the initial configuration (`WF_initial`), which gives the
`CTA.WellSynchronized` corollary below. The proof splits on the terminal last
configuration: `done` is the goal; `err` and deadlock each expose a never-executing
synchronization command (`err_has_unexec_sync` / `deadlock_has_unexec_sync`),
contradicting `wellSync_no_unexec_sync`. The deadlock case rests on the
well-formedness invariant `Config.WF` (`hwf` + `CTAStep.WF_preserved` + `WF_chain`)
specialized to the stuck last configuration (`stuck_has_sync_head`). -/
theorem Config.WellSynchronized.completeTrace_ends_done {s₀ : State} {T₀ : CTA}
    (h : (Config.run s₀ T₀).WellSynchronized)
    (hwf : (Config.run s₀ T₀).WF) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run s₀ T₀) τ) :
    ∃ s, τ.getLast? = some (Config.done s) := by
  obtain ⟨Cₙ, hlast, hcases⟩ := hτ.1.ends
  cases Cₙ with
  | done s => exact ⟨s, hlast⟩
  | err T' =>
    exfalso
    obtain ⟨η, hηsync, hηnoexec⟩ := err_has_unexec_sync hτ ⟨s₀, T₀, rfl⟩ hlast
    exact wellSync_no_unexec_sync h hτ hηsync hηnoexec
  | run s T' =>
    exfalso
    have hstuck : Config.Stuck (Config.run s T') := by
      rcases hcases with ⟨s', hd⟩ | ⟨T'', he⟩ | hs
      · exact Config.noConfusion hd
      · exact Config.noConfusion he
      · exact hs
    obtain ⟨η, hηsync, hηnoexec⟩ := deadlock_has_unexec_sync hτ hwf hlast hstuck
    exact wellSync_no_unexec_sync h hτ hηsync hηnoexec

/-- Definition 6 (§4.1) at the initial configuration: every complete trace of a
well-synchronized CTA ends in `done`. A corollary of the well-formed-configuration
version `Config.WellSynchronized.completeTrace_ends_done`, since `WF` holds
initially. -/
theorem CTA.WellSynchronized.completeTrace_ends_done {T : CTA}
    (h : T.WellSynchronized) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ) :
    ∃ s, τ.getLast? = some (Config.done s) :=
  Config.WellSynchronized.completeTrace_ends_done h WF_initial hτ

/-- A well-synchronized CTA has no complete trace from `initial` ending in the error
state `err`. -/
theorem CTA.WellSynchronized.completeTrace_not_ends_err {T : CTA}
    (h : T.WellSynchronized) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ) :
    ∀ T', τ.getLast? ≠ some (Config.err T') := by
  intro T' hcon
  obtain ⟨s, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done h hτ
  rw [hdone] at hcon
  simp at hcon

/-- A well-synchronized CTA has no deadlocking complete trace from `initial` (one
whose last configuration is a stuck `run`). -/
theorem CTA.WellSynchronized.completeTrace_not_deadlock {T : CTA}
    (h : T.WellSynchronized) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ) :
    ∀ s T', τ.getLast? ≠ some (Config.run s T') := by
  intro s T' hcon
  obtain ⟨s', hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done h hτ
  rw [hdone] at hcon
  simp at hcon

/-! ### IMPORTANT THEOREM: Existence of a complete trace (strong normalization)

/- BEGIN HELPER METHODS GENERATED BY CLAUDE TO PROVE THE THEOREM -/

`exists_completeTrace_ends_done` asks for *one* complete trace from the initial
configuration that ends in `done`. This factors into two independent facts:

* every complete trace ends in `done` — already proved (`completeTrace_ends_done`),
  the only place well-synchronization is used; and
* *some* complete trace exists — a pure **termination** fact that holds for any
  CTA, independent of well-synchronization, because the Weft machine strongly
  normalizes (programs are finite straight-line code).

We prove termination with the measure
`μ(s, T) = 3·(remaining commands) + 2·(enabled threads) + (configured barriers) + 1`
(`Config.cfgMeasure`), which strictly decreases on every `CTAStep`:

* `read`/`write`/`arrive` drop a command (`−3`);
* a `sync` parks — no command drops, but the thread is disabled (`−2`, possibly
  `+1` for newly configuring its barrier);
* `recycle` drops the parked `sync`s and re-enables their threads, and clears one
  barrier — the command/enable terms net out and the barrier term gives `−1`,
  covering even the "all-arrivals" recycle that drops nothing.

The configured-barrier term is counted within a fixed finite support `S`; the
invariant `Config.barriersWithin S` (every configured/mentioned barrier is in `S`)
keeps that count meaningful and is preserved by every step. -/

/-- Total number of remaining commands across all threads of a CTA. -/
def CTA.numCmds (T : CTA) : Nat := ∑ i ∈ T.ids, (T.prog i).length

/-- Number of currently enabled threads. -/
def State.numEnabled (s : State) (T : CTA) : Nat := (T.ids.filter (fun i => s.E i)).card

/-- Number of configured barriers within the finite support `S`. -/
def State.numConfigured (s : State) (S : Finset Barrier) : Nat :=
  (S.filter (fun b => (s.B b).count.isSome)).card

/-- The strong-normalization measure (see the section doc). `done`/`err` are
terminal; the `+1` on `run` keeps `μ(run) ≥ 1 > 0 = μ(done) = μ(err)`, so the
`done`/`error` steps strictly decrease it too. -/
def Config.cfgMeasure (S : Finset Barrier) : Config → Nat
  | .run s T => 3 * T.numCmds + 2 * s.numEnabled T + s.numConfigured S + 1
  | .done _ => 0
  | .err _ => 0

/-- The finite set of barriers mentioned by a CTA's programs — a support that
contains every barrier that could ever be configured along an execution. -/
def CTA.barrierSet (T : CTA) : Finset Barrier :=
  T.ids.biUnion (fun i => ((T.prog i).filterMap Cmd.barrier?).toFinset)

/-- Support invariant: every configured barrier, and every barrier mentioned by a
thread's remaining program, lies in `S`. Vacuous for `done`/`err`. -/
def Config.barriersWithin (S : Finset Barrier) : Config → Prop
  | .run s T =>
      (∀ b, (s.B b).count.isSome → b ∈ S) ∧
      (∀ i, ∀ c ∈ T.prog i, ∀ b, c.barrier? = some b → b ∈ S)
  | _ => True

/-- The support invariant holds at the initial configuration with `S = T.barrierSet`:
no barrier is configured, and every mentioned barrier is in `barrierSet` by
definition. -/
theorem barriersWithin_initial {T : CTA} :
    (Config.run State.initial T).barriersWithin T.barrierSet := by
  refine ⟨fun b hb => ?_, fun i c hc b hbc => ?_⟩
  · simp [State.initial, BarrierState.unconfigured] at hb
  · have hi : i ∈ T.ids := by
      by_contra hni; rw [T.nil_outside_ids i hni] at hc; simp at hc
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨c, hc, hbc⟩

/-- Updating one thread's program changes the command count by the length
difference (stated additively to avoid `Nat` subtraction). -/
theorem numCmds_set {T : CTA} {i : ThreadId} (hi : i ∈ T.ids) (P' : Prog) :
    (T.set i hi P').numCmds + (T.prog i).length = T.numCmds + P'.length := by
  have hset : ∀ j, ((T.set i hi P').prog j).length
      = Function.update (fun k => (T.prog k).length) i P'.length j := by
    intro j
    by_cases h : j = i
    · subst h; simp [CTA.set]
    · simp [CTA.set, Function.update_of_ne h]
  change (∑ j ∈ T.ids, ((T.set i hi P').prog j).length) + (T.prog i).length
      = (∑ j ∈ T.ids, (T.prog j).length) + P'.length
  rw [Finset.sum_congr rfl (fun j _ => hset j), Finset.sum_update_of_mem hi,
      ← Finset.erase_eq, ← Finset.add_sum_erase T.ids (fun k => (T.prog k).length) hi]
  omega

/-- Disabling an enabled thread `i` drops the enabled count by one. -/
theorem numEnabled_update_false {s : State} {T : CTA} {i : ThreadId}
    (hi : i ∈ T.ids) (he : s.E i = true) :
    (T.ids.filter (fun j => Function.update s.E i false j = true)).card + 1
      = (T.ids.filter (fun j => s.E j = true)).card := by
  have he' : i ∈ T.ids.filter (fun j => s.E j = true) := Finset.mem_filter.mpr ⟨hi, he⟩
  rw [show T.ids.filter (fun j => Function.update s.E i false j = true)
        = (T.ids.filter (fun j => s.E j = true)).erase i from ?_]
  · rw [Finset.card_erase_of_mem he']
    have := Finset.card_pos.mpr ⟨i, he'⟩
    omega
  · ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Function.update_apply]
    by_cases hx : x = i <;> simp [hx]

/-- Un-configuring a barrier `b₀ ∈ S` drops the configured count by one. -/
theorem numConfigured_unconfigure {s : State} {S : Finset Barrier} {b₀ : Barrier}
    (hb0S : b₀ ∈ S) (hc0 : (s.B b₀).count.isSome = true) :
    (S.filter (fun b =>
        ((Function.update s.B b₀ BarrierState.unconfigured) b).count.isSome = true)).card + 1
      = (S.filter (fun b => (s.B b).count.isSome = true)).card := by
  have hb0 : b₀ ∈ S.filter (fun b => (s.B b).count.isSome = true) :=
    Finset.mem_filter.mpr ⟨hb0S, hc0⟩
  rw [show S.filter (fun b =>
        ((Function.update s.B b₀ BarrierState.unconfigured) b).count.isSome = true)
        = (S.filter (fun b => (s.B b).count.isSome = true)).erase b₀ from ?_]
  · rw [Finset.card_erase_of_mem hb0]
    have := Finset.card_pos.mpr ⟨b₀, hb0⟩
    omega
  · ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Function.update_apply]
    by_cases hb : b = b₀
    · subst hb; simp [BarrierState.unconfigured]
    · simp [hb]

/-- Configuring a barrier raises the configured count by at most one. -/
theorem numConfigured_configure_le {s : State} {S : Finset Barrier} {b₀ : Barrier}
    {v : BarrierState} :
    (S.filter (fun b => ((Function.update s.B b₀ v) b).count.isSome = true)).card
      ≤ (S.filter (fun b => (s.B b).count.isSome = true)).card + 1 := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le b₀ _)
  intro b hb
  rw [Finset.mem_filter, Function.update_apply] at hb
  obtain ⟨hbS, hbc⟩ := hb
  by_cases h : b = b₀
  · subst h; exact Finset.mem_insert_self _ _
  · rw [if_neg h] at hbc
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hbS, hbc⟩)

/-- Re-registering at an already-configured barrier leaves the configured count
unchanged. -/
theorem numConfigured_reconfigure {s : State} {S : Finset Barrier} {b₀ : Barrier}
    {v : BarrierState} (hv : v.count.isSome = true) (hold : (s.B b₀).count.isSome = true) :
    (S.filter (fun b => ((Function.update s.B b₀ v) b).count.isSome = true)).card
      = (S.filter (fun b => (s.B b).count.isSome = true)).card := by
  congr 1
  ext b
  simp only [Finset.mem_filter, Function.update_apply]
  by_cases h : b = b₀ <;> simp [h, hv, hold]

/-- Waking the threads `I` (each parked at a `sync`, hence with a nonempty program)
drops the command count by one per woken in-domain thread. -/
theorem numCmds_wake {T : CTA} {I : List ThreadId} {b₀ : Barrier} {n : ℕ+}
    (hpark : ∀ i ∈ I, (T.prog i).head? = some (Cmd.sync b₀ n)) :
    T.numCmds = (T.wake I).numCmds + (T.ids.filter (· ∈ I)).card := by
  have key : ∀ j ∈ T.ids, (T.prog j).length
      = ((T.wake I).prog j).length + (if j ∈ I then 1 else 0) := by
    intro j _
    simp only [CTA.wake]
    by_cases h : j ∈ I
    · have hne : (T.prog j) ≠ [] := by
        have hp := hpark j h; intro hnil; rw [hnil] at hp; simp at hp
      obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
      rw [if_pos h, if_pos h, hxs]; simp
    · rw [if_neg h, if_neg h]; simp
  change (∑ j ∈ T.ids, (T.prog j).length)
      = (∑ j ∈ T.ids, ((T.wake I).prog j).length) + (T.ids.filter (· ∈ I)).card
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.card_filter]

/-- Re-enabling the threads `I` raises the enabled count by at most the number of
in-domain woken threads. -/
theorem numEnabled_updateMapOn_le {s : State} {T : CTA} {I : List ThreadId} :
    (T.ids.filter (fun j => updateMapOn s.E I true j = true)).card
      ≤ (T.ids.filter (fun j => s.E j = true)).card + (T.ids.filter (· ∈ I)).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro j hj
  rw [Finset.mem_filter, updateMapOn_apply] at hj
  obtain ⟨hjids, hjE⟩ := hj
  by_cases h : j ∈ I
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjids, h⟩)
  · rw [if_neg h] at hjE
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjids, hjE⟩)

/-- Every `CTAStep` strictly decreases the measure: the machine strongly
normalizes. See the section doc for the per-rule accounting. -/
theorem step_decreases (S : Finset Barrier) {C C' : Config}
    (hstep : CTAStep C C') (hinv : C.barriersWithin S) :
    C'.cfgMeasure S < C.cfgMeasure S := by
  cases hstep with
  | @done s T hdone _ => simp only [Config.cfgMeasure]; omega
  | @error s T i P' _ hth => simp only [Config.cfgMeasure]; omega
  | @interleave s s' T i P' hi hbar hth =>
    obtain ⟨hcfg, hmen⟩ := hinv
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : s.numEnabled (T.set i hi P') = s.numEnabled T := rfl
      simp only [Config.cfgMeasure, hE]; omega
    | write_noop =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : s.numEnabled (T.set i hi P') = s.numEnabled T := rfl
      simp only [Config.cfgMeasure, hE]; omega
    | @arrive_configure _ _ b₀ n _ he hb0 =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with B := Function.update s.B b₀ ⟨[], 1, some n⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hCf : ({s with B := Function.update s.B b₀ ⟨[], 1, some n⟩} : State).numConfigured S
          ≤ s.numConfigured S + 1 := numConfigured_configure_le
      simp only [Config.cfgMeasure, hE]; omega
    | @arrive_register _ _ b₀ n _ I A he hb0 hpos hlt =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with B := Function.update s.B b₀ ⟨I, A + 1, some n⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hCf : ({s with B := Function.update s.B b₀ ⟨I, A + 1, some n⟩} : State).numConfigured S
          = s.numConfigured S := numConfigured_reconfigure rfl (by rw [hb0]; rfl)
      simp only [Config.cfgMeasure, hE, hCf]; omega
    | @sync_configure _ _ b₀ n c he hb0 =>
      set s' : State := ⟨Function.update s.E i false, Function.update s.B b₀ ⟨[i], 0, some n⟩⟩
      have h1 := numCmds_set hi (Cmd.sync b₀ n :: c)
      have h2 : (T.prog i).length = (Cmd.sync b₀ n :: c).length := by rw [hpi]
      have hE : s'.numEnabled (T.set i hi (Cmd.sync b₀ n :: c)) + 1 = s.numEnabled T :=
        numEnabled_update_false hi he
      have hCf : s'.numConfigured S ≤ s.numConfigured S + 1 := numConfigured_configure_le
      simp only [Config.cfgMeasure]; omega
    | @sync_block _ _ b₀ n c I A he hb0 hpos hlt =>
      set s' : State := ⟨Function.update s.E i false, Function.update s.B b₀ ⟨i :: I, A, some n⟩⟩
      have h1 := numCmds_set hi (Cmd.sync b₀ n :: c)
      have h2 : (T.prog i).length = (Cmd.sync b₀ n :: c).length := by rw [hpi]
      have hE : s'.numEnabled (T.set i hi (Cmd.sync b₀ n :: c)) + 1 = s.numEnabled T :=
        numEnabled_update_false hi he
      have hCf : s'.numConfigured S = s.numConfigured S :=
        numConfigured_reconfigure rfl (by rw [hb0]; rfl)
      simp only [Config.cfgMeasure, hCf]; omega
  | @recycle s T b₀ I A n hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    set s' : State := ⟨updateMapOn s.E I true, Function.update s.B b₀ BarrierState.unconfigured⟩
    have hb0S : b₀ ∈ S := hcfg b₀ (by rw [hb0]; rfl)
    have hC : T.numCmds = (T.wake I).numCmds + (T.ids.filter (· ∈ I)).card := numCmds_wake hpark
    have hE : s'.numEnabled (T.wake I) ≤ s.numEnabled T + (T.ids.filter (· ∈ I)).card :=
      numEnabled_updateMapOn_le
    have hCf : s'.numConfigured S + 1 = s.numConfigured S :=
      numConfigured_unconfigure hb0S (by rw [hb0]; rfl)
    simp only [Config.cfgMeasure]; omega

/-- The support invariant `barriersWithin S` is preserved by every step. The
"mentioned" part follows from `progOf_drop` (programs only shrink); the "configured"
part because a newly configured barrier is the (mentioned) barrier of the executed
command, and `recycle` only *un*configures. -/
theorem inv_preserved (S : Finset Barrier) {C C' : Config}
    (hstep : CTAStep C C') (hinv : C.barriersWithin S) :
    C'.barriersWithin S := by
  cases hstep with
  | @done s T hdone _ => trivial
  | @error s T i P' _ hth => trivial
  | @interleave s s' T i P' hi hbar hth =>
    obtain ⟨hcfg, hmen⟩ := hinv
    have hmen' : ∀ j, ∀ c ∈ (T.set i hi P').prog j, ∀ b, c.barrier? = some b → b ∈ S := by
      intro j c hc b hbc
      obtain ⟨d, hd⟩ := (CTAStep.interleave hi hbar hth).progOf_drop j
      simp only [Config.progOf] at hd
      rw [hd] at hc
      exact hmen j c (mem_of_mem_drop hc) b hbc
    refine ⟨fun b hb => ?_, hmen'⟩
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hcfg b hb
    | write_noop => exact hcfg b hb
    | @arrive_configure _ _ b₀ _ _ he hbar0 =>
      simp only [Function.update_apply] at hb
      split at hb
      · rename_i heq; rw [heq]; exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) b₀ rfl
      · exact hcfg b hb
    | @arrive_register _ _ b₀ _ _ _ _ he hb0 hpos hlt =>
      simp only [Function.update_apply] at hb
      split at hb
      · rename_i heq; rw [heq]; exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) b₀ rfl
      · exact hcfg b hb
    | @sync_configure _ _ b₀ _ _ he hbar0 =>
      simp only [Function.update_apply] at hb
      split at hb
      · rename_i heq; rw [heq]; exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) b₀ rfl
      · exact hcfg b hb
    | @sync_block _ _ b₀ _ _ _ _ he hb0 hpos hlt =>
      simp only [Function.update_apply] at hb
      split at hb
      · rename_i heq; rw [heq]; exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) b₀ rfl
      · exact hcfg b hb
  | @recycle s T b₀ I A n hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    have hmen' : ∀ j, ∀ c ∈ (T.wake I).prog j, ∀ b, c.barrier? = some b → b ∈ S := by
      intro j c hc b hbc
      obtain ⟨d, hd⟩ := (CTAStep.recycle hb0 hfull hpark).progOf_drop j
      simp only [Config.progOf] at hd
      rw [hd] at hc
      exact hmen j c (mem_of_mem_drop hc) b hbc
    refine ⟨fun b hb => ?_, hmen'⟩
    simp only [Function.update_apply] at hb
    split at hb
    · simp [BarrierState.unconfigured] at hb
    · exact hcfg b hb

/-- Strong normalization yields a complete trace from *every* configuration: run
the machine to a stuck (terminal) state. By well-founded recursion on the measure
`cfgMeasure S`, with the support invariant `barriersWithin S` carried along. -/
theorem exists_completeTrace (S : Finset Barrier) (C : Config) (hinv : C.barriersWithin S) :
    ∃ τ, IsCompleteTraceFrom C τ := by
  suffices H : ∀ n C, C.barriersWithin S → C.cfgMeasure S = n →
      ∃ τ, IsCompleteTraceFrom C τ from H _ C hinv rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hinv hn
    by_cases hstuck : Config.Stuck C
    · exact ⟨[C], ⟨List.isChain_singleton C, C, by simp, Or.inr (Or.inr hstuck)⟩, by simp⟩
    · simp only [Config.Stuck, not_not] at hstuck
      obtain ⟨C', hCC'⟩ := hstuck
      have hdec : C'.cfgMeasure S < n := hn ▸ step_decreases S hCC' hinv
      obtain ⟨τ', hτ'⟩ := ih _ hdec C' (inv_preserved S hCC' hinv) rfl
      have hτ'ne : τ' ≠ [] := by
        intro h; rw [h] at hτ'; simp [IsCompleteTraceFrom] at hτ'
      refine ⟨C :: τ', ⟨?_, ?_⟩, by simp⟩
      · change List.IsChain CTAStep (C :: τ')
        rw [List.isChain_cons]
        refine ⟨fun y hy => ?_, hτ'.1.subtrace⟩
        rw [hτ'.2, Option.mem_some_iff] at hy; exact hy ▸ hCC'
      · obtain ⟨Cₙ, hlast, hcase⟩ := hτ'.1.ends
        exact ⟨Cₙ, by rw [List.getLast?_cons_of_ne_nil hτ'ne]; exact hlast, hcase⟩

/- END HELPER METHODS GENERATED BY CLAUDE TO PROVE THE THEOREM -/

/--
THIS IS A TOP-LEVEL THEOREM.
A well-synchronized CTA has at least one complete trace from the initial
configuration `(I, T)`, and every such trace ends in `done`
(`completeTrace_ends_done`). Hence there is a complete trace that ends in `done`:
the CTA can make progress and run to successful completion. -/
theorem CTA.WellSynchronized.exists_completeTrace_ends_done {T : CTA}
    (h : T.WellSynchronized) :
    ∃ τ : List Config, IsCompleteTraceFrom (Config.run State.initial T) τ ∧
      ∃ s, τ.getLast? = some (Config.done s) := by
  obtain ⟨τ, hτ⟩ :=
    exists_completeTrace T.barrierSet (Config.run State.initial T) barriersWithin_initial
  exact ⟨τ, hτ, completeTrace_ends_done h hτ⟩

/--
THIS IS A TOP-LEVEL THEOREM.
A well-synchronized CTA has at least one trace that *successfully runs the initial
configuration to completion* (`IsSuccessfulTraceFrom`): a complete trace from
`(I, T)` that ends in `done`. Restated form of `exists_completeTrace_ends_done`
through the bundled `IsSuccessfulTraceFrom` predicate. -/
theorem CTA.WellSynchronized.exists_successfulTrace {T : CTA} (h : T.WellSynchronized) :
    ∃ τ : List Config, IsSuccessfulTraceFrom (Config.run State.initial T) τ := by
  obtain ⟨τ, hτ, hdone⟩ := h.exists_completeTrace_ends_done
  exact ⟨τ, hτ, hdone⟩

/-- A CTA with no instructions on any thread is trivially well-synchronized: it has no
synchronization commands, so the condition holds vacuously. -/
theorem CTA.WellSynchronized.of_empty {P : CTA} (hP : ∀ t, P.prog t = []) :
    P.WellSynchronized := by
  refine ⟨⟨State.initial, P, rfl⟩, fun _ _ _ _ η hη => ?_⟩
  obtain ⟨b, hb⟩ := hη
  have hnone : η.cmd (Config.run State.initial P) = none := by
    change (P.prog η.thread)[η.idx]? = none
    rw [hP η.thread]; rfl
  rw [hnone] at hb
  simp at hb

end Weft
