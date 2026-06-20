/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Traces

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
`n` threads have registered (`|I| + |A| = n`) — the situation in which
`CTAStep.recycle` fires. -/
def BarrierState.isFull (β : BarrierState) : Bool :=
  match β.count with
  | some n => β.synced.length + β.arrived.length == (n : Nat)
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
  | @done s T hdone =>
      exact ⟨(T.prog t).length, by simp [Config.progOf, List.drop_length]⟩
  | @error s T i P' hstep =>
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
  | @error s _ i P' hth =>
    generalize hp : T.prog i = P at hth
    cases hth with
    | sync_err_full _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | sync_err_count _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | arrive_err_full _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
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

/-- The well-formedness invariant. For a `run` configuration: for every configured
barrier `b = (I, A, n)`, registration does not over-fill (`|I|+|A| ≤ n`) and every
synced thread is *parked* at `sync b n` (its program is headed by exactly that
command). The count `n : ℕ+` is positive by construction, so — unlike the earlier
`Nat`-count formulation — no separate "valid counts" side condition is needed.
Vacuously true for `done`/`err`. -/
def Config.WF : Config → Prop
  | .run s T =>
      ∀ b I A n, s.B b = ⟨I, A, some n⟩ →
        I.length + A.length ≤ (n : Nat) ∧ ∀ i ∈ I, (T.prog i).head? = some (Cmd.sync b n)
  | .done _ => True
  | .err _ => True

/-- `WF` holds at the initial configuration: no barrier is configured, so the
barrier condition is vacuous. -/
theorem WF_initial {T : CTA} : (Config.run State.initial T).WF := by
  intro b I A n hB
  simp [State.initial, BarrierState.unconfigured] at hB

/-- A command in a tail/`drop` of a program was in the program. -/
theorem mem_of_mem_drop {α} {a : α} {l : List α} {d : Nat} (h : a ∈ l.drop d) : a ∈ l :=
  List.mem_of_mem_drop h

/-- `WF` is preserved by every step — the main invariant-preservation lemma. -/
theorem CTAStep.WF_preserved {C C' : Config} (hstep : CTAStep C C') (hwf : C.WF) : C'.WF := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
    have hcond := hwf
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop =>
      intro b I A n hB
      obtain ⟨hle, hpark⟩ := hcond b I A n hB
      refine ⟨hle, fun i' hi' => ?_⟩
      have hne : i' ≠ i := by
        rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
      simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
    | write_noop =>
      intro b I A n hB
      obtain ⟨hle, hpark⟩ := hcond b I A n hB
      refine ⟨hle, fun i' hi' => ?_⟩
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
        exact ⟨by simp; omega, fun i' hi' => by simp at hi'⟩
      · obtain ⟨hle, hpark⟩ := hcond b I A n hB
        refine ⟨hle, fun i' hi' => ?_⟩
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
        obtain ⟨_, hcpark⟩ := hcond _ _ _ _ hb
        subst hbq
        refine ⟨by simp only [List.length_cons]; omega, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hcpark i' hi'; rw [hpi] at this; simp at this
        simp only [CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
      · obtain ⟨hle, hpark⟩ := hcond b I A n hB
        refine ⟨hle, fun i' hi' => ?_⟩
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
        refine ⟨by simp; omega, fun i' hi' => ?_⟩
        simp only [List.mem_singleton] at hi'; subst hi'
        simp only [CTA.set, Function.update_self, List.head?_cons]
      · obtain ⟨hle, hpark⟩ := hcond b I A n hB
        refine ⟨hle, fun i' hi' => ?_⟩
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
        obtain ⟨_, hcpark⟩ := hcond _ _ _ _ hb
        subst hbq
        refine ⟨by simp only [List.length_cons]; omega, fun i' hi' => ?_⟩
        rcases List.mem_cons.mp hi' with rfl | hi'
        · simp only [CTA.set, Function.update_self, List.head?_cons]
        · by_cases hne : i' = i
          · subst hne; simp only [CTA.set, Function.update_self, List.head?_cons]
          · simp only [CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
      · obtain ⟨hle, hpark⟩ := hcond b I A n hB
        refine ⟨hle, fun i' hi' => ?_⟩
        by_cases hne : i' = i
        · subst hne; simp only [CTA.set, Function.update_self]; rw [← hpi]; exact hpark _ hi'
        · simp only [CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    have hcond := hwf
    intro b I A n hB
    by_cases hbb : b = b₀
    · subst hbb
      simp only [Function.update_self, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
      exact absurd hB.2.2 (by simp)
    · simp only [Function.update_of_ne hbb] at hB
      obtain ⟨hle, hpk⟩ := hcond b I A n hB
      refine ⟨hle, fun i' hi' => ?_⟩
      have hni : i' ∉ I₀ := by
        intro hmem
        have h1 := hpark i' hmem
        have h2 := hpk i' hi'
        rw [h1] at h2; simp only [Option.some.injEq, Cmd.sync.injEq] at h2; exact hbb h2.1.symm
      simp only [CTA.wake, if_neg hni]; exact hpk i' hi'
  | @done s T hdone => trivial
  | @error s T i P' hth => trivial

/-- Auxiliary invariant: an *unconfigured* barrier (count `none`) has empty lists.
This rules out malformed `⟨I, A, none⟩` with nonempty `I`/`A`. -/
def Config.WFn : Config → Prop
  | .run s _ => ∀ b I A, s.B b = ⟨I, A, none⟩ → I = [] ∧ A = []
  | _ => True

theorem WFn_initial {T : CTA} : (Config.run State.initial T).WFn := by
  intro b I A hB
  simp only [State.initial, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
  exact ⟨hB.1.symm, hB.2.1.symm⟩

theorem CTAStep.WFn_preserved {C C' : Config} (hstep : CTAStep C C') (hwfn : C.WFn) : C'.WFn := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hwfn
    | write_noop => exact hwfn
    | arrive_configure he hb =>
      intro b I A hB; simp only [Function.update_apply] at hB; split at hB
      · simp at hB
      · exact hwfn b I A hB
    | arrive_register he hb hpos hlt =>
      intro b I A hB; simp only [Function.update_apply] at hB; split at hB
      · simp at hB
      · exact hwfn b I A hB
    | sync_configure he hb =>
      intro b I A hB; simp only [Function.update_apply] at hB; split at hB
      · simp at hB
      · exact hwfn b I A hB
    | sync_block he hb hpos hlt =>
      intro b I A hB; simp only [Function.update_apply] at hB; split at hB
      · simp at hB
      · exact hwfn b I A hB
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    intro b I A hB
    by_cases hbb : b = b₀
    · subst hbb
      simp only [Function.update_self, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
      exact ⟨hB.1.symm, hB.2.1.symm⟩
    · simp only [Function.update_of_ne hbb] at hB; exact hwfn b I A hB
  | @done s T hdone => trivial
  | @error s T i P' hth => trivial

/-- `WF` and `WFn` propagate along a chain from a well-formed head to every config. -/
theorem WF_chain : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → C₀.WF → C₀.WFn → ∀ C ∈ τ, C.WF ∧ C.WFn := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead _ _ _ _; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hwf hwfn C hC
    rw [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact ⟨hwf, hwfn⟩
    | cons b t' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact ⟨hwf, hwfn⟩
      · exact ih hbt rfl (hab.WF_preserved hwf) (hab.WFn_preserved hwfn) C hC'

/-- A stuck `run` configuration (well-formed) has a thread headed by a
synchronization command — a thread parked at a `sync`, or one about to register. -/
theorem stuck_has_sync_head {s : State} {T : CTA}
    (hwf : (Config.run s T).WF) (hwfn : (Config.run s T).WFn)
    (hstuck : Config.Stuck (Config.run s T)) :
    ∃ t cmd c b, T.prog t = cmd :: c ∧ cmd.barrier? = some b := by
  have hcond := hwf
  have hnd : ¬ CTA.IsDone T := fun hd => hstuck ⟨_, CTAStep.done hd⟩
  rw [CTA.IsDone] at hnd
  push Not at hnd
  obtain ⟨t₀, ht₀ids, ht₀ne⟩ := hnd
  obtain ⟨cmd₀, c₀, hcmd₀⟩ := List.exists_cons_of_ne_nil ht₀ne
  by_contra hcon
  push Not at hcon
  have hbar0 : cmd₀.barrier? = none := by
    cases hb : cmd₀.barrier? with
    | none => rfl
    | some b => exact absurd hb (hcon t₀ cmd₀ c₀ b hcmd₀)
  by_cases hbar : ∀ bb, s.B bb = BarrierState.unconfigured ∨
      ∃ I A n, s.B bb = ⟨I, A, some n⟩ ∧ I.length + A.length < (n : Nat)
  · apply hstuck
    cases cmd₀ with
    | read g =>
      exact ⟨_, CTAStep.interleave ht₀ids hbar (by rw [hcmd₀]; exact ThreadStep.read_noop)⟩
    | write g =>
      exact ⟨_, CTAStep.interleave ht₀ids hbar (by rw [hcmd₀]; exact ThreadStep.write_noop)⟩
    | sync b n => simp [Cmd.barrier?] at hbar0
    | arrive b n => simp [Cmd.barrier?] at hbar0
  · push Not at hbar
    obtain ⟨bb, hb1, hb2⟩ := hbar
    obtain ⟨bI, bA, bcnt, hbc⟩ : ∃ bI bA bcnt, s.B bb = ⟨bI, bA, bcnt⟩ := ⟨_, _, _, rfl⟩
    cases bcnt with
    | none => obtain ⟨rfl, rfl⟩ := hwfn bb bI bA hbc; exact hb1 hbc
    | some n =>
      obtain ⟨hle, hpark⟩ := hcond bb bI bA n hbc
      have hfull : bI.length + bA.length = (n : Nat) := by have := hb2 bI bA n hbc; omega
      cases bI with
      | nil => exact hstuck ⟨_, CTAStep.recycle hbc hfull (by simp)⟩
      | cons i₀ rest =>
        have hpk := hpark i₀ (by simp)
        cases hp : T.prog i₀ with
        | nil => rw [hp] at hpk; simp at hpk
        | cons x t =>
          rw [hp] at hpk
          simp only [List.head?_cons, Option.some.injEq] at hpk
          exact hcon i₀ x t bb hp (by rw [hpk]; rfl)

/-- A complete trace from the initial configuration that ends in a deadlock (a
stuck `run` configuration) contains a synchronization command that never executes
— some thread is blocked at a `sync` that is never recycled. -/
theorem deadlock_has_unexec_sync {T₀ : CTA} {τ : List Config} {s : State} {T : CTA}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T₀) τ)
    (hlast : τ.getLast? = some (Config.run s T)) (hstuck : Config.Stuck (Config.run s T)) :
    ∃ η : ProgPoint,
      (∃ b, (η.cmd (Config.run State.initial T₀)).bind Cmd.barrier? = some b) ∧
      ¬ ∃ m, IsTimeOf (Config.run State.initial T₀) τ η m := by
  obtain ⟨hwf, hwfn⟩ :=
    WF_chain hτ.1.subtrace hτ.2 WF_initial WFn_initial _ (List.mem_of_mem_getLast? hlast)
  obtain ⟨t, cmd, c, b, hTprog, hbb⟩ := stuck_has_sync_head hwf hwfn hstuck
  exact unexec_sync_of_last hτ hlast (List.mem_of_mem_head? hτ.2) hTprog hbb

/- THE HELPER FUNCTIONS ARE DONE AND THE REAL THEOREMS ARE BELOW -/

/-- Definition 6 (§4.1), the main correctness result: every execution of a
well-synchronized CTA — i.e. every complete trace from the initial configuration
`(I, T)` — ends in `done`.

Restricted to the initial configuration: the unrestricted statement over arbitrary
`run` configurations is *false* — a malformed barrier state can deadlock with no
`sync`-headed thread. (Positive thread counts are no longer a side condition: every
`sync`/`arrive` carries a positive count `n : ℕ+` by construction.) The proof splits
on the terminal last configuration: `done` is the goal; `err` and deadlock each
expose a never-executing synchronization command (`err_has_unexec_sync` /
`deadlock_has_unexec_sync`), contradicting `wellSync_no_unexec_sync`. The deadlock
case rests on the well-formedness invariant `Config.WF`/`WFn` (`WF_initial` +
`CTAStep.WF_preserved` + `WF_chain`) specialized to the stuck last configuration
(`stuck_has_sync_head`). -/
theorem CTA.WellSynchronized.completeTrace_ends_done {T : CTA}
    (h : T.WellSynchronized) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ) :
    ∃ s, τ.getLast? = some (Config.done s) := by
  obtain ⟨Cₙ, hlast, hcases⟩ := hτ.1.ends
  cases Cₙ with
  | done s => exact ⟨s, hlast⟩
  | err T' =>
    exfalso
    obtain ⟨η, hηsync, hηnoexec⟩ := err_has_unexec_sync hτ ⟨State.initial, T, rfl⟩ hlast
    exact wellSync_no_unexec_sync h hτ hηsync hηnoexec
  | run s T' =>
    exfalso
    have hstuck : Config.Stuck (Config.run s T') := by
      rcases hcases with ⟨s', hd⟩ | ⟨T'', he⟩ | hs
      · exact Config.noConfusion hd
      · exact Config.noConfusion he
      · exact hs
    obtain ⟨η, hηsync, hηnoexec⟩ := deadlock_has_unexec_sync hτ hlast hstuck
    exact wellSync_no_unexec_sync h hτ hηsync hηnoexec

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

/-- A well-synchronized CTA has at least one complete trace from the initial
configuration `(I, T)`, and every such trace ends in `done`
(`completeTrace_ends_done`). Hence there is a complete trace that ends in `done`:
the CTA can make progress and run to successful completion. -/
theorem CTA.WellSynchronized.exists_completeTrace_ends_done {T : CTA}
    (h : T.WellSynchronized) :
    ∃ τ : List Config, IsCompleteTraceFrom (Config.run State.initial T) τ ∧
      ∃ s, τ.getLast? = some (Config.done s) := by
  sorry

end Weft
