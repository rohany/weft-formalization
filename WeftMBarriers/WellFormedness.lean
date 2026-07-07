/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.Traces
import WeftCommon.WellFormedness
import Mathlib.Logic.Relation

/-!
# State well-formedness for the mbarrier-extended language

The reachable-state invariants of the combined semantics — the
`WeftNamedBarriers.WellFormedness` suite, extended to cover both barrier kinds
and the fullness-uniqueness property. The file has three layers:

1. **The step discipline and timing layer** — the two per-language obligations
   (`ThreadStep.run_drop`(`_le_one`), `CTAStep.progOf_drop`/
   `progOf_length_le_succ`) that unlock `WeftCommon`'s trace-timing lemmas,
   re-exposed here under their usual names (`IsTimeOf.unique`,
   `exists_time_of_ends_done`, …).

2. **Fullness uniqueness** — `State.FullBarrier` indexes fullness over the sum
   `NamedBarrier ⊕ SharedBarrier` (named: `|I| + A = n`; shared: `A = n`,
   arrivals only), and `State.AtMostOneFull` says the full barriers form a
   `Set.Subsingleton`: **at most one barrier — across both maps — is full at
   any moment**. Every `interleave`/`error` step starts, by its guards
   `hbar`/`hmbar`, from an all-under-full state and registers on at most one
   barrier of one kind; the recycle rules only empty barriers. The headline
   corollary is `recycle_mb_recycle_exclusive`: the fullness premises of
   `CTAStep.recycle` and `CTAStep.mb_recycle` never hold simultaneously, so
   the pending recycle is the *unique* enabled rule and the recycle-priority
   discipline never arbitrates between the two barrier kinds.

3. **The invariant suite** — `State.blocked` indexes the blocking lists
   (`synced`/`waiting`) over the same sum, so `State.BlockInv` states the
   named library's three blocking clauses (`Nodup`, blocked ⇒ disabled, one
   blocking list per thread) across *both* kinds at once; `State.EnabledInv`
   is the converse direction (disabled ⇒ blocked somewhere); and `Config.WF`
   extends the named `Config.WF` with the mbarrier state clauses and the
   `AtMostOneFull` clause. Each comes with its `initial` / step-preservation /
   chain lemmas, plus `WF_of_reaches`; `atMostOneFull_of_reaches` and the
   exclusivity corollary follow by projection.

The step-preservation proofs factor through three transfer lemmas per
invariant — `congr` (the seven rules that touch no blocking list), `park` (the
three parking rules), and `wake` (the two recycles) — so each rule only
supplies a few rewriting facts about its state update.
-/

namespace WeftMBarriers

export WeftCommon (chain_step step_into_getLast suffix_length_le
  updateMapOn_apply cmd_at_last)

namespace List.IsSuffix
export WeftCommon.List.IsSuffix (eq_drop)
end List.IsSuffix

/-- `τ` *successfully runs `C₀` to completion*: a complete trace from `C₀` whose
final configuration is `done`. See `WeftCommon.IsSuccessfulTraceFrom`. -/
abbrev IsSuccessfulTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  WeftCommon.IsSuccessfulTraceFrom CTAStep C₀ τ

/-! ### The step discipline

The two facts that unlock `WeftCommon`'s timing layer for this language, each
by cases on its rules: a step leaves each thread's program a `drop` of what it
was, and shortens it by at most one command. The mbarrier rules keep the
discipline: `mb_init`/`mb_arrive`/`mb_wait_pass` advance by one, `mb_wait_block`
parks (drop `0`), and `mb_recycle` wakes waiters past their parked `wait_mb`
(drop `1`) exactly as the named `recycle` does for parked `sync_nb`s. -/

/-- A non-error thread step changes the program only by dropping a prefix of its
commands: `P' = P.drop d` for some `d` (in fact `d ∈ {0, 1}`). -/
theorem ThreadStep.run_drop {s s' : State} {i : ThreadId} {P P' : Prog}
    (hstep : ThreadStep (.run s i P) (.run s' i P')) : ∃ d, P' = P.drop d := by
  cases hstep with
  | read_noop => exact ⟨1, rfl⟩
  | write_noop => exact ⟨1, rfl⟩
  | arrive_configure => exact ⟨1, rfl⟩
  | arrive_register => exact ⟨1, rfl⟩
  | sync_configure => exact ⟨0, rfl⟩
  | sync_block => exact ⟨0, rfl⟩
  | mb_init => exact ⟨1, rfl⟩
  | mb_arrive => exact ⟨1, rfl⟩
  | mb_wait_block => exact ⟨0, rfl⟩
  | mb_wait_pass => exact ⟨1, rfl⟩

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
  | mb_init => exact ⟨1, by omega, rfl⟩
  | mb_arrive => exact ⟨1, by omega, rfl⟩
  | mb_wait_block => exact ⟨0, by omega, rfl⟩
  | mb_wait_pass => exact ⟨1, by omega, rfl⟩

/-- One CTA step changes each thread's program only by dropping a prefix
(`WeftCommon.StepDropsPrefix`, instantiated). -/
theorem CTAStep.progOf_drop {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    ∃ d, C'.progOf t = (C.progOf t).drop d := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hmbar hstep =>
      by_cases h : t = i
      · subst h
        obtain ⟨d, hd⟩ := hstep.run_drop
        exact ⟨d, by
          simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self, hd]⟩
      · exact ⟨0, by
          simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_of_ne h]⟩
  | @recycle s T nb I A n hb hfull hpark =>
      by_cases h : t ∈ I
      · exact ⟨1, by simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, h, List.drop_one]⟩
      · exact ⟨0, by simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, h]⟩
  | @mb_recycle s T sb I A n ph hb hfull hpark =>
      by_cases h : t ∈ I
      · exact ⟨1, by simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, h, List.drop_one]⟩
      · exact ⟨0, by simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, h]⟩
  | @done s T hdone _ _ =>
      exact ⟨(T.prog t).length, by simp [WeftCommon.Config.progOf, List.drop_length]⟩
  | @error s T i P' _ _ hstep =>
      exact ⟨0, by simp [WeftCommon.Config.progOf]⟩

/-- A single CTA step shortens a thread's remaining program by at most one command
(`WeftCommon.StepShrinksByOne`, instantiated). -/
theorem CTAStep.progOf_length_le_succ {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    (C.progOf t).length ≤ (C'.progOf t).length + 1 := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hmbar hth =>
      simp only [WeftCommon.Config.progOf]
      by_cases h : t = i
      · subst h
        obtain ⟨d, hd1, hd⟩ := hth.run_drop_le_one
        simp only [WeftCommon.CTA.set, Function.update_self, hd, List.length_drop]
        omega
      · simp only [WeftCommon.CTA.set, Function.update_of_ne h]; omega
  | @recycle s T nb I A n hb hfull hpark =>
      simp only [WeftCommon.Config.progOf]
      by_cases h : t ∈ I
      · simp only [WeftCommon.CTA.wake, if_pos h]
        cases T.prog t with
        | nil => simp
        | cons x xs => simp
      · simp only [WeftCommon.CTA.wake, if_neg h]; omega
  | @mb_recycle s T sb I A n ph hb hfull hpark =>
      simp only [WeftCommon.Config.progOf]
      by_cases h : t ∈ I
      · simp only [WeftCommon.CTA.wake, if_pos h]
        cases T.prog t with
        | nil => simp
        | cons x xs => simp
      · simp only [WeftCommon.CTA.wake, if_neg h]; omega
  | @done s T hdone _ _ =>
      have hnil : T.prog t = [] := by
        by_cases ht : t ∈ T.ids
        · exact hdone t ht
        · exact T.nil_outside_ids t ht
      simp only [WeftCommon.Config.progOf, hnil]; simp
  | @error s T i P' _ _ hth =>
      simp only [WeftCommon.Config.progOf]; omega

/-! ### The timing layer, instantiated

Thin wrappers over `WeftCommon`'s step-discipline lemmas, discharging the two
facts above — same names and signatures as in the named-barrier library. -/

/-- One CTA step makes each thread's program a suffix of its previous program. -/
theorem CTAStep.progOf_suffix {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    C'.progOf t <:+ C.progOf t :=
  WeftCommon.progOf_suffix_of_step (fun _ _ h t => h.progOf_drop t) hstep t

/-- Along a (sub)trace, the *last* configuration's program for a thread is a suffix
of every configuration's program for that thread — programs only shrink. -/
theorem CTAStep.suffix_last (t : ThreadId) :
    ∀ {l : List Config} {Cₙ : Config}, List.IsChain CTAStep l → l.getLast? = some Cₙ →
      ∀ C ∈ l, Cₙ.progOf t <:+ C.progOf t :=
  WeftCommon.progOf_suffix_last (fun _ _ h t => h.progOf_drop t) t

/-- Programs only shrink: at a later trace index a thread's remaining program is a
suffix of its program at an earlier index. -/
theorem progOf_suffix_index_le {τ : List Config} (hchain : List.IsChain CTAStep τ)
    (t : ThreadId) {p : Nat} {Cp : Config} (hp : τ[p]? = some Cp)
    {q : Nat} (hpq : p ≤ q) {Cq : Config} (hq : τ[q]? = some Cq) :
    Cq.progOf t <:+ Cp.progOf t :=
  WeftCommon.progOf_suffix_index_le (fun _ _ h t => h.progOf_drop t) hchain t hp hpq hq

/-- `IsTimeOf` is a partial function: an instruction executes at most once in a trace. -/
theorem IsTimeOf.unique {C₀ : Config} {τ : List Config} {η : ProgPoint} {m m' : Nat}
    (h : IsTimeOf C₀ τ η m) (h' : IsTimeOf C₀ τ η m') : m = m' :=
  WeftCommon.IsTimeOf.unique (fun _ _ hs t => hs.progOf_drop t) h h'

/-- The command at the head of the *last* configuration's program never executes. -/
theorem noTime_at_last {C₀ Cₙ : Config} {τ : List Config} {t : ThreadId}
    (hτ : IsCompleteTraceFrom C₀ τ) (hlast : τ.getLast? = some Cₙ)
    (hpos : 0 < (Cₙ.progOf t).length) (hle : (Cₙ.progOf t).length ≤ (C₀.progOf t).length) :
    ¬ ∃ m, IsTimeOf C₀ τ (ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length)) m :=
  WeftCommon.noTime_at_last (fun _ _ h t => h.progOf_drop t) hτ hlast hpos hle

/-- Every command runs in a successful execution: in a complete trace from `C₀` that
ends in `done`, every valid program point has a time. -/
theorem exists_time_of_ends_done {C₀ : Config} {τ' : List Config} {sd : State}
    (hτ : IsCompleteTraceFrom C₀ τ') (hlast : τ'.getLast? = some (Config.done sd))
    {η : ProgPoint} (hk : η.idx < (C₀.progOf η.thread).length) :
    ∃ n, IsTimeOf C₀ τ' η n :=
  WeftCommon.exists_time_of_ends_done (fun _ _ h t => h.progOf_drop t)
    (fun _ _ h t => h.progOf_length_le_succ t) hτ hlast hk

/-- A named-barrier state is *full* when it is configured (count `some n`) and
exactly `n` threads have registered: `|I| + A = n` — the fullness premise of
`CTAStep.recycle`. Unconfigured barriers are never full. -/
def NamedBarrierState.isFull (β : NamedBarrierState) : Bool :=
  match β.count with
  | some n => β.synced.length + β.arrived == (n : Nat)
  | none => false

/-- An mbarrier state is *full* when it is initialized (count `some n`) and
exactly `n` *arrivals* have occurred: `|A| = n` — the fullness premise of
`CTAStep.mb_recycle`. Waiters do not count toward mbarrier fullness, and
uninitialized barriers are never full. -/
def MBarrierState.isFull (β : MBarrierState) : Bool :=
  match β.count with
  | some n => β.arrived == (n : Nat)
  | none => false

/-- Barrier `b` — of either kind, named (`.inl`) or shared (`.inr`) — is full
in state `s`. Working over the sum type lets "at most one barrier is full"
range over both maps at once. -/
def State.FullBarrier (s : State) : NamedBarrier ⊕ SharedBarrier → Prop
  | .inl nb => (s.BN nb).isFull = true
  | .inr sb => (s.BM sb).isFull = true

/-- **At most one barrier — across both maps — is full.** Stated as
`Set.Subsingleton` of the full barriers over the sum of the two name spaces:
any two full barriers are equal (in particular, of the same kind). -/
def State.AtMostOneFull (s : State) : Prop :=
  { b | s.FullBarrier b }.Subsingleton

/-- The initial state satisfies the invariant: no barrier of either kind is
even configured, so none is full. -/
theorem State.atMostOneFull_initial : State.initial.AtMostOneFull := by
  intro b hb
  exfalso
  cases b with
  | inl nb =>
    simp [State.FullBarrier, State.initial, NamedBarrierState.isFull,
      NamedBarrierState.unconfigured] at hb
  | inr sb =>
    simp [State.FullBarrier, State.initial, MBarrierState.isFull,
      MBarrierState.uninitialized] at hb

/-- At most one barrier is full when every full barrier is a specific `b₀`. -/
theorem State.AtMostOneFull.of_unique {s' : State} {b₀ : NamedBarrier ⊕ SharedBarrier}
    (h : ∀ b, s'.FullBarrier b → b = b₀) : s'.AtMostOneFull :=
  fun _ hx _ hy => (h _ hx).trans (h _ hy).symm

/-- At most one barrier is full when none is. -/
theorem State.AtMostOneFull.of_none {s' : State}
    (h : ∀ b, ¬ s'.FullBarrier b) : s'.AtMostOneFull :=
  fun x hx => absurd hx (h x)

/-- The blocking list of a barrier of either kind: the `synced` list of a named
barrier (`.inl`), the `waiting` list of an mbarrier (`.inr`). Indexing by the sum
lets the blocking invariant quantify over the blocking lists of *both* kinds at
once — in particular its uniqueness clause forbids a thread from being parked at
a named barrier and an mbarrier simultaneously. -/
def State.blocked (s : State) : NamedBarrier ⊕ SharedBarrier → List ThreadId
  | .inl nb => (s.BN nb).synced
  | .inr sb => (s.BM sb).waiting

/-- The blocking invariant on a state, ranging over the blocking lists of both
barrier kinds (`State.blocked`): every blocking list is duplicate-free
(`Nodup`), every blocked thread is disabled, and no thread is blocked at two
distinct barriers — of any kinds — simultaneously. A thread is disabled the
instant it parks (`sync_block`/`sync_configure`/`mb_wait_block`) and re-enabled
only by the recycle that clears it, so it cannot re-park (`Nodup`) nor be
parked at two barriers at once (uniqueness). -/
def State.BlockInv (s : State) : Prop :=
  (∀ b, (s.blocked b).Nodup) ∧
  (∀ b i, i ∈ s.blocked b → s.E i = false) ∧
  (∀ b b' i, i ∈ s.blocked b → i ∈ s.blocked b' → b = b')

/-- `BlockInv` holds at the initial state: every blocking list is empty. -/
theorem State.BlockInv.initial : State.initial.BlockInv := by
  refine ⟨fun b => ?_, fun b i hi => ?_, fun b b' i hi hi' => ?_⟩
  · cases b <;> simp [State.blocked, State.initial, NamedBarrierState.unconfigured,
      MBarrierState.uninitialized]
  · exfalso
    cases b <;> simp [State.blocked, State.initial, NamedBarrierState.unconfigured,
      MBarrierState.uninitialized] at hi
  · exfalso
    cases b <;> simp [State.blocked, State.initial, NamedBarrierState.unconfigured,
      MBarrierState.uninitialized] at hi

/-! #### Transfer lemmas

The ten `run → run` thread rules and the two recycles change the blocking
structure in only three ways: not at all (`congr` — `read`/`write`, the
arrive/init rules, and `mb_wait_pass`, none of which touch a blocking list or
the enabled map), by parking the stepping thread at one barrier (`park` —
`sync_configure`/`sync_block`/`mb_wait_block`), or by clearing one barrier's
list and waking exactly its members (`wake` — the two recycles). Each transfer
lemma re-establishes the invariant from a description of the change, so the
step lemmas below only supply three or four rewriting facts per rule. -/

/-- `BlockInv` transfers along a step that changes no blocking list and no
enabledness. -/
theorem State.BlockInv.congr {s s' : State} (hbi : s.BlockInv)
    (hb : ∀ b, s'.blocked b = s.blocked b) (hE : ∀ j, s'.E j = s.E j) :
    s'.BlockInv := by
  obtain ⟨hnd, hdis, hone⟩ := hbi
  refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
  · rw [hb b]; exact hnd b
  · rw [hb b] at hj; rw [hE j]; exact hdis b j hj
  · rw [hb b] at h1; rw [hb b'] at h2; exact hone b b' j h1 h2

/-- `BlockInv` transfers along a step that parks the *enabled* thread `i` at
barrier `b₀` (of either kind), leaving every other blocking list unchanged:
`i` is fresh in every list (it was enabled), so `Nodup` and uniqueness survive
the cons. -/
theorem State.BlockInv.park {s s' : State} (hbi : s.BlockInv) {i : ThreadId}
    {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hpark : s'.blocked b₀ = i :: s.blocked b₀)
    (hsame : ∀ b, b ≠ b₀ → s'.blocked b = s.blocked b)
    (hE : ∀ j, s'.E j = Function.update s.E i false j)
    (hen : s.E i = true) : s'.BlockInv := by
  obtain ⟨hnd, hdis, hone⟩ := hbi
  have hifresh : ∀ b, i ∉ s.blocked b := by
    intro b hmem
    have h := hdis b i hmem
    rw [hen] at h
    exact absurd h (by simp)
  refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
  · by_cases hbb : b = b₀
    · subst hbb; rw [hpark]; exact List.nodup_cons.mpr ⟨hifresh b, hnd b⟩
    · rw [hsame b hbb]; exact hnd b
  · rw [hE j]
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji]
      by_cases hbb : b = b₀
      · subst hbb
        rw [hpark] at hj
        rcases List.mem_cons.mp hj with rfl | hjmem
        · exact absurd rfl hji
        · exact hdis b j hjmem
      · rw [hsame b hbb] at hj; exact hdis b j hj
  · by_cases hji : j = i
    · subst hji
      have hb1 : b = b₀ := by
        by_contra hne
        rw [hsame b hne] at h1
        exact hifresh b h1
      have hb2 : b' = b₀ := by
        by_contra hne
        rw [hsame b' hne] at h2
        exact hifresh b' h2
      rw [hb1, hb2]
    · have h1' : j ∈ s.blocked b := by
        by_cases hbb : b = b₀
        · subst hbb
          rw [hpark] at h1
          rcases List.mem_cons.mp h1 with rfl | h1m
          · exact absurd rfl hji
          · exact h1m
        · rw [hsame b hbb] at h1; exact h1
      have h2' : j ∈ s.blocked b' := by
        by_cases hbb : b' = b₀
        · subst hbb
          rw [hpark] at h2
          rcases List.mem_cons.mp h2 with rfl | h2m
          · exact absurd rfl hji
          · exact h2m
        · rw [hsame b' hbb] at h2; exact h2
      exact hone b b' j h1' h2'

/-- `BlockInv` transfers along a recycle of `b₀` (of either kind): its list is
cleared and exactly its members are woken — by uniqueness they appear in no
other list, so the disabled clause survives everywhere else. -/
theorem State.BlockInv.wake {s s' : State} (hbi : s.BlockInv)
    {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hclear : s'.blocked b₀ = [])
    (hsame : ∀ b, b ≠ b₀ → s'.blocked b = s.blocked b)
    (hE : ∀ j, s'.E j = updateMapOn s.E (s.blocked b₀) true j) : s'.BlockInv := by
  obtain ⟨hnd, hdis, hone⟩ := hbi
  refine ⟨fun b => ?_, fun b j hj => ?_, fun b b' j h1 h2 => ?_⟩
  · by_cases hbb : b = b₀
    · subst hbb; rw [hclear]; exact List.nodup_nil
    · rw [hsame b hbb]; exact hnd b
  · by_cases hbb : b = b₀
    · subst hbb; rw [hclear] at hj; simp at hj
    · rw [hsame b hbb] at hj
      have hnotb₀ : j ∉ s.blocked b₀ := fun hmem => hbb (hone b b₀ j hj hmem)
      rw [hE j, updateMapOn_apply, if_neg hnotb₀]
      exact hdis b j hj
  · by_cases hbb : b = b₀
    · subst hbb; rw [hclear] at h1; simp at h1
    · by_cases hbb' : b' = b₀
      · subst hbb'; rw [hclear] at h2; simp at h2
      · rw [hsame b hbb] at h1; rw [hsame b' hbb'] at h2; exact hone b b' j h1 h2

/-- `BlockInv` is preserved by every step. The interesting cases: a `sync_nb` or
`wait_mb` parks an *enabled* thread (fresh in every blocking list by the
blocked-⇒-disabled clause, keeping `Nodup` and uniqueness), and the two recycle
rules re-enable exactly the threads of the one list they clear, which by
uniqueness appear in no other list of either kind — so the disabled clause
survives everywhere else. -/
theorem blockInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.BlockInv) :
    ∀ s', C'.state? = some s' → s'.BlockInv := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hmbar hth =>
    have hbi := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hbi
    | write_noop => exact hbi
    | mb_wait_pass he hb0 hnep => exact hbi
    | @arrive_configure _ _ nb₀ n _ he hb0 =>
      refine hbi.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          simp [State.blocked, Function.update_self, hb0, NamedBarrierState.unconfigured]
        · simp [State.blocked, Function.update_of_ne hbb]
      | inr sb => rfl
    | @arrive_register _ _ nb₀ n _ I A he hb0 hpos hlt =>
      refine hbi.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb; simp [State.blocked, Function.update_self, hb0]
        · simp [State.blocked, Function.update_of_ne hbb]
      | inr sb => rfl
    | @mb_init _ _ sb₀ n _ he hb0 =>
      refine hbi.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb => rfl
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          simp [State.blocked, Function.update_self, hb0, MBarrierState.uninitialized]
        · simp [State.blocked, Function.update_of_ne hbb]
    | @mb_arrive _ _ sb₀ _ I A n ph he hb0 =>
      refine hbi.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb => rfl
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb; simp [State.blocked, Function.update_self, hb0]
        · simp [State.blocked, Function.update_of_ne hbb]
    | @sync_configure _ _ nb₀ n c he hb0 =>
      refine hbi.park (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => rfl) he
      · simp [State.blocked, Function.update_self, hb0, NamedBarrierState.unconfigured]
      · cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
        | inr sb => rfl
    | @sync_block _ _ nb₀ n c I A he hb0 hpos hlt =>
      refine hbi.park (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => rfl) he
      · simp [State.blocked, Function.update_self, hb0]
      · cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
        | inr sb => rfl
    | @mb_wait_block _ _ sb₀ ph c I A n he hb0 =>
      refine hbi.park (b₀ := .inr sb₀) ?_ (fun b hbne => ?_) (fun j => rfl) he
      · simp [State.blocked, Function.update_self, hb0]
      · cases b with
        | inl nb => rfl
        | inr sb =>
          have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
  | @recycle s T nb₀ I₀ A₀ n₀ hb hfullr hpark =>
    have hbi := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    refine hbi.wake (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => ?_)
    · simp [State.blocked, Function.update_self, NamedBarrierState.unconfigured]
    · cases b with
      | inl nb =>
        have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
        simp [State.blocked, Function.update_of_ne hnn]
      | inr sb => rfl
    · simp [State.blocked, hb]
  | @mb_recycle s T sb₀ I₀ A₀ n₀ ph₀ hb hfullr hpark =>
    have hbi := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    refine hbi.wake (b₀ := .inr sb₀) ?_ (fun b hbne => ?_) (fun j => ?_)
    · simp [State.blocked, Function.update_self]
    · cases b with
      | inl nb => rfl
      | inr sb =>
        have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
        simp [State.blocked, Function.update_of_ne hnn]
    · simp [State.blocked, hb]
  | done hdone hnofull hmbnofull =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    exact hC _ rfl
  | error hbar hmbar hth =>
    simp [WeftCommon.Config.state?] at hs'

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

/-- The enabledness invariant: a disabled thread is blocked *somewhere* — parked
at a named barrier or an mbarrier (`disabled ⟹ blocked`; `BlockInv` supplies the
converse). A thread is disabled exactly by a blocking command (which puts it in
that barrier's blocking list) and re-enabled exactly by the matching recycle
(which removes it). -/
def State.EnabledInv (s : State) : Prop :=
  ∀ i, s.E i = false → ∃ b, i ∈ s.blocked b

/-- `EnabledInv` holds at the initial state: every thread is enabled. -/
theorem State.EnabledInv.initial : State.initial.EnabledInv := by
  intro i hi
  simp [State.initial] at hi

/-- `EnabledInv` transfers along a step that changes no blocking list and no
enabledness. -/
theorem State.EnabledInv.congr {s s' : State} (hei : s.EnabledInv)
    (hb : ∀ b, s'.blocked b = s.blocked b) (hE : ∀ j, s'.E j = s.E j) :
    s'.EnabledInv := by
  intro j hj
  rw [hE j] at hj
  obtain ⟨b, hbm⟩ := hei j hj
  exact ⟨b, by rw [hb b]; exact hbm⟩

/-- `EnabledInv` transfers along a step that parks thread `i` at barrier `b₀`:
the newly disabled `i` is blocked at `b₀`. -/
theorem State.EnabledInv.park {s s' : State} (hei : s.EnabledInv) {i : ThreadId}
    {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hpark : s'.blocked b₀ = i :: s.blocked b₀)
    (hsame : ∀ b, b ≠ b₀ → s'.blocked b = s.blocked b)
    (hE : ∀ j, s'.E j = Function.update s.E i false j) : s'.EnabledInv := by
  intro j hj
  rw [hE j] at hj
  by_cases hji : j = i
  · subst hji
    exact ⟨b₀, by rw [hpark]; exact List.mem_cons_self ..⟩
  · rw [Function.update_of_ne hji] at hj
    obtain ⟨b, hbm⟩ := hei j hj
    by_cases hbb : b = b₀
    · subst hbb
      exact ⟨b, by rw [hpark]; exact List.mem_cons_of_mem _ hbm⟩
    · exact ⟨b, by rw [hsame b hbb]; exact hbm⟩

/-- `EnabledInv` transfers along a recycle of `b₀`: a thread still disabled
afterwards was not woken, so it was not blocked at `b₀` and its blocking
barrier survives. -/
theorem State.EnabledInv.wake {s s' : State} (hei : s.EnabledInv)
    {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hclear : s'.blocked b₀ = [])
    (hsame : ∀ b, b ≠ b₀ → s'.blocked b = s.blocked b)
    (hE : ∀ j, s'.E j = updateMapOn s.E (s.blocked b₀) true j) : s'.EnabledInv := by
  intro j hj
  rw [hE j, updateMapOn_apply] at hj
  split at hj
  · exact absurd hj (by simp)
  · rename_i hnmem
    obtain ⟨b, hbm⟩ := hei j hj
    by_cases hbb : b = b₀
    · subst hbb; exact absurd hbm hnmem
    · exact ⟨b, by rw [hsame b hbb]; exact hbm⟩

/-- `EnabledInv` is preserved by every step: a blocking command that disables
thread `i` simultaneously adds it to a blocking list; each recycle re-enables
exactly the threads it removes from its list; every other step touches neither
the enabled map nor any blocking list relevantly. -/
theorem enabledInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.EnabledInv) :
    ∀ s', C'.state? = some s' → s'.EnabledInv := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hmbar hth =>
    have hei := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hei
    | write_noop => exact hei
    | mb_wait_pass he hb0 hnep => exact hei
    | @arrive_configure _ _ nb₀ n _ he hb0 =>
      refine hei.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          simp [State.blocked, Function.update_self, hb0, NamedBarrierState.unconfigured]
        · simp [State.blocked, Function.update_of_ne hbb]
      | inr sb => rfl
    | @arrive_register _ _ nb₀ n _ I A he hb0 hpos hlt =>
      refine hei.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb; simp [State.blocked, Function.update_self, hb0]
        · simp [State.blocked, Function.update_of_ne hbb]
      | inr sb => rfl
    | @mb_init _ _ sb₀ n _ he hb0 =>
      refine hei.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb => rfl
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          simp [State.blocked, Function.update_self, hb0, MBarrierState.uninitialized]
        · simp [State.blocked, Function.update_of_ne hbb]
    | @mb_arrive _ _ sb₀ _ I A n ph he hb0 =>
      refine hei.congr (fun b => ?_) (fun j => rfl)
      cases b with
      | inl nb => rfl
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb; simp [State.blocked, Function.update_self, hb0]
        · simp [State.blocked, Function.update_of_ne hbb]
    | @sync_configure _ _ nb₀ n c he hb0 =>
      refine hei.park (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => rfl)
      · simp [State.blocked, Function.update_self, hb0, NamedBarrierState.unconfigured]
      · cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
        | inr sb => rfl
    | @sync_block _ _ nb₀ n c I A he hb0 hpos hlt =>
      refine hei.park (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => rfl)
      · simp [State.blocked, Function.update_self, hb0]
      · cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
        | inr sb => rfl
    | @mb_wait_block _ _ sb₀ ph c I A n he hb0 =>
      refine hei.park (b₀ := .inr sb₀) ?_ (fun b hbne => ?_) (fun j => rfl)
      · simp [State.blocked, Function.update_self, hb0]
      · cases b with
        | inl nb => rfl
        | inr sb =>
          have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
          simp [State.blocked, Function.update_of_ne hnn]
  | @recycle s T nb₀ I₀ A₀ n₀ hb hfullr hpark =>
    have hei := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    refine hei.wake (b₀ := .inl nb₀) ?_ (fun b hbne => ?_) (fun j => ?_)
    · simp [State.blocked, Function.update_self, NamedBarrierState.unconfigured]
    · cases b with
      | inl nb =>
        have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
        simp [State.blocked, Function.update_of_ne hnn]
      | inr sb => rfl
    · simp [State.blocked, hb]
  | @mb_recycle s T sb₀ I₀ A₀ n₀ ph₀ hb hfullr hpark =>
    have hei := hC s rfl
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    refine hei.wake (b₀ := .inr sb₀) ?_ (fun b hbne => ?_) (fun j => ?_)
    · simp [State.blocked, Function.update_self]
    · cases b with
      | inl nb => rfl
      | inr sb =>
        have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
        simp [State.blocked, Function.update_of_ne hnn]
    · simp [State.blocked, hb]
  | done hdone hnofull hmbnofull =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'; subst hs'
    exact hC _ rfl
  | error hbar hmbar hth =>
    simp [WeftCommon.Config.state?] at hs'

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

/-- The well-formedness invariant for a `run` configuration — the named-barrier
language's `Config.WF`, extended with the mbarrier clauses and the fullness
uniqueness property. For each barrier:

* a **configured named barrier** (`s.BN nb = ⟨I, A, some n⟩`) has non-empty
  registration (`0 < |I|+A`) that does not over-fill (`|I|+A ≤ n`), and every
  synced thread is *parked* at `sync_nb nb n`;
* an **unconfigured named barrier** has an empty synced list and a zero arrived
  count;
* an **initialized mbarrier** (`s.BM sb = ⟨I, A, some n, ph⟩`) never over-fills
  in arrivals (`A ≤ n` — waiters are unbounded and do not count), and every
  waiting thread is *parked* at the phase-matching `wait_mb sb ph`. There is no
  non-emptiness clause: initialization is explicit (`init_mb`), so an
  initialized mbarrier with no registration is reachable — and a wait can park
  before any arrival, so `I ≠ [] , A = 0` is too;
* an **uninitialized mbarrier** is pristine — `⟨[], 0, none, false⟩`, the
  `MBarrierState.uninitialized` encoding of `sb ∉ dom(BM)` (nothing ever
  de-initializes, so the phase is still `0`);
* **at most one barrier — across both maps — is full** (`State.AtMostOneFull`),
  the fullness-uniqueness property that makes the pending recycle the unique
  enabled rule (`recycle_mb_recycle_exclusive`);
* the blocking invariant `State.BlockInv`.

Vacuously true for `done`/`err`. -/
def Config.WF : Config → Prop
  | .run s T =>
      (∀ nb I A n, s.BN nb = ⟨I, A, some n⟩ →
          I.length + A ≤ (n : Nat) ∧
            (∀ i ∈ I, (T.prog i).head? = some (Cmd.sync_nb nb n)) ∧
            0 < I.length + A) ∧
      (∀ nb I A, s.BN nb = ⟨I, A, none⟩ → I = [] ∧ A = 0) ∧
      (∀ sb I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ →
          A ≤ (n : Nat) ∧ (∀ i ∈ I, (T.prog i).head? = some (Cmd.wait_mb sb ph))) ∧
      (∀ sb I A ph, s.BM sb = ⟨I, A, none, ph⟩ → I = [] ∧ A = 0 ∧ ph = false) ∧
      s.AtMostOneFull ∧
      s.BlockInv
  | .done _ => True
  | .err _ => True

/-- `WF` holds at the initial configuration: no barrier of either kind is
configured, nothing is full, and nothing is blocked. -/
theorem WF_initial {T : CTA} : (Config.WF (Config.run State.initial T)) := by
  refine ⟨fun nb I A n hB => ?_, fun nb I A hB => ?_, fun sb I A n ph hB => ?_,
    fun sb I A ph hB => ?_, State.atMostOneFull_initial, State.BlockInv.initial⟩
  · simp [State.initial, NamedBarrierState.unconfigured] at hB
  · simp only [State.initial, NamedBarrierState.unconfigured,
      NamedBarrierState.mk.injEq] at hB
    exact ⟨hB.1.symm, hB.2.1.symm⟩
  · simp [State.initial, MBarrierState.uninitialized] at hB
  · simp only [State.initial, MBarrierState.uninitialized, MBarrierState.mk.injEq] at hB
    exact ⟨hB.1.symm, hB.2.1.symm, hB.2.2.2.symm⟩

/-- **`WF` is preserved by every step** — the main invariant-preservation lemma,
subsuming the fullness-uniqueness argument. Sketch:

* `interleave`/`error` — the guards `hbar`/`hmbar` put every barrier of both
  kinds strictly under-full beforehand; the thread rule registers on at most
  one barrier of one kind, raising it by one (bounds and `AtMostOneFull`
  survive); a parking rule (`sync_configure`/`sync_block`/`mb_wait_block`)
  parks the stepping thread at exactly the head it is executing (park-heads
  survive; `blockInv_step` covers the blocking clauses); other threads'
  programs are untouched.
* `recycle`/`mb_recycle` — the recycled barrier was full, hence the unique
  full barrier; it is reset (unconfigured / cleared with the phase flipped),
  and `wake` advances exactly its parked threads past their parked heads —
  by `BlockInv` uniqueness no other barrier's parked heads move.
* `done`/`err` — `WF` is `True` there. -/
theorem CTAStep.WF_preserved {C C' : Config} (hstep : CTAStep C C') (hwf : C.WF) :
    C'.WF := by
  -- the blocking-invariant conjunct is preserved uniformly via `blockInv_step`
  have hBIpres : ∀ s', C'.state? = some s' → s'.BlockInv := by
    apply blockInv_step hstep
    obtain ⟨ss, TT, hCeq⟩ := hstep.source_run
    intro s hs
    rw [hCeq] at hwf hs
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    exact hwf.2.2.2.2.2
  cases hstep with
  | @interleave s s'' T i P' hi hbar hmbar hth =>
    obtain ⟨hcond, hcondn, hmcond, hmcondn, hamof, _⟩ := hwf
    -- nothing is full before an interleave step (the guards)
    have hnf : ∀ b, ¬ s.FullBarrier b := by
      intro b hf
      cases b with
      | inl nb =>
        rcases hbar nb with hu | ⟨I, A, n, heq, hlt⟩
        · have h : (s.BN nb).isFull = true := hf
          rw [hu] at h
          simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at h
        · have h : (s.BN nb).isFull = true := hf
          rw [heq] at h
          simp only [NamedBarrierState.isFull, beq_iff_eq] at h
          omega
      | inr sb =>
        rcases hmbar sb with hu | ⟨I, A, n, ph, heq, hlt⟩
        · have h : (s.BM sb).isFull = true := hf
          rw [hu] at h
          simp [MBarrierState.isFull, MBarrierState.uninitialized] at h
        · have h : (s.BM sb).isFull = true := hf
          rw [heq] at h
          simp only [MBarrierState.isFull, beq_iff_eq] at h
          omega
    generalize hpi : T.prog i = Pi at hth
    refine ⟨?_, ?_, ?_, ?_, ?_, hBIpres _ rfl⟩
    -- ## the configured named-barrier clause
    · cases hth with
      | read_noop =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | write_noop =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | arrive_configure he hb0 =>
        intro nb I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hB
          have hpos := n.pos
          obtain ⟨rfl, rfl, rfl⟩ := hB
          exact ⟨by simp; omega, (fun i' hi' => by simp at hi'), by simp⟩
        · obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | arrive_register he hb0 hpos hlt =>
        intro nb I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl⟩ := hB
          obtain ⟨_, hcpark, _⟩ := hcond _ _ _ _ hb0
          subst hbq
          refine ⟨by omega, (fun i' hi' => ?_), by omega⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hcpark i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond nb I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | sync_configure he hb0 =>
        intro nb I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hB
          have hpos := n.pos
          obtain ⟨rfl, rfl, rfl⟩ := hB
          subst hbq
          refine ⟨by simp; omega, (fun i' hi' => ?_), by simp⟩
          simp only [List.mem_singleton] at hi'; subst hi'
          simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
        · obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos⟩
          by_cases hne : i' = i
          · subst hne
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [← hpi]; exact hpark _ hi'
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | sync_block he hb0 hpos hlt =>
        intro nb I A n hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl⟩ := hB
          obtain ⟨_, hcpark, _⟩ := hcond _ _ _ _ hb0
          subst hbq
          refine ⟨by simp only [List.length_cons]; omega, (fun i' hi' => ?_),
            by simp only [List.length_cons]; omega⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
          · by_cases hne : i' = i
            · subst hne
              simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
            · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]
              exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond nb I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          by_cases hne : i' = i
          · subst hne
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [← hpi]; exact hpark _ hi'
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | mb_init he hb0 =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | mb_arrive he hb0 =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | mb_wait_block he hb0 =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | mb_wait_pass he hb0 hnep =>
        intro nb I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
    -- ## the unconfigured named-barrier clause
    · cases hth with
      | read_noop => exact hcondn
      | write_noop => exact hcondn
      | arrive_configure he hb0 =>
        intro nb I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn nb I A hB
      | arrive_register he hb0 hpos hlt =>
        intro nb I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn nb I A hB
      | sync_configure he hb0 =>
        intro nb I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn nb I A hB
      | sync_block he hb0 hpos hlt =>
        intro nb I A hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hcondn nb I A hB
      | mb_init he hb0 => exact hcondn
      | mb_arrive he hb0 => exact hcondn
      | mb_wait_block he hb0 => exact hcondn
      | mb_wait_pass he hb0 hnep => exact hcondn
    -- ## the initialized mbarrier clause
    · cases hth with
      | read_noop =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | write_noop =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | arrive_configure he hb0 =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | arrive_register he hb0 hpos hlt =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | sync_configure he hb0 =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | sync_block he hb0 hpos hlt =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | @mb_init _ _ sb₀ n _ he hb0 =>
        intro sb I A m ph hB
        simp only [Function.update_apply] at hB
        split at hB
        · simp only [MBarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
          exact ⟨Nat.zero_le _, fun i' hi' => by simp at hi'⟩
        · obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
          refine ⟨hle, fun i' hi' => ?_⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | @mb_arrive _ _ sb₀ _ I₀ A₀ n₀ ph₀ he hb0 =>
        intro sb I A m ph hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [MBarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
          obtain ⟨_, hcpk⟩ := hmcond _ _ _ _ _ hb0
          subst hbq
          -- the guard bounds the arrivals strictly before the step
          have hlt : A₀ < (n₀ : Nat) := by
            rcases hmbar sb with hu | ⟨I', A', n', ph', heq, hlt'⟩
            · rw [hb0] at hu
              simp [MBarrierState.uninitialized] at hu
            · rw [hb0] at heq
              simp only [MBarrierState.mk.injEq, Option.some.injEq] at heq
              obtain ⟨-, rfl, rfl, -⟩ := heq
              exact hlt'
          refine ⟨by omega, fun i' hi' => ?_⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hcpk i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hcpk i' hi'
        · obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
          refine ⟨hle, fun i' hi' => ?_⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpk i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | @mb_wait_block _ _ sb₀ ph₀ c I₀ A₀ n₀ he hb0 =>
        intro sb I A m ph hB
        simp only [Function.update_apply] at hB
        split at hB
        · rename_i hbq
          simp only [MBarrierState.mk.injEq, Option.some.injEq] at hB
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
          obtain ⟨hle₀, hcpk⟩ := hmcond _ _ _ _ _ hb0
          subst hbq
          refine ⟨hle₀, fun i' hi' => ?_⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
          · by_cases hne : i' = i
            · subst hne
              simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
            · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]
              exact hcpk i' hi'
        · obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
          refine ⟨hle, fun i' hi' => ?_⟩
          by_cases hne : i' = i
          · subst hne
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [← hpi]; exact hpk _ hi'
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpk i' hi'
      | @mb_wait_pass _ _ sb₀ phc _ I' A' n' ph' he hb0 hnep =>
        intro sb I A m ph hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hne : i' ≠ i := by
          rintro rfl
          have h := hpk i' hi'
          rw [hpi] at h
          simp only [List.head?_cons, Option.some.injEq, Cmd.wait_mb.injEq] at h
          obtain ⟨heq1, heq2⟩ := h
          rw [← heq1] at hB
          rw [hb0] at hB
          simp only [MBarrierState.mk.injEq, Option.some.injEq] at hB
          exact hnep (heq2.trans hB.2.2.2.symm)
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]
        exact hpk i' hi'
    -- ## the uninitialized mbarrier clause
    · cases hth with
      | read_noop => exact hmcondn
      | write_noop => exact hmcondn
      | arrive_configure he hb0 => exact hmcondn
      | arrive_register he hb0 hpos hlt => exact hmcondn
      | sync_configure he hb0 => exact hmcondn
      | sync_block he hb0 hpos hlt => exact hmcondn
      | mb_init he hb0 =>
        intro sb I A ph hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hmcondn sb I A ph hB
      | mb_arrive he hb0 =>
        intro sb I A ph hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hmcondn sb I A ph hB
      | mb_wait_block he hb0 =>
        intro sb I A ph hB; simp only [Function.update_apply] at hB; split at hB
        · simp at hB
        · exact hmcondn sb I A ph hB
      | mb_wait_pass he hb0 hnep => exact hmcondn
    -- ## fullness uniqueness: only the touched barrier can be full afterwards
    · cases hth with
      | read_noop => exact hamof
      | write_noop => exact hamof
      | mb_wait_pass he hb0 hnep => exact hamof
      | @arrive_configure _ _ nb₀ n _ he hb0 =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inl nb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BN nb₀ ⟨[], 1, some n⟩ nb).isFull = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
        | inr sb => exact hfb
      | @arrive_register _ _ nb₀ n _ I A he hb0 hpos hlt =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inl nb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BN nb₀ ⟨I, A + 1, some n⟩ nb).isFull = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
        | inr sb => exact hfb
      | @sync_configure _ _ nb₀ n c he hb0 =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inl nb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BN nb₀ ⟨[i], 0, some n⟩ nb).isFull = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
        | inr sb => exact hfb
      | @sync_block _ _ nb₀ n c I A he hb0 hpos hlt =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inl nb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb =>
          have hnn : nb ≠ nb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BN nb₀ ⟨i :: I, A, some n⟩ nb).isFull = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
        | inr sb => exact hfb
      | @mb_init _ _ sb₀ n _ he hb0 =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inr sb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb => exact hfb
        | inr sb =>
          have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BM sb₀ ⟨[], 0, some n, false⟩ sb).isFull = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
      | @mb_arrive _ _ sb₀ _ I₀ A₀ n₀ ph₀ he hb0 =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inr sb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb => exact hfb
        | inr sb =>
          have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BM sb₀ ⟨I₀, A₀ + 1, some n₀, ph₀⟩ sb).isFull
              = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
      | @mb_wait_block _ _ sb₀ ph₀ c I₀ A₀ n₀ he hb0 =>
        refine State.AtMostOneFull.of_unique (b₀ := Sum.inr sb₀) fun b hfb => ?_
        by_contra hbne
        refine hnf b ?_
        cases b with
        | inl nb => exact hfb
        | inr sb =>
          have hnn : sb ≠ sb₀ := fun h => hbne (by rw [h])
          have h : (Function.update s.BM sb₀ ⟨i :: I₀, A₀, some n₀, ph₀⟩ sb).isFull
              = true := hfb
          rw [Function.update_of_ne hnn] at h
          exact h
  | @recycle s T nb₀ I₀ A₀ n₀ hb hfullr hpark =>
    obtain ⟨hcond, hcondn, hmcond, hmcondn, hamof, _⟩ := hwf
    refine ⟨?_, ?_, ?_, ?_, ?_, hBIpres _ rfl⟩
    · intro nb I A n hB
      by_cases hbb : nb = nb₀
      · subst hbb
        simp only [Function.update_self, NamedBarrierState.unconfigured,
          NamedBarrierState.mk.injEq] at hB
        exact absurd hB.2.2 (by simp)
      · simp only [Function.update_of_ne hbb] at hB
        obtain ⟨hle, hpk, hpos⟩ := hcond nb I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hni : i' ∉ I₀ := by
          intro hmem
          have h1 := hpark i' hmem
          have h2 := hpk i' hi'
          rw [h1] at h2
          simp only [Option.some.injEq, Cmd.sync_nb.injEq] at h2
          exact hbb h2.1.symm
        simp only [WeftCommon.CTA.wake, if_neg hni]; exact hpk i' hi'
    · intro nb I A hB
      by_cases hbb : nb = nb₀
      · subst hbb
        simp only [Function.update_self, NamedBarrierState.unconfigured,
          NamedBarrierState.mk.injEq] at hB
        exact ⟨hB.1.symm, hB.2.1.symm⟩
      · simp only [Function.update_of_ne hbb] at hB; exact hcondn nb I A hB
    · intro sb I A m ph hB
      obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
      refine ⟨hle, fun i' hi' => ?_⟩
      have hni : i' ∉ I₀ := by
        intro hmem
        have h1 := hpark i' hmem
        have h2 := hpk i' hi'
        rw [h1] at h2
        simp at h2
      simp only [WeftCommon.CTA.wake, if_neg hni]; exact hpk i' hi'
    · exact hmcondn
    · refine State.AtMostOneFull.of_none fun x hx => ?_
      have hfb₀ : s.FullBarrier (.inl nb₀) := by
        have h : (s.BN nb₀).isFull = true := by
          rw [hb]
          simp [NamedBarrierState.isFull, hfullr]
        exact h
      have hmem₀ : (Sum.inl nb₀ : NamedBarrier ⊕ SharedBarrier) ∈
          { b | s.FullBarrier b } := hfb₀
      cases x with
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          have h : (Function.update s.BN nb NamedBarrierState.unconfigured nb).isFull
              = true := hx
          rw [Function.update_self] at h
          simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at h
        · have hfs : s.FullBarrier (.inl nb) := by
            have h : (Function.update s.BN nb₀ NamedBarrierState.unconfigured nb).isFull
                = true := hx
            rw [Function.update_of_ne hbb] at h
            exact h
          have hmem : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈
              { b | s.FullBarrier b } := hfs
          have := hamof hmem hmem₀
          simp only [Sum.inl.injEq] at this
          exact hbb this
      | inr sb =>
        have hfs : s.FullBarrier (.inr sb) := hx
        have hmem : (Sum.inr sb : NamedBarrier ⊕ SharedBarrier) ∈
            { b | s.FullBarrier b } := hfs
        exact nomatch (hamof hmem hmem₀)
  | @mb_recycle s T sb₀ I₀ A₀ n₀ ph₀ hb hfullr hpark =>
    obtain ⟨hcond, hcondn, hmcond, hmcondn, hamof, _⟩ := hwf
    refine ⟨?_, ?_, ?_, ?_, ?_, hBIpres _ rfl⟩
    · intro nb I A n hB
      obtain ⟨hle, hpk, hpos⟩ := hcond nb I A n hB
      refine ⟨hle, (fun i' hi' => ?_), hpos⟩
      have hni : i' ∉ I₀ := by
        intro hmem
        have h1 := hpark i' hmem
        have h2 := hpk i' hi'
        rw [h1] at h2
        simp at h2
      simp only [WeftCommon.CTA.wake, if_neg hni]; exact hpk i' hi'
    · exact hcondn
    · intro sb I A m ph hB
      by_cases hbb : sb = sb₀
      · subst hbb
        simp only [Function.update_self, MBarrierState.mk.injEq, Option.some.injEq] at hB
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
        exact ⟨Nat.zero_le _, fun i' hi' => by simp at hi'⟩
      · simp only [Function.update_of_ne hbb] at hB
        obtain ⟨hle, hpk⟩ := hmcond sb I A m ph hB
        refine ⟨hle, fun i' hi' => ?_⟩
        have hni : i' ∉ I₀ := by
          intro hmem
          have h1 := hpark i' hmem
          have h2 := hpk i' hi'
          rw [h1] at h2
          simp only [Option.some.injEq, Cmd.wait_mb.injEq] at h2
          exact hbb h2.1.symm
        simp only [WeftCommon.CTA.wake, if_neg hni]; exact hpk i' hi'
    · intro sb I A ph hB
      by_cases hbb : sb = sb₀
      · subst hbb
        simp only [Function.update_self, MBarrierState.mk.injEq] at hB
        exact absurd hB.2.2.1 (by simp)
      · simp only [Function.update_of_ne hbb] at hB; exact hmcondn sb I A ph hB
    · refine State.AtMostOneFull.of_none fun x hx => ?_
      have hfb₀ : s.FullBarrier (.inr sb₀) := by
        have h : (s.BM sb₀).isFull = true := by
          rw [hb]
          simp [MBarrierState.isFull, hfullr]
        exact h
      have hmem₀ : (Sum.inr sb₀ : NamedBarrier ⊕ SharedBarrier) ∈
          { b | s.FullBarrier b } := hfb₀
      cases x with
      | inl nb =>
        have hfs : s.FullBarrier (.inl nb) := hx
        have hmem : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈
            { b | s.FullBarrier b } := hfs
        exact nomatch (hamof hmem hmem₀)
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          have h : (Function.update s.BM sb ⟨[], 0, some n₀, !ph₀⟩ sb).isFull
              = true := hx
          rw [Function.update_self] at h
          simp only [MBarrierState.isFull, beq_iff_eq] at h
          have := n₀.pos
          omega
        · have hfs : s.FullBarrier (.inr sb) := by
            have h : (Function.update s.BM sb₀ ⟨[], 0, some n₀, !ph₀⟩ sb).isFull
                = true := hx
            rw [Function.update_of_ne hbb] at h
            exact h
          have hmem : (Sum.inr sb : NamedBarrier ⊕ SharedBarrier) ∈
              { b | s.FullBarrier b } := hfs
          have := hamof hmem hmem₀
          simp only [Sum.inr.injEq] at this
          exact hbb this
  | done hdone hnofull hmbnofull => trivial
  | error hbar hmbar hth => trivial

/-- `WF` holds at every configuration of a chain whose head satisfies it. -/
theorem WF_chain : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → C₀.WF → ∀ C ∈ τ, C.WF := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hwf C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hwf
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hwf
      · exact ih hbt rfl (hab.WF_preserved hwf) C hC'

/-- `WF` holds at every configuration reachable from the initial one. -/
theorem WF_of_reaches {T : CTA} {C : Config}
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) : C.WF := by
  induction hreach with
  | refl => exact WF_initial
  | tail _ hstep ih => exact hstep.WF_preserved ih

/-- Fullness uniqueness at every reachable `run` configuration — the
`AtMostOneFull` clause of `WF_of_reaches`, extracted. -/
theorem atMostOneFull_of_reaches {T : CTA} {s : State} {Tc : CTA}
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T)
      (Config.run s Tc)) :
    s.AtMostOneFull :=
  (WF_of_reaches hreach).2.2.2.2.1

/-- **The two recycle rules are mutually exclusive**: in a well-formed state
(`AtMostOneFull` — available at every reachable configuration via
`atMostOneFull_of_reaches`), the fullness premises of `CTAStep.recycle` and
`CTAStep.mb_recycle` cannot hold at once: no named barrier is full at the same
time as an mbarrier. Whichever recycle is pending is therefore the unique
enabled rule — the recycle-priority discipline never arbitrates between the
two barrier kinds. -/
theorem recycle_mb_recycle_exclusive {s : State} (h : s.AtMostOneFull) :
    ¬ ((∃ nb I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A = (n : Nat)) ∧
       (∃ sb I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A = (n : Nat))) := by
  rintro ⟨⟨nb, I, A, n, hbn, hfull⟩, ⟨sb, I', A', n', ph, hbm, hfull'⟩⟩
  have h1 : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈ { b | s.FullBarrier b } := by
    simp [State.FullBarrier, NamedBarrierState.isFull, hbn, hfull]
  have h2 : (Sum.inr sb : NamedBarrier ⊕ SharedBarrier) ∈ { b | s.FullBarrier b } := by
    simp [State.FullBarrier, MBarrierState.isFull, hbm, hfull']
  have h12 := h h1 h2
  simp at h12

end WeftMBarriers
