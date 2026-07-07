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

The three step-preservation lemmas (`blockInv_step`, `enabledInv_step`,
`CTAStep.WF_preserved`) are the remaining `sorry`s, each carrying its proof
sketch.
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

/-- `BlockInv` is preserved by every step. The interesting cases: a `sync_nb` or
`wait_mb` parks an *enabled* thread (fresh in every blocking list by the
blocked-⇒-disabled clause, keeping `Nodup` and uniqueness), and the two recycle
rules re-enable exactly the threads of the one list they clear, which by
uniqueness appear in no other list of either kind — so the disabled clause
survives everywhere else. -/
theorem blockInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.BlockInv) :
    ∀ s', C'.state? = some s' → s'.BlockInv := by
  sorry

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

/-- `EnabledInv` is preserved by every step: a blocking command that disables
thread `i` simultaneously adds it to a blocking list; each recycle re-enables
exactly the threads it removes from its list; every other step touches neither
the enabled map nor any blocking list relevantly. -/
theorem enabledInv_step {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.EnabledInv) :
    ∀ s', C'.state? = some s' → s'.EnabledInv := by
  sorry

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
  sorry

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
