/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.WellFormedness
import WeftCommon.WellSynchronized
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Well-synchronization for the mbarrier-extended language (§4.1, §5.2.3)

The Definition 5–7 layer for the combined language: which barrier a command
operates on, how many times a barrier has recycled along a trace, the
*generation* a command observes, and well-synchronization — the shared
`WeftCommon.WellSynchronized` instantiated at this language's step relation,
classifier, and generation relation.

## Barriers of two kinds

A command's barrier is a `NamedBarrier ⊕ SharedBarrier` (`Cmd.barrier?`), the
same sum indexing `State.FullBarrier` and `State.blocked`. Recycle detection
(`stepRecyclesBarrier`) is per kind: a named barrier recycles when it goes from
full to unconfigured; an mbarrier recycles when it goes from full (in arrivals)
to cleared *with its phase flipped* — the phase flip is the mbarrier's
distinctive recycle signature, and it is exactly what the generation counts.

## Generations are `ℤ`, 0-indexed

`Gen(τ)(cη)` counts the recyclings of the command's barrier strictly before its
execution step — Definition 5 exactly as the paper states it, with **no `+ 1`**:
with `Option`-valued generations there is no "never executes" sentinel to avoid
(that is `none`), so the 0-indexing needs no shift. The value type is `ℤ`
because mbarrier waits can observe generation `−1` (below). This deliberately
diverges from the named-barrier library, whose `IsGenOf` keeps 1-indexed `ℕ`
generations to stay aligned with its computable `pointGen`; generation values
never cross the language boundary, so the two conventions coexist.

## The observed generation of an mbarrier wait (§5.2.3)

After `r` recycles an mbarrier sits at phase `phaseAfter r` (phases start at
`0` and flip on each recycle). A `wait_mb sb ph` executed with `r` recyclings
strictly before it observes

* generation `r` when `ph = phaseAfter r` — the barrier is still in the wait's
  phase, so the wait genuinely waits for round `r` to complete (a blocked
  wait's execution time *is* that round's recycle);
* generation `r − 1` when `ph ≠ phaseAfter r` — the wait's round has already
  completed and the wait passes through (`MB-Wait-Pass`). With `r = 0` this is
  generation `−1`: the vacuously-completed round preceding any recycle.

Every other synchronization command (`arrive_nb`/`sync_nb`/`arrive_mb`/
`init_mb`) observes plain `r` (`Cmd.genValue`).

**Domain note.** `init_mb` is included in `Gen`'s domain (`Cmd.barrier?` sends
it to its mbarrier): well-synchronization then requires an `init_mb` to execute
in every complete trace, with a schedule-independent generation. Exclude it
from `Cmd.barrier?` if initialization should instead be outside the checked
ordering discipline.
-/

namespace WeftMBarriers

/-- The barrier a command operates on — a named barrier (`.inl`) for
`sync_nb`/`arrive_nb`, a shared barrier (`.inr`) for the mbarrier operations,
and `none` for the memory operations. -/
def Cmd.barrier? : Cmd → Option (NamedBarrier ⊕ SharedBarrier)
  | .arrive_nb nb _ => some (.inl nb)
  | .sync_nb nb _ => some (.inl nb)
  | .init_mb sb _ => some (.inr sb)
  | .arrive_mb sb => some (.inr sb)
  | .wait_mb sb _ => some (.inr sb)
  | .read _ => none
  | .write _ => none

/-- The step `C ⤳ C'` recycles barrier `b` (of either kind): `b` is full in `C`
and, in `C'`, reset to unconfigured (named) or cleared with its phase flipped
(shared) — only `CTAStep.recycle` resp. `CTAStep.mb_recycle` produce these
transitions, so this detects exactly the recycle steps for `b` along a trace. -/
def stepRecyclesBarrier (b : NamedBarrier ⊕ SharedBarrier) (C C' : Config) : Bool :=
  match C.state?, C'.state? with
  | some s, some s' =>
      match b with
      | .inl nb =>
          (s.BN nb).isFull && decide (s'.BN nb = NamedBarrierState.unconfigured)
      | .inr sb =>
          (s.BM sb).isFull &&
            decide (s'.BM sb = ⟨[], 0, (s.BM sb).count, !(s.BM sb).phase⟩)
  | _, _ => false

/-- The number of recyclings of barrier `b` among the first `m` steps of `τ`
(the transitions from config index `j` to `j+1` for `j < m`). -/
def recycleCount (b : NamedBarrier ⊕ SharedBarrier) (τ : List Config) (m : Nat) : Nat :=
  (List.range m).countP fun j =>
    match τ[j]?, τ[j + 1]? with
    | some C, some C' => stepRecyclesBarrier b C C'
    | _, _ => false

/-- The phase an mbarrier sits at after `r` recycles: phases start at `0`
(`false`) and flip on each recycle, so this is the parity of `r`. -/
def phaseAfter (r : Nat) : Phase := r % 2 == 1

/-- The generation a command observes when it executes with `r` recyclings of
its barrier strictly before it (§5.2.3). A `wait_mb _ ph` observes `r` when its
phase matches the barrier's current phase (`phaseAfter r`) — it waits for round
`r` to complete — and `r − 1` when the phase has already advanced (the wait
passes; `−1` when `r = 0`). Every other command observes `r`. -/
def Cmd.genValue (c : Cmd) (r : Nat) : ℤ :=
  match c with
  | .wait_mb _ ph => if phaseAfter r = ph then (r : ℤ) else (r : ℤ) - 1
  | _ => (r : ℤ)

/-- Definition 5 (§4.1), adapted per §5.2.3. The generation `Gen(τ)(cη) = g` of
a synchronization command at program point `η`, in a complete trace `τ` from
`C₀`: if `cη` operates on barrier `b` and executes at time `t(τ, η) = m`, then
`g = some (cη.genValue r)` where `r = recycleCount b τ (m - 1)` counts the
recyclings of `b` strictly before step `m`; if `cη` never executes in `τ`
(e.g. blocked by a deadlock), then `g = none`. Like `IsTimeOf`, it carries
`IsCompleteTraceFrom C₀ τ` so it is meaningful used on its own; it is total on
synchronization commands and undefined on `read`/`write` (not in `Gen`'s
domain).

(The `m - 1` reads Definition 5's "strictly before": the time definition is
inclusive of the step that executes the instruction, so the recyclings in the
first `m - 1` steps are exactly those strictly before step `m`.) -/
def IsGenOf (C₀ : Config) (τ : List Config) (η : ProgPoint) (g : Option ℤ) : Prop :=
  IsCompleteTraceFrom C₀ τ ∧
  ∃ c, η.cmd C₀ = some c ∧ ∃ b, c.barrier? = some b ∧
    ((∃ m, IsTimeOf C₀ τ η m ∧ g = some (c.genValue (recycleCount b τ (m - 1)))) ∨
      (g = none ∧ ¬ ∃ m, IsTimeOf C₀ τ η m))

/-- `IsGenOf` is a partial function: a command has at most one generation in a
trace. -/
theorem IsGenOf.unique {C₀ : Config} {τ : List Config} {η : ProgPoint}
    {g g' : Option ℤ} (h : IsGenOf C₀ τ η g) (h' : IsGenOf C₀ τ η g') : g = g' := by
  obtain ⟨_, c, hc, b, hb, hcase⟩ := h
  obtain ⟨_, c', hc', b', hb', hcase'⟩ := h'
  rw [hc] at hc'; obtain rfl := Option.some.inj hc'
  rw [hb] at hb'; obtain rfl := Option.some.inj hb'
  rcases hcase with ⟨m, hm, hg⟩ | ⟨hg0, hno⟩
  · rcases hcase' with ⟨m', hm', hg'⟩ | ⟨hg0', hno'⟩
    · have hmm : m = m' := IsTimeOf.unique hm hm'
      rw [hg, hg', hmm]
    · exact absurd ⟨m, hm⟩ hno'
  · rcases hcase' with ⟨m', hm', _⟩ | ⟨hg0', _⟩
    · exact absurd ⟨m', hm'⟩ hno
    · rw [hg0, hg0']

/-! ### Counting recycles, tracking phases

The trace-level facts the soundness proof of Algorithm 2's happens-before
relation reads generations with: the recycle-count algebra, the decodes of
head-dropping steps (only a recycle of `nb` drops a parked `sync_nb`; a
dropped `wait_mb` was either woken by a recycle or passed on a phase
mismatch), and the phase invariant — along any trace from the initial
configuration, an mbarrier's phase is the parity of its recycle count. -/

/-- One more recycle of `b` between steps `p` and `p+1` raises the recycle
count by exactly one. -/
theorem recycleCount_succ_of_recycle (b : NamedBarrier ⊕ SharedBarrier)
    (τ : List Config) {p : Nat} {C C' : Config}
    (hp : τ[p]? = some C) (hp1 : τ[p + 1]? = some C')
    (hrec : stepRecyclesBarrier b C C' = true) :
    recycleCount b τ (p + 1) = recycleCount b τ p + 1 := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append]
  congr 1
  simp [hp, hp1, hrec]

/-- A non-recycling step leaves the recycle count unchanged. -/
theorem recycleCount_succ_of_not_recycle (b : NamedBarrier ⊕ SharedBarrier)
    {τ : List Config} {p : Nat} {C C' : Config}
    (hp : τ[p]? = some C) (hp1 : τ[p + 1]? = some C')
    (hrec : stepRecyclesBarrier b C C' = false) :
    recycleCount b τ (p + 1) = recycleCount b τ p := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
  simp [hp, hp1, hrec]

/-- The recycle count is monotone in the step bound. -/
theorem recycleCount_mono (b : NamedBarrier ⊕ SharedBarrier) (τ : List Config) :
    Monotone (recycleCount b τ) :=
  monotone_nat_of_le_succ fun p => by
    unfold recycleCount; rw [List.range_succ, List.countP_append]; exact Nat.le_add_right _ _

/-- One more recycle flips the parity phase. -/
theorem phaseAfter_succ (r : Nat) : phaseAfter (r + 1) = !phaseAfter r := by
  rcases Nat.mod_two_eq_zero_or_one r with h | h <;>
    simp [phaseAfter, Nat.add_mod, h]

/-- Only a recycle of `nb` can drop a parked `sync_nb nb nn` head: at the step
where a thread's program advances past a leading `sync_nb`, the transition
recycles that barrier. -/
theorem sync_drop_recycles {C C' : Config} (hstep : CTAStep C C') {t : ThreadId}
    {nb : NamedBarrier} {nn : ℕ+} {rest : Prog}
    (hC : C.progOf t = Cmd.sync_nb nb nn :: rest) (hC' : C'.progOf t = rest) :
    stepRecyclesBarrier (.inl nb) C C' = true := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hmbar hth =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t = i
      · subst h
        simp only [WeftCommon.CTA.set, Function.update_self] at hC'
        subst hC'
        rw [hC] at hth
        cases hth
      · simp only [WeftCommon.CTA.set, Function.update_of_ne h] at hC'
        rw [hC] at hC'; simp at hC'
  | @recycle s T nb₀ I A n hb hfull hpark =>
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t ∈ I
      · have hpk := hpark t h
        rw [hC] at hpk
        simp only [List.head?_cons, Option.some.injEq, Cmd.sync_nb.injEq] at hpk
        obtain ⟨rfl, rfl⟩ := hpk
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
          NamedBarrierState.isFull, hfull, Function.update_self,
          NamedBarrierState.unconfigured]
      · exfalso
        simp only [WeftCommon.CTA.wake, if_neg h] at hC'
        rw [hC] at hC'; simp at hC'
  | @mb_recycle s T sb₀ I A n ph hb hfull hpark =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t ∈ I
      · have hpk := hpark t h
        rw [hC] at hpk; simp at hpk
      · simp only [WeftCommon.CTA.wake, if_neg h] at hC'
        rw [hC] at hC'; simp at hC'
  | @done s T hdone _ _ =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC
      have hnil : T.prog t = [] := by
        by_cases ht : t ∈ T.ids
        · exact hdone t ht
        · exact T.nil_outside_ids t ht
      rw [hnil] at hC; simp at hC
  | @error s T i P' _ _ hth =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC hC'
      rw [hC] at hC'; simp at hC'

/-- A dropped `wait_mb sb ph` head was either woken by a recycle of `sb`
(`MB-Recycle`) or passed through on a phase mismatch (`MB-Wait-Pass`) — in the
latter case the barrier's phase at the pre-state differs from the wait's. -/
theorem wait_drop_recycles_or_pass {C C' : Config} (hstep : CTAStep C C') {t : ThreadId}
    {sb : SharedBarrier} {ph : Phase} {rest : Prog}
    (hC : C.progOf t = Cmd.wait_mb sb ph :: rest) (hC' : C'.progOf t = rest) :
    stepRecyclesBarrier (.inr sb) C C' = true ∨
      ∃ s T, C = Config.run s T ∧ s.E t = true ∧ (s.BM sb).phase ≠ ph := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hmbar hth =>
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t = i
      · subst h
        simp only [WeftCommon.CTA.set, Function.update_self] at hC'
        subst hC'
        rw [hC] at hth
        cases hth with
        | @mb_wait_pass _ _ _ _ _ I A n ph' he hb0 hnep =>
            exact Or.inr ⟨s, T, rfl, he, by rw [hb0]; exact fun hcon => hnep hcon.symm⟩
      · exfalso
        simp only [WeftCommon.CTA.set, Function.update_of_ne h] at hC'
        rw [hC] at hC'; simp at hC'
  | @recycle s T nb₀ I A n hb hfull hpark =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t ∈ I
      · have hpk := hpark t h
        rw [hC] at hpk; simp at hpk
      · simp only [WeftCommon.CTA.wake, if_neg h] at hC'
        rw [hC] at hC'; simp at hC'
  | @mb_recycle s T sb₀ I A n ph₀ hb hfull hpark =>
      simp only [WeftCommon.Config.progOf] at hC hC'
      by_cases h : t ∈ I
      · left
        have hpk := hpark t h
        rw [hC] at hpk
        simp only [List.head?_cons, Option.some.injEq, Cmd.wait_mb.injEq] at hpk
        obtain ⟨rfl, rfl⟩ := hpk
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
          MBarrierState.isFull, hfull, Function.update_self]
      · exfalso
        simp only [WeftCommon.CTA.wake, if_neg h] at hC'
        rw [hC] at hC'; simp at hC'
  | @done s T hdone _ _ =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC
      have hnil : T.prog t = [] := by
        by_cases ht : t ∈ T.ids
        · exact hdone t ht
        · exact T.nil_outside_ids t ht
      rw [hnil] at hC; simp at hC
  | @error s T i P' _ _ hth =>
      exfalso
      simp only [WeftCommon.Config.progOf] at hC hC'
      rw [hC] at hC'; simp at hC'

/-- A recycling step flips the recycled mbarrier's phase — read directly off
the detection literal of `stepRecyclesBarrier`. -/
theorem phase_of_recycle {C C' : Config} {sb : SharedBarrier}
    (h : stepRecyclesBarrier (.inr sb) C C' = true) {s s' : State}
    (hs : C.state? = some s) (hs' : C'.state? = some s') :
    (s'.BM sb).phase = !(s.BM sb).phase := by
  simp only [stepRecyclesBarrier] at h
  rw [hs, hs'] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.2]

/-- A non-recycling step leaves an mbarrier's phase unchanged. -/
theorem phase_of_not_recycle {C C' : Config} (hstep : CTAStep C C') {sb : SharedBarrier}
    (h : stepRecyclesBarrier (.inr sb) C C' = false) {s s' : State}
    (hs : C.state? = some s) (hs' : C'.state? = some s') :
    (s'.BM sb).phase = (s.BM sb).phase := by
  cases hstep with
  | @interleave s₀ s₁ T i P' hi hbar hmbar hth =>
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
      subst hs; subst hs'
      generalize hpi : T.prog i = Pi at hth
      cases hth with
      | read_noop => rfl
      | write_noop => rfl
      | arrive_configure he hb0 => rfl
      | arrive_register he hb0 hpos hlt => rfl
      | sync_configure he hb0 => rfl
      | sync_block he hb0 hpos hlt => rfl
      | mb_wait_pass he hb0 hnep => rfl
      | @mb_init _ _ sb₀ n _ he hb0 =>
          by_cases hbb : sb = sb₀
          · subst hbb
            have h2 : (Function.update s₀.BM sb ⟨[], 0, some n, false⟩ sb).phase
                = (s₀.BM sb).phase := by
              simp [Function.update_self, hb0, MBarrierState.uninitialized]
            exact h2
          · have h2 : (Function.update s₀.BM sb₀ ⟨[], 0, some n, false⟩ sb).phase
                = (s₀.BM sb).phase := by
              rw [Function.update_of_ne hbb]
            exact h2
      | @mb_arrive _ _ sb₀ _ I A n ph he hb0 =>
          by_cases hbb : sb = sb₀
          · subst hbb
            have h2 : (Function.update s₀.BM sb ⟨I, A + 1, some n, ph⟩ sb).phase
                = (s₀.BM sb).phase := by
              simp [Function.update_self, hb0]
            exact h2
          · have h2 : (Function.update s₀.BM sb₀ ⟨I, A + 1, some n, ph⟩ sb).phase
                = (s₀.BM sb).phase := by
              rw [Function.update_of_ne hbb]
            exact h2
      | @mb_wait_block _ _ sb₀ ph c I A n he hb0 =>
          by_cases hbb : sb = sb₀
          · subst hbb
            have h2 : (Function.update s₀.BM sb ⟨i :: I, A, some n, ph⟩ sb).phase
                = (s₀.BM sb).phase := by
              simp [Function.update_self, hb0]
            exact h2
          · have h2 : (Function.update s₀.BM sb₀ ⟨i :: I, A, some n, ph⟩ sb).phase
                = (s₀.BM sb).phase := by
              rw [Function.update_of_ne hbb]
            exact h2
  | @recycle s₀ T nb₀ I A n hb hfull hpark =>
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
      subst hs; subst hs'
      rfl
  | @mb_recycle s₀ T sb₀ I A n ph₀ hb hfull hpark =>
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
      subst hs; subst hs'
      by_cases hbb : sb = sb₀
      · -- this *is* a recycle of `sb`: contradicts `h`
        exfalso
        subst hbb
        have hrec : stepRecyclesBarrier (.inr sb) (Config.run s₀ T)
            (Config.run
              { s₀ with E := updateMapOn s₀.E I true,
                        BM := Function.update s₀.BM sb ⟨[], 0, some n, !ph₀⟩ }
              (T.wake I)) = true := by
          simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
            MBarrierState.isFull, hfull, Function.update_self]
        rw [hrec] at h
        exact absurd h (by simp)
      · have h2 : (Function.update s₀.BM sb₀ ⟨[], 0, some n, !ph₀⟩ sb).phase
            = (s₀.BM sb).phase := by
          rw [Function.update_of_ne hbb]
        exact h2
  | @done s₀ T hdone _ _ =>
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
      subst hs; subst hs'
      rfl
  | @error s₀ T i P' _ _ hth =>
      simp [WeftCommon.Config.state?] at hs'

/-- **The phase invariant**: along any trace from the initial configuration, an
mbarrier's phase is the parity of its recycle count (`phaseAfter`) — phases
start at `0` and each recycle flips exactly one of them. This is what pins the
§5.2.3 phase test of a wait's observed generation to the actual dynamics. -/
theorem phase_eq_phaseAfter {T : CTA} {τ : List Config}
    (hchain : List.IsChain CTAStep τ) (h0 : τ[0]? = some (Config.run State.initial T))
    (sb : SharedBarrier) :
    ∀ (j : Nat) (C : Config) (s : State), τ[j]? = some C → C.state? = some s →
      (s.BM sb).phase = phaseAfter (recycleCount (.inr sb) τ j) := by
  intro j
  induction j with
  | zero =>
      intro C s hC hs
      rw [h0] at hC; obtain rfl := Option.some.inj hC
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
      subst hs
      have hrc : recycleCount (.inr sb) τ 0 = 0 := by unfold recycleCount; simp
      rw [hrc]
      rfl
  | succ p ih =>
      intro C s hC hs
      have hplt : p < τ.length := by
        have := (List.getElem?_eq_some_iff.mp hC).1; omega
      have hCp : τ[p]? = some τ[p] := List.getElem?_eq_getElem hplt
      have hstep := chain_step hchain hCp hC
      obtain ⟨sp, Tp, hrun⟩ := hstep.source_run
      have hsp : τ[p].state? = some sp := by rw [hrun]; rfl
      have hprev := ih τ[p] sp hCp hsp
      cases hrec : stepRecyclesBarrier (.inr sb) τ[p] C with
      | true =>
          have hphase := phase_of_recycle hrec hsp hs
          have hrc := recycleCount_succ_of_recycle _ τ hCp hC hrec
          rw [hphase, hprev, hrc, phaseAfter_succ]
      | false =>
          have hphase := phase_of_not_recycle hstep hrec hsp hs
          have hrc := recycleCount_succ_of_not_recycle _ hCp hC hrec
          rw [hphase, hprev, hrc]

/-- A `sync_nb`'s execution step *is* a recycle of its barrier: at the step `n`
where a `sync_nb nb nn` command runs, the transition `τ[n-1] ⤳ τ[n]` recycles
`nb`. -/
theorem sync_time_recycles {C₀ : Config} {τ : List Config} {η : ProgPoint} {n : Nat}
    {nb : NamedBarrier} {nn : ℕ+} (hm : IsTimeOf C₀ τ η n)
    (hcmd : η.cmd C₀ = some (Cmd.sync_nb nb nn)) :
    ∃ C C', τ[n - 1]? = some C ∧ τ[n]? = some C' ∧
      stepRecyclesBarrier (.inl nb) C C' = true := by
  obtain ⟨hτ, hidxL, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := hm
  subst hn
  refine ⟨C, C', by rw [show j + 1 - 1 = j by omega]; exact hCj, hCj1, ?_⟩
  have hstep : CTAStep C C' := chain_step hτ.1.subtrace hCj hCj1
  have hhead : (C₀.progOf η.thread)[η.idx]'hidxL = Cmd.sync_nb nb nn := by
    have hc := hcmd
    simp only [ProgPoint.cmd] at hc
    rw [List.getElem?_eq_getElem hidxL, Option.some.injEq] at hc
    exact hc
  have hCsync : C.progOf η.thread = Cmd.sync_nb nb nn :: C'.progOf η.thread := by
    rw [hCeq, hC'eq, List.drop_eq_getElem_cons hidxL, hhead]
  exact sync_drop_recycles hstep hCsync rfl

/-- A `wait_mb`'s execution step either recycles its barrier (the wait was
blocked and is being woken) or is a pass at a mismatched phase. -/
theorem wait_time_recycles_or_pass {C₀ : Config} {τ : List Config} {η : ProgPoint}
    {n : Nat} {sb : SharedBarrier} {ph : Phase} (hm : IsTimeOf C₀ τ η n)
    (hcmd : η.cmd C₀ = some (Cmd.wait_mb sb ph)) :
    (∃ C C', τ[n - 1]? = some C ∧ τ[n]? = some C' ∧
      stepRecyclesBarrier (.inr sb) C C' = true) ∨
    (∃ s T, τ[n - 1]? = some (Config.run s T) ∧ s.E η.thread = true ∧
      (s.BM sb).phase ≠ ph) := by
  obtain ⟨hτ, hidxL, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := hm
  subst hn
  have hstep : CTAStep C C' := chain_step hτ.1.subtrace hCj hCj1
  have hhead : (C₀.progOf η.thread)[η.idx]'hidxL = Cmd.wait_mb sb ph := by
    have hc := hcmd
    simp only [ProgPoint.cmd] at hc
    rw [List.getElem?_eq_getElem hidxL, Option.some.injEq] at hc
    exact hc
  have hCwait : C.progOf η.thread = Cmd.wait_mb sb ph :: C'.progOf η.thread := by
    rw [hCeq, hC'eq, List.drop_eq_getElem_cons hidxL, hhead]
  rcases wait_drop_recycles_or_pass hstep hCwait rfl with hrec | ⟨s, T, hCrun, hE, hph⟩
  · exact Or.inl ⟨C, C',
      by rw [show j + 1 - 1 = j by omega]; exact hCj, hCj1, hrec⟩
  · exact Or.inr ⟨s, T,
      by rw [show j + 1 - 1 = j by omega]; rw [hCrun] at hCj; exact hCj, hE, hph⟩

/-- Reading a generation off `IsGenOf` at a known time: if `η`'s command is `c`
on barrier `b` and it executes at `m`, its generation is
`c.genValue (recycleCount b τ (m - 1))`. -/
theorem isGenOf_genValue {C₀ : Config} {τ : List Config} {η : ProgPoint} {g : ℤ}
    {c : Cmd} {b : NamedBarrier ⊕ SharedBarrier} {m : Nat}
    (hgen : IsGenOf C₀ τ η (some g)) (hc : η.cmd C₀ = some c)
    (hb : c.barrier? = some b) (hm : IsTimeOf C₀ τ η m) :
    g = c.genValue (recycleCount b τ (m - 1)) := by
  obtain ⟨_, c', hc', b', hb', hcase⟩ := hgen
  rw [hc] at hc'; obtain rfl := Option.some.inj hc'
  rw [hb] at hb'; obtain rfl := Option.some.inj hb'
  rcases hcase with ⟨m', hm', hg⟩ | ⟨hnone, hno⟩
  · rw [Option.some.inj hg, IsTimeOf.unique hm hm']
  · exact absurd ⟨m, hm⟩ hno

/-- A named-barrier command's generation value is the plain recycle count
(the §5.2.3 wait correction only applies to `wait_mb`). -/
theorem Cmd.genValue_of_inl {c : Cmd} {nb : NamedBarrier}
    (h : c.barrier? = some (.inl nb)) (r : Nat) : c.genValue r = (r : ℤ) := by
  cases c with
  | read g => simp [Cmd.barrier?] at h
  | write g => simp [Cmd.barrier?] at h
  | arrive_nb nb' n => rfl
  | sync_nb nb' n => rfl
  | init_mb sb n => simp [Cmd.barrier?] at h
  | arrive_mb sb => simp [Cmd.barrier?] at h
  | wait_mb sb ph => simp [Cmd.barrier?] at h

/-- Definition 7 (§4.1) for the mbarrier-extended language: the shared
`WeftCommon.WellSynchronized` at this language's step relation, barrier
classifier, and (`ℤ`-valued, §5.2.3-corrected) generation relation. -/
abbrev Config.WellSynchronized (C₀ : Config) : Prop :=
  WeftCommon.WellSynchronized CTAStep Cmd.barrier? IsGenOf C₀

/-- Definition 6 (§4.1). A CTA `T` is *well-synchronized* if the configuration
`(I, T)` is — i.e. Definition 7 at the initial state `I = State.initial`. -/
def CTA.WellSynchronized (T : CTA) : Prop :=
  Config.WellSynchronized (Config.run State.initial T)

/-! ### Well-synchronized configurations terminate cleanly (Definition 6, §4.1)

Every complete trace from a well-synchronized, well-formed `run` configuration
ends in `done`: an `err` ending or a deadlock each expose a synchronization
command that never executes, and well-synchronization assigns every
synchronization command a `some` generation — in particular it executes. -/

/-- The shared core of the `err`/deadlock cases: a thread `t` whose program at the
last configuration is headed by a synchronization command yields a sync program
point that never executes. -/
theorem unexec_sync_of_last {C₀ Cₙ : Config} {τ : List Config} {t : ThreadId}
    {cmd : Cmd} {c : Prog} {b : NamedBarrier ⊕ SharedBarrier}
    (hτ : IsCompleteTraceFrom C₀ τ) (hlast : τ.getLast? = some Cₙ) (hC₀mem : C₀ ∈ τ)
    (hCn : Cₙ.progOf t = cmd :: c) (hb : cmd.barrier? = some b) :
    ∃ η : ProgPoint, (∃ b', (η.cmd C₀).bind Cmd.barrier? = some b') ∧
      ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hsuf : Cₙ.progOf t <:+ C₀.progOf t :=
    CTAStep.suffix_last t hτ.1.subtrace hlast C₀ hC₀mem
  refine ⟨ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length), ⟨b, ?_⟩, ?_⟩
  · rw [cmd_at_last hsuf hCn]; exact hb
  · refine noTime_at_last hτ hlast ?_ (suffix_length_le hsuf)
    rw [hCn]; simp

/-- A complete trace from a `run` configuration that ends in `err` contains a
synchronization command that never executes (the one that triggered the error) —
all five error productions are triggered by barrier commands. -/
theorem err_has_unexec_sync {C₀ : Config} {τ : List Config} {T : CTA}
    (hτ : IsCompleteTraceFrom C₀ τ) (hrun : ∃ s T₀, C₀ = Config.run s T₀)
    (hlast : τ.getLast? = some (Config.err T)) :
    ∃ η : ProgPoint, (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) ∧
      ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hC₀mem : C₀ ∈ τ := List.mem_of_mem_head? hτ.2
  obtain ⟨y, hstep⟩ : ∃ y, CTAStep y (Config.err T) := by
    rcases step_into_getLast hτ.1.subtrace hlast with hhead | h
    · exfalso
      rw [hτ.2] at hhead
      obtain ⟨s, T₀, rfl⟩ := hrun
      simp at hhead
    · exact h
  cases hstep with
  | @error s _ i P' _ _ hth =>
    generalize hp : T.prog i = P at hth
    cases hth with
    | sync_err_count _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | arrive_err_count _ _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | mb_init_err _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | mb_arrive_err _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl
    | mb_wait_err _ _ => exact unexec_sync_of_last hτ hlast hC₀mem hp rfl

/-- Well-synchronization rules out an unexecuted synchronization command: it
assigns every sync command a `some` generation, but an unexecuted one relates
only to `none`. -/
theorem wellSync_no_unexec_sync {C₀ : Config} (h : C₀.WellSynchronized)
    {τ : List Config} (hτ : IsCompleteTraceFrom C₀ τ) {η : ProgPoint}
    (hηsync : ∃ b, (η.cmd C₀).bind Cmd.barrier? = some b)
    (hηnoexec : ¬ ∃ m, IsTimeOf C₀ τ η m) : False := by
  obtain ⟨g, hgen, _⟩ := h.2 τ τ hτ hτ η hηsync
  obtain ⟨_, c, _, b, _, hcase⟩ := hgen
  rcases hcase with ⟨m, hm, _⟩ | ⟨hg, _⟩
  · exact hηnoexec ⟨m, hm⟩
  · exact nomatch hg

/-- A stuck `run` configuration (well-formed) has a thread headed by a
synchronization command — a thread parked at a `sync_nb`/`wait_mb`, or one
about to register. -/
theorem stuck_has_sync_head {s : State} {T : CTA}
    (hwf : (Config.WF (Config.run s T)))
    (hstuck : Config.Stuck (Config.run s T)) :
    ∃ t cmd c b, T.prog t = cmd :: c ∧ cmd.barrier? = some b := by
  by_contra hcon
  push Not at hcon
  -- No named barrier is left full: a full one would let `recycle` fire (its
  -- synced list empty) or expose a parked `sync_nb` head (contradicting `hcon`).
  have hbar : ∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
      ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
    intro nb
    obtain ⟨bI, bA, bcnt, hbc⟩ : ∃ bI bA bcnt, s.BN nb = ⟨bI, bA, bcnt⟩ := ⟨_, _, _, rfl⟩
    cases bcnt with
    | none =>
      obtain ⟨rfl, rfl⟩ := hwf.2.1 nb bI bA hbc
      exact Or.inl hbc
    | some n =>
      obtain ⟨hle, hpark, _⟩ := hwf.1 nb bI bA n hbc
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
            exact hcon i₀ x t (.inl nb) hp (by rw [hpk]; rfl)
  -- No mbarrier is left full in arrivals: symmetric via `mb_recycle`.
  have hmbar : ∀ sb, s.BM sb = MBarrierState.uninitialized ∨
      ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat) := by
    intro sb
    obtain ⟨bI, bA, bcnt, bph, hbc⟩ : ∃ bI bA bcnt bph, s.BM sb = ⟨bI, bA, bcnt, bph⟩ :=
      ⟨_, _, _, _, rfl⟩
    cases bcnt with
    | none =>
      obtain ⟨rfl, rfl, rfl⟩ := hwf.2.2.2.1 sb bI bA bph hbc
      exact Or.inl hbc
    | some n =>
      obtain ⟨hle, hpark⟩ := hwf.2.2.1 sb bI bA n bph hbc
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr ⟨bI, bA, n, bph, hbc, hlt⟩
      · exfalso
        cases bI with
        | nil => exact hstuck ⟨_, CTAStep.mb_recycle hbc heq (by simp)⟩
        | cons i₀ rest =>
          have hpk := hpark i₀ (by simp)
          cases hp : T.prog i₀ with
          | nil => rw [hp] at hpk; simp at hpk
          | cons x t =>
            rw [hp] at hpk
            simp only [List.head?_cons, Option.some.injEq] at hpk
            exact hcon i₀ x t (.inr sb) hp (by rw [hpk]; rfl)
  -- Neither kind full ⟹ the `done` premises hold.
  have hnofull : ∀ nb I A n, s.BN nb = ⟨I, A, some n⟩ → I.length + A < (n : Nat) := by
    intro nb I A n hb
    rcases hbar nb with hu | ⟨I', A', n', hb', hlt⟩
    · rw [hb] at hu; simp [NamedBarrierState.unconfigured] at hu
    · rw [hb] at hb'
      simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hb'
      obtain ⟨rfl, rfl, rfl⟩ := hb'
      exact hlt
  have hmbnofull : ∀ sb I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ → A < (n : Nat) := by
    intro sb I A n ph hb
    rcases hmbar sb with hu | ⟨I', A', n', ph', hb', hlt⟩
    · rw [hb] at hu; simp [MBarrierState.uninitialized] at hu
    · rw [hb] at hb'
      simp only [MBarrierState.mk.injEq, Option.some.injEq] at hb'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
      exact hlt
  by_cases hd : CTA.IsDone T
  · exact hstuck ⟨_, CTAStep.done hd hnofull hmbnofull⟩
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
      exact ⟨_, CTAStep.interleave ht₀ids hbar hmbar
        (by rw [hcmd₀]; exact ThreadStep.read_noop)⟩
    | write g =>
      exact ⟨_, CTAStep.interleave ht₀ids hbar hmbar
        (by rw [hcmd₀]; exact ThreadStep.write_noop)⟩
    | arrive_nb nb n => simp [Cmd.barrier?] at hbar0
    | sync_nb nb n => simp [Cmd.barrier?] at hbar0
    | init_mb sb n => simp [Cmd.barrier?] at hbar0
    | arrive_mb sb => simp [Cmd.barrier?] at hbar0
    | wait_mb sb ph => simp [Cmd.barrier?] at hbar0

/-- A complete trace from a *well-formed* `run` configuration that ends in a deadlock
(a stuck `run` configuration) contains a synchronization command that never
executes. -/
theorem deadlock_has_unexec_sync {C₀ : Config} {τ : List Config} {s : State} {T : CTA}
    (hτ : IsCompleteTraceFrom C₀ τ) (hC₀wf : C₀.WF)
    (hlast : τ.getLast? = some (Config.run s T)) (hstuck : Config.Stuck (Config.run s T)) :
    ∃ η : ProgPoint,
      (∃ b, (η.cmd C₀).bind Cmd.barrier? = some b) ∧
      ¬ ∃ m, IsTimeOf C₀ τ η m := by
  have hwf := WF_chain hτ.1.subtrace hτ.2 hC₀wf _ (List.mem_of_mem_getLast? hlast)
  obtain ⟨t, cmd, c, b, hTprog, hbb⟩ := stuck_has_sync_head hwf hstuck
  exact unexec_sync_of_last hτ hlast (List.mem_of_mem_head? hτ.2) hTprog hbb

/-- Definition 6 (§4.1) for the mbarrier-extended language, at an arbitrary
*well-formed* start configuration: every complete trace from a well-synchronized,
well-formed `run` configuration ends in `done`. -/
theorem Config.WellSynchronized.completeTrace_ends_done {s₀ : State} {T₀ : CTA}
    (h : (Config.WellSynchronized (Config.run s₀ T₀)))
    (hwf : (Config.WF (Config.run s₀ T₀))) {τ : List Config}
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
      · simp at hd
      · simp at he
      · exact hs
    obtain ⟨η, hηsync, hηnoexec⟩ := deadlock_has_unexec_sync hτ hwf hlast hstuck
    exact wellSync_no_unexec_sync h hτ hηsync hηnoexec

/-- Definition 6 (§4.1) at the initial configuration: every complete trace of a
well-synchronized CTA ends in `done`. -/
theorem CTA.WellSynchronized.completeTrace_ends_done {T : CTA}
    (h : T.WellSynchronized) {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ) :
    ∃ s, τ.getLast? = some (Config.done s) :=
  Config.WellSynchronized.completeTrace_ends_done h WF_initial hτ

/-! ### Existence of a complete trace (strong normalization)

The machine strongly normalizes: programs are finite straight-line code, so a
complete trace exists from every configuration. The measure

`μ(s, T) = 3·(remaining commands) + 2·(enabled threads) + (configured barriers)
+ (pending arrivals) + 1`

strictly decreases on every `CTAStep`. The pending-arrivals term (absent from
the named-barrier development) is what covers `mb_recycle`: unlike the named
`recycle` it keeps its barrier configured, so with an empty waiter list nothing
else changes — but it resets `arrived` from `n ≥ 1` to `0`. Both counted terms
range over a fixed finite support `S`; the invariant `Config.barriersWithin S`
keeps them meaningful and is preserved by every step. -/

/-- Number of currently enabled threads. -/
def State.numEnabled (s : State) (T : CTA) : Nat := (T.ids.filter (fun i => s.E i)).card

/-- Whether barrier `b` — of either kind — is configured/initialized. -/
def State.configuredOf (s : State) : NamedBarrier ⊕ SharedBarrier → Bool
  | .inl nb => (s.BN nb).count.isSome
  | .inr sb => (s.BM sb).count.isSome

/-- The arrived count of barrier `b` — of either kind. -/
def State.arrivedOf (s : State) : NamedBarrier ⊕ SharedBarrier → Nat
  | .inl nb => (s.BN nb).arrived
  | .inr sb => (s.BM sb).arrived

/-- `configuredOf` depends only on the barrier maps at `b`'s own key. -/
theorem State.configuredOf_eq {s s' : State} {b : NamedBarrier ⊕ SharedBarrier}
    (hBN : ∀ nb, b = .inl nb → s'.BN nb = s.BN nb)
    (hBM : ∀ sb, b = .inr sb → s'.BM sb = s.BM sb) :
    s'.configuredOf b = s.configuredOf b := by
  cases b with
  | inl nb =>
    change (s'.BN nb).count.isSome = (s.BN nb).count.isSome
    rw [hBN nb rfl]
  | inr sb =>
    change (s'.BM sb).count.isSome = (s.BM sb).count.isSome
    rw [hBM sb rfl]

/-- `arrivedOf` depends only on the barrier maps at `b`'s own key. -/
theorem State.arrivedOf_eq {s s' : State} {b : NamedBarrier ⊕ SharedBarrier}
    (hBN : ∀ nb, b = .inl nb → s'.BN nb = s.BN nb)
    (hBM : ∀ sb, b = .inr sb → s'.BM sb = s.BM sb) :
    s'.arrivedOf b = s.arrivedOf b := by
  cases b with
  | inl nb =>
    change (s'.BN nb).arrived = (s.BN nb).arrived
    rw [hBN nb rfl]
  | inr sb =>
    change (s'.BM sb).arrived = (s.BM sb).arrived
    rw [hBM sb rfl]

/-- Number of configured barriers within the finite support `S`. -/
def State.numConfigured (s : State) (S : Finset (NamedBarrier ⊕ SharedBarrier)) : Nat :=
  (S.filter (fun b => s.configuredOf b = true)).card

/-- Total pending arrivals within the finite support `S`. -/
def State.numArrived (s : State) (S : Finset (NamedBarrier ⊕ SharedBarrier)) : Nat :=
  ∑ b ∈ S, s.arrivedOf b

/-- The strong-normalization measure (see the section doc). `done`/`err` are
terminal; the `+1` on `run` keeps `μ(run) ≥ 1 > 0 = μ(done) = μ(err)`, so the
`done`/`error` steps strictly decrease it too. -/
def Config.cfgMeasure (S : Finset (NamedBarrier ⊕ SharedBarrier)) : Config → Nat
  | .run s T => 3 * WeftCommon.CTA.numCmds T + 2 * s.numEnabled T
      + s.numConfigured S + s.numArrived S + 1
  | .done _ => 0
  | .err _ => 0

/-- The finite set of barriers — of both kinds — mentioned by a CTA's programs:
a support containing every barrier that could ever be configured along an
execution. -/
def CTA.barrierSet (T : CTA) : Finset (NamedBarrier ⊕ SharedBarrier) :=
  T.ids.biUnion (fun i => ((T.prog i).filterMap Cmd.barrier?).toFinset)

/-- Support invariant: every configured barrier, and every barrier mentioned by a
thread's remaining program, lies in `S`. Vacuous for `done`/`err`. -/
def Config.barriersWithin (S : Finset (NamedBarrier ⊕ SharedBarrier)) : Config → Prop
  | .run s T =>
      (∀ b, s.configuredOf b = true → b ∈ S) ∧
      (∀ i, ∀ c ∈ T.prog i, ∀ b, c.barrier? = some b → b ∈ S)
  | _ => True

/-- The support invariant holds at the initial configuration with
`S = T.barrierSet`. -/
theorem barriersWithin_initial {T : CTA} :
    (Config.barriersWithin T.barrierSet (Config.run State.initial T)) := by
  refine ⟨fun b hb => ?_, fun i c hc b hbc => ?_⟩
  · exfalso
    cases b with
    | inl nb =>
      have : ((State.initial.BN nb).count).isSome = true := hb
      simp [State.initial, NamedBarrierState.unconfigured] at this
    | inr sb =>
      have : ((State.initial.BM sb).count).isSome = true := hb
      simp [State.initial, MBarrierState.uninitialized] at this
  · have hi : i ∈ T.ids := by
      by_contra hni; rw [T.nil_outside_ids i hni] at hc; simp at hc
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨c, hc, hbc⟩

/-- Updating one thread's program changes the command count by the length
difference (stated additively to avoid `Nat` subtraction). -/
theorem numCmds_set {T : CTA} {i : ThreadId} (hi : i ∈ T.ids) (P' : Prog) :
    WeftCommon.CTA.numCmds (T.set i hi P') + (T.prog i).length = T.numCmds + P'.length := by
  have hset : ∀ j, ((T.set i hi P').prog j).length
      = Function.update (fun k => (T.prog k).length) i P'.length j := by
    intro j
    by_cases h : j = i
    · subst h; simp [WeftCommon.CTA.set]
    · simp [WeftCommon.CTA.set, Function.update_of_ne h]
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

/-- Waking the threads `I` (each with a nonempty program) drops the command
count by one per woken in-domain thread. -/
theorem numCmds_wake {T : CTA} {I : List ThreadId}
    (hpark : ∀ i ∈ I, (T.prog i).head?.isSome) :
    T.numCmds = WeftCommon.CTA.numCmds (T.wake I) + (T.ids.filter (· ∈ I)).card := by
  have key : ∀ j ∈ T.ids, (T.prog j).length
      = ((T.wake I).prog j).length + (if j ∈ I then 1 else 0) := by
    intro j _
    simp only [WeftCommon.CTA.wake]
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

/-! #### Counting under a one-point change

The step rules touch the barrier maps at one key. These generic helpers turn
"the predicate/weight agrees off `b₀`" plus the value change at `b₀` into the
filter-card / sum change. -/

/-- Predicates agreeing off `b₀`: the filtered card grows by at most one. -/
theorem card_filter_le_of_agree {S : Finset (NamedBarrier ⊕ SharedBarrier)}
    {f g : NamedBarrier ⊕ SharedBarrier → Bool} {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hoff : ∀ b ∈ S, b ≠ b₀ → g b = f b) :
    (S.filter (fun b => g b = true)).card ≤ (S.filter (fun b => f b = true)).card + 1 := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le b₀ _)
  intro b hb
  rw [Finset.mem_filter] at hb
  obtain ⟨hbS, hbg⟩ := hb
  by_cases h : b = b₀
  · subst h; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hbS, by rw [← hoff b hbS h]; exact hbg⟩)

/-- Predicates agreeing off `b₀` and at `b₀`: equal filtered cards. -/
theorem card_filter_eq_of_agree {S : Finset (NamedBarrier ⊕ SharedBarrier)}
    {f g : NamedBarrier ⊕ SharedBarrier → Bool} {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hoff : ∀ b ∈ S, b ≠ b₀ → g b = f b) (hb₀ : g b₀ = f b₀) :
    (S.filter (fun b => g b = true)).card = (S.filter (fun b => f b = true)).card := by
  congr 1
  ext b
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hbS, hbg⟩
    refine ⟨hbS, ?_⟩
    by_cases h : b = b₀
    · subst h; rw [← hb₀]; exact hbg
    · rw [← hoff b hbS h]; exact hbg
  · rintro ⟨hbS, hbf⟩
    refine ⟨hbS, ?_⟩
    by_cases h : b = b₀
    · subst h; rw [hb₀]; exact hbf
    · rw [hoff b hbS h]; exact hbf

/-- Predicates agreeing off `b₀ ∈ S`, with `b₀` flipping `true → false`: the
filtered card drops by exactly one. -/
theorem card_filter_pred_of_agree {S : Finset (NamedBarrier ⊕ SharedBarrier)}
    {f g : NamedBarrier ⊕ SharedBarrier → Bool} {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hoff : ∀ b ∈ S, b ≠ b₀ → g b = f b)
    (hb₀S : b₀ ∈ S) (hg : g b₀ = false) (hf : f b₀ = true) :
    (S.filter (fun b => g b = true)).card + 1 = (S.filter (fun b => f b = true)).card := by
  have hb₀f : b₀ ∈ S.filter (fun b => f b = true) := Finset.mem_filter.mpr ⟨hb₀S, hf⟩
  rw [show S.filter (fun b => g b = true)
        = (S.filter (fun b => f b = true)).erase b₀ from ?_]
  · rw [Finset.card_erase_of_mem hb₀f]
    have := Finset.card_pos.mpr ⟨b₀, hb₀f⟩
    omega
  · ext b
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hbS, hbg⟩
      have hb : b ≠ b₀ := by
        rintro rfl; rw [hg] at hbg; exact absurd hbg (by simp)
      exact ⟨hb, hbS, by rw [← hoff b hbS hb]; exact hbg⟩
    · rintro ⟨hb, hbS, hbf⟩
      exact ⟨hbS, by rw [hoff b hbS hb]; exact hbf⟩

/-- Weights agreeing off `b₀ ∈ S`: the sums differ exactly by the two values at
`b₀` (stated additively). -/
theorem sum_agree_add {S : Finset (NamedBarrier ⊕ SharedBarrier)}
    {f g : NamedBarrier ⊕ SharedBarrier → Nat} {b₀ : NamedBarrier ⊕ SharedBarrier}
    (hoff : ∀ b ∈ S, b ≠ b₀ → g b = f b) (hb₀S : b₀ ∈ S) :
    (∑ b ∈ S, g b) + f b₀ = (∑ b ∈ S, f b) + g b₀ := by
  have hs : ∑ b ∈ S.erase b₀, g b = ∑ b ∈ S.erase b₀, f b :=
    Finset.sum_congr rfl fun b hb =>
      hoff b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
  rw [← Finset.add_sum_erase S g hb₀S, ← Finset.add_sum_erase S f hb₀S, hs]
  omega

/-- Weights agreeing off `b₀`, growing by at most `k` at `b₀`: the sum grows by
at most `k`. -/
theorem sum_agree_le {S : Finset (NamedBarrier ⊕ SharedBarrier)}
    {f g : NamedBarrier ⊕ SharedBarrier → Nat} {b₀ : NamedBarrier ⊕ SharedBarrier} {k : Nat}
    (hoff : ∀ b ∈ S, b ≠ b₀ → g b = f b) (hb₀ : g b₀ ≤ f b₀ + k) :
    (∑ b ∈ S, g b) ≤ (∑ b ∈ S, f b) + k := by
  by_cases hb₀S : b₀ ∈ S
  · have := sum_agree_add hoff hb₀S
    omega
  · rw [Finset.sum_congr rfl fun b hb => hoff b hb (fun h => hb₀S (h ▸ hb))]
    exact Nat.le_add_right _ _

/-- Every `CTAStep` strictly decreases the measure: the machine strongly
normalizes. Per-rule accounting (`cmds`/`enabled`/`configured`/`arrived`):
advancing rules drop a command (`−3`, at worst `+1` configured and `+1`
arrived); parking rules disable the stepping thread (`−2`); `recycle` clears
one barrier (`−1` configured); `mb_recycle` keeps its barrier configured but
resets `arrived` from `n ≥ 1` to `0` (`≤ −1`). -/
theorem step_decreases (S : Finset (NamedBarrier ⊕ SharedBarrier)) {C C' : Config}
    (hstep : CTAStep C C') (hinv : C.barriersWithin S) :
    C'.cfgMeasure S < C.cfgMeasure S := by
  cases hstep with
  | @done s T hdone _ _ => simp only [Config.cfgMeasure]; omega
  | @error s T i P' _ _ hth => simp only [Config.cfgMeasure]; omega
  | @interleave s s' T i P' hi hbar hmbar hth =>
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
    | @arrive_configure _ _ nb n _ he hb0 =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with BN := Function.update s.BN nb ⟨[], 1, some n⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.configuredOf {s with BN := Function.update s.BN nb ⟨[], 1, some n⟩} b
            = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.arrivedOf {s with BN := Function.update s.BN nb ⟨[], 1, some n⟩} b
            = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hCf : ({s with BN := Function.update s.BN nb ⟨[], 1, some n⟩} : State).numConfigured S
          ≤ s.numConfigured S + 1 := card_filter_le_of_agree hoffC
      have hAr : ({s with BN := Function.update s.BN nb ⟨[], 1, some n⟩} : State).numArrived S
          ≤ s.numArrived S + 1 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BN nb ⟨[], 1, some n⟩ nb).arrived ≤ (s.BN nb).arrived + 1
        rw [Function.update_self]
        change (1 : Nat) ≤ (s.BN nb).arrived + 1
        omega
      simp only [Config.cfgMeasure, hE]; omega
    | @arrive_register _ _ nb n _ I A he hb0 hpos hlt =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.configuredOf {s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩} b
            = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.arrivedOf {s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩} b
            = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hCf : ({s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩} : State).numConfigured S
          = s.numConfigured S := by
        refine card_filter_eq_of_agree hoffC ?_
        change (Function.update s.BN nb ⟨I, A + 1, some n⟩ nb).count.isSome
          = (s.BN nb).count.isSome
        rw [Function.update_self, hb0]
      have hAr : ({s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩} : State).numArrived S
          ≤ s.numArrived S + 1 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BN nb ⟨I, A + 1, some n⟩ nb).arrived ≤ (s.BN nb).arrived + 1
        rw [Function.update_self, hb0]
      simp only [Config.cfgMeasure, hE, hCf]; omega
    | @sync_configure _ _ nb n c he hb0 =>
      set s' : State := ⟨Function.update s.E i false,
        Function.update s.BN nb ⟨[i], 0, some n⟩, s.BM⟩ with hs'def
      have h1 := numCmds_set hi (Cmd.sync_nb nb n :: c)
      have h2 : (T.prog i).length = (Cmd.sync_nb nb n :: c).length := by rw [hpi]
      have hE : s'.numEnabled (T.set i hi (Cmd.sync_nb nb n :: c)) + 1 = s.numEnabled T :=
        numEnabled_update_false hi he
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.configuredOf s' b = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.arrivedOf s' b = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hCf : s'.numConfigured S ≤ s.numConfigured S + 1 := card_filter_le_of_agree hoffC
      have hAr : s'.numArrived S ≤ s.numArrived S + 0 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BN nb ⟨[i], 0, some n⟩ nb).arrived ≤ (s.BN nb).arrived + 0
        rw [Function.update_self]
        change (0 : Nat) ≤ (s.BN nb).arrived + 0
        omega
      simp only [Config.cfgMeasure]; omega
    | @sync_block _ _ nb n c I A he hb0 hpos hlt =>
      set s' : State := ⟨Function.update s.E i false,
        Function.update s.BN nb ⟨i :: I, A, some n⟩, s.BM⟩ with hs'def
      have h1 := numCmds_set hi (Cmd.sync_nb nb n :: c)
      have h2 : (T.prog i).length = (Cmd.sync_nb nb n :: c).length := by rw [hpi]
      have hE : s'.numEnabled (T.set i hi (Cmd.sync_nb nb n :: c)) + 1 = s.numEnabled T :=
        numEnabled_update_false hi he
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.configuredOf s' b = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inl nb) →
          State.arrivedOf s' b = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq
          (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
          (fun sb' _ => rfl)
      have hCf : s'.numConfigured S = s.numConfigured S := by
        refine card_filter_eq_of_agree hoffC ?_
        change (Function.update s.BN nb ⟨i :: I, A, some n⟩ nb).count.isSome
          = (s.BN nb).count.isSome
        rw [Function.update_self, hb0]
      have hAr : s'.numArrived S ≤ s.numArrived S + 0 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BN nb ⟨i :: I, A, some n⟩ nb).arrived
          ≤ (s.BN nb).arrived + 0
        rw [Function.update_self, hb0]
        change A ≤ A + 0
        omega
      simp only [Config.cfgMeasure, hCf]; omega
    | @mb_init _ _ sb n _ he hb0 =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.configuredOf {s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩} b
            = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.arrivedOf {s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩} b
            = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hCf : State.numConfigured
            {s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩} S
          ≤ s.numConfigured S + 1 := card_filter_le_of_agree hoffC
      have hAr : State.numArrived
            {s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩} S
          ≤ s.numArrived S + 0 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BM sb ⟨[], 0, some n, false⟩ sb).arrived
          ≤ (s.BM sb).arrived + 0
        rw [Function.update_self]
        change (0 : Nat) ≤ (s.BM sb).arrived + 0
        omega
      simp only [Config.cfgMeasure, hE]; omega
    | @mb_arrive _ _ sb _ I A n ph he hb0 =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : ({s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩} : State).numEnabled
          (T.set i hi P') = s.numEnabled T := rfl
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.configuredOf {s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩} b
            = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.arrivedOf {s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩} b
            = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hCf : State.numConfigured
            {s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩} S
          = s.numConfigured S := by
        refine card_filter_eq_of_agree hoffC ?_
        change (Function.update s.BM sb ⟨I, A + 1, some n, ph⟩ sb).count.isSome
          = (s.BM sb).count.isSome
        rw [Function.update_self, hb0]
      have hAr : State.numArrived
            {s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩} S
          ≤ s.numArrived S + 1 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BM sb ⟨I, A + 1, some n, ph⟩ sb).arrived
          ≤ (s.BM sb).arrived + 1
        rw [Function.update_self, hb0]
      simp only [Config.cfgMeasure, hE, hCf]; omega
    | @mb_wait_block _ _ sb ph c I A n he hb0 =>
      set s' : State := ⟨Function.update s.E i false, s.BN,
        Function.update s.BM sb ⟨i :: I, A, some n, ph⟩⟩ with hs'def
      have h1 := numCmds_set hi (Cmd.wait_mb sb ph :: c)
      have h2 : (T.prog i).length = (Cmd.wait_mb sb ph :: c).length := by rw [hpi]
      have hE : s'.numEnabled (T.set i hi (Cmd.wait_mb sb ph :: c)) + 1 = s.numEnabled T :=
        numEnabled_update_false hi he
      have hoffC : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.configuredOf s' b = State.configuredOf s b := fun b _ hb =>
        State.configuredOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hoffA : ∀ b ∈ S, b ≠ (Sum.inr sb) →
          State.arrivedOf s' b = State.arrivedOf s b := fun b _ hb =>
        State.arrivedOf_eq (fun nb' _ => rfl)
          (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
      have hCf : s'.numConfigured S = s.numConfigured S := by
        refine card_filter_eq_of_agree hoffC ?_
        change (Function.update s.BM sb ⟨i :: I, A, some n, ph⟩ sb).count.isSome
          = (s.BM sb).count.isSome
        rw [Function.update_self, hb0]
      have hAr : s'.numArrived S ≤ s.numArrived S + 0 := by
        refine sum_agree_le hoffA ?_
        change (Function.update s.BM sb ⟨i :: I, A, some n, ph⟩ sb).arrived
          ≤ (s.BM sb).arrived + 0
        rw [Function.update_self, hb0]
        change A ≤ A + 0
        omega
      simp only [Config.cfgMeasure, hCf]; omega
    | @mb_wait_pass _ _ sb ph _ I A n ph' he hb0 hnep =>
      have h1 := numCmds_set hi P'
      have h2 : (T.prog i).length = P'.length + 1 := by rw [hpi]; simp
      have hE : s.numEnabled (T.set i hi P') = s.numEnabled T := rfl
      simp only [Config.cfgMeasure, hE]; omega
  | @recycle s T nb I A n hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    set s' : State := ⟨updateMapOn s.E I true,
      Function.update s.BN nb NamedBarrierState.unconfigured, s.BM⟩ with hs'def
    have hbS : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈ S := by
      refine hcfg _ ?_
      change (s.BN nb).count.isSome = true
      rw [hb0]
      rfl
    have hC : T.numCmds = WeftCommon.CTA.numCmds (T.wake I) + (T.ids.filter (· ∈ I)).card :=
      numCmds_wake (fun j hj => by rw [hpark j hj]; rfl)
    have hE : s'.numEnabled (T.wake I) ≤ s.numEnabled T + (T.ids.filter (· ∈ I)).card :=
      numEnabled_updateMapOn_le
    have hoffC : ∀ b ∈ S, b ≠ (Sum.inl nb) →
        State.configuredOf s' b = State.configuredOf s b := fun b _ hb =>
      State.configuredOf_eq
        (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
        (fun sb' _ => rfl)
    have hoffA : ∀ b ∈ S, b ≠ (Sum.inl nb) →
        State.arrivedOf s' b = State.arrivedOf s b := fun b _ hb =>
      State.arrivedOf_eq
        (fun nb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
        (fun sb' _ => rfl)
    have hCf : s'.numConfigured S + 1 = s.numConfigured S := by
      refine card_filter_pred_of_agree hoffC hbS ?_ ?_
      · change (Function.update s.BN nb NamedBarrierState.unconfigured nb).count.isSome = false
        rw [Function.update_self]
        rfl
      · change (s.BN nb).count.isSome = true
        rw [hb0]
        rfl
    have hAr : s'.numArrived S + (s.BN nb).arrived = s.numArrived S
        + (Function.update s.BN nb NamedBarrierState.unconfigured nb).arrived :=
      sum_agree_add hoffA hbS
    rw [Function.update_self] at hAr
    have hAr' : s'.numArrived S ≤ s.numArrived S := by
      have h0 : (NamedBarrierState.unconfigured).arrived = 0 := rfl
      rw [h0] at hAr
      omega
    simp only [Config.cfgMeasure]; omega
  | @mb_recycle s T sb I A n ph hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    set s' : State := ⟨updateMapOn s.E I true, s.BN,
      Function.update s.BM sb ⟨[], 0, some n, !ph⟩⟩ with hs'def
    have hbS : (Sum.inr sb : NamedBarrier ⊕ SharedBarrier) ∈ S := by
      refine hcfg _ ?_
      change (s.BM sb).count.isSome = true
      rw [hb0]
      rfl
    have hC : T.numCmds = WeftCommon.CTA.numCmds (T.wake I) + (T.ids.filter (· ∈ I)).card :=
      numCmds_wake (fun j hj => by rw [hpark j hj]; rfl)
    have hE : s'.numEnabled (T.wake I) ≤ s.numEnabled T + (T.ids.filter (· ∈ I)).card :=
      numEnabled_updateMapOn_le
    have hoffC : ∀ b ∈ S, b ≠ (Sum.inr sb) →
        State.configuredOf s' b = State.configuredOf s b := fun b _ hb =>
      State.configuredOf_eq (fun nb' _ => rfl)
        (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
    have hoffA : ∀ b ∈ S, b ≠ (Sum.inr sb) →
        State.arrivedOf s' b = State.arrivedOf s b := fun b _ hb =>
      State.arrivedOf_eq (fun nb' _ => rfl)
        (fun sb' hbe => Function.update_of_ne (fun h => hb (by rw [hbe, h])) _ _)
    have hCf : s'.numConfigured S = s.numConfigured S := by
      refine card_filter_eq_of_agree hoffC ?_
      change (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb).count.isSome
        = (s.BM sb).count.isSome
      rw [Function.update_self, hb0]
    have hAr : s'.numArrived S + (s.BM sb).arrived = s.numArrived S
        + (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb).arrived :=
      sum_agree_add hoffA hbS
    rw [Function.update_self] at hAr
    have hArr : (s.BM sb).arrived = (n : Nat) := by rw [hb0]; exact hfull
    have hn : 0 < (n : Nat) := n.pos
    rw [hArr] at hAr
    have hAr' : s'.numArrived S + (n : Nat) = s.numArrived S := by
      have h0 : ((⟨[], 0, some n, !ph⟩ : MBarrierState)).arrived = 0 := rfl
      rw [h0] at hAr
      omega
    simp only [Config.cfgMeasure, hCf]; omega

/-- The support invariant `barriersWithin S` is preserved by every step: programs
only shrink (`progOf_drop`), a newly configured barrier is the barrier of the
executed head command, and the recycles never configure anything new. -/
theorem inv_preserved (S : Finset (NamedBarrier ⊕ SharedBarrier)) {C C' : Config}
    (hstep : CTAStep C C') (hinv : C.barriersWithin S) :
    C'.barriersWithin S := by
  cases hstep with
  | @done s T hdone _ _ => trivial
  | @error s T i P' _ _ hth => trivial
  | @interleave s s' T i P' hi hbar hmbar hth =>
    obtain ⟨hcfg, hmen⟩ := hinv
    have hmen' : ∀ j, ∀ c ∈ (T.set i hi P').prog j, ∀ b, c.barrier? = some b → b ∈ S := by
      intro j c hc b hbc
      obtain ⟨d, hd⟩ := (CTAStep.interleave hi hbar hmbar hth).progOf_drop j
      simp only [WeftCommon.Config.progOf] at hd
      rw [hd] at hc
      exact hmen j c (List.mem_of_mem_drop hc) b hbc
    refine ⟨fun b hb => ?_, hmen'⟩
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hcfg b hb
    | write_noop => exact hcfg b hb
    | @arrive_configure _ _ nb _ _ he hb0 =>
      cases b with
      | inr sb' => exact hcfg _ hb
      | inl nb' =>
        by_cases hbb : nb' = nb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inl nb') ?_
          change (Function.update s.BN nb _ nb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @arrive_register _ _ nb _ _ _ _ he hb0 hpos hlt =>
      cases b with
      | inr sb' => exact hcfg _ hb
      | inl nb' =>
        by_cases hbb : nb' = nb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inl nb') ?_
          change (Function.update s.BN nb _ nb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @sync_configure _ _ nb _ _ he hb0 =>
      cases b with
      | inr sb' => exact hcfg _ hb
      | inl nb' =>
        by_cases hbb : nb' = nb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inl nb') ?_
          change (Function.update s.BN nb _ nb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @sync_block _ _ nb _ _ _ _ he hb0 hpos hlt =>
      cases b with
      | inr sb' => exact hcfg _ hb
      | inl nb' =>
        by_cases hbb : nb' = nb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inl nb') ?_
          change (Function.update s.BN nb _ nb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @mb_init _ _ sb _ _ he hb0 =>
      cases b with
      | inl nb' => exact hcfg _ hb
      | inr sb' =>
        by_cases hbb : sb' = sb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inr sb') ?_
          change (Function.update s.BM sb _ sb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @mb_arrive _ _ sb _ _ _ _ _ he hb0 =>
      cases b with
      | inl nb' => exact hcfg _ hb
      | inr sb' =>
        by_cases hbb : sb' = sb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inr sb') ?_
          change (Function.update s.BM sb _ sb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @mb_wait_block _ _ sb _ _ _ _ _ he hb0 =>
      cases b with
      | inl nb' => exact hcfg _ hb
      | inr sb' =>
        by_cases hbb : sb' = sb
        · subst hbb
          exact hmen i _ (by rw [hpi]; exact List.mem_cons_self) _ rfl
        · refine hcfg (.inr sb') ?_
          change (Function.update s.BM sb _ sb').count.isSome = true at hb
          rwa [Function.update_of_ne hbb] at hb
    | @mb_wait_pass _ _ _ _ _ _ _ _ _ he hb0 hnep => exact hcfg b hb
  | @recycle s T nb I A n hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    have hmen' : ∀ j, ∀ c ∈ (T.wake I).prog j, ∀ b, c.barrier? = some b → b ∈ S := by
      intro j c hc b hbc
      obtain ⟨d, hd⟩ := (CTAStep.recycle hb0 hfull hpark).progOf_drop j
      simp only [WeftCommon.Config.progOf] at hd
      rw [hd] at hc
      exact hmen j c (List.mem_of_mem_drop hc) b hbc
    refine ⟨fun b hb => ?_, hmen'⟩
    cases b with
    | inr sb' => exact hcfg _ hb
    | inl nb' =>
      by_cases hbb : nb' = nb
      · subst hbb
        exfalso
        change (Function.update s.BN nb' NamedBarrierState.unconfigured nb').count.isSome
          = true at hb
        rw [Function.update_self] at hb
        exact absurd hb (by simp [NamedBarrierState.unconfigured])
      · refine hcfg (.inl nb') ?_
        change (Function.update s.BN nb _ nb').count.isSome = true at hb
        rwa [Function.update_of_ne hbb] at hb
  | @mb_recycle s T sb I A n ph hb0 hfull hpark =>
    obtain ⟨hcfg, hmen⟩ := hinv
    have hmen' : ∀ j, ∀ c ∈ (T.wake I).prog j, ∀ b, c.barrier? = some b → b ∈ S := by
      intro j c hc b hbc
      obtain ⟨d, hd⟩ := (CTAStep.mb_recycle hb0 hfull hpark).progOf_drop j
      simp only [WeftCommon.Config.progOf] at hd
      rw [hd] at hc
      exact hmen j c (List.mem_of_mem_drop hc) b hbc
    refine ⟨fun b hb => ?_, hmen'⟩
    cases b with
    | inl nb' => exact hcfg _ hb
    | inr sb' =>
      by_cases hbb : sb' = sb
      · subst hbb
        refine hcfg (.inr sb') ?_
        change (s.BM sb').count.isSome = true
        rw [hb0]
        rfl
      · refine hcfg (.inr sb') ?_
        change (Function.update s.BM sb _ sb').count.isSome = true at hb
        rwa [Function.update_of_ne hbb] at hb

/-- Strong normalization yields a complete trace from *every* configuration: run
the machine to a stuck (terminal) state. By well-founded recursion on the measure
`cfgMeasure S`, with the support invariant `barriersWithin S` carried along. -/
theorem exists_completeTrace (S : Finset (NamedBarrier ⊕ SharedBarrier)) (C : Config)
    (hinv : C.barriersWithin S) : ∃ τ, IsCompleteTraceFrom C τ := by
  suffices H : ∀ n C, C.barriersWithin S → C.cfgMeasure S = n →
      ∃ τ, IsCompleteTraceFrom C τ from H _ C hinv rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hinv hn
    by_cases hstuck : Config.Stuck C
    · exact ⟨[C], ⟨List.isChain_singleton C, C, by simp, Or.inr (Or.inr hstuck)⟩, by simp⟩
    · simp only [Config.Stuck, WeftCommon.Config.Stuck, not_not] at hstuck
      obtain ⟨C', hCC'⟩ := hstuck
      have hdec : Config.cfgMeasure S C' < n := hn ▸ step_decreases S hCC' hinv
      obtain ⟨τ', hτ'⟩ := ih _ hdec C' (inv_preserved S hCC' hinv) rfl
      have hτ'ne : τ' ≠ [] := by
        intro h
        rw [h] at hτ'
        simp [IsCompleteTraceFrom, WeftCommon.IsCompleteTraceFrom] at hτ'
      refine ⟨C :: τ', ⟨?_, ?_⟩, by simp⟩
      · change List.IsChain CTAStep (C :: τ')
        rw [List.isChain_cons]
        refine ⟨fun y hy => ?_, hτ'.1.subtrace⟩
        rw [hτ'.2, Option.mem_some_iff] at hy
        exact hy ▸ hCC'
      · obtain ⟨Cₙ, hlast, hcase⟩ := hτ'.1.ends
        exact ⟨Cₙ, by rw [List.getLast?_cons_of_ne_nil hτ'ne]; exact hlast, hcase⟩

end WeftMBarriers
