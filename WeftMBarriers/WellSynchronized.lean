/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.WellFormedness
import WeftCommon.WellSynchronized

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
      ∃ s T, C = Config.run s T ∧ (s.BM sb).phase ≠ ph := by
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
            exact Or.inr ⟨s, T, rfl, by rw [hb0]; exact fun hcon => hnep hcon.symm⟩
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
    (∃ s T, τ[n - 1]? = some (Config.run s T) ∧ (s.BM sb).phase ≠ ph) := by
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
  rcases wait_drop_recycles_or_pass hstep hCwait rfl with hrec | ⟨s, T, hCrun, hph⟩
  · exact Or.inl ⟨C, C',
      by rw [show j + 1 - 1 = j by omega]; exact hCj, hCj1, hrec⟩
  · exact Or.inr ⟨s, T,
      by rw [show j + 1 - 1 = j by omega]; rw [hCrun] at hCj; exact hCj, hph⟩

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

end WeftMBarriers
