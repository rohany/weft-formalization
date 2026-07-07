/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftNamedBarriers.Traces
import WeftCommon.WellFormedness

/-!
# State well-formedness for the named-barrier language

The reachable-state invariants of the named-barrier semantics — the analogue of
`WeftMBarriers.WellFormedness` — separated from the well-synchronization
development (`WeftNamedBarriers.WellSynchronized`) that consumes them. Each
invariant comes as a definition with its `initial` / step-preservation / chain
lemmas:

* `State.BlockInv` — every barrier's synced list is duplicate-free, every synced
  thread is disabled, and no thread is synced at two barriers at once;
* `State.EnabledInv` — a disabled thread is synced somewhere (so `disabled ⟺
  parked`, with `BlockInv` supplying the converse);
* `Config.WF` — the full well-formedness predicate: configured barriers are
  non-empty, never over-full, and their synced threads are parked at exactly the
  right `sync`; unconfigured barriers are pristine; plus `BlockInv`.

Also here: the state projection `Config.state?` (used by every invariant's
statement) and `CTAStep.source_run` (steps fire from `run` configurations,
letting a step's source state be read off for invariant extraction).
-/

namespace Weft

/-- The state component `(E, B)` of a configuration, if it has one. `run` and
`done` carry a state; the error configuration `err` does not. -/
def Config.state? : Config → Option State
  | .run s _ => some s
  | .done s => some s
  | .err _ => none

export WeftCommon (updateMapOn_apply)

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
theorem WF_initial {T : CTA} : (Config.WF (Config.run State.initial T)) := by
  refine ⟨fun b I A n hB => ?_, fun b I A hB => ?_, State.BlockInv.initial⟩
  · simp [State.initial, BarrierState.unconfigured] at hB
  · simp only [State.initial, BarrierState.unconfigured, BarrierState.mk.injEq] at hB
    exact ⟨hB.1.symm, hB.2.1.symm⟩

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
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
      | write_noop =>
        intro b I A n hB
        obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
        refine ⟨hle, (fun i' hi' => ?_), hpos⟩
        have hne : i' ≠ i := by
          rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
        simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
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
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
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
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          have hne : i' ≠ i := by
            rintro rfl; have := hpark i' hi'; rw [hpi] at this; simp at this
          simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
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
          simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
        · obtain ⟨hle, hpark, hpos⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos⟩
          by_cases hne : i' = i
          · subst hne
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [← hpi]; exact hpark _ hi'
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
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
          · simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
          · by_cases hne : i' = i
            · subst hne; simp only [WeftCommon.CTA.set, Function.update_self, List.head?_cons]
            · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hcpark i' hi'
        · obtain ⟨hle, hpark, hpos'⟩ := hcond b I A n hB
          refine ⟨hle, (fun i' hi' => ?_), hpos'⟩
          by_cases hne : i' = i
          · subst hne
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [← hpi]; exact hpark _ hi'
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hne]; exact hpark i' hi'
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
        simp only [WeftCommon.CTA.wake, if_neg hni]; exact hpk i' hi'
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

end Weft
