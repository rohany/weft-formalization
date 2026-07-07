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
