/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.Language
import WeftMBarriers.State
import WeftMBarriers.Semantics
import WeftMBarriers.Traces
import WeftMBarriers.WellFormedness
import WeftMBarriers.WellSynchronized
import WeftMBarriers.CheckWellSynchronized

/-!
# Weft++ with shared-memory barriers — public interface

The extension of the named-barrier language with shared-memory barriers
(mbarriers), per §5.2 of the weft++ theorems document. This facade states the
headline theorems for the combined language, mirroring `WeftNamedBarriers.lean`:

* `soundAndPrecise_happensBefore` — Algorithm 2's happens-before relation is
  sound and precise for well-synchronized programs;
* `checkWellSynchronized_correct` (to come) — the extended well-synchronization
  check is sound and precise.
-/

namespace WeftMBarriers

section WellSynchronizationProperties

/-- Correctness of the happens-before relation computed by Algorithm 2,
stating that it is sound and precise (Definition 4, on program points) for
well-synchronized programs. -/
theorem soundAndPrecise_happensBefore {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    ∀ η₁ η₂ : ProgPoint, η₁ ∈ T.progPoints → η₂ ∈ T.progPoints →
      (happensBefore T τ η₁ η₂ ↔
        ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
          ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
            IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :=
  soundAndPrecise_happensBefore_impl hτ hws

/-- Correctness of the extended well-synchronized algorithm (Algorithm 2),
stating that it is sound and precise. -/
theorem checkWellSynchronized_correct {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) :
    (CheckWellSynchronized T τ).1 = true ↔ T.WellSynchronized :=
  checkWellSynchronized_correct_impl hτ

end WellSynchronizationProperties

end WeftMBarriers
