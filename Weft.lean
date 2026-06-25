import Weft.Language
import Weft.State
import Weft.Semantics
import Weft.Traces
import Weft.WellSynchronized
import Weft.CheckWellSynchronized
import Weft.Angelic
import Weft.Looping

namespace Weft

section WellSynchronizationProperties

/-- Correctness of the happens-before relation computed by the
    well-synchronized algorithm, stating that it is sound and
    precise for well-synchronized programs. -/
theorem soundAndPrecise_happensBefore {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    ∀ η₁ η₂ : ProgPoint, η₁ ∈ T.progPoints → η₂ ∈ T.progPoints →
      (happensBefore T τ η₁ η₂ ↔
        ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
          ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
            IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :=
  soundAndPrecise_happensBefore_impl hτ hws

/-- Correctness of the well-synchronized algorithm, stating that it is
    sound and precise. -/
theorem checkWellSynchronized_correct {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) :
    (CheckWellSynchronized T τ).1 = true ↔ T.WellSynchronized :=
  checkWellSynchronized_correct_impl hτ

end WellSynchronizationProperties

section AngelicTraceSelection

/-- The angelic completion of a sequential composition: if `A` and `A ⨾ B` are
    well-synchronized, there are successful traces of `A` and of `A ⨾ B` whose `A`-phases
    agree — the `A ⨾ B` trace runs `A` entirely to completion before running any of `B`. -/
theorem CTA.WellSynchronized.seq_angelic_completion {A B : CTA} (hids : A.ids = B.ids)
    (hA : A.WellSynchronized) (hAB : (A.seq B hids).WellSynchronized) :
    ∃ t t', IsSuccessfulTraceFrom (Config.run State.initial A) t ∧
            IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) t' ∧
            t.dropLast.map (Config.seqLift A B) <+: t' :=
  CTA.WellSynchronized.seq_angelic_completion_impl hids hA hAB

/-- No happens-before edge runs from the `B`-phase back into the `A`-phase of a
    well-synchronized sequential composition `A ⨾ B`: the static happens-before relation
    never orders a `B`-instruction before an `A`-instruction. -/
theorem CTA.WellSynchronized.seq_no_happensBefore_B_to_A {A B : CTA} (hids : A.ids = B.ids)
    (hA : A.WellSynchronized) (hAB : (A.seq B hids).WellSynchronized)
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) τ) :
    ¬ ∃ s d : ProgPoint,
        happensBefore (A.seq B hids) τ s d ∧
        ((A.prog s.thread).length ≤ s.idx ∧
          s.idx < (A.prog s.thread).length + (B.prog s.thread).length) ∧
        d.idx < (A.prog d.thread).length :=
  CTA.WellSynchronized.seq_no_happensBefore_B_to_A_impl hids hA hAB hτ

end AngelicTraceSelection

end Weft
