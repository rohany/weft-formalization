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

section LoopBatchStructure

/-- Per-instruction generation offset between the last two batches of an unrolled loop:
    for a well-synchronized batched loop body `(I ^ k)` run `n ≥ 1` times, every barrier
    instruction's generation in batch `n-1` exceeds its generation in batch `n-2` by the
    fixed amount `k * arrivers b / arrivalCount b`. -/
theorem CTA.WellSynchronized.last_batch_gen_offset {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n+1))) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (m : ℕ+),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, m) →
        pointGen ((I ^ k) ^ (n+1)) τ ⟨t, (n) * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ (n+1)) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b :=
  CTA.WellSynchronized.last_batch_gen_offset_impl h hk hn hWS

/-- The last two batches of an unrolled loop have identical internal happens-before
    structure: a happens-before edge between instructions of batch `n-2` holds iff the
    corresponding edge between the same instructions of batch `n-1` holds. -/
theorem CTA.WellSynchronized.last_batch_hb_within {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n+1))) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n+1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n+1)) τ
              ⟨t₁, (n) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n) * ((I ^ k).prog t₂).length + j₂⟩) :=
  CTA.WellSynchronized.last_batch_hb_within_impl h hk hn hWS

theorem CTA.WellSynchronized.last_batch_hb_across {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 2 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n+1))) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n+1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n) * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n+1)) τ
              ⟨t₁, (n - 2) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩) :=
  CTA.WellSynchronized.last_batch_hb_across_impl h hk hn hWS

end LoopBatchStructure

section LoopProofs

theorem CTA.WellSynchronized.batches_inductive_step {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : n >= 2)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ((I ^ k) ^ (n + 1)).WellSynchronized :=
  CTA.WellSynchronized.batches_inductive_step_impl h hk (by omega) hWS


theorem CTA.WellSynchronized.loop_well_synchronized {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : n >= 2)
    (hWS : (I ^ k).BatchesWellSynchronized 2) :
    ((I ^ k) ^ (n)).WellSynchronized :=
  CTA.WellSynchronized.loop_well_synchronized_impl h hk hn hWS

end LoopProofs

end Weft
