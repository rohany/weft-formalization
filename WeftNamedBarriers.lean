import WeftNamedBarriers.Language
import WeftNamedBarriers.State
import WeftNamedBarriers.Semantics
import WeftNamedBarriers.Traces
import WeftNamedBarriers.WellSynchronized
import WeftNamedBarriers.CheckWellSynchronized
import WeftNamedBarriers.Angelic
import WeftNamedBarriers.Looping

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

theorem checkLoopWellSynchronized_correct {P I E : CTA}
    (h : I.ConsistentArrivalCounts)
    (h1 : P.ids = I.ids)
    (h2 : I.ids = E.ids)
    {τp : List Config}
    (hτp : IsSuccessfulTraceFrom (Config.run State.initial P) τp)
    {τpk : List Config}
    (hτpk : IsSuccessfulTraceFrom (Config.run State.initial
      (P.seq (I ^ I.loopK h) (h1.trans (CTA.pow_ids I (I.loopK h)).symm))) τpk)
    {τ : Fin (3 * I.loopK h + 1) → List Config}
    (hτ : ∀ i : Fin (3 * I.loopK h + 1),
      IsSuccessfulTraceFrom (Config.run State.initial (CTA.loopProgram P I E h1 h2 i.val)) (τ i)) :
    checkLoopWellSynchronized P I E h h1 h2 τp τpk τ = true
      ↔ P.WellSynchronized
        ∧ (P.seq (I ^ I.loopK h) (h1.trans (CTA.pow_ids I (I.loopK h)).symm)).WellSynchronized
        ∧ ∀ n : Nat, (CTA.loopProgram P I E h1 h2 n).WellSynchronized :=
  checkLoopWellSynchronized_correct_impl h h1 h2 hτp hτpk hτ

/-- **Loop check for a bare loop (no prefix or epilogue).** Specializing `checkLoopWellSynchronized`
to an empty prefix and epilogue (`CTA.empty I.ids`), the check is correct iff *every* unrolling
`I ^ n` is well-synchronized. Unlike `checkLoopWellSynchronized_correct` it requires neither the
`WS(P)` nor the `WS(P ⨾ I^k)` certificate, and neither of their trace witnesses: an empty prefix is
trivially well-synchronized, while `P ⨾ I^k` is just the unrolling `I^k`, so its trace is the
unrolling `τ ⟨k, _⟩` already supplied (and the empty prefix's trace is the `0`-unrolling
`τ ⟨0, _⟩`). -/
theorem checkLoopWellSynchronized_correct_empty {I : CTA} (h : I.ConsistentArrivalCounts)
    {τ : Fin (3 * I.loopK h + 1) → List Config}
    (hτ : ∀ i : Fin (3 * I.loopK h + 1),
      IsSuccessfulTraceFrom (Config.run State.initial
        (CTA.loopProgram (CTA.empty I.ids I.ids_nonempty) I (CTA.empty I.ids I.ids_nonempty)
          rfl rfl i.val)) (τ i)) :
    checkLoopWellSynchronized (CTA.empty I.ids I.ids_nonempty) I (CTA.empty I.ids I.ids_nonempty)
        h rfl rfl (τ ⟨0, by omega⟩) (τ ⟨I.loopK h, by omega⟩) τ = true
      ↔ ∀ n : Nat, (I ^ n).WellSynchronized :=
  checkLoopWellSynchronized_correct_empty_impl h hτ

end LoopProofs

end Weft
