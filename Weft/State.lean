/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Language
import Mathlib.Logic.Function.Basic

/-!
# The Weft CTA state (§3.2)

This file formalizes the *state* of a CTA from Section 3.2 ("State") of the Weft
paper, together with the initial state.

From the paper, a state `s` of a CTA consists of:

1. An **enabled map** `E` that maps thread identifiers to booleans signifying
   whether the thread is enabled or not. Threads are disabled when they block on
   a barrier.

2. A **barrier map** `B` that maps barrier names to a triple consisting of
   * a list `I` of threads that have *synced* at the barrier,
   * a list `A` of threads that have *arrived* at the barrier, and
   * the thread count, describing the number of threads the barrier is expecting
     to register if it is configured.

The thread count is configured by the first thread that reaches a barrier. The
thread count of unconfigured barriers is denoted `⊥` (here `Option.none`). An
empty list of thread identifiers is `[]` and `::` adds a thread to a list.

The maps `E` and `B` are *total* (the paper writes `∀ i. …` and `∀ b. …`), so we
model them as total functions. The section's update notation `A[x/y]` is then
exactly Mathlib's `Function.update A y x`, whose lemmas (`update_self`,
`update_of_ne`, `update_idem`, …) we reuse rather than reproving. The set-update
`A[x/Y]` (update every key `y ∈ Y` to `x`) is not a single library primitive, so
`updateMapOn` below builds it as an iterated `Function.update`.

The initial state has `∀ i. E(i) = true` and `∀ b. B(b) = ([], [], ⊥)`: all
threads enabled, no thread registered at any barrier, and all barriers
unconfigured.

Finally, `done` denotes a CTA with no more commands to execute.
-/

namespace Weft

/-- The per-barrier state: the triple `(I, A, n)` of §3.2.

* `synced`  is the list `I` of threads that have *synced* (blocked) at the barrier;
* `arrived` is the list `A` of threads that have *arrived* (non-blocking) at it;
* `count`   is the thread count `n` the barrier expects, with `none = ⊥` for an
  unconfigured barrier. -/
structure BarrierState where
  /-- `I`: threads that have synced (blocked) at the barrier. -/
  synced : List ThreadId
  /-- `A`: threads that have arrived (non-blocking) at the barrier. -/
  arrived : List ThreadId
  /-- `n`: the expected thread count (`ℕ+`, positive when configured); `none`
  denotes `⊥` (unconfigured). -/
  count : Option ℕ+
  deriving DecidableEq, Repr, Inhabited

namespace BarrierState

/-- The unconfigured barrier state `([], [], ⊥)`. -/
def unconfigured : BarrierState := ⟨[], [], none⟩

/-- A barrier is configured once its thread count has been set (i.e. `n ≠ ⊥`). -/
def isConfigured (β : BarrierState) : Bool := β.count.isSome

/-- Two barrier states are **equivalent** when they agree up to reordering of the
synced and arrived lists (and have the same thread count). Because `arrive`/`sync`
*prepend* to these lists (`i :: A`), their order merely records execution order,
which is immaterial to the barrier's behaviour; this relation quotients that out.
It is exactly multiset equality of the two lists (`Multiset.coe_eq_coe`), but stated
on the underlying `List` representation so the existing list-based development is
left untouched. -/
def Equiv (β₁ β₂ : BarrierState) : Prop :=
  List.Perm β₁.synced β₂.synced ∧ List.Perm β₁.arrived β₂.arrived ∧
    β₁.count = β₂.count

@[refl]
theorem Equiv.refl (β : BarrierState) : β.Equiv β :=
  ⟨List.Perm.refl _, List.Perm.refl _, rfl⟩

theorem Equiv.rfl {β : BarrierState} : β.Equiv β := Equiv.refl β

theorem Equiv.symm {β₁ β₂ : BarrierState} (h : β₁.Equiv β₂) : β₂.Equiv β₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem Equiv.trans {β₁ β₂ β₃ : BarrierState}
    (h₁ : β₁.Equiv β₂) (h₂ : β₂.Equiv β₃) : β₁.Equiv β₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem Equiv.isEquivalence : Equivalence BarrierState.Equiv :=
  ⟨Equiv.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance : Setoid BarrierState := ⟨BarrierState.Equiv, Equiv.isEquivalence⟩

/-- Equivalent barrier states have the same number of synced threads. -/
theorem Equiv.synced_length_eq {β₁ β₂ : BarrierState} (h : β₁.Equiv β₂) :
    β₁.synced.length = β₂.synced.length := h.1.length_eq

/-- Equivalent barrier states have the same number of arrived threads. -/
theorem Equiv.arrived_length_eq {β₁ β₂ : BarrierState} (h : β₁.Equiv β₂) :
    β₁.arrived.length = β₂.arrived.length := h.2.1.length_eq

/-- Equivalent barrier states have the same thread count. -/
theorem Equiv.count_eq {β₁ β₂ : BarrierState} (h : β₁.Equiv β₂) :
    β₁.count = β₂.count := h.2.2

end BarrierState

/-- A state `s` of a CTA: the enabled map `E` and the barrier map `B`. -/
structure State where
  /-- `E`: the enabled map, sending each thread id to whether it is enabled. -/
  E : ThreadId → Bool
  /-- `B`: the barrier map, sending each barrier name to its `BarrierState`. -/
  B : Barrier → BarrierState

/-- Map update over a set of keys, realizing the paper's `f[x/Y]`: the map that
agrees with `f` on all inputs not in `Y`, and maps every `y ∈ Y` to `x`. Built as
an iterated `Function.update` so it inherits that primitive's lemmas. (The
single-key update `f[x/y]` is just `Function.update f y x` directly.) -/
def updateMapOn {α β : Type} [DecidableEq α]
    (f : α → β) (Y : List α) (x : β) : α → β :=
  Y.foldr (fun y g => Function.update g y x) f

namespace State

/-- The initial state `I`: every thread is enabled (`E(i) = true`) and every
barrier is unconfigured (`B(b) = ([], [], ⊥)`). -/
def initial : State where
  E := fun _ => true
  B := fun _ => BarrierState.unconfigured

/-- Two states are **barrier-equivalent** when their barrier maps agree, barrier by
barrier, up to reordering of the synced/arrived lists (`BarrierState.Equiv`). This
captures "the barriers are back where they started" without pinning the execution
order of the registered threads. (It says nothing about the enabled map `E`; pair it
with `s₁.E = s₂.E` where the enabled map matters too.) -/
def BEquiv (s₁ s₂ : State) : Prop := ∀ b, (s₁.B b).Equiv (s₂.B b)

@[refl]
theorem BEquiv.refl (s : State) : s.BEquiv s := fun b => BarrierState.Equiv.refl _

theorem BEquiv.symm {s₁ s₂ : State} (h : s₁.BEquiv s₂) : s₂.BEquiv s₁ :=
  fun b => (h b).symm

theorem BEquiv.trans {s₁ s₂ s₃ : State}
    (h₁ : s₁.BEquiv s₂) (h₂ : s₂.BEquiv s₃) : s₁.BEquiv s₃ :=
  fun b => (h₁ b).trans (h₂ b)

theorem BEquiv.isEquivalence : Equivalence State.BEquiv :=
  ⟨BEquiv.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end State

/-- `done`: a CTA with no more commands to execute, i.e. every thread in the
domain has reached `return` (the empty command list `[]`). -/
def CTA.IsDone (T : CTA) : Prop := ∀ i ∈ T.ids, T.prog i = []

end Weft
