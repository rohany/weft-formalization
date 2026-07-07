/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftNamedBarriers.Language
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
   * a count `A` of (non-blocking) *arrivals* at the barrier, and
   * the thread count, describing the number of threads the barrier is expecting
     to register if it is configured.

   The arrivals are tracked as a bare count rather than a list of thread ids:
   nothing in the semantics inspects *which* threads arrived (only how many), and
   unlike syncers an arriver is never re-examined, so the identities carry no
   information.

The thread count is configured by the first thread that reaches a barrier. The
thread count of unconfigured barriers is denoted `⊥` (here `Option.none`). An
empty list of thread identifiers is `[]` and `::` adds a thread to a list.

The maps `E` and `B` are *total* (the paper writes `∀ i. …` and `∀ b. …`), so we
model them as total functions. The section's update notation `A[x/y]` is then
exactly Mathlib's `Function.update A y x`, whose lemmas (`update_self`,
`update_of_ne`, `update_idem`, …) we reuse rather than reproving. The set-update
`A[x/Y]` (update every key `y ∈ Y` to `x`) is not a single library primitive, so
`updateMapOn` below builds it as an iterated `Function.update`.

The initial state has `∀ i. E(i) = true` and `∀ b. B(b) = ([], 0, ⊥)`: all
threads enabled, no thread registered at any barrier, and all barriers
unconfigured.

Finally, `done` denotes a CTA with no more commands to execute.
-/

namespace Weft

/-- The per-barrier state: the triple `(I, A, n)` of §3.2.

* `synced`  is the list `I` of threads that have *synced* (blocked) at the barrier;
* `arrived` is the number `A` of (non-blocking) *arrivals* at the barrier;
* `count`   is the thread count `n` the barrier expects, with `none = ⊥` for an
  unconfigured barrier. -/
structure BarrierState where
  /-- `I`: threads that have synced (blocked) at the barrier. -/
  synced : List ThreadId
  /-- `A`: the number of (non-blocking) `arrive` registrations at the barrier.
  Tracked as a count rather than a list of ids: the semantics only ever consults
  *how many* threads have arrived (`|A|`), never *which* ones, and — unlike a
  syncer — an arriver is never re-examined, so its identity carries no
  information. -/
  arrived : ℕ
  /-- `n`: the expected thread count (`ℕ+`, positive when configured); `none`
  denotes `⊥` (unconfigured). -/
  count : Option ℕ+
  deriving DecidableEq, Repr, Inhabited

namespace BarrierState

/-- The unconfigured barrier state `([], 0, ⊥)`. -/
def unconfigured : BarrierState := ⟨[], 0, none⟩

/-- A barrier is configured once its thread count has been set (i.e. `n ≠ ⊥`). -/
def isConfigured (β : BarrierState) : Bool := β.count.isSome

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
barrier is unconfigured (`B(b) = ([], 0, ⊥)`). -/
def initial : State where
  E := fun _ => true
  B := fun _ => BarrierState.unconfigured

/-- Two states register the same number of **arrived** (non-blocking) threads at every
barrier. This is the projection of barrier state preserved by a complete `I ^ k` run: the
total arrivals on each barrier form whole generations, so the arrived count returns to its
entry value. The synced count and the configured/unconfigured status need *not* be
restored — a complete run drains every syncer (none can be parked at `done`) and may leave
a barrier freshly recycled — so this arrived-count projection is the most that holds. -/
def ArrivedCountEquiv (s₁ s₂ : State) : Prop :=
  ∀ b, (s₁.B b).arrived = (s₂.B b).arrived

@[refl]
theorem ArrivedCountEquiv.refl (s : State) : s.ArrivedCountEquiv s := fun _ => rfl

theorem ArrivedCountEquiv.symm {s₁ s₂ : State} (h : s₁.ArrivedCountEquiv s₂) :
    s₂.ArrivedCountEquiv s₁ := fun b => (h b).symm

theorem ArrivedCountEquiv.trans {s₁ s₂ s₃ : State}
    (h₁ : s₁.ArrivedCountEquiv s₂) (h₂ : s₂.ArrivedCountEquiv s₃) :
    s₁.ArrivedCountEquiv s₃ := fun b => (h₁ b).trans (h₂ b)

theorem ArrivedCountEquiv.isEquivalence : Equivalence State.ArrivedCountEquiv :=
  ⟨ArrivedCountEquiv.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end State

/-- `done`: a CTA with no more commands to execute, i.e. every thread in the
domain has reached `return` (the empty command list `[]`). -/
def CTA.IsDone (T : CTA) : Prop := ∀ i ∈ T.ids, T.prog i = []

end Weft
