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
  /-- `n`: the expected thread count; `none` denotes `⊥` (unconfigured). -/
  count : Option Nat
  deriving DecidableEq, Repr, Inhabited

namespace BarrierState

/-- The unconfigured barrier state `([], [], ⊥)`. -/
def unconfigured : BarrierState := ⟨[], [], none⟩

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
barrier is unconfigured (`B(b) = ([], [], ⊥)`). -/
def initial : State where
  E := fun _ => true
  B := fun _ => BarrierState.unconfigured

end State

/-- `done`: a CTA with no more commands to execute, i.e. every thread in the
domain has reached `return` (the empty command list `[]`). -/
def CTA.IsDone (T : CTA) : Prop := ∀ i ∈ T.ids, T.prog i = []

end Weft
