/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.Language
import Mathlib.Logic.Function.Basic

/-!
# The Weft++ CTA state with shared-memory barriers (§5.2, Figure 3)

This file formalizes the *state* of a CTA in the mbarrier-extended language,
together with the initial state. The base state is that of §3.2 of the Weft
paper, extended per Figure 3 of the weft++ theorems document.

A state `s` of a CTA consists of:

1. An **enabled map** `E` that maps thread identifiers to booleans signifying
   whether the thread is enabled or not. Threads are disabled when they block on
   a barrier (a named-barrier `sync_nb` or an mbarrier `wait_mb`).

2. A **named-barrier map** `BN` that maps named-barrier names to a triple
   consisting of
   * a list `I` of threads that have *synced* at the barrier,
   * a count `A` of (non-blocking) *arrivals* at the barrier, and
   * the thread count, describing the number of threads the barrier is expecting
     to register if it is configured.

3. A **shared-memory-barrier (mbarrier) map** `BM` that maps shared barrier
   names to a quadruple `(I, A, n, ph)` consisting of
   * a list `I` of threads *waiting* (blocked) at the barrier,
   * a count `A` of (non-blocking) *arrivals* at the barrier,
   * the arrival count `n` the barrier was initialized with, and
   * the barrier's current *phase bit* `ph`, flipped on each recycle.

   For both barrier kinds the arrivals are tracked as a bare count rather than a
   list of thread ids: nothing in the semantics inspects *which* threads arrived
   (only how many), and unlike syncers/waiters an arriver is never re-examined,
   so the identities carry no information. (This also directly accommodates the
   same thread arriving several times within a generation — each `arrive_mb`
   just increments the count.)

The named thread count is configured by the first thread that reaches a barrier;
the thread count of unconfigured barriers is denoted `⊥` (here `Option.none`).
An mbarrier is instead configured *explicitly* by `init_mb`: the paper makes
`BM` a partial map and guards the rules with `sb ∈ dom(BM)`, which we encode
with the same `⊥` device — a total map whose uninitialized entries carry
`count = none`, so `sb ∈ dom(BM)` is exactly `isInitialized`. An empty list of
thread identifiers is `[]` and `::` adds a thread to a list.

The maps `E`, `BN` and `BM` are *total* (the paper writes `∀ i. …` and
`∀ b. …`), so we model them as total functions. The section's update notation
`A[x/y]` is then exactly Mathlib's `Function.update A y x`, whose lemmas
(`update_self`, `update_of_ne`, `update_idem`, …) we reuse rather than
reproving. The set-update `A[x/Y]` (update every key `y ∈ Y` to `x`) is not a
single library primitive, so `updateMapOn` below builds it as an iterated
`Function.update`.

The initial state has `∀ i. E(i) = true`, `∀ nb. BN(nb) = ([], 0, ⊥)` and
`dom(BM) = ∅`: all threads enabled, no thread registered at any named barrier,
all named barriers unconfigured, and all mbarriers uninitialized.

Finally, `done` denotes a CTA with no more commands to execute.
-/

namespace WeftMBarriers

/-- The per-named-barrier state: the triple `(I, A, n)` of §3.2.

* `synced`  is the list `I` of threads that have *synced* (blocked) at the barrier;
* `arrived` is the number `A` of (non-blocking) *arrivals* at the barrier;
* `count`   is the thread count `n` the barrier expects, with `none = ⊥` for an
  unconfigured barrier. -/
structure NamedBarrierState where
  /-- `I`: threads that have synced (blocked) at the barrier. -/
  synced : List ThreadId
  /-- `A`: the number of (non-blocking) `arrive_nb` registrations at the barrier.
  Tracked as a count rather than a list of ids: the semantics only ever consults
  *how many* threads have arrived (`|A|`), never *which* ones, and — unlike a
  syncer — an arriver is never re-examined, so its identity carries no
  information. -/
  arrived : ℕ
  /-- `n`: the expected thread count (`ℕ+`, positive when configured); `none`
  denotes `⊥` (unconfigured). -/
  count : Option ℕ+
  deriving DecidableEq, Repr, Inhabited

namespace NamedBarrierState

/-- The unconfigured named-barrier state `([], 0, ⊥)`. -/
def unconfigured : NamedBarrierState := ⟨[], 0, none⟩

/-- A named barrier is configured once its thread count has been set
(i.e. `n ≠ ⊥`). -/
def isConfigured (β : NamedBarrierState) : Bool := β.count.isSome

end NamedBarrierState

/-- The per-mbarrier state: the quadruple `(I, A, n, ph)` of Figure 3.

* `waiting` is the list `I` of threads *waiting* (blocked) at the barrier;
* `arrived` is the number `A` of (non-blocking) `arrive_mb` arrivals at the
  barrier;
* `count`   is the arrival count `n` fixed by `init_mb`, with `none = ⊥` for an
  uninitialized barrier (`sb ∉ dom(BM)` in the paper's partial-map phrasing);
* `phase`   is the barrier's current phase bit `ph`, flipped on each recycle. -/
structure MBarrierState where
  /-- `I`: threads waiting (blocked) at the barrier. -/
  waiting : List ThreadId
  /-- `A`: the number of (non-blocking) `arrive_mb` arrivals at the barrier.
  Tracked as a count rather than a list of ids, exactly as for named barriers:
  the semantics only ever consults *how many* arrivals have occurred (`|A|`),
  never *which* threads arrived, and an arriver is never re-examined. The count
  also directly accommodates the same thread arriving several times within a
  generation. -/
  arrived : ℕ
  /-- `n`: the expected arrival count (`ℕ+`, positive when initialized); `none`
  denotes `⊥` (uninitialized, i.e. `sb ∉ dom(BM)`). -/
  count : Option ℕ+
  /-- `ph`: the current phase bit, `false` for phase `0`; `init_mb` starts a
  barrier at phase `0` and each recycle flips it (`ph ⊕ 1 = !ph`). -/
  phase : Phase
  deriving DecidableEq, Repr, Inhabited

namespace MBarrierState

/-- The uninitialized mbarrier state `([], 0, ⊥, 0)` — the encoding of
`sb ∉ dom(BM)`. -/
def uninitialized : MBarrierState := ⟨[], 0, none, false⟩

/-- An mbarrier is initialized once `init_mb` has set its arrival count
(i.e. `n ≠ ⊥`) — the encoding of `sb ∈ dom(BM)`. -/
def isInitialized (β : MBarrierState) : Bool := β.count.isSome

end MBarrierState

/-- A state `s` of a CTA: the enabled map `E`, the named-barrier map `BN` and
the mbarrier map `BM`. -/
structure State where
  /-- `E`: the enabled map, sending each thread id to whether it is enabled. -/
  E : ThreadId → Bool
  /-- `BN`: the named-barrier map, sending each named-barrier name to its
  `NamedBarrierState`. -/
  BN : NamedBarrier → NamedBarrierState
  /-- `BM`: the mbarrier map, sending each shared barrier name to its
  `MBarrierState`. -/
  BM : SharedBarrier → MBarrierState

/-- Map update over a set of keys, realizing the paper's `f[x/Y]`: the map that
agrees with `f` on all inputs not in `Y`, and maps every `y ∈ Y` to `x`. Built as
an iterated `Function.update` so it inherits that primitive's lemmas. (The
single-key update `f[x/y]` is just `Function.update f y x` directly.) -/
def updateMapOn {α β : Type} [DecidableEq α]
    (f : α → β) (Y : List α) (x : β) : α → β :=
  Y.foldr (fun y g => Function.update g y x) f

namespace State

/-- The initial state `I`: every thread is enabled (`E(i) = true`), every named
barrier is unconfigured (`BN(nb) = ([], 0, ⊥)`), and every mbarrier is
uninitialized (`dom(BM) = ∅`). -/
def initial : State where
  E := fun _ => true
  BN := fun _ => NamedBarrierState.unconfigured
  BM := fun _ => MBarrierState.uninitialized

/-- Two states register the same number of **arrived** (non-blocking) threads at every
barrier, named or shared. This is the projection of barrier state preserved by a complete
`I ^ k` run: the total arrivals on each barrier form whole generations, so the arrived
count returns to its entry value. The synced/waiting count and the configured status need
*not* be restored — a complete run drains every syncer and waiter (none can be parked at
`done`) and may leave a barrier freshly recycled — so this arrived-count projection is the
most that holds per barrier. (The mbarrier *phase* is deliberately not included here: a
single generation flips it, and only the loop development's doubled period `fₘ(b) = 2 ·
f(b)` restores it — the phase clause enters there, not in this equivalence.) -/
def ArrivedCountEquiv (s₁ s₂ : State) : Prop :=
  (∀ nb, (s₁.BN nb).arrived = (s₂.BN nb).arrived) ∧
  (∀ sb, (s₁.BM sb).arrived = (s₂.BM sb).arrived)

@[refl]
theorem ArrivedCountEquiv.refl (s : State) : s.ArrivedCountEquiv s :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem ArrivedCountEquiv.symm {s₁ s₂ : State} (h : s₁.ArrivedCountEquiv s₂) :
    s₂.ArrivedCountEquiv s₁ := ⟨fun nb => (h.1 nb).symm, fun sb => (h.2 sb).symm⟩

theorem ArrivedCountEquiv.trans {s₁ s₂ s₃ : State}
    (h₁ : s₁.ArrivedCountEquiv s₂) (h₂ : s₂.ArrivedCountEquiv s₃) :
    s₁.ArrivedCountEquiv s₃ :=
  ⟨fun nb => (h₁.1 nb).trans (h₂.1 nb), fun sb => (h₁.2 sb).trans (h₂.2 sb)⟩

theorem ArrivedCountEquiv.isEquivalence : Equivalence State.ArrivedCountEquiv :=
  ⟨ArrivedCountEquiv.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end State

/-- `done`: a CTA with no more commands to execute, i.e. every thread in the
domain has reached `return` (the empty command list `[]`). -/
def CTA.IsDone (T : CTA) : Prop := ∀ i ∈ T.ids, T.prog i = []

end WeftMBarriers
