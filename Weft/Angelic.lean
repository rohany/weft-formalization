/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.WellSynchronized

/-!
# Sequential composition and angelic completion

This file introduces the *sequential composition* `A ⨾ B` of two CTAs — each
thread runs `A`'s program and then `B`'s — and states (without proof) the
**angelic completion** property:

> If `A` is well-synchronized and `A ⨾ B` is well-synchronized, then every complete
> trace of `A` can be extended to a complete trace of `A ⨾ B`.

Intuitively, no matter how the scheduler resolves the nondeterminism while running
`A`, that partial execution is always a *prefix* of some successful run of the
whole `A ⨾ B`: running `A` first never paints `A ⨾ B` into a corner.

## Composition

`A ⨾ B` (`CTA.seq`) is only meaningful when `A` and `B` are two phases of the *same*
kernel — i.e. they have the **same set of threads** (`A.ids = B.ids`). This equality
is a required argument, so the composition is simply not constructible otherwise.
The thread set is then `A.ids`, and `(A ⨾ B).prog i = A.prog i ++ B.prog i`.

## Relating the two executions — `Config.seqLift`

A trace of `A` is a `List Config` whose configurations carry `A`-derivatives, while
a trace of `A ⨾ B` carries `A ⨾ B`-derivatives, so the two cannot be compared
directly. `Config.seqLift A B` maps a configuration of `A` to the corresponding
configuration of `A ⨾ B` by appending `B`'s program to every thread's *remaining*
program. The crucial point is that the **state** `(E, B)` is shared: while `A ⨾ B`
is still inside its `A`-phase it performs exactly the same synchronization steps as
`A` alone, so a configuration `run s C` of `A` lifts to `run s (C with B appended)`
with the same `s`. A finished `A`-configuration (`done s`) lifts to the `A ⨾ B`
configuration in which `A` is done and `B` is poised to start.

The lift appends programs with `CTA.appendTail`, a *total* program-concatenation
(over the union of thread sets) that coincides with `CTA.seq` exactly when the two
CTAs share their threads — which they do for every configuration of an actual
`A`-trace. "`t` is a prefix of `t'`" is then `t.map (Config.seqLift A B) <+: t'`.
-/

namespace Weft

/-- Sequential composition `A ⨾ B`: each thread runs `A`'s program and then `B`'s.
Valid **only when `A` and `B` have the same threads** (`hids : A.ids = B.ids`) — two
phases of one kernel — so the equality is a required argument. The thread set is
`A.ids` and `(A ⨾ B).prog i = A.prog i ++ B.prog i`. -/
def CTA.seq (A B : CTA) (hids : A.ids = B.ids) : CTA where
  ids := A.ids
  prog := fun i => A.prog i ++ B.prog i
  nil_outside_ids := by
    intro i hi
    show A.prog i ++ B.prog i = []
    rw [A.nil_outside_ids i hi, B.nil_outside_ids i (hids ▸ hi)]; rfl
  ids_nonempty := A.ids_nonempty

/-- `A` with every thread finished (all programs empty), keeping `A`'s threads.
Describes the `A`-half of an `A ⨾ B` configuration once `A` is done. -/
def CTA.emptied (A : CTA) : CTA where
  ids := A.ids
  prog := fun _ => []
  nil_outside_ids := fun _ _ => rfl
  ids_nonempty := A.ids_nonempty

/-- `B`'s programs appended to `C`'s remaining programs, over the *union* of their
threads — a total operation (no `ids` hypothesis) used to lift configurations of `A`
into `A ⨾ B`. When `C` and `B` share their threads it agrees with `CTA.seq`. -/
def CTA.appendTail (C B : CTA) : CTA where
  ids := C.ids ∪ B.ids
  prog := fun i => C.prog i ++ B.prog i
  nil_outside_ids := by
    intro i hi
    simp only [Finset.mem_union, not_or] at hi
    show C.prog i ++ B.prog i = []
    rw [C.nil_outside_ids i hi.1, B.nil_outside_ids i hi.2]; rfl
  ids_nonempty := by
    obtain ⟨i, hi⟩ := C.ids_nonempty
    exact ⟨i, Finset.mem_union_left _ hi⟩

/-- Lift a configuration of `A` to the corresponding configuration of `A ⨾ B`,
appending `B`'s program to each thread's remaining program (the state `s` is
unchanged, since `A ⨾ B` performs the same steps while in its `A`-phase). A finished
`A`-configuration (`done`) becomes the `A ⨾ B` configuration in which `A` is done and
`B` is about to start. -/
def Config.seqLift (A B : CTA) : Config → Config
  | .run s C => .run s (C.appendTail B)
  | .done s  => .run s (A.emptied.appendTail B)
  | .err T   => .err (T.appendTail B)

/-- **Angelic completion** (statement only). If `A` and the composition `A ⨾ B` are
both well-synchronized, then every complete trace `t` of `A` is a prefix of some
complete trace `t'` of `A ⨾ B`: any partial execution that runs `A` to completion can
always be continued to a successful run of the whole composition. Here "`t` is a
prefix of `t'`" means that lifting each `A`-configuration into `A ⨾ B`
(`Config.seqLift`) yields an initial segment of `t'`. -/
theorem CTA.WellSynchronized.seq_angelic_prefix {A B : CTA} (hids : A.ids = B.ids)
    (hA : A.WellSynchronized) (hAB : (A.seq B hids).WellSynchronized) :
    ∀ t, IsCompleteTraceFrom (Config.run State.initial A) t →
      ∃ t', IsCompleteTraceFrom (Config.run State.initial (A.seq B hids)) t' ∧
        t.map (Config.seqLift A B) <+: t' := by
  sorry

end Weft
