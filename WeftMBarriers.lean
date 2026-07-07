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

/-!
# Weft++ with shared-memory barriers — public interface

The extension of the named-barrier language with shared-memory barriers
(mbarriers), per §5.2 of the weft++ theorems document. Once the development is
in place, this facade will state the two headline theorems for the combined
language, mirroring `WeftNamedBarriers.lean`:

* `soundAndPrecise_happensBefore` — Algorithm 2's happens-before relation is
  sound and precise for well-synchronized programs;
* `checkWellSynchronized_correct` — the extended well-synchronization check is
  sound and precise.
-/
