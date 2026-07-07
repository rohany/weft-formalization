/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Function.Basic

/-!
# The Weft++ language with shared-memory barriers (§5.2, Figure 3)

This library formalizes the extension of the named-barrier language with
*shared-memory barriers* (mbarriers), following §5.2 of the weft++ theorems
document. The syntax (Figure 3) extends the named-barrier commands with three
mbarrier operations, and the state carries a shared-barrier map `BM` alongside
the named-barrier map `BN` and the enabled map `E`:

* `init_mb sb n` — configure a fresh mbarrier `sb` with arrival count `n`
  (re-initialization is an error);
* `arrive_mb sb` — record an arrival on `sb` (a thread may arrive more than
  once: the arrivers are a *list*, not a set);
* `wait_mb sb ph` — wait on `sb` at phase `ph`: blocks and joins the waiter
  list when `ph` matches the barrier's current phase bit, and passes through
  as a no-op otherwise (`MB-Wait-Pass`).

An mbarrier's state is `(I, A, n, ph)` — waiters, arrivers, arrival count, and
a *phase bit* that flips on each recycle (`MB-Recycle`), so an mbarrier's
period is twice a named barrier's (`fₘ(b) = 2 · f(b)`).

The named-barrier development lives in `WeftNamedBarriers` and stays frozen as
the verified baseline; this library re-develops the combined language natively
(shared-core split). Definitions are stated so that the named-barrier fragment
stays as close as possible to `WeftNamedBarriers.Language`, keeping the
copy-adapt port of the named cases mechanical.

Target theorems (§5.2.4–§5.2.6): `soundAndPrecise_happensBefore` for
Algorithm 2's happens-before relation — note its `R` is *asymmetric* for
mbarriers (no wait→wait clique edges, since mbarrier waits need not resolve
simultaneously) — and `checkWellSynchronized_correct` for the extended
checker, where mbarrier wait generations are phase-corrected (`g` or `g − 1`)
and generation `−1`/`0`-indexing must be resolved in the statement of
well-synchronization.
-/

namespace WeftMBarriers

-- TODO(§5.2, Figure 3): syntax — barrier names split into named (`nb`) and
-- shared (`sb`); `Cmd` gains `init_mb`, `arrive_mb`, `wait_mb`; `CTA` as in
-- the named-barrier language.

end WeftMBarriers
