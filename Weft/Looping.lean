/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Angelic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Repeated sequential composition (`I ^ k`)

This file defines the `k`-fold *repeated sequential composition* of a single CTA
`I` with itself, written `I ^ k`: each thread runs `I`'s program `k` times in a
row. It is built directly on the sequential composition `A ⨾ B` (`CTA.seq`) of
`Weft/Angelic.lean`.

## The `ids`-equality obstacle

`CTA.seq A B hids` is only constructible when `A` and `B` have the **same** thread
set (`hids : A.ids = B.ids`) — composition is meant for two phases of one kernel.
To form `I ⨾ (I ^ k)` we therefore need `I.ids = (I ^ k).ids`. That fact is true
but it is itself a statement *about* `I ^ k`, so we cannot appeal to it before the
power is even defined.

We break the cycle by recursing into a **subtype** that carries the invariant
alongside the data: `CTA.powAux I k : { C : CTA // C.ids = I.ids }`. At each step
the stored proof `prev.property` is exactly the `hids` argument the next `CTA.seq`
demands, and the new proof is `rfl` because both `CTA.seq` and `CTA.emptied` fix
their `ids` field to the left operand's (`I.ids`). `CTA.pow` then projects out the
CTA and `CTA.pow_ids` projects out the invariant.

## Base case

`I ^ 0` is the unit of sequential composition: `I.emptied`, the CTA on `I`'s
threads with every program empty. Hence `(I ^ (k+1)).prog j = I.prog j ++ (I ^ k).prog j`
and `I ^ 1 = I` (up to `CTA.ext`, since `I.prog j ++ [] = I.prog j`).
-/

namespace Weft

/-- Auxiliary recursion for `CTA.pow` that threads the thread-set invariant through
the subtype `{ C : CTA // C.ids = I.ids }`. The stored proof is precisely the
`hids` hypothesis the next `CTA.seq` needs; both branches close their own invariant
by `rfl`, since `CTA.emptied` and `CTA.seq I _` each set `ids := I.ids`. -/
def CTA.powAux (I : CTA) : Nat → { C : CTA // C.ids = I.ids }
  | 0 => ⟨I.emptied, rfl⟩
  | k + 1 =>
    let prev := I.powAux k
    ⟨I.seq prev.val prev.property.symm, rfl⟩

/-- `k`-fold repeated sequential composition of `I` with itself: each thread runs
`I`'s program `k` times, then stops. `I ^ 0` is `I.emptied` (all threads empty) and
`I ^ (k+1) = I ⨾ (I ^ k)`. Exposed through the `^` notation via the `HPow` instance
below. -/
def CTA.pow (I : CTA) (k : Nat) : CTA := (I.powAux k).val

/-- `I ^ k` is `CTA.pow I k`: `I` sequentially composed with itself `k` times. -/
instance : HPow CTA Nat CTA := ⟨CTA.pow⟩

/-- Repeated sequential composition preserves the thread set: `I ^ k` has exactly
`I`'s threads, for every `k`. This is the invariant carried by `CTA.powAux`. -/
@[simp] theorem CTA.pow_ids (I : CTA) (k : Nat) : (I ^ k).ids = I.ids :=
  (I.powAux k).property

/-- `I ^ 0` is the all-empty CTA on `I`'s threads — the unit of `⨾`. -/
@[simp] theorem CTA.pow_zero (I : CTA) : I ^ 0 = I.emptied := rfl

/-- `I ^ (k+1) = I ⨾ (I ^ k)`: one more copy of `I` sequenced in front. The required
`ids` equality is `(CTA.pow_ids I k).symm`. -/
theorem CTA.pow_succ (I : CTA) (k : Nat) :
    I ^ (k + 1) = I.seq (I ^ k) (I.pow_ids k).symm := rfl

/-!
## Computing the iteration count `k` (§1, Theorem 1)

The loop body is itself a CTA `I` (one iteration: every thread runs its fragment of
the body once). §1 defines, for each named barrier `b` referenced by `I`, a factor
`f(b)` in terms of

* `arrival-count(b)` — the expected thread count `n` carried by the `arrive`/`sync`
  instructions on `b` (constant across all references to `b`, by assumption); and
* `arrivers(b)` — the number of arrivals on `b` in one iteration, i.e. how many
  `arrive`/`sync` instructions across all threads reference `b` (each such
  instruction registers exactly one thread, per the operational semantics).

Theorem 1's iteration count is `k = LCM(f(b₁), …, f(bₙ))` over all referenced
barriers: after `k` iterations every barrier has advanced its generation at least
once and returned to its entry state (or the run deadlocks first). This is exactly
the exponent of the repeated composition `I ^ k` above.
-/

/-- The barrier and expected count a command registers at, if any. Both `arrive b n`
and `sync b n` register one arrival at `b` with expected count `n`; `read`/`write`
reference no barrier. -/
def Cmd.barrierRef : Cmd → Option (Barrier × ℕ+)
  | .arrive b n => some (b, n)
  | .sync b n   => some (b, n)
  | .read _     => none
  | .write _    => none

/-- The distinct barriers referenced by `I` (the `b₁, …, bₙ` of Theorem 1). -/
def CTA.barriers (I : CTA) : Finset Barrier :=
  I.ids.biUnion fun i => (((I.prog i).filterMap Cmd.barrierRef).map Prod.fst).toFinset

/-- `I` uses a **consistent arrival count** for every barrier (§1's assumption that
"only a constant arrival count is used at all instructions that reference `b`"),
*witnessed* by an arrival-count function `ac`: every `arrive`/`sync` instruction
referencing a barrier `b` expects exactly `ac b` threads. The witness `ac` is the
arrival-count function `CTA.arrivalCount` reads off, so the assumption can be threaded
directly into the definitions that need it. -/
def CTA.ConsistentArrivalCounts (I : CTA) : Prop :=
  ∃ ac : Barrier → Nat, ∀ i ∈ I.ids, ∀ c ∈ I.prog i, ∀ b n,
    Cmd.barrierRef c = some (b, n) → ac b = (n : Nat)

/-- `arrivers(b)`: the number of arrivals on `b` in one iteration of `I` — how many
`arrive`/`sync` instructions across all threads reference `b` (summed over threads,
each instruction contributing one arrival per the operational semantics). -/
def CTA.arrivers (I : CTA) (b : Barrier) : Nat :=
  Finset.sum I.ids fun i =>
    ((I.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)

/-- `arrival-count(b)`: the expected thread count of barrier `b`, read off the witness
of the consistency assumption `h`. Threading `h` through is exactly what makes this
well-defined — §1 guarantees every reference to `b` uses this single count, so no
auxiliary "the value matches each reference" lemma is needed. -/
noncomputable def CTA.arrivalCount (I : CTA) (h : I.ConsistentArrivalCounts)
    (b : Barrier) : Nat :=
  h.choose b

/-- The per-barrier factor `f(b)` of §1. Writing `a = arrivers(b)` and
`c = arrival-count(b)`:

* `a = c`  ⇒ `1`     — one iteration already completes exactly one generation;
* `a ∣ c`  ⇒ `c / a` — `c/a` iterations' worth of arrivals fill one generation;
* `c ∣ a`  ⇒ `1`     — each iteration completes `a/c` whole generations;
* otherwise ⇒ `lcm(a, c)`.

The cases are tried in this order, matching the document (the `a = c` case takes
precedence over the two divisibility cases, which overlap there). -/
def loopFactor (arrivers arrivalCount : Nat) : Nat :=
  if arrivers = arrivalCount then 1
  else if arrivers ∣ arrivalCount then arrivalCount / arrivers
  else if arrivalCount ∣ arrivers then 1
  else Nat.lcm arrivers arrivalCount

/-- **Theorem 1's iteration count `k`** for the loop body `I`: the least number of
iterations after which every referenced barrier has advanced its generation at
least once and returned to its entry state (or the run deadlocks first). It is the
LCM of the per-barrier factors `f(b)` over all barriers referenced by `I`; the empty
LCM is `1` (a loop touching no barrier needs a single iteration). This `k` is the
exponent of the repeated composition `I ^ k`.

Requires `CTA.ConsistentArrivalCounts I` — Theorem 1's standing assumption that each
barrier is referenced with a single arrival count. The proof is threaded into
`arrivalCount`, whose witness supplies each barrier's count. -/
noncomputable def CTA.loopK (I : CTA) (h : I.ConsistentArrivalCounts) : Nat :=
  I.barriers.lcm fun b => loopFactor (I.arrivers b) (I.arrivalCount h b)

/-!
## Theorem 1 (§1): barriers advance over a complete run

A piece of Theorem 1: with `k = I.loopK` the §1 iteration count, if `I ^ k` is
well-synchronized from a state `s`, then every barrier the loop body uses advances
its generation at least once over a complete trace starting at `s`. We phrase
"generation increased by at least one" as `1 ≤ recycleCount b τ …`, since each
recycle of `b` along `τ` increments `b`'s generation by exactly one
(`recycleCount b τ (τ.length - 1)` counts the recycles of `b` over all of `τ`'s
steps), and "barriers used by `I ^ k`" as `b ∈ (I ^ k).barrierSet`.
-/

/-- **Theorem 1 (partial).** Let `k = I.loopK h` be the §1 iteration count (for a
consistency witness `h`). If `I ^ k` is well-synchronized from a state `s`, then along
any successful trace `τ` of `I ^ k` starting at `s`, every barrier `b` used by `I ^ k`
is recycled at least once — its generation increases by at least one. -/
theorem Config.WellSynchronized.pow_barriers_advance {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State}
    (hWS : (Config.run s (I ^ I.loopK h)).WellSynchronized) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    {b : Barrier} (hb : b ∈ (I ^ I.loopK h).barrierSet) :
    1 ≤ recycleCount b τ (τ.length - 1) := by
  sorry

end Weft
