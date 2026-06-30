/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Angelic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-- The program of a loop with prefix `P`, body `I`, and epilogue `E`, with the body unrolled
`n` times: `P ⨾ I^n ⨾ E`. The thread-set obligations of the two `CTA.seq`s are discharged from
`h1 : P.ids = I.ids` and `h2 : I.ids = E.ids` (using `CTA.pow_ids` to see that `I^n` has `I`'s
threads, and `(CTA.seq A B _).ids = A.ids` to reduce the outer obligation to `P.ids = E.ids`). -/
def CTA.loopProgram (P I E : CTA) (h1 : P.ids = I.ids) (h2 : I.ids = E.ids) (n : Nat) : CTA :=
  (P.seq (I ^ n) (h1.trans (CTA.pow_ids I n).symm)).seq E (h1.trans h2)

/-- `loopProgram`'s thread set is the prefix's (every `CTA.seq` keeps its left operand's ids). -/
@[simp] theorem CTA.loopProgram_ids (P I E : CTA) (h1 : P.ids = I.ids) (h2 : I.ids = E.ids)
    (n : Nat) : (CTA.loopProgram P I E h1 h2 n).ids = P.ids := rfl

/-- `loopProgram`'s per-thread program is the prefix, then `n` copies of the body, then the
epilogue. -/
theorem CTA.loopProgram_prog (P I E : CTA) (h1 : P.ids = I.ids) (h2 : I.ids = E.ids)
    (n : Nat) (t : ThreadId) :
    (CTA.loopProgram P I E h1 h2 n).prog t = P.prog t ++ (I ^ n).prog t ++ E.prog t := rfl

/-- **The loop well-synchronization check.** Decides whether a loop with body `I` is
well-synchronized by running `CheckWellSynchronized` on every unrolling of the body
out to `2k` copies, where `k = I.loopK h` is the loop exponent (so `h :
I.ConsistentArrivalCounts` is required — `loopK` needs it, hence so does this check).
It is the executable transcription of

```
for i in [0, 2k]:
  unroll i times          -- form the i-fold unrolling `I ^ i`
  if !ws: return false     -- `CheckWellSynchronized (I ^ i) (τ i)`
return true
```

`I ^ i` is the loop body sequentially composed with itself `i` times (`CTA.pow`);
`τ i` is a concrete complete trace of `I ^ i` ending in `done` (the standing
assumption of `CheckWellSynchronized`, one per unrolling); and `ws` is
`CheckWellSynchronized`'s `Bool` verdict. `List.all` short-circuits, so the first
failing unrolling makes the whole check `false`, exactly as `return false` does.

The trace family `τ` is indexed by `Fin (2k + 1)` — exactly one trace per unrolling
in `[0, 2k]`, the only inputs the check ever consults — rather than a total
`Nat → List Config`, which would demand a trace for every unrolling the check ignores.

Checking the unrollings out to `2k` (two batches of `I ^ k`) is what
`CTA.WellSynchronized.loop_well_synchronized` shows to be sufficient: if every
prefix up to two batches is well-synchronized, *every* unrolling is, so the loop is
safe for any iteration count. The range `[0, 2k]` is read inclusively.

`noncomputable` because `loopK` is (it is an LCM defined via the arrival-count
witness). -/
noncomputable def checkLoopWellSynchronized (P : CTA) (I : CTA) (E : CTA)
    (h : I.ConsistentArrivalCounts)
    (h1 : P.ids = I.ids) (h2 : I.ids = E.ids)
    (τp : List Config) (τpk : List Config)
    (τ : Fin (3 * I.loopK h + 1) → List Config) : Bool :=
  (CheckWellSynchronized P τp).1 &&
  (CheckWellSynchronized (P.seq (I ^ I.loopK h)
      (h1.trans (CTA.pow_ids I (I.loopK h)).symm)) τpk).1 &&
  (List.finRange (3 * I.loopK h + 1)).all fun i =>
    (CheckWellSynchronized (CTA.loopProgram P I E h1 h2 i.val) (τ i)).1

/-!
## Step 2 of Theorem 1: the arrival-count lower bound

After `k = loopK` iterations the total arrivals on every referenced barrier `b`
reach its arrival count: `arrival-count(b) ≤ arrivers(I ^ k)(b)`
(`CTA.arrivalCount_le_pow_arrivers`). This is the static arithmetic core of
Theorem 1, combining: arrivals scale linearly with iterations
(`arrivers_pow`); the per-barrier factor `f(b)` satisfies `c ≤ f(b)·a`
(`loopFactor_mul_ge`); and `f(b) ∣ loopK` with `loopK > 0`, so `f(b) ≤ loopK`.
-/

/-- `(I ^ (k+1)).prog i = I.prog i ++ (I ^ k).prog i`: one more copy of `I` runs
first, then the remaining `k`. -/
theorem CTA.pow_succ_prog (I : CTA) (k : Nat) (i : ThreadId) :
    (I ^ (k + 1)).prog i = I.prog i ++ (I ^ k).prog i := by
  rw [CTA.pow_succ]; rfl

/-- Arrivals on `b` scale linearly with the iteration count:
`(I ^ k).arrivers b = k * I.arrivers b`. -/
theorem CTA.arrivers_pow (I : CTA) (b : Barrier) (k : Nat) :
    (I ^ k).arrivers b = k * I.arrivers b := by
  induction k with
  | zero => simp [CTA.pow_zero, CTA.arrivers, CTA.emptied]
  | succ k ih =>
    have hk : (I ^ k).arrivers b
        = ∑ i ∈ I.ids, (((I ^ k).prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
      rw [CTA.arrivers, CTA.pow_ids]
    have hk1 : (I ^ (k + 1)).arrivers b
        = ∑ i ∈ I.ids,
            (((I ^ (k + 1)).prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
      rw [CTA.arrivers, CTA.pow_ids]
    rw [hk1]
    have key : (∑ i ∈ I.ids,
            (((I ^ (k + 1)).prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
        = (∑ i ∈ I.ids, ((I.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
          + ∑ i ∈ I.ids,
              (((I ^ k).prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [CTA.pow_succ_prog, List.filterMap_append, List.countP_append]
    rw [key, ← hk, ih]
    change I.arrivers b + k * I.arrivers b = (k + 1) * I.arrivers b
    rw [Nat.add_mul, one_mul]
    exact Nat.add_comm _ _

/-- A barrier in `I.barriers` is genuinely referenced: some thread's program contains
an `arrive`/`sync` on it with a positive count. -/
theorem CTA.exists_ref_of_mem_barriers (I : CTA) {b : Barrier} (hb : b ∈ I.barriers) :
    ∃ i ∈ I.ids, ∃ c ∈ I.prog i, ∃ n : ℕ+, Cmd.barrierRef c = some (b, n) := by
  simp only [CTA.barriers, Finset.mem_biUnion, List.mem_toFinset, List.mem_map,
    List.mem_filterMap] at hb
  obtain ⟨i, hi, ⟨b', n⟩, ⟨c, hc, href⟩, hp1⟩ := hb
  change b' = b at hp1
  subst hp1
  exact ⟨i, hi, c, hc, n, href⟩

/-- Under the consistency assumption, `arrivalCount` reads off the count of any actual
reference: an `arrive`/`sync b n` in thread `i` forces `I.arrivalCount h b = n`. -/
theorem CTA.arrivalCount_eq_of_ref (I : CTA) (h : I.ConsistentArrivalCounts)
    {i : ThreadId} {b : Barrier} {c : Cmd} {n : ℕ+}
    (hi : i ∈ I.ids) (hc : c ∈ I.prog i) (href : Cmd.barrierRef c = some (b, n)) :
    I.arrivalCount h b = (n : Nat) :=
  h.choose_spec i hi c hc b n href

/-- `arrivers(b) ≥ 1` for a referenced barrier. -/
theorem CTA.arrivers_pos (I : CTA) {b : Barrier} (hb : b ∈ I.barriers) :
    0 < I.arrivers b := by
  obtain ⟨i, hi, c, hc, n, href⟩ := I.exists_ref_of_mem_barriers hb
  rw [CTA.arrivers]
  have hterm : 0 < ((I.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) :=
    List.countP_pos_iff.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hc, href⟩, by simp⟩
  refine lt_of_lt_of_le hterm
    (Finset.single_le_sum
      (f := fun j => ((I.prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
      (fun j _ => Nat.zero_le _) hi)

/-- `arrival-count(b) ≥ 1` for a referenced barrier (its count is a positive `ℕ+`). -/
theorem CTA.arrivalCount_pos (I : CTA) (h : I.ConsistentArrivalCounts) {b : Barrier}
    (hb : b ∈ I.barriers) : 0 < I.arrivalCount h b := by
  obtain ⟨i, hi, c, hc, n, href⟩ := I.exists_ref_of_mem_barriers hb
  rw [I.arrivalCount_eq_of_ref h hi hc href]
  exact n.pos

/-- The per-barrier factor is positive when both arrivers and arrival-count are. -/
theorem loopFactor_pos {a c : Nat} (ha : 0 < a) (hc : 0 < c) : 0 < loopFactor a c := by
  unfold loopFactor
  split_ifs with h1 h2 h3
  · omega
  · exact Nat.div_pos (Nat.le_of_dvd hc h2) ha
  · omega
  · exact Nat.lcm_pos ha hc

/-- In each `loopFactor` case, one iteration's arrivals scaled by the factor cover the
arrival count: `c ≤ loopFactor a c * a` (for `a, c > 0`). -/
theorem loopFactor_mul_ge {a c : Nat} (ha : 0 < a) (hc : 0 < c) :
    c ≤ loopFactor a c * a := by
  unfold loopFactor
  split_ifs with h1 h2 h3
  · omega
  · exact le_of_eq (Nat.div_mul_cancel h2).symm
  · rw [one_mul]; exact Nat.le_of_dvd ha h3
  · have hlcm : c ≤ Nat.lcm a c := Nat.le_of_dvd (Nat.lcm_pos ha hc) (Nat.dvd_lcm_right a c)
    have h2 : Nat.lcm a c * 1 ≤ Nat.lcm a c * a := Nat.mul_le_mul (le_refl _) ha
    simp only [Nat.mul_one] at h2
    omega

/-- In each `loopFactor` case, the arrival count `c` *exactly divides* one factor's worth
of arrivals: `c ∣ loopFactor a c * a`. (Sharpens `loopFactor_mul_ge` from `≤` to `∣`.) This
is what makes the total arrivals over `loopK` iterations a whole number of generations. -/
theorem loopFactor_mul_dvd {a c : Nat} (_ : 0 < a) (_ : 0 < c) :
    c ∣ loopFactor a c * a := by
  unfold loopFactor
  split_ifs with h1 h2 h3
  · rw [one_mul, h1]
  · rw [Nat.div_mul_cancel h2]
  · rw [one_mul]; exact h3
  · exact Dvd.dvd.mul_right (Nat.dvd_lcm_right a c) a

/-- The factor `f(b)` divides `k = loopK` (it is one of the LCM's arguments). -/
theorem CTA.loopFactor_dvd_loopK (I : CTA) (h : I.ConsistentArrivalCounts) {b : Barrier}
    (hb : b ∈ I.barriers) :
    loopFactor (I.arrivers b) (I.arrivalCount h b) ∣ I.loopK h := by
  rw [CTA.loopK]
  exact Finset.dvd_lcm hb

/-- `loopK > 0`: it is an LCM of positive per-barrier factors. -/
theorem CTA.loopK_pos (I : CTA) (h : I.ConsistentArrivalCounts) : 0 < I.loopK h := by
  rw [CTA.loopK]
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro x hx
  exact (loopFactor_pos (I.arrivers_pos hx) (I.arrivalCount_pos h hx)).ne'

/-- **Step 2 (§1).** For a referenced barrier `b`, the total arrivals over `k = loopK`
iterations reach the arrival count: `arrival-count(b) ≤ arrivers(I ^ k)(b)`. -/
theorem CTA.arrivalCount_le_pow_arrivers (I : CTA) (h : I.ConsistentArrivalCounts)
    {b : Barrier} (hb : b ∈ I.barriers) :
    I.arrivalCount h b ≤ (I ^ I.loopK h).arrivers b := by
  have ha : 0 < I.arrivers b := I.arrivers_pos hb
  have hc : 0 < I.arrivalCount h b := I.arrivalCount_pos h hb
  have hfle : loopFactor (I.arrivers b) (I.arrivalCount h b) ≤ I.loopK h :=
    Nat.le_of_dvd (I.loopK_pos h) (I.loopFactor_dvd_loopK h hb)
  calc I.arrivalCount h b
      ≤ loopFactor (I.arrivers b) (I.arrivalCount h b) * I.arrivers b := loopFactor_mul_ge ha hc
    _ ≤ I.loopK h * I.arrivers b := Nat.mul_le_mul hfle (le_refl _)
    _ = (I ^ I.loopK h).arrivers b := (I.arrivers_pow b (I.loopK h)).symm

/-- **Step 2′.** The total arrivals over `k = loopK` iterations are an exact multiple of
the arrival count: `arrival-count(b) ∣ arrivers(I ^ k)(b)`. Since `arrivers(I ^ k) b =
k * arrivers(b)` and `f(b) ∣ k` with `arrival-count(b) ∣ f(b) * arrivers(b)`, the count
divides the total. This is the divisibility that makes the recycle count come out exact. -/
theorem CTA.arrivalCount_dvd_pow_arrivers (I : CTA) (h : I.ConsistentArrivalCounts)
    {b : Barrier} (hb : b ∈ I.barriers) :
    I.arrivalCount h b ∣ (I ^ I.loopK h).arrivers b := by
  have ha : 0 < I.arrivers b := I.arrivers_pos hb
  have hc : 0 < I.arrivalCount h b := I.arrivalCount_pos h hb
  obtain ⟨t, ht⟩ := I.loopFactor_dvd_loopK h hb
  rw [I.arrivers_pow b (I.loopK h), ht, Nat.mul_right_comm]
  exact (loopFactor_mul_dvd ha hc).mul_right t

/-!
## Step 3 of Theorem 1: the arrival potential is conserved without recycling

The key dynamic invariant. For a barrier `b`, define the *arrival potential*
`Φ_b(C) := |arrived(b)| + (remaining arrive/sync-on-b commands across all threads)`.
Every step that is **not** a recycle of `b` preserves `Φ_b`: an `arrive`-on-`b`
increments the arrived count (−1 command, +1 arrived); a `sync`-on-`b`
registers but stays in the program (no change — the registration is "pending" in
the command count); steps on other barriers and reads/writes leave both summands
alone; and `done` only fires with empty programs (the command count is already 0).
A recycle of `b` is the only step that drops `Φ_b` (by the arrival count `n`). Hence
along a recycle-free trace `Φ_b` is constant, which pins the final `|arrived(b)|` to
the total number of `arrive`/`sync`-on-`b` commands — i.e. to `arrivers`.
-/

/-- Remaining `arrive`/`sync`-on-`b` commands across all threads (one summand of the
arrival potential); `0` once every thread has returned (`done`). -/
def Config.barrierProgCount (b : Barrier) : Config → Nat
  | .run _ T => ∑ i ∈ T.ids, ((T.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
  | .done _ => 0
  | .err T  => ∑ i ∈ T.ids, ((T.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)

/-- Number of threads currently *arrived* (non-blocking) at `b`. -/
def Config.arrivedLen (b : Barrier) : Config → Nat
  | .run s _ => (s.B b).arrived
  | .done s  => (s.B b).arrived
  | .err _   => 0

/-- The **arrival potential** of `b`: pending arrived registrations plus remaining
`arrive`/`sync`-on-`b` commands. Conserved by every non-recycle-of-`b` step. -/
def Config.barrierPotential (b : Barrier) (C : Config) : Nat :=
  C.arrivedLen b + C.barrierProgCount b

/-- Updating one thread's program changes the `arrive`/`sync`-on-`b` command count by
the per-thread difference (stated additively to avoid `Nat` subtraction; mirrors
`numCmds_set`). -/
theorem acountSum_set {T : CTA} {i : ThreadId} (hi : i ∈ T.ids) (P' : Prog) (b : Barrier) :
    (∑ j ∈ T.ids, (((T.set i hi P').prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
      + ((T.prog i).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
    = (∑ j ∈ T.ids, ((T.prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
      + (P'.filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
  have hset : ∀ j, (((T.set i hi P').prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
      = Function.update
          (fun k => ((T.prog k).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)) i
          ((P'.filterMap Cmd.barrierRef).countP (fun r => r.1 == b)) j := by
    intro j
    by_cases h : j = i
    · subst h; simp [CTA.set]
    · simp [CTA.set, Function.update_of_ne h]
  rw [Finset.sum_congr rfl (fun j _ => hset j), Finset.sum_update_of_mem hi,
      ← Finset.erase_eq, ← Finset.add_sum_erase T.ids _ hi]
  omega

/-- The `arrive`/`sync`-on-`b` command count of `arrive b₀ n :: c`: one more than
that of `c` exactly when `b₀ = b`. -/
private theorem acount_arrive_cons (b b₀ : Barrier) (n : ℕ+) (c : Prog) :
    ((Cmd.arrive b₀ n :: c).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
      = ((c.filterMap Cmd.barrierRef).countP (fun r => r.1 == b)) + (if b₀ = b then 1 else 0) := by
  rw [List.filterMap_cons_some (show Cmd.barrierRef (Cmd.arrive b₀ n) = some (b₀, n) from rfl),
      List.countP_cons]
  congr 1
  by_cases h : b₀ = b
  · subst h; simp
  · simp [h, beq_eq_false_iff_ne.mpr h]

/-- Dropping a non-`b` `arrive`/`sync` head does not change the `arrive`/`sync`-on-`b`
count: `arrive b₀ n :: c` and `c` agree when `b₀ ≠ b`. -/
private theorem acount_read_cons (b : Barrier) (g : Loc) (c : Prog) :
    ((Cmd.read g :: c).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
      = (c.filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
  rw [List.filterMap_cons_none (show Cmd.barrierRef (Cmd.read g) = none from rfl)]

private theorem acount_write_cons (b : Barrier) (g : Loc) (c : Prog) :
    ((Cmd.write g :: c).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
      = (c.filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
  rw [List.filterMap_cons_none (show Cmd.barrierRef (Cmd.write g) = none from rfl)]

/-- **The conservation lemma.** Any step that is not a recycle of `b` (and does not go
to the error state) preserves `b`'s arrival potential. -/
theorem barrierPotential_step {b : Barrier} {C C' : Config} (hstep : CTAStep C C')
    (hnr : stepRecyclesBarrier b C C' = false) (hne : ∀ T, C' ≠ Config.err T) :
    C'.barrierPotential b = C.barrierPotential b := by
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
    have hsum := acountSum_set hi P' b
    have hbpc : (Config.run s' (T.set i hi P')).barrierProgCount b
        = ∑ j ∈ T.ids,
            (((T.set i hi P').prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := rfl
    have hbpcR : (Config.run s T).barrierProgCount b
        = ∑ j ∈ T.ids, ((T.prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := rfl
    simp only [Config.barrierPotential, Config.arrivedLen]
    rw [hbpc, hbpcR]
    generalize hpi : T.prog i = Pi at hth hsum
    cases hth with
    | read_noop => rw [acount_read_cons] at hsum; omega
    | write_noop => rw [acount_write_cons] at hsum; omega
    | arrive_configure he hb0 =>
      rename_i b₀ n
      rw [acount_arrive_cons] at hsum
      by_cases hbb : b = b₀
      · subst hbb
        rw [if_pos rfl] at hsum
        simp only [Function.update_self, hb0, BarrierState.unconfigured]
        omega
      · rw [if_neg (Ne.symm hbb)] at hsum
        simp only [Function.update_of_ne hbb]
        omega
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      rw [acount_arrive_cons] at hsum
      by_cases hbb : b = b₀
      · subst hbb
        rw [if_pos rfl] at hsum
        simp only [Function.update_self, hb0]
        omega
      · rw [if_neg (Ne.symm hbb)] at hsum
        simp only [Function.update_of_ne hbb]
        omega
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, hb0, BarrierState.unconfigured]
        omega
      · simp only [Function.update_of_ne hbb]; omega
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, hb0]
        omega
      · simp only [Function.update_of_ne hbb]; omega
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    by_cases hbb : b = b₀
    · exfalso
      subst hbb
      simp only [stepRecyclesBarrier, Config.state?, hb, BarrierState.isFull, hfull,
        Function.update_self, BarrierState.unconfigured, beq_self_eq_true, decide_true,
        Bool.and_self] at hnr
      exact absurd hnr (by decide)
    · simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
      have hbpcw : (∑ j ∈ (T.wake I₀).ids,
            (((T.wake I₀).prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b))
          = ∑ j ∈ T.ids, ((T.prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [CTA.wake]
        by_cases hj : j ∈ I₀
        · simp only [if_pos hj]
          have hh := hpark j hj
          have hjne : T.prog j ≠ [] := fun hnil => by rw [hnil] at hh; simp at hh
          obtain ⟨x, tl, hxtl⟩ := List.exists_cons_of_ne_nil hjne
          rw [hxtl] at hh ⊢
          rw [List.head?_cons, Option.some.injEq] at hh
          subst hh
          have hsync : Cmd.barrierRef (Cmd.sync b₀ n₀) = some (b₀, n₀) := rfl
          rw [List.tail_cons, List.filterMap_cons_some hsync, List.countP_cons]
          simp [beq_eq_false_iff_ne.mpr (Ne.symm hbb)]
        · simp only [if_neg hj]
      rw [hbpcw]
      simp only [Function.update_of_ne hbb]
  | @done s T hdone _ =>
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
    rw [Finset.sum_eq_zero (fun j hj => by rw [hdone j hj]; simp)]
  | @error s T i P' hth => exact absurd rfl (hne T)

/-- If no step of `τ` recycles `b` and no configuration is the error state, then `b`'s
arrival potential is the same at the end of `τ` as at the start. -/
theorem barrierPotential_conservation (b : Barrier) :
    ∀ {τ : List Config} {C₀ Cn : Config}, List.IsChain CTAStep τ →
      τ.head? = some C₀ → τ.getLast? = some Cn →
      (∀ C ∈ τ, ∀ T, C ≠ Config.err T) →
      (∀ j C C', τ[j]? = some C → τ[j+1]? = some C' → stepRecyclesBarrier b C C' = false) →
      Cn.barrierPotential b = C₀.barrierPotential b := by
  intro τ
  induction τ with
  | nil => intro C₀ Cn _ hhead _ _ _; simp at hhead
  | cons a rest ih =>
    intro C₀ Cn hchain hhead hlast hne hnr
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hlast
      rw [hlast]
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hstepeq : b₁.barrierPotential b = a.barrierPotential b :=
        barrierPotential_step hstep (hnr 0 a b₁ rfl rfl) (fun T => hne b₁ (by simp) T)
      have hlast' : (b₁ :: rest').getLast? = some Cn := by
        rwa [List.getLast?_cons_cons] at hlast
      have hnr' : ∀ j C C', (b₁ :: rest')[j]? = some C → (b₁ :: rest')[j+1]? = some C' →
          stepRecyclesBarrier b C C' = false := fun j C C' hC hC' =>
        hnr (j + 1) C C' (by rw [List.getElem?_cons_succ]; exact hC)
          (by rw [List.getElem?_cons_succ]; exact hC')
      rw [ih hchain' rfl hlast' (fun C hC => hne C (List.mem_cons_of_mem _ hC)) hnr', hstepeq]

/-- `recycleCount b τ (len-1) = 0` means no consecutive pair of `τ` recycles `b`. -/
theorem noRecycle_of_recycleCount_zero (b : Barrier) {τ : List Config}
    (h : recycleCount b τ (τ.length - 1) = 0) :
    ∀ j C C', τ[j]? = some C → τ[j+1]? = some C' → stepRecyclesBarrier b C C' = false := by
  intro j C C' hC hC'
  rw [recycleCount, List.countP_eq_zero] at h
  have hj1 : j + 1 < τ.length := (List.getElem?_eq_some_iff.mp hC').1
  have hpred := h j (List.mem_range.mpr (by omega))
  simp only [hC, hC', Bool.not_eq_true] at hpred
  exact hpred

/-- Every command of `I ^ k` is a command of `I` (the power just repeats `I`). -/
theorem CTA.mem_pow_prog (I : CTA) {i : ThreadId} {c : Cmd} :
    ∀ {k : Nat}, c ∈ (I ^ k).prog i → c ∈ I.prog i := by
  intro k
  induction k with
  | zero => intro hc; simp [CTA.pow_zero, CTA.emptied] at hc
  | succ k ih => intro hc; rw [CTA.pow_succ_prog, List.mem_append] at hc; exact hc.elim id ih

/-- Along a chain, every configuration's remaining program is a suffix of the head's
program — programs only shrink as the trace advances. -/
theorem progOf_suffix_head : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → ∀ C ∈ τ, ∀ t, C.progOf t <:+ C₀.progOf t := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead C hC t
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact List.suffix_refl _
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact List.suffix_refl _
      · exact (ih hchain' rfl C hC' t).trans (hstep.progOf_suffix t)

/-- `b`'s configured thread count at a configuration (`none` if unconfigured or at the
error state). -/
def Config.bcount (b : Barrier) : Config → Option ℕ+
  | .run s _ => (s.B b).count
  | .done s  => (s.B b).count
  | .err _   => none

/-- One step preserves "`b`'s configured count is `nb`", given that every `b`-command
of the source uses count `nb` (the consistency fact, supplied per configuration). A
fresh configuration of `b` reads its count from the executing command; re-registration
keeps the (already-`nb`) count; recycling unconfigures `b`. -/
theorem bcount_step {b : Barrier} {nb : Nat} {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ n', C.bcount b = some n' → (n' : Nat) = nb)
    (hcmd : ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) → (m : Nat) = nb) :
    ∀ n', C'.bcount b = some n' → (n' : Nat) = nb := by
  intro n' hn'
  cases hstep with
  | @interleave s s' T i P' hi hbar hth =>
    simp only [Config.bcount] at hn' hC
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hC n' hn'
    | write_noop => exact hC n' hn'
    | arrive_configure he hb0 =>
      rename_i b₀ n
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.arrive b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        have hnnb := hcmd i (Cmd.arrive b n) hmem n rfl
        simp only [Function.update_self, Option.some.injEq] at hn'
        rw [← hn']; exact hnnb
      · simp only [Function.update_of_ne hbb] at hn'; exact hC n' hn'
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, Option.some.injEq] at hn'
        rw [← hn']; exact hC n (by rw [hb0])
      · simp only [Function.update_of_ne hbb] at hn'; exact hC n' hn'
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.sync b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        have hnnb := hcmd i (Cmd.sync b n) hmem n rfl
        simp only [Function.update_self, Option.some.injEq] at hn'
        rw [← hn']; exact hnnb
      · simp only [Function.update_of_ne hbb] at hn'; exact hC n' hn'
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, Option.some.injEq] at hn'
        rw [← hn']; exact hC n (by rw [hb0])
      · simp only [Function.update_of_ne hbb] at hn'; exact hC n' hn'
  | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
    simp only [Config.bcount] at hn' hC
    by_cases hbb : b = b₀
    · subst hbb; simp [Function.update_self, BarrierState.unconfigured] at hn'
    · simp only [Function.update_of_ne hbb] at hn'; exact hC n' hn'
  | @done s T hdone _ =>
    simp only [Config.bcount] at hn' hC
    exact hC n' hn'
  | @error s T i P' hth => simp [Config.bcount] at hn'

/-- The count-consistency invariant propagates along a chain: if `b`'s count is `nb`
at the head and every configuration uses count `nb` on its `b`-commands, then `b`'s
count is `nb` at every configuration. -/
theorem bcount_chain {b : Barrier} {nb : Nat} :
    ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ → τ.head? = some C₀ →
      (∀ n', C₀.bcount b = some n' → (n' : Nat) = nb) →
      (∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
        (m : Nat) = nb) →
      ∀ C ∈ τ, ∀ n', C.bcount b = some n' → (n' : Nat) = nb := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ hcmd C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ n', b₁.bcount b = some n' → (n' : Nat) = nb :=
        bcount_step hstep hC₀ (hcmd a (by simp))
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 (fun C hC'' => hcmd C (List.mem_cons_of_mem _ hC'')) C hC'

/-- In a chain, the last configuration is either the head or has a predecessor *in the
chain* that steps to it. -/
theorem getLast_has_pred_mem : ∀ {τ : List Config} {x : Config}, List.IsChain CTAStep τ →
    τ.getLast? = some x → τ.head? = some x ∨ ∃ y ∈ τ, CTAStep y x := by
  intro τ
  induction τ with
  | nil => intro x _ hlast; simp at hlast
  | cons a rest ih =>
    intro x hchain hlast
    cases rest with
    | nil => left; rw [List.getLast?_singleton] at hlast; rwa [List.head?_cons]
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.getLast?_cons_cons] at hlast
      rcases ih hbt hlast with hhead | ⟨y, hy_mem, hy_step⟩
      · right
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨a, by simp, hhead ▸ hab⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy_mem, hy_step⟩

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

/-- A *full* barrier state is not the unconfigured state (its count is `some _`). -/
theorem BarrierState.isFull_ne_unconfigured {β : BarrierState} (h : β.isFull = true) :
    β ≠ BarrierState.unconfigured := by
  intro he; rw [he] at h; simp [BarrierState.isFull, BarrierState.unconfigured] at h

/-- **The recycle drop.** Recycling a *duplicate-free* full barrier `b` (count `n₀`)
lowers `b`'s arrival potential by exactly `n₀`: the `A₀` arrived registrations are
cleared and the `I₀` woken threads each drop their parked `sync b n₀` command, and
`|I₀| + A₀ = n₀`. Duplicate-freeness (`hnd`) is what makes the woken-thread command
drop equal to `I₀.length` rather than the number of *distinct* woken ids. -/
theorem barrierPotential_recycle_eq {s : State} {T : CTA} {b : Barrier}
    {I₀ : List ThreadId} {A₀ : ℕ} {n₀ : ℕ+}
    (hb : s.B b = ⟨I₀, A₀, some n₀⟩) (hfull : I₀.length + A₀ = (n₀ : Nat))
    (hpark : ∀ i ∈ I₀, (T.prog i).head? = some (Cmd.sync b n₀)) (hnd : I₀.Nodup) :
    (Config.run s T).barrierPotential b
      = (Config.run
            (⟨updateMapOn s.E I₀ true, Function.update s.B b BarrierState.unconfigured⟩ : State)
            (T.wake I₀)).barrierPotential b
        + (n₀ : Nat) := by
  have hsub : ∀ i ∈ I₀, i ∈ T.ids := by
    intro i hi
    by_contra hni
    have hh := hpark i hi
    rw [T.nil_outside_ids i hni] at hh; simp at hh
  have hcard : (T.ids.filter (· ∈ I₀)).card = I₀.length := by
    have hset : T.ids.filter (· ∈ I₀) = I₀.toFinset := by
      apply Finset.ext; intro x
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩
    rw [hset, List.toFinset_card_of_nodup hnd]
  have key : ∀ j ∈ T.ids,
      ((T.prog j).filterMap Cmd.barrierRef).countP (fun r => r.1 == b)
        = ((if j ∈ I₀ then (T.prog j).tail else T.prog j).filterMap Cmd.barrierRef).countP
            (fun r => r.1 == b) + (if j ∈ I₀ then 1 else 0) := by
    intro j _
    by_cases hj : j ∈ I₀
    · rw [if_pos hj, if_pos hj]
      have hh := hpark j hj
      have hjne : T.prog j ≠ [] := fun hnil => by rw [hnil] at hh; simp at hh
      obtain ⟨x, tl, hxtl⟩ := List.exists_cons_of_ne_nil hjne
      rw [hxtl] at hh ⊢
      rw [List.head?_cons, Option.some.injEq] at hh; subst hh
      rw [List.tail_cons,
        List.filterMap_cons_some (show Cmd.barrierRef (Cmd.sync b n₀) = some (b, n₀) from rfl),
        List.countP_cons]
      simp
    · rw [if_neg hj, if_neg hj]; simp
  simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, hb,
    Function.update_self, BarrierState.unconfigured, Nat.zero_add, CTA.wake]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.card_filter, hcard]
  omega

/-- **Per-step potential accounting.** Each step lowers `b`'s arrival potential by `nb`
if it recycles `b`, and by `0` otherwise. Non-recycle steps conserve it
(`barrierPotential_step`); a recycle of `b` drops it by its count `n₀ = nb`
(`barrierPotential_recycle_eq`, with duplicate-freeness supplied by `BlockInv`). All
other constructors cannot make `stepRecyclesBarrier b` true (`interleave`/`done` leave no
barrier full, a recycle of `b' ≠ b` leaves `b` non-unconfigured). -/
theorem barrierPotential_step_count {b : Barrier} {nb : Nat} {C C' : Config}
    (hstep : CTAStep C C') (hne : ∀ T, C' ≠ Config.err T)
    (hcount : ∀ n', C.bcount b = some n' → (n' : Nat) = nb)
    (hBI : ∀ s, C.state? = some s → s.BlockInv) :
    C.barrierPotential b
      = C'.barrierPotential b + (if stepRecyclesBarrier b C C' = true then nb else 0) := by
  by_cases hrec : stepRecyclesBarrier b C C' = true
  · rw [if_pos hrec]
    cases hstep with
    | @interleave s s' T i P' hi hbar hth =>
      exfalso
      have hfalse : (s.B b).isFull = false := by
        rcases hbar b with h | ⟨I, A, n, h, hlt⟩
        · rw [h]; rfl
        · rw [h]; simp only [BarrierState.isFull]; exact beq_false_of_ne (Nat.ne_of_lt hlt)
      simp [stepRecyclesBarrier, Config.state?, hfalse] at hrec
    | @recycle s T b₀ I₀ A₀ n₀ hb hfull hpark =>
      by_cases hbb : b = b₀
      · subst hbb
        have hnd : I₀.Nodup := by have h := (hBI s rfl).1 b; rwa [hb] at h
        have hn0 : (n₀ : Nat) = nb := hcount n₀ (by simp only [Config.bcount, hb])
        rw [← hn0]; exact barrierPotential_recycle_eq hb hfull hpark hnd
      · exfalso
        simp only [stepRecyclesBarrier, Config.state?, Function.update_of_ne hbb,
          Bool.and_eq_true] at hrec
        exact BarrierState.isFull_ne_unconfigured hrec.1 (of_decide_eq_true hrec.2)
    | @done s T hdone hnofull =>
      exfalso
      simp only [stepRecyclesBarrier, Config.state?, Bool.and_eq_true] at hrec
      exact BarrierState.isFull_ne_unconfigured hrec.1 (of_decide_eq_true hrec.2)
    | @error s T i P' hth => exact absurd rfl (hne T)
  · rw [Bool.not_eq_true] at hrec
    rw [if_neg (by rw [hrec]; simp), barrierPotential_step hstep hrec hne, Nat.add_zero]

/-- Head recurrence for `recycleCount` over a two-or-more-element chain: the recycles in
`a :: b₁ :: rest'` are the first step `a ⤳ b₁` plus the recycles in `b₁ :: rest'`. -/
theorem recycleCount_cons_cons (b : Barrier) (a b₁ : Config) (rest' : List Config) :
    recycleCount b (a :: b₁ :: rest') ((a :: b₁ :: rest').length - 1)
      = (if stepRecyclesBarrier b a b₁ = true then 1 else 0)
        + recycleCount b (b₁ :: rest') ((b₁ :: rest').length - 1) := by
  simp only [recycleCount, List.length_cons, Nat.add_sub_cancel]
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map, Nat.add_comm]
  congr 1

/-- **Recycle-counting conservation.** Generalizing `barrierPotential_conservation` to
runs that *do* recycle `b`: along an err-free chain whose `b`-counts are all `nb` and
whose states satisfy `BlockInv`, the head's arrival potential exceeds the last's by
exactly `nb` per recycle of `b`. Summed from the per-step accounting
(`barrierPotential_step_count`) via the `recycleCount` head recurrence. -/
theorem barrierPotential_with_recycles {b : Barrier} {nb : Nat} :
    ∀ {τ : List Config} {C₀ Cn : Config}, List.IsChain CTAStep τ →
      τ.head? = some C₀ → τ.getLast? = some Cn →
      (∀ C ∈ τ, ∀ T, C ≠ Config.err T) →
      (∀ C ∈ τ, ∀ n', C.bcount b = some n' → (n' : Nat) = nb) →
      (∀ C ∈ τ, ∀ s, C.state? = some s → s.BlockInv) →
      C₀.barrierPotential b = Cn.barrierPotential b + nb * recycleCount b τ (τ.length - 1) := by
  intro τ
  induction τ with
  | nil => intro C₀ Cn _ hhead _ _ _ _; simp at hhead
  | cons a rest ih =>
    intro C₀ Cn hchain hhead hlast hne hcount hBI
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hlast; subst hlast
      simp [recycleCount]
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hlast' : (b₁ :: rest').getLast? = some Cn := by rwa [List.getLast?_cons_cons] at hlast
      have hstepc := barrierPotential_step_count (b := b) (nb := nb) hstep
        (fun T => hne b₁ (by simp) T) (hcount a (by simp)) (hBI a (by simp))
      have ihr := ih hchain' rfl hlast'
        (fun C hC => hne C (List.mem_cons_of_mem _ hC))
        (fun C hC => hcount C (List.mem_cons_of_mem _ hC))
        (fun C hC => hBI C (List.mem_cons_of_mem _ hC))
      rw [recycleCount_cons_cons, hstepc, ihr, Nat.mul_add]
      split_ifs <;> omega

/-- One step keeps `b`'s barrier state *frozen* at a configured, **not-full** value
`⟨I₀, A₀, some n₀⟩` whose count `n₀` does **not** match `nb`, given that every
`b`-command of the source uses count `nb`. Such a `b` can never be touched: a recycle
needs `b` full (ruled out by `hlen`); a (re)registration on `b` runs `arrive/sync b n₀`,
forcing `n₀ = nb` by consistency (ruled out by `hne`); a fresh configuration needs `b`
unconfigured. So every step leaves `b`'s entry exactly as it was. The mirror of
`bcount_step` for the whole barrier-state, used to show a mismatched entry count would
have to persist unchanged to the final `done` — contradicting conservation. -/
theorem bstate_frozen_step {b : Barrier} {nb : Nat} {I₀ : List ThreadId} {A₀ : ℕ} {n₀ : ℕ+}
    (hlen : I₀.length + A₀ ≠ (n₀ : Nat)) (hne : (n₀ : Nat) ≠ nb)
    {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s', C.state? = some s' → s'.B b = ⟨I₀, A₀, some n₀⟩)
    (hcmd : ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) → (m : Nat) = nb) :
    ∀ s', C'.state? = some s' → s'.B b = ⟨I₀, A₀, some n₀⟩ := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hth =>
    have hCb : s.B b = ⟨I₀, A₀, some n₀⟩ := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hCb
    | write_noop => exact hCb
    | arrive_configure he hb0 =>
      rename_i b₀ n
      by_cases hbb : b = b₀
      · subst hbb; rw [hCb] at hb0; simp [BarrierState.unconfigured] at hb0
      · simp only [Function.update_of_ne hbb]; exact hCb
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.arrive b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        have hnnb := hcmd i (Cmd.arrive b n) hmem n rfl
        exfalso; apply hne
        have hn : n₀ = n := by
          have := hCb.symm.trans hb0
          simp only [BarrierState.mk.injEq, Option.some.injEq] at this; exact this.2.2
        rw [hn]; exact hnnb
      · simp only [Function.update_of_ne hbb]; exact hCb
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb; rw [hCb] at hb0; simp [BarrierState.unconfigured] at hb0
      · simp only [Function.update_of_ne hbb]; exact hCb
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.sync b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        have hnnb := hcmd i (Cmd.sync b n) hmem n rfl
        exfalso; apply hne
        have hn : n₀ = n := by
          have := hCb.symm.trans hb0
          simp only [BarrierState.mk.injEq, Option.some.injEq] at this; exact this.2.2
        rw [hn]; exact hnnb
      · simp only [Function.update_of_ne hbb]; exact hCb
  | @recycle s T b₀ I A n hb hfullr hpark =>
    have hCb : s.B b = ⟨I₀, A₀, some n₀⟩ := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    by_cases hbb : b = b₀
    · subst hbb
      exfalso; apply hlen
      have heq := hCb.symm.trans hb
      simp only [BarrierState.mk.injEq, Option.some.injEq] at heq
      obtain ⟨hI, hA, hn⟩ := heq
      rw [hI, hA, hn]; exact hfullr
    · simp only [Function.update_of_ne hbb]; exact hCb
  | @done s T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    exact hC s rfl
  | @error s T i P' hth => simp [Config.state?] at hs'

/-- Iterating `bstate_frozen_step` along a chain: a configured, not-full, count-`n₀ ≠ nb`
entry value for `b` at the head stays frozen at every configuration, given every
configuration's `b`-commands use `nb`. The mirror of `bcount_chain`. -/
theorem bstate_frozen_chain {b : Barrier} {nb : Nat} {I₀ : List ThreadId} {A₀ : ℕ} {n₀ : ℕ+}
    (hlen : I₀.length + A₀ ≠ (n₀ : Nat)) (hne : (n₀ : Nat) ≠ nb) :
    ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ → τ.head? = some C₀ →
      (∀ s', C₀.state? = some s' → s'.B b = ⟨I₀, A₀, some n₀⟩) →
      (∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
        (m : Nat) = nb) →
      ∀ C ∈ τ, ∀ s', C.state? = some s' → s'.B b = ⟨I₀, A₀, some n₀⟩ := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ hcmd C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ s', b₁.state? = some s' → s'.B b = ⟨I₀, A₀, some n₀⟩ :=
        bstate_frozen_step hlen hne hstep hC₀ (hcmd a (by simp))
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 (fun C hC'' => hcmd C (List.mem_cons_of_mem _ hC'')) C hC'

/-- **Entry count-consistency from a successful run.** If `b` is referenced by `I ^ k`
and is **not full** at the start state `s` (`(s.B b).isFull = false`, i.e. `b` is
unconfigured or strictly under-full), then along any err-free successful trace the head
count of `b` is exactly its arrival count.

The `isFull = false` premise is essential, and rules out a specific degenerate entry
state. If `b` were full at `s` with a *mismatched* count `n₀ ≠ arrival-count(b)`, then
from `run s (I ^ k)` neither `interleave` (its `hbar` needs every barrier strictly
under-full) nor `done` (its `hnofull` likewise) can fire: the *only* available step is
`recycle`, which erases `n₀ → none` before any `arrive/sync b (arrival-count b)` ever
compares against it. The run would still be a successful, err-free trace, yet the head
count would be the bogus `n₀` — so err-freeness alone cannot pin it. Forbidding a full
entry (`isFull = false`) is exactly what excludes that case: an under-full `b` blocks no
step, no `arrive/sync` on `b` can succeed against a wrong count (`arrive_err_count` /
`sync_err_count`), and the thread that must eventually run its `arrive/sync b
(arrival-count b)` to reach `done` errs unless the count already matches. -/
theorem Config.WellSynchronized.headCount_consistent_of_successful {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State} {b : Barrier}
    -- avoids the full-at-entry case: a full `b` forces an immediate `recycle` that
    -- erases its (possibly mismatched) count before any command tests it.
    (hfull : (s.B b).isFull = false) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet) :
    ∀ n', (s.B b).count = some n' → (n' : Nat) = I.arrivalCount h b := by
  intro n' hn'
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, s_d, hlast⟩ := hτ
  set k := I.loopK h with hk
  set nb := I.arrivalCount h b with hnb
  by_contra hcon
  -- `b` is configured under-full at `s` with the (assumed) mismatched count `n'`
  have hβ : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ := by rw [← hn']
  have hlen : (s.B b).synced.length + (s.B b).arrived ≠ (n' : Nat) := by
    simp only [BarrierState.isFull, hn'] at hfull
    intro heq; rw [heq] at hfull; simp at hfull
  -- `b ∈ I.barriers` (referenced by the loop body, not just the unrolling)
  have hbI : b ∈ I.barriers := by
    rw [CTA.barrierSet, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hbi⟩ := hb
    rw [List.mem_toFinset, List.mem_filterMap] at hbi
    obtain ⟨c, hc, hcb⟩ := hbi
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc
    have hi' : i ∈ I.ids := by rw [← CTA.pow_ids I k]; exact hi
    obtain ⟨n, hbref⟩ : ∃ n, Cmd.barrierRef c = some (b, n) := by
      cases c with
      | read g => simp [Cmd.barrier?] at hcb
      | write g => simp [Cmd.barrier?] at hcb
      | arrive b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
      | sync b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi', List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  have hstep2 : nb ≤ (I ^ k).arrivers b := I.arrivalCount_le_pow_arrivers h hbI
  have hnbpos : 0 < nb := I.arrivalCount_pos h hbI
  -- every configuration in `τ` is `run` or `done`, never `err`
  have hno_err : ∀ C ∈ τ, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : τ ≠ [] := by rintro rfl; simp at hhead
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at hlast
      rw [hlast, hCerr] at hCl; exact Config.noConfusion hCl
  -- the consistency fact, available at every configuration via the suffix relation
  have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
      (m : Nat) = nb := by
    intro C hC i c hc m hbref
    have hc0 : c ∈ (Config.run s (I ^ k)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (I ^ k).prog i := by simpa [Config.progOf] using hc0
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc1
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    rw [hnb]; exact (h.choose_spec i hi c hcI b m hbref).symm
  -- the mismatched entry value of `b` stays frozen all the way to `done`
  have hJall : ∀ C ∈ τ, ∀ s', C.state? = some s' →
      s'.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ :=
    bstate_frozen_chain hlen hcon hchain hhead
      (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; exact hβ)
      hcmd_all
  have hbd : s_d.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ :=
    hJall (Config.done s_d) (List.mem_of_mem_getLast? hlast) s_d rfl
  -- frozen ⇒ `b` is never full ⇒ no step recycles `b`
  have hnorec : ∀ j C C', τ[j]? = some C → τ[j+1]? = some C' →
      stepRecyclesBarrier b C C' = false := by
    intro j C C' hCj hC'j
    have hCmem : C ∈ τ := List.mem_of_getElem? hCj
    cases hCs : C.state? with
    | none => simp [stepRecyclesBarrier, hCs]
    | some sC =>
      have hfullC : (sC.B b).isFull = false := by
        rw [hJall C hCmem sC hCs]
        simp only [BarrierState.isFull]
        exact beq_false_of_ne hlen
      cases hC's : C'.state? with
      | none => simp [stepRecyclesBarrier, hCs, hC's]
      | some sC' => simp [stepRecyclesBarrier, hCs, hC's, hfullC]
  -- conservation then forces `arrivers (I ^ k) b = 0`, impossible for a referenced barrier
  have hcons := barrierPotential_conservation b hchain hhead hlast hno_err hnorec
  have hdonepot : (Config.done s_d).barrierPotential b = (s.B b).arrived := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount,
      Nat.add_zero, hbd]
  have hheadpot : (Config.run s (I ^ k)).barrierPotential b
      = (s.B b).arrived + (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  rw [hdonepot, hheadpot] at hcons
  have : 0 < (I ^ k).arrivers b := lt_of_lt_of_le hnbpos hstep2
  omega

/-- **Theorem 1 (partial).** Let `k = I.loopK h` be the §1 iteration count (for a
consistency witness `h`). If `I ^ k` is run from a well-formed state `s` in which `b`
is **not full** (`(s.B b).isFull = false`), then along any successful trace `τ` of
`I ^ k` starting at `s`, every barrier `b` used by `I ^ k` is recycled at least once —
its generation increases by at least one.

The hypotheses `hwf` (the start state is well-formed) and `hfull` (`b` is unconfigured
or strictly under-full at `s`) hold for free at the initial configuration (`WF_initial`,
`State.initial`: `b` is unconfigured, so `hfull` is immediate). `hfull` replaces the
former "`b` unconfigured" requirement, so the theorem now also applies at a non-initial
start state with `b` already partially registered; it discharges the head
count-consistency obligation via `headCount_consistent_of_successful` (which is also
where the case `hfull` avoids is documented).

The argument is by contradiction: if `b` were never recycled, its *arrival potential*
(`barrierPotential_conservation`) pins the number of threads finally arrived at `b` to
`arrivers(I ^ k) b ≥ arrival-count(b)` (`arrivalCount_le_pow_arrivers`), while the
final `done` step's premise and the count-consistency invariant (`bcount_chain`) force
that number strictly below `arrival-count(b)` — a contradiction.
NOTE (rohany): This is an important, top-level theorem. -/
theorem Config.WellSynchronized.pow_barriers_advance {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State} {b : Barrier}
    (hwf : (Config.run s (I ^ I.loopK h)).WF)
    -- avoids the full-at-entry case (see `headCount_consistent_of_successful`): a full
    -- `b` forces an immediate `recycle` that erases its count before any command tests it.
    (hfull : (s.B b).isFull = false)
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet) :
    1 ≤ recycleCount b τ (τ.length - 1) := by
  -- the head count of `b` is pinned to its arrival count by the successful (err-free) run
  have hb0 : ∀ n', (s.B b).count = some n' → (n' : Nat) = I.arrivalCount h b :=
    Config.WellSynchronized.headCount_consistent_of_successful h hfull hτ hb
  set k := I.loopK h with hk
  by_contra hcon
  rw [Nat.not_le, Nat.lt_one_iff] at hcon
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, s_d, hlast⟩ := hτ
  -- `b ∈ I.barriers` (referenced by the loop body, not just the unrolling)
  have hbI : b ∈ I.barriers := by
    rw [CTA.barrierSet, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hbi⟩ := hb
    rw [List.mem_toFinset, List.mem_filterMap] at hbi
    obtain ⟨c, hc, hcb⟩ := hbi
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc
    have hi' : i ∈ I.ids := by rw [← CTA.pow_ids I k]; exact hi
    obtain ⟨n, hbref⟩ : ∃ n, Cmd.barrierRef c = some (b, n) := by
      cases c with
      | read g => simp [Cmd.barrier?] at hcb
      | write g => simp [Cmd.barrier?] at hcb
      | arrive b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
      | sync b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi', List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  set nb := I.arrivalCount h b with hnb
  have hstep2 : nb ≤ (I ^ k).arrivers b := I.arrivalCount_le_pow_arrivers h hbI
  have hnbpos : 0 < nb := I.arrivalCount_pos h hbI
  -- every configuration in `τ` is `run` or `done`, never `err`
  have hno_err : ∀ C ∈ τ, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : τ ≠ [] := by rintro rfl; simp at hhead
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at hlast
      rw [hlast, hCerr] at hCl; exact Config.noConfusion hCl
  -- the consistency fact, available at every configuration via the suffix relation
  have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
      (m : Nat) = nb := by
    intro C hC i c hc m hbref
    have hc0 : c ∈ (Config.run s (I ^ k)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (I ^ k).prog i := by simpa [Config.progOf] using hc0
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc1
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    rw [hnb]; exact (h.choose_spec i hi c hcI b m hbref).symm
  -- conservation: the final number arrived at `b` equals `arrivers (I ^ k) b`
  have hcons := barrierPotential_conservation b hchain hhead hlast hno_err
    (noRecycle_of_recycleCount_zero b hcon)
  -- a lower bound on the start potential suffices (any starting residue only helps);
  -- the program command-count alone already accounts for all `arrivers (I ^ k) b`
  have hC₀pot : (I ^ k).arrivers b ≤ (Config.run s (I ^ k)).barrierPotential b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
    exact Nat.le_add_left _ _
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hdonepot] at hcons
  have harr : nb ≤ (s_d.B b).arrived := by rw [hcons]; exact le_trans hstep2 hC₀pot
  -- count consistency at `done s_d`
  have hbcount := bcount_chain hchain hhead
    (by intro n' hn'; exact hb0 n' (by simpa only [Config.bcount] using hn'))
    hcmd_all (Config.done s_d) (List.mem_of_mem_getLast? hlast)
  -- the predecessor of `done s_d` is the `done` step, which carries `hnofull`
  obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s_d) := by
    rcases getLast_has_pred_mem hchain hlast with hh | hp
    · rw [hhead] at hh; exact absurd hh (by simp)
    · exact hp
  have hwf_y : y.WF := WF_chain hchain hhead hwf y hy_mem
  cases hy_step with
  | @done sd T' hdone hnofull =>
    by_cases hcfg : (s_d.B b).count = none
    · have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, none⟩ := by rw [← hcfg]
      have harr0 := (hwf_y.2.1 b (s_d.B b).synced (s_d.B b).arrived heq).2
      rw [harr0] at harr; simp at harr; omega
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hbcount n' (by simp only [Config.bcount]; exact hn')
      have hlt := (hwf_y.1 b (s_d.B b).synced (s_d.B b).arrived n' heq).1
      have hlt2 := hnofull b (s_d.B b).synced (s_d.B b).arrived n' heq
      omega

/-- **Theorem 1 (partial, exact generation count).** Sharpening of
`pow_barriers_advance` from a lower bound to an exact count: over a successful trace
`τ` of `I ^ k` (with `k = I.loopK h`) starting at a well-formed state `s` in which `b`
is **not full**, every barrier `b` used by the loop is recycled *exactly*
`(k * arrivers(b)) / arrival-count(b)` times — its generation increases by precisely
that amount.

As in `pow_barriers_advance`, no "`b` unconfigured" assumption is made — `b` may already
be registered at `s`, subject only to `hfull` (`b` is not full at entry). `hfull` is doubly
necessary: it pins the head count (via `headCount_consistent_of_successful`) and rules out
a *full* entry generation, which would force one extra recycle before the loop even begins.
Duplicate-freeness of the synced lists — needed so each recycle consumes exactly
`arrival-count(b)` registrations (`barrierPotential_with_recycles`) — comes from `hwf`,
since the blocking invariant `s.BlockInv` is now part of well-formedness.

The proof: arrival-potential conservation-with-recycles gives
`|arrived(s)| + arrivers(I ^ k) b = |arrived(s_d)| + arrival-count(b) · R` where `R` is the
recycle count. Since `arrival-count(b) ∣ arrivers(I ^ k) b`
(`arrivalCount_dvd_pow_arrivers`) and both arrived-list lengths are `< arrival-count(b)`
(entry not full; exit under-full at `done`), the residues cancel modulo the count and
`R = arrivers(I ^ k) b / arrival-count(b) = k · arrivers(b) / arrival-count(b)`.
`pow_barriers_advance` is the `1 ≤ ·` corollary via `Nat.one_le_div_iff`.
NOTE (rohany): This is an important, top-level theorem.
-/
theorem Config.WellSynchronized.pow_barriers_advance_count {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State} {b : Barrier}
    (hwf : (Config.run s (I ^ I.loopK h)).WF)
    -- avoids the full-at-entry case (see `headCount_consistent_of_successful`): a full
    -- `b` is forced to `recycle` once before the loop body runs, which would add one
    -- recycle on top of the `(k * arrivers b) / arrival-count b` from the loop itself.
    (hfull : (s.B b).isFull = false)
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet) :
    recycleCount b τ (τ.length - 1) = I.loopK h * I.arrivers b / I.arrivalCount h b := by
  -- head count of `b` is its arrival count (from the successful, err-free run)
  have hb0 := Config.WellSynchronized.headCount_consistent_of_successful h hfull hτ hb
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, s_d, hlast⟩ := hτ
  set k := I.loopK h with hk
  set nb := I.arrivalCount h b with hnb
  -- `b ∈ I.barriers`
  have hbI : b ∈ I.barriers := by
    rw [CTA.barrierSet, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hbi'⟩ := hb
    rw [List.mem_toFinset, List.mem_filterMap] at hbi'
    obtain ⟨c, hc, hcb⟩ := hbi'
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc
    have hi' : i ∈ I.ids := by rw [← CTA.pow_ids I k]; exact hi
    obtain ⟨n, hbref⟩ : ∃ n, Cmd.barrierRef c = some (b, n) := by
      cases c with
      | read g => simp [Cmd.barrier?] at hcb
      | write g => simp [Cmd.barrier?] at hcb
      | arrive b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
      | sync b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi', List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  have hnbpos : 0 < nb := I.arrivalCount_pos h hbI
  have hdvd : nb ∣ (I ^ k).arrivers b := I.arrivalCount_dvd_pow_arrivers h hbI
  -- err-freeness, command-consistency, and the chain hypotheses
  have hno_err : ∀ C ∈ τ, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : τ ≠ [] := by rintro rfl; simp at hhead
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at hlast
      rw [hlast, hCerr] at hCl; exact Config.noConfusion hCl
  have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
      (m : Nat) = nb := by
    intro C hC i c hc m hbref
    have hc0 : c ∈ (Config.run s (I ^ k)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (I ^ k).prog i := by simpa [Config.progOf] using hc0
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc1
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    rw [hnb]; exact (h.choose_spec i hi c hcI b m hbref).symm
  have hcount_all := bcount_chain hchain hhead
    (by intro n' hn'; exact hb0 n' (by simpa only [Config.bcount] using hn')) hcmd_all
  -- the blocking invariant is now part of well-formedness (`hwf.2.2`)
  have hBI_all := blockInv_chain hchain hhead
    (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; exact hwf.2.2)
  -- conservation with recycles
  have hcons := barrierPotential_with_recycles (b := b) (nb := nb) hchain hhead hlast hno_err
    hcount_all hBI_all
  have hC₀pot : (Config.run s (I ^ k)).barrierPotential b
      = (s.B b).arrived + (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hC₀pot, hdonepot] at hcons
  -- both arrived counts are below the arrival count
  have hA0 : (s.B b).arrived < nb := by
    by_cases hcfg : (s.B b).count = none
    · have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, none⟩ := by rw [← hcfg]
      have harr0 := (hwf.2.1 b (s.B b).synced (s.B b).arrived heq).2
      rw [harr0]; simpa using hnbpos
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hb0 n' hn'
      have hle := (hwf.1 b (s.B b).synced (s.B b).arrived n' heq).1
      have hne2 : (s.B b).synced.length + (s.B b).arrived ≠ (n' : Nat) := by
        intro he; rw [heq] at hfull; simp [BarrierState.isFull, he] at hfull
      omega
  have hAd : (s_d.B b).arrived < nb := by
    obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s_d) := by
      rcases getLast_has_pred_mem hchain hlast with hh | hp
      · rw [hhead] at hh; exact absurd hh (by simp)
      · exact hp
    have hwf_y : y.WF := WF_chain hchain hhead hwf y hy_mem
    cases hy_step with
    | @done sd T' hdone hnofull =>
      by_cases hcfg : (s_d.B b).count = none
      · have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, none⟩ := by rw [← hcfg]
        have harr0 := (hwf_y.2.1 b (s_d.B b).synced (s_d.B b).arrived heq).2
        rw [harr0]; simpa using hnbpos
      · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
        have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, some n'⟩ := by rw [← hn']
        have hnn := (hcount_all (Config.done s_d) (List.mem_of_mem_getLast? hlast)) n'
          (by simp only [Config.bcount]; exact hn')
        have hlt2 := hnofull b (s_d.B b).synced (s_d.B b).arrived n' heq
        omega
  -- the recycle count is the exact quotient
  obtain ⟨q, hq⟩ := hdvd
  rw [hq] at hcons
  have hAeq : (s.B b).arrived = (s_d.B b).arrived := by
    have e : ((s.B b).arrived + nb * q) % nb
        = ((s_d.B b).arrived + nb * recycleCount b τ (τ.length - 1)) % nb := by rw [hcons]
    rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA0,
      Nat.mod_eq_of_lt hAd] at e
  have hqR : q = recycleCount b τ (τ.length - 1) := by
    have : nb * q = nb * recycleCount b τ (τ.length - 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left hnbpos this
  rw [← I.arrivers_pow b k, hq, Nat.mul_div_cancel_left _ hnbpos, hqR]

/-!
## Theorem 1 (§1): arrived counts are restored over a complete run

Companion to `pow_barriers_advance`. That theorem shows every loop barrier's
*generation* advances over the §1 unrolling; this one shows that, generation aside, the
run leaves every barrier with the same number of *arrived* threads it started with
(`State.ArrivedCountEquiv`). Only the arrived *count* is restored: a complete run drains
every syncer (none can be parked at `done`) and may leave a barrier freshly recycled, so
neither the synced count, the configured/unconfigured status, nor thread identities are
preserved.
-/

/-- For a **referenced** barrier `b` that is not full at entry, a complete `I ^ k` run
returns it to its entry arrived count. This is the conservation-and-divisibility core (the
same `hAeq` step proved inside `pow_barriers_advance_count`): the total arrivals
`k · arrivers(b)` are a multiple of `arrival-count(b)`, and both arrived counts are below
it, so they must be equal. -/
theorem arrivedLen_preserved {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {b : Barrier} (hwf : (Config.run s (I ^ I.loopK h)).WF)
    (hfull : (s.B b).isFull = false) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet)
    {s_d : State} (hlast : τ.getLast? = some (Config.done s_d)) :
    (s_d.B b).arrived = (s.B b).arrived := by
  have hb0 := Config.WellSynchronized.headCount_consistent_of_successful h hfull hτ hb
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, _⟩ := hτ
  set k := I.loopK h with hk
  set nb := I.arrivalCount h b with hnb
  have hbI : b ∈ I.barriers := by
    rw [CTA.barrierSet, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hbi'⟩ := hb
    rw [List.mem_toFinset, List.mem_filterMap] at hbi'
    obtain ⟨c, hc, hcb⟩ := hbi'
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc
    have hi' : i ∈ I.ids := by rw [← CTA.pow_ids I k]; exact hi
    obtain ⟨n, hbref⟩ : ∃ n, Cmd.barrierRef c = some (b, n) := by
      cases c with
      | read g => simp [Cmd.barrier?] at hcb
      | write g => simp [Cmd.barrier?] at hcb
      | arrive b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
      | sync b' n => simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi', List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  have hnbpos : 0 < nb := I.arrivalCount_pos h hbI
  have hdvd : nb ∣ (I ^ k).arrivers b := I.arrivalCount_dvd_pow_arrivers h hbI
  have hno_err : ∀ C ∈ τ, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : τ ≠ [] := by rintro rfl; simp at hhead
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at hlast
      rw [hlast, hCerr] at hCl; exact Config.noConfusion hCl
  have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c = some (b, m) →
      (m : Nat) = nb := by
    intro C hC i c hc m hbref
    have hc0 : c ∈ (Config.run s (I ^ k)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (I ^ k).prog i := by simpa [Config.progOf] using hc0
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc1
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    rw [hnb]; exact (h.choose_spec i hi c hcI b m hbref).symm
  have hcount_all := bcount_chain hchain hhead
    (by intro n' hn'; exact hb0 n' (by simpa only [Config.bcount] using hn')) hcmd_all
  have hBI_all := blockInv_chain hchain hhead
    (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; exact hwf.2.2)
  have hcons := barrierPotential_with_recycles (b := b) (nb := nb) hchain hhead hlast hno_err
    hcount_all hBI_all
  have hC₀pot : (Config.run s (I ^ k)).barrierPotential b
      = (s.B b).arrived + (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hC₀pot, hdonepot] at hcons
  have hA0 : (s.B b).arrived < nb := by
    by_cases hcfg : (s.B b).count = none
    · have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, none⟩ := by rw [← hcfg]
      have harr0 := (hwf.2.1 b (s.B b).synced (s.B b).arrived heq).2
      rw [harr0]; simpa using hnbpos
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hb0 n' hn'
      have hle := (hwf.1 b (s.B b).synced (s.B b).arrived n' heq).1
      have hne2 : (s.B b).synced.length + (s.B b).arrived ≠ (n' : Nat) := by
        intro he; rw [heq] at hfull; simp [BarrierState.isFull, he] at hfull
      omega
  have hAd : (s_d.B b).arrived < nb := by
    obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s_d) := by
      rcases getLast_has_pred_mem hchain hlast with hh | hp
      · rw [hhead] at hh; exact absurd hh (by simp)
      · exact hp
    have hwf_y : y.WF := WF_chain hchain hhead hwf y hy_mem
    cases hy_step with
    | @done sd T' hdone hnofull =>
      by_cases hcfg : (s_d.B b).count = none
      · have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, none⟩ := by rw [← hcfg]
        have harr0 := (hwf_y.2.1 b (s_d.B b).synced (s_d.B b).arrived heq).2
        rw [harr0]; simpa using hnbpos
      · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
        have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, some n'⟩ := by rw [← hn']
        have hnn := (hcount_all (Config.done s_d) (List.mem_of_mem_getLast? hlast)) n'
          (by simp only [Config.bcount]; exact hn')
        have hlt2 := hnofull b (s_d.B b).synced (s_d.B b).arrived n' heq
        omega
  obtain ⟨q, hq⟩ := hdvd
  rw [hq] at hcons
  have e : ((s.B b).arrived + nb * q) % nb
      = ((s_d.B b).arrived + nb * recycleCount b τ (τ.length - 1)) % nb := by rw [hcons]
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA0,
    Nat.mod_eq_of_lt hAd, eq_comm] at e

/-- A barrier that **no command references** and that is not full at entry has its state
frozen by every step: a registration happens only at the executed command's barrier
(which is `≠ b`, since no command mentions `b`), and a recycle of `b` would need `b` full
(contradicting `hfullβ`). The unreferenced-barrier analogue of `bstate_frozen_step`. -/
theorem bstate_unref_step {b : Barrier} {β : BarrierState} (hfullβ : β.isFull = false)
    {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s', C.state? = some s' → s'.B b = β)
    (hcmd : ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c ≠ some (b, m)) :
    ∀ s', C'.state? = some s' → s'.B b = β := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hth =>
    have hCb : s.B b = β := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hCb
    | write_noop => exact hCb
    | arrive_configure he hb0 =>
      rename_i b₀ n
      have hbb : b ≠ b₀ := fun heq => by
        subst heq
        exact hcmd i (Cmd.arrive b n)
          (by simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self) n rfl
      simp only [Function.update_of_ne hbb]; exact hCb
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      have hbb : b ≠ b₀ := fun heq => by
        subst heq
        exact hcmd i (Cmd.arrive b n)
          (by simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self) n rfl
      simp only [Function.update_of_ne hbb]; exact hCb
    | sync_configure he hb0 =>
      rename_i b₀ n c
      have hbb : b ≠ b₀ := fun heq => by
        subst heq
        exact hcmd i (Cmd.sync b n)
          (by simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self) n rfl
      simp only [Function.update_of_ne hbb]; exact hCb
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      have hbb : b ≠ b₀ := fun heq => by
        subst heq
        exact hcmd i (Cmd.sync b n)
          (by simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self) n rfl
      simp only [Function.update_of_ne hbb]; exact hCb
  | @recycle s T b₀ I₀ A₀ n₀ hb hfullr hpark =>
    have hCb : s.B b = β := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    have hbb : b ≠ b₀ := by
      intro heq; subst heq
      have hβeq : β = ⟨I₀, A₀, some n₀⟩ := hCb.symm.trans hb
      rw [hβeq] at hfullβ
      simp [BarrierState.isFull, hfullr] at hfullβ
    simp only [Function.update_of_ne hbb]; exact hCb
  | @done s T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
    exact hC s rfl
  | @error s T i P' hth => simp [Config.state?] at hs'

/-- Iterating `bstate_unref_step`: an unreferenced, not-full barrier stays frozen at every
configuration of a chain whose commands never mention it. -/
theorem bstate_unref_chain {b : Barrier} {β : BarrierState} (hfullβ : β.isFull = false) :
    ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ → τ.head? = some C₀ →
      (∀ s', C₀.state? = some s' → s'.B b = β) →
      (∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c ≠ some (b, m)) →
      ∀ C ∈ τ, ∀ s', C.state? = some s' → s'.B b = β := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ hcmd C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 := bstate_unref_step hfullβ hstep hC₀ (hcmd a (by simp))
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 (fun C hC'' => hcmd C (List.mem_cons_of_mem _ hC'')) C hC'

/-- **Theorem 1 (partial, arrived counts restored).** Let `k = I.loopK h` be the §1
iteration count. Over any successful trace `τ` of `I ^ k` from a well-formed state `s` in
which no barrier is full, every barrier ends the run (`Config.done s_d`) with the same
number of *arrived* threads it started with: `s_d.ArrivedCountEquiv s`. For a referenced
barrier this is the conservation/divisibility core (`arrivedLen_preserved`); an
unreferenced barrier is never touched, so its whole state is frozen.
NOTE (rohany): This is an important top-level theorem. -/
theorem Config.WellSynchronized.pow_barriers_restored {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State}
    (hwf : (Config.run s (I ^ I.loopK h)).WF)
    (hfull : ∀ b, (s.B b).isFull = false) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    {s_d : State} (hlast : τ.getLast? = some (Config.done s_d)) :
    s_d.ArrivedCountEquiv s := by
  intro b
  by_cases hb : b ∈ (I ^ I.loopK h).barrierSet
  · -- referenced barrier: conservation + divisibility pin the arrived count
    exact arrivedLen_preserved h hwf (hfull b) hτ hb hlast
  · -- unreferenced barrier: nothing ever touches `b`, so its state is frozen
    set k := I.loopK h with hk
    obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, _⟩ := hτ
    have hcmd : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+, Cmd.barrierRef c ≠ some (b, m) := by
      intro C hC i c hc m hbref
      apply hb
      have hc0 : c ∈ (Config.run s (I ^ k)).progOf i :=
        (progOf_suffix_head hchain hhead C hC i).subset hc
      have hc1 : c ∈ (I ^ k).prog i := by simpa [Config.progOf] using hc0
      have hbar : Cmd.barrier? c = some b := by
        cases c with
        | read g => simp [Cmd.barrierRef] at hbref
        | write g => simp [Cmd.barrierRef] at hbref
        | arrive b' n =>
          simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbref
          simp only [Cmd.barrier?, hbref.1]
        | sync b' n =>
          simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbref
          simp only [Cmd.barrier?, hbref.1]
      have hi : i ∈ (I ^ k).ids := by
        by_contra hni; rw [(I ^ k).nil_outside_ids i hni] at hc1; simp at hc1
      rw [CTA.barrierSet, Finset.mem_biUnion]
      exact ⟨i, hi, List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨c, hc1, hbar⟩)⟩
    have hfrozen := bstate_unref_chain (hfull b) hchain hhead
      (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; rfl)
      hcmd (Config.done s_d) (List.mem_of_mem_getLast? hlast) s_d rfl
    rw [hfrozen]

/-!
## Lemma 3 (§ "Structure of `G` across iteration batches"), two-batch case

The document's Lemma 3 (`lemma:structure-g-across-iterations`) states that, across
consecutive batches of the §1 unrolling `I ^ k`, the recovered generation mapping is
constant up to a per-barrier offset. Here we state the **simplest instance**: just two
batches, i.e. the program `I ^ k ⨾ I ^ k` (the document's `I₀^k ; I₁^k`, with `n = 0`).

The offset for a barrier `b` is the number of times one batch `I ^ k` recycles `b`,
which `Config.WellSynchronized.pow_barriers_advance_count` computes to be exactly
`k · arrivers(b) / arrival-count(b)` (here `k = I.loopK h`); this is the same count that
already appears in `pow_barriers_advance_count` / `arrivedLen_preserved`.
-/

/-- **Full state restoration from `State.initial`.** A successful run of `I ^ k`
(`k = I.loopK h`) starting from `State.initial` returns the *entire* state to
`State.initial`: the terminal `done s_d` has `s_d = State.initial`.

This is stronger than the general `pow_barriers_restored` (which restores only arrived
*counts*, `ArrivedCountEquiv`), and holds specifically because we start from `initial`.
At the terminal configuration every barrier's `arrived` count is zero (`pow_barriers_restored`),
its `synced` list is empty (`done` leaves no thread parked, so `WF`'s parked clause forces it),
and hence — by `WF`'s "configured ⟹ non-empty registration" conjunct — it is unconfigured;
and every thread is enabled (`EnabledInv`: a disabled thread would be parked at some syncer,
but there are none). It is the fact that lets the second batch of `I ^ k ⨾ I ^ k` *replay*
the first batch's schedule verbatim. -/
theorem pow_done_state_initial {I : CTA} (h : I.ConsistentArrivalCounts) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial (I ^ I.loopK h)) τ)
    {s_d : State} (hlast : τ.getLast? = some (Config.done s_d)) :
    s_d = State.initial := by
  have hchain : List.IsChain CTAStep τ := hτ.1.1.subtrace
  have hhead := hτ.1.2
  have hAC : s_d.ArrivedCountEquiv State.initial :=
    Config.WellSynchronized.pow_barriers_restored h WF_initial (fun _ => rfl) hτ hlast
  obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s_d) := by
    rcases getLast_has_pred_mem hchain hlast with hh | hp
    · rw [hhead] at hh; exact absurd hh (by simp)
    · exact hp
  have hwf_y : y.WF := WF_chain hchain hhead WF_initial y hy_mem
  have hEnab : ∀ s, y.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hhead
      (by intro s hs; simp only [Config.state?, Option.some.injEq] at hs; subst hs
          exact State.EnabledInv.initial) y hy_mem
  cases hy_step with
  | @done sd T hdone hnofull =>
    obtain ⟨hcfg, huncfg, _⟩ := hwf_y
    have hEnabled : s_d.EnabledInv := hEnab s_d rfl
    -- every barrier is unconfigured at the terminal state
    have hBunc : ∀ b, s_d.B b = BarrierState.unconfigured := by
      intro b
      obtain ⟨sy, ar, cnt, hbeq⟩ : ∃ sy ar cnt, s_d.B b = ⟨sy, ar, cnt⟩ := ⟨_, _, _, rfl⟩
      have har : ar = 0 := by
        have hl := hAC b
        rw [hbeq] at hl; simpa [State.initial, BarrierState.unconfigured] using hl
      have hsy : sy = [] := by
        cases cnt with
        | none => exact (huncfg b sy ar hbeq).1
        | some n =>
          obtain ⟨_, hpark, _⟩ := hcfg b sy ar n hbeq
          cases sy with
          | nil => rfl
          | cons i₀ rest =>
            exfalso
            have hh := hpark i₀ (by simp)
            have hTnil : T.prog i₀ = [] := by
              by_cases hmem : i₀ ∈ T.ids
              · exact hdone i₀ hmem
              · exact T.nil_outside_ids i₀ hmem
            rw [hTnil] at hh; simp at hh
      have hcnt : cnt = none := by
        cases cnt with
        | none => rfl
        | some n =>
          exfalso
          obtain ⟨_, _, hpos⟩ := hcfg b sy ar n hbeq
          rw [hsy, har] at hpos; simp at hpos
      subst har; subst hsy; subst hcnt; exact hbeq
    -- every thread is enabled at the terminal state
    have hE : ∀ i, s_d.E i = true := by
      intro i
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      obtain ⟨b, hb'⟩ := hEnabled i hcon
      rw [hBunc b] at hb'; simp [BarrierState.unconfigured] at hb'
    have hEeq : s_d.E = State.initial.E := funext hE
    have hBeq : s_d.B = State.initial.B := funext hBunc
    calc s_d = ⟨s_d.E, s_d.B⟩ := rfl
      _ = ⟨State.initial.E, State.initial.B⟩ := by rw [hEeq, hBeq]
      _ = State.initial := rfl

/-- **Full state restoration from a `done` start.** A successful run of `I ^ k` (`k = I.loopK h`)
from a state `s` that is *itself a valid done state* — every thread enabled (`hsE`), no thread
parked (`hsync`), well-formed (`hwf`), no barrier full (`hfull`) — returns the *entire* state to
`s`: the terminal `done s_d` has `s_d = s`.

This generalizes `pow_done_state_initial` (the `s = State.initial` case). Arrived counts are
restored by `pow_barriers_restored`; the `synced` lists empty and `E` returns to all-`true` at any
`done` configuration. The configured *count* is restored because a successful (error-free) run
forces every reference's count to agree with the entry count — `headCount_consistent_of_successful`
pins the entry count to `arrivalCount h b` and `bcount_chain` propagates it to `done`
(`sync_err_count`/`arrive_err_count` would otherwise fire). Unreferenced barriers are frozen. This
is what lets the loop body replay verbatim from a non-initial post-prefix state. -/
theorem pow_done_state_restored {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    (hwf : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false)
    (hsE : ∀ i, s.E i = true) (hsync : ∀ b, (s.B b).synced = [])
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    {s_d : State} (hlast : τ.getLast? = some (Config.done s_d)) :
    s_d = s := by
  have hchain : List.IsChain CTAStep τ := hτ.1.1.subtrace
  have hhead : τ.head? = some (Config.run s (I ^ I.loopK h)) := hτ.1.2
  have hAC : s_d.ArrivedCountEquiv s :=
    Config.WellSynchronized.pow_barriers_restored h hwf hfull hτ hlast
  obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s_d) := by
    rcases getLast_has_pred_mem hchain hlast with hh | hp
    · rw [hhead] at hh; exact absurd hh (by simp)
    · exact hp
  have hwf_y : y.WF := WF_chain hchain hhead hwf y hy_mem
  obtain ⟨hcfg_s, huncfg_s, -⟩ := hwf
  have hEnab : ∀ s', y.state? = some s' → s'.EnabledInv :=
    enabledInv_chain hchain hhead
      (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
          intro i hi; rw [hsE i] at hi; exact absurd hi (by simp)) y hy_mem
  cases hy_step with
  | @done sd T hdone hnofull =>
    obtain ⟨hcfg_d, huncfg_d, -⟩ := hwf_y
    have hEnabled : s_d.EnabledInv := hEnab s_d rfl
    -- synced lists are empty at the terminal `done`
    have hSync_d : ∀ b, (s_d.B b).synced = [] := by
      intro b
      obtain ⟨sy, ar, cnt, hbeq⟩ : ∃ sy ar cnt, s_d.B b = ⟨sy, ar, cnt⟩ := ⟨_, _, _, rfl⟩
      have hsy : sy = [] := by
        cases cnt with
        | none => exact (huncfg_d b sy ar hbeq).1
        | some n =>
          obtain ⟨_, hpark, _⟩ := hcfg_d b sy ar n hbeq
          cases sy with
          | nil => rfl
          | cons i₀ rest =>
            exfalso
            have hh := hpark i₀ (by simp)
            have hTnil : T.prog i₀ = [] := by
              by_cases hmem : i₀ ∈ T.ids
              · exact hdone i₀ hmem
              · exact T.nil_outside_ids i₀ hmem
            rw [hTnil] at hh; simp at hh
      rw [hbeq]; exact hsy
    -- all threads enabled at the terminal state
    have hE_d : ∀ i, s_d.E i = true := by
      intro i; by_contra hcon; rw [Bool.not_eq_true] at hcon
      obtain ⟨b, hb'⟩ := hEnabled i hcon
      rw [hSync_d b] at hb'; simp at hb'
    -- a `BarrierState` is determined by its three projections
    have hmkeq : ∀ {β₁ β₂ : BarrierState}, β₁.synced = β₂.synced → β₁.arrived = β₂.arrived →
        β₁.count = β₂.count → β₁ = β₂ := by
      intro β₁ β₂ h1 h2 h3; cases β₁; cases β₂; simp_all
    -- match the barrier maps
    have hBeq : s_d.B = s.B := by
      funext b
      have hsyd : (s_d.B b).synced = [] := hSync_d b
      have hsys : (s.B b).synced = [] := hsync b
      have hard : (s_d.B b).arrived = (s.B b).arrived := hAC b
      have hcnt : (s_d.B b).count = (s.B b).count := by
        by_cases hbref : b ∈ (I ^ I.loopK h).barrierSet
        · -- referenced: head-count consistency + propagation pin the count to `arrivalCount h b`
          set nb := I.arrivalCount h b with hnb
          have hhc : ∀ n', (s.B b).count = some n' → (n' : Nat) = nb :=
            Config.WellSynchronized.headCount_consistent_of_successful h (hfull b) hτ hbref
          have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+,
              Cmd.barrierRef c = some (b, m) → (m : Nat) = nb := by
            intro C hC i c hc m hbref'
            have hc0 : c ∈ (Config.run s (I ^ I.loopK h)).progOf i :=
              (progOf_suffix_head hchain hhead C hC i).subset hc
            have hc1 : c ∈ (I ^ I.loopK h).prog i := by simpa [Config.progOf] using hc0
            have hcI : c ∈ I.prog i := I.mem_pow_prog hc1
            have hi : i ∈ I.ids := by
              by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
            rw [hnb]; exact (h.choose_spec i hi c hcI b m hbref').symm
          have hdc : ∀ n', (s_d.B b).count = some n' → (n' : Nat) = nb := by
            have hch := bcount_chain hchain hhead (fun n' hn' => hhc n' hn') hcmd_all
              (Config.done s_d) (List.mem_of_mem_getLast? hlast)
            intro n' hn'; exact hch n' hn'
          cases hcd : (s_d.B b).count with
          | none =>
            cases hcs : (s.B b).count with
            | none => rfl
            | some ns =>
              exfalso
              have hbs' : s.B b = ⟨[], (s.B b).arrived, some ns⟩ := hmkeq hsys rfl hcs
              have hpos := (hcfg_s b [] (s.B b).arrived ns hbs').2.2
              have hbd' : s_d.B b = ⟨[], (s_d.B b).arrived, none⟩ := hmkeq hsyd rfl hcd
              have hard0 := (huncfg_d b [] (s_d.B b).arrived hbd').2
              simp only [List.length_nil, Nat.zero_add] at hpos
              rw [hard] at hard0; omega
          | some nd =>
            cases hcs : (s.B b).count with
            | none =>
              exfalso
              have hbd' : s_d.B b = ⟨[], (s_d.B b).arrived, some nd⟩ := hmkeq hsyd rfl hcd
              have hpos := (hcfg_d b [] (s_d.B b).arrived nd hbd').2.2
              have hbs' : s.B b = ⟨[], (s.B b).arrived, none⟩ := hmkeq hsys rfl hcs
              have hars0 := (huncfg_s b [] (s.B b).arrived hbs').2
              simp only [List.length_nil, Nat.zero_add] at hpos
              rw [← hard] at hars0; omega
            | some ns =>
              have h1 : (nd : Nat) = nb := hdc nd hcd
              have h2 : (ns : Nat) = nb := hhc ns hcs
              congr 1
              exact PNat.coe_injective (h1.trans h2.symm)
        · -- unreferenced: the whole barrier state is frozen
          have hcmd_noref : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ m : ℕ+,
              Cmd.barrierRef c ≠ some (b, m) := by
            intro C hC i c hc m hbref'
            apply hbref
            have hc0 : c ∈ (Config.run s (I ^ I.loopK h)).progOf i :=
              (progOf_suffix_head hchain hhead C hC i).subset hc
            have hc1 : c ∈ (I ^ I.loopK h).prog i := by simpa [Config.progOf] using hc0
            have hi : i ∈ (I ^ I.loopK h).ids := by
              by_contra hni; rw [(I ^ I.loopK h).nil_outside_ids i hni] at hc1; simp at hc1
            have hbar : Cmd.barrier? c = some b := by
              cases c with
              | read g => simp [Cmd.barrierRef] at hbref'
              | write g => simp [Cmd.barrierRef] at hbref'
              | arrive b' n =>
                simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbref'
                simp only [Cmd.barrier?, hbref'.1]
              | sync b' n =>
                simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbref'
                simp only [Cmd.barrier?, hbref'.1]
            rw [CTA.barrierSet, Finset.mem_biUnion]
            exact ⟨i, hi, List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨c, hc1, hbar⟩)⟩
          have hfrozen := bstate_unref_chain (hfull b) hchain hhead
            (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; rfl)
            hcmd_noref (Config.done s_d) (List.mem_of_mem_getLast? hlast) s_d rfl
          rw [hfrozen]
      exact hmkeq (hsyd.trans hsys.symm) hard hcnt
    have hEeq : s_d.E = s.E := funext fun i => by rw [hE_d i, hsE i]
    calc s_d = ⟨s_d.E, s_d.B⟩ := rfl
      _ = ⟨s.E, s.B⟩ := by rw [hEeq, hBeq]
      _ = s := rfl

/-- `Config.seqLift` preserves the state component: appending `B`'s programs to a
configuration changes only the programs, not the state `(E, B)`. -/
theorem Config.seqLift_state? (A B : CTA) (X : Config) :
    (Config.seqLift A B X).state? = X.state? := by
  cases X <;> rfl

/-- Lifting two configurations into `A ⨾ B` (`Config.seqLift`) does not change whether the
step between them recycles `b`: `stepRecyclesBarrier` reads only the state, which `seqLift`
preserves. This is why the lifted first batch recycles exactly as the standalone run does. -/
theorem stepRecyclesBarrier_seqLift (A B : CTA) (b : Barrier) (X Y : Config) :
    stepRecyclesBarrier b (Config.seqLift A B X) (Config.seqLift A B Y)
      = stepRecyclesBarrier b X Y := by
  unfold stepRecyclesBarrier
  rw [Config.seqLift_state?, Config.seqLift_state?]

/-- The recycle count is invariant under lifting a whole trace into `A ⨾ B`:
`recycleCount b (l.map (seqLift A B)) M = recycleCount b l M`. -/
theorem recycleCount_map_seqLift (A B : CTA) (b : Barrier) (l : List Config) (M : Nat) :
    recycleCount b (l.map (Config.seqLift A B)) M = recycleCount b l M := by
  unfold recycleCount
  apply List.countP_congr
  intro j _
  simp only [List.getElem?_map]
  rcases l[j]? with _ | C
  · rfl
  · rcases l[j+1]? with _ | C'
    · rfl
    · simp only [Option.map_some]
      rw [stepRecyclesBarrier_seqLift]

/-- `recycleCount b · M` depends only on the first `M+1` configurations of a trace: two
traces agreeing on indices `0..M` have the same recycle count up to step `M`. -/
theorem recycleCount_eq_of_getElem?_eq (b : Barrier) {τ₁ τ₂ : List Config} {M : Nat}
    (h : ∀ j ≤ M, τ₁[j]? = τ₂[j]?) : recycleCount b τ₁ M = recycleCount b τ₂ M := by
  unfold recycleCount
  apply List.countP_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [h j (by omega), h (j + 1) (by omega)]

/-- Recycle count of a trace that has `σ` as a suffix starting at index `p` splits as the
count over the first `p` steps plus the count over `σ`: if `τ[p + r]? = σ[r]?` for all `r`,
then `recycleCount b τ (p + K) = recycleCount b τ p + recycleCount b σ K`. -/
theorem recycleCount_suffix (b : Barrier) {τ σ : List Config} {p K : Nat}
    (h : ∀ r, τ[p + r]? = σ[r]?) :
    recycleCount b τ (p + K) = recycleCount b τ p + recycleCount b σ K := by
  unfold recycleCount
  rw [List.range_add, List.countP_append, List.countP_map]
  congr 1
  apply List.countP_congr
  intro r _
  simp only [Function.comp_apply]
  rw [h r, show p + r + 1 = p + (r + 1) from by omega, h (r + 1)]

/-- A `run → run` step preserves the CTA's thread set: `interleave` updates one program
(`CTA.set`) and `recycle` advances parked threads (`CTA.wake`), both keeping `ids`. -/
theorem CTAStep.run_ids_eq {s s' : State} {T T' : CTA}
    (hstep : CTAStep (Config.run s T) (Config.run s' T')) : T'.ids = T.ids := by
  cases hstep with
  | interleave hi hbar hth => rfl
  | recycle hb hfull hpark => rfl

/-- The thread set is invariant along a chain: every `run` configuration of a trace whose
head is `run _ A` carries a CTA with `ids = A.ids`. -/
theorem run_ids_chain {A : CTA} : ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ →
    τ.head? = some C₀ → (∀ s T, C₀ = Config.run s T → T.ids = A.ids) →
    ∀ C ∈ τ, ∀ s T, C = Config.run s T → T.ids = A.ids := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ s T, b₁ = Config.run s T → T.ids = A.ids := by
        intro s' T' hb1eq
        obtain ⟨sa, Ta, haeq⟩ := hstep.source_run
        have hTa : Ta.ids = A.ids := hC₀ sa Ta haeq
        rw [haeq, hb1eq] at hstep
        rw [hstep.run_ids_eq, hTa]
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 C hC'

/-- The configuration just before a restoring `A`-trace's terminal `done sd`, lifted into
`A ⨾ B` (`A.ids = B.ids`), is `run sd B` — the "`A` done, `B` poised" boundary configuration.
(The penultimate config has all programs empty by `progOf_penultimate_done`, and thread set
`A.ids` by `run_ids_chain`, so appending `B` recovers exactly `B`.) The `B = A` case is the
replay boundary used by `replay_trace`; the general case backs `glue_trace`. -/
theorem seqLift_penultimate_gen {A B : CTA} (hids : A.ids = B.ids) {s₀ : State} {t : List Config}
    (hchain : List.IsChain CTAStep t) (hhead : t.head? = some (Config.run s₀ A))
    {sd : State} (hlast : t.getLast? = some (Config.done sd)) (hdrop : t.dropLast ≠ []) :
    Config.seqLift A B (t.dropLast.getLast hdrop) = Config.run sd B := by
  have hne : t ≠ [] := fun h => by rw [h] at hlast; simp at hlast
  have hgl : t.getLast hne = Config.done sd := by
    have h := List.getLast?_eq_some_getLast hne; rw [hlast, Option.some.injEq] at h; exact h.symm
  have e1 : t.dropLast ++ [Config.done sd] = t := by
    have h := List.dropLast_concat_getLast hne; rwa [hgl] at h
  have e2 : t.dropLast.dropLast ++ [t.dropLast.getLast hdrop] = t.dropLast :=
    List.dropLast_concat_getLast hdrop
  have hdecomp : t.dropLast.dropLast ++ (t.dropLast.getLast hdrop) :: Config.done sd :: [] = t := by
    rw [show (t.dropLast.getLast hdrop) :: Config.done sd :: []
          = [t.dropLast.getLast hdrop] ++ [Config.done sd] from rfl, ← List.append_assoc, e2, e1]
  have hstep : CTAStep (t.dropLast.getLast hdrop) (Config.done sd) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain hdecomp.symm
  have hXmem : (t.dropLast.getLast hdrop) ∈ t :=
    List.dropLast_subset _ (List.getLast_mem hdrop)
  obtain ⟨sX, T, hXeq⟩ := hstep.source_run
  have hTids : T.ids = A.ids :=
    run_ids_chain hchain hhead
      (by intro s T' he; rw [Config.run.injEq] at he; rw [← he.2])
      (t.dropLast.getLast hdrop) hXmem sX T hXeq
  rw [hXeq] at hstep ⊢
  cases hstep with
  | done hdone _ =>
    have hTprog : ∀ i, T.prog i = [] := by
      intro i; by_cases hi : i ∈ T.ids
      · exact hdone i hi
      · exact T.nil_outside_ids i hi
    have hBeq : T.appendTail B = B := by
      apply CTA.ext
      · change T.ids ∪ B.ids = B.ids; rw [hTids, hids, Finset.union_self]
      · funext i; change T.prog i ++ B.prog i = B.prog i; rw [hTprog i, List.nil_append]
    change Config.run sd (T.appendTail B) = Config.run sd B
    rw [hBeq]

/-- **Done-state properties.** The terminal `done s` of any successful trace (from `initial`) is a
*valid done state*: every thread enabled, no thread parked (`synced = []`), no barrier full, and —
since the parked clause of `WF` is then vacuous — `run s T` is well-formed for **any** `T`. These
are exactly the hypotheses `pow_done_state_restored` / `pow_replay_recycle_structure` need to
replay the loop body from `s`. -/
theorem done_state_of_successfulTrace {T₀ : CTA} {s : State} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T₀) τ)
    (hlast : τ.getLast? = some (Config.done s)) :
    (∀ i, s.E i = true) ∧ (∀ b, (s.B b).synced = []) ∧ (∀ b, (s.B b).isFull = false) ∧
      ∀ (T : CTA), (Config.run s T).WF := by
  have hchain : List.IsChain CTAStep τ := hτ.1.1.subtrace
  have hhead : τ.head? = some (Config.run State.initial T₀) := hτ.1.2
  obtain ⟨y, hy_mem, hy_step⟩ : ∃ y ∈ τ, CTAStep y (Config.done s) := by
    rcases getLast_has_pred_mem hchain hlast with hh | hp
    · rw [hhead] at hh; exact absurd hh (by simp)
    · exact hp
  have hwf_y : y.WF := WF_chain hchain hhead WF_initial y hy_mem
  have hEnab : ∀ s', y.state? = some s' → s'.EnabledInv :=
    enabledInv_chain hchain hhead
      (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
          exact State.EnabledInv.initial) y hy_mem
  cases hy_step with
  | @done sd T hdone hnofull =>
    obtain ⟨hcfg_d, huncfg_d, hBI_d⟩ := hwf_y
    have hEnabled : s.EnabledInv := hEnab s rfl
    have hSync : ∀ b, (s.B b).synced = [] := by
      intro b
      obtain ⟨sy, ar, cnt, hbeq⟩ : ∃ sy ar cnt, s.B b = ⟨sy, ar, cnt⟩ := ⟨_, _, _, rfl⟩
      have hsy : sy = [] := by
        cases cnt with
        | none => exact (huncfg_d b sy ar hbeq).1
        | some n =>
          obtain ⟨_, hpark, _⟩ := hcfg_d b sy ar n hbeq
          cases sy with
          | nil => rfl
          | cons i₀ rest =>
            exfalso
            have hh := hpark i₀ (by simp)
            have hTnil : T.prog i₀ = [] := by
              by_cases hmem : i₀ ∈ T.ids
              · exact hdone i₀ hmem
              · exact T.nil_outside_ids i₀ hmem
            rw [hTnil] at hh; simp at hh
      rw [hbeq]; exact hsy
    have hE : ∀ i, s.E i = true := by
      intro i; by_contra hcon; rw [Bool.not_eq_true] at hcon
      obtain ⟨b, hb'⟩ := hEnabled i hcon
      rw [hSync b] at hb'; simp at hb'
    have hfull : ∀ b, (s.B b).isFull = false := by
      intro b
      cases hc : (s.B b).count with
      | none => simp [BarrierState.isFull, hc]
      | some n =>
        have hbeq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n⟩ := by rw [← hc]
        have hlt := hnofull b (s.B b).synced (s.B b).arrived n hbeq
        rw [hSync b, List.length_nil, Nat.zero_add] at hlt
        simp only [BarrierState.isFull, hc, hSync b, List.length_nil, Nat.zero_add]
        exact beq_false_of_ne (Nat.ne_of_lt hlt)
    refine ⟨hE, hSync, hfull, fun T' => ?_⟩
    refine ⟨fun b I A n hbq => ?_, huncfg_d, hBI_d⟩
    obtain ⟨hle, -, hpos⟩ := hcfg_d b I A n hbq
    refine ⟨hle, fun i hi => ?_, hpos⟩
    have : I = [] := by have := hSync b; rw [hbq] at this; exact this
    rw [this] at hi; simp at hi

/-- **Angelic tail.** The "completion" half of `seq_angelic_prefix`, isolated. From `WS(A ⨾ B)`
and a successful `A`-trace ending in `done s_d`, the strong-normalization completion of `B` from
the boundary `run s_d B` is itself a *successful* `B`-trace from `run s_d B` — `WS(A ⨾ B)` forces
the spliced trace (hence its suffix, the completion) to terminate in `done`. This extracts a clean
`B`-from-`s_d` trace *without* assuming `WS(B)`: the prefix-loop construction uses it to obtain the
loop body's batch trace from the post-prefix done-state, where `WS(I^k)` is unavailable but
`WS(Pre ⨾ I^k)` is. -/
theorem CTA.WellSynchronized.seq_angelic_tail {A B : CTA} (hids : A.ids = B.ids)
    (hAB : (A.seq B hids).WellSynchronized) {t : List Config}
    (ht : IsSuccessfulTraceFrom (Config.run State.initial A) t)
    {s_d : State} (hAlast : t.getLast? = some (Config.done s_d)) :
    ∃ cont, IsSuccessfulTraceFrom (Config.run s_d B) cont := by
  obtain ⟨⟨htIC, hthead⟩, -⟩ := ht
  have hchain : List.IsChain CTAStep t := htIC.subtrace
  obtain ⟨c1, trest, rfl⟩ :
      ∃ c1 trest, t = Config.run State.initial A :: c1 :: trest := by
    rcases t with _ | ⟨c, _ | ⟨c1, tr⟩⟩
    · simp at hthead
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      simp only [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hthead] at hAlast; simp at hAlast
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      subst hthead; exact ⟨c1, tr, rfl⟩
  have ht' : IsSuccessfulTraceFrom (Config.run State.initial A)
      (Config.run State.initial A :: c1 :: trest) := ⟨⟨htIC, hthead⟩, s_d, hAlast⟩
  have hdrop : (Config.run State.initial A :: c1 :: trest).dropLast ≠ [] := by simp
  have hCstar : Config.seqLift A B
      ((Config.run State.initial A :: c1 :: trest).dropLast.getLast hdrop) = Config.run s_d B :=
    seqLift_penultimate_gen hids hchain hthead hAlast hdrop
  set P := (Config.run State.initial A :: c1 :: trest).dropLast.map (Config.seqLift A B) with hPdef
  have hPchain : List.IsChain CTAStep P :=
    isChain_seqLift A B (mem_dropLast_isRun htIC.subtrace) htIC.subtrace.dropLast
  have hPhead : P.head? = some (Config.run State.initial (A.seq B hids)) := by
    rw [hPdef, List.dropLast_cons_cons, List.map_cons, List.head?_cons,
      Config.seqLift, CTA.appendTail_eq_seq hids]
  have hPlast : P.getLast? = some (Config.run s_d B) := by
    rw [hPdef, List.getLast?_map, List.getLast?_eq_some_getLast hdrop, Option.map_some, hCstar]
  -- strong normalization supplies a completion from the boundary `C⋆ = run s_d B`
  have hbw : (Config.run s_d B).barriersWithin (A.seq B hids).barrierSet :=
    barriersWithin_chain _ hPchain hPhead barriersWithin_initial _ (List.mem_of_getLast? hPlast)
  obtain ⟨cont, hcont⟩ := exists_completeTrace (A.seq B hids).barrierSet _ hbw
  have hconthead : cont.head? = some (Config.run s_d B) := hcont.2
  have hcontne : cont ≠ [] := by intro hc; rw [hc] at hconthead; simp at hconthead
  -- splice; `WS(A ⨾ B)` makes the whole successful, so its suffix `cont` ends in `done`
  have hcont' : IsCompleteTraceFrom (Config.seqLift A B
      ((Config.run State.initial A :: c1 :: trest).dropLast.getLast hdrop)) cont := by
    rw [hCstar]; exact hcont
  obtain ⟨hICF, hsplit⟩ := seq_splice hids ht' hdrop hcont'
  obtain ⟨sf, hflast⟩ := completeTrace_ends_done hAB hICF
  refine ⟨cont, hcont, sf, ?_⟩
  rw [hsplit] at hflast
  obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hcontne
  rw [hxs, List.getLast?_append_cons] at hflast
  rw [hxs]; exact hflast

/-- **The replay trace.** Given a successful `A`-trace `t₁` from `State.initial` that ends in
`done State.initial` (full restoration), the list `(t₁.dropLast.map (seqLift A A)) ++ t₁.tail`
is a successful trace of `A ⨾ A`: it lifts `t₁`'s execution as the first batch, and — since
the boundary configuration is `run State.initial A` again (`seqLift_penultimate_gen`) — replays
`t₁` verbatim as the second batch. It is the `B = A` instance of `glue_trace`, packaged via
`seq_splice`. -/
theorem replay_trace (A : CTA) {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run State.initial A) t₁)
    (hlast : t₁.getLast? = some (Config.done State.initial)) :
    IsSuccessfulTraceFrom (Config.run State.initial (A.seq A rfl))
      (t₁.dropLast.map (Config.seqLift A A) ++ t₁.tail) := by
  have hchain : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead : t₁.head? = some (Config.run State.initial A) := ht₁.1.2
  obtain ⟨c1, trest, hteq⟩ : ∃ c1 trest, t₁ = Config.run State.initial A :: c1 :: trest := by
    rcases t₁ with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hhead
    · rw [List.head?_cons, Option.some.injEq] at hhead
      rw [List.getLast?_singleton, Option.some.injEq] at hlast
      rw [hhead] at hlast; exact absurd hlast (by simp)
    · rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead; exact ⟨b, l, rfl⟩
  have hdrop : t₁.dropLast ≠ [] := by rw [hteq]; simp
  -- the boundary `seqLift A A (penult t₁) = run init A` (restoration), so `t₁` itself replays
  -- as the second batch; `seq_splice` glues it on
  have hCstar : Config.seqLift A A (t₁.dropLast.getLast hdrop) = Config.run State.initial A :=
    seqLift_penultimate_gen rfl hchain hhead hlast hdrop
  have hcont : IsCompleteTraceFrom (Config.seqLift A A (t₁.dropLast.getLast hdrop)) t₁ := by
    rw [hCstar]; exact ht₁.1
  obtain ⟨hICF, -⟩ := seq_splice rfl ht₁ hdrop hcont
  have htailglast : t₁.tail.getLast? = some (Config.done State.initial) := by
    have htaileq : t₁.tail = c1 :: trest := by rw [hteq]; rfl
    rw [htaileq]; rw [hteq, List.getLast?_cons_cons] at hlast; exact hlast
  exact ⟨hICF, State.initial, List.mem_getLast?_append_of_mem_getLast? htailglast⟩

/-- A step into a `done` configuration never recycles: the `done` rule keeps the state
fixed, so `b` cannot be both full (source) and unconfigured (target). -/
theorem stepRecyclesBarrier_to_done (b : Barrier) (C : Config) (s : State)
    (hstep : CTAStep C (Config.done s)) : stepRecyclesBarrier b C (Config.done s) = false := by
  obtain ⟨sC, T, hCeq⟩ := hstep.source_run
  rw [hCeq] at hstep ⊢
  cases hstep with
  | done hdone _ =>
    simp only [stepRecyclesBarrier, Config.state?]
    by_cases hf : (s.B b).isFull = true
    · rw [hf, Bool.true_and, decide_eq_false]
      exact BarrierState.isFull_ne_unconfigured hf
    · rw [Bool.not_eq_true] at hf; rw [hf, Bool.false_and]

/-- The last step of a successful trace (into `done`) does not recycle, so the recycle count
over the whole trace equals the count over its `dropLast` steps. -/
theorem recycleCount_done_last {τ : List Config} {sd : State} {b : Barrier}
    (hchain : List.IsChain CTAStep τ) (hlast : τ.getLast? = some (Config.done sd))
    (h2 : 2 ≤ τ.length) :
    recycleCount b τ (τ.length - 1) = recycleCount b τ (τ.length - 2) := by
  obtain ⟨X, hX⟩ : ∃ X, τ[τ.length - 2]? = some X :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hdone : τ[τ.length - 2 + 1]? = some (Config.done sd) := by
    rw [show τ.length - 2 + 1 = τ.length - 1 by omega, ← List.getLast?_eq_getElem?]; exact hlast
  have hstep : CTAStep X (Config.done sd) := chain_step hchain hX hdone
  have hnr := stepRecyclesBarrier_to_done b X sd hstep
  -- the step from index `τ.length - 2` does not recycle, so the recycle count is unchanged
  -- across it (inlined, to keep this file independent of `CheckWellSynchronized`)
  have hstepeq : recycleCount b τ (τ.length - 2 + 1) = recycleCount b τ (τ.length - 2) := by
    unfold recycleCount
    rw [List.range_succ, List.countP_append]
    simp [hX, hdone, hnr]
  rwa [show τ.length - 2 + 1 = τ.length - 1 by omega] at hstepeq

/-- A barrier-registering command's `barrier?` agrees with the barrier of its
`barrierRef`: both single out the same `b` for `arrive`/`sync`. -/
theorem Cmd.barrier?_of_barrierRef {c : Cmd} {b : Barrier} {n : ℕ+}
    (hbr : Cmd.barrierRef c = some (b, n)) : Cmd.barrier? c = some b := by
  cases c with
  | read g => simp [Cmd.barrierRef] at hbr
  | write g => simp [Cmd.barrierRef] at hbr
  | arrive b' n' =>
    simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
    obtain ⟨rfl, -⟩ := hbr; rfl
  | sync b' n' =>
    simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
    obtain ⟨rfl, -⟩ := hbr; rfl

/-- **The recycle-count core of Lemma 3 (two-batch case).** *Stated, not yet proved.*
This isolates the one genuinely hard fact behind `second_batch_gen_offset`: there is a
successful trace `τ` of `I ^ k ⨾ I ^ k` along which, for every barrier instruction, `b`
has been recycled exactly `k · arrivers(b) / arrival-count(b)` *more* times just before
the **second** batch's copy executes than just before the **first** batch's copy. Since a
barrier instruction's generation is `(recycles of its barrier before it executes) + 1`
(Definition 5, `pointGen`), this offset is precisely the generation offset claimed by
Lemma 3; `second_batch_gen_offset` is the routine `pointGen`-to-`recycleCount` repackaging
of this statement (it converts each generation into a recycle count via the instruction's
execution time and then applies this lemma).

Proving it is the substance of the paper's Lemma 3: it needs a trace that runs the first
`I ^ k` to completion and then *replays the same schedule* on the second `I ^ k`, so the
recycle counts line up. All the conceptual prerequisites are now in place:

* `pow_done_state_initial` — the batch-boundary state is *exactly* `State.initial` (full
  restoration from `initial`, established via the new `WF` non-emptiness conjunct and the
  `EnabledInv` invariant), so the second batch can replay the first batch's trace verbatim;
* `recycleCount_map_seqLift` / `stepRecyclesBarrier_seqLift` — the lifted first batch
  recycles exactly as the standalone `I ^ k` run does;
* `recycleCount_eq_of_getElem?_eq` — recycle counts depend only on a trace prefix;
* `Config.WellSynchronized.pow_barriers_advance_count` — one batch recycles `b` exactly
  `k · arrivers(b) / arrival-count(b)` times.

What remains is the mechanical assembly: glue `(t₁.dropLast).map (seqLift A A) ++ t₁.tail`
into a successful trace of `A ⨾ A` (`A := I ^ k`), locate the two instruction times in the
two batches via the progOf-length invariants (as in `seq_no_happensBefore_B_to_A`), and add
up the recycle counts with the lemmas above. -/
theorem replay_recycle_offset {I : CTA} (h : I.ConsistentArrivalCounts)
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run State.initial (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done State.initial))
    (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (n : ℕ+) (m₁ m₂ : Nat)
    (hcj : ((I ^ I.loopK h).prog t)[j]? = some c) (hbr : Cmd.barrierRef c = some (b, n))
    (ht1 : IsTimeOf (Config.run State.initial ((I ^ I.loopK h).seq (I ^ I.loopK h) rfl))
        (t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) (I ^ I.loopK h)) ++ t₁.tail) ⟨t, j⟩ m₁)
    (ht2 : IsTimeOf (Config.run State.initial ((I ^ I.loopK h).seq (I ^ I.loopK h) rfl))
        (t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) (I ^ I.loopK h)) ++ t₁.tail)
        ⟨t, ((I ^ I.loopK h).prog t).length + j⟩ m₂) :
    recycleCount b (t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) (I ^ I.loopK h)) ++ t₁.tail)
        (m₂ - 1)
      = recycleCount b (t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) (I ^ I.loopK h)) ++ t₁.tail)
          (m₁ - 1)
        + I.loopK h * I.arrivers b / I.arrivalCount h b := by
  set A := I ^ I.loopK h with hA
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead1 : t₁.head? = some (Config.run State.initial A) := ht₁.1.2
  obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
  -- t₁ has length ≥ 2 (starts `run`, ends `done`), so its `dropLast` is nonempty
  have hne : t₁ ≠ [] := fun hd => by rw [hd] at hhead1; simp at hhead1
  obtain ⟨a, l, htl⟩ := List.exists_cons_of_ne_nil hne
  have hlne : l ≠ [] := by
    rintro rfl
    rw [htl] at hhead1 ht₁L
    simp only [List.head?_cons, Option.some.injEq] at hhead1
    simp only [List.getLast?_singleton, Option.some.injEq] at ht₁L
    rw [hhead1] at ht₁L; exact absurd ht₁L (by simp)
  have h2 : 2 ≤ t₁.length := by
    rw [htl, List.length_cons]; have := List.length_pos_of_ne_nil hlne; omega
  have hdrop : t₁.dropLast ≠ [] := by
    intro hd; have : t₁.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
    omega
  -- the trace has length ≥ 3 (its penultimate config is all-empty, but `A.prog t ≠ []`)
  have hpenult : (t₁.dropLast.getLast hdrop).progOf t = [] :=
    progOf_penultimate_done hchain1 ht₁L (List.getLast?_eq_some_getLast hdrop) t
  have hN3 : 3 ≤ t₁.length := by
    rcases Nat.lt_or_ge t₁.length 3 with hlt | hge
    · exfalso
      have hlen2 : t₁.length = 2 := by omega
      have e1 : t₁.dropLast.getLast? = t₁.head? := by
        rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?, List.length_dropLast,
          List.getElem?_dropLast, if_pos (by omega)]
        congr 1; omega
      rw [List.getLast?_eq_some_getLast hdrop, hhead1] at e1
      have hpen0 : t₁.dropLast.getLast hdrop = Config.run State.initial A :=
        (Option.some.injEq _ _).mp e1
      rw [hpen0, show (Config.run State.initial A).progOf t = A.prog t from rfl] at hpenult
      rw [hpenult] at hjL; exact absurd hjL (by simp)
    · exact hge
  -- start-config program splits in two; boundary config is `run init A`
  have hC0 : (Config.run State.initial (A.seq A rfl)).progOf t = A.prog t ++ A.prog t := rfl
  have hCstar : Config.seqLift A A (t₁.dropLast.getLast hdrop) = Config.run State.initial A :=
    seqLift_penultimate_gen rfl hchain1 hhead1 ht₁L hdrop
  -- lengths and list structure of the replay trace `τ = P_lift ++ t₁.tail = Q ++ t₁`
  have hPLlen : (t₁.dropLast.map (Config.seqLift A A)).length = t₁.length - 1 := by
    rw [List.length_map, List.length_dropLast]
  have hPLne : (t₁.dropLast.map (Config.seqLift A A)) ≠ [] := by
    rw [Ne, List.map_eq_nil_iff]; exact hdrop
  have ht₁cons : Config.run State.initial A :: t₁.tail = t₁ := by
    rw [htl] at hhead1 ⊢
    simp only [List.head?_cons, Option.some.injEq] at hhead1
    rw [List.tail_cons, hhead1]
  have hPLgl : (t₁.dropLast.map (Config.seqLift A A)).getLast hPLne
      = Config.run State.initial A := by
    have hg : (t₁.dropLast.map (Config.seqLift A A)).getLast?
        = some (Config.run State.initial A) := by
      rw [List.getLast?_map, List.getLast?_eq_some_getLast hdrop, Option.map_some, hCstar]
    have hh := List.getLast?_eq_some_getLast hPLne; rw [hg] at hh
    exact (Option.some.injEq _ _).mp hh.symm
  have htlist : (t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail
      = (t₁.dropLast.map (Config.seqLift A A)).dropLast ++ t₁ := by
    conv_lhs => rw [← List.dropLast_concat_getLast hPLne]
    rw [hPLgl, List.append_assoc, List.singleton_append, ht₁cons]
  have hQlen : ((t₁.dropLast.map (Config.seqLift A A)).dropLast).length = t₁.length - 2 := by
    rw [List.length_dropLast, hPLlen]; omega
  -- suffix: the second batch of `τ` is exactly `t₁`
  have hsnd : ∀ r, ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail)[(t₁.length - 2) + r]?
      = t₁[r]? := by
    intro r
    rw [htlist, List.getElem?_append_right (by rw [hQlen]; omega), hQlen]
    congr 1; omega
  -- first batch agrees with the lifted `t₁`
  have hdropget : ∀ q, q < t₁.length - 1 → t₁.dropLast[q]? = t₁[q]? :=
    fun q hq => by rw [List.getElem?_dropLast, if_pos hq]
  have hfst : ∀ q, q ≤ t₁.length - 2 →
      ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail)[q]?
        = (t₁.map (Config.seqLift A A))[q]? := by
    intro q hq
    rw [List.getElem?_append_left (by rw [hPLlen]; omega), List.getElem?_map, List.getElem?_map,
      hdropget q (by omega)]
  -- `b` is referenced by `A`, so the per-batch recycle count is `Δ`
  have hb : b ∈ A.barrierSet := by
    rw [CTA.barrierSet, Finset.mem_biUnion]
    exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
      (List.mem_filterMap.mpr ⟨c, List.mem_of_getElem? hcj, Cmd.barrier?_of_barrierRef hbr⟩)⟩
  -- extract execution data (rephrased with `t`/`j` in place of the `ProgPoint` projections)
  obtain ⟨-, -, j₀, C, C', hm₁eq, hCj, hCj1, hCeq0, hC'eq0⟩ := ht1
  obtain ⟨-, -, j₂, D, D', hm₂eq, hDj, hDj1, hDeq0, hD'eq0⟩ := ht2
  have hCeq : C.progOf t = (A.prog t ++ A.prog t).drop j := hCeq0
  have hC'eq : C'.progOf t = (A.prog t ++ A.prog t).drop (j + 1) := hC'eq0
  have hDeq : D.progOf t = (A.prog t ++ A.prog t).drop ((A.prog t).length + j) := hDeq0
  have hD'eq : D'.progOf t = (A.prog t ++ A.prog t).drop ((A.prog t).length + j + 1) := hD'eq0
  -- locate η₁ in the first batch: `j₀ ≤ N - 3`
  have hj₀ : j₀ ≤ t₁.length - 3 := by
    by_contra hcon
    push Not at hcon
    have hCt : t₁[j₀ - (t₁.length - 2)]? = some C := by
      have := hsnd (j₀ - (t₁.length - 2))
      rw [show (t₁.length - 2) + (j₀ - (t₁.length - 2)) = j₀ by omega, hCj] at this
      exact this.symm
    have hle : (C.progOf t).length ≤ (A.prog t).length :=
      suffix_length_le (progOf_suffix_head hchain1 hhead1 C (List.mem_of_getElem? hCt) t)
    rw [hCeq, List.length_drop, List.length_append] at hle
    omega
  -- η₁ executes in `t₁` at `j₀ + 1`
  have hfj₀ := hfst j₀ (by omega)
  rw [hCj, List.getElem?_map] at hfj₀
  obtain ⟨Ct, hCtj, hCteq⟩ := Option.map_eq_some_iff.mp hfj₀.symm
  have hfj₀1 := hfst (j₀ + 1) (by omega)
  rw [hCj1, List.getElem?_map] at hfj₀1
  obtain ⟨Ct', hCtj1, hCt'eq⟩ := Option.map_eq_some_iff.mp hfj₀1.symm
  have hCtprog : Ct.progOf t = (A.prog t).drop j := by
    have e : C.progOf t = Ct.progOf t ++ A.prog t := by rw [← hCteq, Config.seqLift_progOf]
    rw [hCeq, List.drop_append_of_le_length (by omega)] at e
    exact (List.append_cancel_right e).symm
  have hCt'prog : Ct'.progOf t = (A.prog t).drop (j + 1) := by
    have e : C'.progOf t = Ct'.progOf t ++ A.prog t := by rw [← hCt'eq, Config.seqLift_progOf]
    rw [hC'eq, List.drop_append_of_le_length (by omega)] at e
    exact (List.append_cancel_right e).symm
  have hT1 : IsTimeOf (Config.run State.initial A) t₁ ⟨t, j⟩ (j₀ + 1) :=
    ⟨ht₁.1, hjL, j₀, Ct, Ct', rfl, hCtj, hCtj1, hCtprog, hCt'prog⟩
  -- locate η₂ in the second batch: `N - 2 ≤ j₂`
  have hj₂ : t₁.length - 2 ≤ j₂ := by
    by_contra hcon
    push Not at hcon
    have hfd := hfst (j₂ + 1) (by omega)
    rw [hDj1, List.getElem?_map] at hfd
    obtain ⟨Dt', _, hDt'eq⟩ := Option.map_eq_some_iff.mp hfd.symm
    have hge : (A.prog t).length ≤ (D'.progOf t).length := by
      rw [← hDt'eq, Config.seqLift_progOf, List.length_append]; omega
    have hlt : (D'.progOf t).length < (A.prog t).length := by
      rw [hD'eq, List.length_drop, List.length_append]; omega
    omega
  -- η₂'s instruction is the same `⟨t,j⟩`, executing in `t₁` at `j₂ - (N-2) + 1`
  have hDt : t₁[j₂ - (t₁.length - 2)]? = some D := by
    have := hsnd (j₂ - (t₁.length - 2))
    rw [show (t₁.length - 2) + (j₂ - (t₁.length - 2)) = j₂ by omega, hDj] at this
    exact this.symm
  have hDt1 : t₁[(j₂ - (t₁.length - 2)) + 1]? = some D' := by
    have := hsnd ((j₂ - (t₁.length - 2)) + 1)
    rw [show (t₁.length - 2) + ((j₂ - (t₁.length - 2)) + 1) = j₂ + 1 by omega, hDj1] at this
    exact this.symm
  have hDprog : D.progOf t = (A.prog t).drop j := by
    rw [hDeq, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1; omega
  have hD'prog : D'.progOf t = (A.prog t).drop (j + 1) := by
    rw [hD'eq, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 1; omega
  have hT2 : IsTimeOf (Config.run State.initial A) t₁ ⟨t, j⟩ ((j₂ - (t₁.length - 2)) + 1) :=
    ⟨ht₁.1, hjL, j₂ - (t₁.length - 2), D, D', rfl, hDt, hDt1, hDprog, hD'prog⟩
  have huniq : j₀ + 1 = (j₂ - (t₁.length - 2)) + 1 := IsTimeOf.unique hT1 hT2
  -- assemble the recycle counts
  have hF1 : recycleCount b ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail) j₀
      = recycleCount b t₁ j₀ := by
    rw [recycleCount_eq_of_getElem?_eq b (fun q _ => hfst q (by omega))]
    exact recycleCount_map_seqLift A A b t₁ j₀
  have hF2 : recycleCount b ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail) (t₁.length - 2)
      = recycleCount b t₁ (t₁.length - 2) := by
    rw [recycleCount_eq_of_getElem?_eq b (fun q hq => hfst q hq)]
    exact recycleCount_map_seqLift A A b t₁ (t₁.length - 2)
  have hΔ : recycleCount b t₁ (t₁.length - 2) = I.loopK h * I.arrivers b / I.arrivalCount h b := by
    rw [← recycleCount_done_last hchain1 ht₁L h2]
    exact Config.WellSynchronized.pow_barriers_advance_count h WF_initial rfl ht₁ hb
  subst hm₁eq hm₂eq
  simp only [Nat.add_sub_cancel]
  rw [show j₂ = (t₁.length - 2) + j₀ by omega, recycleCount_suffix b hsnd, hF1, hF2, hΔ]
  omega

/-- **The recycle-count core of Lemma 3 (two-batch case).** There is a successful trace `τ` of
`I ^ k ⨾ I ^ k` along which, for every barrier instruction, `b` has been recycled exactly
`k · arrivers(b) / arrival-count(b)` *more* times just before the **second** batch's copy
executes than just before the **first** batch's copy. This packages `replay_recycle_offset`
with a single batch trace `t₁` obtained from `hWS0`. -/
theorem CTA.WellSynchronized.second_batch_recycle_offset {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (n : ℕ+) (m₁ m₂ : Nat),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, n) →
        IsTimeOf (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ⟨t, j⟩ m₁ →
        IsTimeOf (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ
            ⟨t, ((I ^ k).prog t).length + j⟩ m₂ →
        recycleCount b τ (m₂ - 1)
          = recycleCount b τ (m₁ - 1) + k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  obtain ⟨t₁, ht₁⟩ := hWS0.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  exact ⟨_, replay_trace (I ^ I.loopK h) ht₁ ht₁L, replay_recycle_offset h ht₁ ht₁L⟩

/-! ### Structural lemmas for the `n`-batch program layout

`(A ^ m).prog t` is `m` consecutive copies of one batch `A.prog t`. These lemmas expose
that layout: programs split additively in the exponent (`pow_add_prog`), lengths scale
(`pow_prog_length`), and the small cases `m = 1, 2` collapse to the obvious forms. They are
what lets the `n`-batch program regroup as `(A ^ (n-2)) ⨾ (A ⨾ A)` — the first `n-2`
batches followed by the last two. -/

/-- `(A ^ (a + b)).prog t = (A ^ a).prog t ++ (A ^ b).prog t`: the program of `a + b`
batches is the `a`-batch program followed by the `b`-batch program (every batch is the same
`A.prog t`, so the split is purely by count). -/
theorem CTA.pow_add_prog (A : CTA) (a b : Nat) (t : ThreadId) :
    (A ^ (a + b)).prog t = (A ^ a).prog t ++ (A ^ b).prog t := by
  induction a with
  | zero => rw [Nat.zero_add]; simp [CTA.pow_zero, CTA.emptied]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, CTA.pow_succ_prog, ih, ← List.append_assoc,
      ← CTA.pow_succ_prog]

/-- `((A ^ m).prog t).length = m * (A.prog t).length`: `m` batches of length `|A.prog t|`. -/
theorem CTA.pow_prog_length (A : CTA) (m : Nat) (t : ThreadId) :
    ((A ^ m).prog t).length = m * (A.prog t).length := by
  induction m with
  | zero => simp [CTA.pow_zero, CTA.emptied]
  | succ m ih => rw [CTA.pow_succ_prog, List.length_append, ih, Nat.succ_mul]; omega

/-- `(A ^ 1).prog t = A.prog t`: one batch is just `A` (the trailing `A ^ 0 = emptied` adds
nothing). -/
theorem CTA.pow_one_prog (A : CTA) (t : ThreadId) : (A ^ 1).prog t = A.prog t := by
  rw [show (1 : Nat) = 0 + 1 from rfl, CTA.pow_succ_prog]; simp [CTA.pow_zero, CTA.emptied]

/-- `(A ^ 2).prog t = A.prog t ++ A.prog t`: two batches back to back — the program of
`A ⨾ A`. -/
theorem CTA.pow_two_prog (A : CTA) (t : ThreadId) :
    (A ^ 2).prog t = A.prog t ++ A.prog t := by
  rw [show (2 : Nat) = 1 + 1 from rfl, CTA.pow_succ_prog, CTA.pow_one_prog]

/-- `A ^ 1 = A`: one batch is `A` itself. -/
theorem CTA.pow_one (A : CTA) : A ^ 1 = A := by
  apply CTA.ext
  · rw [CTA.pow_ids]
  · funext t; rw [CTA.pow_one_prog]

/-- `A ^ 2 = A ⨾ A`: two batches *are* the sequential composition `A ⨾ A`. -/
theorem CTA.pow_two_eq_seq (A : CTA) : A ^ 2 = A.seq A rfl := by
  apply CTA.ext
  · change (A ^ 2).ids = A.ids; rw [CTA.pow_ids]
  · funext t; change (A ^ 2).prog t = A.prog t ++ A.prog t; rw [CTA.pow_two_prog]

/-- `A ^ 3 = (A ⨾ A) ⨾ A`: three batches *are* the left-associated sequential composition (the
program shape used by the three-batch Lemma 4.2 theorems). -/
theorem CTA.pow_three_eq_seq (A : CTA) : A ^ 3 = (A.seq A rfl).seq A rfl := by
  apply CTA.ext
  · change (A ^ 3).ids = A.ids; rw [CTA.pow_ids]
  · funext t
    change (A ^ 3).prog t = (A.prog t ++ A.prog t) ++ A.prog t
    rw [show (3 : Nat) = 2 + 1 from rfl, CTA.pow_succ_prog, CTA.pow_two_prog, List.append_assoc]

/-- `(A ^ a) ^ b = A ^ (a * b)`: iterating the `a`-batch power `b` times is the `a * b`-batch
power — exponents multiply. The bridge between the batched loop `(I ^ k) ^ c` and the flat
unrolling `I ^ (k * c)`. -/
theorem CTA.pow_mul (A : CTA) (a b : Nat) : (A ^ a) ^ b = A ^ (a * b) := by
  apply CTA.ext
  · simp only [CTA.pow_ids]
  · funext t
    induction b with
    | zero => simp [CTA.pow_zero, CTA.emptied]
    | succ b ih =>
      rw [CTA.pow_succ_prog, ih, ← CTA.pow_add_prog, Nat.mul_succ, Nat.add_comm a (a * b)]

/-- `A ^ (a + b) = (A ^ a) ⨾ (A ^ b)`: splitting the exponent additively is the sequential
composition of the two sub-powers. -/
theorem CTA.pow_add_eq_seq (A : CTA) (a b : Nat) :
    A ^ (a + b) = (A ^ a).seq (A ^ b) (by simp only [CTA.pow_ids]) := by
  apply CTA.ext
  · change (A ^ (a + b)).ids = (A ^ a).ids; simp only [CTA.pow_ids]
  · funext t
    change (A ^ (a + b)).prog t = (A ^ a).prog t ++ (A ^ b).prog t
    rw [CTA.pow_add_prog]

/-- The split underlying the loop-with-epilogue reduction: `k * c + r` iterations factor as
`c` full `k`-batches `(I ^ k) ^ c` followed by an `r`-iteration epilogue `I ^ r`. -/
theorem CTA.pow_split (I : CTA) (k c r : Nat) :
    I ^ (k * c + r) = ((I ^ k) ^ c).seq (I ^ r) (by simp only [CTA.pow_ids]) := by
  apply CTA.ext
  · change (I ^ (k * c + r)).ids = ((I ^ k) ^ c).ids; simp only [CTA.pow_ids]
  · funext t
    change (I ^ (k * c + r)).prog t = ((I ^ k) ^ c).prog t ++ (I ^ r).prog t
    rw [CTA.pow_add_prog, CTA.pow_mul]

/-- **Regroup the last two batches.** For `n ≥ 2`, the `n`-batch program `A ^ n` *is* the
first `n - 2` batches sequentially composed with the last two: `A ^ n = (A ^ (n-2)) ⨾ (A ⨾ A)`.
This is the structural identity that lets `last_batch_gen_offset` reuse the two-batch
`second_batch` machinery on the final `A ⨾ A`, with the first `n - 2` batches as an inert
prefix. -/
theorem CTA.pow_regroup_last_two (A : CTA) {n : Nat} (hn : 2 ≤ n) :
    A ^ n = (A ^ (n - 2)).seq (A.seq A rfl) (CTA.pow_ids A (n - 2)) := by
  apply CTA.ext
  · change (A ^ n).ids = (A ^ (n - 2)).ids; rw [CTA.pow_ids, CTA.pow_ids]
  · funext t
    change (A ^ n).prog t = (A ^ (n - 2)).prog t ++ (A.prog t ++ A.prog t)
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [CTA.pow_add_prog, CTA.pow_two_prog]

/-- **Regroup the last batch.** For `n ≥ 1`, `A ^ n = (A ^ (n-1)) ⨾ A`: the first `n-1`
batches sequentially composed with the last one. The companion of `pow_regroup_last_two`,
used to expose the final batch as the appended `B`-part for `seq_no_happensBefore_B_to_A`. -/
theorem CTA.pow_regroup_last_one (A : CTA) {n : Nat} (hn : 1 ≤ n) :
    A ^ n = (A ^ (n - 1)).seq A (CTA.pow_ids A (n - 1)) := by
  apply CTA.ext
  · change (A ^ n).ids = (A ^ (n - 1)).ids; rw [CTA.pow_ids, CTA.pow_ids]
  · funext t
    change (A ^ n).prog t = (A ^ (n - 1)).prog t ++ A.prog t
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [CTA.pow_add_prog, CTA.pow_one_prog]

/-- **Regroup the last three batches.** For `n ≥ 3`, `A ^ n = (A ^ (n-3)) ⨾ (A ⨾ (A ⨾ A))`:
the first `n-3` batches sequentially composed with the last three (right-associated, matching
the program shape of `third_batch_recycle_offset`). Lets the `n`-batch Lemma 4.2 reuse the
three-batch machinery on the final `A ⨾ (A ⨾ A)`. -/
theorem CTA.pow_regroup_last_three (A : CTA) {n : Nat} (hn : 3 ≤ n) :
    A ^ n = (A ^ (n - 3)).seq (A.seq (A.seq A rfl) rfl) (CTA.pow_ids A (n - 3)) := by
  apply CTA.ext
  · change (A ^ n).ids = (A ^ (n - 3)).ids; rw [CTA.pow_ids, CTA.pow_ids]
  · funext t
    change (A ^ n).prog t = (A ^ (n - 3)).prog t ++ (A.prog t ++ (A.prog t ++ A.prog t))
    have h3 : (A ^ 3).prog t = A.prog t ++ (A.prog t ++ A.prog t) := by
      rw [show (3 : Nat) = 2 + 1 from rfl, CTA.pow_succ_prog, CTA.pow_two_prog]
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [CTA.pow_add_prog, h3]

/-! ### Gluing traces across a batch boundary

`glue_trace` generalizes `replay_trace`: given a successful `A`-trace ending in
`done State.initial` (full restoration) and *any* successful `B`-trace from `State.initial`
(`A.ids = B.ids`), it splices the lifted `A`-execution in front of the `B`-trace to obtain a
successful trace of `A ⨾ B`. Iterating it (`pow_replay_trace`) builds a trace of `A ^ m` that
runs `m` batches of `A` back to back. -/

/-- **Splice two batches.** A successful `A`-trace `t_A` that fully restores the state
(`done State.initial`) followed by any successful `B`-trace `τ_B` from `State.initial` glue
into a successful trace of `A ⨾ B`: lift `t_A`'s execution (minus its terminal `done`) as the
`A`-phase, then continue with `τ_B` (minus its head, which the lifted phase already reaches).
The glued trace ends exactly where `τ_B` ends. -/
theorem glue_trace {A B : CTA} (hids : A.ids = B.ids) {s_A s_mid : State} {t_A : List Config}
    (htA : IsSuccessfulTraceFrom (Config.run s_A A) t_A)
    (hAlast : t_A.getLast? = some (Config.done s_mid))
    {τ_B : List Config} (hτB : IsSuccessfulTraceFrom (Config.run s_mid B) τ_B) :
    IsSuccessfulTraceFrom (Config.run s_A (A.seq B hids))
        (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail) ∧
      (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail).getLast? = τ_B.getLast? ∧
      ∀ r, (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail)[(t_A.length - 2) + r]?
          = τ_B[r]? := by
  have hchain : List.IsChain CTAStep t_A := htA.1.1.subtrace
  have hhead : t_A.head? = some (Config.run s_A A) := htA.1.2
  obtain ⟨_, _, hteq⟩ : ∃ c1 trest, t_A = Config.run s_A A :: c1 :: trest := by
    rcases t_A with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hhead
    · rw [List.head?_cons, Option.some.injEq] at hhead
      rw [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hhead] at hAlast; exact absurd hAlast (by simp)
    · rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead; exact ⟨b, l, rfl⟩
  have hdrop : t_A.dropLast ≠ [] := by rw [hteq]; simp
  -- The boundary config `C⋆ = seqLift A B (penult t_A)` is `run s_mid B` (the `A`-run ends at
  -- `s_mid`), so the given B-trace `τ_B` from `s_mid` is a complete continuation from `C⋆`;
  -- `seq_splice` glues it onto the lifted `A`-phase.
  have hCstar : Config.seqLift A B (t_A.dropLast.getLast hdrop) = Config.run s_mid B :=
    seqLift_penultimate_gen hids hchain hhead hAlast hdrop
  have hcont : IsCompleteTraceFrom (Config.seqLift A B (t_A.dropLast.getLast hdrop)) τ_B := by
    rw [hCstar]; exact hτB.1
  obtain ⟨hICF, hsplit⟩ := seq_splice hids htA hdrop hcont
  obtain ⟨sB, hBlast⟩ := hτB.2
  -- the glued trace ends where `τ_B` ends (rewriting it via `hsplit` to `P.dropLast ++ τ_B`)
  have hgetlast : (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail).getLast? = τ_B.getLast? := by
    rw [hsplit, hBlast]; exact List.mem_getLast?_append_of_mem_getLast? hBlast
  -- the suffix-index relation, also a consequence of `hsplit`
  have hQlen : ((t_A.dropLast.map (Config.seqLift A B)).dropLast).length = t_A.length - 2 := by
    rw [List.length_dropLast, List.length_map, List.length_dropLast]; omega
  have hsnd : ∀ r, (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail)[(t_A.length - 2) + r]?
      = τ_B[r]? := by
    intro r
    rw [hsplit, List.getElem?_append_right (by rw [hQlen]; omega), hQlen]
    congr 1; omega
  exact ⟨⟨hICF, sB, hgetlast.trans hBlast⟩, hgetlast, hsnd⟩

/-- **The `m`-fold replay trace.** From a single restoring batch trace `t₁` (a successful
`A`-trace from `State.initial` ending in `done State.initial`), build a successful trace of
`A ^ m` that runs `m` batches of `A` back to back, each one replaying `t₁`. Every such trace
again ends in `done State.initial` (full restoration is preserved across batches), so the
next batch can be spliced in front. The construction needs only `t₁` — no well-synchronization
of `A ^ m` itself. -/
theorem pow_replay_trace (A : CTA) {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run State.initial A) t₁)
    (h1last : t₁.getLast? = some (Config.done State.initial)) :
    ∀ (m : Nat), ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial (A ^ m)) τ ∧
      τ.getLast? = some (Config.done State.initial) := by
  intro m
  induction m with
  | zero =>
    have hstep : CTAStep (Config.run State.initial (A ^ 0)) (Config.done State.initial) := by
      apply CTAStep.done
      · intro i _; simp [CTA.pow_zero, CTA.emptied]
      · intro b I A' n hb; simp [State.initial, BarrierState.unconfigured] at hb
    exact ⟨[Config.run State.initial (A ^ 0), Config.done State.initial],
      ⟨⟨⟨List.isChain_cons_cons.mpr ⟨hstep, List.isChain_singleton _⟩,
            Config.done State.initial, rfl, Or.inl ⟨State.initial, rfl⟩⟩, rfl⟩,
        State.initial, rfl⟩, rfl⟩
  | succ m ih =>
    obtain ⟨τ, hτ, hτlast⟩ := ih
    obtain ⟨hglue, hgluelast, _⟩ := glue_trace (A.pow_ids m).symm ht₁ h1last hτ
    refine ⟨t₁.dropLast.map (Config.seqLift A (A ^ m)) ++ τ.tail, ?_, ?_⟩
    · rw [CTA.pow_succ]; exact hglue
    · rw [hgluelast, hτlast]

/-- **The `m`-fold replay trace from a restoring `done` start `s`.** The non-initial-start
generalization of `pow_replay_trace`: from a single batch trace `t₁` of `A` from `run s A` that
restores `s` (ends `done s`), plus the no-full premise `hnofull` of `s` (which lets the empty
`A ^ 0` terminate at `s`), build a successful trace of `A ^ m` from `run s (A ^ m)` again ending
in `done s`. This replays the loop body verbatim from the post-prefix state. -/
theorem pow_replay_trace_from (A : CTA) {s : State}
    (hnofull : ∀ b I A' n, s.B b = ⟨I, A', some n⟩ → I.length + A' < (n : Nat))
    {t₁ : List Config} (ht₁ : IsSuccessfulTraceFrom (Config.run s A) t₁)
    (h1last : t₁.getLast? = some (Config.done s)) :
    ∀ (m : Nat), ∃ τ, IsSuccessfulTraceFrom (Config.run s (A ^ m)) τ ∧
      τ.getLast? = some (Config.done s) := by
  intro m
  induction m with
  | zero =>
    have hstep : CTAStep (Config.run s (A ^ 0)) (Config.done s) := by
      apply CTAStep.done
      · intro i _; simp [CTA.pow_zero, CTA.emptied]
      · exact hnofull
    exact ⟨[Config.run s (A ^ 0), Config.done s],
      ⟨⟨⟨List.isChain_cons_cons.mpr ⟨hstep, List.isChain_singleton _⟩,
            Config.done s, rfl, Or.inl ⟨s, rfl⟩⟩, rfl⟩,
        s, rfl⟩, rfl⟩
  | succ m ih =>
    obtain ⟨τ, hτ, hτlast⟩ := ih
    obtain ⟨hglue, hgluelast, _⟩ := glue_trace (A.pow_ids m).symm ht₁ h1last hτ
    refine ⟨t₁.dropLast.map (Config.seqLift A (A ^ m)) ++ τ.tail, ?_, ?_⟩
    · rw [CTA.pow_succ]; exact hglue
    · rw [hgluelast, hτlast]

/-- Every batch-prefix of the `n`-fold composition `A ^ n` is well-synchronized: each of
`A ^ 1, A ^ 2, …, A ^ n` is well-synchronized — i.e. running `1, 2, …, n` consecutive batches
of `A` is well-synchronized in every case. This is the hypothesis the `n`-batch Lemma 3 needs:
the two-batch `second_batch_gen_offset` assumed `A` and `A ⨾ A` separately (the `m = 1` and
`m = 2` prefixes); the general statement relates batch `m` to batch `m - 1` inside each
`m`-batch run, so it needs the analogous well-synchronization of every prefix `A ^ m`,
`1 ≤ m ≤ n`. -/
def CTA.BatchesWellSynchronized (A : CTA) (n : Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ n → (A ^ m).WellSynchronized

/-- **The recycle-count core of the `n`-batch Lemma 3.** There is a successful trace `τ` of
`(I ^ k) ^ n` along which, for every barrier instruction, the recycle count of `b` just
before the **last** batch's copy executes exceeds the count just before the **second-to-last**
batch's copy by exactly `k · arrivers(b) / arrival-count(b)` — one batch's worth of recycles.

The trace is built by `glue`-ing the two-batch trace of `second_batch_recycle_offset` (the
last two batches) onto an `(n-2)`-fold replay (`pow_replay_trace`) of the first batches, using
the regrouping `(I ^ k) ^ n = (I ^ k) ^ (n-2) ⨾ ((I ^ k) ⨾ (I ^ k))`. The first `n-2` batches
add the *same* constant recycle count before both of the final two copies, so it cancels in
the difference, leaving exactly the two-batch offset. -/
theorem CTA.WellSynchronized.last_batch_recycle_offset {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 2 ≤ n)
    (hWS0 : (I ^ k).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ n)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (m₁ m₂ : Nat),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run State.initial ((I ^ k) ^ n)) τ
            ⟨t, (n - 2) * ((I ^ k).prog t).length + j⟩ m₁ →
        IsTimeOf (Config.run State.initial ((I ^ k) ^ n)) τ
            ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩ m₂ →
        recycleCount b τ (m₂ - 1)
          = recycleCount b τ (m₁ - 1) + k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  -- well-synchronization of one batch, the only ingredient the construction needs
  have hWSA : (I ^ I.loopK h).WellSynchronized := hWS0
  -- single batch trace, restoring the state to `initial`
  obtain ⟨t₁, ht₁⟩ := hWSA.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  -- two-batch trace with the per-instruction offset (the hard two-batch case)
  obtain ⟨τAA, hτAA, hrecAA⟩ := CTA.WellSynchronized.second_batch_recycle_offset h rfl hWSA
  -- `(n-2)`-fold replay of the first batches
  obtain ⟨tC, htC, htCL⟩ := pow_replay_trace (I ^ I.loopK h) ht₁ ht₁L (n - 2)
  set A := I ^ I.loopK h with hA
  -- glue the first `n-2` batches in front of the last two
  obtain ⟨hglue, -, hsnd⟩ := glue_trace (B := A.seq A rfl) (CTA.pow_ids A (n - 2)) htC htCL hτAA
  have hAn : A ^ n = (A ^ (n - 2)).seq (A.seq A rfl) (CTA.pow_ids A (n - 2)) :=
    CTA.pow_regroup_last_two A hn
  refine ⟨tC.dropLast.map (Config.seqLift (A ^ (n - 2)) (A.seq A rfl)) ++ τAA.tail, ?_, ?_⟩
  · rw [hAn]; exact hglue
  · intro t j c b par m₁ m₂ hcj hbr ht1 ht2
    obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
    have hSucc : IsSuccessfulTraceFrom (Config.run State.initial (A ^ n))
        (tC.dropLast.map (Config.seqLift (A ^ (n - 2)) (A.seq A rfl)) ++ τAA.tail) := by
      rw [hAn]; exact hglue
    -- program-length bookkeeping for thread `t`
    have hCLen : ((A ^ (n - 2)).prog t).length = (n - 2) * (A.prog t).length :=
      CTA.pow_prog_length A (n - 2) t
    have hAAlen : ((A.seq A rfl).prog t).length = (A.prog t).length + (A.prog t).length := by
      change (A.prog t ++ A.prog t).length = _; rw [List.length_append]
    have hnL : n * (A.prog t).length
        = (n - 2) * (A.prog t).length + ((A.prog t).length + (A.prog t).length) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.add_mul]
      omega
    have hnLen : ((A ^ n).prog t).length = n * (A.prog t).length := CTA.pow_prog_length A n t
    have hprogeq : (A ^ n).prog t = (A ^ (n - 2)).prog t ++ (A.seq A rfl).prog t :=
      congrFun (congrArg CTA.prog hAn) t
    -- transport a two-batch instruction time into the `n`-batch trace (shifted by the prefix)
    have transport : ∀ (q M' : Nat), q < ((A.seq A rfl).prog t).length →
        IsTimeOf (Config.run State.initial (A.seq A rfl)) τAA ⟨t, q⟩ M' →
        IsTimeOf (Config.run State.initial (A ^ n))
          (tC.dropLast.map (Config.seqLift (A ^ (n - 2)) (A.seq A rfl)) ++ τAA.tail)
          ⟨t, (n - 2) * (A.prog t).length + q⟩ ((tC.length - 2) + M') := by
      intro q M' hq hT'
      obtain ⟨-, -, j', D, D', hM'eq, hDj, hDj1, hDprog, hD'prog⟩ := hT'
      rw [hAAlen] at hq
      refine ⟨hSucc.1, ?_, (tC.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
      · change (n - 2) * (A.prog t).length + q < ((A ^ n).prog t).length
        rw [hnLen, hnL]; omega
      · exact (hsnd j').trans hDj
      · rw [show (tC.length - 2) + j' + 1 = (tC.length - 2) + (j' + 1) from by omega]
        exact (hsnd (j' + 1)).trans hDj1
      · change D.progOf t = ((A ^ n).prog t).drop ((n - 2) * (A.prog t).length + q)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 2) * (A.prog t).length + q - ((A ^ (n - 2)).prog t).length = q from by
            rw [hCLen]; omega]
        exact hDprog
      · change D'.progOf t = ((A ^ n).prog t).drop ((n - 2) * (A.prog t).length + q + 1)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 2) * (A.prog t).length + q + 1 - ((A ^ (n - 2)).prog t).length = q + 1 from by
            rw [hCLen]; omega]
        exact hD'prog
    -- the two corresponding instruction times in the two-batch trace
    obtain ⟨sdAA, hAAlast⟩ := hτAA.2
    obtain ⟨m₁', hT1'⟩ := exists_time_of_ends_done hτAA.1 hAAlast (η := ⟨t, j⟩)
      (by change j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
    obtain ⟨m₂', hT2'⟩ := exists_time_of_ends_done hτAA.1 hAAlast
      (η := ⟨t, (A.prog t).length + j⟩)
      (by change (A.prog t).length + j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
    have hΔAA := hrecAA t j c b par m₁' m₂' hcj hbr hT1' hT2'
    -- match the given times against the transported ones
    have hidx2 : (n - 1) * (A.prog t).length + j
        = (n - 2) * (A.prog t).length + ((A.prog t).length + j) := by
      rw [show n - 1 = (n - 2) + 1 from by omega, Nat.succ_mul]; omega
    have hTr1 := transport j m₁' (by rw [hAAlen]; omega) hT1'
    have hTr2 := transport ((A.prog t).length + j) m₂' (by rw [hAAlen]; omega) hT2'
    rw [hidx2] at ht2
    have hm₁ : m₁ = (tC.length - 2) + m₁' := IsTimeOf.unique ht1 hTr1
    have hm₂ : m₂ = (tC.length - 2) + m₂' := IsTimeOf.unique ht2 hTr2
    have hm1' : 1 ≤ m₁' := by obtain ⟨_, _, _, he, _⟩ := hT1'.2.2; omega
    have hm2' : 1 ≤ m₂' := by obtain ⟨_, _, _, he, _⟩ := hT2'.2.2; omega
    have e1 : m₁ - 1 = (tC.length - 2) + (m₁' - 1) := by rw [hm₁]; omega
    have e2 : m₂ - 1 = (tC.length - 2) + (m₂' - 1) := by rw [hm₂]; omega
    rw [e1, e2, recycleCount_suffix b hsnd, recycleCount_suffix b hsnd, hΔAA]
    omega

/-- **Lemma 3, `n`-batch case (last two batches).** Let
`k = I.loopK h` be the §1 iteration count and fix a batch count `n ≥ 2`. The `n`-fold
repeated composition `(I ^ k) ^ n` lays each thread's program out as `n` consecutive
copies of one batch `(I ^ k).prog t` (`CTA.pow_succ_prog`, iterated). Assuming **every
batch-prefix** `(I ^ k) ^ m` (`1 ≤ m ≤ n`) is well-synchronized (`hWS`, a
`CTA.BatchesWellSynchronized` hypothesis — generalizing the two `WellSynchronized`
assumptions of `second_batch_gen_offset`, which were exactly the `m = 1` and `m = 2`
prefixes), there is a successful trace `τ` of `(I ^ k) ^ n` whose recovered generation mapping
(`pointGen`) exhibits the document's Lemma 3 relationship between the **last two** batches:
every barrier instruction of the **last** batch has the same generation as the corresponding
instruction of the **second-to-last** batch, incremented by `k · arrivers(b) / arrival-count(b)`,
the number of times one batch recycles that instruction's barrier `b`.

A program point `⟨t, j⟩` with `((I ^ k).prog t)[j]? = some c` is instruction `j` of thread
`t` within one batch (`j < |(I ^ k).prog t|`). With `L = |(I ^ k).prog t|`, the copy of that
instruction in batch `i` (0-indexed) is `⟨t, i · L + j⟩`; the last batch is `i = n - 1` and
the second-to-last is `i = n - 2`. The statement is given only for barrier instructions
(`Cmd.barrierRef c = some (b, m)`), the ones generations are defined on. This is the two-batch
`second_batch_gen_offset` with the first/second pair replaced by the second-to-last/last pair,
which the absence of backward happens-before edges between batches
(`seq_no_happensBefore_B_to_A`) makes equivalent: the earlier batches cannot perturb the
generations of the final two, so only their *relative* recycle offset (one batch's worth)
survives. -/
theorem CTA.WellSynchronized.last_batch_gen_offset_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (m : ℕ+),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, m) →
        pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, n * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b := by
  -- single-batch well-synchronization is all the recycle core needs
  have hWS0 : (I ^ k).WellSynchronized := by
    have := hWS 1 (le_refl 1) hn; rwa [CTA.pow_one] at this
  -- The recycle-count core (applied to `n + 1` batches) supplies the trace and the
  -- per-instruction offset between the last two batches `n - 1` and `n`; this is the routine
  -- `pointGen`-to-`recycleCount` repackaging.
  obtain ⟨τ, hτ, hrec⟩ :=
    CTA.WellSynchronized.last_batch_recycle_offset (n := n + 1) h hk (by omega) hWS0
  rw [show n + 1 - 2 = n - 1 from by omega, show n + 1 - 1 = n from by omega] at hrec
  refine ⟨τ, hτ, ?_⟩
  intro t j c b par hcj hbr
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hcj
  obtain ⟨sd, hlast⟩ := hτ.2
  -- length bookkeeping for thread `t`'s `(n + 1)`-batch program
  have hnLen : (((I ^ k) ^ (n + 1)).prog t).length = (n + 1) * ((I ^ k).prog t).length :=
    CTA.pow_prog_length (I ^ k) (n + 1) t
  have hnL : (n + 1) * ((I ^ k).prog t).length
      = (n - 1) * ((I ^ k).prog t).length
        + (((I ^ k).prog t).length + ((I ^ k).prog t).length) := by
    conv_lhs => rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]
    omega
  have hn1L : n * ((I ^ k).prog t).length
      = (n - 1) * ((I ^ k).prog t).length + ((I ^ k).prog t).length := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [Nat.add_mul, Nat.one_mul]
  -- the command at each of the two copies is `c`, a barrier op on `b`
  have hcmdat : ∀ q, q < n + 1 →
      (((I ^ k) ^ (n + 1)).prog t)[q * ((I ^ k).prog t).length + j]? = some c := by
    intro q hq
    have hqLen : (((I ^ k) ^ q).prog t).length = q * ((I ^ k).prog t).length :=
      CTA.pow_prog_length (I ^ k) q t
    have hsplit : ((I ^ k) ^ (n + 1)).prog t
        = ((I ^ k) ^ q).prog t ++ ((I ^ k) ^ (n + 1 - q)).prog t := by
      conv_lhs => rw [show n + 1 = q + (n + 1 - q) from by omega]
      rw [CTA.pow_add_prog]
    rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
      show q * ((I ^ k).prog t).length + j - q * ((I ^ k).prog t).length = j from by omega,
      show n + 1 - q = (n + 1 - q - 1) + 1 from by omega, CTA.pow_succ_prog,
      List.getElem?_append_left hjlt]
    exact hcj
  have hcmd1 : ((I ^ k) ^ (n + 1)).cmdAt ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat (n - 1) (by omega)
  have hcmd2 : ((I ^ k) ^ (n + 1)).cmdAt ⟨t, n * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat n (by omega)
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  -- both copies execute in the successful trace `τ`
  obtain ⟨m₁, ht1⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩)
    (by change (n - 1) * ((I ^ k).prog t).length + j < (((I ^ k) ^ (n + 1)).prog t).length
        rw [hnLen, hnL]; omega)
  obtain ⟨m₂, ht2⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, n * ((I ^ k).prog t).length + j⟩)
    (by change n * ((I ^ k).prog t).length + j < (((I ^ k) ^ (n + 1)).prog t).length
        rw [hnLen, hnL, hn1L]; omega)
  -- each generation is its barrier's recycle count just before its execution time, plus one
  have hg1 : pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₁ - 1) + 1 := by
    simp only [pointGen, hcmd1, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht1]
  have hg2 : pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, n * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₂ - 1) + 1 := by
    simp only [pointGen, hcmd2, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht2]
  rw [hg1, hg2, hrec t j c b par m₁ m₂ hcj hbr ht1 ht2]; omega

/-- One batch recycles each referenced barrier at least once: the per-batch recycle
constant `δ_b = k · arrivers(b) / arrival-count(b)` is `≥ 1`. Since `k = loopK h`, the total
arrivals over one batch reach the arrival count (`arrivalCount_le_pow_arrivers`), which
divides them (`arrivalCount_dvd_pow_arrivers`), so the quotient is at least one. -/
theorem one_le_delta {I : CTA} (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h)
    {b : Barrier} (hb : b ∈ I.barriers) :
    1 ≤ k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  have hc : 0 < I.arrivalCount h b := I.arrivalCount_pos h hb
  have hle : I.arrivalCount h b ≤ I.loopK h * I.arrivers b := by
    have := I.arrivalCount_le_pow_arrivers h hb
    rwa [I.arrivers_pow b (I.loopK h)] at this
  rw [Nat.le_div_iff_mul_le hc]; omega

/-- A barrier referenced by a command of `(I ^ k) ^ m` is referenced by `I` itself. The
command lives in `((I ^ k) ^ m).prog`, hence (peeling the two repeated compositions with
`CTA.mem_pow_prog`) in `I.prog`, so its barrier joins `I.barriers`. -/
theorem mem_barriers_of_cmdAt_pow {I : CTA} {k m : Nat} {η : ProgPoint} {c : Cmd}
    {b : Barrier} {par : ℕ+} (hcmd : ((I ^ k) ^ m).cmdAt η = some c)
    (hbr : Cmd.barrierRef c = some (b, par)) : b ∈ I.barriers := by
  rw [CTA.cmdAt] at hcmd
  have hmem : c ∈ ((I ^ k) ^ m).prog η.thread := List.mem_of_getElem? hcmd
  have hmemI : c ∈ I.prog η.thread := I.mem_pow_prog ((I ^ k).mem_pow_prog hmem)
  have hlt : η.idx < (((I ^ k) ^ m).prog η.thread).length :=
    (List.getElem?_eq_some_iff.mp hcmd).1
  have hid : η.thread ∈ I.ids := by
    have := mem_ids_of_idx_lt ((I ^ k) ^ m) hlt
    rwa [CTA.pow_ids, CTA.pow_ids] at this
  rw [CTA.barriers, Finset.mem_biUnion]
  exact ⟨η.thread, hid, List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨(b, par), List.mem_filterMap.mpr ⟨c, hmemI, hbr⟩, rfl⟩)⟩

/-- **No backward happens-before edge across batches** (WS-free). Along the replay trace
`τ`, `happensBefore` never runs from a point in batch `≥ p` down into a strictly earlier
batch `< p`. The argument is purely generational: every `initRelation` edge is either program
order (same thread, index increases) or a barrier edge whose two endpoints share a generation;
its target is a `sync` whose generation is `≤ (batch + 1)·δ` (hypothesis `hU`) while its source
in batch `p` has generation `≥ p·δ + 1` (hypothesis `hL`); with `δ ≥ 1` equal generations force
source-batch `≤` target-batch. No well-synchronization of `(I ^ k) ^ (n + 1)` is needed. -/
theorem no_backward_edge {I : CTA} (h : I.ConsistentArrivalCounts) {k : Nat}
    (hk : k = I.loopK h) {n : Nat} {τ : List Config}
    (hL : ∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
       ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
       (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers b / I.arrivalCount h b) + 1
         ≤ pointGen ((I ^ k) ^ (n + 1)) τ η)
    (hU : ∀ (η : ProgPoint) (b : Barrier) (par : ℕ+),
       ((I ^ k) ^ (n + 1)).cmdAt η = some (Cmd.sync b par) →
       pointGen ((I ^ k) ^ (n + 1)) τ η
         ≤ (η.idx / ((I ^ k).prog η.thread).length + 1) * (k * I.arrivers b / I.arrivalCount h b)) :
    ∀ (p : Nat) (s d : ProgPoint), happensBefore ((I ^ k) ^ (n + 1)) τ s d →
      p * ((I ^ k).prog s.thread).length ≤ s.idx →
      d.idx < p * ((I ^ k).prog d.thread).length → False := by
  -- per-step batch monotonicity: an `initRelation` edge cannot lower the batch threshold `p`
  have step : ∀ (p : Nat) (x y : ProgPoint), (x, y) ∈ initRelation ((I ^ k) ^ (n + 1)) τ →
      p * ((I ^ k).prog x.thread).length ≤ x.idx →
      p * ((I ^ k).prog y.thread).length ≤ y.idx := by
    intro p x y hxy hxp
    rw [mem_initRelation_iff] at hxy
    rcases hxy with ⟨_, _, hyeq⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩
    · -- program order: same thread, index only grows
      subst hyeq; dsimp only; omega
    · -- arrive → sync
      have hbI : bb ∈ I.barriers := mem_barriers_of_cmdAt_pow hc1 rfl
      have hLx := hL x _ bb par hc1 rfl
      have hUy := hU y bb par hc2
      have hLxpos : 0 < ((I ^ k).prog x.thread).length := by
        rcases Nat.eq_zero_or_pos ((I ^ k).prog x.thread).length with h0 | hpos
        · rw [h0, Nat.mul_zero] at hxp
          rw [CTA.cmdAt] at hc1
          have := (List.getElem?_eq_some_iff.mp hc1).1
          rw [CTA.pow_prog_length, h0, Nat.mul_zero] at this; omega
        · exact hpos
      have hLypos : 0 < ((I ^ k).prog y.thread).length := by
        rw [CTA.cmdAt] at hc2
        have hlt := (List.getElem?_eq_some_iff.mp hc2).1
        rcases Nat.eq_zero_or_pos ((I ^ k).prog y.thread).length with h0 | hpos
        · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hlt; omega
        · exact hpos
      have hdelta : 1 ≤ k * I.arrivers bb / I.arrivalCount h bb := one_le_delta h hk hbI
      set δ := k * I.arrivers bb / I.arrivalCount h bb with hδ
      have hple : p ≤ x.idx / ((I ^ k).prog x.thread).length :=
        (Nat.le_div_iff_mul_le hLxpos).mpr (by omega)
      have hchain : p * δ + 1 ≤ (y.idx / ((I ^ k).prog y.thread).length + 1) * δ := by
        calc p * δ + 1 ≤ (x.idx / ((I ^ k).prog x.thread).length) * δ + 1 :=
              by have := Nat.mul_le_mul_right δ hple; omega
          _ ≤ pointGen ((I ^ k) ^ (n + 1)) τ x := hLx
          _ = pointGen ((I ^ k) ^ (n + 1)) τ y := hg
          _ ≤ (y.idx / ((I ^ k).prog y.thread).length + 1) * δ := hUy
      have hpq : p ≤ y.idx / ((I ^ k).prog y.thread).length := by
        by_contra hcon
        push Not at hcon
        have : (y.idx / ((I ^ k).prog y.thread).length + 1) * δ ≤ p * δ :=
          Nat.mul_le_mul_right δ (by omega)
        omega
      calc p * ((I ^ k).prog y.thread).length
          ≤ (y.idx / ((I ^ k).prog y.thread).length) * ((I ^ k).prog y.thread).length :=
            Nat.mul_le_mul_right _ hpq
        _ ≤ y.idx := Nat.div_mul_le_self _ _
    · -- sync → sync
      have hbI : bb ∈ I.barriers := mem_barriers_of_cmdAt_pow hc1 rfl
      have hLx := hL x _ bb par hc1 rfl
      have hUy := hU y bb par hc2
      have hLxpos : 0 < ((I ^ k).prog x.thread).length := by
        rcases Nat.eq_zero_or_pos ((I ^ k).prog x.thread).length with h0 | hpos
        · rw [h0, Nat.mul_zero] at hxp
          rw [CTA.cmdAt] at hc1
          have := (List.getElem?_eq_some_iff.mp hc1).1
          rw [CTA.pow_prog_length, h0, Nat.mul_zero] at this; omega
        · exact hpos
      have hLypos : 0 < ((I ^ k).prog y.thread).length := by
        rw [CTA.cmdAt] at hc2
        have hlt := (List.getElem?_eq_some_iff.mp hc2).1
        rcases Nat.eq_zero_or_pos ((I ^ k).prog y.thread).length with h0 | hpos
        · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hlt; omega
        · exact hpos
      have hdelta : 1 ≤ k * I.arrivers bb / I.arrivalCount h bb := one_le_delta h hk hbI
      set δ := k * I.arrivers bb / I.arrivalCount h bb with hδ
      have hple : p ≤ x.idx / ((I ^ k).prog x.thread).length :=
        (Nat.le_div_iff_mul_le hLxpos).mpr (by omega)
      have hchain : p * δ + 1 ≤ (y.idx / ((I ^ k).prog y.thread).length + 1) * δ := by
        calc p * δ + 1 ≤ (x.idx / ((I ^ k).prog x.thread).length) * δ + 1 :=
              by have := Nat.mul_le_mul_right δ hple; omega
          _ ≤ pointGen ((I ^ k) ^ (n + 1)) τ x := hLx
          _ = pointGen ((I ^ k) ^ (n + 1)) τ y := hg
          _ ≤ (y.idx / ((I ^ k).prog y.thread).length + 1) * δ := hUy
      have hpq : p ≤ y.idx / ((I ^ k).prog y.thread).length := by
        by_contra hcon
        push Not at hcon
        have : (y.idx / ((I ^ k).prog y.thread).length + 1) * δ ≤ p * δ :=
          Nat.mul_le_mul_right δ (by omega)
        omega
      calc p * ((I ^ k).prog y.thread).length
          ≤ (y.idx / ((I ^ k).prog y.thread).length) * ((I ^ k).prog y.thread).length :=
            Nat.mul_le_mul_right _ hpq
        _ ≤ y.idx := Nat.div_mul_le_self _ _
  intro p s d hsd
  induction hsd using Relation.ReflTransGen.head_induction_on with
  | refl => intro hs hd; omega
  | @head x y hxy hyd ih => intro hx hd; exact ih (step p x y hxy hx) hd

/-- **Global recycle structure of the replay trace.** From a single restoring batch trace `t₁`
of `A = I ^ k` (ending in `done State.initial`), the `m`-fold replay trace `τ` of `A ^ m` has a
clean batch-additive recycle structure: the recycle count just before any barrier copy in batch
`p < m` exceeds the count before the matching copy in `t₁` itself by exactly `p · δ_b`, where
`δ_b = k · arrivers(b) / arrival-count(b)` is one batch's recycle count.

Proved by induction on `m`, gluing one fresh front batch (a copy of `t₁`) ahead of the `m`-batch
replay. The front batch recycles `b` exactly `δ_b` times (`pow_barriers_advance_count`), and the
later batches' copies are the recursive trace's copies shifted by the front batch; the count
splits across the front boundary by `recycleCount_suffix`, and the front portion mirrors `t₁`
itself (`recycleCount_map_seqLift`). Stating the offset relative to the fixed `t₁` (not the
batch-`0` copy in `τ`) is what keeps the induction non-circular. -/
theorem pow_replay_recycle_structure {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s))
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false) (m : Nat) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h) ^ m)) τ ∧
      τ.getLast? = some (Config.done s) ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (p M M₁ : Nat),
        p < m → ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run s ((I ^ I.loopK h) ^ m)) τ
            ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩ M →
        IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
        recycleCount b τ (M - 1)
          = recycleCount b t₁ (M₁ - 1) + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
  set A := I ^ I.loopK h with hA
  -- the no-full premise of `s` (configured ⟹ strictly under-full), from `hwf_s` and `hfull`
  have hnofull : ∀ b I' A' n, s.B b = ⟨I', A', some n⟩ → I'.length + A' < (n : Nat) := by
    intro b I' A' n hb
    have hle := (hwf_s.1 b I' A' n hb).1
    have hne : I'.length + A' ≠ (n : Nat) := by
      have hf := hfull b; rw [hb] at hf
      simp only [BarrierState.isFull] at hf
      intro heq; rw [heq] at hf; simp at hf
    omega
  -- `t₁` is long enough that its `dropLast` is nonempty (it starts `run`, ends `done`)
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead1 : t₁.head? = some (Config.run s A) := ht₁.1.2
  have hne : t₁ ≠ [] := fun hd => by rw [hd] at hhead1; simp at hhead1
  obtain ⟨a, l, htl⟩ := List.exists_cons_of_ne_nil hne
  have hlne : l ≠ [] := by
    rintro rfl
    rw [htl] at hhead1 ht₁L
    simp only [List.head?_cons, Option.some.injEq] at hhead1
    simp only [List.getLast?_singleton, Option.some.injEq] at ht₁L
    rw [hhead1] at ht₁L; exact absurd ht₁L (by simp)
  have h2 : 2 ≤ t₁.length := by
    rw [htl, List.length_cons]; have := List.length_pos_of_ne_nil hlne; omega
  -- the penultimate config of `t₁` (index `t₁.length - 2`) has all programs empty
  have hpen : ∀ (i : ThreadId) (C : Config), t₁[t₁.length - 2]? = some C → C.progOf i = [] := by
    intro i C hC
    have hdrop : t₁.dropLast ≠ [] := by
      intro hd; have : t₁.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
      omega
    have hgl : t₁.dropLast.getLast? = some C := by
      rw [List.getLast?_eq_getElem?, List.length_dropLast, List.getElem?_dropLast,
        if_pos (by omega), show t₁.length - 1 - 1 = t₁.length - 2 from by omega]
      exact hC
    exact progOf_penultimate_done hchain1 ht₁L hgl i
  induction m with
  | zero =>
    obtain ⟨τ, hτ, hτL⟩ := pow_replay_trace_from A hnofull ht₁ ht₁L 0
    exact ⟨τ, hτ, hτL, fun t j c b par p M M₁ hp _ _ _ _ => absurd hp (by omega)⟩
  | succ m ih =>
    obtain ⟨τm, hτm, hτmL, hrecm⟩ := ih
    obtain ⟨hglue, hgluelast, hsnd⟩ := glue_trace (A.pow_ids m).symm ht₁ ht₁L hτm
    set τ := t₁.dropLast.map (Config.seqLift A (A ^ m)) ++ τm.tail with hτdef
    have hτsucc : IsSuccessfulTraceFrom (Config.run s (A ^ (m + 1))) τ := by
      rw [CTA.pow_succ]; exact hglue
    have hτsuccL : τ.getLast? = some (Config.done s) := by
      rw [hτdef, hgluelast, hτmL]
    refine ⟨τ, hτsucc, hτsuccL, ?_⟩
    intro t j c b par p M M₁ hp hcj hbr htM htM₁
    obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
    have hbA : b ∈ A.barrierSet := by
      rw [CTA.barrierSet, Finset.mem_biUnion]
      exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
        (List.mem_filterMap.mpr ⟨c, List.mem_of_getElem? hcj, Cmd.barrier?_of_barrierRef hbr⟩)⟩
    -- the front batch's full recycle count of `b` is exactly `δ`
    have hfrontΔ : recycleCount b t₁ (t₁.length - 2)
        = I.loopK h * I.arrivers b / I.arrivalCount h b := by
      rw [← recycleCount_done_last hchain1 ht₁L h2]
      exact Config.WellSynchronized.pow_barriers_advance_count h hwf_s (hfull b) ht₁ hbA
    have hmLen : ((A ^ m).prog t).length = m * (A.prog t).length := CTA.pow_prog_length A m t
    have hsuccLen : ((A ^ (m + 1)).prog t).length = (m + 1) * (A.prog t).length :=
      CTA.pow_prog_length A (m + 1) t
    have hprogeq : (A ^ (m + 1)).prog t = A.prog t ++ (A ^ m).prog t := CTA.pow_succ_prog A m t
    -- the front of `τ` mirrors `t₁` lifted: recycle counts agree on the front portion
    have hfrontrec : ∀ M, M ≤ t₁.length - 2 → recycleCount b τ M = recycleCount b t₁ M := by
      intro M hM
      have hfst : ∀ r, r ≤ M → τ[r]? = (t₁.map (Config.seqLift A (A ^ m)))[r]? := by
        intro r hr
        rw [hτdef, List.getElem?_append_left
            (by rw [List.length_map, List.length_dropLast]; omega),
          List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
      rw [recycleCount_eq_of_getElem?_eq b (fun r hr => hfst r hr),
        recycleCount_map_seqLift A (A ^ m) b t₁ M]
    -- transport a front instruction time of `t₁` into `τ` (unshifted)
    have frontTransport : ∀ (q M' : Nat), q < (A.prog t).length →
        IsTimeOf (Config.run s A) t₁ ⟨t, q⟩ M' →
        IsTimeOf (Config.run s (A ^ (m + 1))) τ ⟨t, q⟩ M' ∧ M' ≤ t₁.length - 2 := by
      intro q M' hq hT
      obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hT
      have hj'1 : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
      -- the executing config `D` has nonempty program for `t`, so it is not the penultimate one
      have hDne : D.progOf t ≠ [] := by
        rw [hDprog]
        change (A.prog t).drop q ≠ []
        rw [Ne, List.drop_eq_nil_iff]; omega
      have hjlt : j' < t₁.length - 2 := by
        by_contra hcon
        have hje : j' = t₁.length - 2 := by omega
        exact hDne (hpen t D (by rw [← hje]; exact hDj))
      have hMb : M' ≤ t₁.length - 2 := by omega
      have hfst : ∀ r, r ≤ t₁.length - 2 → τ[r]? = (t₁.map (Config.seqLift A (A ^ m)))[r]? := by
        intro r hr
        rw [hτdef, List.getElem?_append_left
            (by rw [List.length_map, List.length_dropLast]; omega),
          List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
      refine ⟨⟨hτsucc.1, ?_, j', Config.seqLift A (A ^ m) D, Config.seqLift A (A ^ m) D',
        hMeq, ?_, ?_, ?_, ?_⟩, hMb⟩
      · change q < ((A ^ (m + 1)).prog t).length
        rw [hsuccLen]
        calc q < (A.prog t).length := hq
          _ ≤ (m + 1) * (A.prog t).length := Nat.le_mul_of_pos_left _ (by omega)
      · rw [hfst j' (by omega), List.getElem?_map, hDj]; rfl
      · rw [hfst (j' + 1) (by omega), List.getElem?_map, hDj1]; rfl
      · change (Config.seqLift A (A ^ m) D).progOf t = ((A ^ (m + 1)).prog t).drop q
        rw [Config.seqLift_progOf, hDprog]
        change (A.prog t).drop q ++ (A ^ m).prog t = ((A ^ (m + 1)).prog t).drop q
        rw [hprogeq, List.drop_append_of_le_length (by omega)]
      · change (Config.seqLift A (A ^ m) D').progOf t = ((A ^ (m + 1)).prog t).drop (q + 1)
        rw [Config.seqLift_progOf, hD'prog]
        change (A.prog t).drop (q + 1) ++ (A ^ m).prog t = ((A ^ (m + 1)).prog t).drop (q + 1)
        rw [hprogeq, List.drop_append_of_le_length (by omega)]
    -- transport an `A ^ m` instruction time of `τm` into `τ`, shifted by the front batch
    have suffixTransport : ∀ (q M' : Nat), q < ((A ^ m).prog t).length →
        IsTimeOf (Config.run s (A ^ m)) τm ⟨t, q⟩ M' →
        IsTimeOf (Config.run s (A ^ (m + 1))) τ
          ⟨t, (A.prog t).length + q⟩ ((t₁.length - 2) + M') := by
      intro q M' hq hT'
      obtain ⟨-, -, j', D, D', hM'eq, hDj, hDj1, hDprog, hD'prog⟩ := hT'
      refine ⟨hτsucc.1, ?_, (t₁.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
      · change (A.prog t).length + q < ((A ^ (m + 1)).prog t).length
        rw [hsuccLen]
        have hm1 : (m + 1) * (A.prog t).length = (A.prog t).length + m * (A.prog t).length := by
          rw [Nat.succ_mul]; omega
        rw [hm1]; omega
      · exact (hsnd j').trans hDj
      · rw [show (t₁.length - 2) + j' + 1 = (t₁.length - 2) + (j' + 1) from by omega]
        exact (hsnd (j' + 1)).trans hDj1
      · change D.progOf t = ((A ^ (m + 1)).prog t).drop ((A.prog t).length + q)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
          List.nil_append, Nat.add_sub_cancel_left]
        exact hDprog
      · change D'.progOf t = ((A ^ (m + 1)).prog t).drop ((A.prog t).length + q + 1)
        rw [hprogeq, List.drop_append,
          List.drop_eq_nil_of_le (show (A.prog t).length ≤ (A.prog t).length + q + 1 by omega),
          List.nil_append, show (A.prog t).length + q + 1 - (A.prog t).length = q + 1 from by omega]
        exact hD'prog
    -- `M₁ - 1 ≤ t₁.length - 2` (the `t₁` copy executes strictly before the terminal `done`)
    have hM₁le : M₁ - 1 ≤ t₁.length - 2 := by
      obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, -, -⟩ := htM₁
      have hj'1 : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
      omega
    rcases Nat.eq_zero_or_pos p with hp0 | hppos
    · -- batch 0: the copy is the front copy of `⟨t, j⟩`; `M = M₁` and the count is the front count
      subst hp0
      rw [Nat.zero_mul, Nat.zero_add] at htM
      have hMeq : M = M₁ := IsTimeOf.unique htM (frontTransport j M₁ hjL htM₁).1
      rw [hMeq, Nat.zero_mul, Nat.add_zero, hfrontrec (M₁ - 1) hM₁le]
    · -- batch `p ≥ 1`: the copy is the batch-`p-1` copy of `τm` shifted by the front batch
      -- its time in `τm`
      obtain ⟨sdm, hmlast⟩ := hτm.2
      have hpidx : p * (A.prog t).length + j
          = (A.prog t).length + ((p - 1) * (A.prog t).length + j) := by
        conv_lhs => rw [show p = (p - 1) + 1 from by omega, Nat.succ_mul]
        omega
      have hppm1lt : (p - 1) * (A.prog t).length + j < ((A ^ m).prog t).length := by
        rw [hmLen]
        have hle : (p - 1) * (A.prog t).length ≤ (m - 1) * (A.prog t).length :=
          Nat.mul_le_mul_right _ (by omega)
        have hmm : m * (A.prog t).length = (m - 1) * (A.prog t).length + (A.prog t).length := by
          conv_lhs => rw [show m = (m - 1) + 1 from by omega, Nat.succ_mul]
        omega
      obtain ⟨Mm, hMm⟩ := exists_time_of_ends_done hτm.1 hmlast
        (η := ⟨t, (p - 1) * (A.prog t).length + j⟩)
        (by change (p - 1) * (A.prog t).length + j < ((A ^ m).prog t).length; exact hppm1lt)
      -- transport that time up to `τ`; it matches the given `M`
      have htrM := suffixTransport ((p - 1) * (A.prog t).length + j) Mm hppm1lt hMm
      rw [← hpidx] at htrM
      have hMval : M = (t₁.length - 2) + Mm := IsTimeOf.unique htM htrM
      -- positivity of `Mm`
      have hMmpos : 1 ≤ Mm := by obtain ⟨_, _, _, he, _⟩ := hMm.2.2; omega
      -- the recursive offset for batch `p - 1` in `τm`
      have hIH := hrecm t j c b par (p - 1) Mm M₁ (by omega) hcj hbr hMm htM₁
      -- split the count of `τ` across the front boundary; the front contributes `δ`
      have hsplit : recycleCount b τ (M - 1)
          = recycleCount b τ (t₁.length - 2) + recycleCount b τm (Mm - 1) := by
        rw [hMval, show (t₁.length - 2) + Mm - 1 = (t₁.length - 2) + (Mm - 1) from by omega,
          recycleCount_suffix b hsnd]
      rw [hsplit, hfrontrec (t₁.length - 2) (le_refl _), hfrontΔ, hIH]
      have hpδ : (p - 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b)
          = p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
        conv_rhs => rw [show p = (p - 1) + 1 from by omega, Nat.succ_mul]
      omega

/-- **The full recycle count of any complete `m`-batch run is `m · δ_b`.** A schedule-invariant
companion to `pow_barriers_advance_count`: for *any* successful trace `τ` of `(I ^ k) ^ m` from
`State.initial` ending in `done State.initial`, every barrier `b` referenced by `I ^ k` is
recycled exactly `m · δ_b` times over `τ`. Proved by the same `barrierPotential`-conservation
accounting as the single-batch case, using `(A ^ m).arrivers b = m · A.arrivers b`. -/
theorem pow_full_recycleCount {I : CTA} (h : I.ConsistentArrivalCounts) {s : State} {m : Nat}
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h) ^ m)) τ)
    (hτL : τ.getLast? = some (Config.done s)) (hBI_s : s.BlockInv)
    {b : Barrier} (hb : b ∈ (I ^ I.loopK h).barrierSet)
    (hcount_s : ∀ n', (s.B b).count = some n' → (n' : Nat) = I.arrivalCount h b) :
    recycleCount b τ (τ.length - 1) = m * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
  set A := I ^ I.loopK h with hA
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, s_d, hlast⟩ := hτ
  have hsd : s_d = s := by rw [hlast] at hτL; simpa using hτL
  subst s_d
  set nb := I.arrivalCount h b with hnb
  -- `b ∈ I.barriers`
  have hbI : b ∈ I.barriers := by
    rw [CTA.barrierSet, Finset.mem_biUnion] at hb
    obtain ⟨i, hi, hbi'⟩ := hb
    rw [List.mem_toFinset, List.mem_filterMap] at hbi'
    obtain ⟨c, hc, hcb⟩ := hbi'
    have hcI : c ∈ I.prog i := I.mem_pow_prog hc
    have hi' : i ∈ I.ids := by rw [← CTA.pow_ids I (I.loopK h)]; exact hi
    obtain ⟨n, hbref⟩ : ∃ n, Cmd.barrierRef c = some (b, n) := by
      cases c with
      | read g => simp [Cmd.barrier?] at hcb
      | write g => simp [Cmd.barrier?] at hcb
      | arrive b' n =>
        simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
      | sync b' n =>
        simp only [Cmd.barrier?, Option.some.injEq] at hcb; subst hcb; exact ⟨n, rfl⟩
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi', List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, n), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  have hnbpos : 0 < nb := I.arrivalCount_pos h hbI
  -- `nb ∣ A.arrivers b`, so `nb ∣ (A ^ m).arrivers b = m * A.arrivers b`
  have hdvdA : nb ∣ A.arrivers b := by
    rw [hA]; exact I.arrivalCount_dvd_pow_arrivers h hbI
  obtain ⟨qA, hqA⟩ := hdvdA
  have hAarr : (A ^ m).arrivers b = m * A.arrivers b := CTA.arrivers_pow A b m
  -- err-freeness, command-consistency, the chain hypotheses
  have hno_err : ∀ C ∈ τ, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : τ ≠ [] := by rintro rfl; simp at hhead
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at hlast
      rw [hlast, hCerr] at hCl; exact Config.noConfusion hCl
  have hcmd_all : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ p : ℕ+, Cmd.barrierRef c = some (b, p) →
      (p : Nat) = nb := by
    intro C hC i c hc p hbref
    have hc0 : c ∈ (Config.run s (A ^ m)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (A ^ m).prog i := by simpa [Config.progOf] using hc0
    have hcA : c ∈ A.prog i := A.mem_pow_prog hc1
    have hcI : c ∈ I.prog i := by rw [hA] at hcA; exact I.mem_pow_prog hcA
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    rw [hnb]; exact (h.choose_spec i hi c hcI b p hbref).symm
  have hbcount0 : ∀ n', (Config.run s (A ^ m)).bcount b = some n' → (n' : Nat) = nb := by
    intro n' hn'
    simp only [Config.bcount] at hn'
    rw [hnb]; exact hcount_s n' hn'
  have hcount_all := bcount_chain hchain hhead
    (by intro n' hn'; exact hbcount0 n' (by simpa only [Config.bcount] using hn')) hcmd_all
  have hBI_all := blockInv_chain hchain hhead
    (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'
        exact hBI_s)
  -- conservation with recycles
  have hcons := barrierPotential_with_recycles (b := b) (nb := nb) hchain hhead hlast hno_err
    hcount_all hBI_all
  have hC₀pot : (Config.run s (A ^ m)).barrierPotential b
      = (s.B b).arrived + (A ^ m).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s).barrierPotential b = (s.B b).arrived := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hC₀pot, hdonepot] at hcons
  -- the start's own arrived count cancels (`s` is restored), leaving `m · A.arrivers b / nb`
  rw [hAarr, hqA] at hcons
  set R := recycleCount b τ (τ.length - 1) with hRdef
  have hcancel : m * (nb * qA) = nb * R := Nat.add_left_cancel hcons
  have hqR : R = m * qA := by
    have h2 : nb * (m * qA) = nb * R := by rw [Nat.mul_left_comm]; exact hcancel
    exact (Nat.eq_of_mul_eq_mul_left hnbpos h2).symm
  -- relate `qA` to `δ`: `A.arrivers b = nb * qA` and `δ = loopK * arrivers / nb`
  have hδ : I.loopK h * I.arrivers b / I.arrivalCount h b = qA := by
    have hAa : A.arrivers b = I.loopK h * I.arrivers b := by rw [hA]; exact I.arrivers_pow b _
    rw [← hnb, ← hAa, hqA, Nat.mul_div_cancel_left _ hnbpos]
  rw [hδ, ← hqR, hRdef]

/-- **Unconfigured stays unconfigured.** If `b` is unconfigured at `C` and no command of `C`'s
remaining program references `b`, then `b` is unconfigured at `C'` — the only ways to configure
`b` are `arrive b`/`sync b`, which need a `b`-command in the program. -/
theorem bstate_unconfigured_step {b : Barrier} {C C' : Config} (hstep : CTAStep C C')
    (hC : ∀ s, C.state? = some s → s.B b = BarrierState.unconfigured)
    (hcmd : ∀ i c, c ∈ C.progOf i → ∀ p : ℕ+, Cmd.barrierRef c ≠ some (b, p)) :
    ∀ s', C'.state? = some s' → s'.B b = BarrierState.unconfigured := by
  intro s' hs'
  cases hstep with
  | @interleave s s'' T i P' hi hbar hth =>
    have hCb : s.B b = BarrierState.unconfigured := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact hCb
    | write_noop => exact hCb
    | arrive_configure he hb0 =>
      rename_i b₀ n
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.arrive b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        exact absurd rfl (hcmd i (Cmd.arrive b n) hmem n)
      · simp only [Function.update_of_ne hbb]; exact hCb
    | arrive_register he hb0 hpos hlt =>
      rename_i b₀ n I A
      by_cases hbb : b = b₀
      · subst hbb; rw [hCb] at hb0; simp [BarrierState.unconfigured] at hb0
      · simp only [Function.update_of_ne hbb]; exact hCb
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb
        have hmem : Cmd.sync b n ∈ (Config.run s T).progOf i := by
          simp only [Config.progOf]; rw [hpi]; exact List.mem_cons_self
        exact absurd rfl (hcmd i (Cmd.sync b n) hmem n)
      · simp only [Function.update_of_ne hbb]; exact hCb
    | sync_block he hb0 hpos hlt =>
      rename_i b₀ n c I A
      by_cases hbb : b = b₀
      · subst hbb; rw [hCb] at hb0; simp [BarrierState.unconfigured] at hb0
      · simp only [Function.update_of_ne hbb]; exact hCb
  | @recycle s T b₀ I A n hb hfullr hpark =>
    have hCb : s.B b = BarrierState.unconfigured := hC s rfl
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    by_cases hbb : b = b₀
    · subst hbb; rw [hCb] at hb; simp [BarrierState.unconfigured] at hb
    · simp only [Function.update_of_ne hbb]; exact hCb
  | @done s T hdone hnofull =>
    simp only [Config.state?, Option.some.injEq] at hs'
    subst hs'
    exact hC s rfl
  | @error s T i P' hth => simp [Config.state?] at hs'

/-- Iterating `bstate_unconfigured_step` along a chain: an unconfigured `b` at the head stays
unconfigured at every configuration, given no configuration's program references `b`. -/
theorem bstate_unconfigured_chain {b : Barrier} :
    ∀ {τ : List Config} {C₀ : Config}, List.IsChain CTAStep τ → τ.head? = some C₀ →
      (∀ s', C₀.state? = some s' → s'.B b = BarrierState.unconfigured) →
      (∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ p : ℕ+, Cmd.barrierRef c ≠ some (b, p)) →
      ∀ C ∈ τ, ∀ s', C.state? = some s' → s'.B b = BarrierState.unconfigured := by
  intro τ
  induction τ with
  | nil => intro C₀ _ hhead; simp at hhead
  | cons a rest ih =>
    intro C₀ hchain hhead hC₀ hcmd C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hC₀
    | cons b₁ rest' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hstep, hchain'⟩ := hchain
      have hb1 : ∀ s', b₁.state? = some s' → s'.B b = BarrierState.unconfigured :=
        bstate_unconfigured_step hstep hC₀ (hcmd a (by simp))
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hC₀
      · exact ih hchain' rfl hb1 (fun C hC'' => hcmd C (List.mem_cons_of_mem _ hC'')) C hC'

/-- **An `A`-unreferenced barrier is recycled zero times in a complete `m`-batch run.** If `b`
is not in `I.barriers` then no command of `A^m = (I^k)^m` references it, so it never becomes
full and is never recycled; the total recycle count is `0`. The complement of
`pow_full_recycleCount` (where then `δ_b = 0` as well, since `arrivers b = 0`). -/
theorem pow_full_recycleCount_zero {I : CTA} (h : I.ConsistentArrivalCounts) {s : State} {m : Nat}
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h) ^ m)) τ)
    (_hτL : τ.getLast? = some (Config.done s)) (hfull : ∀ b, (s.B b).isFull = false)
    {b : Barrier} (hbI : b ∉ I.barriers) :
    recycleCount b τ (τ.length - 1) = 0 := by
  set A := I ^ I.loopK h with hA
  obtain ⟨⟨⟨hchain, _hends⟩, hhead⟩, _s_d, _hlast⟩ := hτ
  -- no command of `A^m` references `b` (else `b ∈ I.barriers`)
  have hnoref : ∀ C ∈ τ, ∀ i c, c ∈ C.progOf i → ∀ p : ℕ+, Cmd.barrierRef c ≠ some (b, p) := by
    intro C hC i c hc p hbref
    have hc0 : c ∈ (Config.run s (A ^ m)).progOf i :=
      (progOf_suffix_head hchain hhead C hC i).subset hc
    have hc1 : c ∈ (A ^ m).prog i := by simpa [Config.progOf] using hc0
    have hcA : c ∈ A.prog i := A.mem_pow_prog hc1
    have hcI : c ∈ I.prog i := by rw [hA] at hcA; exact I.mem_pow_prog hcA
    have hi : i ∈ I.ids := by
      by_contra hni; rw [I.nil_outside_ids i hni] at hcI; simp at hcI
    apply hbI
    rw [CTA.barriers, Finset.mem_biUnion]
    exact ⟨i, hi, List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(b, p), List.mem_filterMap.mpr ⟨c, hcI, hbref⟩, rfl⟩)⟩
  -- `b`'s barrier state is frozen at `s.B b` all along `τ`
  have hfrozen := bstate_unref_chain (hfull b) hchain hhead
    (by intro s' hs'; simp only [Config.state?, Option.some.injEq] at hs'; subst hs'; rfl)
    hnoref
  -- a frozen, non-full barrier is never recycled (its source can't be full and unconfigured)
  have hnostep : ∀ C ∈ τ, ∀ C', stepRecyclesBarrier b C C' = false := by
    intro C hC C'
    rcases hCs : C.state? with _ | sC
    · simp [stepRecyclesBarrier, hCs]
    · have hbC : sC.B b = s.B b := hfrozen C hC sC hCs
      rcases hC's : C'.state? with _ | sC'
      · simp [stepRecyclesBarrier, hCs, hC's]
      · simp [stepRecyclesBarrier, hCs, hC's, hbC, hfull b]
  unfold recycleCount
  rw [List.countP_eq_zero]
  intro j _
  rcases hCj : τ[j]? with _ | C
  · simp
  · rcases hCj1 : τ[j + 1]? with _ | C'
    · simp
    · simp [hnostep C (List.mem_of_getElem? hCj) C']

/-- **A single batch's `sync` generation is at most `δ`.** In one restoring batch `t₁` of
`A = I ^ k`, the recycle count of `b` strictly before a `sync`-on-`b`'s execution is `< δ_b`:
the sync's own recycle (the step that unblocks it, `sync_time_recycles`) is one of the batch's
`δ_b` recycles (`pow_barriers_advance_count`) and occurs *at* the sync's step, not before it. -/
theorem sync_recycleCount_lt_batch {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s))
    {t : ThreadId} {j : Nat} {b : Barrier} {par : ℕ+} {M₁ : Nat}
    (hcj : ((I ^ I.loopK h).prog t)[j]? = some (Cmd.sync b par))
    (hM₁ : IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁)
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false) :
    recycleCount b t₁ (M₁ - 1) + 1 ≤ I.loopK h * I.arrivers b / I.arrivalCount h b := by
  set A := I ^ I.loopK h with hA
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hbA : b ∈ A.barrierSet := by
    rw [CTA.barrierSet, Finset.mem_biUnion]
    exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
      (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hcj, rfl⟩)⟩
  -- `t₁` has length ≥ 2
  have h2 : 2 ≤ t₁.length := by
    obtain ⟨j', C0, C0', hMeq, hC0, hC0', hC0eq, hC0'eq⟩ := hM₁.2.2
    have := (List.getElem?_eq_some_iff.mp hC0').1; omega
  -- one batch recycles `b` exactly `δ` times
  have hΔ : recycleCount b t₁ (t₁.length - 2) = I.loopK h * I.arrivers b / I.arrivalCount h b := by
    rw [← recycleCount_done_last hchain1 ht₁L h2]
    exact Config.WellSynchronized.pow_barriers_advance_count h hwf_s (hfull b) ht₁ hbA
  -- the sync's step `M₁ - 1 → M₁` recycles `b`
  have hcmdC : (ProgPoint.mk t j).cmd (Config.run s A) = some (Cmd.sync b par) := by
    change (A.prog t)[j]? = some (Cmd.sync b par); exact hcj
  obtain ⟨C, C', hCm1, hCm, hrec⟩ := sync_time_recycles hM₁ hcmdC
  have hM1pos : 1 ≤ M₁ := by
    obtain ⟨j', C0, C0', hMeq, -, -, -, -⟩ := hM₁.2.2; omega
  -- the recycle target `C'` is at index `M₁`, so `M₁ < t₁.length`
  have hM1lt : M₁ < t₁.length := (List.getElem?_eq_some_iff.mp hCm).1
  -- the step is a genuine recycle (run → run), so `M₁` is not the terminal `done` index
  have hM1ne : M₁ ≠ t₁.length - 1 := by
    intro he
    -- then `C' = done s`, but a recycle step cannot land in `done`
    have hCmdone : t₁[M₁]? = some (Config.done s) := by
      rw [he, ← List.getLast?_eq_getElem?]; exact ht₁L
    have hC'done : C' = Config.done s := by
      rw [hCm, Option.some.injEq] at hCmdone; exact hCmdone
    rw [hC'done] at hrec
    have hstep : CTAStep C (Config.done s) :=
      chain_step hchain1 hCm1 (by rw [show M₁ - 1 + 1 = M₁ from by omega, hCm, hC'done])
    rw [stepRecyclesBarrier_to_done b C s hstep] at hrec
    exact absurd hrec (by simp)
  have hM1le : M₁ ≤ t₁.length - 2 := by omega
  -- `recycleCount(M₁) = recycleCount(M₁ - 1) + 1`, and is `≤ δ` by monotonicity
  have hsucc : recycleCount b t₁ M₁ = recycleCount b t₁ (M₁ - 1) + 1 := by
    have := recycleCount_succ_of_recycle b t₁ (p := M₁ - 1) hCm1
      (by rw [show M₁ - 1 + 1 = M₁ from by omega]; exact hCm) hrec
    rwa [show M₁ - 1 + 1 = M₁ from by omega] at this
  have hmono : recycleCount b t₁ M₁ ≤ recycleCount b t₁ (t₁.length - 2) :=
    recycleCount_mono b t₁ hM1le
  omega

/-- **A single batch's barrier-op generation is at most `δ + 1`.** Companion to
`sync_recycleCount_lt_batch` valid for *any* barrier op (arrive or sync), with a non-strict
bound: in one restoring batch `t₁`, the recycle count of `b` strictly before any barrier-op
on `b` is `≤ δ_b` (it lies within the batch, whose total recycle count is exactly `δ_b`). -/
theorem barrierOp_recycleCount_le_batch {I : CTA} (h : I.ConsistentArrivalCounts)
    {s : State} {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s))
    {t : ThreadId} {j : Nat} {c : Cmd} {b : Barrier} {par : ℕ+} {M₁ : Nat}
    (hcj : ((I ^ I.loopK h).prog t)[j]? = some c) (hbr : Cmd.barrierRef c = some (b, par))
    (hM₁ : IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁)
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false) :
    recycleCount b t₁ (M₁ - 1) ≤ I.loopK h * I.arrivers b / I.arrivalCount h b := by
  set A := I ^ I.loopK h with hA
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hbA : b ∈ A.barrierSet := by
    rw [CTA.barrierSet, Finset.mem_biUnion]
    exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
      (List.mem_filterMap.mpr ⟨c, List.mem_of_getElem? hcj, Cmd.barrier?_of_barrierRef hbr⟩)⟩
  -- `M₁ < t₁.length` (the point executes within the trace)
  obtain ⟨-, -, jj, C0, C0', hMeq, -, hC0', -, -⟩ := hM₁
  have hM1lt : M₁ < t₁.length := by
    have := (List.getElem?_eq_some_iff.mp hC0').1; omega
  -- `t₁` has length ≥ 2
  have h2 : 2 ≤ t₁.length := by omega
  -- one batch recycles `b` exactly `δ` times
  have hΔ : recycleCount b t₁ (t₁.length - 2) = I.loopK h * I.arrivers b / I.arrivalCount h b := by
    rw [← recycleCount_done_last hchain1 ht₁L h2]
    exact Config.WellSynchronized.pow_barriers_advance_count h hwf_s (hfull b) ht₁ hbA
  have hM1le : M₁ - 1 ≤ t₁.length - 2 := by omega
  have hmono : recycleCount b t₁ (M₁ - 1) ≤ recycleCount b t₁ (t₁.length - 2) :=
    recycleCount_mono b t₁ hM1le
  omega

/-- **A single batch's arrive generation is strictly bounded by `δ`.** For arrive ops on `b`, the
recycle count strictly before execution is `< δ_b`: if all `δ` recyclings had already occurred,
the arrival potential would be 0, contradicting the presence of an unexecuted arrive command.
Uses `barrierPotential_conservation` on the suffix after the arrive's time. -/
theorem arrive_recycleCount_lt_batch {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s))
    {t : ThreadId} {j : Nat} {b : Barrier} {par : ℕ+} {M₁ : Nat}
    (hcj : ((I ^ I.loopK h).prog t)[j]? = some (Cmd.arrive b par))
    (hM₁ : IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁)
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false)
    (harr0 : (s.B b).arrived = 0) :
    recycleCount b t₁ (M₁ - 1) + 1 ≤ I.loopK h * I.arrivers b / I.arrivalCount h b := by
  set A := I ^ I.loopK h with hA
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hle : recycleCount b t₁ (M₁ - 1) ≤ I.loopK h * I.arrivers b / I.arrivalCount h b :=
    barrierOp_recycleCount_le_batch h ht₁ ht₁L hcj rfl hM₁ hwf_s hfull
  obtain ⟨-, -, jj, CM1, CM1', hMeq, hCM1, hCM1', hprogM1, -⟩ := hM₁
  have hM1lt : M₁ < t₁.length := by have := (List.getElem?_eq_some_iff.mp hCM1').1; omega
  have h2 : 2 ≤ t₁.length := by omega
  have hδ_eq : recycleCount b t₁ (t₁.length - 2)
      = I.loopK h * I.arrivers b / I.arrivalCount h b := by
    have hbA : b ∈ A.barrierSet := by
      rw [CTA.barrierSet, Finset.mem_biUnion]
      exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
        (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hcj, rfl⟩)⟩
    rw [← recycleCount_done_last hchain1 ht₁L h2]
    exact Config.WellSynchronized.pow_barriers_advance_count h hwf_s (hfull b) ht₁ hbA
  by_contra hcon
  push Not at hcon
  set δ := I.loopK h * I.arrivers b / I.arrivalCount h b
  have heq : recycleCount b t₁ (M₁ - 1) = δ := by omega
  -- No recyclings from step M₁-1 onward: any such recycling would push the count past δ
  have hnostep : ∀ r C C', t₁[M₁ - 1 + r]? = some C → t₁[M₁ - 1 + r + 1]? = some C' →
      stepRecyclesBarrier b C C' = false := by
    intro r C C' hCr hCr1
    by_contra hnr
    rw [Bool.not_eq_false] at hnr
    have hsucc := recycleCount_succ_of_recycle b t₁ hCr hCr1 hnr
    have hm1 : recycleCount b t₁ (M₁ - 1) ≤ recycleCount b t₁ (M₁ - 1 + r) :=
      recycleCount_mono b t₁ (Nat.le_add_right _ _)
    have hm2 : recycleCount b t₁ (M₁ - 1 + r + 1) ≤ δ :=
      calc recycleCount b t₁ (M₁ - 1 + r + 1)
          ≤ recycleCount b t₁ (t₁.length - 1) :=
            recycleCount_mono b t₁ (by have := (List.getElem?_eq_some_iff.mp hCr1).1; omega)
        _ = recycleCount b t₁ (t₁.length - 2) := recycleCount_done_last hchain1 ht₁L h2
        _ = δ := hδ_eq
    omega
  -- No errors in t₁ (successful trace ending in done)
  have hno_err : ∀ C ∈ t₁, ∀ T, C ≠ Config.err T := by
    intro C hC T hCerr
    have hτne : t₁ ≠ [] := by rintro rfl; exact absurd ht₁.1.2 (by simp)
    rw [← List.dropLast_append_getLast hτne, List.mem_append, List.mem_singleton] at hC
    rcases hC with hCd | hCl
    · obtain ⟨s', T', hrun⟩ := mem_dropLast_isRun hchain1 C hCd
      rw [hCerr] at hrun; exact Config.noConfusion hrun
    · rw [List.getLast?_eq_some_getLast hτne, Option.some.injEq] at ht₁L
      rw [ht₁L, hCerr] at hCl; exact Config.noConfusion hCl
  -- Potential conservation on suffix σ = t₁.drop (M₁ - 1)
  set σ := t₁.drop (M₁ - 1) with hσdef
  have hσchain : List.IsChain CTAStep σ := hchain1.drop (M₁ - 1)
  have hσhead : σ.head? = some CM1 := by
    rw [hσdef, List.head?_drop, show M₁ - 1 = jj from by omega]
    exact hCM1
  have hσlast : σ.getLast? = some (Config.done s) := by
    rw [hσdef, List.getLast?_drop, if_neg (by have := (List.getElem?_eq_some_iff.mp hCM1).1; omega)]
    exact ht₁L
  have hσ_norec : ∀ r C C', σ[r]? = some C → σ[r + 1]? = some C' →
      stepRecyclesBarrier b C C' = false := by
    intro r C C' hCr hCr1
    simp only [hσdef, List.getElem?_drop] at hCr hCr1
    exact hnostep r C C' hCr
      (by rwa [show M₁ - 1 + (r + 1) = M₁ - 1 + r + 1 from by omega] at hCr1)
  have hcons := barrierPotential_conservation b hσchain hσhead hσlast
    (fun C hC T hCerr => hno_err C (List.mem_of_mem_drop hC) T hCerr) hσ_norec
  -- Φ(done s) = 0 (harr0 and no remaining commands)
  have hpot_done : (Config.done s).barrierPotential b = 0 := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, harr0]
  -- CM1 is a run config (progOf t is non-empty; done has empty progOf)
  obtain ⟨sM, TM, hCM1run⟩ : ∃ sM TM, CM1 = Config.run sM TM := by
    cases CM1 with
    | run sM TM => exact ⟨sM, TM, rfl⟩
    | done sM =>
      simp only [Config.progOf] at hprogM1
      have : (A.prog t).drop j = [] := hprogM1.symm
      rw [List.drop_eq_nil_iff] at this; omega
    | err TM => exact absurd rfl (hno_err (Config.err TM) (List.mem_of_getElem? hCM1) TM)
  -- TM.ids = A.ids; t ∈ TM.ids; TM.prog t = (A.prog t).drop j
  have hTMids : TM.ids = A.ids :=
    run_ids_chain hchain1 ht₁.1.2 (fun s₀ T₀ hC₀ => (congr_arg CTA.ids (Config.run.inj hC₀).2).symm)
      CM1 (List.mem_of_getElem? hCM1) sM TM hCM1run
  have htIds : t ∈ TM.ids := hTMids ▸ mem_ids_of_idx_lt A hjL
  have hTMprog : TM.prog t = (A.prog t).drop j := by
    have h := hprogM1; rw [hCM1run] at h; simpa [Config.progOf] using h
  -- barrierProgCount b CM1 ≥ 1: arrive b par is at the head of TM.prog t
  have hbpc : 1 ≤ CM1.barrierProgCount b := by
    rw [hCM1run, Config.barrierProgCount]
    refine Nat.le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) htIds)
    rw [hTMprog]
    have hne : (A.prog t).drop j ≠ [] := by
      rw [List.ne_nil_iff_length_pos, List.length_drop]; omega
    obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil hne
    have hhd : hd = Cmd.arrive b par := by
      have hh : ((A.prog t).drop j).head? = some hd := by rw [heq, List.head?_cons]
      rw [List.head?_drop] at hh; exact Option.some.inj (hh.symm.trans hcj)
    subst hhd
    rw [heq,
        List.filterMap_cons_some (show Cmd.barrierRef (Cmd.arrive b par) = some (b, par) from rfl),
        List.countP_cons]
    simp
  -- Φ(CM1) ≥ 1 (potential = arrivedLen + barrierProgCount)
  have hpot_pos : 1 ≤ CM1.barrierPotential b := by
    simp only [Config.barrierPotential]; omega
  rw [← hcons, hpot_done] at hpot_pos
  exact absurd hpot_pos (by omega)

/-! ## Lemma 4.2 (`structure-r-across-iterations`), simple two- and three-batch cases

The document's Lemma `structure-r-across-iterations` is the happens-before (`R`) analogue of
the generation lemma `second_batch_gen_offset` (`structure-g-across-iterations`). It has two
conclusions about the observed happens-before relation `R_T` across consecutive batches of
the §1 unrolling `I ^ k`:

1. **within a batch:** HB among instructions *inside* batch `n` agrees with HB among the
   corresponding instructions inside batch `n + 1`;
2. **across batches:** an HB edge from batch `n` into batch `n + 1` agrees with the
   corresponding edge from batch `n - 1` into batch `n`.

Here we state the **simplest instances**, as `second_batch_gen_offset` does for Lemma 4.1.
A program point of a multi-batch program `…` for thread `t` indexes into the concatenation
of the per-batch programs `(I ^ k).prog t`; writing `L = ((I ^ k).prog t).length`, the copy
of body instruction `j` (`j < L`) in batch `i` (0-indexed) is `⟨t, i * L + j⟩`. -/

/- **Lemma 4.2, conclusion 1 (within-batch), `n`-batch case (last two batches).**
*Stated, not yet proved.* The `n`-batch generalization of `second_batch_hb_within`: for the
`n`-fold composition `(I ^ k) ^ n` (`n ≥ 2`), there is a successful trace `τ` whose
happens-before relation agrees *internally* between the **last two** batches. With
`L = ((I ^ k).prog _).length`, the copy of body instruction `⟨t, j⟩` (`j < L`) in batch `i`
(0-indexed) is `⟨t, i * L + j⟩`; the last batch is `i = n - 1` and the second-to-last is
`i = n - 2`. The claim: for any two body instructions `⟨t₁, j₁⟩` and `⟨t₂, j₂⟩` of `I ^ k`,
their second-to-last-batch copies are happens-before related exactly when their last-batch
copies are.

This is conclusion 1 of `structure-r-across-iterations` applied to the final batch pair;
`second_batch_hb_within` is the `n = 2` instance (`n - 2 = 0`, `n - 1 = 1`, and
`(I ^ k) ^ 2 = (I ^ k) ⨾ (I ^ k)`). The hypothesis is the `CTA.BatchesWellSynchronized`
family — every batch-prefix `(I ^ k) ^ m` (`1 ≤ m ≤ n`) is well-synchronized — generalizing
the two `WellSynchronized` assumptions of `second_batch_hb_within`. As there, the statement
is for *all* instruction pairs, not only barrier instructions (`R` orders read/write
instructions too, via program order and the sync edges). -/

/-- **Command agreement on prefix points.** A program point `η` whose index lies inside the
first `n` batches of `(A ^ (n + 1))` — i.e. `η.idx < n · |A.prog η.thread|` — reads the same
command in the `(n + 1)`-batch program as in the `n`-batch prefix `A ^ n`. The `(n + 1)`-batch
program of a thread is the `n`-batch program followed by one more batch
(`pow_succ_prog`, regrouped via `pow_add_prog`), and `η.idx` lands in the `A ^ n` prefix
(`getElem?_append_left`, since `n · |A.prog η.thread| = |(A ^ n).prog η.thread|`). -/
theorem CTA.cmdAt_pow_succ_prefix (A : CTA) {n : Nat} {η : ProgPoint}
    (hidx : η.idx < n * (A.prog η.thread).length) :
    (A ^ (n + 1)).cmdAt η = (A ^ n).cmdAt η := by
  obtain ⟨t, idx⟩ := η
  dsimp only at hidx ⊢
  have hnLen : ((A ^ n).prog t).length = n * (A.prog t).length := CTA.pow_prog_length A n t
  change ((A ^ (n + 1)).prog t)[idx]? = ((A ^ n).prog t)[idx]?
  rw [show n + 1 = n + 1 from rfl, CTA.pow_add_prog A n 1 t,
    List.getElem?_append_left (by rw [hnLen]; exact hidx)]

/-- **Command at a batch copy.** The copy of body instruction `j` (`j < |A.prog t|`) in batch
`p` (`p < m`) of `A ^ m` reads the same command as `j` in a single batch: `(A^m).cmdAt
⟨t, p·L + j⟩ = (A.prog t)[j]?`. -/
theorem CTA.cmdAt_pow_batch_copy (A : CTA) {m : Nat} {t : ThreadId} {j p : Nat}
    (hj : j < (A.prog t).length) (hp : p < m) :
    (A ^ m).cmdAt ⟨t, p * (A.prog t).length + j⟩ = (A.prog t)[j]? := by
  have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
  have hsplit : (A ^ m).prog t = (A ^ p).prog t ++ (A ^ (m - p)).prog t := by
    conv_lhs => rw [show m = p + (m - p) from by omega]
    rw [CTA.pow_add_prog]
  change ((A ^ m).prog t)[p * (A.prog t).length + j]? = (A.prog t)[j]?
  rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
    show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
    show m - p = (m - p - 1) + 1 from by omega, CTA.pow_succ_prog,
    List.getElem?_append_left hj]

/-- **The shared-trace bundle for the last-batch happens-before lemmas.** A single
successful replay trace `τ` of `(I ^ k) ^ (n + 1)` carries every fact the within-batch and
across-batch happens-before proofs need:

* the **consecutive-batch generation offset** for *every* adjacent pair of batches
  `1 ≤ p ≤ n` (the document's Lemma 3 relationship between batch `p` and `p - 1`);
* the **lower** generation bound `(L)`: a barrier op at index `idx` has generation
  `≥ (idx / L) · δ_b + 1` (the `idx / L` prior batches each contribute `δ_b ≥ 1` recycles);
* the **upper** generation bound `(U)`: a `sync` at index `idx` has generation
  `≤ (idx / L + 1) · δ_b` (it completes within its own batch).

`(L)` and `(U)` are exactly the hypotheses of `no_backward_edge`, so the bundle replaces the
`seq_no_happensBefore`-based no-backward-edge blocks with a well-synchronization-free argument
that does not assume `(I ^ k) ^ (n + 1)` itself is well-synchronized. -/
theorem CTA.WellSynchronized.last_batches_replay_bundle {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ ∧
      (∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
        1 ≤ p → p ≤ n → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, p * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (p - 1) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b) ∧
      (∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers b / I.arrivalCount h b) + 1
          ≤ pointGen ((I ^ k) ^ (n + 1)) τ η) ∧
      (∀ (η : ProgPoint) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some (Cmd.sync b par) →
        pointGen ((I ^ k) ^ (n + 1)) τ η
          ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
              * (k * I.arrivers b / I.arrivalCount h b)) ∧
      (∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        pointGen ((I ^ k) ^ (n + 1)) τ η
          ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
              * (k * I.arrivers b / I.arrivalCount h b)) ∧
      ∃ τn, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ n)) τn ∧
        (∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
          1 ≤ p → p ≤ n - 1 → ((I ^ k).prog t)[j]? = some c →
          Cmd.barrierRef c = some (b, par) →
          pointGen ((I ^ k) ^ n) τn ⟨t, p * ((I ^ k).prog t).length + j⟩
            = pointGen ((I ^ k) ^ n) τn ⟨t, (p - 1) * ((I ^ k).prog t).length + j⟩
              + k * I.arrivers b / I.arrivalCount h b) ∧
        (∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
          ((I ^ k) ^ n).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
          (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers b / I.arrivalCount h b) + 1
            ≤ pointGen ((I ^ k) ^ n) τn η) ∧
        (∀ (η : ProgPoint) (b : Barrier) (par : ℕ+),
          ((I ^ k) ^ n).cmdAt η = some (Cmd.sync b par) →
          pointGen ((I ^ k) ^ n) τn η
            ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
                * (k * I.arrivers b / I.arrivalCount h b)) ∧
        (∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
          η.idx < n * ((I ^ k).prog η.thread).length →
          ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
          pointGen ((I ^ k) ^ (n + 1)) τ η = pointGen ((I ^ k) ^ n) τn η) ∧
        (∀ a b : ProgPoint, happensBefore ((I ^ k) ^ n) τn a b →
          happensBefore ((I ^ k) ^ (n + 1)) τ a b) := by
  subst hk
  -- single-batch trace, restoring the state to `initial`
  have hWSA : (I ^ I.loopK h).WellSynchronized := by
    have := hWS 1 (le_refl 1) hn; rwa [CTA.pow_one] at this
  obtain ⟨t₁, ht₁⟩ := hWSA.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  -- the global replay trace and its recycle structure
  obtain ⟨τ, hτ, hτL, hrec⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L WF_initial (fun _ => rfl) (n + 1)
  obtain ⟨sd, hlast⟩ := hτ.2
  -- the prefix replay trace of `n` batches, built from the *same* `t₁`, with its recycle
  -- structure: this is what makes the prefix generations agree batch-for-batch with `τ`
  obtain ⟨τn, hτn, hτnL, hrecn⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L WF_initial (fun _ => rfl) n
  obtain ⟨sdn, hlastn⟩ := hτn.2
  set A := I ^ I.loopK h with hA
  -- **Per-point generation.** A barrier copy at batch `p ≤ n` position `j` (`j < L`) has
  -- generation `recycleCount b t₁ (M₁ - 1) + 1 + p·δ`, where `M₁` is `⟨t, j⟩`'s time in `t₁`.
  have keygen : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
      j < (A.prog t).length → p ≤ n →
      (A.prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
      ∃ M₁, IsTimeOf (Config.run State.initial A) t₁ ⟨t, j⟩ M₁ ∧
        pointGen (A ^ (n + 1)) τ ⟨t, p * (A.prog t).length + j⟩
          = recycleCount b t₁ (M₁ - 1) + 1
            + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j p c b par hjL hp hcj hbr
    have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
    -- the copy executes in `τ` and `⟨t, j⟩` executes in `t₁`
    have hppLen : (((A ^ (n + 1)).prog t).length) = (n + 1) * (A.prog t).length :=
      CTA.pow_prog_length A (n + 1) t
    have hidxlt : p * (A.prog t).length + j < ((A ^ (n + 1)).prog t).length := by
      rw [hppLen]
      have hle : p * (A.prog t).length ≤ n * (A.prog t).length := Nat.mul_le_mul_right _ hp
      have : (n + 1) * (A.prog t).length = n * (A.prog t).length + (A.prog t).length := by
        rw [Nat.succ_mul]
      omega
    obtain ⟨M, hM⟩ := exists_time_of_ends_done hτ.1 hlast
      (η := ⟨t, p * (A.prog t).length + j⟩) hidxlt
    obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) (by exact hjL)
    -- the command at the copy is `c`, a barrier op on `b`
    have hcmdcopy : (A ^ (n + 1)).cmdAt ⟨t, p * (A.prog t).length + j⟩ = some c := by
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
        conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
        rw [CTA.pow_add_prog]
      change ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = some c
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL]
      exact hcj
    refine ⟨M₁, hM₁, ?_⟩
    have hg : pointGen (A ^ (n + 1)) τ ⟨t, p * (A.prog t).length + j⟩
        = recycleCount b τ (M - 1) + 1 := by
      simp only [pointGen, hcmdcopy, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
    rw [hg, hrec t j c b par p M M₁ (by omega) hcj hbr hM hM₁]; omega
  -- **Per-point generation in the prefix trace.** Mirror of `keygen` for the `n`-batch replay
  -- `τn`: a barrier copy at batch `p < n` position `j` has the *same* offset structure relative
  -- to the SAME `t₁`-time `M₁`, so the two traces' generations of a prefix barrier point agree.
  obtain ⟨sdn', hlastn'⟩ : ∃ sdn', τn.getLast? = some (Config.done sdn') := ⟨State.initial, hτnL⟩
  have keygenN : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
      j < (A.prog t).length → p < n →
      (A.prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
      ∃ M₁, IsTimeOf (Config.run State.initial A) t₁ ⟨t, j⟩ M₁ ∧
        pointGen (A ^ n) τn ⟨t, p * (A.prog t).length + j⟩
          = recycleCount b t₁ (M₁ - 1) + 1
            + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j p c b par hjL hp hcj hbr
    have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
    have hppLen : (((A ^ n).prog t).length) = n * (A.prog t).length := CTA.pow_prog_length A n t
    have hidxlt : p * (A.prog t).length + j < ((A ^ n).prog t).length := by
      rw [hppLen]
      have hle : (p + 1) * (A.prog t).length ≤ n * (A.prog t).length :=
        Nat.mul_le_mul_right _ (by omega)
      have : (p + 1) * (A.prog t).length = p * (A.prog t).length + (A.prog t).length := by
        rw [Nat.succ_mul]
      omega
    obtain ⟨M, hM⟩ := exists_time_of_ends_done hτn.1 hlastn'
      (η := ⟨t, p * (A.prog t).length + j⟩) hidxlt
    obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) (by exact hjL)
    have hcmdcopy : (A ^ n).cmdAt ⟨t, p * (A.prog t).length + j⟩ = some c := by
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ n).prog t = (A ^ p).prog t ++ (A ^ (n - p)).prog t := by
        conv_lhs => rw [show n = p + (n - p) from by omega]
        rw [CTA.pow_add_prog]
      change ((A ^ n).prog t)[p * (A.prog t).length + j]? = some c
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n - p = (n - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL]
      exact hcj
    refine ⟨M₁, hM₁, ?_⟩
    have hg : pointGen (A ^ n) τn ⟨t, p * (A.prog t).length + j⟩
        = recycleCount b τn (M - 1) + 1 := by
      simp only [pointGen, hcmdcopy, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
    rw [hg, hrecn t j c b par p M M₁ (by omega) hcj hbr hM hM₁]; omega
  -- (GP) generation preservation on prefix barrier points, factored out so the
  -- monotonicity proof can reuse it to transfer the generation equalities on barrier edges.
  have hGP : ∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
      η.idx < n * (A.prog η.thread).length →
      (A ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
      pointGen (A ^ (n + 1)) τ η = pointGen (A ^ n) τn η := by
    intro η c b par hidx hcmd hbr
    obtain ⟨t, idx⟩ := η
    dsimp only at hidx hcmd ⊢
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [h0, Nat.mul_zero] at hidx; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p < n := by
      have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
      have hmul : p * (A.prog t).length < n * (A.prog t).length := by omega
      exact Nat.lt_of_mul_lt_mul_right hmul
    -- the command at `⟨t, idx⟩` is the batch-0 instruction `(A.prog t)[j]`
    have hcj : (A.prog t)[j]? = some c := by
      have hcmd' : ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = some c := by
        change ((A ^ (n + 1)).prog t)[idx]? = some c at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
        conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygen t j p c b par hjL (by omega) hcj hbr
    obtain ⟨M₁', hM₁', hgpn⟩ := keygenN t j p c b par hjL hpn hcj hbr
    have hM₁eq : M₁ = M₁' := IsTimeOf.unique hM₁ hM₁'
    change pointGen (A ^ (n + 1)) τ ⟨t, idx⟩ = pointGen (A ^ n) τn ⟨t, idx⟩
    rw [hidxeq, hgp, hgpn, hM₁eq]
  refine ⟨τ, hτ, ?_, ?_, ?_, ?_, τn, hτn, ?_, ?_, ?_, ?_, ?_⟩
  · -- consecutive-batch generation offset
    intro t j p c b par hp1 hpn hcj hbr
    have hjL : j < (A.prog t).length := (List.getElem?_eq_some_iff.mp hcj).1
    obtain ⟨M₁, hM₁, hgp⟩ := keygen t j p c b par hjL hpn hcj hbr
    obtain ⟨M₁', hM₁', hgp1⟩ := keygen t j (p - 1) c b par hjL (by omega) hcj hbr
    have hM₁eq : M₁ = M₁' := IsTimeOf.unique hM₁ hM₁'
    rw [hgp, hgp1, hM₁eq]
    have hpδ : p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
        = (p - 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
      conv_lhs => rw [show p = (p - 1) + 1 from by omega, Nat.succ_mul]
    omega
  · -- lower generation bound
    intro η c b par hcmd hbr
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmd ⊢
    -- valid point: `idx < (n+1)·L`, so `L > 0`, write `p = idx / L`, `j = idx % L`
    have hidxlt : idx < ((A ^ (n + 1)).prog t).length := (List.getElem?_eq_some_iff.mp hcmd).1
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hidxlt; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p ≤ n := by
      rw [CTA.pow_prog_length] at hidxlt
      have hmul : p * (A.prog t).length < (n + 1) * (A.prog t).length := by
        have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hmul)
    have hcj : (A.prog t)[j]? = some c := by
      have hcmd' : ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = some c := by
        change ((A ^ (n + 1)).prog t)[idx]? = some c at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
        conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygen t j p c b par hjL hpn hcj hbr
    rw [hidxeq, hgp]
    omega
  · -- upper generation bound (syncs)
    intro η b par hcmd
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmd ⊢
    have hidxlt : idx < ((A ^ (n + 1)).prog t).length := (List.getElem?_eq_some_iff.mp hcmd).1
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hidxlt; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p ≤ n := by
      rw [CTA.pow_prog_length] at hidxlt
      have hmul : p * (A.prog t).length < (n + 1) * (A.prog t).length := by
        have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hmul)
    have hcj : (A.prog t)[j]? = some (Cmd.sync b par) := by
      have hcmd' : ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = some (Cmd.sync b par) := by
        change ((A ^ (n + 1)).prog t)[idx]? = some (Cmd.sync b par) at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
        conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygen t j p (Cmd.sync b par) b par hjL hpn hcj rfl
    rw [hidxeq, hgp]
    -- the batch-0 sync recycle bound: `recycleCount b t₁ (M₁ - 1) + 1 ≤ δ`
    have hsyncbound : recycleCount b t₁ (M₁ - 1) + 1
        ≤ I.loopK h * I.arrivers b / I.arrivalCount h b :=
      sync_recycleCount_lt_batch h ht₁ ht₁L hcj hM₁ WF_initial (fun _ => rfl)
    have hexp : (p + 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
        = p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by rw [Nat.succ_mul]
    omega
  · -- general barrier-op upper bound: any barrier op `c` on `b` has gen `≤ (p+1)·δ`
    intro η c b par hcmd hbr
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmd ⊢
    have hidxlt : idx < ((A ^ (n + 1)).prog t).length := (List.getElem?_eq_some_iff.mp hcmd).1
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hidxlt; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p ≤ n := by
      rw [CTA.pow_prog_length] at hidxlt
      have hmul : p * (A.prog t).length < (n + 1) * (A.prog t).length := by
        have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hmul)
    have hcj : (A.prog t)[j]? = some c := by
      have hcmd' : ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = some c := by
        change ((A ^ (n + 1)).prog t)[idx]? = some c at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
        conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygen t j p c b par hjL hpn hcj hbr
    rw [hidxeq, hgp]
    -- strict recycle bound: `recycleCount b t₁ (M₁ - 1) + 1 ≤ δ` (arrive or sync)
    have hbound : recycleCount b t₁ (M₁ - 1) + 1
        ≤ I.loopK h * I.arrivers b / I.arrivalCount h b := by
      cases c with
      | read g => simp [Cmd.barrierRef] at hbr
      | write g => simp [Cmd.barrierRef] at hbr
      | arrive bb mm =>
        simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
        obtain ⟨rfl, rfl⟩ := hbr
        exact arrive_recycleCount_lt_batch h ht₁ ht₁L hcj hM₁ WF_initial (fun _ => rfl) rfl
      | sync bb mm =>
        simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
        obtain ⟨rfl, rfl⟩ := hbr
        exact sync_recycleCount_lt_batch h ht₁ ht₁L hcj hM₁ WF_initial (fun _ => rfl)
    have hexp : (p + 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
        = p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by rw [Nat.succ_mul]
    omega
  · -- (τn) consecutive-batch generation offset for the prefix trace (`p ≤ n - 1`)
    intro t j p c b par hp1 hpn hcj hbr
    have hjL : j < (A.prog t).length := (List.getElem?_eq_some_iff.mp hcj).1
    obtain ⟨M₁, hM₁, hgp⟩ := keygenN t j p c b par hjL (by omega) hcj hbr
    obtain ⟨M₁', hM₁', hgp1⟩ := keygenN t j (p - 1) c b par hjL (by omega) hcj hbr
    have hM₁eq : M₁ = M₁' := IsTimeOf.unique hM₁ hM₁'
    rw [hgp, hgp1, hM₁eq]
    have hpδ : p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
        = (p - 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
      conv_lhs => rw [show p = (p - 1) + 1 from by omega, Nat.succ_mul]
    omega
  · -- (τn) lower generation bound for the prefix program `A ^ n`
    intro η c b par hcmd hbr
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmd ⊢
    have hidxlt : idx < ((A ^ n).prog t).length := (List.getElem?_eq_some_iff.mp hcmd).1
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hidxlt; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p < n := by
      rw [CTA.pow_prog_length] at hidxlt
      have hmul : p * (A.prog t).length < n * (A.prog t).length := by
        have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_of_mul_lt_mul_right hmul
    have hcj : (A.prog t)[j]? = some c := by
      have hcmd' : ((A ^ n).prog t)[p * (A.prog t).length + j]? = some c := by
        change ((A ^ n).prog t)[idx]? = some c at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ n).prog t = (A ^ p).prog t ++ (A ^ (n - p)).prog t := by
        conv_lhs => rw [show n = p + (n - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n - p = (n - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygenN t j p c b par hjL hpn hcj hbr
    rw [hidxeq, hgp]
    omega
  · -- (τn) upper generation bound (syncs) for the prefix program `A ^ n`
    intro η b par hcmd
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmd ⊢
    have hidxlt : idx < ((A ^ n).prog t).length := (List.getElem?_eq_some_iff.mp hcmd).1
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hpos
      · rw [CTA.pow_prog_length, h0, Nat.mul_zero] at hidxlt; omega
      · exact hpos
    set p := idx / (A.prog t).length with hpdef
    set j := idx % (A.prog t).length with hjdef
    have hjL : j < (A.prog t).length := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * (A.prog t).length + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx (A.prog t).length).symm
    have hpn : p < n := by
      rw [CTA.pow_prog_length] at hidxlt
      have hmul : p * (A.prog t).length < n * (A.prog t).length := by
        have : p * (A.prog t).length ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_of_mul_lt_mul_right hmul
    have hcj : (A.prog t)[j]? = some (Cmd.sync b par) := by
      have hcmd' : ((A ^ n).prog t)[p * (A.prog t).length + j]? = some (Cmd.sync b par) := by
        change ((A ^ n).prog t)[idx]? = some (Cmd.sync b par) at hcmd
        rw [← hidxeq]; exact hcmd
      have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
      have hsplit : (A ^ n).prog t = (A ^ p).prog t ++ (A ^ (n - p)).prog t := by
        conv_lhs => rw [show n = p + (n - p) from by omega]
        rw [CTA.pow_add_prog]
      rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
        show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
        show n - p = (n - p - 1) + 1 from by omega, CTA.pow_succ_prog,
        List.getElem?_append_left hjL] at hcmd'
      exact hcmd'
    obtain ⟨M₁, hM₁, hgp⟩ := keygenN t j p (Cmd.sync b par) b par hjL hpn hcj rfl
    rw [hidxeq, hgp]
    have hsyncbound : recycleCount b t₁ (M₁ - 1) + 1
        ≤ I.loopK h * I.arrivers b / I.arrivalCount h b :=
      sync_recycleCount_lt_batch h ht₁ ht₁L hcj hM₁ WF_initial (fun _ => rfl)
    have hexp : (p + 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
        = p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by rw [Nat.succ_mul]
    omega
  · -- (GP) generation preservation on prefix barrier points
    exact hGP
  · -- (MONO) happens-before monotonicity: prefix program ⊆ full program
    intro a b hab
    -- reduce to the per-edge claim via `ReflTransGen.mono`
    refine Relation.ReflTransGen.mono ?_ hab
    intro x y hxy
    -- a prefix edge has both endpoints in the first `n` batches; lift it to the full program
    obtain ⟨hxpts, hypts, -⟩ := initRelation_cases hxy
    have hxidx : x.idx < n * (A.prog x.thread).length := by
      have := ((mem_progPoints_iff (A ^ n) x).mp hxpts).2
      rwa [CTA.pow_prog_length] at this
    have hyidx : y.idx < n * (A.prog y.thread).length := by
      have := ((mem_progPoints_iff (A ^ n) y).mp hypts).2
      rwa [CTA.pow_prog_length] at this
    -- commands agree between the two programs on prefix points
    have hcmdx : (A ^ (n + 1)).cmdAt x = (A ^ n).cmdAt x := CTA.cmdAt_pow_succ_prefix A hxidx
    have hcmdy : (A ^ (n + 1)).cmdAt y = (A ^ n).cmdAt y := CTA.cmdAt_pow_succ_prefix A hyidx
    -- membership of the endpoints in the bigger program
    have hxlt : x.idx < ((A ^ (n + 1)).prog x.thread).length := by
      rw [CTA.pow_prog_length]
      exact Nat.lt_of_lt_of_le hxidx (Nat.mul_le_mul_right _ (by omega))
    have hylt : y.idx < ((A ^ (n + 1)).prog y.thread).length := by
      rw [CTA.pow_prog_length]
      exact Nat.lt_of_lt_of_le hyidx (Nat.mul_le_mul_right _ (by omega))
    have hxpts' : x ∈ (A ^ (n + 1)).progPoints :=
      (mem_progPoints_iff _ x).mpr ⟨mem_ids_of_idx_lt (A ^ (n + 1)) hxlt, hxlt⟩
    have hypts' : y ∈ (A ^ (n + 1)).progPoints :=
      (mem_progPoints_iff _ y).mpr ⟨mem_ids_of_idx_lt (A ^ (n + 1)) hylt, hylt⟩
    -- generation agreement transfers from the prefix to the full program (via GP)
    have hgenx : ∀ (c : Cmd) (bb : Barrier) (pp : ℕ+), (A ^ n).cmdAt x = some c →
        Cmd.barrierRef c = some (bb, pp) →
        pointGen (A ^ (n + 1)) τ x = pointGen (A ^ n) τn x :=
      fun c bb pp hc hb => hGP x c bb pp hxidx (by rw [hcmdx]; exact hc) hb
    have hgeny : ∀ (c : Cmd) (bb : Barrier) (pp : ℕ+), (A ^ n).cmdAt y = some c →
        Cmd.barrierRef c = some (bb, pp) →
        pointGen (A ^ (n + 1)) τ y = pointGen (A ^ n) τn y :=
      fun c bb pp hc hb => hGP y c bb pp hyidx (by rw [hcmdy]; exact hc) hb
    rw [mem_initRelation_iff] at hxy ⊢
    rcases hxy with ⟨_, hlt, hbeq⟩ | ⟨bb, m, _, _, hca, hcb, hg⟩ | ⟨bb, m, _, _, hca, hcb, hg⟩
    · -- program order
      refine Or.inl ⟨hxpts', ?_, hbeq⟩
      rw [CTA.pow_prog_length] at hlt ⊢
      exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ (by omega))
    · -- arrive → sync
      refine Or.inr (Or.inl ⟨bb, m, hxpts', hypts', ?_, ?_, ?_⟩)
      · rw [hcmdx]; exact hca
      · rw [hcmdy]; exact hcb
      · rw [hgenx (Cmd.arrive bb m) bb m hca rfl, hgeny (Cmd.sync bb m) bb m hcb rfl]
        exact hg
    · -- sync ↔ sync
      refine Or.inr (Or.inr ⟨bb, m, hxpts', hypts', ?_, ?_, ?_⟩)
      · rw [hcmdx]; exact hca
      · rw [hcmdy]; exact hcb
      · rw [hgenx (Cmd.sync bb m) bb m hca rfl, hgeny (Cmd.sync bb m) bb m hcb rfl]
        exact hg

/-- **`M`-parametric core of `last_batch_hb_within_impl`.** Takes the shared replay trace `τ`
of `(I ^ k) ^ (n + 1)` together with its consecutive-batch generation offset `hoffset` and the
`(L)`/`(U)` generation bounds as *hypotheses* (the `last_batches_replay_bundle` outputs), and
proves the within-batch happens-before equivalence for the last two batches `n - 1` and `n`.
Stating it over abstract bundle outputs lets it be reused at *prefix* exponents (`n - 1` with the
prefix trace `τn`), which `batches_inductive_step` needs. -/
theorem CTA.WellSynchronized.last_batch_hb_within_core {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (τ : List Config)
    (_hτ : IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ)
    (hoffset : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
        1 ≤ p → p ≤ n → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, p * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (p - 1) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b)
    (hL : ∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers b / I.arrivalCount h b) + 1
          ≤ pointGen ((I ^ k) ^ (n + 1)) τ η)
    (hU : ∀ (η : ProgPoint) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some (Cmd.sync b par) →
        pointGen ((I ^ k) ^ (n + 1)) τ η
          ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
              * (k * I.arrivers b / I.arrivalCount h b)) :
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, n * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, n * ((I ^ k).prog t₂).length + j₂⟩) := by
  -- the offset between the last two batches `n - 1` and `n` (Lemma 4.1) at `p := n`
  have hgen : ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (m : ℕ+),
      ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, m) →
      pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, n * ((I ^ k).prog t).length + j⟩
        = pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
          + k * I.arrivers b / I.arrivalCount h b := by
    intro t j c b m hcj hbr
    exact hoffset t j n c b m (by omega) (le_refl n) hcj hbr
  set A := I ^ k with hA
  -- length bookkeeping for the `n + 1`-batch program (`L = (A.prog t).length`)
  have hPlen : ∀ (t : ThreadId), ((A ^ (n + 1)).prog t).length = (n + 1) * (A.prog t).length :=
    fun t => CTA.pow_prog_length A (n + 1) t
  have hnL : ∀ (t : ThreadId), (n + 1) * (A.prog t).length
      = (n - 1) * (A.prog t).length + ((A.prog t).length + (A.prog t).length) := by
    intro t
    conv_lhs => rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]
    omega
  have hn1L : ∀ (t : ThreadId), n * (A.prog t).length
      = (n - 1) * (A.prog t).length + (A.prog t).length := by
    intro t
    conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.add_mul, Nat.one_mul]
  have hnpred : ∀ (t : ThreadId), (n + 1) * (A.prog t).length
      = n * (A.prog t).length + (A.prog t).length := by
    intro t; rw [Nat.add_mul, Nat.one_mul]
  -- the command at the copy of body instruction `j` in batch `p` is the body command
  have hcmdbatch : ∀ (t : ThreadId) (j p : Nat), j < (A.prog t).length → p < n + 1 →
      (A ^ (n + 1)).cmdAt ⟨t, p * (A.prog t).length + j⟩ = (A.prog t)[j]? := by
    intro t j p hj hp
    have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
    have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
      conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
      rw [CTA.pow_add_prog]
    change ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = (A.prog t)[j]?
    rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
      show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
      show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
      List.getElem?_append_left hj]
  -- program points of the second-to-last (lower) and last (upper) batches are valid
  have hppLowAbs : ∀ (t : ThreadId) (idx : Nat),
      (n - 1) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (⟨t, idx⟩ : ProgPoint) ∈ (A ^ (n + 1)).progPoints := by
    intro t idx hlo hhi
    have hi : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by have := hn1L t; omega
    rw [mem_progPoints_iff]
    refine ⟨?_, ?_⟩
    · change t ∈ (A ^ (n + 1)).ids
      rw [CTA.pow_ids]; exact mem_ids_of_idx_lt A hi
    · change idx < ((A ^ (n + 1)).prog t).length
      rw [hPlen]; have := hn1L t; rw [hnL t]; omega
  have hppUpAbs : ∀ (t : ThreadId) (idx : Nat),
      (n - 1) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (⟨t, idx + (A.prog t).length⟩ : ProgPoint) ∈ (A ^ (n + 1)).progPoints := by
    intro t idx hlo hhi
    have hi : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by have := hn1L t; omega
    rw [mem_progPoints_iff]
    refine ⟨?_, ?_⟩
    · change t ∈ (A ^ (n + 1)).ids
      rw [CTA.pow_ids]; exact mem_ids_of_idx_lt A hi
    · change idx + (A.prog t).length < ((A ^ (n + 1)).prog t).length
      rw [hPlen]; have := hn1L t; rw [hnL t]; omega
  -- commands agree under a one-batch (n-1 → n) shift
  have hcmdN : ∀ (t : ThreadId) (idx : Nat),
      (n - 1) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (A ^ (n + 1)).cmdAt ⟨t, idx + (A.prog t).length⟩ = (A ^ (n + 1)).cmdAt ⟨t, idx⟩ := by
    intro t idx hlo hhi
    have hi : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by have := hn1L t; omega
    have e1 := hcmdbatch t (idx - (n - 1) * (A.prog t).length) (n - 1) hi (by omega)
    have e2 := hcmdbatch t (idx - (n - 1) * (A.prog t).length) n hi (by omega)
    rw [show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx from by omega]
      at e1
    rw [show n * (A.prog t).length + (idx - (n - 1) * (A.prog t).length)
          = idx + (A.prog t).length from by have := hn1L t; omega] at e2
    rw [e2, e1]
  -- **Generation neighbour offset.** Shifting a lower (batch n-1) barrier point up by one batch
  -- adds `Δ = k·arrivers(b)/count(b)` to its generation.
  have hgenN : ∀ (t : ThreadId) (idx : Nat) (c : Cmd) (b : Barrier) (m : ℕ+),
      (n - 1) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (A ^ (n + 1)).cmdAt ⟨t, idx⟩ = some c → Cmd.barrierRef c = some (b, m) →
      pointGen (A ^ (n + 1)) τ ⟨t, idx + (A.prog t).length⟩
        = pointGen (A ^ (n + 1)) τ ⟨t, idx⟩ + k * I.arrivers b / I.arrivalCount h b := by
    intro t idx c b m hlo hhi hcmd hbr
    have hi : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by have := hn1L t; omega
    have hbody : (A.prog t)[idx - (n - 1) * (A.prog t).length]? = some c := by
      have e := hcmdbatch t (idx - (n - 1) * (A.prog t).length) (n - 1) hi (by omega)
      rw [show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx
            from by omega] at e
      rw [← e]; exact hcmd
    have hh := hgen t (idx - (n - 1) * (A.prog t).length) c b m hbody hbr
    rw [show n * (A.prog t).length + (idx - (n - 1) * (A.prog t).length)
          = idx + (A.prog t).length from by have := hn1L t; omega,
        show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx from by omega]
      at hh
    exact hh
  -- **Edge shift.** An `initRelation` edge between two second-to-last-batch points exists iff the
  -- edge between their last-batch copies does. Barrier edges hinge on generation *equality*,
  -- preserved because both endpoints shift by the same per-barrier offset (`hgenN`).
  have hshift : ∀ (a b : ProgPoint),
      (n - 1) * (A.prog a.thread).length ≤ a.idx → a.idx < n * (A.prog a.thread).length →
      (n - 1) * (A.prog b.thread).length ≤ b.idx → b.idx < n * (A.prog b.thread).length →
      ((a, b) ∈ initRelation (A ^ (n + 1)) τ ↔
        (⟨a.thread, a.idx + (A.prog a.thread).length⟩,
          ⟨b.thread, b.idx + (A.prog b.thread).length⟩) ∈ initRelation (A ^ (n + 1)) τ) := by
    intro a b haLo haHi hbLo hbHi
    obtain ⟨s₁, i₁⟩ := a
    obtain ⟨s₂, i₂⟩ := b
    dsimp only at haLo haHi hbLo hbHi
    rw [mem_initRelation_iff, mem_initRelation_iff]
    constructor
    · rintro (⟨_, _, heq⟩ | ⟨bb, m, _, _, hc1, hc2, hg⟩ | ⟨bb, m, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        refine Or.inl ⟨hppUpAbs s₂ i₁ haLo haHi, ?_, ?_⟩
        · change i₁ + (A.prog s₂).length + 1 < ((A ^ (n + 1)).prog s₂).length
          rw [hPlen]; have := hnpred s₂; omega
        · change (⟨s₂, i₁ + 1 + (A.prog s₂).length⟩ : ProgPoint)
              = ⟨s₂, i₁ + (A.prog s₂).length + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · refine Or.inr (Or.inl
          ⟨bb, m, hppUpAbs s₁ i₁ haLo haHi, hppUpAbs s₂ i₂ hbLo hbHi, ?_, ?_, ?_⟩)
        · rw [hcmdN s₁ i₁ haLo haHi]; exact hc1
        · rw [hcmdN s₂ i₂ hbLo hbHi]; exact hc2
        · rw [hgenN s₁ i₁ _ bb m haLo haHi hc1 rfl, hgenN s₂ i₂ _ bb m hbLo hbHi hc2 rfl, hg]
      · refine Or.inr (Or.inr
          ⟨bb, m, hppUpAbs s₁ i₁ haLo haHi, hppUpAbs s₂ i₂ hbLo hbHi, ?_, ?_, ?_⟩)
        · rw [hcmdN s₁ i₁ haLo haHi]; exact hc1
        · rw [hcmdN s₂ i₂ hbLo hbHi]; exact hc2
        · rw [hgenN s₁ i₁ _ bb m haLo haHi hc1 rfl, hgenN s₂ i₂ _ bb m hbLo hbHi hc2 rfl, hg]
    · rintro (⟨_, _, heq⟩ | ⟨bb, m, _, _, hc1, hc2, hg⟩ | ⟨bb, m, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, hidx⟩ := heq
        refine Or.inl ⟨hppLowAbs s₂ i₁ haLo haHi, ?_, ?_⟩
        · change i₁ + 1 < ((A ^ (n + 1)).prog s₂).length
          rw [hPlen]; have := hnpred s₂; omega
        · change (⟨s₂, i₂⟩ : ProgPoint) = ⟨s₂, i₁ + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · have he1 : (A ^ (n + 1)).cmdAt ⟨s₁, i₁⟩ = some (Cmd.arrive bb m) := by
          rw [← hcmdN s₁ i₁ haLo haHi]; exact hc1
        have he2 : (A ^ (n + 1)).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb m) := by
          rw [← hcmdN s₂ i₂ hbLo hbHi]; exact hc2
        refine Or.inr (Or.inl
          ⟨bb, m, hppLowAbs s₁ i₁ haLo haHi, hppLowAbs s₂ i₂ hbLo hbHi, he1, he2, ?_⟩)
        rw [hgenN s₁ i₁ _ bb m haLo haHi he1 rfl, hgenN s₂ i₂ _ bb m hbLo hbHi he2 rfl] at hg
        omega
      · have he1 : (A ^ (n + 1)).cmdAt ⟨s₁, i₁⟩ = some (Cmd.sync bb m) := by
          rw [← hcmdN s₁ i₁ haLo haHi]; exact hc1
        have he2 : (A ^ (n + 1)).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb m) := by
          rw [← hcmdN s₂ i₂ hbLo hbHi]; exact hc2
        refine Or.inr (Or.inr
          ⟨bb, m, hppLowAbs s₁ i₁ haLo haHi, hppLowAbs s₂ i₂ hbLo hbHi, he1, he2, ?_⟩)
        rw [hgenN s₁ i₁ _ bb m haLo haHi he1 rfl, hgenN s₂ i₂ _ bb m hbLo hbHi he2 rfl] at hg
        omega
  -- **No backward edges into the last batch** (batch monotonicity, `no_backward_edge` at `p := n`).
  have NB_upper : ¬ ∃ s d : ProgPoint, happensBefore (A ^ (n + 1)) τ s d ∧
      (n * (A.prog s.thread).length ≤ s.idx ∧ s.idx < (n + 1) * (A.prog s.thread).length) ∧
      d.idx < n * (A.prog d.thread).length := by
    rintro ⟨s, d, hR, ⟨h1, _⟩, h3⟩
    exact no_backward_edge h hk hL hU n s d hR h1 h3
  -- **No backward edges from the last two batches into earlier batches** (`no_backward_edge`
  -- at `p := n - 1`); vacuous for `n = 1`, where there is nothing below.
  have NB_lower : ¬ ∃ s d : ProgPoint, happensBefore (A ^ (n + 1)) τ s d ∧
      ((n - 1) * (A.prog s.thread).length ≤ s.idx ∧ s.idx < (n + 1) * (A.prog s.thread).length) ∧
      d.idx < (n - 1) * (A.prog d.thread).length := by
    rintro ⟨s, d, hR, ⟨h1, _⟩, h3⟩
    exact no_backward_edge h hk hL hU (n - 1) s d hR h1 h3
  intro t₁ t₂ j₁ j₂ hj₁ hj₂
  -- **Confinement (lower).** A happens-before path landing in batch `n-1` stays in batch `n-1`:
  -- nothing above (batch `n`, `NB_upper`) nor below (`NB_lower`) it reaches batch `n-1`.
  have confLow : ∀ (c : ProgPoint),
      happensBefore (A ^ (n + 1)) τ c ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩ →
      ((n - 1) * (A.prog c.thread).length ≤ c.idx ∧ c.idx < n * (A.prog c.thread).length) →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 1) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < n * (A.prog x.thread).length) ∧
          ((n - 1) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < n * (A.prog y.thread).length))
        c ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩ := by
    intro c hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxL
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyL : (n - 1) * (A.prog y.thread).length ≤ y.idx ∧
          y.idx < n * (A.prog y.thread).length := by
        refine ⟨?_, ?_⟩
        · by_contra hcon
          exact NB_lower ⟨x, y, Relation.ReflTransGen.single hxy,
            ⟨hxL.1, by have := hnpred x.thread; omega⟩, by omega⟩
        · by_contra hcon
          have hdb : (n - 1) * (A.prog t₂).length + j₂ < n * (A.prog t₂).length := by
            have := hn1L t₂; omega
          exact NB_upper ⟨y, ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩, hyd,
            ⟨by omega, hypp.2⟩, hdb⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxL, hyL⟩ (ih hyL)
  -- **Confinement (upper).** A happens-before path leaving batch `n` stays in batch `n`:
  -- nothing in batch `n` reaches an earlier batch (`NB_upper`).
  have confUp : ∀ (c d : ProgPoint), happensBefore (A ^ (n + 1)) τ c d →
      (n * (A.prog c.thread).length ≤ c.idx ∧ c.idx < (n + 1) * (A.prog c.thread).length) →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          (n * (A.prog x.thread).length ≤ x.idx ∧ x.idx < (n + 1) * (A.prog x.thread).length) ∧
          (n * (A.prog y.thread).length ≤ y.idx ∧ y.idx < (n + 1) * (A.prog y.thread).length))
        c d := by
    intro c d hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxU
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyU : n * (A.prog y.thread).length ≤ y.idx ∧
          y.idx < (n + 1) * (A.prog y.thread).length := by
        refine ⟨?_, hypp.2⟩
        by_contra hcon
        exact NB_upper ⟨x, y, Relation.ReflTransGen.single hxy, hxU, by omega⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxU, hyU⟩ (ih hyU)
  constructor
  · -- forward: confine to batch n-1, shift edge-by-edge up to batch n
    intro hHB
    have hcL : (n - 1) * (A.prog t₁).length ≤ (n - 1) * (A.prog t₁).length + j₁ ∧
        (n - 1) * (A.prog t₁).length + j₁ < n * (A.prog t₁).length :=
      ⟨Nat.le_add_right _ _, by have := hn1L t₁; omega⟩
    have hUp : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          (n * (A.prog x.thread).length ≤ x.idx ∧ x.idx < (n + 1) * (A.prog x.thread).length) ∧
          (n * (A.prog y.thread).length ≤ y.idx ∧ y.idx < (n + 1) * (A.prog y.thread).length))
        ⟨t₁, (n - 1) * (A.prog t₁).length + j₁ + (A.prog t₁).length⟩
        ⟨t₂, (n - 1) * (A.prog t₂).length + j₂ + (A.prog t₂).length⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, η.idx + (A.prog η.thread).length⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haL, hbL⟩ := hab
          dsimp only at haL hbL
          have hat := hn1L at'; have hbt := hn1L bt
          have hatp := hnpred at'; have hbtp := hnpred bt
          refine ⟨(hshift ⟨at', ai⟩ ⟨bt, bi⟩ haL.1 haL.2 hbL.1 hbL.2).mp hab', ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
          · change n * (A.prog at').length ≤ ai + (A.prog at').length
            omega
          · change ai + (A.prog at').length < (n + 1) * (A.prog at').length
            omega
          · change n * (A.prog bt).length ≤ bi + (A.prog bt).length
            omega
          · change bi + (A.prog bt).length < (n + 1) * (A.prog bt).length
            omega)
        (confLow ⟨t₁, (n - 1) * (A.prog t₁).length + j₁⟩ hHB hcL)
    rw [show (n - 1) * (A.prog t₁).length + j₁ + (A.prog t₁).length
          = n * (A.prog t₁).length + j₁ from by have := hn1L t₁; omega,
        show (n - 1) * (A.prog t₂).length + j₂ + (A.prog t₂).length
          = n * (A.prog t₂).length + j₂ from by have := hn1L t₂; omega] at hUp
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hUp
  · -- backward: confine to batch n, shift edge-by-edge down to batch n-1
    intro hHB
    have hcU : n * (A.prog t₁).length ≤ n * (A.prog t₁).length + j₁ ∧
        n * (A.prog t₁).length + j₁ < (n + 1) * (A.prog t₁).length :=
      ⟨Nat.le_add_right _ _, by have := hnpred t₁; omega⟩
    have hLow : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 1) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < n * (A.prog x.thread).length) ∧
          ((n - 1) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < n * (A.prog y.thread).length))
        ⟨t₁, n * (A.prog t₁).length + j₁ - (A.prog t₁).length⟩
        ⟨t₂, n * (A.prog t₂).length + j₂ - (A.prog t₂).length⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, η.idx - (A.prog η.thread).length⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haU, hbU⟩ := hab
          dsimp only at haU hbU
          have hat := hn1L at'; have hbt := hn1L bt
          have hatp := hnpred at'; have hbtp := hnpred bt
          have hp1lo : (n - 1) * (A.prog at').length ≤ ai - (A.prog at').length := by omega
          have hp1hi : ai - (A.prog at').length < n * (A.prog at').length := by omega
          have hp2lo : (n - 1) * (A.prog bt).length ≤ bi - (A.prog bt).length := by omega
          have hp2hi : bi - (A.prog bt).length < n * (A.prog bt).length := by omega
          refine ⟨?_, ⟨hp1lo, hp1hi⟩, ⟨hp2lo, hp2hi⟩⟩
          rw [hshift ⟨at', ai - (A.prog at').length⟩ ⟨bt, bi - (A.prog bt).length⟩
              hp1lo hp1hi hp2lo hp2hi,
            show ai - (A.prog at').length + (A.prog at').length = ai from by omega,
            show bi - (A.prog bt).length + (A.prog bt).length = bi from by omega]
          exact hab')
        (confUp ⟨t₁, n * (A.prog t₁).length + j₁⟩
          ⟨t₂, n * (A.prog t₂).length + j₂⟩ hHB hcU)
    rw [show n * (A.prog t₁).length + j₁ - (A.prog t₁).length
          = (n - 1) * (A.prog t₁).length + j₁ from by have := hn1L t₁; omega,
        show n * (A.prog t₂).length + j₂ - (A.prog t₂).length
          = (n - 1) * (A.prog t₂).length + j₂ from by have := hn1L t₂; omega] at hLow
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hLow

theorem CTA.WellSynchronized.last_batch_hb_within_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 1 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, n * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, n * ((I ^ k).prog t₂).length + j₂⟩) := by
  obtain ⟨τ, hτ, hoffset, hL, hU, -⟩ :=
    CTA.WellSynchronized.last_batches_replay_bundle h hk hn hWS
  exact ⟨τ, hτ, last_batch_hb_within_core h hk hn τ hτ hoffset hL hU⟩


/-- **Consecutive-batch recycle offset for three batches** (regrouped as `A ⨾ (A ⨾ A)`).
*(Helper for `third_batch_gen_offset`.)* There is a successful trace `τ` of the three-batch
program along which, for every barrier instruction and every batch index `i < 2`, the recycle
count of `b` just before the copy in batch `i + 1` executes exceeds the count just before the
copy in batch `i` by exactly `k · arrivers(b) / arrival-count(b)`. The trace glues a single
batch `t₁` (batch 0) in front of the two-batch replay trace `τ_AA` (batches 1–2). For `i = 1`
both copies sit in the suffix `τ_AA`, so the offset is `replay_recycle_offset`'s; for `i = 0`
the front contributes exactly one batch's worth of recycles (`pow_barriers_advance_count`),
which is the offset, the shared before-the-copy recycles cancelling. -/
theorem CTA.WellSynchronized.third_batch_recycle_offset {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized)
    (hWS1 : ((I ^ k).seq (I ^ k) rfl).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom
        (Config.run State.initial ((I ^ k).seq ((I ^ k).seq (I ^ k) rfl) rfl)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (i : Nat) (m₁ m₂ : Nat),
        i < 2 → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run State.initial ((I ^ k).seq ((I ^ k).seq (I ^ k) rfl) rfl)) τ
            ⟨t, i * ((I ^ k).prog t).length + j⟩ m₁ →
        IsTimeOf (Config.run State.initial ((I ^ k).seq ((I ^ k).seq (I ^ k) rfl) rfl)) τ
            ⟨t, (i + 1) * ((I ^ k).prog t).length + j⟩ m₂ →
        recycleCount b τ (m₂ - 1)
          = recycleCount b τ (m₁ - 1) + k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  obtain ⟨t₁, ht₁⟩ := hWS0.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  set A := I ^ I.loopK h with hA
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead1 : t₁.head? = some (Config.run State.initial A) := ht₁.1.2
  -- `t₁` has length ≥ 2 (starts `run`, ends `done`)
  have h2 : 2 ≤ t₁.length := by
    rcases t₁ with _ | ⟨a, _ | ⟨b₀, l⟩⟩
    · simp at hhead1
    · simp only [List.head?_cons, Option.some.injEq] at hhead1
      simp only [List.getLast?_singleton, Option.some.injEq] at ht₁L
      rw [hhead1] at ht₁L; exact absurd ht₁L (by simp)
    · simp only [List.length_cons]; omega
  have hdrop : t₁.dropLast ≠ [] := by
    intro hd
    have : t₁.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
    omega
  -- the two-batch replay trace `τAA` (a trace of `A ⨾ A`), and its glue in front with `t₁`
  have hτAA : IsSuccessfulTraceFrom (Config.run State.initial (A.seq A rfl))
      (t₁.dropLast.map (Config.seqLift A A) ++ t₁.tail) := replay_trace A ht₁ ht₁L
  obtain ⟨hglue, -, hsnd⟩ := glue_trace (A := A) (B := A.seq A rfl) rfl ht₁ ht₁L hτAA
  refine ⟨t₁.dropLast.map (Config.seqLift A (A.seq A rfl))
      ++ (t₁.dropLast.map (Config.seqLift A A) ++ t₁.tail).tail, hglue, ?_⟩
  intro t j c b par i m₁ m₂ hi2 hcj hbr ht1 ht2
  obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
  -- abbreviations: τAA the two-batch suffix, τ₃ the glued three-batch trace
  set τAA := t₁.dropLast.map (Config.seqLift A A) ++ t₁.tail with hτAAdef
  set τ₃ := t₁.dropLast.map (Config.seqLift A (A.seq A rfl)) ++ τAA.tail with hτ₃def
  have hpenult : (t₁.dropLast.getLast hdrop).progOf t = [] :=
    progOf_penultimate_done hchain1 ht₁L (List.getLast?_eq_some_getLast hdrop) t
  -- a batch instruction (`q' < |A.prog t|`) executes strictly before the terminal `done` step,
  -- so its time is at most `t₁.length - 2`
  have htimebound : ∀ (q' M' : Nat), q' < (A.prog t).length →
      IsTimeOf (Config.run State.initial A) t₁ ⟨t, q'⟩ M' → M' ≤ t₁.length - 2 := by
    intro q' M' hq' hT
    obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hT
    have hj'lt : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
    by_contra hcon
    have hj'eq : j' = t₁.length - 2 := by omega
    have hpeneq : t₁.dropLast.getLast hdrop = D := by
      have h1 : t₁.dropLast.getLast? = some (t₁.dropLast.getLast hdrop) :=
        List.getLast?_eq_some_getLast hdrop
      rw [List.getLast?_eq_getElem?, List.length_dropLast, List.getElem?_dropLast,
        if_pos (by omega), show t₁.length - 1 - 1 = j' from by omega, hDj] at h1
      exact ((Option.some.injEq _ _).mp h1).symm
    rw [hpeneq, hDprog] at hpenult
    have hpos : 0 < (((Config.run State.initial A).progOf t).drop q').length := by
      rw [List.length_drop]; change 0 < (A.prog t).length - q'; omega
    rw [hpenult] at hpos; simp at hpos
  -- `b` is referenced by `A`, so a single batch recycles it `Δ` times
  have hb : b ∈ A.barrierSet := by
    rw [CTA.barrierSet, Finset.mem_biUnion]
    exact ⟨t, mem_ids_of_idx_lt A hjL, List.mem_toFinset.mpr
      (List.mem_filterMap.mpr ⟨c, List.mem_of_getElem? hcj, Cmd.barrier?_of_barrierRef hbr⟩)⟩
  have hΔt1 : recycleCount b t₁ (t₁.length - 2)
      = I.loopK h * I.arrivers b / I.arrivalCount h b := by
    rw [← recycleCount_done_last hchain1 ht₁L h2]
    exact Config.WellSynchronized.pow_barriers_advance_count h WF_initial rfl ht₁ hb
  -- length bookkeeping for the regrouped program
  have hReglen : ((A.seq (A.seq A rfl) rfl).prog t).length
      = (A.prog t).length + ((A.prog t).length + (A.prog t).length) := by
    change (A.prog t ++ (A.prog t ++ A.prog t)).length = _
    rw [List.length_append, List.length_append]
  have hAAlen : ((A.seq A rfl).prog t).length = (A.prog t).length + (A.prog t).length := by
    change (A.prog t ++ A.prog t).length = _; rw [List.length_append]
  -- the front of `τ₃` mirrors `t₁` lifted into `A ⨾ (A ⨾ A)`, and `τAA` mirrors `t₁` lifted
  -- into `A ⨾ A` — both index-by-index over the first `t₁.length - 1` configurations
  have hfst3 : ∀ q, q ≤ t₁.length - 2 →
      τ₃[q]? = (t₁.map (Config.seqLift A (A.seq A rfl)))[q]? := by
    intro q hq
    rw [hτ₃def, List.getElem?_append_left (by rw [List.length_map, List.length_dropLast]; omega),
      List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  have hfstAA : ∀ q, q ≤ t₁.length - 2 → τAA[q]? = (t₁.map (Config.seqLift A A))[q]? := by
    intro q hq
    rw [hτAAdef, List.getElem?_append_left (by rw [List.length_map, List.length_dropLast]; omega),
      List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  have hfrontrec : ∀ M, M ≤ t₁.length - 2 → recycleCount b τ₃ M = recycleCount b t₁ M := by
    intro M hM
    rw [recycleCount_eq_of_getElem?_eq b (fun q hq => hfst3 q (Nat.le_trans hq hM)),
      recycleCount_map_seqLift A (A.seq A rfl) b t₁ M]
  have hfrontrecAA : ∀ M, M ≤ t₁.length - 2 → recycleCount b τAA M = recycleCount b t₁ M := by
    intro M hM
    rw [recycleCount_eq_of_getElem?_eq b (fun q hq => hfstAA q (Nat.le_trans hq hM)),
      recycleCount_map_seqLift A A b t₁ M]
  -- **Front transport.** A batch-0 instruction time in `t₁` lifts (unshifted) into `τ₃`.
  have frontTransport : ∀ (q M : Nat), q < (A.prog t).length →
      IsTimeOf (Config.run State.initial A) t₁ ⟨t, q⟩ M →
      IsTimeOf (Config.run State.initial (A.seq (A.seq A rfl) rfl)) τ₃ ⟨t, q⟩ M := by
    intro q M hq hT
    have hMb : M ≤ t₁.length - 2 := htimebound q M hq hT
    obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hT
    have hj'1 : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
    refine ⟨hglue.1, ?_, j', Config.seqLift A (A.seq A rfl) D, Config.seqLift A (A.seq A rfl) D',
      hMeq, ?_, ?_, ?_, ?_⟩
    · change q < ((A.seq (A.seq A rfl) rfl).prog t).length
      rw [hReglen]; omega
    · rw [hfst3 j' (by omega), List.getElem?_map, hDj]; rfl
    · rw [hfst3 (j' + 1) (by omega), List.getElem?_map, hDj1]; rfl
    · change (Config.seqLift A (A.seq A rfl) D).progOf t
          = ((A.seq (A.seq A rfl) rfl).prog t).drop q
      rw [Config.seqLift_progOf, hDprog]
      change (A.prog t).drop q ++ (A.seq A rfl).prog t = (A.prog t ++ (A.seq A rfl).prog t).drop q
      rw [List.drop_append_of_le_length (by omega)]
    · change (Config.seqLift A (A.seq A rfl) D').progOf t
          = ((A.seq (A.seq A rfl) rfl).prog t).drop (q + 1)
      rw [Config.seqLift_progOf, hD'prog]
      change (A.prog t).drop (q + 1) ++ (A.seq A rfl).prog t
          = (A.prog t ++ (A.seq A rfl).prog t).drop (q + 1)
      rw [List.drop_append_of_le_length (by omega)]
  -- **Front transport into `τAA`.** A batch-0 instruction time in `t₁` lifts into `τAA`.
  have frontTransportAA : ∀ (q M : Nat), q < (A.prog t).length →
      IsTimeOf (Config.run State.initial A) t₁ ⟨t, q⟩ M →
      IsTimeOf (Config.run State.initial (A.seq A rfl)) τAA ⟨t, q⟩ M := by
    intro q M hq hT
    have hMb : M ≤ t₁.length - 2 := htimebound q M hq hT
    obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hT
    have hj'1 : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
    refine ⟨hτAA.1, ?_, j', Config.seqLift A A D, Config.seqLift A A D', hMeq, ?_, ?_, ?_, ?_⟩
    · change q < ((A.seq A rfl).prog t).length
      rw [hAAlen]; omega
    · rw [hfstAA j' (by omega), List.getElem?_map, hDj]; rfl
    · rw [hfstAA (j' + 1) (by omega), List.getElem?_map, hDj1]; rfl
    · change (Config.seqLift A A D).progOf t = ((A.seq A rfl).prog t).drop q
      rw [Config.seqLift_progOf, hDprog]
      change (A.prog t).drop q ++ A.prog t = (A.prog t ++ A.prog t).drop q
      rw [List.drop_append_of_le_length (by omega)]
    · change (Config.seqLift A A D').progOf t = ((A.seq A rfl).prog t).drop (q + 1)
      rw [Config.seqLift_progOf, hD'prog]
      change (A.prog t).drop (q + 1) ++ A.prog t = (A.prog t ++ A.prog t).drop (q + 1)
      rw [List.drop_append_of_le_length (by omega)]
  -- **Suffix transport.** A `τAA` instruction time lifts into `τ₃`, shifted by the front batch.
  have suffixTransport : ∀ (q M' : Nat), q < ((A.seq A rfl).prog t).length →
      IsTimeOf (Config.run State.initial (A.seq A rfl)) τAA ⟨t, q⟩ M' →
      IsTimeOf (Config.run State.initial (A.seq (A.seq A rfl) rfl)) τ₃
        ⟨t, (A.prog t).length + q⟩ ((t₁.length - 2) + M') := by
    intro q M' hq hT'
    obtain ⟨-, -, j', D, D', hM'eq, hDj, hDj1, hDprog, hD'prog⟩ := hT'
    rw [hAAlen] at hq
    refine ⟨hglue.1, ?_, (t₁.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
    · change (A.prog t).length + q < ((A.seq (A.seq A rfl) rfl).prog t).length
      rw [hReglen]; omega
    · exact (hsnd j').trans hDj
    · rw [show (t₁.length - 2) + j' + 1 = (t₁.length - 2) + (j' + 1) from by omega]
      exact (hsnd (j' + 1)).trans hDj1
    · change D.progOf t = ((A.seq (A.seq A rfl) rfl).prog t).drop ((A.prog t).length + q)
      change D.progOf t = (A.prog t ++ (A.seq A rfl).prog t).drop ((A.prog t).length + q)
      rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
        Nat.add_sub_cancel_left]
      exact hDprog
    · change D'.progOf t = ((A.seq (A.seq A rfl) rfl).prog t).drop ((A.prog t).length + q + 1)
      change D'.progOf t = (A.prog t ++ (A.seq A rfl).prog t).drop ((A.prog t).length + q + 1)
      rw [List.drop_append,
        List.drop_eq_nil_of_le (show (A.prog t).length ≤ (A.prog t).length + q + 1 by omega),
        List.nil_append, show (A.prog t).length + q + 1 - (A.prog t).length = q + 1 from by omega]
      exact hD'prog
  -- the canonical instruction times: `MT` in `t₁`, `M_AA0`/`M_AA1` in `τAA`
  obtain ⟨sdAA, hAAlast⟩ := hτAA.2
  obtain ⟨MT, hMT⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) (by exact hjL)
  obtain ⟨M_AA0, hMAA0⟩ := exists_time_of_ends_done hτAA.1 hAAlast (η := ⟨t, j⟩)
    (by change j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
  obtain ⟨M_AA1, hMAA1⟩ := exists_time_of_ends_done hτAA.1 hAAlast (η := ⟨t, (A.prog t).length + j⟩)
    (by change (A.prog t).length + j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
  -- positivity of the times (each is `step + 1`)
  have hMTpos : 1 ≤ MT := by obtain ⟨_, _, _, he, _⟩ := hMT.2.2; omega
  have hM0pos : 1 ≤ M_AA0 := by obtain ⟨_, _, _, he, _⟩ := hMAA0.2.2; omega
  have hM1pos : 1 ≤ M_AA1 := by obtain ⟨_, _, _, he, _⟩ := hMAA1.2.2; omega
  -- `MT - 1 ≤ t₁.length - 2` (the copy executes strictly before the terminal `done`)
  have hMTle : MT - 1 ≤ t₁.length - 2 := by
    obtain ⟨_, _, j', _, _, hMeq, _, hDj1, _, _⟩ := hMT
    have : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
    omega
  -- `M_AA0 = MT`: the batch-0 copy executes at the same step in `t₁` and in `τAA`'s front
  have hM0eq : M_AA0 = MT := IsTimeOf.unique hMAA0 (frontTransportAA j MT hjL hMT)
  -- the `τAA` offset (the hard two-batch fact); refold its trace to the `τAA` abbreviation
  have hΔAA := replay_recycle_offset h ht₁ ht₁L t j c b par M_AA0 M_AA1 hcj hbr hMAA0 hMAA1
  rw [← hA, ← hτAAdef] at hΔAA
  -- recycle counts at the three relevant times, via the front/suffix decompositions
  have hrecSuf : ∀ (M' : Nat), 1 ≤ M' →
      recycleCount b τ₃ ((t₁.length - 2) + M' - 1)
        = recycleCount b τ₃ (t₁.length - 2) + recycleCount b τAA (M' - 1) := by
    intro M' hM'
    rw [show (t₁.length - 2) + M' - 1 = (t₁.length - 2) + (M' - 1) from by omega,
      recycleCount_suffix b hsnd]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · -- i = 0: batch 0 (front) and batch 1 (suffix)
    have h1m : m₁ = MT := IsTimeOf.unique (by simpa using ht1) (frontTransport j MT hjL hMT)
    have h2m : m₂ = (t₁.length - 2) + M_AA0 :=
      IsTimeOf.unique (by simpa using ht2) (suffixTransport j M_AA0 (by rw [hAAlen]; omega) hMAA0)
    rw [h1m, h2m, hrecSuf M_AA0 hM0pos, hfrontrec (t₁.length - 2) (le_refl _),
      hfrontrecAA (M_AA0 - 1) (by omega), hfrontrec (MT - 1) hMTle, hΔt1, hM0eq]
    omega
  · -- i = 1: batch 1 and batch 2, both in the suffix `τAA`
    have h1m : m₁ = (t₁.length - 2) + M_AA0 :=
      IsTimeOf.unique (by simpa using ht1) (suffixTransport j M_AA0 (by rw [hAAlen]; omega) hMAA0)
    have h2m : m₂ = (t₁.length - 2) + M_AA1 := by
      refine IsTimeOf.unique ?_ (suffixTransport ((A.prog t).length + j) M_AA1
        (by rw [hAAlen]; omega) hMAA1)
      have e : (1 + 1) * (A.prog t).length + j = (A.prog t).length + ((A.prog t).length + j) := by
        omega
      rw [e] at ht2; exact ht2
    rw [h1m, h2m, hrecSuf M_AA0 hM0pos, hrecSuf M_AA1 hM1pos, hΔAA]
    omega

/-- **Consecutive-batch recycle offset for the last three batches of `(I ^ k) ^ n`.**
*(Helper for `last_batches_gen_offset`.)* The `n`-batch generalization of
`third_batch_recycle_offset`: there is a successful trace `τ` of `(I ^ k) ^ n` (`n ≥ 3`) along
which, for every barrier instruction and every `i < 2`, the recycle count of `b` just before
the copy in batch `n - 3 + i + 1` exceeds the count just before the copy in batch `n - 3 + i`
by exactly `k · arrivers(b) / arrival-count(b)`. The trace glues the first `n - 3` batches
(`pow_replay_trace`) in front of the three-batch trace of `third_batch_recycle_offset` via the
regrouping `(I ^ k) ^ n = (I ^ k) ^ (n-3) ⨾ ((I ^ k) ⨾ ((I ^ k) ⨾ (I ^ k)))`. The front
batches contribute the *same* constant recycle count before each of the final three copies, so
it cancels in the differences, leaving the three-batch offsets. -/
theorem CTA.WellSynchronized.last_batches_recycle_offset {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 3 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ n)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (i : Nat) (m₁ m₂ : Nat),
        i < 2 → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run State.initial ((I ^ k) ^ n)) τ
            ⟨t, (n - 3 + i) * ((I ^ k).prog t).length + j⟩ m₁ →
        IsTimeOf (Config.run State.initial ((I ^ k) ^ n)) τ
            ⟨t, (n - 3 + i + 1) * ((I ^ k).prog t).length + j⟩ m₂ →
        recycleCount b τ (m₂ - 1)
          = recycleCount b τ (m₁ - 1) + k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  have hWSA : (I ^ I.loopK h).WellSynchronized := by
    have := hWS 1 (le_refl 1) (by omega); rwa [CTA.pow_one] at this
  have hWSAA : ((I ^ I.loopK h).seq (I ^ I.loopK h) rfl).WellSynchronized := by
    have := hWS 2 (by omega) (by omega); rwa [CTA.pow_two_eq_seq] at this
  obtain ⟨t₁, ht₁⟩ := hWSA.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  -- three-batch trace with the per-instruction offsets (the hard case)
  obtain ⟨τAAA, hτAAA, hrecAAA⟩ := CTA.WellSynchronized.third_batch_recycle_offset h rfl hWSA hWSAA
  -- `(n-3)`-fold replay of the first batches
  obtain ⟨tC, htC, htCL⟩ := pow_replay_trace (I ^ I.loopK h) ht₁ ht₁L (n - 3)
  set A := I ^ I.loopK h with hA
  obtain ⟨hglue, -, hsnd⟩ :=
    glue_trace (B := A.seq (A.seq A rfl) rfl) (CTA.pow_ids A (n - 3)) htC htCL hτAAA
  have hAn : A ^ n = (A ^ (n - 3)).seq (A.seq (A.seq A rfl) rfl) (CTA.pow_ids A (n - 3)) :=
    CTA.pow_regroup_last_three A hn
  refine ⟨tC.dropLast.map (Config.seqLift (A ^ (n - 3)) (A.seq (A.seq A rfl) rfl)) ++ τAAA.tail,
    ?_, ?_⟩
  · rw [hAn]; exact hglue
  · intro t j c b par i m₁ m₂ hi2 hcj hbr ht1 ht2
    obtain ⟨hjL, -⟩ := List.getElem?_eq_some_iff.mp hcj
    have hSucc : IsSuccessfulTraceFrom (Config.run State.initial (A ^ n))
        (tC.dropLast.map (Config.seqLift (A ^ (n - 3)) (A.seq (A.seq A rfl) rfl))
          ++ τAAA.tail) := by
      rw [hAn]; exact hglue
    have hCLen : ((A ^ (n - 3)).prog t).length = (n - 3) * (A.prog t).length :=
      CTA.pow_prog_length A (n - 3) t
    have hAAAlen : ((A.seq (A.seq A rfl) rfl).prog t).length
        = (A.prog t).length + ((A.prog t).length + (A.prog t).length) := by
      change (A.prog t ++ (A.prog t ++ A.prog t)).length = _
      rw [List.length_append, List.length_append]
    have hnL : n * (A.prog t).length
        = (n - 3) * (A.prog t).length
          + ((A.prog t).length + ((A.prog t).length + (A.prog t).length)) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.add_mul]
      omega
    have hnLen : ((A ^ n).prog t).length = n * (A.prog t).length := CTA.pow_prog_length A n t
    have hprogeq : (A ^ n).prog t = (A ^ (n - 3)).prog t ++ (A.seq (A.seq A rfl) rfl).prog t :=
      congrFun (congrArg CTA.prog hAn) t
    -- transport a three-batch instruction time into the `n`-batch trace (shifted by the prefix)
    have transport : ∀ (q M' : Nat), q < ((A.seq (A.seq A rfl) rfl).prog t).length →
        IsTimeOf (Config.run State.initial (A.seq (A.seq A rfl) rfl)) τAAA ⟨t, q⟩ M' →
        IsTimeOf (Config.run State.initial (A ^ n))
          (tC.dropLast.map (Config.seqLift (A ^ (n - 3)) (A.seq (A.seq A rfl) rfl)) ++ τAAA.tail)
          ⟨t, (n - 3) * (A.prog t).length + q⟩ ((tC.length - 2) + M') := by
      intro q M' hq hT'
      obtain ⟨-, -, j', D, D', hM'eq, hDj, hDj1, hDprog, hD'prog⟩ := hT'
      rw [hAAAlen] at hq
      refine ⟨hSucc.1, ?_, (tC.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
      · change (n - 3) * (A.prog t).length + q < ((A ^ n).prog t).length
        rw [hnLen, hnL]; omega
      · exact (hsnd j').trans hDj
      · rw [show (tC.length - 2) + j' + 1 = (tC.length - 2) + (j' + 1) from by omega]
        exact (hsnd (j' + 1)).trans hDj1
      · change D.progOf t = ((A ^ n).prog t).drop ((n - 3) * (A.prog t).length + q)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 3) * (A.prog t).length + q - ((A ^ (n - 3)).prog t).length = q from by
            rw [hCLen]; omega]
        exact hDprog
      · change D'.progOf t = ((A ^ n).prog t).drop ((n - 3) * (A.prog t).length + q + 1)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 3) * (A.prog t).length + q + 1 - ((A ^ (n - 3)).prog t).length = q + 1 from by
            rw [hCLen]; omega]
        exact hD'prog
    -- the two corresponding instruction times in the three-batch trace
    obtain ⟨sdAAA, hAAAlast⟩ := hτAAA.2
    have hb1 : i * (A.prog t).length + j < ((A.seq (A.seq A rfl) rfl).prog t).length := by
      rw [hAAAlen]
      have hle : i * (A.prog t).length ≤ 1 * (A.prog t).length := Nat.mul_le_mul_right _ (by omega)
      simp only [Nat.one_mul] at hle; omega
    have hb2 : (i + 1) * (A.prog t).length + j < ((A.seq (A.seq A rfl) rfl).prog t).length := by
      rw [hAAAlen]
      have hle : (i + 1) * (A.prog t).length ≤ 2 * (A.prog t).length :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨m₁', hT1'⟩ := exists_time_of_ends_done hτAAA.1 hAAAlast
      (η := ⟨t, i * (A.prog t).length + j⟩) hb1
    obtain ⟨m₂', hT2'⟩ := exists_time_of_ends_done hτAAA.1 hAAAlast
      (η := ⟨t, (i + 1) * (A.prog t).length + j⟩) hb2
    have hΔAAA := hrecAAA t j c b par i m₁' m₂' hi2 hcj hbr hT1' hT2'
    have hidx1 : (n - 3 + i) * (A.prog t).length + j
        = (n - 3) * (A.prog t).length + (i * (A.prog t).length + j) := by
      rw [Nat.add_mul]; omega
    have hidx2 : (n - 3 + i + 1) * (A.prog t).length + j
        = (n - 3) * (A.prog t).length + ((i + 1) * (A.prog t).length + j) := by
      rw [show n - 3 + i + 1 = (n - 3) + (i + 1) from by omega, Nat.add_mul]; omega
    have hTr1 := transport (i * (A.prog t).length + j) m₁' hb1 hT1'
    have hTr2 := transport ((i + 1) * (A.prog t).length + j) m₂' hb2 hT2'
    rw [hidx1] at ht1
    rw [hidx2] at ht2
    have hm₁ : m₁ = (tC.length - 2) + m₁' := IsTimeOf.unique ht1 hTr1
    have hm₂ : m₂ = (tC.length - 2) + m₂' := IsTimeOf.unique ht2 hTr2
    have hm1' : 1 ≤ m₁' := by obtain ⟨_, _, _, he, _⟩ := hT1'.2.2; omega
    have hm2' : 1 ≤ m₂' := by obtain ⟨_, _, _, he, _⟩ := hT2'.2.2; omega
    have e1 : m₁ - 1 = (tC.length - 2) + (m₁' - 1) := by rw [hm₁]; omega
    have e2 : m₂ - 1 = (tC.length - 2) + (m₂' - 1) := by rw [hm₂]; omega
    rw [e1, e2, recycleCount_suffix b hsnd, recycleCount_suffix b hsnd, hΔAAA]
    omega

/-- **Consecutive-batch generation offset for the last three batches of `(I ^ k) ^ n`.**
*(Helper for `last_batch_hb_across`.)* The `n`-batch generalization of `third_batch_gen_offset`:
for `(I ^ k) ^ n` (`n ≥ 3`) there is a successful trace `τ` whose recovered generation mapping
(`pointGen`) increases by exactly `k · arrivers(b) / arrival-count(b)` from each of the last
three batches to the next: for a barrier body instruction `⟨t, j⟩` and `i < 2`, the generation
of the copy in batch `n - 3 + i + 1` exceeds that of the copy in batch `n - 3 + i` by one
batch's worth of recycles. Supplies both adjacent-batch offsets along a *single* trace, which
is what `last_batch_hb_across` needs to shift barrier (`R`) edges by one batch. -/
theorem CTA.WellSynchronized.last_batches_gen_offset_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 3 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ n)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (i : Nat),
        i < 2 → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        pointGen ((I ^ k) ^ n) τ ⟨t, (n - 3 + i + 1) * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ n) τ ⟨t, (n - 3 + i) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b := by
  obtain ⟨τ, hτ, hrec⟩ := CTA.WellSynchronized.last_batches_recycle_offset h hk hn hWS
  refine ⟨τ, hτ, ?_⟩
  intro t j c b par i hi2 hcj hbr
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hcj
  obtain ⟨sd, hlast⟩ := hτ.2
  have hnLen : (((I ^ k) ^ n).prog t).length = n * ((I ^ k).prog t).length :=
    CTA.pow_prog_length (I ^ k) n t
  have hcmdat : ∀ q, q < n →
      (((I ^ k) ^ n).prog t)[q * ((I ^ k).prog t).length + j]? = some c := by
    intro q hq
    have hqLen : (((I ^ k) ^ q).prog t).length = q * ((I ^ k).prog t).length :=
      CTA.pow_prog_length (I ^ k) q t
    have hsplit : ((I ^ k) ^ n).prog t = ((I ^ k) ^ q).prog t ++ ((I ^ k) ^ (n - q)).prog t := by
      conv_lhs => rw [show n = q + (n - q) from by omega]
      rw [CTA.pow_add_prog]
    rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
      show q * ((I ^ k).prog t).length + j - q * ((I ^ k).prog t).length = j from by omega,
      show n - q = (n - q - 1) + 1 from by omega, CTA.pow_succ_prog,
      List.getElem?_append_left hjlt]
    exact hcj
  have hple : ∀ p, p ≤ n - 1 →
      p * ((I ^ k).prog t).length + j < (((I ^ k) ^ n).prog t).length := by
    intro p hp
    rw [hnLen]
    have hle : p * ((I ^ k).prog t).length ≤ (n - 1) * ((I ^ k).prog t).length :=
      Nat.mul_le_mul_right _ hp
    have hn1 : n * ((I ^ k).prog t).length
        = (n - 1) * ((I ^ k).prog t).length + ((I ^ k).prog t).length := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.add_mul]
      omega
    omega
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  obtain ⟨m₁, ht1⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, (n - 3 + i) * ((I ^ k).prog t).length + j⟩) (hple (n - 3 + i) (by omega))
  obtain ⟨m₂, ht2⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, (n - 3 + i + 1) * ((I ^ k).prog t).length + j⟩) (hple (n - 3 + i + 1) (by omega))
  have hcmd1 : ((I ^ k) ^ n).cmdAt ⟨t, (n - 3 + i) * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat (n - 3 + i) (by omega)
  have hcmd2 : ((I ^ k) ^ n).cmdAt ⟨t, (n - 3 + i + 1) * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat (n - 3 + i + 1) (by omega)
  have hg1 : pointGen ((I ^ k) ^ n) τ ⟨t, (n - 3 + i) * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₁ - 1) + 1 := by
    simp only [pointGen, hcmd1, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht1]
  have hg2 : pointGen ((I ^ k) ^ n) τ ⟨t, (n - 3 + i + 1) * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₂ - 1) + 1 := by
    simp only [pointGen, hcmd2, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht2]
  rw [hg1, hg2, hrec t j c b par i m₁ m₂ hi2 hcj hbr ht1 ht2]; omega

/-- **Lemma 4.2, conclusion 2 (across batches), `n`-batch case (last three batches).**
*Stated, not yet proved.* The `n`-batch generalization of `second_batch_hb_across`: for the
`n`-fold composition `(I ^ k) ^ n` (`n ≥ 3`), there is a successful trace `τ` along which the
happens-before edge running from the **second-to-last** batch into the **last** batch agrees
with the corresponding edge from the **third-to-last** batch into the **second-to-last**.
Those are two distinct adjacent-batch pairs, so the statement genuinely refers to the last
*three* batches (it cannot be expressed on only two), which is why `n ≥ 3`.

With `L = ((I ^ k).prog _).length`, the copy of body instruction `⟨t, j⟩` (`j < L`) in batch
`i` (0-indexed) is `⟨t, i * L + j⟩`. The claim relates the edge from batch `n - 2`'s copy of
`⟨t₁, j₁⟩` (at index `(n - 2) · L + j₁`) into batch `n - 1`'s copy of `⟨t₂, j₂⟩` (at index
`(n - 1) · L + j₂`) with the edge from batch `n - 3`'s copy of `⟨t₁, j₁⟩` (at index
`(n - 3) · L + j₁`) into batch `n - 2`'s copy of `⟨t₂, j₂⟩` (at index `(n - 2) · L + j₂`).

`second_batch_hb_across` is the `n = 3` instance (`n - 3 = 0`, `n - 2 = 1`, `n - 1 = 2`, and
`(I ^ k) ^ 3 = ((I ^ k) ⨾ (I ^ k)) ⨾ (I ^ k)`). The hypothesis is the
`CTA.BatchesWellSynchronized` family — every batch-prefix `(I ^ k) ^ m` (`1 ≤ m ≤ n`) is
well-synchronized — generalizing the three `WellSynchronized` assumptions of
`second_batch_hb_across`. As there, the statement is for *all* instruction pairs, not only
barrier instructions (`R` orders read/write instructions too, via program order and the sync
edges).

This is the **`M`-parametric core**: it takes the `last_batches_replay_bundle` outputs
`τ, hτ, hoffset, hL, hU` as hypotheses, so it can be reused at prefix exponents. -/
theorem CTA.WellSynchronized.last_batch_hb_across_core {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 2 ≤ n)
    (τ : List Config)
    (_hτ : IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ)
    (hoffset : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
        1 ≤ p → p ≤ n → ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, p * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ (n + 1)) τ ⟨t, (p - 1) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b)
    (hL : ∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers b / I.arrivalCount h b) + 1
          ≤ pointGen ((I ^ k) ^ (n + 1)) τ η)
    (hU : ∀ (η : ProgPoint) (b : Barrier) (par : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt η = some (Cmd.sync b par) →
        pointGen ((I ^ k) ^ (n + 1)) τ η
          ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
              * (k * I.arrivers b / I.arrivalCount h b)) :
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, n * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 2) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩) := by
  set A := I ^ k with hA
  -- arithmetic relating the batch boundaries `n-2, n-1, n, n+1` for a fixed thread
  have hE2 : ∀ (t : ThreadId), (n - 1) * (A.prog t).length
      = (n - 2) * (A.prog t).length + (A.prog t).length := by
    intro t; rw [show n - 1 = (n - 2) + 1 from by omega, Nat.add_mul, Nat.one_mul]
  have hE1 : ∀ (t : ThreadId), n * (A.prog t).length
      = (n - 2) * (A.prog t).length + ((A.prog t).length + (A.prog t).length) := by
    intro t
    conv_lhs => rw [show n = (n - 2) + 2 from by omega, Nat.add_mul]
    omega
  have hE0 : ∀ (t : ThreadId), (n + 1) * (A.prog t).length
      = (n - 2) * (A.prog t).length
        + ((A.prog t).length + (A.prog t).length + (A.prog t).length) := by
    intro t
    conv_lhs => rw [show n + 1 = (n - 2) + 3 from by omega, Nat.add_mul]
    omega
  have hPlen : ∀ (t : ThreadId), ((A ^ (n + 1)).prog t).length = (n + 1) * (A.prog t).length :=
    fun t => CTA.pow_prog_length A (n + 1) t
  -- the command at the copy of body instruction `j` in batch `p` is the body command
  have hcmdbatch : ∀ (t : ThreadId) (j p : Nat), j < (A.prog t).length → p < n + 1 →
      (A ^ (n + 1)).cmdAt ⟨t, p * (A.prog t).length + j⟩ = (A.prog t)[j]? := by
    intro t j p hj hp
    have hqLen : ((A ^ p).prog t).length = p * (A.prog t).length := CTA.pow_prog_length A p t
    have hsplit : (A ^ (n + 1)).prog t = (A ^ p).prog t ++ (A ^ (n + 1 - p)).prog t := by
      conv_lhs => rw [show n + 1 = p + (n + 1 - p) from by omega]
      rw [CTA.pow_add_prog]
    change ((A ^ (n + 1)).prog t)[p * (A.prog t).length + j]? = (A.prog t)[j]?
    rw [hsplit, List.getElem?_append_right (by rw [hqLen]; omega), hqLen,
      show p * (A.prog t).length + j - p * (A.prog t).length = j from by omega,
      show n + 1 - p = (n + 1 - p - 1) + 1 from by omega, CTA.pow_succ_prog,
      List.getElem?_append_left hj]
  -- program points of the lower (batches n-2, n-1) and upper (batches n-1, n) regions
  have hppLow : ∀ (t : ThreadId) (idx : Nat),
      (n - 2) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (⟨t, idx⟩ : ProgPoint) ∈ (A ^ (n + 1)).progPoints := by
    intro t idx hlo hhi
    rw [mem_progPoints_iff]
    refine ⟨?_, ?_⟩
    · change t ∈ (A ^ (n + 1)).ids
      rw [CTA.pow_ids]
      exact mem_ids_of_idx_lt A (show (0 : Nat) < (A.prog t).length by have := hE1 t; omega)
    · change idx < ((A ^ (n + 1)).prog t).length
      rw [hPlen]; have := hE0 t; have := hE1 t; omega
  have hppUp : ∀ (t : ThreadId) (idx : Nat),
      (n - 2) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (⟨t, idx + (A.prog t).length⟩ : ProgPoint) ∈ (A ^ (n + 1)).progPoints := by
    intro t idx hlo hhi
    rw [mem_progPoints_iff]
    refine ⟨?_, ?_⟩
    · change t ∈ (A ^ (n + 1)).ids
      rw [CTA.pow_ids]
      exact mem_ids_of_idx_lt A (show (0 : Nat) < (A.prog t).length by have := hE1 t; omega)
    · change idx + (A.prog t).length < ((A ^ (n + 1)).prog t).length
      rw [hPlen]; have := hE0 t; have := hE1 t; omega
  -- commands agree under a one-batch shift inside the lower region (two batches wide)
  have hcmdA : ∀ (t : ThreadId) (idx : Nat),
      (n - 2) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (A ^ (n + 1)).cmdAt ⟨t, idx + (A.prog t).length⟩ = (A ^ (n + 1)).cmdAt ⟨t, idx⟩ := by
    intro t idx hlo hhi
    rcases Nat.lt_or_ge idx ((n - 1) * (A.prog t).length) with hcase | hcase
    · have hr : idx - (n - 2) * (A.prog t).length < (A.prog t).length := by have := hE2 t; omega
      have e1 := hcmdbatch t (idx - (n - 2) * (A.prog t).length) (n - 2) hr (by omega)
      have e2 := hcmdbatch t (idx - (n - 2) * (A.prog t).length) (n - 1) hr (by omega)
      rw [show (n - 2) * (A.prog t).length + (idx - (n - 2) * (A.prog t).length) = idx
            from by omega] at e1
      rw [show (n - 1) * (A.prog t).length + (idx - (n - 2) * (A.prog t).length)
            = idx + (A.prog t).length from by have := hE2 t; omega] at e2
      rw [e2, e1]
    · have hr : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by
        have := hE2 t; have := hE1 t; omega
      have e1 := hcmdbatch t (idx - (n - 1) * (A.prog t).length) (n - 1) hr (by omega)
      have e2 := hcmdbatch t (idx - (n - 1) * (A.prog t).length) n hr (by omega)
      rw [show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx
            from by omega] at e1
      rw [show n * (A.prog t).length + (idx - (n - 1) * (A.prog t).length)
            = idx + (A.prog t).length from by have := hE1 t; have := hE2 t; omega] at e2
      rw [e2, e1]
  -- **Generation neighbour offset (NEIGHBOR form).** Shifting a lower barrier point up by one
  -- batch adds `Δ` to its generation; from the bundle, casing on which of the two lower batches.
  have hgen : ∀ (t : ThreadId) (idx : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
      (n - 2) * (A.prog t).length ≤ idx → idx < n * (A.prog t).length →
      (A ^ (n + 1)).cmdAt ⟨t, idx⟩ = some c → Cmd.barrierRef c = some (b, par) →
      pointGen (A ^ (n + 1)) τ ⟨t, idx + (A.prog t).length⟩
        = pointGen (A ^ (n + 1)) τ ⟨t, idx⟩ + k * I.arrivers b / I.arrivalCount h b := by
    intro t idx c b par hlo hhi hcmd hbr
    rcases Nat.lt_or_ge idx ((n - 1) * (A.prog t).length) with hcase | hcase
    · -- batch n-2 (lower copy of the lower region), shift to batch n-1
      have hr : idx - (n - 2) * (A.prog t).length < (A.prog t).length := by have := hE2 t; omega
      have hbody : (A.prog t)[idx - (n - 2) * (A.prog t).length]? = some c := by
        have e := hcmdbatch t (idx - (n - 2) * (A.prog t).length) (n - 2) hr (by omega)
        rw [show (n - 2) * (A.prog t).length + (idx - (n - 2) * (A.prog t).length) = idx
              from by omega] at e
        rw [← e]; exact hcmd
      have hh := hoffset t (idx - (n - 2) * (A.prog t).length) (n - 1) c b par
        (by omega) (by omega) hbody hbr
      rw [show (n - 1) * (A.prog t).length + (idx - (n - 2) * (A.prog t).length)
              = idx + (A.prog t).length from by have := hE2 t; omega,
          show (n - 1 - 1) * (A.prog t).length + (idx - (n - 2) * (A.prog t).length) = idx
              from by rw [show n - 1 - 1 = n - 2 from by omega]; omega] at hh
      exact hh
    · -- batch n-1 (upper copy of the lower region), shift to batch n
      have hr : idx - (n - 1) * (A.prog t).length < (A.prog t).length := by
        have := hE2 t; have := hE1 t; omega
      have hbody : (A.prog t)[idx - (n - 1) * (A.prog t).length]? = some c := by
        have e := hcmdbatch t (idx - (n - 1) * (A.prog t).length) (n - 1) hr (by omega)
        rw [show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx
              from by omega] at e
        rw [← e]; exact hcmd
      have hh := hoffset t (idx - (n - 1) * (A.prog t).length) n c b par
        (by omega) (le_refl n) hbody hbr
      rw [show n * (A.prog t).length + (idx - (n - 1) * (A.prog t).length)
              = idx + (A.prog t).length from by have := hE1 t; have := hE2 t; omega,
          show (n - 1) * (A.prog t).length + (idx - (n - 1) * (A.prog t).length) = idx
              from by omega] at hh
      exact hh
  -- **Edge shift.** An `initRelation` edge between two lower-region points exists iff the edge
  -- between their one-batch-shifted copies does (barrier edges via generation equality, `hgen`).
  have hshift : ∀ (a b : ProgPoint),
      (n - 2) * (A.prog a.thread).length ≤ a.idx → a.idx < n * (A.prog a.thread).length →
      (n - 2) * (A.prog b.thread).length ≤ b.idx → b.idx < n * (A.prog b.thread).length →
      ((a, b) ∈ initRelation (A ^ (n + 1)) τ ↔
        (⟨a.thread, a.idx + (A.prog a.thread).length⟩,
          ⟨b.thread, b.idx + (A.prog b.thread).length⟩) ∈ initRelation (A ^ (n + 1)) τ) := by
    intro a b haLo haHi hbLo hbHi
    obtain ⟨s₁, i₁⟩ := a
    obtain ⟨s₂, i₂⟩ := b
    dsimp only at haLo haHi hbLo hbHi
    rw [mem_initRelation_iff, mem_initRelation_iff]
    constructor
    · rintro (⟨_, _, heq⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        refine Or.inl ⟨hppUp s₂ i₁ haLo haHi, ?_, ?_⟩
        · change i₁ + (A.prog s₂).length + 1 < ((A ^ (n + 1)).prog s₂).length
          rw [hPlen]; have := hE0 s₂; have := hE1 s₂; omega
        · change (⟨s₂, i₁ + 1 + (A.prog s₂).length⟩ : ProgPoint)
              = ⟨s₂, i₁ + (A.prog s₂).length + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · refine Or.inr (Or.inl
          ⟨bb, par, hppUp s₁ i₁ haLo haHi, hppUp s₂ i₂ hbLo hbHi, ?_, ?_, ?_⟩)
        · rw [hcmdA s₁ i₁ haLo haHi]; exact hc1
        · rw [hcmdA s₂ i₂ hbLo hbHi]; exact hc2
        · rw [hgen s₁ i₁ _ bb par haLo haHi hc1 rfl, hgen s₂ i₂ _ bb par hbLo hbHi hc2 rfl, hg]
      · refine Or.inr (Or.inr
          ⟨bb, par, hppUp s₁ i₁ haLo haHi, hppUp s₂ i₂ hbLo hbHi, ?_, ?_, ?_⟩)
        · rw [hcmdA s₁ i₁ haLo haHi]; exact hc1
        · rw [hcmdA s₂ i₂ hbLo hbHi]; exact hc2
        · rw [hgen s₁ i₁ _ bb par haLo haHi hc1 rfl, hgen s₂ i₂ _ bb par hbLo hbHi hc2 rfl, hg]
    · rintro (⟨_, _, heq⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩ | ⟨bb, par, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, hidx⟩ := heq
        refine Or.inl ⟨hppLow s₂ i₁ haLo haHi, ?_, ?_⟩
        · change i₁ + 1 < ((A ^ (n + 1)).prog s₂).length
          rw [hPlen]; have := hE0 s₂; have := hE1 s₂; omega
        · change (⟨s₂, i₂⟩ : ProgPoint) = ⟨s₂, i₁ + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · have he1 : (A ^ (n + 1)).cmdAt ⟨s₁, i₁⟩ = some (Cmd.arrive bb par) := by
          rw [← hcmdA s₁ i₁ haLo haHi]; exact hc1
        have he2 : (A ^ (n + 1)).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb par) := by
          rw [← hcmdA s₂ i₂ hbLo hbHi]; exact hc2
        refine Or.inr (Or.inl
          ⟨bb, par, hppLow s₁ i₁ haLo haHi, hppLow s₂ i₂ hbLo hbHi, he1, he2, ?_⟩)
        rw [hgen s₁ i₁ _ bb par haLo haHi he1 rfl, hgen s₂ i₂ _ bb par hbLo hbHi he2 rfl] at hg
        omega
      · have he1 : (A ^ (n + 1)).cmdAt ⟨s₁, i₁⟩ = some (Cmd.sync bb par) := by
          rw [← hcmdA s₁ i₁ haLo haHi]; exact hc1
        have he2 : (A ^ (n + 1)).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb par) := by
          rw [← hcmdA s₂ i₂ hbLo hbHi]; exact hc2
        refine Or.inr (Or.inr
          ⟨bb, par, hppLow s₁ i₁ haLo haHi, hppLow s₂ i₂ hbLo hbHi, he1, he2, ?_⟩)
        rw [hgen s₁ i₁ _ bb par haLo haHi he1 rfl, hgen s₂ i₂ _ bb par hbLo hbHi he2 rfl] at hg
        omega
  -- **No backward edges into the last batch** (`no_backward_edge` at `p := n`).
  have NB_up : ¬ ∃ s d : ProgPoint, happensBefore (A ^ (n + 1)) τ s d ∧
      (n * (A.prog s.thread).length ≤ s.idx ∧ s.idx < (n + 1) * (A.prog s.thread).length) ∧
      d.idx < n * (A.prog d.thread).length := by
    rintro ⟨s, d, hR, ⟨h1, _⟩, h3⟩
    exact no_backward_edge h hk hL hU n s d hR h1 h3
  -- **No backward edges from the last two batches** (`no_backward_edge` at `p := n - 1`).
  have NB_mid : ¬ ∃ s d : ProgPoint, happensBefore (A ^ (n + 1)) τ s d ∧
      ((n - 1) * (A.prog s.thread).length ≤ s.idx ∧ s.idx < (n + 1) * (A.prog s.thread).length) ∧
      d.idx < (n - 1) * (A.prog d.thread).length := by
    rintro ⟨s, d, hR, ⟨h1, _⟩, h3⟩
    exact no_backward_edge h hk hL hU (n - 1) s d hR h1 h3
  -- **No backward edges from the last three batches** (`no_backward_edge` at `p := n - 2`);
  -- vacuous for `n = 2`, where there is nothing below.
  have NB_lo : ¬ ∃ s d : ProgPoint, happensBefore (A ^ (n + 1)) τ s d ∧
      ((n - 2) * (A.prog s.thread).length ≤ s.idx ∧ s.idx < (n + 1) * (A.prog s.thread).length) ∧
      d.idx < (n - 2) * (A.prog d.thread).length := by
    rintro ⟨s, d, hR, ⟨h1, _⟩, h3⟩
    exact no_backward_edge h hk hL hU (n - 2) s d hR h1 h3
  intro t₁ t₂ j₁ j₂ hj₁ hj₂
  -- **Confinement (lower).** A path landing in batches `n-2, n-1` stays there.
  have confLow : ∀ (c : ProgPoint),
      happensBefore (A ^ (n + 1)) τ c ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩ →
      ((n - 2) * (A.prog c.thread).length ≤ c.idx ∧ c.idx < n * (A.prog c.thread).length) →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 2) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < n * (A.prog x.thread).length) ∧
          ((n - 2) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < n * (A.prog y.thread).length))
        c ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩ := by
    intro c hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxL
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyL : (n - 2) * (A.prog y.thread).length ≤ y.idx ∧
          y.idx < n * (A.prog y.thread).length := by
        refine ⟨?_, ?_⟩
        · by_contra hcon
          exact NB_lo ⟨x, y, Relation.ReflTransGen.single hxy,
            ⟨hxL.1, by have := hE0 x.thread; have := hE1 x.thread; omega⟩, by omega⟩
        · by_contra hcon
          have hdb : (n - 1) * (A.prog t₂).length + j₂ < n * (A.prog t₂).length := by
            have := hE1 t₂; have := hE2 t₂; omega
          exact NB_up ⟨y, ⟨t₂, (n - 1) * (A.prog t₂).length + j₂⟩, hyd,
            ⟨by omega, hypp.2⟩, hdb⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxL, hyL⟩ (ih hyL)
  -- **Confinement (upper).** A path leaving batches `n-1, n` stays there.
  have confUp : ∀ (c d : ProgPoint), happensBefore (A ^ (n + 1)) τ c d →
      ((n - 1) * (A.prog c.thread).length ≤ c.idx ∧ c.idx < (n + 1) * (A.prog c.thread).length) →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 1) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < (n + 1) * (A.prog x.thread).length) ∧
          ((n - 1) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < (n + 1) * (A.prog y.thread).length))
        c d := by
    intro c d hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxU
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyU : (n - 1) * (A.prog y.thread).length ≤ y.idx ∧
          y.idx < (n + 1) * (A.prog y.thread).length := by
        refine ⟨?_, hypp.2⟩
        by_contra hcon
        exact NB_mid ⟨x, y, Relation.ReflTransGen.single hxy, hxU, by omega⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxU, hyU⟩ (ih hyU)
  constructor
  · -- forward: confine the upper edge to batches n-1, n, shift down to batches n-2, n-1
    intro hHB
    have hcU : (n - 1) * (A.prog t₁).length ≤ (n - 1) * (A.prog t₁).length + j₁ ∧
        (n - 1) * (A.prog t₁).length + j₁ < (n + 1) * (A.prog t₁).length :=
      ⟨Nat.le_add_right _ _, by have := hE0 t₁; have := hE2 t₁; omega⟩
    have hLow : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 2) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < n * (A.prog x.thread).length) ∧
          ((n - 2) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < n * (A.prog y.thread).length))
        ⟨t₁, (n - 1) * (A.prog t₁).length + j₁ - (A.prog t₁).length⟩
        ⟨t₂, n * (A.prog t₂).length + j₂ - (A.prog t₂).length⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, η.idx - (A.prog η.thread).length⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haU, hbU⟩ := hab
          dsimp only at haU hbU
          have ha2 := hE2 at'; have ha1 := hE1 at'; have ha0 := hE0 at'
          have hb2 := hE2 bt; have hb1 := hE1 bt; have hb0 := hE0 bt
          have hp1lo : (n - 2) * (A.prog at').length ≤ ai - (A.prog at').length := by omega
          have hp1hi : ai - (A.prog at').length < n * (A.prog at').length := by omega
          have hp2lo : (n - 2) * (A.prog bt).length ≤ bi - (A.prog bt).length := by omega
          have hp2hi : bi - (A.prog bt).length < n * (A.prog bt).length := by omega
          refine ⟨?_, ⟨hp1lo, hp1hi⟩, ⟨hp2lo, hp2hi⟩⟩
          rw [hshift ⟨at', ai - (A.prog at').length⟩ ⟨bt, bi - (A.prog bt).length⟩
              hp1lo hp1hi hp2lo hp2hi,
            show ai - (A.prog at').length + (A.prog at').length = ai from by omega,
            show bi - (A.prog bt).length + (A.prog bt).length = bi from by omega]
          exact hab')
        (confUp ⟨t₁, (n - 1) * (A.prog t₁).length + j₁⟩
          ⟨t₂, n * (A.prog t₂).length + j₂⟩ hHB hcU)
    rw [show (n - 1) * (A.prog t₁).length + j₁ - (A.prog t₁).length
          = (n - 2) * (A.prog t₁).length + j₁ from by have := hE2 t₁; omega,
        show n * (A.prog t₂).length + j₂ - (A.prog t₂).length
          = (n - 1) * (A.prog t₂).length + j₂ from by have := hE1 t₂; have := hE2 t₂; omega] at hLow
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hLow
  · -- backward: confine the lower edge to batches n-2, n-1, shift up to batches n-1, n
    intro hHB
    have hcL : (n - 2) * (A.prog t₁).length ≤ (n - 2) * (A.prog t₁).length + j₁ ∧
        (n - 2) * (A.prog t₁).length + j₁ < n * (A.prog t₁).length :=
      ⟨Nat.le_add_right _ _, by have := hE1 t₁; omega⟩
    have hUp : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A ^ (n + 1)) τ ∧
          ((n - 1) * (A.prog x.thread).length ≤ x.idx ∧
            x.idx < (n + 1) * (A.prog x.thread).length) ∧
          ((n - 1) * (A.prog y.thread).length ≤ y.idx ∧
            y.idx < (n + 1) * (A.prog y.thread).length))
        ⟨t₁, (n - 2) * (A.prog t₁).length + j₁ + (A.prog t₁).length⟩
        ⟨t₂, (n - 1) * (A.prog t₂).length + j₂ + (A.prog t₂).length⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, η.idx + (A.prog η.thread).length⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haL, hbL⟩ := hab
          dsimp only at haL hbL
          have ha2 := hE2 at'; have ha1 := hE1 at'; have ha0 := hE0 at'
          have hb2 := hE2 bt; have hb1 := hE1 bt; have hb0 := hE0 bt
          refine ⟨(hshift ⟨at', ai⟩ ⟨bt, bi⟩ haL.1 haL.2 hbL.1 hbL.2).mp hab', ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
          · change (n - 1) * (A.prog at').length ≤ ai + (A.prog at').length
            omega
          · change ai + (A.prog at').length < (n + 1) * (A.prog at').length
            omega
          · change (n - 1) * (A.prog bt).length ≤ bi + (A.prog bt).length
            omega
          · change bi + (A.prog bt).length < (n + 1) * (A.prog bt).length
            omega)
        (confLow ⟨t₁, (n - 2) * (A.prog t₁).length + j₁⟩ hHB hcL)
    rw [show (n - 2) * (A.prog t₁).length + j₁ + (A.prog t₁).length
          = (n - 1) * (A.prog t₁).length + j₁ from by have := hE2 t₁; omega,
        show (n - 1) * (A.prog t₂).length + j₂ + (A.prog t₂).length
          = n * (A.prog t₂).length + j₂ from by have := hE1 t₂; have := hE2 t₂; omega] at hUp
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hUp

theorem CTA.WellSynchronized.last_batch_hb_across_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 2 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ (n + 1))) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, n * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore ((I ^ k) ^ (n + 1)) τ
              ⟨t₁, (n - 2) * ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩) := by
  obtain ⟨τ, hτ, hoffset, hL, hU, -⟩ :=
    CTA.WellSynchronized.last_batches_replay_bundle h hk (by omega) hWS
  exact ⟨τ, hτ, last_batch_hb_across_core h hk hn τ hτ hoffset hL hU⟩

/-- **Lemma 1 (§3 "Weft++").** The strengthened inductive step that yields Theorem 3 — every
iteration count of a singly-nested loop is well-synchronized.

Paper statement: *Assume that for some `n`, `∀ i ∈ [0, n], WS(I₀ᵏ; … ; Iᵢᵏ)`, where `k` is
the §1 iteration count. Then `WS(I₀ᵏ; … ; Iₙᵏ; I_{n+1}ᵏ)`.*

A "batch" `Iⱼᵏ` is the loop body `I` unrolled `k = I.loopK h` times, written `I ^ k`, and `m`
batches in sequence are `(I ^ k) ^ m`. So the hypothesis — every prefix of `1 … n+1` batches is
well-synchronized — is `(I ^ k).BatchesWellSynchronized (n + 1)`, and the conclusion is
well-synchronization of the `(n + 2)`-batch program `(I ^ k) ^ (n + 2)`. -/
theorem CTA.WellSynchronized.batches_inductive_step_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : n >= 2)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ((I ^ k) ^ (n + 1)).WellSynchronized := by
  -- The shared replay trace `τ` of `(I^k)^(n+1)` with everything Phases C–E built on it:
  -- the consecutive-batch generation offset (`hoffset`), the (L)/(U) generation bounds
  -- (`hL`, `hU`), the prefix trace `τn` of the WS prefix `(I^k)^n` with its own offset/(L)/(U)
  -- (`hoffsetN`, `hLN`, `hUN`), generation preservation on prefix points (`hGP`), and
  -- happens-before monotonicity prefix→full (`hMONO`).
  obtain ⟨τ, hτ, hoffset, hL, hU, hUgen, τn, hτn, hoffsetN, hLN, hUN, hGP, hMONO⟩ :=
    CTA.WellSynchronized.last_batches_replay_bundle h hk (by omega) hWS
  -- **Phase G.** Close via soundness of the checker; it remains
  -- to show the checker accepts `τ`.
  refine wellSynchronized_of_check hτ ?_
  -- The WS prefix makes the *prefix* checker accept `τn` (Theorem 1 completeness direction).
  have hprefix : (CheckWellSynchronized ((I ^ k) ^ n) τn).1 = true :=
    (checkWellSynchronized_correct_impl hτn).mpr (hWS n (by omega) (le_refl n))
  -- The within/across happens-before equivalences from the cores, on the shared traces:
  --   `hWithinFull` : batches `n-1 ↔ n` of the full program `(I^k)^(n+1)` (trace `τ`);
  --   `hAcrossFull` : batches `n-1→n ↔ n-2→n-1` of the full program (trace `τ`);
  --   `hWithinPre`  : batches `n-2 ↔ n-1` of the prefix program `(I^k)^n` (trace `τn`).
  have hWithinFull := CTA.WellSynchronized.last_batch_hb_within_core h hk
    (show 1 ≤ n by omega) τ hτ hoffset hL hU
  have hAcrossFull := CTA.WellSynchronized.last_batch_hb_across_core h hk
    (show 2 ≤ n by omega) τ hτ hoffset hL hU
  -- The prefix within-core at `N := n - 1`: program `(I^k)^((n-1)+1) = (I^k)^n`, trace `τn`.
  -- We pick a witness `m` with `n = m + 1`, so the prefix program `(I^k)^n = (I^k)^(m+1)` is
  -- literally the core's `(N+1)`-program with `N := m`; its last two batches are `m-1 = n-2`
  -- and `m = n-1`.  The `n = m + 1` rewrite is purely local to this `have`.
  have hWithinPre : ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
      j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
      (happensBefore ((I ^ k) ^ n) τn
            ⟨t₁, (n - 2) * ((I ^ k).prog t₁).length + j₁⟩
            ⟨t₂, (n - 2) * ((I ^ k).prog t₂).length + j₂⟩
        ↔ happensBefore ((I ^ k) ^ n) τn
            ⟨t₁, (n - 1) * ((I ^ k).prog t₁).length + j₁⟩
            ⟨t₂, (n - 1) * ((I ^ k).prog t₂).length + j₂⟩) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    have hcore := CTA.WellSynchronized.last_batch_hb_within_core h hk
      (show 1 ≤ m by omega) τn hτn hoffsetN hLN hUN
    -- `(m+1)-1 = m` and `(m+1)-2 = m-1` are defeq to the core's `m` and `m-1`.
    exact hcore
  -- **Phase F.** Suppose the full checker rejects; `exists_failing_pair` exhibits a flagged
  -- line-18 pair: a barrier op `c1` on `b`, a barrier op `c2` on `b` at generation `gen c1 + 1`
  -- (`1 ≤ c2.idx`), with predecessor `c3 = ⟨c2.thread, c2.idx-1⟩` that `R` fails to order
  -- after `c1`.  We derive a contradiction by placing `(c1, c3)` in `R`.
  by_contra hcheckfalse
  rw [Bool.not_eq_true] at hcheckfalse
  obtain ⟨c1, hc1, b, hbar1, c2, hc2, hbar2, hgen, hfail⟩ :=
    exists_failing_pair hcheckfalse
  -- The `c2.idx = 0` failure mode of the strengthened checker is vacuous here: an `idx = 0`
  -- barrier op is its thread's first instruction, so on the well-synchronized prefix
  -- `(I^k)^n` it has generation `1` (`firstInstr_highGen_not_wellSynchronized'`); the bundle's
  -- prefix generation-preservation `hGP` carries that generation up to `(I^k)^(n+1)`, so `c2`
  -- cannot have generation `≥ 2` there.
  have hidxne : c2.idx ≠ 0 := by
    intro hidx0
    obtain ⟨cc2, par2, hc2cmd, hc2ref⟩ : ∃ (cc2 : Cmd) (par2 : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt c2 = some cc2 ∧ Cmd.barrierRef cc2 = some (b, par2) := by
      cases hcm : ((I ^ k) ^ (n + 1)).cmdAt c2 with
      | none => rw [hcm] at hbar2; simp at hbar2
      | some cc =>
        cases cc with
        | read g => rw [hcm] at hbar2; simp [Cmd.barrier?] at hbar2
        | write g => rw [hcm] at hbar2; simp [Cmd.barrier?] at hbar2
        | arrive bb mm =>
          rw [hcm] at hbar2; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcm] at hbar2; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
    obtain ⟨sd, hdone⟩ := hτ.2
    have hc1L : c1.idx < (((I ^ k) ^ (n + 1)).prog c1.thread).length :=
      ((mem_progPoints_iff _ c1).mp hc1).2
    obtain ⟨mc1, hmc1⟩ := exists_time_of_ends_done hτ.1 hdone hc1L
    have hge2 : 2 ≤ pointGen ((I ^ k) ^ (n + 1)) τ c2 := by
      have := isGenOf_recycleCount (isGenOf_pointGen hbar1 hmc1) hbar1 hmc1; omega
    have hc2L0 : c2.idx < (((I ^ k) ^ (n + 1)).prog c2.thread).length :=
      ((mem_progPoints_iff _ c2).mp hc2).2
    rw [CTA.pow_prog_length] at hc2L0
    have hLpos : 0 < ((I ^ k).prog c2.thread).length :=
      Nat.pos_of_ne_zero fun hL0 => by
        rw [hL0, Nat.mul_zero, hidx0] at hc2L0; exact absurd hc2L0 (lt_irrefl 0)
    have hidxlt : c2.idx < n * ((I ^ k).prog c2.thread).length := by
      rw [hidx0]; exact Nat.mul_pos (by omega) hLpos
    have htransfer := hGP c2 cc2 b par2 hidxlt hc2cmd hc2ref
    have hbase : ((I ^ k).prog c2.thread)[0]? = some cc2 := by
      have h : (((I ^ k) ^ (n + 1)).prog c2.thread)[c2.idx]? = some cc2 := hc2cmd
      rw [hidx0, CTA.pow_succ_prog, List.getElem?_append_left hLpos] at h; exact h
    have hc2cmdn : ((I ^ k) ^ n).cmdAt c2 = some cc2 := by
      obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
      change (((I ^ k) ^ n).prog c2.thread)[c2.idx]? = some cc2
      rw [hidx0, hq, CTA.pow_succ_prog, List.getElem?_append_left hLpos]; exact hbase
    have hbar2n : (((I ^ k) ^ n).cmdAt c2).bind Cmd.barrier? = some b := by
      rw [hc2cmdn]; simp only [Option.bind_some]; exact Cmd.barrier?_of_barrierRef hc2ref
    have hc2n : c2 ∈ ((I ^ k) ^ n).progPoints := by
      rw [mem_progPoints_iff]
      refine ⟨?_, by rw [hidx0, CTA.pow_prog_length]; exact Nat.mul_pos (by omega) hLpos⟩
      have := ((mem_progPoints_iff _ c2).mp hc2).1; rw [CTA.pow_ids] at this ⊢; exact this
    exact firstInstr_highGen_not_wellSynchronized' hτn (hWS n (by omega) (le_refl n)) hc2n hbar2n
      (htransfer ▸ hge2) hidx0
  obtain ⟨hidx, hc1ne3, hnotmem⟩ := hfail.resolve_right hidxne
  apply hnotmem
  rw [snd_checkWellSynchronized]
  set L1 := ((I ^ k).prog c1.thread).length with hL1
  set L2 := ((I ^ k).prog c2.thread).length with hL2
  set c3 : ProgPoint := ⟨c2.thread, c2.idx - 1⟩ with hc3
  -- `exists_failing_pair` provides `hc1ne3 : c1 ≠ c3`, so it suffices to find an HB edge.
  have hHB : happensBefore ((I ^ k) ^ (n + 1)) τ c1 c3 := by
    -- ===== Shared facts: the barrier `b` of `c1`/`c2`, its per-batch offset `δ ≥ 1`,
    -- positivity of the per-thread lengths, and the index ranges of `c1`, `c2`. =====
    -- `c2`'s command is a barrier op on `b` (decoded from `hbar2`): `cmdAt c2 = some cc2'`
    -- with `barrierRef cc2' = some (b, par2)`.
    obtain ⟨cc2', par2, hc2cmd, hc2ref⟩ : ∃ (cc2x : Cmd) (par2 : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt c2 = some cc2x ∧ Cmd.barrierRef cc2x = some (b, par2) := by
      cases hcmd2 : ((I ^ k) ^ (n + 1)).cmdAt c2 with
      | none => rw [hcmd2] at hbar2; simp at hbar2
      | some cc2 =>
        cases cc2 with
        | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | arrive bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
    -- `c1`'s command is a barrier op on `b` (decoded from `hbar1`): `cmdAt c1 = some cc1'`
    -- with `barrierRef cc1' = some (b, par1)`.
    obtain ⟨cc1', par1, hc1cmd, hc1ref⟩ : ∃ (cc1x : Cmd) (par1 : ℕ+),
        ((I ^ k) ^ (n + 1)).cmdAt c1 = some cc1x ∧ Cmd.barrierRef cc1x = some (b, par1) := by
      cases hcmd1 : ((I ^ k) ^ (n + 1)).cmdAt c1 with
      | none => rw [hcmd1] at hbar1; simp at hbar1
      | some cc1 =>
        cases cc1 with
        | read g => rw [hcmd1] at hbar1; simp [Cmd.barrier?] at hbar1
        | write g => rw [hcmd1] at hbar1; simp [Cmd.barrier?] at hbar1
        | arrive bb mm =>
          rw [hcmd1] at hbar1
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
          subst hbar1; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcmd1] at hbar1
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
          subst hbar1; exact ⟨_, mm, rfl, rfl⟩
    -- `b ∈ I.barriers`, so `δ_b = k·arrivers(b)/count(b) ≥ 1`
    have hbI : b ∈ I.barriers := mem_barriers_of_cmdAt_pow hc1cmd hc1ref
    set δ := k * I.arrivers b / I.arrivalCount h b with hδdef
    have hδ : 1 ≤ δ := one_le_delta h hk hbI
    -- index ranges and positive lengths for `c1`, `c2`
    have hc1lt : c1.idx < (((I ^ k) ^ (n + 1)).prog c1.thread).length :=
      ((mem_progPoints_iff _ c1).mp hc1).2
    have hc2lt : c2.idx < (((I ^ k) ^ (n + 1)).prog c2.thread).length :=
      ((mem_progPoints_iff _ c2).mp hc2).2
    rw [CTA.pow_prog_length] at hc1lt hc2lt
    have hL1pos : 0 < L1 := by
      rw [hL1]; rcases Nat.eq_zero_or_pos ((I ^ k).prog c1.thread).length with h0 | hp
      · rw [h0, Nat.mul_zero] at hc1lt; omega
      · exact hp
    have hL2pos : 0 < L2 := by
      rw [hL2]; rcases Nat.eq_zero_or_pos ((I ^ k).prog c2.thread).length with h0 | hp
      · rw [h0, Nat.mul_zero] at hc2lt; omega
      · exact hp
    rw [← hL1] at hc1lt; rw [← hL2] at hc2lt
    -- **Prefix-edge helper.** A prefix line-18 pair `(X, c2x)` — `X` a barrier op on `b`, `c2x`
    -- a same-barrier op of generation `gen X + 1` with `1 ≤ c2x.idx` — yields the prefix
    -- happens-before edge `X → ⟨c2x.thread, c2x.idx - 1⟩` via the prefix checker `hprefix`.
    have prefixHB : ∀ (X c2x : ProgPoint),
        (((I ^ k) ^ n).cmdAt X).bind Cmd.barrier? = some b →
        (((I ^ k) ^ n).cmdAt c2x).bind Cmd.barrier? = some b →
        pointGen ((I ^ k) ^ n) τn c2x = pointGen ((I ^ k) ^ n) τn X + 1 → 1 ≤ c2x.idx →
        happensBefore ((I ^ k) ^ n) τn X ⟨c2x.thread, c2x.idx - 1⟩ := by
      intro X c2x hbXbar hbX hgX hiX
      have hXmem : X ∈ ((I ^ k) ^ n).progPoints := by
        cases hcc : ((I ^ k) ^ n).cmdAt X with
        | none => rw [hcc] at hbXbar; simp at hbXbar
        | some cc => exact mem_progPoints_of_cmdAt _ hcc
      have hc2xmem : c2x ∈ ((I ^ k) ^ n).progPoints := by
        cases hcc : ((I ^ k) ^ n).cmdAt c2x with
        | none => rw [hcc] at hbX; simp at hbX
        | some cc => exact mem_progPoints_of_cmdAt _ hcc
      exact happensBefore_of_check hprefix hXmem hbXbar hc2xmem hbX hgX hiX
    -- ===== Pen-and-paper case analysis (paper Lemma 1, p.6), in Lean batch indices =====
    -- Case on where `c1` and `c2` come from.  `g := pointGen c1`, `pointGen c2 = g + 1`.
    by_cases hc2pre : c2.idx < n * L2
    · -- **Case A** (paper: `c1, c2 ∈ I^k_{[0,n]}`).  `c2` — hence `c1` and `c3` — lie in the
      -- prefix `(I^k)^n`.  `(c1,c2)` is a prefix line-18 pair (generations preserved by `hGP`),
      -- so `hprefix` gives `(c1,c3) ∈ R_prefix`, and `hMONO` lifts it to the full program.
      by_cases hc1pre : c1.idx < n * L1
      · -- both `c1` and `c2` (hence `c3`) lie in the prefix `(I^k)^n`
        apply hMONO
        -- commands and generations transfer to the prefix program/trace
        have hcmdc1 : ((I ^ k) ^ n).cmdAt c1 = some cc1' := by
          rw [← CTA.cmdAt_pow_succ_prefix (I ^ k) (n := n) (by rw [← hL1]; exact hc1pre)]
          exact hc1cmd
        have hbarc1 : (((I ^ k) ^ n).cmdAt c1).bind Cmd.barrier? = some b := by
          rw [hcmdc1, Option.bind_some, Cmd.barrier?_of_barrierRef hc1ref]
        have hcmdc2 : ((I ^ k) ^ n).cmdAt c2 = some cc2' := by
          rw [← CTA.cmdAt_pow_succ_prefix (I ^ k) (n := n) (by rw [← hL2]; exact hc2pre)]
          exact hc2cmd
        have hbarc2 : (((I ^ k) ^ n).cmdAt c2).bind Cmd.barrier? = some b := by
          rw [hcmdc2, Option.bind_some, Cmd.barrier?_of_barrierRef hc2ref]
        have hGPc1 := hGP c1 cc1' b par1 (by rw [← hL1]; exact hc1pre) hc1cmd hc1ref
        have hGPc2 := hGP c2 cc2' b par2 (by rw [← hL2]; exact hc2pre) hc2cmd hc2ref
        have hgenpre : pointGen ((I ^ k) ^ n) τn c2 = pointGen ((I ^ k) ^ n) τn c1 + 1 := by
          rw [← hGPc1, ← hGPc2]; exact hgen
        exact prefixHB c1 c2 hbarc1 hbarc2 hgenpre hidx
      · -- `c1 ∈ batch n` but `c2 ∈ batch < n`: impossible (generations ≥ 2 apart)
        exfalso
        push Not at hc1pre
        -- `c1`'s generation: `c1.idx / L1 ≥ n`
        have hLc1 := hL c1 cc1' b par1 hc1cmd hc1ref
        rw [← hL1, ← hδdef] at hLc1
        have hc1div : n ≤ c1.idx / L1 := (Nat.le_div_iff_mul_le hL1pos).mpr hc1pre
        have hlow : n * δ + 1 ≤ pointGen ((I ^ k) ^ (n + 1)) τ c1 := by
          have : n * δ ≤ (c1.idx / L1) * δ := Nat.mul_le_mul_right δ hc1div
          omega
        -- `c2`'s generation: `c2.idx / L2 ≤ n - 1`
        have hUc2 := hUgen c2 cc2' b par2 hc2cmd hc2ref
        rw [← hL2, ← hδdef] at hUc2
        have hc2div : c2.idx / L2 ≤ n - 1 := by
          have : c2.idx / L2 < n := (Nat.div_lt_iff_lt_mul hL2pos).mpr hc2pre
          omega
        have hup : pointGen ((I ^ k) ^ (n + 1)) τ c2 ≤ n * δ := by
          have hle : (c2.idx / L2 + 1) * δ ≤ n * δ := Nat.mul_le_mul_right δ (by omega)
          omega
        -- `gen c2 = gen c1 + 1 ≥ n*δ + 2`, contradicting `gen c2 ≤ n*δ`
        omega
    · -- `c2` lies in the last batch `n`.
      by_cases hc1n : n * L1 ≤ c1.idx
      · -- **Case C** (paper: `c1, c2 ∈ I^k_{n+1}`).  Both in the last batch.
        by_cases hc3n : n * L2 ≤ c2.idx - 1
        · -- C-ii: `c3 ∈ batch n`.  The within-batch-`n` edge `c1 → c3` is the up-shift of a
          -- batch-`(n-1)` prefix edge (`last_batch_hb_within`); discharge that by `hprefix` +
          -- `hMONO`.
          push Not at hc2pre
          -- batch-boundary expansions so `omega` can compare batch indices `n-1, n, n+1`
          have e1 : (n + 1) * L1 = n * L1 + L1 := by rw [Nat.succ_mul]
          have e2 : (n + 1) * L2 = n * L2 + L2 := by rw [Nat.succ_mul]
          have e3 : n * L1 = (n - 1) * L1 + L1 := by
            conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
          have e4 : n * L2 = (n - 1) * L2 + L2 := by
            conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
          -- body positions: `j1` for `c1`, `jc2` for `c2`, `j3 = jc2 - 1` for `c3`
          set j1 := c1.idx - n * L1 with hj1
          set jc2 := c2.idx - n * L2 with hjc2
          have hj1L : j1 < L1 := by omega
          have hjc2L : jc2 < L2 := by omega
          have hjc2pos : 1 ≤ jc2 := by omega
          have hc1eq : c1 = ⟨c1.thread, n * L1 + j1⟩ := by
            have hh : c1.idx = n * L1 + j1 := by omega
            rw [← hh]
          have hc3eq : c3 = ⟨c2.thread, n * L2 + (jc2 - 1)⟩ := by
            have hh : c3.idx = n * L2 + (jc2 - 1) := by rw [hc3]; dsimp only; omega
            rw [← hh]
          -- body commands (read off the batch copies)
          have hbody1 : ((I ^ k).prog c1.thread)[j1]? = some cc1' := by
            have hb1 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c1.thread)
              (j := j1) (p := n) (by rw [← hL1]; exact hj1L) (by omega)
            rw [← hL1, ← hc1eq, hc1cmd] at hb1; exact hb1.symm
          have hbody2 : ((I ^ k).prog c2.thread)[jc2]? = some cc2' := by
            have hb2 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c2.thread)
              (j := jc2) (p := n) (by rw [← hL2]; exact hjc2L) (by omega)
            rw [← hL2, show n * L2 + jc2 = c2.idx from by omega] at hb2
            change ((I ^ k) ^ (n + 1)).cmdAt c2 = _ at hb2
            rw [hc2cmd] at hb2; exact hb2.symm
          -- the down-shifted prefix points `c1↓`, `c2↓` (batch `n-1`)
          set c1d : ProgPoint := ⟨c1.thread, (n - 1) * L1 + j1⟩ with hc1d
          set c2d : ProgPoint := ⟨c2.thread, (n - 1) * L2 + jc2⟩ with hc2d
          have hc1dlt : c1d.idx < n * ((I ^ k).prog c1d.thread).length := by
            rw [hc1d]; dsimp only; rw [← hL1]; omega
          have hc2dlt : c2d.idx < n * ((I ^ k).prog c2d.thread).length := by
            rw [hc2d]; dsimp only; rw [← hL2]; omega
          have hcmd1d : ((I ^ k) ^ n).cmdAt c1d = some cc1' := by
            rw [hc1d, show (n - 1) * L1 + j1 = (n - 1) * ((I ^ k).prog c1.thread).length + j1 from
              by rw [hL1], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c1.thread)
              (j := j1) (p := n - 1) (by rw [← hL1]; exact hj1L) (by omega)]
            exact hbody1
          have hcmd2d : ((I ^ k) ^ n).cmdAt c2d = some cc2' := by
            rw [hc2d, show (n - 1) * L2 + jc2 = (n - 1) * ((I ^ k).prog c2.thread).length + jc2 from
              by rw [hL2], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c2.thread)
              (j := jc2) (p := n - 1) (by rw [← hL2]; exact hjc2L) (by omega)]
            exact hbody2
          have hbar1d : (((I ^ k) ^ n).cmdAt c1d).bind Cmd.barrier? = some b := by
            rw [hcmd1d, Option.bind_some, Cmd.barrier?_of_barrierRef hc1ref]
          have hbar2d : (((I ^ k) ^ n).cmdAt c2d).bind Cmd.barrier? = some b := by
            rw [hcmd2d, Option.bind_some, Cmd.barrier?_of_barrierRef hc2ref]
          -- the same commands in the full program (`c1d`, `c2d` lie in the prefix)
          have hcmd1dF : ((I ^ k) ^ (n + 1)).cmdAt c1d = some cc1' := by
            rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc1dlt]; exact hcmd1d
          have hcmd2dF : ((I ^ k) ^ (n + 1)).cmdAt c2d = some cc2' := by
            rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc2dlt]; exact hcmd2d
          -- generation of `c2d`, `c1d` in `τn` from the full-trace offset + GP
          have hoff1 := hoffset c1.thread j1 n cc1' b par1 (by omega) (le_refl n)
            hbody1 hc1ref
          have hoff2 := hoffset c2.thread jc2 n cc2' b par2 (by omega) (le_refl n) hbody2 hc2ref
          have hGP1 := hGP c1d cc1' b par1 hc1dlt hcmd1dF hc1ref
          have hGP2 := hGP c2d cc2' b par2 hc2dlt hcmd2dF hc2ref
          have hgen2d : pointGen ((I ^ k) ^ n) τn c2d
              = pointGen ((I ^ k) ^ n) τn c1d + 1 := by
            -- `hoff1/hoff2` relate batch-`n` gens to batch-`(n-1)` gens (full trace); `hGP*`
            -- transfer the batch-`(n-1)` gens to the prefix trace; `hgen` ties `c1`/`c2`.
            rw [hc1d] at hGP1
            rw [hc2d] at hGP2
            rw [← hL1] at hoff1
            rw [← hL2] at hoff2
            rw [← hc1eq] at hoff1
            have hc2eq : (⟨c2.thread, n * L2 + jc2⟩ : ProgPoint) = c2 := by
              rw [show n * L2 + jc2 = c2.idx from by omega]
            rw [hc2eq] at hoff2
            rw [hc1d, hc2d]
            omega
          -- the prefix within-batch-`(n-1)` edge, lifted to the full program by `hMONO`
          have hpre := prefixHB c1d c2d hbar1d hbar2d hgen2d (by rw [hc2d]; dsimp only; omega)
          have hc2dm1 : (⟨c2d.thread, c2d.idx - 1⟩ : ProgPoint)
              = ⟨c2.thread, (n - 1) * L2 + (jc2 - 1)⟩ := by
            rw [hc2d]; dsimp only; congr 1; omega
          rw [hc2dm1] at hpre
          have hfulld := hMONO _ _ hpre
          rw [hc1d] at hfulld
          -- assemble the goal `hb c1 c3` from the batch-`(n-1)` edge via `hWithinFull.mp`
          rw [hc1eq, hc3eq]
          have hwithin := (hWithinFull c1.thread c2.thread j1 (jc2 - 1)
            (by rw [← hL1]; exact hj1L) (by rw [← hL2]; omega)).mp
          rw [← hL1, ← hL2] at hwithin
          exact hwithin hfulld
        · -- C-i: `c3 ∈ batch n-1` (so `c2` is the first op of batch `n`).  Paper: *impossible*
          -- — `c1 → c3` would run backwards `n → n-1`, which the generation stratification
          -- (`no_backward_edge`) forbids; ruled out via `hL`/`hU` + `hgen`.
          exfalso
          push Not at hc2pre hc3n
          -- `c2` is the first op of batch `n`: `c2.idx = n * L2`
          have e1 : (n + 1) * L1 = n * L1 + L1 := by rw [Nat.succ_mul]
          have e2 : (n + 1) * L2 = n * L2 + L2 := by rw [Nat.succ_mul]
          have hc2first : c2.idx = n * L2 := by omega
          have e3 : n * L1 = (n - 1) * L1 + L1 := by
            conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
          have e4 : n * L2 = (n - 1) * L2 + L2 := by
            conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
          set j1 := c1.idx - n * L1 with hj1
          have hj1L : j1 < L1 := by omega
          have hc1eq : c1 = ⟨c1.thread, n * L1 + j1⟩ := by
            have hh : c1.idx = n * L1 + j1 := by omega
            rw [← hh]
          have hbody1 : ((I ^ k).prog c1.thread)[j1]? = some cc1' := by
            have hb1 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c1.thread)
              (j := j1) (p := n) (by rw [← hL1]; exact hj1L) (by omega)
            rw [← hL1, ← hc1eq, hc1cmd] at hb1; exact hb1.symm
          have hbody2 : ((I ^ k).prog c2.thread)[0]? = some cc2' := by
            have hb2 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c2.thread)
              (j := 0) (p := n) hL2pos (by omega)
            rw [Nat.add_zero, ← hL2, hc2first.symm] at hb2
            change ((I ^ k) ^ (n + 1)).cmdAt c2 = _ at hb2
            rw [hc2cmd] at hb2; exact hb2.symm
          -- the down-shifted prefix points `c1↓`, `c2↓` (batch `n-1`)
          set c1d : ProgPoint := ⟨c1.thread, (n - 1) * L1 + j1⟩ with hc1d
          set c2d : ProgPoint := ⟨c2.thread, (n - 1) * L2⟩ with hc2d
          have hc1dlt : c1d.idx < n * ((I ^ k).prog c1d.thread).length := by
            rw [hc1d]; dsimp only; rw [← hL1]; omega
          have hc2dlt : c2d.idx < n * ((I ^ k).prog c2d.thread).length := by
            rw [hc2d]; dsimp only; rw [← hL2]; omega
          have hcmd1d : ((I ^ k) ^ n).cmdAt c1d = some cc1' := by
            rw [hc1d, show (n - 1) * L1 + j1 = (n - 1) * ((I ^ k).prog c1.thread).length + j1 from
              by rw [hL1], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c1.thread)
              (j := j1) (p := n - 1) (by rw [← hL1]; exact hj1L) (by omega)]
            exact hbody1
          have hcmd2d : ((I ^ k) ^ n).cmdAt c2d = some cc2' := by
            rw [hc2d, show (n - 1) * L2 = (n - 1) * ((I ^ k).prog c2.thread).length + 0 from
              by rw [hL2, Nat.add_zero], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n)
              (t := c2.thread) (j := 0) (p := n - 1) hL2pos (by omega)]
            exact hbody2
          have hbar1d : (((I ^ k) ^ n).cmdAt c1d).bind Cmd.barrier? = some b := by
            rw [hcmd1d, Option.bind_some, Cmd.barrier?_of_barrierRef hc1ref]
          have hbar2d : (((I ^ k) ^ n).cmdAt c2d).bind Cmd.barrier? = some b := by
            rw [hcmd2d, Option.bind_some, Cmd.barrier?_of_barrierRef hc2ref]
          have hcmd1dF : ((I ^ k) ^ (n + 1)).cmdAt c1d = some cc1' := by
            rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc1dlt]; exact hcmd1d
          have hcmd2dF : ((I ^ k) ^ (n + 1)).cmdAt c2d = some cc2' := by
            rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc2dlt]; exact hcmd2d
          have hoff1 := hoffset c1.thread j1 n cc1' b par1 (by omega) (le_refl n) hbody1 hc1ref
          have hoff2 := hoffset c2.thread 0 n cc2' b par2 (by omega) (le_refl n) hbody2 hc2ref
          have hGP1 := hGP c1d cc1' b par1 hc1dlt hcmd1dF hc1ref
          have hGP2 := hGP c2d cc2' b par2 hc2dlt hcmd2dF hc2ref
          have hgen2d : pointGen ((I ^ k) ^ n) τn c2d
              = pointGen ((I ^ k) ^ n) τn c1d + 1 := by
            rw [hc1d] at hGP1
            rw [hc2d] at hGP2
            rw [← hL1] at hoff1
            rw [← hL2] at hoff2
            simp only [Nat.add_zero] at hoff2
            rw [← hc1eq] at hoff1
            have hc2eq : (⟨c2.thread, n * L2⟩ : ProgPoint) = c2 := by
              conv_rhs => rw [show c2 = ⟨c2.thread, c2.idx⟩ from rfl]
              rw [hc2first]
            rw [hc2eq] at hoff2
            rw [hc1d, hc2d]
            omega
          have hpos : 0 < (n - 1) * L2 := Nat.mul_pos (by omega) hL2pos
          have hpre := prefixHB c1d c2d hbar1d hbar2d hgen2d (by rw [hc2d]; dsimp only; omega)
          -- `c3↓ = ⟨c2.thread, (n-1)*L2 - 1⟩` lies in batch `n-2`, `c1↓` in batch `n-1`
          have hbackward : happensBefore ((I ^ k) ^ ((n - 1) + 1)) τn
              c1d ⟨c2d.thread, c2d.idx - 1⟩ := by
            rw [show (n - 1) + 1 = n from by omega]; exact hpre
          have hLN' : ∀ (η : ProgPoint) (c : Cmd) (bb : Barrier) (par : ℕ+),
              ((I ^ k) ^ ((n - 1) + 1)).cmdAt η = some c → Cmd.barrierRef c = some (bb, par) →
              (η.idx / ((I ^ k).prog η.thread).length) * (k * I.arrivers bb / I.arrivalCount h bb)
                + 1 ≤ pointGen ((I ^ k) ^ ((n - 1) + 1)) τn η := by
            rw [show (n - 1) + 1 = n from by omega]; exact hLN
          have hUN' : ∀ (η : ProgPoint) (bb : Barrier) (par : ℕ+),
              ((I ^ k) ^ ((n - 1) + 1)).cmdAt η = some (Cmd.sync bb par) →
              pointGen ((I ^ k) ^ ((n - 1) + 1)) τn η
                ≤ (η.idx / ((I ^ k).prog η.thread).length + 1)
                    * (k * I.arrivers bb / I.arrivalCount h bb) := by
            rw [show (n - 1) + 1 = n from by omega]; exact hUN
          exact no_backward_edge h hk hLN' hUN' (n - 1) c1d ⟨c2d.thread, c2d.idx - 1⟩
            hbackward
            (by rw [hc1d]; dsimp only; rw [← hL1]; omega)
            (by rw [hc2d]; dsimp only; rw [← hL2]; omega)
      · by_cases hc1n1 : (n - 1) * L1 ≤ c1.idx
        · -- **Case B** (paper: `c1 ∈ I^k_n`, `c2 ∈ I^k_{n+1}`).  `c1 ∈ batch n-1`, `c2 ∈ n`.
          by_cases hc3n : n * L2 ≤ c2.idx - 1
          · -- B-ii: `c3 ∈ batch n`.  Across edge `n-1 → n` is the up-shift of an `n-2 → n-1`
            -- prefix edge (`last_batch_hb_across`); discharge that by `hprefix` + `hMONO`.
            push Not at hc2pre hc1n
            -- batch-boundary expansions for batches `n-2, n-1, n, n+1`
            have e1 : (n + 1) * L2 = n * L2 + L2 := by rw [Nat.succ_mul]
            have eA1 : n * L1 = (n - 1) * L1 + L1 := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
            have eA2 : (n - 1) * L1 = (n - 2) * L1 + L1 := by
              conv_lhs => rw [show n - 1 = (n - 2) + 1 from by omega, Nat.succ_mul]
            have eB1 : n * L2 = (n - 1) * L2 + L2 := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
            -- body positions: `j1` for `c1` (batch n-1), `jc2`/`j3` for `c2`/`c3` (batch n)
            set j1 := c1.idx - (n - 1) * L1 with hj1
            set jc2 := c2.idx - n * L2 with hjc2
            have hj1L : j1 < L1 := by omega
            have hjc2L : jc2 < L2 := by omega
            have hjc2pos : 1 ≤ jc2 := by omega
            have hc1eq : c1 = ⟨c1.thread, (n - 1) * L1 + j1⟩ := by
              have hh : c1.idx = (n - 1) * L1 + j1 := by omega
              rw [← hh]
            have hc3eq : c3 = ⟨c2.thread, n * L2 + (jc2 - 1)⟩ := by
              have hh : c3.idx = n * L2 + (jc2 - 1) := by rw [hc3]; dsimp only; omega
              rw [← hh]
            -- body commands
            have hbody1 : ((I ^ k).prog c1.thread)[j1]? = some cc1' := by
              have hb1 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c1.thread)
                (j := j1) (p := n - 1) (by rw [← hL1]; exact hj1L) (by omega)
              rw [show (n - 1) * ((I ^ k).prog c1.thread).length + j1
                    = c1.idx from by rw [← hL1]; omega] at hb1
              change ((I ^ k) ^ (n + 1)).cmdAt c1 = _ at hb1
              rw [hc1cmd] at hb1; exact hb1.symm
            have hbody2 : ((I ^ k).prog c2.thread)[jc2]? = some cc2' := by
              have hb2 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c2.thread)
                (j := jc2) (p := n) (by rw [← hL2]; exact hjc2L) (by omega)
              rw [show n * ((I ^ k).prog c2.thread).length + jc2
                    = c2.idx from by rw [← hL2]; omega] at hb2
              change ((I ^ k) ^ (n + 1)).cmdAt c2 = _ at hb2
              rw [hc2cmd] at hb2; exact hb2.symm
            -- the down-shifted prefix points `c1↓` (batch n-2), `c2↓` (batch n-1)
            set c1d : ProgPoint := ⟨c1.thread, (n - 2) * L1 + j1⟩ with hc1d
            set c2d : ProgPoint := ⟨c2.thread, (n - 1) * L2 + jc2⟩ with hc2d
            have hc1dlt : c1d.idx < n * ((I ^ k).prog c1d.thread).length := by
              rw [hc1d]; dsimp only; rw [← hL1]; omega
            have hc2dlt : c2d.idx < n * ((I ^ k).prog c2d.thread).length := by
              rw [hc2d]; dsimp only; rw [← hL2]; omega
            have hcmd1d : ((I ^ k) ^ n).cmdAt c1d = some cc1' := by
              rw [hc1d, show (n - 2) * L1 + j1 = (n - 2) * ((I ^ k).prog c1.thread).length + j1 from
                by rw [hL1], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c1.thread)
                (j := j1) (p := n - 2) (by rw [← hL1]; exact hj1L) (by omega)]
              exact hbody1
            have hcmd2d : ((I ^ k) ^ n).cmdAt c2d = some cc2' := by
              rw [hc2d, show (n - 1) * L2 + jc2 = (n - 1) * ((I ^ k).prog c2.thread).length + jc2
                from by rw [hL2], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c2.thread)
                (j := jc2) (p := n - 1) (by rw [← hL2]; exact hjc2L) (by omega)]
              exact hbody2
            have hbar1d : (((I ^ k) ^ n).cmdAt c1d).bind Cmd.barrier? = some b := by
              rw [hcmd1d, Option.bind_some, Cmd.barrier?_of_barrierRef hc1ref]
            have hbar2d : (((I ^ k) ^ n).cmdAt c2d).bind Cmd.barrier? = some b := by
              rw [hcmd2d, Option.bind_some, Cmd.barrier?_of_barrierRef hc2ref]
            have hcmd1dF : ((I ^ k) ^ (n + 1)).cmdAt c1d = some cc1' := by
              rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc1dlt]; exact hcmd1d
            have hcmd2dF : ((I ^ k) ^ (n + 1)).cmdAt c2d = some cc2' := by
              rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc2dlt]; exact hcmd2d
            -- generations: drop one batch (offset) then GP, tying `c2d`/`c1d` via `hgen`
            have hoff1 := hoffset c1.thread j1 (n - 1) cc1' b par1 (by omega) (by omega)
              hbody1 hc1ref
            have hoff2 := hoffset c2.thread jc2 n cc2' b par2 (by omega) (le_refl n) hbody2 hc2ref
            have hGP1 := hGP c1d cc1' b par1 hc1dlt hcmd1dF hc1ref
            have hGP2 := hGP c2d cc2' b par2 hc2dlt hcmd2dF hc2ref
            have hgen2d : pointGen ((I ^ k) ^ n) τn c2d
                = pointGen ((I ^ k) ^ n) τn c1d + 1 := by
              rw [hc1d] at hGP1
              rw [hc2d] at hGP2
              rw [← hL1, show n - 1 - 1 = n - 2 from by omega] at hoff1
              rw [← hL2] at hoff2
              have hc1eq' : (⟨c1.thread, (n - 1) * L1 + j1⟩ : ProgPoint) = c1 := hc1eq.symm
              rw [hc1eq'] at hoff1
              have hc2eq : (⟨c2.thread, n * L2 + jc2⟩ : ProgPoint) = c2 := by
                rw [show n * L2 + jc2 = c2.idx from by omega]
              rw [hc2eq] at hoff2
              rw [hc1d, hc2d]
              omega
            have hpre := prefixHB c1d c2d hbar1d hbar2d hgen2d (by rw [hc2d]; dsimp only; omega)
            have hc2dm1 : (⟨c2d.thread, c2d.idx - 1⟩ : ProgPoint)
                = ⟨c2.thread, (n - 1) * L2 + (jc2 - 1)⟩ := by
              rw [hc2d]; dsimp only; congr 1; omega
            rw [hc2dm1] at hpre
            have hfulld := hMONO _ _ hpre
            rw [hc1d] at hfulld
            -- assemble `hb c1 c3` via `hAcrossFull.mpr` from the `n-2 → n-1` prefix edge
            rw [hc1eq, hc3eq]
            have hacross := (hAcrossFull c1.thread c2.thread j1 (jc2 - 1)
              (by rw [← hL1]; exact hj1L) (by rw [← hL2]; omega)).mpr
            rw [← hL1, ← hL2] at hacross
            exact hacross hfulld
          · -- B-i: `c3 ∈ batch n-1`.  Within-batch-`(n-1)` prefix edge (paper: batch symmetry;
            -- `last_batch_hb_within` applied to the prefix `(I^k)^n`/`τn`); discharge by
            -- `hprefix` + `hMONO`.
            push Not at hc2pre hc1n hc3n
            -- `c2` is the first op of batch `n`: `c2.idx = n * L2`
            have hc2first : c2.idx = n * L2 := by omega
            have e1 : (n + 1) * L2 = n * L2 + L2 := by rw [Nat.succ_mul]
            have eA1 : n * L1 = (n - 1) * L1 + L1 := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
            have eA2 : (n - 1) * L1 = (n - 2) * L1 + L1 := by
              conv_lhs => rw [show n - 1 = (n - 2) + 1 from by omega, Nat.succ_mul]
            have eB1 : n * L2 = (n - 1) * L2 + L2 := by
              conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
            have eB2 : (n - 1) * L2 = (n - 2) * L2 + L2 := by
              conv_lhs => rw [show n - 1 = (n - 2) + 1 from by omega, Nat.succ_mul]
            -- body positions: `j1` for `c1` (batch n-1), `j3 = L2 - 1` for `c3` (batch n-1)
            set j1 := c1.idx - (n - 1) * L1 with hj1
            have hj1L : j1 < L1 := by omega
            have hc1eq : c1 = ⟨c1.thread, (n - 1) * L1 + j1⟩ := by
              have hh : c1.idx = (n - 1) * L1 + j1 := by omega
              rw [← hh]
            have hc3eq : c3 = ⟨c2.thread, (n - 1) * L2 + (L2 - 1)⟩ := by
              have hh : c3.idx = (n - 1) * L2 + (L2 - 1) := by rw [hc3]; dsimp only; omega
              rw [← hh]
            -- body commands (`c2`'s is position `0`; `c1`'s is position `j1`)
            have hbody1 : ((I ^ k).prog c1.thread)[j1]? = some cc1' := by
              have hb1 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c1.thread)
                (j := j1) (p := n - 1) (by rw [← hL1]; exact hj1L) (by omega)
              rw [show (n - 1) * ((I ^ k).prog c1.thread).length + j1
                    = c1.idx from by rw [← hL1]; omega] at hb1
              change ((I ^ k) ^ (n + 1)).cmdAt c1 = _ at hb1
              rw [hc1cmd] at hb1; exact hb1.symm
            have hbody2 : ((I ^ k).prog c2.thread)[0]? = some cc2' := by
              have hb2 := CTA.cmdAt_pow_batch_copy (I ^ k) (m := n + 1) (t := c2.thread)
                (j := 0) (p := n) hL2pos (by omega)
              rw [Nat.add_zero, show n * ((I ^ k).prog c2.thread).length
                    = c2.idx from by rw [← hL2]; omega] at hb2
              change ((I ^ k) ^ (n + 1)).cmdAt c2 = _ at hb2
              rw [hc2cmd] at hb2; exact hb2.symm
            -- the doubly-down-shifted prefix points `c1↓↓` (batch n-2), `c2↓↓` (batch n-1)
            set c1d : ProgPoint := ⟨c1.thread, (n - 2) * L1 + j1⟩ with hc1d
            set c2d : ProgPoint := ⟨c2.thread, (n - 1) * L2⟩ with hc2d
            have hc1dlt : c1d.idx < n * ((I ^ k).prog c1d.thread).length := by
              rw [hc1d]; dsimp only; rw [← hL1]; omega
            have hc2dlt : c2d.idx < n * ((I ^ k).prog c2d.thread).length := by
              rw [hc2d]; dsimp only; rw [← hL2]; omega
            have hcmd1d : ((I ^ k) ^ n).cmdAt c1d = some cc1' := by
              rw [hc1d, show (n - 2) * L1 + j1 = (n - 2) * ((I ^ k).prog c1.thread).length + j1 from
                by rw [hL1], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n) (t := c1.thread)
                (j := j1) (p := n - 2) (by rw [← hL1]; exact hj1L) (by omega)]
              exact hbody1
            have hcmd2d : ((I ^ k) ^ n).cmdAt c2d = some cc2' := by
              rw [hc2d, show (n - 1) * L2 = (n - 1) * ((I ^ k).prog c2.thread).length + 0 from
                by rw [hL2, Nat.add_zero], CTA.cmdAt_pow_batch_copy (I ^ k) (m := n)
                (t := c2.thread) (j := 0) (p := n - 1) hL2pos (by omega)]
              exact hbody2
            have hbar1d : (((I ^ k) ^ n).cmdAt c1d).bind Cmd.barrier? = some b := by
              rw [hcmd1d, Option.bind_some, Cmd.barrier?_of_barrierRef hc1ref]
            have hbar2d : (((I ^ k) ^ n).cmdAt c2d).bind Cmd.barrier? = some b := by
              rw [hcmd2d, Option.bind_some, Cmd.barrier?_of_barrierRef hc2ref]
            have hcmd1dF : ((I ^ k) ^ (n + 1)).cmdAt c1d = some cc1' := by
              rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc1dlt]; exact hcmd1d
            have hcmd2dF : ((I ^ k) ^ (n + 1)).cmdAt c2d = some cc2' := by
              rw [CTA.cmdAt_pow_succ_prefix (I ^ k) hc2dlt]; exact hcmd2d
            -- generations: drop one batch (offset) then GP, tying `c2d`/`c1d` via `hgen`
            have hoff1 := hoffset c1.thread j1 (n - 1) cc1' b par1 (by omega) (by omega)
              hbody1 hc1ref
            have hoff2 := hoffset c2.thread 0 n cc2' b par2 (by omega) (le_refl n) hbody2 hc2ref
            have hGP1 := hGP c1d cc1' b par1 hc1dlt hcmd1dF hc1ref
            have hGP2 := hGP c2d cc2' b par2 hc2dlt hcmd2dF hc2ref
            have hgen2d : pointGen ((I ^ k) ^ n) τn c2d
                = pointGen ((I ^ k) ^ n) τn c1d + 1 := by
              rw [hc1d] at hGP1
              rw [hc2d] at hGP2
              rw [← hL1, show n - 1 - 1 = n - 2 from by omega] at hoff1
              rw [← hL2] at hoff2
              simp only [Nat.add_zero] at hoff2
              have hc1eq' : (⟨c1.thread, (n - 1) * L1 + j1⟩ : ProgPoint) = c1 := hc1eq.symm
              rw [hc1eq'] at hoff1
              have hc2eq : (⟨c2.thread, n * L2⟩ : ProgPoint) = c2 := by
                conv_rhs => rw [show c2 = ⟨c2.thread, c2.idx⟩ from rfl]
                rw [hc2first]
              rw [hc2eq] at hoff2
              rw [hc1d, hc2d]
              omega
            have hpos : 0 < (n - 1) * L2 := Nat.mul_pos (by omega) hL2pos
            have hpre := prefixHB c1d c2d hbar1d hbar2d hgen2d (by rw [hc2d]; dsimp only; omega)
            -- `c2d - 1 = ⟨c2.thread, (n-1)*L2 - 1⟩`, the batch-`(n-2)` copy of `c3`
            have hc2dm1 : (⟨c2d.thread, c2d.idx - 1⟩ : ProgPoint)
                = ⟨c2.thread, (n - 2) * L2 + (L2 - 1)⟩ := by
              rw [hc2d]; dsimp only; congr 1; omega
            rw [hc2dm1] at hpre
            -- lift the batch-`(n-2)` prefix edge to batch `n-1` (still in `τn`) by `hWithinPre`
            have hwp := (hWithinPre c1.thread c2.thread j1 (L2 - 1)
              (by rw [← hL1]; exact hj1L) (by rw [← hL2]; omega)).mp
            rw [← hL1, ← hL2] at hwp
            rw [hc1d] at hpre
            have hpre1 := hwp hpre
            -- lift the batch-`(n-1)` prefix edge to the full program by `hMONO`
            rw [hc1eq, hc3eq]
            exact hMONO _ _ hpre1
        · -- **Case D** (paper: `c1 ∈ I^k_{[0,n-1]}`, `c2 ∈ I^k_{n+1}`).  `c1 ∈ batch ≤ n-2`,
          -- `c2 ∈ batch n`: *impossible* — `δ ≥ 1` puts their generations ≥ 2 apart, so
          -- `pointGen c2 = pointGen c1 + 1` cannot hold (`hgen` + `hL`/`hU` + `one_le_delta`).
          exfalso
          push Not at hc2pre hc1n1
          -- lower bound on `c2`'s generation: `c2 ∈ batch ≥ n`
          have hLc2 := hL c2 cc2' b par2 hc2cmd hc2ref
          rw [← hL2, ← hδdef] at hLc2
          have hc2div : n ≤ c2.idx / L2 := (Nat.le_div_iff_mul_le hL2pos).mpr hc2pre
          have hlow : n * δ + 1 ≤ pointGen ((I ^ k) ^ (n + 1)) τ c2 := by
            have : n * δ ≤ (c2.idx / L2) * δ := Nat.mul_le_mul_right δ hc2div
            omega
          -- upper bound on `c1`'s generation: `c1 ∈ batch ≤ n-2`
          have hUc1 := hUgen c1 cc1' b par1 hc1cmd hc1ref
          rw [← hL1, ← hδdef] at hUc1
          have hc1div : c1.idx / L1 ≤ n - 2 := by
            have : c1.idx / L1 < n - 1 := (Nat.div_lt_iff_lt_mul hL1pos).mpr hc1n1
            omega
          have hup : pointGen ((I ^ k) ^ (n + 1)) τ c1 ≤ (n - 1) * δ := by
            have hle : (c1.idx / L1 + 1) * δ ≤ (n - 1) * δ :=
              Nat.mul_le_mul_right δ (by omega)
            omega
          -- combine: `n*δ+1 ≤ gen c2 = gen c1+1 ≤ (n-1)*δ+1`, so `n*δ ≤ (n-1)*δ`, but `δ ≥ 1`.
          have hnd : (n - 1) * δ + δ = n * δ := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega
  rw [happensBefore, Relation.reflTransGen_iff_eq_or_transGen] at hHB
  rcases hHB with heq | htg
  · exact absurd heq.symm hc1ne3
  · exact mem_transClosure_of_transGen _ hc1ne3 htg

theorem CTA.WellSynchronized.loop_well_synchronized_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : n >= 2)
    (hWS : (I ^ k).BatchesWellSynchronized 2) :
    ((I ^ k) ^ (n)).WellSynchronized := by
  -- Strengthen to `BatchesWellSynchronized N` for every `N ≥ 3`, by induction from the base
  -- case `3` (the hypothesis); each step adds the new top batch via `batches_inductive_step_impl`
  -- (`BatchesWellSynchronized N → (I ^ k) ^ (N + 1)` well-synchronized).
  have key : ∀ N, 2 ≤ N → (I ^ k).BatchesWellSynchronized N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact hWS
    | succ N hN ih =>
      intro m hm1 hmN1
      rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · exact ih m hm1 (by omega)
      · rw [show m = N + 1 from by omega]
        exact CTA.WellSynchronized.batches_inductive_step_impl h hk (by omega) ih
  exact key n hn n (by omega) (le_refl n)

/-- **Front-batch decomposition of a power-with-epilogue.** The `(n+1)`-batch program with
epilogue is *one batch* `I ^ k` prepended to the `n`-batch program with epilogue:
`((I^k)^(n+1)) ⨾ E = (I^k) ⨾ ((I^k)^n ⨾ E)`. So the `n`-batch-with-epilogue program `Pn` embeds
into the `(n+1)`-batch one `P` by a uniform `+|(I^k).prog t|` index shift (the prepended batch),
which is what makes the inductive step's casework reduce cleanly to the prefix `Pn`. -/
theorem CTA.pow_succ_seq_assoc (I : CTA) (k n : Nat) {E : CTA} (hids : (I ^ k).ids = E.ids) :
    ((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)
      = (I ^ k).seq (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids))
          (by simp only [CTA.seq, CTA.pow_ids]) := by
  apply CTA.ext
  · change ((I ^ k) ^ (n + 1)).ids = (I ^ k).ids; simp only [CTA.pow_ids]
  · funext t
    change ((I ^ k) ^ (n + 1)).prog t ++ E.prog t
       = (I ^ k).prog t ++ (((I ^ k) ^ n).prog t ++ E.prog t)
    rw [CTA.pow_succ_prog, List.append_assoc]

/-- **Back-batch decomposition of a power-with-epilogue.** Splitting off the *last* batch into
the epilogue: `((I^k)^(m+1)) ⨾ E = (I^k)^m ⨾ ((I^k) ⨾ E)`. This is what lets a replay trace of
`P` be built by gluing the `(I^k) ⨾ E`-trace (from `hbatchE`) onto an `m`-batch replay. -/
theorem CTA.pow_seq_assoc_last (I : CTA) (k m : Nat) {E : CTA} (hids : (I ^ k).ids = E.ids) :
    ((I ^ k) ^ (m + 1)).seq E ((CTA.pow_ids (I ^ k) (m + 1)).trans hids)
      = ((I ^ k) ^ m).seq ((I ^ k).seq E hids)
          (by simp only [CTA.seq, CTA.pow_ids]) := by
  apply CTA.ext
  · change ((I ^ k) ^ (m + 1)).ids = ((I ^ k) ^ m).ids; simp only [CTA.pow_ids]
  · funext t
    change ((I ^ k) ^ (m + 1)).prog t ++ E.prog t
       = ((I ^ k) ^ m).prog t ++ ((I ^ k).prog t ++ E.prog t)
    rw [CTA.pow_add_prog (I ^ k) m 1, CTA.pow_one_prog, List.append_assoc]

/-- **Generation of a barrier point in a glued epilogue replay.** Let `A = I ^ k`,
`B = A ⨾ E`, and `τ = glue(τ_m, tE)` the trace of `A^m ⨾ B` obtained by prepending an
`m`-batch replay `τ_m` of `A^m` (with `pow_replay_recycle_structure` data `hrec`) ahead of a
`B`-trace `tE`. This computes the generation of every barrier point of `A^m ⨾ B`:

* a **prefix** point (`idx < m·L`, a batch-`p` copy of body instruction `j`) has generation
  `recycleCount b t₁ (M₁-1) + 1 + p·δ` — the same as in the pure replay `τ_m`;
* an **epilogue** point (`idx ≥ m·L`, position `e = idx - m·L` in `B`) has generation
  `pointGen B tE ⟨t, e⟩ + m·δ` — the `B`-generation bumped by the `m` prepended batches.

The epilogue bump is `m·δ` because the `m`-batch prefix recycles `b` exactly `m·δ` times
(`pow_full_recycleCount`), and the count splits across the glue boundary (`recycleCount_suffix`).
The two cases are the seq-analogue of `last_batches_replay_bundle`'s `keygen`. -/
theorem glue_replay_gen {I : CTA} (h : I.ConsistentArrivalCounts) {s : State} {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (_ht₁L : t₁.getLast? = some (Config.done s)) {E : CTA}
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false)
    (hids : (I ^ I.loopK h).ids = E.ids) {m : Nat} {τm : List Config}
    (hτm : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h) ^ m)) τm)
    (hτmL : τm.getLast? = some (Config.done s))
    (hrec : ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (p M M₁ : Nat),
        p < m → ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run s ((I ^ I.loopK h) ^ m)) τm
            ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩ M →
        IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
        recycleCount b τm (M - 1)
          = recycleCount b t₁ (M₁ - 1) + p * (I.loopK h * I.arrivers b / I.arrivalCount h b))
    {tE : List Config}
    (htE : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h).seq E hids)) tE)
    (hmB : ((I ^ I.loopK h) ^ m).ids = ((I ^ I.loopK h).seq E hids).ids) :
    -- prefix point generation
    (∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
        j < ((I ^ I.loopK h).prog t).length → p < m →
        ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
        IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
        pointGen (((I ^ I.loopK h) ^ m).seq ((I ^ I.loopK h).seq E hids) hmB)
            (τm.dropLast.map (Config.seqLift ((I ^ I.loopK h) ^ m) ((I ^ I.loopK h).seq E hids))
              ++ tE.tail)
            ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
          = recycleCount b t₁ (M₁ - 1) + 1
            + p * (I.loopK h * I.arrivers b / I.arrivalCount h b)) ∧
    -- epilogue point generation
    (∀ (t : ThreadId) (e : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
        ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c → Cmd.barrierRef c = some (b, par) →
        pointGen (((I ^ I.loopK h) ^ m).seq ((I ^ I.loopK h).seq E hids) hmB)
            (τm.dropLast.map (Config.seqLift ((I ^ I.loopK h) ^ m) ((I ^ I.loopK h).seq E hids))
              ++ tE.tail)
            ⟨t, m * ((I ^ I.loopK h).prog t).length + e⟩
          = pointGen ((I ^ I.loopK h).seq E hids) tE ⟨t, e⟩
            + m * (I.loopK h * I.arrivers b / I.arrivalCount h b)) := by
  set A := I ^ I.loopK h with hA
  set B := A.seq E hids with hB
  set P := (A ^ m).seq B hmB with hP
  set τ := τm.dropLast.map (Config.seqLift (A ^ m) B) ++ tE.tail with hτdef
  -- glue structure
  obtain ⟨hglue, hgluelast, hsnd⟩ := glue_trace hmB hτm hτmL htE
  obtain ⟨sd, hlast⟩ := hglue.2
  -- basic length facts about `τm` (starts `run`, ends `done`)
  have hchainm : List.IsChain CTAStep τm := hτm.1.1.subtrace
  have hheadm : τm.head? = some (Config.run s (A ^ m)) := hτm.1.2
  have hmne : τm ≠ [] := fun hd => by rw [hd] at hheadm; simp at hheadm
  have hm2 : 2 ≤ τm.length := by
    rcases τm with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hheadm
    · simp only [List.head?_cons, Option.some.injEq] at hheadm
      simp only [List.getLast?_singleton, Option.some.injEq] at hτmL
      rw [hheadm] at hτmL; exact absurd hτmL (by simp)
    · simp only [List.length_cons]; omega
  -- the front of `τ` mirrors `τm` lifted into `P`; recycle counts agree on the front
  have hfst : ∀ q, q ≤ τm.length - 2 → τ[q]? = (τm.map (Config.seqLift (A ^ m) B))[q]? := by
    intro q hq
    rw [hτdef, List.getElem?_append_left
        (by rw [List.length_map, List.length_dropLast]; omega),
      List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  have hfrontrec : ∀ (b : Barrier) M, M ≤ τm.length - 2 →
      recycleCount b τ M = recycleCount b τm M := by
    intro b M hM
    rw [recycleCount_eq_of_getElem?_eq b (fun q hq => hfst q (Nat.le_trans hq hM)),
      recycleCount_map_seqLift (A ^ m) B b τm M]
  -- the penultimate config of `τm` has empty `A^m`-programs
  have hpenm : ∀ (i : ThreadId) (C : Config), τm[τm.length - 2]? = some C → C.progOf i = [] := by
    intro i C hC
    have hdrop : τm.dropLast ≠ [] := by
      intro hd; have : τm.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
      omega
    have hgl : τm.dropLast.getLast? = some C := by
      rw [List.getLast?_eq_getElem?, List.length_dropLast, List.getElem?_dropLast,
        if_pos (by omega), show τm.length - 1 - 1 = τm.length - 2 from by omega]
      exact hC
    exact progOf_penultimate_done hchainm hτmL hgl i
  -- program length facts: `(P.prog t).length = m·L + (B.prog t).length`
  have hPprog : ∀ t, P.prog t = (A ^ m).prog t ++ B.prog t := fun t => rfl
  have hmLen : ∀ t, ((A ^ m).prog t).length = m * (A.prog t).length :=
    fun t => CTA.pow_prog_length A m t
  -- **Front transport.** A prefix point's time in `τm` lifts (unshifted) into `τ`, and is `≤
  -- τm.length - 2`.
  have frontTransport : ∀ (q M' : Nat) (t : ThreadId), q < ((A ^ m).prog t).length →
      IsTimeOf (Config.run s (A ^ m)) τm ⟨t, q⟩ M' →
      IsTimeOf (Config.run s P) τ ⟨t, q⟩ M' ∧ M' ≤ τm.length - 2 := by
    intro q M' t hq hT
    obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hT
    have hj'1 : j' + 1 < τm.length := (List.getElem?_eq_some_iff.mp hDj1).1
    have hDne : D.progOf t ≠ [] := by
      rw [hDprog]; change ((A ^ m).prog t).drop q ≠ []
      rw [Ne, List.drop_eq_nil_iff]; omega
    have hjlt : j' < τm.length - 2 := by
      by_contra hcon
      have hje : j' = τm.length - 2 := by omega
      exact hDne (hpenm t D (by rw [← hje]; exact hDj))
    have hMb : M' ≤ τm.length - 2 := by omega
    refine ⟨⟨hglue.1, ?_, j', Config.seqLift (A ^ m) B D, Config.seqLift (A ^ m) B D',
      hMeq, ?_, ?_, ?_, ?_⟩, hMb⟩
    · change q < (P.prog t).length
      rw [hPprog, List.length_append]; omega
    · rw [hfst j' (by omega), List.getElem?_map, hDj]; rfl
    · rw [hfst (j' + 1) (by omega), List.getElem?_map, hDj1]; rfl
    · change (Config.seqLift (A ^ m) B D).progOf t = (P.prog t).drop q
      rw [Config.seqLift_progOf, hDprog, hPprog, List.drop_append_of_le_length (by omega)]
      rfl
    · change (Config.seqLift (A ^ m) B D').progOf t = (P.prog t).drop (q + 1)
      rw [Config.seqLift_progOf, hD'prog, hPprog, List.drop_append_of_le_length (by omega)]
      rfl
  -- **Suffix transport.** An epilogue point `⟨t, e⟩` (a `B`-point) at time `M'` in `tE` lifts
  -- into `τ` at `⟨t, m·L + e⟩` with time `(τm.length - 2) + M'`.
  have suffixTransport : ∀ (e M' : Nat) (t : ThreadId), e < (B.prog t).length →
      IsTimeOf (Config.run s B) tE ⟨t, e⟩ M' →
      IsTimeOf (Config.run s P) τ ⟨t, m * (A.prog t).length + e⟩
        ((τm.length - 2) + M') := by
    intro e M' t he hT'
    obtain ⟨-, -, j', D, D', hM'eq, hDj, hDj1, hDprog, hD'prog⟩ := hT'
    refine ⟨hglue.1, ?_, (τm.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
    · change m * (A.prog t).length + e < (P.prog t).length
      rw [hPprog, List.length_append, ← hmLen t]; omega
    · exact (hsnd j').trans hDj
    · rw [show (τm.length - 2) + j' + 1 = (τm.length - 2) + (j' + 1) from by omega]
      exact (hsnd (j' + 1)).trans hDj1
    · change D.progOf t = (P.prog t).drop (m * (A.prog t).length + e)
      rw [hPprog, ← hmLen t, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _),
        List.nil_append, Nat.add_sub_cancel_left]
      exact hDprog
    · change D'.progOf t = (P.prog t).drop (m * (A.prog t).length + e + 1)
      rw [hPprog, ← hmLen t, List.drop_append,
        List.drop_eq_nil_of_le
          (show ((A ^ m).prog t).length ≤ ((A ^ m).prog t).length + e + 1 by omega),
        List.nil_append,
        show ((A ^ m).prog t).length + e + 1 - ((A ^ m).prog t).length = e + 1 by omega]
      exact hD'prog
  -- the suffix recycle split across the glue boundary
  have hsplit : ∀ (b : Barrier) (K : Nat),
      recycleCount b τ ((τm.length - 2) + K)
        = recycleCount b τ (τm.length - 2) + recycleCount b tE K :=
    fun b K => recycleCount_suffix b hsnd
  -- the full prefix count: `m·δ` (via `pow_full_recycleCount` on `τm`)
  have hfullpref : ∀ (b : Barrier), b ∈ A.barrierSet →
      recycleCount b τ (τm.length - 2)
        = m * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro b hbA
    rw [hfrontrec b (τm.length - 2) (le_refl _), ← recycleCount_done_last hchainm hτmL hm2]
    exact pow_full_recycleCount h hτm hτmL hwf_s.2.2 hbA
      (Config.WellSynchronized.headCount_consistent_of_successful h (hfull b) ht₁ hbA)
  refine ⟨?_, ?_⟩
  · -- prefix point generation
    intro t j p c b par M₁ hjL hp hcj hbr hM₁
    have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
    -- the copy executes in `τm` at some time `M`; transport it to `τ`
    obtain ⟨sdm, hmlast⟩ := hτm.2
    have hjL' : j < (A.prog t).length := hjL
    have hidxlt : p * (A.prog t).length + j < ((A ^ m).prog t).length := by
      rw [hmLen]
      have hle : (p + 1) * (A.prog t).length ≤ m * (A.prog t).length :=
        Nat.mul_le_mul_right _ (by omega)
      have hexp : (p + 1) * (A.prog t).length = p * (A.prog t).length + (A.prog t).length := by
        rw [Nat.succ_mul]
      omega
    obtain ⟨M, hM⟩ := exists_time_of_ends_done hτm.1 hmlast
      (η := ⟨t, p * (A.prog t).length + j⟩) hidxlt
    obtain ⟨hτM, hMb⟩ := frontTransport (p * (A.prog t).length + j) M t hidxlt hM
    -- command at the copy in `P` is `c` (prefix region)
    have hcmdcopy : P.cmdAt ⟨t, p * (A.prog t).length + j⟩ = some c := by
      have hpre : (A ^ m).cmdAt ⟨t, p * (A.prog t).length + j⟩ = some c := by
        rw [CTA.cmdAt_pow_batch_copy A hjL hp]; exact hcj
      change (P.prog t)[p * (A.prog t).length + j]? = some c
      rw [hPprog, List.getElem?_append_left hidxlt]
      exact hpre
    have hg : pointGen P τ ⟨t, p * (A.prog t).length + j⟩
        = recycleCount b τ (M - 1) + 1 := by
      simp only [pointGen, hcmdcopy, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hτM]
    rw [hg]
    -- `M - 1 ≤ τm.length - 2`, so the front count agrees with `τm`'s; then `hrec`
    have hMm1 : M - 1 ≤ τm.length - 2 := by
      obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, -, -⟩ := hM
      have hj'1 : j' + 1 < τm.length := (List.getElem?_eq_some_iff.mp hDj1).1
      omega
    rw [hfrontrec b (M - 1) hMm1, hrec t j c b par p M M₁ hp hcj hbr hM hM₁]
    omega
  · -- epilogue point generation
    intro t e c b par hcmdE0 hbr
    have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
    have hcmdE : B.cmdAt ⟨t, e⟩ = some c := hcmdE0
    have heL : e < (B.prog t).length := (List.getElem?_eq_some_iff.mp hcmdE).1
    -- the epilogue point executes in `tE`; transport it to `τ`
    obtain ⟨sdE, hElast⟩ := htE.2
    obtain ⟨ME, hME⟩ := exists_time_of_ends_done htE.1 hElast (η := ⟨t, e⟩) heL
    have hτE := suffixTransport e ME t heL hME
    have hMEpos : 1 ≤ ME := by
      obtain ⟨-, -, j', D, D', hMeq, -, -, -, -⟩ := hME; omega
    -- command in `P` at the lifted point is `c` (epilogue region)
    have hcmdcopy : P.cmdAt ⟨t, m * (A.prog t).length + e⟩ = some c := by
      change (P.prog t)[m * (A.prog t).length + e]? = some c
      rw [hPprog, List.getElem?_append_right (by rw [hmLen]; omega), hmLen,
        show m * (A.prog t).length + e - m * (A.prog t).length = e from by omega]
      exact hcmdE
    have hgE : pointGen P τ ⟨t, m * (A.prog t).length + e⟩
        = recycleCount b τ ((τm.length - 2) + (ME - 1)) + 1 := by
      simp only [pointGen, hcmdcopy, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hτE,
        show (τm.length - 2) + ME - 1 = (τm.length - 2) + (ME - 1) from by omega]
    have hgEtE : pointGen B tE ⟨t, e⟩ = recycleCount b tE (ME - 1) + 1 := by
      simp only [pointGen, hcmdE, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hME]
    -- the full prefix count of `b` is `m·δ` whether or not `b ∈ A.barrierSet`
    have hpref : recycleCount b τ (τm.length - 2)
        = m * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
      by_cases hbA : b ∈ A.barrierSet
      · exact hfullpref b hbA
      · -- `b` not used by `A`, hence not by `I`: `I.arrivers b = 0`, so `δ = 0`
        have hbInot : b ∉ I.barriers := by
          intro hbIyes
          -- `b ∈ I.barriers ⟹ b ∈ A.barrierSet = (I^loopK).barrierSet`
          rw [CTA.barriers, Finset.mem_biUnion] at hbIyes
          obtain ⟨i, hi, hbi⟩ := hbIyes
          rw [List.mem_toFinset, List.mem_map] at hbi
          obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
          simp only at hb'; subst hb'
          rw [List.mem_filterMap] at hr
          obtain ⟨c, hc, hcr⟩ := hr
          -- `c ∈ I.prog i ⊆ (I^loopK).prog i = A.prog i` (`loopK ≥ 1`)
          have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
          have hcA : c ∈ A.prog i := by
            rw [hA, show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
              List.mem_append]
            exact Or.inl hc
          apply hbA
          rw [CTA.barrierSet, Finset.mem_biUnion]
          refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
            ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
          rw [hA, CTA.pow_ids]; exact hi
        rw [hfrontrec b (τm.length - 2) (le_refl _),
          ← recycleCount_done_last hchainm hτmL hm2]
        have hδ0 : I.loopK h * I.arrivers b / I.arrivalCount h b = 0 := by
          have hIarr0 : I.arrivers b = 0 := by
            rw [CTA.arrivers]; apply Finset.sum_eq_zero
            intro i hi
            rw [List.countP_eq_zero]
            intro r hr
            simp only [List.mem_filterMap] at hr
            obtain ⟨c, hc, hcr⟩ := hr
            simp only [beq_iff_eq]; intro hrb
            apply hbInot
            rw [CTA.barriers, Finset.mem_biUnion]
            exact ⟨i, hi, List.mem_toFinset.mpr
              (List.mem_map.mpr ⟨r, List.mem_filterMap.mpr ⟨c, hc, hcr⟩, hrb⟩)⟩
          rw [hIarr0, Nat.mul_zero, Nat.zero_div]
        rw [hδ0, Nat.mul_zero]
        exact pow_full_recycleCount_zero h hτm hτmL hfull hbInot
    rw [hgE, hsplit b (ME - 1), hpref, hgEtE]
    omega

/-- **Generation across a general glue, epilogue side.** For the glue of an `A`-trace `tA`
(ending `done s_mid`) onto a `B`-trace `tB` (from `run s_mid B`), a `B`-point `⟨t, |A.prog t| + e⟩`
has generation `recycleCount b tA (|tA|-2) + pointGen B tB ⟨t, e⟩`: its generation in the spliced
trace is its generation in `tB` plus the recycles `b` accrued over the whole `A`-phase. (The
`A`-phase recycle count is a *constant* per `b`, so it **cancels** in any relative comparison of
two such glues sharing the same `A`-phase — which is how the prefix `Pre` drops out of the
shift/front facts.) The `(I^k)^m`-specific `glue_replay_gen` is the instance `A = (I^k)^m`,
where the constant is `m · δ_b`. -/
theorem seq_glue_epilogue_pointGen {A B : CTA} (hids : A.ids = B.ids) {s_A s_mid : State}
    {tA : List Config} (htA : IsSuccessfulTraceFrom (Config.run s_A A) tA)
    (hAlast : tA.getLast? = some (Config.done s_mid))
    {tB : List Config} (htB : IsSuccessfulTraceFrom (Config.run s_mid B) tB)
    {t : ThreadId} {e : Nat} {c : Cmd} {b : Barrier} {par : ℕ+}
    (hcE : B.cmdAt ⟨t, e⟩ = some c) (hbr : Cmd.barrierRef c = some (b, par)) :
    pointGen (A.seq B hids) (tA.dropLast.map (Config.seqLift A B) ++ tB.tail)
        ⟨t, (A.prog t).length + e⟩
      = recycleCount b tA (tA.length - 2) + pointGen B tB ⟨t, e⟩ := by
  obtain ⟨htglue, -, hsnd⟩ := glue_trace hids htA hAlast htB
  set P := A.seq B hids with hPdef
  set τ := tA.dropLast.map (Config.seqLift A B) ++ tB.tail with hτdef
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have heB : e < (B.prog t).length := (List.getElem?_eq_some_iff.mp hcE).1
  have h2 : 2 ≤ tA.length := by
    obtain ⟨⟨⟨_, _⟩, hhead⟩, -⟩ := htA
    rcases tA with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hhead
    · simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hhead] at hAlast; exact absurd hAlast (by simp)
    · simp only [List.length_cons]; omega
  obtain ⟨sdB, hBlast⟩ := htB.2
  obtain ⟨ME, hME⟩ := exists_time_of_ends_done htB.1 hBlast (η := ⟨t, e⟩) heB
  -- suffix transport: the `B`-point executes in `τ` at time `(|tA|-2) + ME`
  have hsuffix : IsTimeOf (Config.run s_A P) τ ⟨t, (A.prog t).length + e⟩
      ((tA.length - 2) + ME) := by
    obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hME
    refine ⟨htglue.1, ?_, (tA.length - 2) + j', D, D', by omega, ?_, ?_, ?_, ?_⟩
    · change (A.prog t).length + e < (A.prog t ++ B.prog t).length
      rw [List.length_append]; omega
    · rw [hsnd j']; exact hDj
    · rw [show (tA.length - 2) + j' + 1 = (tA.length - 2) + (j' + 1) from by omega, hsnd (j' + 1)]
      exact hDj1
    · change D.progOf t = (A.prog t ++ B.prog t).drop ((A.prog t).length + e)
      rw [List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.nil_append,
        Nat.add_sub_cancel_left]
      exact hDprog
    · change D'.progOf t = (A.prog t ++ B.prog t).drop ((A.prog t).length + e + 1)
      rw [List.drop_append,
        List.drop_eq_nil_of_le (show (A.prog t).length ≤ (A.prog t).length + e + 1 by omega),
        List.nil_append, show (A.prog t).length + e + 1 - (A.prog t).length = e + 1 from by omega]
      exact hD'prog
  have hcmdP : P.cmdAt ⟨t, (A.prog t).length + e⟩ = some c := by
    change (A.prog t ++ B.prog t)[(A.prog t).length + e]? = some c
    rw [List.getElem?_append_right (by omega),
      show (A.prog t).length + e - (A.prog t).length = e from by omega]
    exact hcE
  have hMEpos : 1 ≤ ME := by obtain ⟨-, -, j', D, D', hMeq, -, -, -, -⟩ := hME; omega
  have hgP : pointGen P τ ⟨t, (A.prog t).length + e⟩
      = recycleCount b τ ((tA.length - 2) + (ME - 1)) + 1 := by
    simp only [pointGen, hcmdP, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hsuffix,
      show (tA.length - 2) + ME - 1 = (tA.length - 2) + (ME - 1) from by omega]
  have hsplit : recycleCount b τ ((tA.length - 2) + (ME - 1))
      = recycleCount b τ (tA.length - 2) + recycleCount b tB (ME - 1) :=
    recycleCount_suffix b hsnd
  have hfront : recycleCount b τ (tA.length - 2) = recycleCount b tA (tA.length - 2) := by
    have hfst : ∀ q, q ≤ tA.length - 2 → τ[q]? = (tA.map (Config.seqLift A B))[q]? := by
      intro q hq
      rw [hτdef, List.getElem?_append_left
          (by rw [List.length_map, List.length_dropLast]; omega),
        List.getElem?_map, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
    rw [recycleCount_eq_of_getElem?_eq b (fun q hq => hfst q hq),
      recycleCount_map_seqLift A B b tA (tA.length - 2)]
  have hgB : pointGen B tB ⟨t, e⟩ = recycleCount b tB (ME - 1) + 1 := by
    simp only [pointGen, hcE, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hME]
  rw [hgP, hsplit, hfront, hgB]; omega

/-- **Generation across a general glue, prefix side.** For the glue of an `A`-trace `tA`
(ending `done s_mid`) onto a `B`-trace `tB`, an `A`-point `⟨t, idx⟩` (command `c` referencing
`b`, `idx < |A.prog t|`) has the *same* generation as in the standalone `A`-run `tA`: the point
executes during the `A`-phase, whose configurations are the lifted `tA`-prefix, so its time and
recycle prefix are unchanged by appending `B`. This is the A-side companion to
`seq_glue_epilogue_pointGen`; it lets front-agreement extend over the prefix `Pre` (both the full
program and the reference glue the same `tP` in front, so `Pre`-point generations coincide). -/
theorem seq_glue_prefix_pointGen {A B : CTA} (hids : A.ids = B.ids) {s_A s_mid : State}
    {tA : List Config} (htA : IsSuccessfulTraceFrom (Config.run s_A A) tA)
    (hAlast : tA.getLast? = some (Config.done s_mid))
    {tB : List Config} (htB : IsSuccessfulTraceFrom (Config.run s_mid B) tB)
    {t : ThreadId} {idx : Nat} {c : Cmd} {b : Barrier} {par : ℕ+}
    (hcA : A.cmdAt ⟨t, idx⟩ = some c) (hbr : Cmd.barrierRef c = some (b, par)) :
    pointGen (A.seq B hids) (tA.dropLast.map (Config.seqLift A B) ++ tB.tail) ⟨t, idx⟩
      = pointGen A tA ⟨t, idx⟩ := by
  obtain ⟨htglue, -, -⟩ := glue_trace hids htA hAlast htB
  set P := A.seq B hids with hPdef
  set τ := tA.dropLast.map (Config.seqLift A B) ++ tB.tail with hτdef
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have hidxA : idx < (A.prog t).length := by
    have hc : (A.prog t)[idx]? = some c := hcA
    exact (List.getElem?_eq_some_iff.mp hc).1
  -- chain/last facts about `tA`
  have hchainA : List.IsChain CTAStep tA := htA.1.1.subtrace
  have hheadA : tA.head? = some (Config.run s_A A) := htA.1.2
  have hA2 : 2 ≤ tA.length := by
    rcases tA with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hheadA
    · simp only [List.head?_cons, Option.some.injEq] at hheadA
      simp only [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hheadA] at hAlast; exact absurd hAlast (by simp)
    · simp only [List.length_cons]; omega
  -- the penultimate config of `tA` has empty programs
  have hpenA : ∀ (i : ThreadId) (C : Config), tA[tA.length - 2]? = some C → C.progOf i = [] := by
    intro i C hC
    have hdrop : tA.dropLast ≠ [] := by
      intro hd; have : tA.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
      omega
    have hgl : tA.dropLast.getLast? = some C := by
      rw [List.getLast?_eq_getElem?, List.length_dropLast, List.getElem?_dropLast,
        if_pos (by omega), show tA.length - 1 - 1 = tA.length - 2 from by omega]
      exact hC
    exact progOf_penultimate_done hchainA hAlast hgl i
  -- the `A`-point's time `M` in `tA`
  obtain ⟨M, hM⟩ := exists_time_of_ends_done htA.1 hAlast (η := ⟨t, idx⟩) hidxA
  obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := id hM
  change D.progOf t = (A.prog t).drop idx at hDprog
  change D'.progOf t = (A.prog t).drop (idx + 1) at hD'prog
  have hj'1 : j' + 1 < tA.length := (List.getElem?_eq_some_iff.mp hDj1).1
  -- `D` is not the penultimate config (`drop idx ≠ []`), so `j' < |tA| - 2`
  have hDne : D.progOf t ≠ [] := by rw [hDprog, Ne, List.drop_eq_nil_iff]; omega
  have hj'lt : j' < tA.length - 2 := by
    by_contra hcon
    have hje : j' = tA.length - 2 := by omega
    exact hDne (hpenA t D (by rw [← hje]; exact hDj))
  -- the glue front agrees with the lifted `tA` on indices `≤ |tA| - 2`
  have hτget : ∀ q, q ≤ tA.length - 2 → τ[q]? = (tA[q]?).map (Config.seqLift A B) := by
    intro q hq
    rw [hτdef, List.getElem?_append_left
        (by rw [List.length_map, List.length_dropLast]; omega),
      List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  -- the `A`-point executes at the SAME time `M` in `τ` (lifted configs `D`, `D'`)
  have hcmdP : P.cmdAt ⟨t, idx⟩ = some c := by
    change (A.prog t ++ B.prog t)[idx]? = some c
    rw [List.getElem?_append_left hidxA]; exact hcA
  have hMτ : IsTimeOf (Config.run s_A P) τ ⟨t, idx⟩ M := by
    refine ⟨htglue.1, ?_, j', Config.seqLift A B D, Config.seqLift A B D', hMeq, ?_, ?_, ?_, ?_⟩
    · change idx < (A.prog t ++ B.prog t).length
      rw [List.length_append]; omega
    · rw [hτget j' (by omega), hDj]; rfl
    · rw [hτget (j' + 1) (by omega), hDj1]; rfl
    · change (Config.seqLift A B D).progOf t = (A.prog t ++ B.prog t).drop idx
      rw [Config.seqLift_progOf, hDprog, List.drop_append_of_le_length (by omega)]
    · change (Config.seqLift A B D').progOf t = (A.prog t ++ B.prog t).drop (idx + 1)
      rw [Config.seqLift_progOf, hD'prog, List.drop_append_of_le_length (by omega)]
  -- compute both generations and match the (front) recycle counts
  have hgP : pointGen P τ ⟨t, idx⟩ = recycleCount b τ (M - 1) + 1 := by
    simp only [pointGen, hcmdP, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hMτ]
  have hgA : pointGen A tA ⟨t, idx⟩ = recycleCount b tA (M - 1) + 1 := by
    simp only [pointGen, hcA, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
  rw [hgP, hgA]
  congr 1
  have h1 : recycleCount b τ (M - 1) = recycleCount b (tA.map (Config.seqLift A B)) (M - 1) :=
    recycleCount_eq_of_getElem?_eq b (fun q hq => by
      rw [hτget q (by omega), List.getElem?_map])
  rw [h1, recycleCount_map_seqLift A B b tA (M - 1)]

/-- **A `sync`'s generation is at most the trace's total recycle count.** In any successful trace
`tP` of `T` from `run s T` ending in `done s'`, a `sync b` at `⟨t, idx⟩` executing at time `M` has
generation `recycleCount b tP (M-1) + 1`, bounded by the total recycles of `b` over the whole run,
`recycleCount b tP (|tP|-2)`: the sync's own recycle (`sync_time_recycles`) is at step `M ≤ |tP|-2`
(a recycle is a `run → run` step, never the terminal `done`), counted in the total but not in the
strict-prefix count. This generation separation keeps a prefix's `sync` generations strictly below
those of the appended loop body in a glued trace. -/
theorem sync_gen_le_total {T : CTA} {s s' : State} {tP : List Config}
    (htP : IsSuccessfulTraceFrom (Config.run s T) tP)
    (htPL : tP.getLast? = some (Config.done s'))
    {t : ThreadId} {idx : Nat} {b : Barrier} {par : ℕ+}
    (hcj : T.cmdAt ⟨t, idx⟩ = some (Cmd.sync b par)) :
    pointGen T tP ⟨t, idx⟩ ≤ recycleCount b tP (tP.length - 2) := by
  have hchain : List.IsChain CTAStep tP := htP.1.1.subtrace
  have hidxL : idx < (T.prog t).length := (List.getElem?_eq_some_iff.mp hcj).1
  obtain ⟨M, hM⟩ := exists_time_of_ends_done htP.1 htPL (η := ⟨t, idx⟩) hidxL
  have hcmdC : (ProgPoint.mk t idx).cmd (Config.run s T) = some (Cmd.sync b par) := by
    change (T.prog t)[idx]? = some (Cmd.sync b par); exact hcj
  obtain ⟨C, C', hCm1, hCm, hrec⟩ := sync_time_recycles hM hcmdC
  have hM1pos : 1 ≤ M := by obtain ⟨-, -, j', C0, C0', hMeq, -, -, -, -⟩ := hM; omega
  have hM1lt : M < tP.length := (List.getElem?_eq_some_iff.mp hCm).1
  have hM1ne : M ≠ tP.length - 1 := by
    intro he
    have hCmdone : tP[M]? = some (Config.done s') := by
      rw [he, ← List.getLast?_eq_getElem?]; exact htPL
    have hC'done : C' = Config.done s' := by
      rw [hCm, Option.some.injEq] at hCmdone; exact hCmdone
    rw [hC'done] at hrec
    have hstep : CTAStep C (Config.done s') :=
      chain_step hchain hCm1 (by rw [show M - 1 + 1 = M from by omega, hCm, hC'done])
    rw [stepRecyclesBarrier_to_done b C s' hstep] at hrec
    exact absurd hrec (by simp)
  have hM1le : M ≤ tP.length - 2 := by omega
  have hbar : Cmd.barrier? (Cmd.sync b par) = some b := rfl
  have hg : pointGen T tP ⟨t, idx⟩ = recycleCount b tP (M - 1) + 1 := by
    simp only [pointGen, hcj, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
  have hsucc : recycleCount b tP M = recycleCount b tP (M - 1) + 1 := by
    have hsr := recycleCount_succ_of_recycle b tP (p := M - 1) hCm1
      (by rw [show M - 1 + 1 = M from by omega]; exact hCm) hrec
    rwa [show M - 1 + 1 = M from by omega] at hsr
  have hmono : recycleCount b tP M ≤ recycleCount b tP (tP.length - 2) :=
    recycleCount_mono b tP hM1le
  rw [hg]; omega

/-- **A barrier op's generation is at most the trace's total recycle count plus one.** Any
barrier op on `b` at `⟨t, idx⟩` of `T` in a done-ending trace `tP` has generation
`≤ recycleCount b tP (|tP|-2) + 1`: it executes at some time `M ≤ |tP|-1`, so the recycles
strictly before it are `≤` the total. (For `sync`s `sync_gen_le_total` sharpens this by one.) -/
theorem barrierOp_gen_le_total {T : CTA} {s s' : State} {tP : List Config}
    (htP : IsSuccessfulTraceFrom (Config.run s T) tP)
    (htPL : tP.getLast? = some (Config.done s'))
    {t : ThreadId} {idx : Nat} {c : Cmd} {b : Barrier} {par : ℕ+}
    (hcj : T.cmdAt ⟨t, idx⟩ = some c) (hbr : Cmd.barrierRef c = some (b, par)) :
    pointGen T tP ⟨t, idx⟩ ≤ recycleCount b tP (tP.length - 2) + 1 := by
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have hidxL : idx < (T.prog t).length := (List.getElem?_eq_some_iff.mp hcj).1
  obtain ⟨M, hM⟩ := exists_time_of_ends_done htP.1 htPL (η := ⟨t, idx⟩) hidxL
  have hMlt : M < tP.length := by
    obtain ⟨-, -, j', C0, C0', hMeq, -, hC0', -, -⟩ := hM
    have := (List.getElem?_eq_some_iff.mp hC0').1; omega
  have hg : pointGen T tP ⟨t, idx⟩ = recycleCount b tP (M - 1) + 1 := by
    simp only [pointGen, hcj, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
  rw [hg]
  have : recycleCount b tP (M - 1) ≤ recycleCount b tP (tP.length - 2) :=
    recycleCount_mono b tP (by omega)
  omega

/-- **A barrier op of a successful trace has positive generation.** In a done-ending trace every
program point is executed, so a barrier op on `b` has `pointGen ≥ 1`. -/
theorem one_le_pointGen_barrierOp {T : CTA} {s s' : State} {tP : List Config}
    (htP : IsSuccessfulTraceFrom (Config.run s T) tP)
    (htPL : tP.getLast? = some (Config.done s'))
    {t : ThreadId} {idx : Nat} {c : Cmd} {b : Barrier} {par : ℕ+}
    (hcj : T.cmdAt ⟨t, idx⟩ = some c) (hbr : Cmd.barrierRef c = some (b, par)) :
    1 ≤ pointGen T tP ⟨t, idx⟩ := by
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have hidxL : idx < (T.prog t).length := (List.getElem?_eq_some_iff.mp hcj).1
  obtain ⟨M, hM⟩ := exists_time_of_ends_done htP.1 htPL (η := ⟨t, idx⟩) hidxL
  have hg : pointGen T tP ⟨t, idx⟩ = recycleCount b tP (M - 1) + 1 := by
    simp only [pointGen, hcj, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
  omega

/-- **Front-batch generation of an angelic epilogue trace.** When `tE` is the *structured*
successful trace of `B := (I^k) ⨾ E` obtained from `seq_angelic_prefix` applied to the
single-batch trace `t₁` (so `t₁.dropLast` lifted is a prefix of `tE`, `htEpre`), the generation
of a front-batch barrier point `⟨t, j⟩` (`j < L`, command `c` referencing barrier `b`, with
`t₁`-time `M₁`) in `tE` is exactly the standalone `(I^k)`-run value `recycleCount b t₁ (M₁-1)+1`.
The `(I^k)`-phase of `tE` *is* the lifted `t₁`, so `⟨t,j⟩` executes at the same time `M₁` and the
recycle count over its prefix is unchanged across the lift (`recycleCount_map_seqLift`). This is
the "inverse-glue" fact the front-agreement residual (`n=1`, `p=1`) and the co-location epilogue
case need: that `B`'s first-batch sync generations match a standalone batch run. -/
theorem seq_front_pointGen {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s)) {E : CTA}
    (hids : (I ^ I.loopK h).ids = E.ids) {tE : List Config}
    (htE : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h).seq E hids)) tE)
    (htEpre : t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) E) <+: tE)
    {t : ThreadId} {j : Nat} {c : Cmd} {b : Barrier} {par : ℕ+} {M₁ : Nat}
    (hjL : j < ((I ^ I.loopK h).prog t).length)
    (hcj : ((I ^ I.loopK h).prog t)[j]? = some c) (hbr : Cmd.barrierRef c = some (b, par))
    (hM₁ : IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁) :
    pointGen ((I ^ I.loopK h).seq E hids) tE ⟨t, j⟩ = recycleCount b t₁ (M₁ - 1) + 1 := by
  set A := I ^ I.loopK h with hA
  set B := A.seq E hids with hB
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  -- chain/last facts about `t₁`
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead1 : t₁.head? = some (Config.run s A) := ht₁.1.2
  have h1ne : t₁ ≠ [] := fun hd => by rw [hd] at hhead1; simp at hhead1
  have h12 : 2 ≤ t₁.length := by
    rcases t₁ with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hhead1
    · simp only [List.head?_cons, Option.some.injEq] at hhead1
      simp only [List.getLast?_singleton, Option.some.injEq] at ht₁L
      rw [hhead1] at ht₁L; exact absurd ht₁L (by simp)
    · simp only [List.length_cons]; omega
  -- the penultimate config of `t₁` has empty `A`-programs
  have hpen1 : ∀ (i : ThreadId) (C : Config), t₁[t₁.length - 2]? = some C → C.progOf i = [] := by
    intro i C hC
    have hdrop : t₁.dropLast ≠ [] := by
      intro hd; have : t₁.length - 1 = 0 := by rw [← List.length_dropLast, hd]; rfl
      omega
    have hgl : t₁.dropLast.getLast? = some C := by
      rw [List.getLast?_eq_getElem?, List.length_dropLast, List.getElem?_dropLast,
        if_pos (by omega), show t₁.length - 1 - 1 = t₁.length - 2 from by omega]
      exact hC
    exact progOf_penultimate_done hchain1 ht₁L hgl i
  -- destructure the time witness; normalise the `progOf` to `A.prog`/`B.prog` form
  obtain ⟨-, -, j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hM₁
  change D.progOf t = (A.prog t).drop j at hDprog
  change D'.progOf t = (A.prog t).drop (j + 1) at hD'prog
  have hj'1 : j' + 1 < t₁.length := (List.getElem?_eq_some_iff.mp hDj1).1
  -- `D` is not the penultimate config: `D.progOf t = (A.prog t).drop j ≠ []`
  have hDne : D.progOf t ≠ [] := by
    rw [hDprog]; rw [Ne, List.drop_eq_nil_iff]; omega
  have hj'lt : j' < t₁.length - 2 := by
    by_contra hcon
    have hje : j' = t₁.length - 2 := by omega
    exact hDne (hpen1 t D (by rw [← hje]; exact hDj))
  -- the lifted prefix agrees with `tE` on indices `≤ t₁.length - 2`
  set tlift := t₁.dropLast.map (Config.seqLift A E) with htliftdef
  obtain ⟨ss, htEeq⟩ := htEpre
  have hliftlen : tlift.length = t₁.length - 1 := by
    rw [htliftdef, List.length_map, List.length_dropLast]
  have htEget : ∀ q, q ≤ t₁.length - 2 → tE[q]? = tlift[q]? := by
    intro q hq
    rw [← htEeq, List.getElem?_append_left (by rw [hliftlen]; omega)]
  have htliftget : ∀ q, q < t₁.length - 1 → tlift[q]? = (t₁[q]?).map (Config.seqLift A E) := by
    intro q hq
    rw [htliftdef, List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  -- `⟨t,j⟩` executes at the SAME time `M₁` in `tE` (lifted configs `D`, `D'`)
  have hcmdB : B.cmdAt ⟨t, j⟩ = some c := by
    change (A.prog t ++ E.prog t)[j]? = some c
    rw [List.getElem?_append_left hjL]; exact hcj
  have hME : IsTimeOf (Config.run s B) tE ⟨t, j⟩ M₁ := by
    refine ⟨htE.1, ?_, j', Config.seqLift A E D, Config.seqLift A E D', hMeq, ?_, ?_, ?_, ?_⟩
    · change j < (B.prog t).length
      change j < (A.prog t ++ E.prog t).length
      rw [List.length_append]; omega
    · rw [htEget j' (by omega), htliftget j' (by omega), hDj]; rfl
    · rw [htEget (j' + 1) (by omega), htliftget (j' + 1) (by omega), hDj1]; rfl
    · change (Config.seqLift A E D).progOf t = (B.prog t).drop j
      rw [Config.seqLift_progOf, hDprog]
      change (A.prog t).drop j ++ E.prog t = (A.prog t ++ E.prog t).drop j
      rw [List.drop_append_of_le_length (by omega)]
    · change (Config.seqLift A E D').progOf t = (B.prog t).drop (j + 1)
      rw [Config.seqLift_progOf, hD'prog]
      change (A.prog t).drop (j + 1) ++ E.prog t = (A.prog t ++ E.prog t).drop (j + 1)
      rw [List.drop_append_of_le_length (by omega)]
  -- compute the generation; the recycle count over the front prefix agrees with `t₁`'s
  have hg : pointGen B tE ⟨t, j⟩ = recycleCount b tE (M₁ - 1) + 1 := by
    simp only [pointGen, hcmdB, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hME]
  rw [hg]
  -- `M₁ - 1 = j' ≤ t₁.length - 2`, so the front recycle count of `tE` matches the lifted `t₁`'s
  have hM1m1 : M₁ - 1 = j' := by omega
  rw [hM1m1]
  -- step 1: `recycleCount b tE j' = recycleCount b tlift j'` (front prefix agreement)
  have hstep1 : recycleCount b tE j' = recycleCount b tlift j' :=
    recycleCount_eq_of_getElem?_eq b (fun q hq => htEget q (by omega))
  -- step 2: `recycleCount b tlift j' = recycleCount b t₁.dropLast j'` (the lift is transparent)
  have hstep2 : recycleCount b tlift j' = recycleCount b t₁.dropLast j' := by
    rw [htliftdef, recycleCount_map_seqLift A E b t₁.dropLast j']
  -- step 3: `recycleCount b t₁.dropLast j' = recycleCount b t₁ j'` (`dropLast` agrees up to `j'`)
  have hstep3 : recycleCount b t₁.dropLast j' = recycleCount b t₁ j' :=
    recycleCount_prefix_eq b j' (fun q hq => by
      rw [List.getElem?_dropLast, if_pos (by omega)])
  rw [hstep1, hstep2, hstep3]

/-- **Epilogue-region generation lower bound.** In the *structured* trace `tE` (its `(I^k)`-phase
is the complete lifted `t₁`, via `htEpre`), a point `⟨t, e⟩` *strictly past* the front batch
(`L ≤ e`, so it lies in `E`'s segment of `B = (I^k) ⨾ E`) and referencing a batch-used barrier
`b` has generation at least `δ + 1`.  The point executes only after the whole `(I^k)`-phase has
run (its predecessor index `ME-1 ≥ t₁.length-2`), by which time `b` has already recycled exactly
`δ = recycleCount b t₁ (t₁.length-2)` times; the generation is that count `+ 1`. -/
theorem seq_epilogue_pointGen_lower {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s)) {E : CTA}
    (hids : (I ^ I.loopK h).ids = E.ids) {tE : List Config}
    (htE : IsSuccessfulTraceFrom (Config.run s ((I ^ I.loopK h).seq E hids)) tE)
    (htEpre : t₁.dropLast.map (Config.seqLift (I ^ I.loopK h) E) <+: tE)
    {t : ThreadId} {e : Nat} {c : Cmd} {b : Barrier} {par : ℕ+}
    (heL : ((I ^ I.loopK h).prog t).length ≤ e)
    (hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c)
    (hbr : Cmd.barrierRef c = some (b, par)) (hbA : b ∈ (I ^ I.loopK h).barrierSet)
    (hwf_s : (Config.run s (I ^ I.loopK h)).WF) (hfull : ∀ b, (s.B b).isFull = false) :
    I.loopK h * I.arrivers b / I.arrivalCount h b + 1
      ≤ pointGen ((I ^ I.loopK h).seq E hids) tE ⟨t, e⟩ := by
  set A := I ^ I.loopK h with hA
  set B := A.seq E hids with hB
  set δ := I.loopK h * I.arrivers b / I.arrivalCount h b with hδdef
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have hchain1 : List.IsChain CTAStep t₁ := ht₁.1.1.subtrace
  have hhead1 : t₁.head? = some (Config.run s A) := ht₁.1.2
  -- `t₁` has length ≥ 2 (starts `run`, ends `done`)
  have h12 : 2 ≤ t₁.length := by
    rcases t₁ with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hhead1
    · simp only [List.head?_cons, Option.some.injEq] at hhead1
      simp only [List.getLast?_singleton, Option.some.injEq] at ht₁L
      rw [hhead1] at ht₁L; exact absurd ht₁L (by simp)
    · simp only [List.length_cons]; omega
  -- the front `(I^k)`-phase recycles `b` exactly `δ` times
  have hΔ : recycleCount b t₁ (t₁.length - 2) = δ := by
    rw [← recycleCount_done_last hchain1 ht₁L h12]
    exact Config.WellSynchronized.pow_barriers_advance_count h hwf_s (hfull b) ht₁ hbA
  -- length facts about `B`
  have heB : e < (B.prog t).length := (List.getElem?_eq_some_iff.mp hcE).1
  have hBlen : (B.prog t).length = (A.prog t).length + (E.prog t).length := by
    change (A.prog t ++ E.prog t).length = _; rw [List.length_append]
  -- the lifted prefix agrees with `tE` on indices `≤ t₁.length - 2`; front configs keep `E.prog t`
  set tlift := t₁.dropLast.map (Config.seqLift A E) with htliftdef
  obtain ⟨ss, htEeq⟩ := htEpre
  have hliftlen : tlift.length = t₁.length - 1 := by
    rw [htliftdef, List.length_map, List.length_dropLast]
  have htEget : ∀ q, q < t₁.length - 1 → tE[q]? = (t₁[q]?).map (Config.seqLift A E) := by
    intro q hq
    rw [← htEeq, List.getElem?_append_left (by rw [hliftlen]; omega), htliftdef,
      List.getElem?_map, List.getElem?_dropLast, if_pos (by omega)]
  -- the E-point executes at some time `ME`
  obtain ⟨sdE, hElast⟩ := htE.2
  obtain ⟨ME, hME⟩ := exists_time_of_ends_done htE.1 hElast (η := ⟨t, e⟩) heB
  -- `ME ≥ t₁.length - 1`: the successor config `D'` is a strict tail of `E.prog t`, which no
  -- front-phase config (which still carries the *full* `E.prog t` as a suffix) can be.
  obtain ⟨j', D, D', hMeq, hDj, hDj1, hDprog, hD'prog⟩ := hME.2.2
  have hD'prog' : D'.progOf t = (B.prog t).drop (e + 1) := hD'prog
  have hD'len : (D'.progOf t).length < (E.prog t).length := by
    rw [hD'prog']
    change ((A.prog t ++ E.prog t).drop (e + 1)).length < (E.prog t).length
    rw [List.length_drop, List.length_append]; omega
  have hMElt : t₁.length - 1 ≤ ME := by
    by_contra hcon
    have hj'lt : j' < t₁.length - 1 := by omega
    have hget := htEget (j' + 1) (by omega)
    rw [hDj1, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.mp hDj1).1; omega), Option.map_some,
      Option.some.injEq] at hget
    rw [hget, Config.seqLift_progOf, List.length_append] at hD'len
    omega
  -- monotonicity: `recycleCount b tE (ME-1) ≥ recycleCount b tE (t₁.length-2) = δ`
  have hmono : recycleCount b tE (t₁.length - 2) ≤ recycleCount b tE (ME - 1) :=
    recycleCount_mono b tE (by omega)
  -- front recycle count of `tE` equals `t₁`'s (lift is transparent, dropLast agrees up to `j'`)
  have hfront : recycleCount b tE (t₁.length - 2) = δ := by
    rw [← hΔ]
    rw [show recycleCount b tE (t₁.length - 2)
        = recycleCount b tlift (t₁.length - 2) from
      recycleCount_eq_of_getElem?_eq b (fun q hq => by
        rw [← htEeq, List.getElem?_append_left (by rw [hliftlen]; omega)])]
    rw [htliftdef, recycleCount_map_seqLift A E b t₁.dropLast (t₁.length - 2)]
    exact recycleCount_prefix_eq b (t₁.length - 2) (fun q hq => by
      rw [List.getElem?_dropLast, if_pos (by omega)])
  -- compute the generation
  have hg : pointGen B tE ⟨t, e⟩ = recycleCount b tE (ME - 1) + 1 := by
    simp only [pointGen, hcE, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hME]
  rw [hg]
  omega

/-- **Program order is happens-before.** Consecutive same-thread program points are joined by the
program-order edges of `initRelation`, so `⟨t, i⟩` happens-before `⟨t, j⟩` whenever
`i ≤ j < |T.prog t|`. (Used to lift the `Pre`↔loop seam edge to a multi-step path in the prefix
monotonicity.) -/
theorem happensBefore_progOrder {T : CTA} {τ : List Config} {t : ThreadId} {i j : Nat}
    (hij : i ≤ j) (hj : j < (T.prog t).length) :
    happensBefore T τ ⟨t, i⟩ ⟨t, j⟩ := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
    have hjlt : j < (T.prog t).length := by omega
    refine (ih hjlt).tail ?_
    rw [mem_initRelation_iff]
    exact Or.inl ⟨(mem_progPoints_iff T ⟨t, j⟩).mpr ⟨mem_ids_of_idx_lt T hjlt, hjlt⟩, hj, rfl⟩

/-- **No happens-before edge runs from `B` back into `A`, given an explicit `A`-completion.** The
trace-parameterized analogue of `seq_no_happensBefore_B_to_A_impl`: instead of `WS(A)` (which we
lack for a non-well-synchronized prefix `A = Pre ⨾ (I^k)^2`), we supply a successful `A`-trace `tA`
(from `initial`, ending `done s_mid`) directly. The angelic schedule that runs `A` fully then `B`
is `glue(tA, B-completion)`, where the `B`-completion comes from `WS(A ⨾ B)` via `seq_angelic_tail`.
In it every `A`-instruction runs strictly before every `B`-instruction, so soundness
(`happensBefore_sound`) forbids any happens-before pair from a `B`-point to an `A`-point. -/
theorem glue_no_happensBefore_B_to_A {A B : CTA} (hids : A.ids = B.ids)
    (hAB : (A.seq B hids).WellSynchronized)
    {tA : List Config} (htA : IsSuccessfulTraceFrom (Config.run State.initial A) tA)
    {s_mid : State} (hAlast : tA.getLast? = some (Config.done s_mid))
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) τ) :
    ¬ ∃ s d : ProgPoint,
        happensBefore (A.seq B hids) τ s d ∧
        ((A.prog s.thread).length ≤ s.idx ∧
          s.idx < (A.prog s.thread).length + (B.prog s.thread).length) ∧
        d.idx < (A.prog d.thread).length := by
  rintro ⟨s, d, hR, ⟨hsB1, hsB2⟩, hdA⟩
  have hC0prog : ∀ i, (Config.run State.initial (A.seq B hids)).progOf i
      = A.prog i ++ B.prog i := fun _ => rfl
  have hsound := happensBefore_sound hτ hAB hR
  -- angelic schedule: run `A` fully (`tA`), then complete `B` from `s_mid`, glued
  obtain ⟨tB', htB'⟩ := CTA.WellSynchronized.seq_angelic_tail hids hAB htA hAlast
  obtain ⟨ht'succ, -, -⟩ := glue_trace hids htA hAlast htB'
  set P := tA.dropLast.map (Config.seqLift A B) with hPdef
  set t' := tA.dropLast.map (Config.seqLift A B) ++ tB'.tail with ht'def
  have hrest : P ++ tB'.tail = t' := rfl
  obtain ⟨sdone, htlast⟩ := ht'succ.2
  have ht'complete : IsCompleteTraceFrom (Config.run State.initial (A.seq B hids)) t' := ht'succ.1
  have ht'chain : List.IsChain CTAStep t' := ht'complete.1.subtrace
  obtain ⟨n₂, htd⟩ : ∃ n, IsTimeOf (Config.run State.initial (A.seq B hids)) t' d n :=
    exists_time_of_ends_done (η := d) ht'complete htlast
      (by rw [hC0prog, List.length_append]; omega)
  obtain ⟨n₁, hts⟩ : ∃ n, IsTimeOf (Config.run State.initial (A.seq B hids)) t' s n :=
    exists_time_of_ends_done (η := s) ht'complete htlast
      (by rw [hC0prog, List.length_append]; omega)
  -- `P` (the `A`-phase) is nonempty: `tA` has length ≥ 2
  have hthead : tA.head? = some (Config.run State.initial A) := htA.1.2
  have htlen2 : 2 ≤ tA.length := by
    rcases tA with _ | ⟨c0, _ | ⟨c1, tr⟩⟩
    · simp at hthead
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      simp only [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hthead] at hAlast; simp at hAlast
    · simp only [List.length_cons]; omega
  have hPlen : P.length = tA.length - 1 := by rw [hPdef, List.length_map, List.length_dropLast]
  have hPpos : 0 < P.length := by rw [hPlen]; omega
  have hPne : P ≠ [] := List.ne_nil_of_length_pos hPpos
  have hdropne : tA.dropLast ≠ [] := fun hd => hPne (by rw [hPdef, hd, List.map_nil])
  obtain ⟨Cstar, hCstar⟩ : ∃ C, P.getLast? = some C := by
    cases hPl : P.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hPl; exact absurd hPl hPne
    | some C => exact ⟨C, rfl⟩
  have hXempty : ∀ i, (tA.dropLast.getLast hdropne).progOf i = [] := fun i =>
    progOf_penultimate_done htA.1.1.subtrace hAlast (List.getLast?_eq_some_getLast hdropne) i
  have hCstarprog : ∀ i, Cstar.progOf i = B.prog i := by
    intro i
    have hmap : P.getLast? = (tA.dropLast.getLast?).map (Config.seqLift A B) := by
      rw [hPdef, List.getLast?_map]
    rw [List.getLast?_eq_some_getLast hdropne, Option.map_some, hCstar, Option.some.injEq] at hmap
    rw [hmap, Config.seqLift_progOf, hXempty i, List.nil_append]
  have hp : P.length - 1 < P.length := by omega
  have hCstaridx : t'[P.length - 1]? = some Cstar := by
    rw [← hrest, List.getElem?_append_left hp, ← List.getLast?_eq_getElem?]; exact hCstar
  have hPinv : ∀ q (C : Config), q < P.length → t'[q]? = some C →
      ∀ i, (B.prog i).length ≤ (C.progOf i).length := by
    intro q C hq hCq i
    rw [← hrest, List.getElem?_append_left hq, hPdef, List.getElem?_map] at hCq
    obtain ⟨X', _, hCeq⟩ := Option.map_eq_some_iff.mp hCq
    rw [← hCeq, Config.seqLift_progOf, List.length_append]; omega
  have hTinv : ∀ q (C : Config), P.length - 1 ≤ q → t'[q]? = some C →
      ∀ i, (C.progOf i).length ≤ (B.prog i).length := by
    intro q C hq hCq i
    have hsuf := progOf_suffix_index_le ht'chain i hCstaridx hq hCq
    have hle := suffix_length_le hsuf
    rwa [hCstarprog i] at hle
  obtain ⟨-, -, jd, Cd, _Cd', hn₂eq, hCdj, _, hCdeq, _⟩ := id htd
  have hCdlen : (Cd.progOf d.thread).length
      = (A.prog d.thread).length + (B.prog d.thread).length - d.idx := by
    rw [hCdeq, hC0prog, List.length_drop, List.length_append]
  have hjd : jd < P.length - 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h := hTinv jd Cd hcon hCdj d.thread
    rw [hCdlen] at h; omega
  obtain ⟨-, -, js, _Cs, Cs', hn₁eq, _, hCsj1, _, hCs'eq⟩ := id hts
  have hCs'len : (Cs'.progOf s.thread).length
      = (A.prog s.thread).length + (B.prog s.thread).length - (s.idx + 1) := by
    rw [hCs'eq, hC0prog, List.length_drop, List.length_append]
  have hjs : P.length ≤ js + 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have h := hPinv (js + 1) Cs' hcon hCsj1 s.thread
    rw [hCs'len] at h; omega
  have hlt : n₂ < n₁ := by omega
  have hle : n₁ ≤ n₂ := hsound t' ht'complete n₁ n₂ hts htd
  omega

/-- **Prefix-loop batch data.** From the prefix-loop hypotheses `WS(Pre)`, `WS(Pre ⨾ I^k)`,
`WS(Pre ⨾ I^k ⨾ E)`, construct the data the from-`s_P` replay bundle needs: the post-prefix
done-state `s_P`, its done-state properties (`isFull = false`, `WF` for any body), a restoring
single-batch trace `t₁` of `I^k` from `s_P` (`WS(Pre ⨾ I^k)` makes the body terminate on its own,
and `pow_done_state_restored` returns it to `s_P`), and the structured epilogue trace `tE` of
`I^k ⨾ E` from `s_P` whose `I^k`-phase is exactly the lift of `t₁` (glued from `t₁` and the
`E`-completion of `WS((Pre ⨾ I^k) ⨾ E)`). This is the non-initial-start analogue of the
`exists_successfulTrace`/`seq_angelic_prefix` opening of `loop_epilogue_replay_bundle`. -/
theorem loop_prefix_batch_data {I : CTA} (h : I.ConsistentArrivalCounts) {k : Nat}
    (hk : k = I.loopK h) {Pre E : CTA} (hpre : Pre.ids = (I ^ k).ids) (hids : (I ^ k).ids = E.ids)
    (hPre : Pre.WellSynchronized) (hPreBody : (Pre.seq (I ^ k) hpre).WellSynchronized)
    (hPreBatchE : (CTA.loopProgram Pre (I ^ k) E hpre hids 1).WellSynchronized) :
    ∃ s_P, (∀ b, (s_P.B b).isFull = false) ∧ (∀ (T : CTA), (Config.run s_P T).WF) ∧
      ∃ tP, IsSuccessfulTraceFrom (Config.run State.initial Pre) tP ∧
        tP.getLast? = some (Config.done s_P) ∧
      ∃ t₁, IsSuccessfulTraceFrom (Config.run s_P (I ^ k)) t₁ ∧
        t₁.getLast? = some (Config.done s_P) ∧
        ∃ tE, IsSuccessfulTraceFrom (Config.run s_P ((I ^ k).seq E hids)) tE ∧
          t₁.dropLast.map (Config.seqLift (I ^ k) E) <+: tE := by
  subst hk
  -- (1) a `Pre`-trace from `initial`, ending in `done s_P`, and `s_P`'s done-state properties
  obtain ⟨tP, htP⟩ := hPre.exists_successfulTrace
  obtain ⟨s_P, htPL⟩ := htP.2
  obtain ⟨hsE, hsync, hfull, hwf_any⟩ := done_state_of_successfulTrace htP htPL
  -- (2) the restoring single-batch trace `t₁` of `I^k` from `s_P`
  obtain ⟨t₁, ht₁⟩ := CTA.WellSynchronized.seq_angelic_tail hpre hPreBody htP htPL
  obtain ⟨s₁, ht₁L⟩ := ht₁.2
  have hs₁ : s₁ = s_P :=
    pow_done_state_restored h (hwf_any (I ^ I.loopK h)) hfull hsE hsync ht₁ ht₁L
  rw [hs₁] at ht₁L
  refine ⟨s_P, hfull, hwf_any, tP, htP, htPL, t₁, ht₁, ht₁L, ?_⟩
  -- (3) glue `tP` onto `t₁` to get a `Pre ⨾ I^k` trace ending `done s_P`
  obtain ⟨htPk, htPklast0, -⟩ := glue_trace hpre htP htPL ht₁
  have htPklast : (tP.dropLast.map (Config.seqLift Pre (I ^ I.loopK h)) ++ t₁.tail).getLast?
      = some (Config.done s_P) := htPklast0.trans ht₁L
  -- (4) view `WS(Pre ⨾ I^k ⨾ E)` as `WS((Pre ⨾ I^k) ⨾ E)` and complete `E` from `s_P`
  have hids2 : (Pre.seq (I ^ I.loopK h) hpre).ids = E.ids := hpre.trans hids
  have hreassoc : CTA.loopProgram Pre (I ^ I.loopK h) E hpre hids 1
      = (Pre.seq (I ^ I.loopK h) hpre).seq E hids2 := by
    apply CTA.ext
    · simp only [CTA.loopProgram_ids, CTA.seq]
    · funext t
      rw [CTA.loopProgram_prog]
      change Pre.prog t ++ ((I ^ I.loopK h) ^ 1).prog t ++ E.prog t
        = Pre.prog t ++ (I ^ I.loopK h).prog t ++ E.prog t
      rw [CTA.pow_one_prog]
  rw [hreassoc] at hPreBatchE
  obtain ⟨tE_E, htE_E⟩ :=
    CTA.WellSynchronized.seq_angelic_tail hids2 hPreBatchE htPk htPklast
  -- (5) glue `t₁` (the `I^k`-phase) onto `tE_E` (the `E`-phase) to get `tE`
  obtain ⟨htE, -, -⟩ := glue_trace hids ht₁ ht₁L htE_E
  exact ⟨_, htE, List.prefix_append _ _⟩

/-- **Prefix-loop reference data.** From `WS(Pre ⨾ (I^k)^2 ⨾ E_ref)` and the prefix data
(`s_P`, `tP`, the restoring batch `t₁`), produce (a) a structured `(I^k) ⨾ E_ref`-from-`s_P` trace
`tER` whose `(I^k)`-phase is the lift of `t₁` — exactly what the from-`s_P` bundle needs to build a
`(I^k)^2 ⨾ E_ref` replay with controlled front generations — and (b) a `Pre ⨾ (I^k)^2`-trace `tAR`
from `initial` ending `done s_P`, the explicit `A`-completion the front-case confinement
(`glue_no_happensBefore_B_to_A`, `A := Pre ⨾ (I^k)^2`) consumes. Both are built by the same
glue/`seq_angelic_tail` recipe as `loop_prefix_batch_data`'s `tE`, but with two body batches. -/
theorem loop_prefix_ref_data {I : CTA} (h : I.ConsistentArrivalCounts) {k : Nat}
    (hk : k = I.loopK h) {Pre E_ref : CTA} (hpre : Pre.ids = (I ^ k).ids)
    (hidsRef : (I ^ k).ids = E_ref.ids)
    {s_P : State} (hfull : ∀ b, (s_P.B b).isFull = false)
    (hwf_any : ∀ (T : CTA), (Config.run s_P T).WF)
    {tP : List Config} (htP : IsSuccessfulTraceFrom (Config.run State.initial Pre) tP)
    (htPL : tP.getLast? = some (Config.done s_P))
    {t₁ : List Config} (ht₁ : IsSuccessfulTraceFrom (Config.run s_P (I ^ k)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s_P))
    (hPre3BatchRef : (CTA.loopProgram Pre (I ^ k) E_ref hpre hidsRef 3).WellSynchronized) :
    (∃ tER, IsSuccessfulTraceFrom (Config.run s_P ((I ^ k).seq E_ref hidsRef)) tER ∧
        t₁.dropLast.map (Config.seqLift (I ^ k) E_ref) <+: tER) ∧
    (∃ tAR, IsSuccessfulTraceFrom (Config.run State.initial
        (Pre.seq ((I ^ k) ^ 3) (hpre.trans (CTA.pow_ids (I ^ k) 3).symm))) tAR ∧
        tAR.getLast? = some (Config.done s_P)) := by
  subst hk
  set A := I ^ I.loopK h with hA
  have hpre2 : Pre.ids = (A ^ 3).ids := hpre.trans (CTA.pow_ids A 3).symm
  -- (1) a `(I^k)^3`-replay from `s_P` (ends `done s_P`)
  obtain ⟨τ2P, hτ2P, hτ2PL, -⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L (hwf_any A) hfull 3
  -- (2) glue `tP` onto it → a `Pre ⨾ (I^k)^3`-trace `tAR` ending `done s_P`
  obtain ⟨htAR, htARlast0, -⟩ := glue_trace hpre2 htP htPL hτ2P
  have htARlast : (tP.dropLast.map (Config.seqLift Pre (A ^ 3)) ++ τ2P.tail).getLast?
      = some (Config.done s_P) := htARlast0.trans hτ2PL
  -- (3) view `WS(Pre ⨾ (I^k)^3 ⨾ E_ref)` as `WS((Pre ⨾ (I^k)^3) ⨾ E_ref)`, complete `E_ref`
  have hids2 : (Pre.seq (A ^ 3) hpre2).ids = E_ref.ids := hpre.trans hidsRef
  have hreassoc : CTA.loopProgram Pre A E_ref hpre hidsRef 3
      = (Pre.seq (A ^ 3) hpre2).seq E_ref hids2 := by
    apply CTA.ext
    · simp only [CTA.loopProgram_ids, CTA.seq]
    · funext t
      rw [CTA.loopProgram_prog]
      change Pre.prog t ++ (A ^ 3).prog t ++ E_ref.prog t
        = Pre.prog t ++ (A ^ 3).prog t ++ E_ref.prog t
      rfl
  rw [hreassoc] at hPre3BatchRef
  obtain ⟨tER_E, htER_E⟩ :=
    CTA.WellSynchronized.seq_angelic_tail hids2 hPre3BatchRef htAR htARlast
  -- (4) glue `t₁` (the `I^k`-phase) onto `tER_E` (the `E_ref`-phase) → `tER`
  obtain ⟨htER, -, -⟩ := glue_trace hidsRef ht₁ ht₁L htER_E
  exact ⟨⟨_, htER, List.prefix_append _ _⟩, ⟨_, htAR, htARlast⟩⟩

/-- **Epilogue replay/generation bundle** (the analogue of `last_batches_replay_bundle` for a
program-with-epilogue; proof deferred). By `pow_succ_seq_assoc` the full program
`P := (I^k)^(n+1) ⨾ E` is the one-batch-shorter `Pn := (I^k)^n ⨾ E` with a single batch `I^k`
*prepended* at the front, so `Pn` embeds into `P` by the uniform index shift
`⟨t, i⟩ ↦ ⟨t, i + L t⟩`, `L t = |(I^k).prog t|`. The bundle produces a replay trace of `P`, of `Pn`,
and of the first two batches `(I^k)^2`, plus the facts the inductive step's casework consumes
(abbreviating `δ b = k·arrivers(b)/count(b)`):

* **(co-location)** any flagged line-18 pair `(c1, c2)` either lands entirely in the first two
  batches (`idx < 2L`) or is entirely shiftable into the prefix (`c1.idx ≥ L` and `c2.idx > L`).
  This packages the `(L)`/`(U)` generation-bound bookkeeping that places the pair by batch.
* **(uniform shift / monotonicity)** for the shiftable case: every `Pn`-barrier's generation
  bumps by `δ` under the `+L` embedding, and `Pn`'s happens-before lifts to `P` under it — the
  user's "the generations all just shift by the factor that `I^k` adds";
* **(front agreement / monotonicity)** for the first-two-batch case: generations and
  happens-before on `idx < 2L` agree with the literal front prefix `(I^k)^2` (whose
  well-synchronization the step gets from `h2batch`). -/
theorem CTA.WellSynchronized.loop_epilogue_replay_bundle {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {E : CTA}
    (hids : (I ^ k).ids = E.ids) {n : Nat} (hn : 1 ≤ n)
    {s : State} {t₁ : List Config}
    (ht₁ : IsSuccessfulTraceFrom (Config.run s (I ^ k)) t₁)
    (ht₁L : t₁.getLast? = some (Config.done s)) {tE : List Config}
    (htE : IsSuccessfulTraceFrom (Config.run s ((I ^ k).seq E hids)) tE)
    (htEpre : t₁.dropLast.map (Config.seqLift (I ^ k) E) <+: tE)
    (hfull : ∀ b, (s.B b).isFull = false) (hwf_any : ∀ (T : CTA), (Config.run s T).WF) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run s
        (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids))) τ ∧
      -- (co-location) a flagged pair is front-local or fully shiftable
      (∀ (c1 c2 : ProgPoint) (bb : Barrier) (nn2 : ℕ+),
          (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt c1
            = some (Cmd.sync bb nn2) →
          ((((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt c2).bind
            Cmd.barrier? = some bb →
          pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ c2
            = pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ c1
              + 1 →
          1 ≤ c2.idx →
          (c1.idx < 2 * ((I ^ k).prog c1.thread).length ∧
              c2.idx < 2 * ((I ^ k).prog c2.thread).length) ∨
            (((I ^ k).prog c1.thread).length ≤ c1.idx ∧
              ((I ^ k).prog c2.thread).length < c2.idx)) ∧
      ∃ τn, IsSuccessfulTraceFrom (Config.run s
          (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids))) τn ∧
        -- (uniform shift)
        (∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
            (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)).cmdAt η = some c →
            Cmd.barrierRef c = some (b, par) →
            pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                ⟨η.thread, η.idx + ((I ^ k).prog η.thread).length⟩
              = pointGen (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)) τn η
                + k * I.arrivers b / I.arrivalCount h b) ∧
        -- (uniform monotonicity)
        (∀ a b : ProgPoint,
            happensBefore (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)) τn a b →
            happensBefore (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
              ⟨a.thread, a.idx + ((I ^ k).prog a.thread).length⟩
              ⟨b.thread, b.idx + ((I ^ k).prog b.thread).length⟩) ∧
        ∃ τ2, IsSuccessfulTraceFrom (Config.run s ((I ^ k) ^ 2)) τ2 ∧
          -- (front agreement) generations on the first two batches agree with `(I^k)^2`
          (∀ η : ProgPoint, η.idx < 2 * ((I ^ k).prog η.thread).length →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ η
                = pointGen ((I ^ k) ^ 2) τ2 η) ∧
          -- (front monotonicity) happens-before on the first two batches lifts from `(I^k)^2`
          (∀ a b : ProgPoint, a.idx < 2 * ((I ^ k).prog a.thread).length →
              b.idx < 2 * ((I ^ k).prog b.thread).length →
              happensBefore ((I ^ k) ^ 2) τ2 a b →
              happensBefore (((I ^ k) ^ (n + 1)).seq E
                ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ a b) ∧
          -- (generation bounds) front/sync upper + ≥2-batch lower, `∀` barrier; the prefix layer
          -- transports these across the `Pre` glue (each gains `recycleCount b tP (|tP|-2)`).
          (∀ (b : Barrier),
              (∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
                  (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt η
                      = some c → Cmd.barrierRef c = some (b, par) →
                  η.idx < 2 * ((I ^ k).prog η.thread).length →
                  pointGen (((I ^ k) ^ (n + 1)).seq E
                      ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ η
                    ≤ 2 * (k * I.arrivers b / I.arrivalCount h b) + 1) ∧
              (∀ (η : ProgPoint) (par : ℕ+),
                  (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt η
                      = some (Cmd.sync b par) →
                  η.idx < ((I ^ k).prog η.thread).length →
                  pointGen (((I ^ k) ^ (n + 1)).seq E
                      ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ η
                    ≤ k * I.arrivers b / I.arrivalCount h b) ∧
              (b ∈ I.barriers → ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
                  (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt η
                      = some c → Cmd.barrierRef c = some (b, par) →
                  2 * ((I ^ k).prog η.thread).length ≤ η.idx →
                  2 * (k * I.arrivers b / I.arrivalCount h b) + 1
                    ≤ pointGen (((I ^ k) ^ (n + 1)).seq E
                        ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ η)) ∧
          -- (front closed form) front-2-batch barrier generations, independent of the epilogue `E`
          (∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
              j < ((I ^ k).prog t).length → p < 2 → ((I ^ k).prog t)[j]? = some c →
              Cmd.barrierRef c = some (b, par) →
              IsTimeOf (Config.run s (I ^ k)) t₁ ⟨t, j⟩ M₁ →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                  ⟨t, p * ((I ^ k).prog t).length + j⟩
                = recycleCount b t₁ (M₁ - 1) + 1 + p * (k * I.arrivers b / I.arrivalCount h b)) ∧
          -- (first-`n`-batch agreement) generations on the first `n` batches agree between the
          -- `(n+1)`- and `n`-batch replays (both equal the `E`-independent closed form)
          (∀ (t : ThreadId) (e : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
              e < n * ((I ^ k).prog t).length →
              (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).cmdAt ⟨t, e⟩
                = some c → Cmd.barrierRef c = some (b, par) →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                  ⟨t, e⟩
                = pointGen (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)) τn
                    ⟨t, e⟩) ∧
          -- (prefix-region front closed form) any batch `p < n` of `P` has the `E`-independent
          -- generation `rec + 1 + p·δ` (used by the 3-batch front of `loop_prefix`, `n ≥ 3`)
          (∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
              j < ((I ^ k).prog t).length → p < n →
              ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
              IsTimeOf (Config.run s (I ^ k)) t₁ ⟨t, j⟩ M₁ →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                  ⟨t, p * ((I ^ k).prog t).length + j⟩
                = recycleCount b t₁ (M₁ - 1) + 1
                  + p * (k * I.arrivers b / I.arrivalCount h b)) ∧
          -- (epilogue-region front closed form) the *last* batch `p = n` of `P` carries the same
          -- `E`-independent generation `rec + 1 + n·δ` (via `gτepi` + `seq_front_pointGen`); the
          -- `p = n` analog of `hfrontpre`, supplying the 3-batch-front *reference*'s batch 2
          -- (`n_ref = 2`, epilogue region) in `loop_prefix`.
          (∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
              j < ((I ^ k).prog t).length →
              ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
              IsTimeOf (Config.run s (I ^ k)) t₁ ⟨t, j⟩ M₁ →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                  ⟨t, n * ((I ^ k).prog t).length + j⟩
                = recycleCount b t₁ (M₁ - 1) + 1
                  + n * (k * I.arrivers b / I.arrivalCount h b)) ∧
          -- (epilogue bridge) for *any* barrier op of `B = (I^k) ⨾ E` at `⟨t,e⟩`, `P`'s generation
          -- at the last-batch-onward position `n·L+e` is `B`'s generation at `e` plus `n·δ`
          -- (`gτepi`, (n+1)-form).  With `seq_epilogue_pointGen_lower` this gives the E-region
          -- `≥(δ+1)+n·δ` lower bound `loop_prefix`'s 3-batch dispatch needs.
          (∀ (t : ThreadId) (e : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
              ((I ^ k).seq E hids).cmdAt ⟨t, e⟩ = some c → Cmd.barrierRef c = some (b, par) →
              pointGen (((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)) τ
                  ⟨t, n * ((I ^ k).prog t).length + e⟩
                = pointGen ((I ^ k).seq E hids) tE ⟨t, e⟩
                  + n * (k * I.arrivers b / I.arrivalCount h b)) := by
  subst hk
  -- replays of `n`, `n-1`, `2` batches built from the input batch trace `t₁`, anchored at `s`
  obtain ⟨τn0, hτn0, hτn0L, hrecn0⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L (hwf_any (I ^ I.loopK h)) hfull n
  obtain ⟨τnm0, hτnm0, hτnm0L, hrecnm0⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L (hwf_any (I ^ I.loopK h)) hfull (n - 1)
  obtain ⟨τ2, hτ2, hτ2L, hrec2⟩ :=
    pow_replay_recycle_structure h ht₁ ht₁L (hwf_any (I ^ I.loopK h)) hfull 2
  -- the ids equalities for the two gluings
  have hidsE : ((I ^ I.loopK h) ^ n).ids = ((I ^ I.loopK h).seq E hids).ids := by
    simp only [CTA.seq, CTA.pow_ids]
  have hidsEm : ((I ^ I.loopK h) ^ (n - 1)).ids = ((I ^ I.loopK h).seq E hids).ids := by
    simp only [CTA.seq, CTA.pow_ids]
  -- τ : trace of `((I^k)^n) ⨾ ((I^k) ⨾ E) = P`
  obtain ⟨hglueτ, hglueτlast, hsndτ⟩ := glue_trace hidsE hτn0 hτn0L htE
  set τ := τn0.dropLast.map (Config.seqLift ((I ^ I.loopK h) ^ n) ((I ^ I.loopK h).seq E hids))
      ++ tE.tail with hτdef
  have hPeq : ((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE
      = ((I ^ I.loopK h) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids) :=
    (CTA.pow_seq_assoc_last I (I.loopK h) n hids).symm
  have hτ : IsSuccessfulTraceFrom (Config.run s
      (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids))) τ := by
    rw [← hPeq]; exact hglueτ
  -- τn : trace of `((I^k)^(n-1)) ⨾ ((I^k) ⨾ E) = Pn`
  obtain ⟨hglueτn, hglueτnlast, hsndτn⟩ := glue_trace hidsEm hτnm0 hτnm0L htE
  set τn := τnm0.dropLast.map
      (Config.seqLift ((I ^ I.loopK h) ^ (n - 1)) ((I ^ I.loopK h).seq E hids))
      ++ tE.tail with hτndef
  have hPneq : ((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm
      = ((I ^ I.loopK h) ^ n).seq E ((CTA.pow_ids (I ^ I.loopK h) n).trans hids) := by
    apply CTA.ext
    · change ((I ^ I.loopK h) ^ (n - 1)).ids = ((I ^ I.loopK h) ^ n).ids
      simp only [CTA.pow_ids]
    · funext t
      change ((I ^ I.loopK h) ^ (n - 1)).prog t ++ ((I ^ I.loopK h).prog t ++ E.prog t)
        = ((I ^ I.loopK h) ^ n).prog t ++ E.prog t
      rw [← List.append_assoc, ← CTA.pow_one_prog (I ^ I.loopK h) t,
        ← CTA.pow_add_prog (I ^ I.loopK h) (n - 1) 1, show (n - 1) + 1 = n from by omega]
  have hτn : IsSuccessfulTraceFrom (Config.run s
      (((I ^ I.loopK h) ^ n).seq E ((CTA.pow_ids (I ^ I.loopK h) n).trans hids))) τn := by
    rw [← hPneq]; exact hglueτn
  -- generation structure of both glued traces (prefix + epilogue cases)
  obtain ⟨gτpre, gτepi⟩ :=
    glue_replay_gen h ht₁ ht₁L (hwf_any (I ^ I.loopK h)) hfull hids hτn0 hτn0L hrecn0 htE hidsE
  obtain ⟨gτnpre, gτnepi⟩ :=
    glue_replay_gen h ht₁ ht₁L (hwf_any (I ^ I.loopK h)) hfull hids hτnm0 hτnm0L hrecnm0 htE hidsEm
  -- generation of a barrier copy in the pure two-batch replay `τ2` (a `keygen` for `(I^k)^2`)
  have gτ2 : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
      j < ((I ^ I.loopK h).prog t).length → p < 2 →
      ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
      IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
      pointGen ((I ^ I.loopK h) ^ 2) τ2 ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
        = recycleCount b t₁ (M₁ - 1) + 1
          + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j p c b par M₁ hjL hp2 hcj hbr hM₁
    have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
    obtain ⟨sd2, h2last⟩ := hτ2.2
    have hidxlt : p * ((I ^ I.loopK h).prog t).length + j
        < (((I ^ I.loopK h) ^ 2).prog t).length := by
      have hpl : (((I ^ I.loopK h) ^ 2).prog t).length = 2 * ((I ^ I.loopK h).prog t).length :=
        CTA.pow_prog_length (I ^ I.loopK h) 2 t
      rw [hpl]
      calc p * ((I ^ I.loopK h).prog t).length + j
          < p * ((I ^ I.loopK h).prog t).length + ((I ^ I.loopK h).prog t).length := by omega
        _ = (p + 1) * ((I ^ I.loopK h).prog t).length := by rw [Nat.succ_mul]
        _ ≤ 2 * ((I ^ I.loopK h).prog t).length := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨M, hM⟩ := exists_time_of_ends_done hτ2.1 h2last
      (η := ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩) hidxlt
    have hcmdcopy : ((I ^ I.loopK h) ^ 2).cmdAt ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
        = some c := by rw [CTA.cmdAt_pow_batch_copy (I ^ I.loopK h) hjL hp2]; exact hcj
    have hg : pointGen ((I ^ I.loopK h) ^ 2) τ2 ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
        = recycleCount b τ2 (M - 1) + 1 := by
      simp only [pointGen, hcmdcopy, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM]
    rw [hg, hrec2 t j c b par p M M₁ hp2 hcj hbr hM hM₁]
    omega
  -- **(prefix-region front closed form)**: for *any* batch `p < n`, `P`'s generation is the
  -- `E`-independent `rec + 1 + p·δ` (via `gτpre`).  `loop_prefix` (with `n ≥ 3`) uses this for its
  -- 3-batch front, where every front batch `p < 3 ≤ n` is prefix-region — no epilogue case.
  have hfrontpre : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
      j < ((I ^ I.loopK h).prog t).length → p < n →
      ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
      IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
          ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
        = recycleCount b t₁ (M₁ - 1) + 1
          + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j p c b par M₁ hjL hpn hcj hbr hM₁
    have hgp := gτpre t j p c b par M₁ hjL hpn hcj hbr hM₁
    rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
        ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
      = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
          ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩ from by rw [hPeq]]
    rw [hgp]
  -- **(epilogue-region front closed form)**: the *last* batch `p = n` (the `B = (I^k) ⨾ E` region)
  -- carries the same `rec + 1 + n·δ` for a barrier in `B`'s `(I^k)`-phase (`j < L`), via `gτepi`
  -- (epilogue generation) composed with `seq_front_pointGen` (front of the structured `tE`).  This
  -- is the `p = n` analog of `hfrontpre`; it supplies the reference batch-2 in `loop_prefix`.
  have hfrontepi : ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
      j < ((I ^ I.loopK h).prog t).length →
      ((I ^ I.loopK h).prog t)[j]? = some c → Cmd.barrierRef c = some (b, par) →
      IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
          ⟨t, n * ((I ^ I.loopK h).prog t).length + j⟩
        = recycleCount b t₁ (M₁ - 1) + 1
          + n * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j c b par M₁ hjL hcj hbr hM₁
    -- the barrier op lives in `B`'s `(I^k)`-phase (`j < L`)
    have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, j⟩ = some c := by
      change ((I ^ I.loopK h).prog t ++ E.prog t)[j]? = some c
      rw [List.getElem?_append_left hjL]; exact hcj
    have hgp := gτepi t j c b par hcE hbr
    rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
        ⟨t, n * ((I ^ I.loopK h).prog t).length + j⟩
      = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
          ⟨t, n * ((I ^ I.loopK h).prog t).length + j⟩ from by rw [hPeq]]
    rw [hgp, seq_front_pointGen h ht₁ ht₁L hids htE htEpre hjL hcj hbr hM₁]
  -- **(epilogue bridge)**: `gτepi` in (n+1)-form — `P`'s generation at `n·L+e` equals `B`'s
  -- generation at `e` plus `n·δ`, for any barrier op of `B`.  Used by `loop_prefix`'s E-region
  -- lower bound (combine with `seq_epilogue_pointGen_lower`).
  have hepiBridge : ∀ (t : ThreadId) (e : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
      ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c → Cmd.barrierRef c = some (b, par) →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
          ⟨t, n * ((I ^ I.loopK h).prog t).length + e⟩
        = pointGen ((I ^ I.loopK h).seq E hids) tE ⟨t, e⟩
          + n * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t e c b par hcE hbr
    have hgp := gτepi t e c b par hcE hbr
    rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
        ⟨t, n * ((I ^ I.loopK h).prog t).length + e⟩
      = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
          ⟨t, n * ((I ^ I.loopK h).prog t).length + e⟩ from by rw [hPeq]]
    rw [hgp]
  -- **(uniform shift), factored out** so both the shift clause and the monotonicity clause can
  -- consume it: every `Pn`-barrier's generation bumps by `δ` under the `+L` embedding.
  have hshift : ∀ (η : ProgPoint) (c : Cmd) (b : Barrier) (par : ℕ+),
      (((I ^ I.loopK h) ^ n).seq E ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)).cmdAt η = some c →
      Cmd.barrierRef c = some (b, par) →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ
          ⟨η.thread, η.idx + ((I ^ I.loopK h).prog η.thread).length⟩
        = pointGen (((I ^ I.loopK h) ^ n).seq E ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn η
          + I.loopK h * I.arrivers b / I.arrivalCount h b := by
    intro η c b par hcmdη hbr
    obtain ⟨t, idx⟩ := η
    dsimp only at hcmdη ⊢
    -- view `Pn` in glue form `((I^k)^(n-1)) ⨾ B`; split `idx` at `(n-1)·L`
    have hcmdη' : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).cmdAt
        ⟨t, idx⟩ = some c := by rw [hPneq]; exact hcmdη
    set L := ((I ^ I.loopK h).prog t).length with hLeq
    have hmLenm : (((I ^ I.loopK h) ^ (n - 1)).prog t).length = (n - 1) * L :=
      CTA.pow_prog_length _ (n - 1) t
    have hPnprog : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).prog t
        = ((I ^ I.loopK h) ^ (n - 1)).prog t ++ ((I ^ I.loopK h).seq E hids).prog t := rfl
    by_cases hsplit : idx < (n - 1) * L
    · -- prefix sub-case: `idx = p·L + j`, shifted to batch `p+1`
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos'
      · rw [hL0] at hsplit; omega
      set p := idx / L with hpdef
      set j := idx % L with hjdef
      have hjL : j < L := Nat.mod_lt _ hLpos'
      have hidxeq : idx = p * L + j := by
        rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
      have hpn1 : p < n - 1 := by
        have : p * L < (n - 1) * L := by
          have : p * L ≤ idx := by rw [hidxeq]; omega
          omega
        exact Nat.lt_of_mul_lt_mul_right this
      -- the body command `(I^k).prog t [j]? = some c`
      have hcj : ((I ^ I.loopK h).prog t)[j]? = some c := by
        have hcmd2 : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).cmdAt
            ⟨t, p * L + j⟩ = some c := by rw [← hidxeq]; exact hcmdη'
        have hsplitcmd : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).cmdAt
            ⟨t, p * L + j⟩ = ((I ^ I.loopK h) ^ (n - 1)).cmdAt ⟨t, p * L + j⟩ := by
          change (((I ^ I.loopK h) ^ (n - 1)).prog t
              ++ ((I ^ I.loopK h).seq E hids).prog t)[p * L + j]?
            = (((I ^ I.loopK h) ^ (n - 1)).prog t)[p * L + j]?
          rw [List.getElem?_append_left (by rw [hmLenm]; omega)]
        rw [hsplitcmd, CTA.cmdAt_pow_batch_copy (I ^ I.loopK h) hjL hpn1] at hcmd2
        exact hcmd2
      -- transport `⟨t,j⟩`'s `t₁`-time
      obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) hjL
      -- τn generation of `η` (batch `p`); τ generation of shifted `η` (batch `p+1`)
      have hgn := gτnpre t j p c b par M₁ hjL hpn1 hcj hbr hM₁
      have hgp := gτpre t j (p + 1) c b par M₁ hjL (by omega) hcj hbr hM₁
      -- rewrite both index points into glue form
      have hidxL : idx + L = (p + 1) * L + j := by rw [Nat.succ_mul, hidxeq]; omega
      rw [show (⟨t, idx + L⟩ : ProgPoint) = ⟨t, (p + 1) * L + j⟩ from by rw [hidxL]]
      rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, p * L + j⟩ from by rw [hidxeq]]
      -- rewrite `P`/`Pn` to the glue program
      rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ ⟨t, (p + 1) * L + j⟩
        = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
            ⟨t, (p + 1) * L + j⟩ from by rw [hPeq]]
      rw [show pointGen (((I ^ I.loopK h) ^ n).seq E
          ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn ⟨t, p * L + j⟩
        = pointGen (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm) τn
            ⟨t, p * L + j⟩ from by rw [hPneq]]
      rw [hgp, hgn]
      have hexp : (p + 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          = p * (I.loopK h * I.arrivers b / I.arrivalCount h b)
            + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by rw [Nat.succ_mul]
      omega
    · -- epilogue sub-case: `idx = (n-1)·L + e`, shifted to `n·L + e`
      rw [Nat.not_lt] at hsplit
      set e := idx - (n - 1) * L with hedef
      have hidxeq : idx = (n - 1) * L + e := by omega
      -- the command in `B` at `⟨t, e⟩`
      have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c := by
        have hcmd2 : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).cmdAt
            ⟨t, (n - 1) * L + e⟩ = some c := by rw [← hidxeq]; exact hcmdη'
        have hsplitcmd : (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm).cmdAt
            ⟨t, (n - 1) * L + e⟩ = ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ := by
          change (((I ^ I.loopK h) ^ (n - 1)).prog t
              ++ ((I ^ I.loopK h).seq E hids).prog t)[(n - 1) * L + e]?
            = (((I ^ I.loopK h).seq E hids).prog t)[e]?
          rw [List.getElem?_append_right (by rw [hmLenm]; omega), hmLenm,
            show (n - 1) * L + e - (n - 1) * L = e from by omega]
        rw [hsplitcmd] at hcmd2
        exact hcmd2
      have hgn := gτnepi t e c b par hcE hbr
      have hgp := gτepi t e c b par hcE hbr
      have hidxL : idx + L = n * L + e := by
        have hnL : (n - 1) * L + L = n * L := by
          conv_rhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
        rw [hidxeq]; omega
      rw [show (⟨t, idx + L⟩ : ProgPoint) = ⟨t, n * L + e⟩ from by rw [hidxL]]
      rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, (n - 1) * L + e⟩ from by rw [hidxeq]]
      rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ ⟨t, n * L + e⟩
        = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
            ⟨t, n * L + e⟩ from by rw [hPeq]]
      rw [show pointGen (((I ^ I.loopK h) ^ n).seq E
          ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn ⟨t, (n - 1) * L + e⟩
        = pointGen (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm) τn
            ⟨t, (n - 1) * L + e⟩ from by rw [hPneq]]
      rw [hgp, hgn]
      have hnexp : n * (I.loopK h * I.arrivers b / I.arrivalCount h b)
          = (n - 1) * (I.loopK h * I.arrivers b / I.arrivalCount h b)
            + (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega, Nat.succ_mul]
      omega
  -- **(front agreement), factored out** so the front-monotonicity clause can reuse it: on the
  -- first two batches (`idx < 2L`, a literal front prefix of `P`) `τ`'s generations agree with the
  -- pure two-batch replay `τ2`.  Both are computed from the same restoring batch `t₁`.
  have hfrontgen : ∀ η : ProgPoint,
      η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ η
        = pointGen ((I ^ I.loopK h) ^ 2) τ2 η := by
    intro η hη
    obtain ⟨t, idx⟩ := η
    dsimp only at hη ⊢
    set L := ((I ^ I.loopK h).prog t).length with hLeq
    -- front command transfer: `P.cmdAt = ((I^k)^2).cmdAt` on `idx < 2L`
    have hP2prog : (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).prog t
          = ((I ^ I.loopK h) ^ 2).prog t
            ++ (((I ^ I.loopK h) ^ (n - 1)).prog t ++ E.prog t) := by
      change ((I ^ I.loopK h) ^ (n + 1)).prog t ++ E.prog t = _
      rw [show n + 1 = 2 + (n - 1) from by omega, CTA.pow_add_prog, List.append_assoc]
    have hcmdfront : (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt ⟨t, idx⟩
          = ((I ^ I.loopK h) ^ 2).cmdAt ⟨t, idx⟩ := by
      simp only [CTA.cmdAt]
      rw [hP2prog, List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact hη)]
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · rw [hL0] at hη; omega
    -- decompose `idx = p·L + j`, `p ∈ {0, 1}`
    set p := idx / L with hpdef
    set j := idx % L with hjdef
    have hjL : j < L := Nat.mod_lt _ hLpos
    have hidxeq : idx = p * L + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
    have hp2 : p < 2 := by
      have : p * L < 2 * L := by
        have : p * L ≤ idx := by rw [hidxeq]; omega
        omega
      exact Nat.lt_of_mul_lt_mul_right this
    -- case on whether the front command is a barrier op
    cases hc : ((I ^ I.loopK h) ^ 2).cmdAt ⟨t, idx⟩ with
    | none =>
      -- no command: both generations are `0`
      simp only [pointGen, hcmdfront, hc, Option.bind_none]
    | some cc =>
      cases hcbar : Cmd.barrierRef cc with
      | none =>
        -- a `read`/`write`: `barrier? = none`, both generations `0`
        have hbar0 : Cmd.barrier? cc = none := by
          cases cc with
          | read g => rfl
          | write g => rfl
          | arrive b m => simp [Cmd.barrierRef] at hcbar
          | sync b m => simp [Cmd.barrierRef] at hcbar
        simp only [pointGen, hcmdfront, hc, Option.bind_some, hbar0]
      | some bpar =>
        obtain ⟨b, par⟩ := bpar
        -- the body command `(I^k).prog t [j]? = some cc`
        have hcj : ((I ^ I.loopK h).prog t)[j]? = some cc := by
          have hcopy : ((I ^ I.loopK h) ^ 2).cmdAt ⟨t, p * L + j⟩
              = ((I ^ I.loopK h).prog t)[j]? :=
            CTA.cmdAt_pow_batch_copy (I ^ I.loopK h) hjL hp2
          rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, p * L + j⟩ from by rw [hidxeq]] at hc
          rw [hcopy] at hc; exact hc
        -- `⟨t, j⟩`'s time in `t₁`
        obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) hjL
        have hg2 := gτ2 t j p cc b par M₁ hjL hp2 hcj hcbar hM₁
        rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, p * L + j⟩ from by rw [hidxeq]]
        rw [hg2]
        by_cases hpn : p < n
        · -- prefix region of `P`: `gτpre` gives the identical closed form
          have hgp := gτpre t j p cc b par M₁ hjL hpn hcj hcbar hM₁
          rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ ⟨t, p * L + j⟩
            = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                ⟨t, p * L + j⟩ from by rw [hPeq]]
          rw [hgp]
        · -- `n = 1`, `p = 1`: the front-prefix's *second* batch executes inside the structured
          -- `B`-trace `tE`, at `B`-position `e = j` (still in `tE`'s `(I^k)`-phase).  `gτepi`
          -- (`n = 1`) reduces the goal to `pointGen B tE ⟨t, j⟩`, which `seq_front_pointGen`
          -- (using `htEpre`, the lifted-`t₁` front of `tE`) evaluates to
          -- `recycleCount b t₁ (M₁-1) + 1`.
          have hn1 : n = 1 := by omega
          have hp1 : p = 1 := by omega
          subst hn1
          rw [hp1]
          -- the front-batch command lives in `B`'s `(I^k)`-phase
          have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, j⟩ = some cc := by
            change ((I ^ I.loopK h).prog t ++ E.prog t)[j]? = some cc
            rw [List.getElem?_append_left hjL]; exact hcj
          -- `gτepi` for `e = j` gives `pointGen B tE ⟨t,j⟩ + 1·δ`
          have hgp := gτepi t j cc b par hcE hcbar
          rw [show (1 : ℕ) * L + j = 1 * List.length ((I ^ I.loopK h).prog t) + j from rfl]
          rw [show pointGen (((I ^ I.loopK h) ^ (1 + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (1 + 1)).trans hids)) τ
              ⟨t, 1 * List.length ((I ^ I.loopK h).prog t) + j⟩
            = pointGen (((I ^ I.loopK h) ^ 1).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                ⟨t, 1 * List.length ((I ^ I.loopK h).prog t) + j⟩ from by rw [hPeq]]
          rw [hgp, seq_front_pointGen h ht₁ ht₁L hids htE htEpre hjL hcj hcbar hM₁]
  -- **(generation bounds), factored out** `∀ b` so the prefix layer can transport them across the
  -- `Pre` glue.  Self-contained copy of the co-location's front/sync/lower bounds.
  have hgenbounds : ∀ (b : Barrier),
      (∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
          (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt η = some c →
          Cmd.barrierRef c = some (b, par) →
          η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length →
          pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ η
            ≤ 2 * (I.loopK h * I.arrivers b / I.arrivalCount h b) + 1) ∧
      (∀ (η : ProgPoint) (par : ℕ+),
          (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt η = some (Cmd.sync b par) →
          η.idx < ((I ^ I.loopK h).prog η.thread).length →
          pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ η
            ≤ I.loopK h * I.arrivers b / I.arrivalCount h b) ∧
      (b ∈ I.barriers → ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
          (((I ^ I.loopK h) ^ (n + 1)).seq E
              ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt η = some c →
          Cmd.barrierRef c = some (b, par) →
          2 * ((I ^ I.loopK h).prog η.thread).length ≤ η.idx →
          2 * (I.loopK h * I.arrivers b / I.arrivalCount h b) + 1
            ≤ pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
                ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ η) := by
    intro b
    set P := ((I ^ I.loopK h) ^ (n + 1)).seq E
      ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids) with hPdef
    set δ := I.loopK h * I.arrivers b / I.arrivalCount h b with hδdef
    have hbAofI : b ∈ I.barriers → b ∈ (I ^ I.loopK h).barrierSet := by
      intro hbI
      rw [CTA.barriers, Finset.mem_biUnion] at hbI
      obtain ⟨i, hi, hbi⟩ := hbI
      rw [List.mem_toFinset, List.mem_map] at hbi
      obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
      simp only at hb'; subst hb'
      rw [List.mem_filterMap] at hr
      obtain ⟨c, hc, hcr⟩ := hr
      have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
      have hcA : c ∈ (I ^ I.loopK h).prog i := by
        rw [show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
          List.mem_append]
        exact Or.inl hc
      rw [CTA.barrierSet, Finset.mem_biUnion]
      refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
      rw [CTA.pow_ids]; exact hi
    have hPprog : ∀ t, P.prog t = ((I ^ I.loopK h) ^ (n + 1)).prog t ++ E.prog t := fun t => rfl
    have hPplen : ∀ t, (((I ^ I.loopK h) ^ (n + 1)).prog t).length
        = (n + 1) * ((I ^ I.loopK h).prog t).length := fun t => CTA.pow_prog_length _ (n + 1) t
    have hcmdfront : ∀ (x : ProgPoint), x.idx < (n + 1) * ((I ^ I.loopK h).prog x.thread).length →
        ((I ^ I.loopK h) ^ (n + 1)).cmdAt x = P.cmdAt x := by
      intro x hx
      simp only [CTA.cmdAt]
      rw [hPprog x.thread, List.getElem?_append_left (by rw [hPplen]; exact hx)]
    have hcmdE : ∀ (x : ProgPoint), (n + 1) * ((I ^ I.loopK h).prog x.thread).length ≤ x.idx →
        ((I ^ I.loopK h).seq E hids).cmdAt
            ⟨x.thread, x.idx - n * ((I ^ I.loopK h).prog x.thread).length⟩ = P.cmdAt x := by
      intro x hx
      simp only [CTA.cmdAt]
      have hBprog : ((I ^ I.loopK h).seq E hids).prog x.thread
          = (I ^ I.loopK h).prog x.thread ++ E.prog x.thread := rfl
      rw [hBprog, hPprog x.thread]
      set L := ((I ^ I.loopK h).prog x.thread).length with hLx
      have hexp : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
      rw [List.getElem?_append_right (by omega),
        List.getElem?_append_right (by rw [hPplen]; omega), hPplen]
      congr 1
      rw [← hLx]; omega
    have bodyCmd : ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length →
        ((I ^ I.loopK h).prog η.thread)[η.idx % ((I ^ I.loopK h).prog η.thread).length]? = some c
          ∧ η.idx % ((I ^ I.loopK h).prog η.thread).length
              < ((I ^ I.loopK h).prog η.thread).length := by
      intro η c par hcmd hbr hlt
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hLpos : 0 < L := by
        rcases Nat.eq_zero_or_pos L with h0 | hp
        · rw [h0, Nat.mul_zero] at hlt; omega
        · exact hp
      have hjL : idx % L < L := Nat.mod_lt _ hLpos
      have hp : idx / L < n + 1 := by
        rw [Nat.div_lt_iff_lt_mul hLpos]; exact hlt
      have hidxeq : idx = (idx / L) * L + idx % L := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
      have hcopy : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, (idx / L) * L + idx % L⟩
          = ((I ^ I.loopK h).prog t)[idx % L]? := CTA.cmdAt_pow_batch_copy _ hjL hp
      rw [← hidxeq, hcmdfront ⟨t, idx⟩ hlt, hcmd] at hcopy
      exact ⟨hcopy.symm, hjL⟩
    have hUpperLE : ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length →
        pointGen P τ η ≤ 2 * δ + 1 := by
      intro η c par hcmd hbr hlt2
      have hltn1 : η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length := by
        have : 2 * ((I ^ I.loopK h).prog η.thread).length
            ≤ (n + 1) * ((I ^ I.loopK h).prog η.thread).length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨hbody, hjL⟩ := bodyCmd η c par hcmd hbr hltn1
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt2 hjL hbody ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hLpos : 0 < L := by omega
      have hp2 : idx / L < 2 := by rw [Nat.div_lt_iff_lt_mul hLpos]; omega
      have hidxeq : idx = (idx / L) * L + idx % L := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
      obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
      rw [hfrontgen ⟨t, idx⟩ hlt2,
        show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by rw [← hidxeq]]
      rw [gτ2 t (idx % L) (idx / L) c b par M₁ hjL hp2 hbody hbr hM₁, ← hδdef]
      have hrec := barrierOp_recycleCount_le_batch h ht₁ ht₁L hbody hbr hM₁
        (hwf_any (I ^ I.loopK h)) hfull
      rw [← hδdef] at hrec
      have hple : idx / L ≤ 1 := by omega
      have hmul : (idx / L) * δ ≤ 1 * δ := Nat.mul_le_mul_right δ hple
      omega
    have hSync0 : ∀ (η : ProgPoint) (par : ℕ+),
        P.cmdAt η = some (Cmd.sync b par) →
        η.idx < ((I ^ I.loopK h).prog η.thread).length →
        pointGen P τ η ≤ δ := by
      intro η par hcmd hlt0
      have hlt2 : η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length := by omega
      have hltn1 : η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length := by
        have : 1 * ((I ^ I.loopK h).prog η.thread).length
            ≤ (n + 1) * ((I ^ I.loopK h).prog η.thread).length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨hbody, hjL⟩ := bodyCmd η (Cmd.sync b par) par hcmd rfl hltn1
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt0 hlt2 hjL hbody ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hmod : idx % L = idx := Nat.mod_eq_of_lt hlt0
      have hdiv : idx / L = 0 := Nat.div_eq_of_lt hlt0
      obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
      rw [hfrontgen ⟨t, idx⟩ hlt2,
        show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by
          rw [hdiv, hmod, Nat.zero_mul, Nat.zero_add]]
      rw [gτ2 t (idx % L) (idx / L) (Cmd.sync b par) b par M₁ hjL (by rw [hdiv]; omega)
        hbody rfl hM₁, ← hδdef, hdiv, Nat.zero_mul, Nat.add_zero]
      have hsync := sync_recycleCount_lt_batch h ht₁ ht₁L hbody hM₁
        (hwf_any (I ^ I.loopK h)) hfull
      rw [← hδdef] at hsync
      omega
    have hLowerGE2 : b ∈ I.barriers → ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        2 * ((I ^ I.loopK h).prog η.thread).length ≤ η.idx →
        2 * δ + 1 ≤ pointGen P τ η := by
      intro hbI η c par hcmd hbr hge2
      have hbA : b ∈ (I ^ I.loopK h).barrierSet := hbAofI hbI
      have hδ1 : 1 ≤ δ := one_le_delta h rfl hbI
      obtain ⟨t, idx⟩ := η
      dsimp only at hge2 ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      by_cases hpre : idx < n * L
      · have hLpos : 0 < L := by
          rcases Nat.eq_zero_or_pos L with h0 | hp
          · rw [h0, Nat.mul_zero] at hpre; omega
          · exact hp
        have hpltn1 : idx < (n + 1) * L := by
          have h1 : n * L ≤ (n + 1) * L := Nat.mul_le_mul_right L (by omega)
          omega
        obtain ⟨hbody, hjL⟩ := bodyCmd ⟨t, idx⟩ c par hcmd hbr (by
          dsimp only; rw [← hLdef]; exact hpltn1)
        dsimp only at hbody hjL
        have hp : idx / L < n := by
          rw [Nat.div_lt_iff_lt_mul hLpos]; exact hpre
        have hpge : 2 ≤ idx / L := by
          rw [Nat.le_div_iff_mul_le hLpos]; omega
        have hidxeq : idx = (idx / L) * L + idx % L := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
        obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
        rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by rw [← hidxeq]]
        rw [show pointGen P τ ⟨t, (idx / L) * L + idx % L⟩
            = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                ⟨t, (idx / L) * L + idx % L⟩ from by rw [hPeq]]
        rw [gτpre t (idx % L) (idx / L) c b par M₁ hjL hp hbody hbr hM₁, ← hδdef]
        have hmul : 2 * δ ≤ (idx / L) * δ := Nat.mul_le_mul_right δ hpge
        omega
      · rw [Nat.not_lt] at hpre
        set e := idx - n * L with hedef
        have hidxeq : idx = n * L + e := by omega
        by_cases heL : L ≤ e
        · have hge : (n + 1) * L ≤ idx := by
            have h1 : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
            omega
          have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c := by
            have hmap := hcmdE ⟨t, idx⟩ (by dsimp only; rw [← hLdef]; exact hge)
            dsimp only at hmap
            rw [show idx - n * ((I ^ I.loopK h).prog t).length = e from by rw [← hLdef]] at hmap
            rw [hmap]; exact hcmd
          rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, n * L + e⟩ from by rw [← hidxeq]]
          rw [show pointGen P τ ⟨t, n * L + e⟩
              = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                  ⟨t, n * L + e⟩ from by rw [hPeq]]
          rw [gτepi t e c b par hcE hbr, ← hδdef]
          have hlow := seq_epilogue_pointGen_lower h ht₁ ht₁L hids htE htEpre heL hcE hbr hbA
            (hwf_any (I ^ I.loopK h)) hfull
          rw [← hδdef] at hlow
          have hnmul : 1 * δ ≤ n * δ := Nat.mul_le_mul_right δ hn
          omega
        · rw [Nat.not_le] at heL
          have hltn1 : idx < (n + 1) * ((I ^ I.loopK h).prog t).length := by
            rw [← hLdef]; have h1 : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
            omega
          have hbody : ((I ^ I.loopK h).prog t)[e]? = some c := by
            have hcopy : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, n * L + e⟩
                = ((I ^ I.loopK h).prog t)[e]? := CTA.cmdAt_pow_batch_copy _ heL (by omega)
            rw [hcmdfront ⟨t, n * L + e⟩ (by dsimp only; rw [← hLdef, ← hidxeq]; exact hltn1),
              show (⟨t, n * L + e⟩ : ProgPoint) = ⟨t, idx⟩ from by rw [← hidxeq], hcmd] at hcopy
            exact hcopy.symm
          have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c := by
            change ((I ^ I.loopK h).prog t ++ E.prog t)[e]? = some c
            rw [List.getElem?_append_left heL]; exact hbody
          rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, n * L + e⟩ from by rw [← hidxeq]]
          rw [show pointGen P τ ⟨t, n * L + e⟩
              = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                  ⟨t, n * L + e⟩ from by rw [hPeq]]
          rw [gτepi t e c b par hcE hbr, ← hδdef]
          obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, e⟩) heL
          rw [seq_front_pointGen h ht₁ ht₁L hids htE htEpre heL hbody hbr hM₁]
          have hnge2 : 2 ≤ n := by
            by_contra hcon
            have hn1 : n = 1 := by omega
            rw [hn1, Nat.one_mul] at hpre
            have heidx : e = idx - L := by rw [hedef, hn1, Nat.one_mul]
            omega
          have hnmul : 2 * δ ≤ n * δ := Nat.mul_le_mul_right δ hnge2
          omega
    exact ⟨hUpperLE, hSync0, hLowerGE2⟩
  -- **(front closed form)** the front-2-batch generation, `recycleCount b t₁ (M₁-1)+1 + p·δ`,
  -- independent of `E` — `hfrontgen` reduces to `(I^k)^2`, then `gτ2`.
  have hfrontclosed : ∀ (t : ThreadId) (j p : Nat) (c : Cmd) (b : Barrier) (par : ℕ+) (M₁ : Nat),
      j < ((I ^ I.loopK h).prog t).length → p < 2 → ((I ^ I.loopK h).prog t)[j]? = some c →
      Cmd.barrierRef c = some (b, par) →
      IsTimeOf (Config.run s (I ^ I.loopK h)) t₁ ⟨t, j⟩ M₁ →
      pointGen
        (((I ^ I.loopK h) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids))
          τ ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩
        = recycleCount b t₁ (M₁ - 1) + 1 + p * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
    intro t j p c b par M₁ hjL hp2 hcj hbr hM₁
    have hlt2 : p * ((I ^ I.loopK h).prog t).length + j
        < 2 * ((I ^ I.loopK h).prog t).length := by
      calc p * ((I ^ I.loopK h).prog t).length + j
          < p * ((I ^ I.loopK h).prog t).length + ((I ^ I.loopK h).prog t).length := by omega
        _ = (p + 1) * ((I ^ I.loopK h).prog t).length := by rw [Nat.succ_mul]
        _ ≤ 2 * ((I ^ I.loopK h).prog t).length := Nat.mul_le_mul_right _ (by omega)
    rw [hfrontgen ⟨t, p * ((I ^ I.loopK h).prog t).length + j⟩ hlt2]
    exact gτ2 t j p c b par M₁ hjL hp2 hcj hbr hM₁
  -- **(first-`n`-batch agreement)** the first `n` batches of the `(n+1)`-batch replay `τ` and the
  -- `n`-batch replay `τn` carry the same barrier generations (both equal `gτpre`/`gτnpre`'s closed
  -- form; the last batch `p = n-1` of `τn` uses `gτnepi` + `seq_front_pointGen`).
  have hfirstNagree : ∀ (t : ThreadId) (e : Nat) (c : Cmd) (b : Barrier) (par : ℕ+),
      e < n * ((I ^ I.loopK h).prog t).length →
      (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt ⟨t, e⟩ = some c →
      Cmd.barrierRef c = some (b, par) →
      pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ ⟨t, e⟩
        = pointGen (((I ^ I.loopK h) ^ n).seq E
            ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn ⟨t, e⟩ := by
    intro t e c b par he hcmd hbr
    set L := ((I ^ I.loopK h).prog t).length with hLeq
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · rw [hL0, Nat.mul_zero] at he; omega
    set p := e / L with hpdef
    set j := e % L with hjdef
    have hjL : j < L := Nat.mod_lt _ hLpos
    have hpn : p < n := by rw [hpdef, Nat.div_lt_iff_lt_mul hLpos]; omega
    have hidxeq : e = p * L + j := by
      rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod e L).symm
    have hcj : ((I ^ I.loopK h).prog t)[j]? = some c := by
      have hcopy : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, p * L + j⟩
          = ((I ^ I.loopK h).prog t)[j]? :=
        CTA.cmdAt_pow_batch_copy (I ^ I.loopK h) hjL (Nat.lt_succ_of_lt hpn)
      have hc : (((I ^ I.loopK h) ^ (n + 1)).seq E
          ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)).cmdAt ⟨t, e⟩ = some c := hcmd
      rw [show (⟨t, e⟩ : ProgPoint) = ⟨t, p * L + j⟩ from by rw [hidxeq]] at hc
      have hc2 : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, p * L + j⟩ = some c := by
        have hx : (((I ^ I.loopK h) ^ (n + 1)).prog t ++ E.prog t)[p * L + j]? = some c := hc
        rwa [List.getElem?_append_left (by
          rw [CTA.pow_prog_length]
          calc p * L + j < (p + 1) * L := by rw [Nat.succ_mul]; omega
            _ ≤ (n + 1) * L := Nat.mul_le_mul_right _ (by omega))] at hx
      rw [hcopy] at hc2; exact hc2
    obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, j⟩) hjL
    rw [show (⟨t, e⟩ : ProgPoint) = ⟨t, p * L + j⟩ from by rw [hidxeq]]
    have hgp := gτpre t j p c b par M₁ hjL hpn hcj hbr hM₁
    rw [show pointGen (((I ^ I.loopK h) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids)) τ ⟨t, p * L + j⟩
      = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
          ⟨t, p * L + j⟩ from by rw [hPeq]]
    rw [hgp]
    rcases Nat.lt_or_ge p (n - 1) with hp | hp
    · have hgnp := gτnpre t j p c b par M₁ hjL hp hcj hbr hM₁
      rw [show pointGen (((I ^ I.loopK h) ^ n).seq E
          ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn ⟨t, p * L + j⟩
        = pointGen (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm) τn
            ⟨t, p * L + j⟩ from by rw [hPneq]]
      rw [hgnp]
    · have hpe : p = n - 1 := by omega
      have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, j⟩ = some c := by
        change ((I ^ I.loopK h).prog t ++ E.prog t)[j]? = some c
        rw [List.getElem?_append_left hjL]; exact hcj
      have hgne := gτnepi t j c b par hcE hbr
      rw [seq_front_pointGen h ht₁ ht₁L hids htE htEpre hjL hcj hbr hM₁] at hgne
      rw [show pointGen (((I ^ I.loopK h) ^ n).seq E
          ((CTA.pow_ids (I ^ I.loopK h) n).trans hids)) τn ⟨t, p * L + j⟩
        = pointGen (((I ^ I.loopK h) ^ (n - 1)).seq ((I ^ I.loopK h).seq E hids) hidsEm) τn
            ⟨t, (n - 1) * L + j⟩ from by rw [hPneq, hpe]]
      rw [hgne, hpe]
  refine ⟨τ, hτ, ?_, τn, hτn, hshift, ?_, τ2, hτ2, hfrontgen, ?_, hgenbounds, hfrontclosed,
    hfirstNagree, hfrontpre, hfrontepi, hepiBridge⟩
  · -- (co-location): place the flagged pair `(c1, c2)` by batch, via generation bounds.  Write
    -- `δ = k·arrivers(b)/count(b) ≥ 1`.  Three bounds (front upper, batch-0 sync upper, ≥2-batch
    -- lower) split the pair: `c2` in the first two batches forces `c1` there too (front disjunct);
    -- otherwise `c2`'s generation `≥ 2δ+1` forces `c1` past the front batch (shiftable disjunct).
    intro c1 c2 b nn hsync1 hbar2 hgen hidx
    set P := ((I ^ I.loopK h) ^ (n + 1)).seq E
      ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids) with hPdef
    set L1 := ((I ^ I.loopK h).prog c1.thread).length with hL1
    set L2 := ((I ^ I.loopK h).prog c2.thread).length with hL2
    -- `c2`'s command is a barrier op on `b`
    obtain ⟨cc2', par2, hc2cmd, hc2ref⟩ : ∃ (cc2x : Cmd) (par2 : ℕ+),
        P.cmdAt c2 = some cc2x ∧ Cmd.barrierRef cc2x = some (b, par2) := by
      cases hcmd2 : P.cmdAt c2 with
      | none => rw [hcmd2] at hbar2; simp at hbar2
      | some cc2 =>
        cases cc2 with
        | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | arrive bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
    set δ := I.loopK h * I.arrivers b / I.arrivalCount h b with hδdef
    -- `b ∈ I.barriers ⟹ b ∈ (I^k).barrierSet`
    have hbAofI : b ∈ I.barriers → b ∈ (I ^ I.loopK h).barrierSet := by
      intro hbI
      rw [CTA.barriers, Finset.mem_biUnion] at hbI
      obtain ⟨i, hi, hbi⟩ := hbI
      rw [List.mem_toFinset, List.mem_map] at hbi
      obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
      simp only at hb'; subst hb'
      rw [List.mem_filterMap] at hr
      obtain ⟨c, hc, hcr⟩ := hr
      have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
      have hcA : c ∈ (I ^ I.loopK h).prog i := by
        rw [show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
          List.mem_append]
        exact Or.inl hc
      rw [CTA.barrierSet, Finset.mem_biUnion]
      refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
        ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
      rw [CTA.pow_ids]; exact hi
    -- positive front-batch lengths (else the index ranges are vacuous)
    have hc1lt : c1.idx < (P.prog c1.thread).length :=
      ((mem_progPoints_iff _ c1).mp (mem_progPoints_of_cmdAt _ hsync1)).2
    have hc2lt : c2.idx < (P.prog c2.thread).length :=
      ((mem_progPoints_iff _ c2).mp (mem_progPoints_of_cmdAt _ hc2cmd)).2
    -- `P.prog t = ((I^k)^(n+1)).prog t ++ E.prog t`; its `(I^k)`-part has length `(n+1)·L`
    have hPprog : ∀ t, P.prog t = ((I ^ I.loopK h) ^ (n + 1)).prog t ++ E.prog t := fun t => rfl
    have hPplen : ∀ t, (((I ^ I.loopK h) ^ (n + 1)).prog t).length
        = (n + 1) * ((I ^ I.loopK h).prog t).length := fun t => CTA.pow_prog_length _ (n + 1) t
    rw [hPprog c1.thread, List.length_append, hPplen c1.thread, ← hL1] at hc1lt
    rw [hPprog c2.thread, List.length_append, hPplen c2.thread, ← hL2] at hc2lt
    -- the `(I^k)`-part command transfer (front region `idx < (n+1)·L`)
    have hcmdfront : ∀ (x : ProgPoint), x.idx < (n + 1) * ((I ^ I.loopK h).prog x.thread).length →
        ((I ^ I.loopK h) ^ (n + 1)).cmdAt x = P.cmdAt x := by
      intro x hx
      simp only [CTA.cmdAt]
      rw [hPprog x.thread, List.getElem?_append_left (by rw [hPplen]; exact hx)]
    -- the `E`-part command transfer (epilogue region `idx ≥ (n+1)·L`)
    have hcmdE : ∀ (x : ProgPoint), (n + 1) * ((I ^ I.loopK h).prog x.thread).length ≤ x.idx →
        ((I ^ I.loopK h).seq E hids).cmdAt
            ⟨x.thread, x.idx - n * ((I ^ I.loopK h).prog x.thread).length⟩ = P.cmdAt x := by
      intro x hx
      simp only [CTA.cmdAt]
      have hBprog : ((I ^ I.loopK h).seq E hids).prog x.thread
          = (I ^ I.loopK h).prog x.thread ++ E.prog x.thread := rfl
      rw [hBprog, hPprog x.thread]
      set L := ((I ^ I.loopK h).prog x.thread).length with hLx
      have hexp : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
      rw [List.getElem?_append_right (by omega),
        List.getElem?_append_right (by rw [hPplen]; omega), hPplen]
      congr 1
      rw [← hLx]; omega
    -- a body-instruction extractor for a front/prefix barrier point of `P`
    have bodyCmd : ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length →
        ((I ^ I.loopK h).prog η.thread)[η.idx % ((I ^ I.loopK h).prog η.thread).length]? = some c
          ∧ η.idx % ((I ^ I.loopK h).prog η.thread).length
              < ((I ^ I.loopK h).prog η.thread).length := by
      intro η c par hcmd hbr hlt
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hLpos : 0 < L := by
        rcases Nat.eq_zero_or_pos L with h0 | hp
        · rw [h0, Nat.mul_zero] at hlt; omega
        · exact hp
      have hjL : idx % L < L := Nat.mod_lt _ hLpos
      have hp : idx / L < n + 1 := by
        rw [Nat.div_lt_iff_lt_mul hLpos]; exact hlt
      have hidxeq : idx = (idx / L) * L + idx % L := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
      have hcopy : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, (idx / L) * L + idx % L⟩
          = ((I ^ I.loopK h).prog t)[idx % L]? := CTA.cmdAt_pow_batch_copy _ hjL hp
      rw [← hidxeq, hcmdfront ⟨t, idx⟩ hlt, hcmd] at hcopy
      exact ⟨hcopy.symm, hjL⟩
    -- **(U-front)** a front-2-batch barrier-`b` op has generation `≤ 2δ + 1`
    have hUpperLE : ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length →
        pointGen P τ η ≤ 2 * δ + 1 := by
      intro η c par hcmd hbr hlt2
      have hltn1 : η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length := by
        have : 2 * ((I ^ I.loopK h).prog η.thread).length
            ≤ (n + 1) * ((I ^ I.loopK h).prog η.thread).length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨hbody, hjL⟩ := bodyCmd η c par hcmd hbr hltn1
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt2 hjL hbody ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hLpos : 0 < L := by omega
      have hp2 : idx / L < 2 := by rw [Nat.div_lt_iff_lt_mul hLpos]; omega
      have hidxeq : idx = (idx / L) * L + idx % L := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
      obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
      rw [hfrontgen ⟨t, idx⟩ hlt2,
        show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by rw [← hidxeq]]
      rw [gτ2 t (idx % L) (idx / L) c b par M₁ hjL hp2 hbody hbr hM₁, ← hδdef]
      have hrec := barrierOp_recycleCount_le_batch h ht₁ ht₁L hbody hbr hM₁
        (hwf_any (I ^ I.loopK h)) hfull
      rw [← hδdef] at hrec
      have hple : idx / L ≤ 1 := by omega
      have hmul : (idx / L) * δ ≤ 1 * δ := Nat.mul_le_mul_right δ hple
      omega
    -- **(U-sync, batch 0)** a `sync b` in the front batch has generation `≤ δ`
    have hSync0 : ∀ (η : ProgPoint) (par : ℕ+),
        P.cmdAt η = some (Cmd.sync b par) →
        η.idx < ((I ^ I.loopK h).prog η.thread).length →
        pointGen P τ η ≤ δ := by
      intro η par hcmd hlt0
      have hlt2 : η.idx < 2 * ((I ^ I.loopK h).prog η.thread).length := by omega
      have hltn1 : η.idx < (n + 1) * ((I ^ I.loopK h).prog η.thread).length := by
        have : 1 * ((I ^ I.loopK h).prog η.thread).length
            ≤ (n + 1) * ((I ^ I.loopK h).prog η.thread).length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨hbody, hjL⟩ := bodyCmd η (Cmd.sync b par) par hcmd rfl hltn1
      obtain ⟨t, idx⟩ := η
      dsimp only at hlt0 hlt2 hjL hbody ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      have hmod : idx % L = idx := Nat.mod_eq_of_lt hlt0
      have hdiv : idx / L = 0 := Nat.div_eq_of_lt hlt0
      obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
      rw [hfrontgen ⟨t, idx⟩ hlt2,
        show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by
          rw [hdiv, hmod, Nat.zero_mul, Nat.zero_add]]
      rw [gτ2 t (idx % L) (idx / L) (Cmd.sync b par) b par M₁ hjL (by rw [hdiv]; omega)
        hbody rfl hM₁, ← hδdef, hdiv, Nat.zero_mul, Nat.add_zero]
      have hsync := sync_recycleCount_lt_batch h ht₁ ht₁L hbody hM₁
        (hwf_any (I ^ I.loopK h)) hfull
      rw [← hδdef] at hsync
      omega
    -- **(L, ≥2 batches)** a barrier-`b` op past the first two batches has generation `≥ 2δ + 1`
    have hLowerGE2 : b ∈ I.barriers → ∀ (η : ProgPoint) (c : Cmd) (par : ℕ+),
        P.cmdAt η = some c → Cmd.barrierRef c = some (b, par) →
        2 * ((I ^ I.loopK h).prog η.thread).length ≤ η.idx →
        2 * δ + 1 ≤ pointGen P τ η := by
      intro hbI η c par hcmd hbr hge2
      have hbA : b ∈ (I ^ I.loopK h).barrierSet := hbAofI hbI
      have hδ1 : 1 ≤ δ := one_le_delta h rfl hbI
      obtain ⟨t, idx⟩ := η
      dsimp only at hge2 ⊢
      set L := ((I ^ I.loopK h).prog t).length with hLdef
      by_cases hpre : idx < n * L
      · -- prefix region: `gτpre` with batch `p = idx / L ≥ 2`
        have hLpos : 0 < L := by
          rcases Nat.eq_zero_or_pos L with h0 | hp
          · rw [h0, Nat.mul_zero] at hpre; omega
          · exact hp
        have hpltn1 : idx < (n + 1) * L := by
          have h1 : n * L ≤ (n + 1) * L := Nat.mul_le_mul_right L (by omega)
          omega
        obtain ⟨hbody, hjL⟩ := bodyCmd ⟨t, idx⟩ c par hcmd hbr (by
          dsimp only; rw [← hLdef]; exact hpltn1)
        dsimp only at hbody hjL
        have hp : idx / L < n := by
          rw [Nat.div_lt_iff_lt_mul hLpos]; exact hpre
        have hpge : 2 ≤ idx / L := by
          rw [Nat.le_div_iff_mul_le hLpos]; omega
        have hidxeq : idx = (idx / L) * L + idx % L := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod idx L).symm
        obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, idx % L⟩) hjL
        rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, (idx / L) * L + idx % L⟩ from by rw [← hidxeq]]
        rw [show pointGen P τ ⟨t, (idx / L) * L + idx % L⟩
            = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                ⟨t, (idx / L) * L + idx % L⟩ from by rw [hPeq]]
        rw [gτpre t (idx % L) (idx / L) c b par M₁ hjL hp hbody hbr hM₁, ← hδdef]
        have hmul : 2 * δ ≤ (idx / L) * δ := Nat.mul_le_mul_right δ hpge
        omega
      · -- `B`-region (`idx ≥ n·L`): `gτepi` with `e = idx - n·L`
        rw [Nat.not_lt] at hpre
        set e := idx - n * L with hedef
        have hidxeq : idx = n * L + e := by omega
        -- `gτepi` needs the `B`-region rewrite; the command transfer is region-dependent
        by_cases heL : L ≤ e
        · -- `E`-segment point (`idx ≥ (n+1)·L`): lower bound `≥ δ + 1` plus the `n·δ` bump
          have hge : (n + 1) * L ≤ idx := by
            have h1 : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
            omega
          have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c := by
            have hmap := hcmdE ⟨t, idx⟩ (by dsimp only; rw [← hLdef]; exact hge)
            dsimp only at hmap
            rw [show idx - n * ((I ^ I.loopK h).prog t).length = e from by rw [← hLdef]] at hmap
            rw [hmap]; exact hcmd
          rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, n * L + e⟩ from by rw [← hidxeq]]
          rw [show pointGen P τ ⟨t, n * L + e⟩
              = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                  ⟨t, n * L + e⟩ from by rw [hPeq]]
          rw [gτepi t e c b par hcE hbr, ← hδdef]
          have hlow := seq_epilogue_pointGen_lower h ht₁ ht₁L hids htE htEpre heL hcE hbr hbA
            (hwf_any (I ^ I.loopK h)) hfull
          rw [← hδdef] at hlow
          have hnmul : 1 * δ ≤ n * δ := Nat.mul_le_mul_right δ hn
          omega
        · -- batch-`n` front (`e < L`, `idx < (n+1)·L`): `seq_front_pointGen`; `idx ≥ 2L` ⟹ `n ≥ 2`
          rw [Nat.not_le] at heL
          have hltn1 : idx < (n + 1) * ((I ^ I.loopK h).prog t).length := by
            rw [← hLdef]; have h1 : (n + 1) * L = n * L + L := by rw [Nat.succ_mul]
            omega
          have hbody : ((I ^ I.loopK h).prog t)[e]? = some c := by
            have hcopy : ((I ^ I.loopK h) ^ (n + 1)).cmdAt ⟨t, n * L + e⟩
                = ((I ^ I.loopK h).prog t)[e]? := CTA.cmdAt_pow_batch_copy _ heL (by omega)
            rw [hcmdfront ⟨t, n * L + e⟩ (by dsimp only; rw [← hLdef, ← hidxeq]; exact hltn1),
              show (⟨t, n * L + e⟩ : ProgPoint) = ⟨t, idx⟩ from by rw [← hidxeq], hcmd] at hcopy
            exact hcopy.symm
          have hcE : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, e⟩ = some c := by
            change ((I ^ I.loopK h).prog t ++ E.prog t)[e]? = some c
            rw [List.getElem?_append_left heL]; exact hbody
          rw [show (⟨t, idx⟩ : ProgPoint) = ⟨t, n * L + e⟩ from by rw [← hidxeq]]
          rw [show pointGen P τ ⟨t, n * L + e⟩
              = pointGen (((I ^ I.loopK h) ^ n).seq ((I ^ I.loopK h).seq E hids) hidsE) τ
                  ⟨t, n * L + e⟩ from by rw [hPeq]]
          rw [gτepi t e c b par hcE hbr, ← hδdef]
          obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L (η := ⟨t, e⟩) heL
          rw [seq_front_pointGen h ht₁ ht₁L hids htE htEpre heL hbody hbr hM₁]
          have hnge2 : 2 ≤ n := by
            by_contra hcon
            -- `n = 1`: `e = idx - L < L` and `2L ≤ idx` are contradictory
            have hn1 : n = 1 := by omega
            rw [hn1, Nat.one_mul] at hpre
            have heidx : e = idx - L := by rw [hedef, hn1, Nat.one_mul]
            omega
          have hnmul : 2 * δ ≤ n * δ := Nat.mul_le_mul_right δ hnge2
          omega
    -- **Classification.**  Split on whether `b` is referenced by `I` (`δ ≥ 1`).
    by_cases hbI : b ∈ I.barriers
    · -- `δ ≥ 1`: the generation bounds place the pair.
      have hδ1 : 1 ≤ δ := one_le_delta h rfl hbI
      by_cases hc2front : c2.idx < 2 * L2
      · -- `c2` in the first two batches.  If `c1.idx ≥ 2L1`, generations would jump by `> 1`.
        refine Or.inl ⟨?_, hc2front⟩
        by_contra hc1
        rw [Nat.not_lt] at hc1
        have hlow := hLowerGE2 hbI c1 (Cmd.sync b nn) nn hsync1 rfl (by rw [← hL1]; exact hc1)
        have hupp := hUpperLE c2 cc2' par2 hc2cmd hc2ref (by rw [← hL2]; exact hc2front)
        omega
      · -- `c2` past the first two batches: shiftable.  `c1` cannot be in the front batch.
        rw [Nat.not_lt] at hc2front
        refine Or.inr ⟨?_, by omega⟩
        by_contra hc1
        rw [Nat.not_le] at hc1
        have hupp := hSync0 c1 nn hsync1 (by rw [← hL1]; exact hc1)
        have hlow := hLowerGE2 hbI c2 cc2' par2 hc2cmd hc2ref (by rw [← hL2]; exact hc2front)
        omega
    · -- `b ∉ I.barriers`: neither endpoint is in the `(I^k)^(n+1)` prefix, so both lie in `E`.
      refine Or.inr ⟨?_, ?_⟩
      · -- `c1` past the front batch: else `cmdAt c1 ∈ (I^k)^(n+1)` would force `b ∈ I.barriers`
        by_contra hc1
        rw [Nat.not_le] at hc1
        apply hbI
        have hltn1 : c1.idx < (n + 1) * ((I ^ I.loopK h).prog c1.thread).length := by
          have hbr1 : 1 * ((I ^ I.loopK h).prog c1.thread).length
              ≤ (n + 1) * ((I ^ I.loopK h).prog c1.thread).length :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.one_mul] at hbr1; rw [hL1] at hc1; omega
        exact mem_barriers_of_cmdAt_pow (by rw [hcmdfront c1 hltn1]; exact hsync1) rfl
      · -- likewise `c2`
        by_contra hc2
        rw [Nat.not_lt] at hc2
        apply hbI
        have hltn1 : c2.idx < (n + 1) * ((I ^ I.loopK h).prog c2.thread).length := by
          rw [hL2] at hc2
          rcases Nat.eq_zero_or_pos ((I ^ I.loopK h).prog c2.thread).length with h0 | hp
          · rw [h0] at hc2; omega
          · have hbr2 : 1 * ((I ^ I.loopK h).prog c2.thread).length
                < (n + 1) * ((I ^ I.loopK h).prog c2.thread).length :=
              (Nat.mul_lt_mul_right hp).mpr (by omega)
            rw [Nat.one_mul] at hbr2; omega
        exact mem_barriers_of_cmdAt_pow (by rw [hcmdfront c2 hltn1]; exact hc2cmd) hc2ref
  · -- (uniform monotonicity): lift each `Pn`-edge by the uniform `+L` shift into `P`.
    -- `P.prog t = (I^k).prog t ++ Pn.prog t`, so shifting an index by `L t` moves a `Pn`-point
    -- into `P` while preserving program order and (via `hshift`) all barrier generations.
    intro a b hab
    set Pn := ((I ^ I.loopK h) ^ n).seq E ((CTA.pow_ids (I ^ I.loopK h) n).trans hids) with hPndef
    set P := ((I ^ I.loopK h) ^ (n + 1)).seq E
      ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids) with hPdef
    -- the front-batch decomposition of `P`
    have hPprog : ∀ t, P.prog t = (I ^ I.loopK h).prog t ++ Pn.prog t := fun t => by
      rw [hPdef, CTA.pow_succ_seq_assoc I (I.loopK h) n hids]; rfl
    -- command/membership transfer for a shifted point
    have hcmdtr : ∀ (x : ProgPoint),
        P.cmdAt ⟨x.thread, x.idx + ((I ^ I.loopK h).prog x.thread).length⟩ = Pn.cmdAt x := by
      intro x
      simp only [CTA.cmdAt]
      rw [hPprog x.thread,
        List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
    have hmemtr : ∀ (x : ProgPoint), x ∈ Pn.progPoints →
        (⟨x.thread, x.idx + ((I ^ I.loopK h).prog x.thread).length⟩ : ProgPoint)
          ∈ P.progPoints := by
      intro x hx
      obtain ⟨hth, hlt⟩ := (mem_progPoints_iff Pn x).mp hx
      refine (mem_progPoints_iff P _).mpr ⟨?_, ?_⟩
      · change x.thread ∈ P.ids; rw [hPdef]; change x.thread ∈ ((I ^ I.loopK h) ^ (n + 1)).ids
        rw [CTA.pow_ids]; rw [hPndef] at hth; change x.thread ∈ ((I ^ I.loopK h) ^ n).ids at hth
        rwa [CTA.pow_ids] at hth
      · change x.idx + ((I ^ I.loopK h).prog x.thread).length
          < (P.prog x.thread).length
        rw [hPprog x.thread, List.length_append]; omega
    -- the generation-shift fact in `set` form
    have hshift' : ∀ (η : ProgPoint) (c : Cmd) (bb : Barrier) (par : ℕ+),
        Pn.cmdAt η = some c → Cmd.barrierRef c = some (bb, par) →
        pointGen P τ ⟨η.thread, η.idx + ((I ^ I.loopK h).prog η.thread).length⟩
          = pointGen Pn τn η + I.loopK h * I.arrivers bb / I.arrivalCount h bb :=
      hshift
    refine Relation.ReflTransGen.lift
      (fun η => (⟨η.thread, η.idx + ((I ^ I.loopK h).prog η.thread).length⟩ : ProgPoint))
      (fun x y hxy => ?_) hab
    rw [mem_initRelation_iff] at hxy ⊢
    rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, m, hxpts, hypts, hca, hcb, hg⟩
        | ⟨bb, m, hxpts, hypts, hca, hcb, hg⟩
    · -- program order: both endpoints shift by the same `L x.thread`
      subst hbeq
      refine Or.inl ⟨hmemtr x hxpts, ?_,
        by simp only [ProgPoint.mk.injEq, true_and]; omega⟩
      change x.idx + ((I ^ I.loopK h).prog x.thread).length + 1
        < (P.prog x.thread).length
      rw [hPprog x.thread, List.length_append]; omega
    · -- arrive → sync: both gens bump by `δ_bb`, so they stay equal
      refine Or.inr (Or.inl ⟨bb, m, hmemtr x hxpts, hmemtr y hypts,
        by rw [hcmdtr]; exact hca, by rw [hcmdtr]; exact hcb, ?_⟩)
      rw [hshift' x (Cmd.arrive bb m) bb m hca rfl,
        hshift' y (Cmd.sync bb m) bb m hcb rfl, hg]
    · -- sync ↔ sync: both gens bump by `δ_bb`, so they stay equal
      refine Or.inr (Or.inr ⟨bb, m, hmemtr x hxpts, hmemtr y hypts,
        by rw [hcmdtr]; exact hca, by rw [hcmdtr]; exact hcb, ?_⟩)
      rw [hshift' x (Cmd.sync bb m) bb m hca rfl,
        hshift' y (Cmd.sync bb m) bb m hcb rfl, hg]
  · -- (front monotonicity): every `(I^k)^2`-edge is a `P`-edge (identity embedding).  All
    -- `(I^k)^2`-points have `idx < 2L`, where `((I^k)^2)` is the literal front prefix of `P`, so
    -- commands transfer and generations agree by `hfrontgen`.
    intro a b _ha _hb hab
    set P := ((I ^ I.loopK h) ^ (n + 1)).seq E
      ((CTA.pow_ids (I ^ I.loopK h) (n + 1)).trans hids) with hPdef
    -- `P.prog t = ((I^k)^2).prog t ++ rest`, so on `idx < 2L` commands/points transfer
    have hP2prog : ∀ t, P.prog t
        = ((I ^ I.loopK h) ^ 2).prog t
          ++ (((I ^ I.loopK h) ^ (n - 1)).prog t ++ E.prog t) := by
      intro t
      rw [hPdef]
      change ((I ^ I.loopK h) ^ (n + 1)).prog t ++ E.prog t = _
      rw [show n + 1 = 2 + (n - 1) from by omega, CTA.pow_add_prog, List.append_assoc]
    -- index bound from `(I^k)^2`-membership
    have h2lt : ∀ (x : ProgPoint), x ∈ ((I ^ I.loopK h) ^ 2).progPoints →
        x.idx < 2 * ((I ^ I.loopK h).prog x.thread).length := by
      intro x hx
      have := ((mem_progPoints_iff _ x).mp hx).2
      rwa [CTA.pow_prog_length] at this
    -- command transfer on front points
    have hcmdtr : ∀ (x : ProgPoint),
        x.idx < 2 * ((I ^ I.loopK h).prog x.thread).length →
        P.cmdAt x = ((I ^ I.loopK h) ^ 2).cmdAt x := by
      intro x hx
      simp only [CTA.cmdAt]
      rw [hP2prog x.thread, List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact hx)]
    -- membership transfer on front points
    have hmemtr : ∀ (x : ProgPoint), x ∈ ((I ^ I.loopK h) ^ 2).progPoints →
        x ∈ P.progPoints := by
      intro x hx
      obtain ⟨hth, hlt⟩ := (mem_progPoints_iff _ x).mp hx
      refine (mem_progPoints_iff P _).mpr ⟨?_, ?_⟩
      · rw [hPdef]
        change x.thread ∈ ((I ^ I.loopK h) ^ (n + 1)).ids
        rw [CTA.pow_ids]; rw [CTA.pow_ids] at hth; exact hth
      · rw [hP2prog x.thread, List.length_append]
        rw [CTA.pow_prog_length] at hlt ⊢; omega
    refine Relation.ReflTransGen.mono (fun x y hxy => ?_) hab
    rw [mem_initRelation_iff] at hxy ⊢
    rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, m, hxpts, hypts, hca, hcb, hg⟩
        | ⟨bb, m, hxpts, hypts, hca, hcb, hg⟩
    · -- program order: stays in `P`, target index still in range
      refine Or.inl ⟨hmemtr x hxpts, ?_, hbeq⟩
      rw [hP2prog x.thread, List.length_append]
      rw [CTA.pow_prog_length] at hlt ⊢; omega
    · -- arrive → sync: commands/gens transfer on the front
      refine Or.inr (Or.inl ⟨bb, m, hmemtr x hxpts, hmemtr y hypts,
        by rw [hcmdtr x (h2lt x hxpts)]; exact hca,
        by rw [hcmdtr y (h2lt y hypts)]; exact hcb, ?_⟩)
      rw [hfrontgen x (h2lt x hxpts), hfrontgen y (h2lt y hypts)]; exact hg
    · -- sync ↔ sync
      refine Or.inr (Or.inr ⟨bb, m, hmemtr x hxpts, hmemtr y hypts,
        by rw [hcmdtr x (h2lt x hxpts)]; exact hca,
        by rw [hcmdtr y (h2lt y hypts)]; exact hcb, ?_⟩)
      rw [hfrontgen x (h2lt x hxpts), hfrontgen y (h2lt y hypts)]; exact hg

/-- **One-batch inductive step for `loop_with_epilogue`** (the analogue of
`batches_inductive_step_impl`; proof deferred). Given the batch certifications and a
well-synchronized `n`-batches-plus-epilogue program `(I^k)^n ⨾ E`, extending by one more batch
stays well-synchronized: `WS((I^k)^(n+1) ⨾ E)`.

This is where the substantive work lives. Its proof will mirror `batches_inductive_step_impl`'s
checker-soundness casework (`wellSynchronized_of_check` + a hypothetical failing line-18 pair,
classified by where its endpoints fall), generalized to carry the epilogue `E`. The casework
will be fed by sub-lemmas added *when we prove this step*:

* the **epilogue replay/generation bundle**, which (via `pow_succ_seq_assoc`, `P = (I^k) ⨾ Pn`)
  gives replay traces of `P` and `Pn := (I^k)^n ⨾ E` and the uniform `+L` shift/monotonicity facts
  transporting `Pn`'s well-synchronization into `P` — the user's "generations all shift by the
  per-batch factor".

A flagged pair is then classified by whether `c2` lands in the prepended front batch (index
`< L`, handled by `hbatch = WS(I^k)`) or in the shifted prefix (index `≥ L`, shifted down to a
flagged pair of `Pn` that `hprev`'s checker orders, then lifted back by monotonicity). -/
theorem CTA.WellSynchronized.loop_epilogue_inductive_step {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {E : CTA}
    (hids : (I ^ k).ids = E.ids)
    (hbatch : (I ^ k).WellSynchronized) (h2batch : ((I ^ k) ^ 2).WellSynchronized)
    (hbatchE : ((I ^ k).seq E hids).WellSynchronized)
    {n : Nat} (hn : 1 ≤ n)
    (hprev : (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)).WellSynchronized) :
    (((I ^ k) ^ (n + 1)).seq E
        ((CTA.pow_ids (I ^ k) (n + 1)).trans hids)).WellSynchronized := by
  -- Build the initial-anchored batch data and feed the (now from-`s`) bundle.
  obtain ⟨t₁, ht₁⟩ := hbatch.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h (hk ▸ ht₁) ht₁L
  rw [hinit] at ht₁L
  obtain ⟨tE, htE, htEpre⟩ := CTA.WellSynchronized.seq_angelic_prefix hids hbatchE t₁ ht₁
  -- The shared replay traces and the uniform `+L` shift/monotonicity facts (`P = (I^k) ⨾ Pn`).
  obtain ⟨τ, hτ, hcoloc, τn, hτn, hshift, hmono, τ2, hτ2, hfrontgen, hfrontmono, hgenbounds,
      hfrontclosed, -, -, -, hbridge⟩ :=
    CTA.WellSynchronized.loop_epilogue_replay_bundle h hk hids hn ht₁ ht₁L htE htEpre
      (fun _ => rfl) (fun _ => WF_initial)
  set Pn := ((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids) with hPn
  set P := ((I ^ k) ^ (n + 1)).seq E ((CTA.pow_ids (I ^ k) (n + 1)).trans hids) with hP
  -- Close via checker soundness; it remains to show the checker accepts `τ`.
  refine wellSynchronized_of_check hτ ?_
  -- Suppose the checker rejects; `exists_failing_pair` exposes a flagged pair `(c1, c2)`.
  by_contra hcheckfalse
  rw [Bool.not_eq_true] at hcheckfalse
  obtain ⟨c1, hc1, b, hbar1, c2, hc2, hbar2, hgen, hfail⟩ :=
    exists_failing_pair hcheckfalse
  -- The `c2.idx = 0` failure mode of the strengthened checker is vacuous for these
  -- well-synchronized batched-loop programs: a barrier op that is its thread's first
  -- instruction has generation `≤ 1` (it gets registered into generation `1` on a schedule
  -- that steps its thread first), so it can never be the gen-`(k+1)` target of a Step-3 pair.
  -- An idx-`0` op lives either in the loop's prepended front batch (transfer to the WS
  -- `(I^k)^2` reference) or, if the loop body is empty for its thread, at the head of the
  -- epilogue `E` (transfer to the WS `(I^k) ⨾ E`, where the bridge forces its per-batch
  -- factor `δ` to `0`).
  have hidxne : c2.idx ≠ 0 := by
    intro hidx0
    clear_value P Pn
    subst hk
    -- decode c2's barrier command kind and its reference
    obtain ⟨cc2, par2, hc2cmd, hc2ref⟩ : ∃ (cc2 : Cmd) (par2 : ℕ+),
        P.cmdAt c2 = some cc2 ∧ Cmd.barrierRef cc2 = some (b, par2) := by
      cases hcm : P.cmdAt c2 with
      | none => rw [hcm] at hbar2; simp at hbar2
      | some cc =>
        cases cc with
        | read g => rw [hcm] at hbar2; simp [Cmd.barrier?] at hbar2
        | write g => rw [hcm] at hbar2; simp [Cmd.barrier?] at hbar2
        | arrive bb mm =>
          rw [hcm] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcm] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
    -- gen(c2) ≥ 2: `pointGen c2 = pointGen c1 + 1` and `pointGen c1 ≥ 1` (c1 executes in `done τ`)
    obtain ⟨sd, hdone⟩ := hτ.2
    have hc1L : c1.idx < (P.prog c1.thread).length :=
      ((mem_progPoints_iff _ c1).mp hc1).2
    obtain ⟨mc1, hmc1⟩ := exists_time_of_ends_done hτ.1 hdone hc1L
    have hge2 : 2 ≤ pointGen P τ c2 := by
      have := isGenOf_recycleCount (isGenOf_pointGen hbar1 hmc1) hbar1 hmc1; omega
    -- c2's thread is one of the loop body's threads
    have hthread : c2.thread ∈ (I ^ I.loopK h).ids := by
      have hmem := ((mem_progPoints_iff _ c2).mp hc2).1
      rw [hP] at hmem
      change c2.thread ∈ ((I ^ I.loopK h) ^ (n + 1)).ids at hmem
      rwa [CTA.pow_ids] at hmem
    by_cases hLpos : 0 < ((I ^ I.loopK h).prog c2.thread).length
    · -- c2 is in the loop's prepended front batch: transfer to `(I^k)^2` and apply `firstInstr'`
      have hidxlt2 : c2.idx < 2 * ((I ^ I.loopK h).prog c2.thread).length := by
        rw [hidx0]; omega
      have htransfer := hfrontgen c2 hidxlt2
      have hbase : ((I ^ I.loopK h).prog c2.thread)[0]? = some cc2 := by
        have hh : (P.prog c2.thread)[c2.idx]? = some cc2 := hc2cmd
        rw [hidx0, hP] at hh
        change ((((I ^ I.loopK h) ^ (n + 1)).prog c2.thread) ++ E.prog c2.thread)[0]?
          = some cc2 at hh
        rw [CTA.pow_succ_prog, List.append_assoc, List.getElem?_append_left hLpos] at hh
        exact hh
      have hc2cmd2 : ((I ^ I.loopK h) ^ 2).cmdAt c2 = some cc2 := by
        change (((I ^ I.loopK h) ^ 2).prog c2.thread)[c2.idx]? = some cc2
        rw [hidx0, show (2 : ℕ) = 1 + 1 from rfl, CTA.pow_succ_prog,
          List.getElem?_append_left hLpos]
        exact hbase
      have hbar2_2 : (((I ^ I.loopK h) ^ 2).cmdAt c2).bind Cmd.barrier? = some b := by
        rw [hc2cmd2]; simp only [Option.bind_some]; exact Cmd.barrier?_of_barrierRef hc2ref
      have hc2pts2 : c2 ∈ ((I ^ I.loopK h) ^ 2).progPoints := by
        rw [mem_progPoints_iff]
        refine ⟨by rw [CTA.pow_ids]; exact hthread, ?_⟩
        rw [hidx0, CTA.pow_prog_length]; omega
      exact firstInstr_highGen_not_wellSynchronized' hτ2 h2batch hc2pts2 hbar2_2
        (htransfer ▸ hge2) hidx0
    · -- the loop body is empty for c2's thread: c2 is the first instruction of the epilogue `E`
      rw [Nat.not_lt, Nat.le_zero] at hLpos
      have hc2eta : (⟨c2.thread, c2.idx⟩ : ProgPoint) = c2 := rfl
      have hpow0 : ((I ^ I.loopK h) ^ (n + 1)).prog c2.thread = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [CTA.pow_prog_length, hLpos, Nat.mul_zero]
      have hIk0 : (I ^ I.loopK h).prog c2.thread = [] :=
        List.eq_nil_of_length_eq_zero hLpos
      have hEbase : (E.prog c2.thread)[c2.idx]? = some cc2 := by
        have hh : (P.prog c2.thread)[c2.idx]? = some cc2 := hc2cmd
        rw [hP] at hh
        change ((((I ^ I.loopK h) ^ (n + 1)).prog c2.thread) ++ E.prog c2.thread)[c2.idx]?
          = some cc2 at hh
        rw [hpow0, List.nil_append] at hh
        exact hh
      have hcEcmd : ((I ^ I.loopK h).seq E hids).cmdAt c2 = some cc2 := by
        change ((I ^ I.loopK h).prog c2.thread ++ E.prog c2.thread)[c2.idx]? = some cc2
        rw [hIk0, List.nil_append]; exact hEbase
      have hbar2B : (((I ^ I.loopK h).seq E hids).cmdAt c2).bind Cmd.barrier? = some b := by
        rw [hcEcmd]; simp only [Option.bind_some]; exact Cmd.barrier?_of_barrierRef hc2ref
      have hc2idxlt : c2.idx < (E.prog c2.thread).length :=
        (List.getElem?_eq_some_iff.mp hEbase).1
      have hc2B : c2 ∈ ((I ^ I.loopK h).seq E hids).progPoints := by
        rw [mem_progPoints_iff]
        refine ⟨hthread, ?_⟩
        change c2.idx < ((I ^ I.loopK h).prog c2.thread ++ E.prog c2.thread).length
        rw [List.length_append, hLpos, Nat.zero_add]; exact hc2idxlt
      -- the WS sub-program `(I^k) ⨾ E` has c2 as a first instruction ⇒ its generation is `≤ 1`
      have hgenB_le : pointGen ((I ^ I.loopK h).seq E hids) tE c2 ≤ 1 := by
        by_contra hgt
        rw [Nat.not_le] at hgt
        exact firstInstr_highGen_not_wellSynchronized' htE hbatchE hc2B hbar2B (by omega) hidx0
      -- the per-batch factor `δ` for c2's barrier is `0`
      have hδ0 : I.loopK h * I.arrivers b / I.arrivalCount h b = 0 := by
        by_cases hbA : b ∈ (I ^ I.loopK h).barrierSet
        · have heL : ((I ^ I.loopK h).prog c2.thread).length ≤ c2.idx := by
            rw [hLpos]; exact Nat.zero_le _
          have hlow := seq_epilogue_pointGen_lower (t := c2.thread) (e := c2.idx)
            h ht₁ ht₁L hids htE htEpre heL hcEcmd hc2ref hbA WF_initial (fun _ => rfl)
          have hcomb := le_trans hlow hgenB_le
          set δ := I.loopK h * I.arrivers b / I.arrivalCount h b
          clear_value δ
          omega
        · -- `b` is not used by the loop body, so `arrivers(b) = 0` and `δ = 0`
          have hbInot : b ∉ I.barriers := by
            intro hbIyes
            rw [CTA.barriers, Finset.mem_biUnion] at hbIyes
            obtain ⟨i, hi, hbi⟩ := hbIyes
            rw [List.mem_toFinset, List.mem_map] at hbi
            obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
            simp only at hb'; subst hb'
            rw [List.mem_filterMap] at hr
            obtain ⟨c, hc, hcr⟩ := hr
            have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
            have hcA : c ∈ (I ^ I.loopK h).prog i := by
              rw [show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
                List.mem_append]
              exact Or.inl hc
            apply hbA
            rw [CTA.barrierSet, Finset.mem_biUnion]
            refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
              ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
            rw [CTA.pow_ids]; exact hi
          have hIarr0 : I.arrivers b = 0 := by
            rw [CTA.arrivers]; apply Finset.sum_eq_zero
            intro i hi
            rw [List.countP_eq_zero]
            intro r hr
            simp only [List.mem_filterMap] at hr
            obtain ⟨c, hc, hcr⟩ := hr
            simp only [beq_iff_eq]; intro hrb
            apply hbInot
            rw [CTA.barriers, Finset.mem_biUnion]
            exact ⟨i, hi, List.mem_toFinset.mpr
              (List.mem_map.mpr ⟨r, List.mem_filterMap.mpr ⟨c, hc, hcr⟩, hrb⟩)⟩
          rw [hIarr0, Nat.mul_zero, Nat.zero_div]
      -- the bridge at `e = c2.idx` (where `n·L + e = c2.idx` since `L = 0`) gives
      -- `pointGen P τ c2 = pointGen ((I^k) ⨾ E) tE c2 + n·δ ≤ 1`, contradicting `gen(c2) ≥ 2`
      have hbridgeApp := hbridge c2.thread c2.idx cc2 b par2 hcEcmd hc2ref
      rw [hLpos, Nat.mul_zero, Nat.zero_add, hδ0, Nat.mul_zero, Nat.add_zero, hc2eta]
        at hbridgeApp
      omega
  obtain ⟨hidx, hc1ne3, hnotmem⟩ := hfail.resolve_right hidxne
  apply hnotmem
  rw [snd_checkWellSynchronized]
  -- The full program is one front batch prepended to `Pn`: `P.prog t = (I^k).prog t ++ Pn.prog t`.
  have hPprog : ∀ t, P.prog t = (I ^ k).prog t ++ Pn.prog t :=
    fun t => by rw [hP, CTA.pow_succ_seq_assoc I k n hids]; rfl
  -- `L1`, `L2` are the prepended front batch's lengths in `c1`/`c2`'s threads.
  set L2 := ((I ^ k).prog c2.thread).length with hL2
  set L1 := ((I ^ k).prog c1.thread).length with hL1
  -- Decode c1's barrier command kind and its reference.
  obtain ⟨cc1, par1, hc1cmd, hc1ref⟩ : ∃ (cc1 : Cmd) (par1 : ℕ+),
      P.cmdAt c1 = some cc1 ∧ Cmd.barrierRef cc1 = some (b, par1) := by
    cases hcmd : P.cmdAt c1 with
    | none => rw [hcmd] at hbar1; simp at hbar1
    | some cc1 =>
      cases cc1 with
      | read g => rw [hcmd] at hbar1; simp [Cmd.barrier?] at hbar1
      | write g => rw [hcmd] at hbar1; simp [Cmd.barrier?] at hbar1
      | arrive bb mm =>
        rw [hcmd] at hbar1
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
        subst hbar1; exact ⟨_, mm, rfl, rfl⟩
      | sync bb mm =>
        rw [hcmd] at hbar1
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
        subst hbar1; exact ⟨_, mm, rfl, rfl⟩
  -- Decode c2's barrier command kind and its reference.
  obtain ⟨cc2, par2, hc2cmd, hc2ref⟩ : ∃ (cc2 : Cmd) (par2 : ℕ+),
      P.cmdAt c2 = some cc2 ∧ Cmd.barrierRef cc2 = some (b, par2) := by
    cases hcmd : P.cmdAt c2 with
    | none => rw [hcmd] at hbar2; simp at hbar2
    | some cc2 =>
      cases cc2 with
      | read g => rw [hcmd] at hbar2; simp [Cmd.barrier?] at hbar2
      | write g => rw [hcmd] at hbar2; simp [Cmd.barrier?] at hbar2
      | arrive bb mm =>
        rw [hcmd] at hbar2
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
        subst hbar2; exact ⟨_, mm, rfl, rfl⟩
      | sync bb mm =>
        rw [hcmd] at hbar2
        simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
        subst hbar2; exact ⟨_, mm, rfl, rfl⟩
  -- Classify the pair as front-local or shiftable; sync uses the bundle coloc, arrive the bounds.
  have hcoloc_result : (c1.idx < 2 * L1 ∧ c2.idx < 2 * L2) ∨ (L1 ≤ c1.idx ∧ L2 < c2.idx) := by
    cases hcc1 : cc1 with
    | sync b' par1' =>
      obtain ⟨rfl, rfl⟩ : b = b' ∧ par1 = par1' := by
        have h := hc1ref; rw [hcc1] at h
        simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      rw [hcc1] at hc1cmd
      exact hcoloc c1 c2 b par1 hc1cmd hbar2 hgen hidx
    | arrive b' par1' =>
      obtain ⟨rfl, rfl⟩ : b = b' ∧ par1 = par1' := by
        have h := hc1ref; rw [hcc1] at h
        simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, h.2.symm⟩
      -- c1 is an arrive on b
      by_cases hbI : b ∈ I.barriers
      · have hδ1 : 1 ≤ k * I.arrivers b / I.arrivalCount h b := one_le_delta h hk hbI
        by_cases hc2front : c2.idx < 2 * L2
        · -- c2 in front: c1 must also be in front (else gen(c1) ≥ 2δ+1 but gen(c2) ≤ 2δ+1)
          refine Or.inl ⟨?_, hc2front⟩
          by_contra hc1ge
          rw [Nat.not_lt] at hc1ge
          have hlow := (hgenbounds b).2.2 hbI c1 cc1 par1 hc1cmd hc1ref
            (by rw [← hL1]; exact hc1ge)
          have hupp := (hgenbounds b).1 c2 cc2 par2 hc2cmd hc2ref
            (by rw [← hL2]; exact hc2front)
          omega
        · -- c2 past front: c1 must be shiftable (else gen(c1) ≤ δ < 2δ+1 ≤ gen(c2) = gen(c1)+1)
          rw [Nat.not_lt] at hc2front
          refine Or.inr ⟨?_, by omega⟩
          by_contra hc1lt
          rw [Nat.not_le] at hc1lt
          have hbody1 : ((I ^ k).prog c1.thread)[c1.idx]? = some cc1 := by
            have h := hc1cmd
            simp only [CTA.cmdAt, hPprog c1.thread,
              List.getElem?_append_left (by rw [← hL1]; exact hc1lt)] at h
            simpa [CTA.cmdAt]
          obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L
            (η := ⟨c1.thread, c1.idx⟩) (hL1 ▸ hc1lt)
          have hfc := hfrontclosed c1.thread c1.idx 0 cc1 b par1 M₁
            (hL1 ▸ hc1lt) (by omega) hbody1 hc1ref hM₁
          simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] at hfc
          rw [show (⟨c1.thread, c1.idx⟩ : ProgPoint) = c1 from rfl] at hfc
          have hrec := arrive_recycleCount_lt_batch h (hk ▸ ht₁) ht₁L
            (hk ▸ hcc1 ▸ hbody1) (hk ▸ hM₁) WF_initial (fun _ => rfl) rfl
          rw [← hk] at hrec
          have hlow := (hgenbounds b).2.2 hbI c2 cc2 par2 hc2cmd hc2ref
            (by rw [← hL2]; omega)
          omega
      · -- b ∉ I.barriers: both c1 and c2 lie in the epilogue E (past all body batches)
        refine Or.inr ⟨?_, ?_⟩
        · by_contra hc1lt
          rw [Nat.not_le] at hc1lt
          apply hbI
          have hbody1 : ((I ^ k).prog c1.thread)[c1.idx]? = some cc1 := by
            have h := hc1cmd
            simp only [CTA.cmdAt, hPprog c1.thread,
              List.getElem?_append_left (by rw [← hL1]; exact hc1lt)] at h
            simpa [CTA.cmdAt]
          exact mem_barriers_of_cmdAt_pow (I := I) (k := k) (m := 1)
            (by rw [CTA.pow_one]; simpa [CTA.cmdAt]) hc1ref
        · by_contra hc2le
          rw [Nat.not_lt] at hc2le
          apply hbI
          have hc2lt_n1 : c2.idx < (n + 1) * L2 := by
            have hL2pos : 0 < L2 := by omega
            have hlt : L2 < (n + 1) * L2 := by
              rw [Nat.add_mul, Nat.one_mul]
              have : 0 < n * L2 := Nat.mul_pos (by omega) hL2pos
              omega
            omega
          have hP_c2 : ((I ^ k) ^ (n + 1)).cmdAt c2 = some cc2 := by
            have hprog : P.prog c2.thread =
                ((I ^ k) ^ (n + 1)).prog c2.thread ++ E.prog c2.thread := by rw [hP]; rfl
            simp only [CTA.cmdAt, hprog,
              List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact hc2lt_n1)] at hc2cmd
            simpa [CTA.cmdAt]
          exact mem_barriers_of_cmdAt_pow hP_c2 hc2ref
    | read g => simp [Cmd.barrierRef, hcc1] at hc1ref
    | write g => simp [Cmd.barrierRef, hcc1] at hc1ref
  -- It suffices to produce the happens-before edge `c1 → c3`; `hc1ne3` lifts it into `R`.
  suffices hHB : happensBefore P τ c1 ⟨c2.thread, c2.idx - 1⟩ by
    rw [happensBefore, Relation.reflTransGen_iff_eq_or_transGen] at hHB
    rcases hHB with heq | htg
    · exact absurd heq.symm hc1ne3
    · exact mem_transClosure_of_transGen _ hc1ne3 htg
  -- Dispatch front vs. core case.
  rcases hcoloc_result with ⟨hc1s, hc2s⟩ | ⟨hc1b, hc2b⟩
  · -- **Front case.** Both endpoints lie in the first two batches `(I^k)^2`; order via `h2batch`.
    have hP2prog : ∀ t, P.prog t
        = ((I ^ k) ^ 2).prog t ++ (((I ^ k) ^ (n - 1)).prog t ++ E.prog t) := by
      intro t
      rw [hP]
      change ((I ^ k) ^ (n + 1)).prog t ++ E.prog t = _
      rw [show n + 1 = 2 + (n - 1) from by omega, CTA.pow_add_prog, List.append_assoc]
    have hcmdfront : ∀ η : ProgPoint, η.idx < 2 * ((I ^ k).prog η.thread).length →
        ((I ^ k) ^ 2).cmdAt η = P.cmdAt η := by
      intro η hη
      simp only [CTA.cmdAt]
      rw [hP2prog η.thread, List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact hη)]
    have hbar1₂ : (((I ^ k) ^ 2).cmdAt c1).bind Cmd.barrier? = some b := by
      rw [hcmdfront c1 hc1s]; exact hbar1
    have hbar2₂ : (((I ^ k) ^ 2).cmdAt c2).bind Cmd.barrier? = some b := by
      rw [hcmdfront c2 hc2s]; exact hbar2
    have hc1₂ : ((I ^ k) ^ 2).cmdAt c1 = some cc1 := by
      rw [hcmdfront c1 hc1s]; exact hc1cmd
    have hc2₂ : ((I ^ k) ^ 2).cmdAt c2 = some cc2 := by
      rw [hcmdfront c2 hc2s]; exact hc2cmd
    have hgen₂ : pointGen ((I ^ k) ^ 2) τ2 c2 = pointGen ((I ^ k) ^ 2) τ2 c1 + 1 := by
      rw [← hfrontgen c1 hc1s, ← hfrontgen c2 hc2s]; exact hgen
    have hcheck₂ : (CheckWellSynchronized ((I ^ k) ^ 2) τ2).1 = true :=
      (checkWellSynchronized_correct_impl hτ2).mpr h2batch
    exact hfrontmono c1 ⟨c2.thread, c2.idx - 1⟩ hc1s
      (by change c2.idx - 1 < 2 * ((I ^ k).prog c2.thread).length; omega)
      (happensBefore_of_check hcheck₂ (mem_progPoints_of_cmdAt _ hc1₂) hbar1₂
        (mem_progPoints_of_cmdAt _ hc2₂) hbar2₂ hgen₂ hidx)
  · -- **Core case.** Both endpoints lie in the shifted prefix `Pn`; order via `hprev` and lift.
    have hcmd1 : Pn.cmdAt ⟨c1.thread, c1.idx - L1⟩ = P.cmdAt c1 := by
      simp only [CTA.cmdAt]
      rw [hPprog c1.thread, List.getElem?_append_right hc1b]
    have hcmd2 : Pn.cmdAt ⟨c2.thread, c2.idx - L2⟩ = P.cmdAt c2 := by
      simp only [CTA.cmdAt]
      rw [hPprog c2.thread, List.getElem?_append_right hc2b.le]
    have hbar1' : (Pn.cmdAt ⟨c1.thread, c1.idx - L1⟩).bind Cmd.barrier? = some b := by
      rw [hcmd1]; exact hbar1
    have hbar2' : (Pn.cmdAt ⟨c2.thread, c2.idx - L2⟩).bind Cmd.barrier? = some b := by
      rw [hcmd2]; exact hbar2
    have hcheckPn : (CheckWellSynchronized Pn τn).1 = true :=
      (checkWellSynchronized_correct_impl hτn).mpr hprev
    have hpt1 : c1.idx - L1 + ((I ^ k).prog c1.thread).length = c1.idx := by rw [← hL1]; omega
    have hpt2 : c2.idx - L2 + ((I ^ k).prog c2.thread).length = c2.idx := by rw [← hL2]; omega
    have hpt3 : c2.idx - L2 - 1 + ((I ^ k).prog c2.thread).length = c2.idx - 1 := by
      rw [← hL2]; omega
    have hc1Pn : Pn.cmdAt ⟨c1.thread, c1.idx - L1⟩ = some cc1 := by rw [hcmd1, hc1cmd]
    have hc2Pn : Pn.cmdAt ⟨c2.thread, c2.idx - L2⟩ = some cc2 := by rw [hcmd2, hc2cmd]
    have hg1 : pointGen P τ c1 = pointGen Pn τn ⟨c1.thread, c1.idx - L1⟩
        + k * I.arrivers b / I.arrivalCount h b := by
      have hs1 := hshift ⟨c1.thread, c1.idx - L1⟩ cc1 b par1 hc1Pn hc1ref
      rwa [hpt1] at hs1
    have hg2 : pointGen P τ c2 = pointGen Pn τn ⟨c2.thread, c2.idx - L2⟩
        + k * I.arrivers b / I.arrivalCount h b := by
      have hs2 := hshift ⟨c2.thread, c2.idx - L2⟩ cc2 b par2 hc2Pn hc2ref
      rwa [hpt2] at hs2
    have hgen' : pointGen Pn τn ⟨c2.thread, c2.idx - L2⟩
        = pointGen Pn τn ⟨c1.thread, c1.idx - L1⟩ + 1 := by omega
    have hidx' : 1 ≤ c2.idx - L2 := by omega
    have hHBpn := happensBefore_of_check hcheckPn
      (mem_progPoints_of_cmdAt Pn hc1Pn) hbar1'
      (mem_progPoints_of_cmdAt Pn hc2Pn) hbar2' hgen' hidx'
    have hHBp := hmono _ _ hHBpn
    rw [hpt1, hpt3] at hHBp
    exact hHBp

/-- **Loop with epilogue** (the crux of the loop check). If the batch `I ^ k` and the
two-batch loop `(I ^ k) ^ 2` are well-synchronized, and `I ^ k` followed by an arbitrary
epilogue `E` is well-synchronized, then *any* number `n ≥ 1` of batches followed by `E` is
well-synchronized: `WS((I ^ k) ^ n ⨾ E)`.

This generalizes `loop_well_synchronized_impl` (the `E`-free pure loop) by carrying a trailing
epilogue through the batch induction. Instantiating `E := I ^ r` discharges the non-multiple
unrollings `I ^ (k * n + r)` of `checkLoopWellSynchronized_correct` below: `r = 0` is the pure
loop, `0 < r < k` the "trailing iterations" after the last full batch.

The `(I ^ k) ^ 2` hypothesis is essential and *not* redundant with `WS(I ^ k)`: among the `n`
batches the batch-to-batch boundaries form a pure loop, which — exactly as for
`loop_well_synchronized` — needs the two-batch certification (a single batch cannot exhibit a
batch boundary). All three hypotheses sit among the first `2k` checked unrollings (`I ^ k`,
`I ^ (2k) = (I ^ k) ^ 2`, and `I ^ (k + r) = I ^ k ⨾ I ^ r`).

Proof: induction on `n` — base `n = 1` is `hbatchE` (since `(I ^ k) ^ 1 = I ^ k`); the step is
`loop_epilogue_inductive_step`. -/
theorem CTA.WellSynchronized.loop_with_epilogue {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {E : CTA} (hids : (I ^ k).ids = E.ids)
    (hbatch : (I ^ k).WellSynchronized) (h2batch : ((I ^ k) ^ 2).WellSynchronized)
    (hbatchE : ((I ^ k).seq E hids).WellSynchronized) :
    ∀ n, 1 ≤ n →
      (((I ^ k) ^ n).seq E ((CTA.pow_ids (I ^ k) n).trans hids)).WellSynchronized := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp only [CTA.pow_one]; exact hbatchE
  | succ n hn ih =>
      exact CTA.WellSynchronized.loop_epilogue_inductive_step h hk hids hbatch h2batch hbatchE
        hn ih

/-- **Regroup a loop-with-epilogue unrolling into prefix-loop form.** `k * c + r` body
iterations factor as `c` full `k`-batches with the `r`-iteration remainder folded into the
epilogue: `P ⨾ I^(k*c+r) ⨾ E = P ⨾ (I^k)^c ⨾ (I^r ⨾ E)`. This is the bridge from the loop
check (which certifies unrollings `P ⨾ I^i ⨾ E`) to `loop_with_prefix_epilogue` (which reasons
about `Pre ⨾ (I^k)^n ⨾ E`); take `Pre := P`, body `I^k`, epilogue `I^r ⨾ E`. -/
theorem CTA.loopProgram_regroup (P I E : CTA) (h1 : P.ids = I.ids) (h2 : I.ids = E.ids)
    (k c r : Nat) :
    CTA.loopProgram P I E h1 h2 (k * c + r)
      = CTA.loopProgram P (I ^ k) ((I ^ r).seq E ((CTA.pow_ids I r).trans h2))
          (h1.trans (CTA.pow_ids I k).symm) ((CTA.pow_ids I k).trans (CTA.pow_ids I r).symm) c := by
  apply CTA.ext
  · simp only [CTA.loopProgram_ids]
  · funext t
    simp only [CTA.loopProgram_prog]
    change P.prog t ++ (I ^ (k * c + r)).prog t ++ E.prog t
        = P.prog t ++ ((I ^ k) ^ c).prog t ++ ((I ^ r).prog t ++ E.prog t)
    rw [CTA.pow_add_prog, CTA.pow_mul]
    simp only [List.append_assoc]

/-- **One-batch inductive step for `loop_with_prefix_epilogue`.** The prefix analogue of
`loop_epilogue_inductive_step`: from `WS(Pre ⨾ (I^k)^n ⨾ E)` derive `WS(Pre ⨾ (I^k)^(n+1) ⨾ E)`.
A flagged pair of the `(n+1)`-program is classified by co-location into a *front* pair (both in
`Pre` + the first two batches, `idx < Lp + 2L`), ordered via the two-batch reference
`hPre2BatchRef` and lifted by front-monotonicity (with the front chain confined by soundness,
`glue_no_happensBefore_B_to_A`), or a *core* pair (both off the inserted first batch
`[Lp, Lp+L)`), shifted down one batch, ordered via `hprev`, and lifted by the total ψ-embedding. -/
theorem CTA.WellSynchronized.loop_prefix_epilogue_inductive_step {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h) {Pre E E_ref : CTA}
    (hpre : Pre.ids = (I ^ k).ids) (hids : (I ^ k).ids = E.ids)
    (hidsRef : (I ^ k).ids = E_ref.ids)
    (hPre : Pre.WellSynchronized) (hPreBody : (Pre.seq (I ^ k) hpre).WellSynchronized)
    (hPreBatchE : (CTA.loopProgram Pre (I ^ k) E hpre hids 1).WellSynchronized)
    (hPre3BatchRef : (CTA.loopProgram Pre (I ^ k) E_ref hpre hidsRef 3).WellSynchronized)
    {n : Nat} (hn : 2 ≤ n)
    (hprev : (CTA.loopProgram Pre (I ^ k) E hpre hids n).WellSynchronized) :
    (CTA.loopProgram Pre (I ^ k) E hpre hids (n + 1)).WellSynchronized := by
  subst hk
  set A := I ^ I.loopK h with hA
  -- prefix data (`s_P`, `tP`, restoring batch `t₁`, structured `tE`) and reference data
  obtain ⟨s_P, hfull, hwf_any, tP, htP, htPL, t₁, ht₁, ht₁L, tE, htE, htEpre⟩ :=
    loop_prefix_batch_data h rfl hpre hids hPre hPreBody hPreBatchE
  obtain ⟨⟨tER, htER, htERpre⟩, ⟨tAR, htAR, htARlast⟩⟩ :=
    loop_prefix_ref_data h rfl hpre hidsRef hfull hwf_any htP htPL ht₁ ht₁L hPre3BatchRef
  -- from-`s_P` bundles for `E` (`n` batches) and `E_ref` (`1` batch → `(A^2) ⨾ E_ref`)
  obtain ⟨τX, hτX, hcolocX, τnX, hτnX, hshiftX, hmonoX, τ2X, hτ2X, hfrontgenX, hfrontmonoX,
      hgbX, hfcX, hfcNX, hfrontpreX, hfrontepiX, hbridgeX⟩ :=
    loop_epilogue_replay_bundle h rfl hids (show (1 : ℕ) ≤ n by omega) ht₁ ht₁L htE htEpre hfull
      hwf_any
  obtain ⟨τZ, hτZ, hcolocZ, τnZ, hτnZ, hshiftZ, hmonoZ, τ2Z, hτ2Z, hfrontgenZ, hfrontmonoZ,
      hgbZ, hfcZ, -, hfrontpreZ, hfrontepiZ, -⟩ :=
    loop_epilogue_replay_bundle h rfl hidsRef (by omega : (1 : ℕ) ≤ 2) ht₁ ht₁L htER htERpre
      hfull hwf_any
  -- view the goal as `Pre ⨾ Xfull` with `Xfull = (A^(n+1)) ⨾ E`
  set Xfull := (A ^ (n + 1)).seq E ((CTA.pow_ids A (n + 1)).trans hids) with hXfull
  have hpreXf : Pre.ids = Xfull.ids := by
    rw [hXfull]; change Pre.ids = (A ^ (n + 1)).ids; rw [CTA.pow_ids]; exact hpre
  have hfullEq : CTA.loopProgram Pre A E hpre hids (n + 1) = Pre.seq Xfull hpreXf := by
    apply CTA.ext
    · simp only [CTA.loopProgram_ids, CTA.seq]
    · funext t
      rw [CTA.loopProgram_prog]
      change Pre.prog t ++ (A ^ (n + 1)).prog t ++ E.prog t
        = Pre.prog t ++ ((A ^ (n + 1)).prog t ++ E.prog t)
      rw [List.append_assoc]
  rw [hfullEq]
  obtain ⟨hτfull, -, -⟩ := glue_trace hpreXf htP htPL hτX
  set Pfull := Pre.seq Xfull hpreXf with hPfulldef
  set τfull := List.map (Config.seqLift Pre Xfull) tP.dropLast ++ τX.tail with hτfulldef
  refine wellSynchronized_of_check hτfull ?_
  by_contra hcheckfalse
  rw [Bool.not_eq_true] at hcheckfalse
  obtain ⟨c1, hc1, b, hbar1, c2, hc2, hbar2, hgen, hfail⟩ :=
    exists_failing_pair hcheckfalse
  -- The `c2.idx = 0` failure mode of the strengthened checker is vacuous for these
  -- well-synchronized prefix-loop programs.  An idx-`0` barrier op is its thread's first
  -- instruction, so its generation is `≤ 1` in any well-synchronized program that has it as a
  -- first instruction.  By region (relative to `Pre`/loop/`E`) `c2` is the head of either the
  -- prefix `Pre` (use `hPre`), the loop body (use `hPreBody`, generations matching via the
  -- batch-0 closed form), or — when both `Pre` and the loop body are empty for `c2`'s thread —
  -- the epilogue `E` (use `hPreBatchE`, where the epilogue bridge forces the per-batch factor
  -- `δ` to `0`).  Each contradicts `firstInstr_highGen_not_wellSynchronized'`.
  have hidxne : c2.idx ≠ 0 := by
    intro hidx0
    have hc2eta : (⟨c2.thread, c2.idx⟩ : ProgPoint) = c2 := rfl
    -- decode c2's barrier command kind and its reference
    obtain ⟨cc2, par2, hc2cmd, hc2ref⟩ : ∃ (cc2 : Cmd) (par2 : ℕ+),
        Pfull.cmdAt c2 = some cc2 ∧ Cmd.barrierRef cc2 = some (b, par2) := by
      cases hcmd2 : Pfull.cmdAt c2 with
      | none => rw [hcmd2] at hbar2; simp at hbar2
      | some cc2 =>
        cases cc2 with
        | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
        | arrive bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
        | sync bb mm =>
          rw [hcmd2] at hbar2
          simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
          subst hbar2; exact ⟨_, mm, rfl, rfl⟩
    have hbar : Cmd.barrier? cc2 = some b := Cmd.barrier?_of_barrierRef hc2ref
    -- gen(c2) ≥ 2
    obtain ⟨sd, hdone⟩ := hτfull.2
    have hc1L : c1.idx < (Pfull.prog c1.thread).length :=
      ((mem_progPoints_iff _ c1).mp hc1).2
    obtain ⟨mc1, hmc1⟩ := exists_time_of_ends_done hτfull.1 hdone hc1L
    have hge2 : 2 ≤ pointGen Pfull τfull c2 := by
      have := isGenOf_recycleCount (isGenOf_pointGen hbar1 hmc1) hbar1 hmc1; omega
    have hthread : c2.thread ∈ Pre.ids := by
      have hmem := ((mem_progPoints_iff _ c2).mp hc2).1
      rw [hPfulldef] at hmem; exact hmem
    by_cases hLppos : 0 < (Pre.prog c2.thread).length
    · -- **region 1**: `c2` is the first instruction of the prefix `Pre`
      have hc2lt : c2.idx < (Pre.prog c2.thread).length := by omega
      have hcmdPre : Pre.cmdAt c2 = some cc2 := by
        have hx : (Pre.prog c2.thread ++ Xfull.prog c2.thread)[c2.idx]? = some cc2 := hc2cmd
        rwa [List.getElem?_append_left hc2lt] at hx
      have hbarPre : (Pre.cmdAt c2).bind Cmd.barrier? = some b := by
        rw [hcmdPre]; simp only [Option.bind_some]; exact hbar
      have hc2Pre : c2 ∈ Pre.progPoints := (mem_progPoints_iff _ _).mpr ⟨hthread, hc2lt⟩
      have hgenPre : pointGen Pfull τfull c2 = pointGen Pre tP c2 := by
        rw [hPfulldef, hτfulldef]
        exact seq_glue_prefix_pointGen hpreXf htP htPL hτX hcmdPre hc2ref
      exact firstInstr_highGen_not_wellSynchronized' htP hPre hc2Pre hbarPre
        (hgenPre ▸ hge2) hidx0
    · rw [Nat.not_lt, Nat.le_zero] at hLppos
      have hPreNil : Pre.prog c2.thread = [] := List.eq_nil_of_length_eq_zero hLppos
      have hcX2 : Xfull.cmdAt c2 = some cc2 := by
        have hx : (Pre.prog c2.thread ++ Xfull.prog c2.thread)[c2.idx]? = some cc2 := hc2cmd
        rwa [hPreNil, List.nil_append] at hx
      -- `pointGen Pfull` of an `Xfull`-region point lifts across the `Pre` glue by `+R`
      have hPfullgen : pointGen Pfull τfull c2
          = recycleCount b tP (tP.length - 2) + pointGen Xfull τX c2 := by
        have h := seq_glue_epilogue_pointGen hpreXf htP htPL hτX hcX2 hc2ref
        simp only [hLppos, Nat.zero_add, hc2eta] at h
        rw [hPfulldef, hτfulldef]; exact h
      by_cases hLpos : 0 < ((I ^ I.loopK h).prog c2.thread).length
      · -- **region 2**: empty prefix, `c2` is the first instruction of the loop body
        have hc2Llt : c2.idx < ((I ^ I.loopK h).prog c2.thread).length := by
          rw [hidx0]; exact hLpos
        have hbody : (I ^ I.loopK h).cmdAt c2 = some cc2 := by
          have hx : ((((I ^ I.loopK h) ^ (n + 1)).prog c2.thread) ++ E.prog c2.thread)[c2.idx]?
              = some cc2 := hcX2
          rw [List.getElem?_append_left
                (by rw [CTA.pow_prog_length, hidx0]; exact Nat.mul_pos (by omega) hLpos),
              hidx0, CTA.pow_succ_prog, List.getElem?_append_left hLpos] at hx
          change ((I ^ I.loopK h).prog c2.thread)[c2.idx]? = some cc2
          rw [hidx0]; exact hx
        obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L hc2Llt
        -- batch-0 generation closed form, both in `Xfull` and in the bare batch `t₁`
        have hXgen : pointGen Xfull τX c2 = recycleCount b t₁ (M₁ - 1) + 1 := by
          have h := hfrontpreX c2.thread c2.idx 0 cc2 b par2 M₁ hc2Llt (by omega) hbody hc2ref hM₁
          simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, hc2eta] at h
          exact h
        have hAgen : pointGen (I ^ I.loopK h) t₁ c2 = recycleCount b t₁ (M₁ - 1) + 1 := by
          simp only [pointGen, hbody, Option.bind_some, hbar, pointTime_eq_of_isTimeOf hM₁]
        -- the reference `Pre ⨾ (I^k)` (= `hPreBody`) with c2's generation matching
        obtain ⟨hτbody, -, -⟩ := glue_trace hpre htP htPL ht₁
        have hgenbody := seq_glue_epilogue_pointGen hpre htP htPL ht₁ hbody hc2ref
        simp only [hLppos, Nat.zero_add, hc2eta] at hgenbody
        have hcmdbody : (Pre.seq (I ^ I.loopK h) hpre).cmdAt c2 = some cc2 := by
          change (Pre.prog c2.thread ++ (I ^ I.loopK h).prog c2.thread)[c2.idx]? = some cc2
          rw [hPreNil, List.nil_append]; exact hbody
        have hbarbody : ((Pre.seq (I ^ I.loopK h) hpre).cmdAt c2).bind Cmd.barrier? = some b := by
          rw [hcmdbody]; simp only [Option.bind_some]; exact hbar
        have hc2body : c2 ∈ (Pre.seq (I ^ I.loopK h) hpre).progPoints := by
          rw [mem_progPoints_iff]; refine ⟨hthread, ?_⟩
          change c2.idx < (Pre.prog c2.thread ++ (I ^ I.loopK h).prog c2.thread).length
          rw [List.length_append, hLppos, Nat.zero_add]; exact hc2Llt
        have hge2body : 2 ≤ pointGen (Pre.seq (I ^ I.loopK h) hpre)
            (tP.dropLast.map (Config.seqLift Pre (I ^ I.loopK h)) ++ t₁.tail) c2 := by
          rw [hgenbody, hAgen, ← hXgen, ← hPfullgen]; exact hge2
        exact firstInstr_highGen_not_wellSynchronized' hτbody hPreBody hc2body hbarbody
          hge2body hidx0
      · -- **region 3**: empty prefix and empty loop body, `c2` heads the epilogue `E`
        rw [Nat.not_lt, Nat.le_zero] at hLpos
        have hAnil : (I ^ I.loopK h).prog c2.thread = [] := List.eq_nil_of_length_eq_zero hLpos
        have hpow0 : ((I ^ I.loopK h) ^ (n + 1)).prog c2.thread = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [CTA.pow_prog_length, hLpos, Nat.mul_zero]
        have hcEcmd : ((I ^ I.loopK h).seq E hids).cmdAt c2 = some cc2 := by
          change ((I ^ I.loopK h).prog c2.thread ++ E.prog c2.thread)[c2.idx]? = some cc2
          rw [hAnil, List.nil_append]
          have hx : ((((I ^ I.loopK h) ^ (n + 1)).prog c2.thread) ++ E.prog c2.thread)[c2.idx]?
              = some cc2 := hcX2
          rwa [hpow0, List.nil_append] at hx
        have hEnonnil : c2.idx < (E.prog c2.thread).length := by
          have hx : ((I ^ I.loopK h).prog c2.thread ++ E.prog c2.thread)[c2.idx]? = some cc2 :=
            hcEcmd
          rw [hAnil, List.nil_append] at hx
          exact (List.getElem?_eq_some_iff.mp hx).1
        -- the bridge: `pointGen Xfull` of c2 = `pointGen (I^k ⨾ E) tE c2 + n·δ` (here `n·δ = 0`)
        have hbr2 : pointGen Xfull τX c2 = pointGen ((I ^ I.loopK h).seq E hids) tE c2
            + n * (I.loopK h * I.arrivers b / I.arrivalCount h b) := by
          have h := hbridgeX c2.thread c2.idx cc2 b par2 hcEcmd hc2ref
          simp only [hLpos, Nat.mul_zero, Nat.zero_add, hc2eta] at h
          exact h
        rw [hbr2] at hPfullgen
        -- the reference `Pre ⨾ (I^k ⨾ E)` (= `hPreBatchE`), forcing c2's generation `≤ 1`
        have hpreB : Pre.ids = ((I ^ I.loopK h).seq E hids).ids := hpre
        have hQeq : CTA.loopProgram Pre (I ^ I.loopK h) E hpre hids 1
            = Pre.seq ((I ^ I.loopK h).seq E hids) hpreB := by
          apply CTA.ext
          · rfl
          · funext t
            rw [CTA.loopProgram_prog]
            change Pre.prog t ++ ((I ^ I.loopK h) ^ 1).prog t ++ E.prog t
              = Pre.prog t ++ ((I ^ I.loopK h).prog t ++ E.prog t)
            rw [CTA.pow_one_prog, List.append_assoc]
        rw [hQeq] at hPreBatchE
        obtain ⟨hτQ, -, -⟩ := glue_trace hpreB htP htPL htE
        have hgenQ := seq_glue_epilogue_pointGen hpreB htP htPL htE hcEcmd hc2ref
        simp only [hLppos, Nat.zero_add, hc2eta] at hgenQ
        have hcmdQ : (Pre.seq ((I ^ I.loopK h).seq E hids) hpreB).cmdAt c2 = some cc2 := by
          change (Pre.prog c2.thread ++ ((I ^ I.loopK h).seq E hids).prog c2.thread)[c2.idx]?
            = some cc2
          rw [hPreNil, List.nil_append]; exact hcEcmd
        have hbarQ : ((Pre.seq ((I ^ I.loopK h).seq E hids) hpreB).cmdAt c2).bind Cmd.barrier?
            = some b := by rw [hcmdQ]; simp only [Option.bind_some]; exact hbar
        have hc2Q : c2 ∈ (Pre.seq ((I ^ I.loopK h).seq E hids) hpreB).progPoints := by
          rw [mem_progPoints_iff]; refine ⟨hthread, ?_⟩
          change c2.idx
            < (Pre.prog c2.thread ++ ((I ^ I.loopK h).seq E hids).prog c2.thread).length
          rw [List.length_append, hLppos, Nat.zero_add]
          change c2.idx < ((I ^ I.loopK h).prog c2.thread ++ E.prog c2.thread).length
          rw [List.length_append, hLpos, Nat.zero_add]; exact hEnonnil
        have hQle1 : pointGen (Pre.seq ((I ^ I.loopK h).seq E hids) hpreB)
            (tP.dropLast.map (Config.seqLift Pre ((I ^ I.loopK h).seq E hids)) ++ tE.tail) c2
            ≤ 1 := by
          by_contra hgt
          rw [Nat.not_le] at hgt
          exact firstInstr_highGen_not_wellSynchronized' hτQ hPreBatchE hc2Q hbarQ
            (by omega) hidx0
        have hBle1 : pointGen ((I ^ I.loopK h).seq E hids) tE c2 ≤ 1 := by
          have h := hQle1; rw [hgenQ] at h; omega
        -- the per-batch factor `δ` for `c2`'s barrier is `0`
        have hδ0 : I.loopK h * I.arrivers b / I.arrivalCount h b = 0 := by
          by_cases hbA : b ∈ (I ^ I.loopK h).barrierSet
          · have heL : ((I ^ I.loopK h).prog c2.thread).length ≤ c2.idx := by
              rw [hLpos]; exact Nat.zero_le _
            have hlow := seq_epilogue_pointGen_lower (t := c2.thread) (e := c2.idx)
              h ht₁ ht₁L hids htE htEpre heL hcEcmd hc2ref hbA (hwf_any _) hfull
            rw [hc2eta] at hlow
            have hcomb := le_trans hlow hBle1
            set δ := I.loopK h * I.arrivers b / I.arrivalCount h b
            clear_value δ; omega
          · have hbInot : b ∉ I.barriers := by
              intro hbIyes
              rw [CTA.barriers, Finset.mem_biUnion] at hbIyes
              obtain ⟨i, hi, hbi⟩ := hbIyes
              rw [List.mem_toFinset, List.mem_map] at hbi
              obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
              simp only at hb'; subst hb'
              rw [List.mem_filterMap] at hr
              obtain ⟨c, hc, hcr⟩ := hr
              have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
              have hcA : c ∈ (I ^ I.loopK h).prog i := by
                rw [show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
                  List.mem_append]
                exact Or.inl hc
              apply hbA
              rw [CTA.barrierSet, Finset.mem_biUnion]
              refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
                ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
              rw [CTA.pow_ids]; exact hi
            have hIarr0 : I.arrivers b = 0 := by
              rw [CTA.arrivers]; apply Finset.sum_eq_zero
              intro i hi
              rw [List.countP_eq_zero]
              intro r hr
              simp only [List.mem_filterMap] at hr
              obtain ⟨c, hc, hcr⟩ := hr
              simp only [beq_iff_eq]; intro hrb
              apply hbInot
              rw [CTA.barriers, Finset.mem_biUnion]
              exact ⟨i, hi, List.mem_toFinset.mpr
                (List.mem_map.mpr ⟨r, List.mem_filterMap.mpr ⟨c, hc, hcr⟩, hrb⟩)⟩
            rw [hIarr0, Nat.mul_zero, Nat.zero_div]
        rw [hδ0, Nat.mul_zero, Nat.add_zero] at hPfullgen
        omega
  obtain ⟨hidx, hc1ne3, hnotmem⟩ := hfail.resolve_right hidxne
  apply hnotmem
  rw [snd_checkWellSynchronized]
  set δ := I.loopK h * I.arrivers b / I.arrivalCount h b with hδ
  set R := recycleCount b tP (tP.length - 2) with hR
  -- decode `c1`'s barrier op generically (mirror the `c2` decode below)
  obtain ⟨cc1, par1, hc1cmd, hc1ref⟩ : ∃ (cc1 : Cmd) (par1 : ℕ+),
      Pfull.cmdAt c1 = some cc1 ∧ Cmd.barrierRef cc1 = some (b, par1) := by
    cases hcmd1 : Pfull.cmdAt c1 with
    | none => rw [hcmd1] at hbar1; simp at hbar1
    | some cc1 =>
      cases cc1 with
      | read g => rw [hcmd1] at hbar1; simp [Cmd.barrier?] at hbar1
      | write g => rw [hcmd1] at hbar1; simp [Cmd.barrier?] at hbar1
      | arrive bb mm =>
        rw [hcmd1] at hbar1; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
        subst hbar1; exact ⟨_, mm, rfl, rfl⟩
      | sync bb mm =>
        rw [hcmd1] at hbar1; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar1
        subst hbar1; exact ⟨_, mm, rfl, rfl⟩
  -- `Pfull.prog t = Pre.prog t ++ Xfull.prog t`, with `Xfull.prog t = (A^(n+1)).prog t ++ E.prog t`
  have hPfullprog : ∀ t, Pfull.prog t = Pre.prog t ++ Xfull.prog t := fun _ => rfl
  -- (Step 0) generation of an `Xfull`-region point across the `Pre` glue
  have hgX : ∀ (t : ThreadId) (e : Nat) (cc : Cmd) (par : ℕ+),
      Xfull.cmdAt ⟨t, e⟩ = some cc → Cmd.barrierRef cc = some (b, par) →
      pointGen Pfull τfull ⟨t, (Pre.prog t).length + e⟩ = R + pointGen Xfull τX ⟨t, e⟩ :=
    fun t e cc par hcE hbr => seq_glue_epilogue_pointGen hpreXf htP htPL hτX hcE hbr
  -- a `Pfull`-command in the `Pre` region restricts to `Pre`
  have hcmdPre : ∀ (η : ProgPoint) (cc : Cmd), η.idx < (Pre.prog η.thread).length →
      Pfull.cmdAt η = some cc → Pre.cmdAt η = some cc := by
    intro η cc hlt hcmd
    have : (Pre.prog η.thread ++ Xfull.prog η.thread)[η.idx]? = some cc := hcmd
    rwa [List.getElem?_append_left hlt] at this
  -- a `Pfull`-command in the `Xfull` region restricts to `Xfull` (shifted index)
  have hcmdX : ∀ (η : ProgPoint) (cc : Cmd), (Pre.prog η.thread).length ≤ η.idx →
      Pfull.cmdAt η = some cc →
      Xfull.cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ = some cc := by
    intro η cc hle hcmd
    have : (Pre.prog η.thread ++ Xfull.prog η.thread)[η.idx]? = some cc := hcmd
    rwa [List.getElem?_append_right hle] at this
  -- **(front closed form on `Pfull`)** an in-batch (`e < (n+1)·L`) `Xfull`-region barrier-`b` op,
  -- lifted across the `Pre` glue, has generation `R + rec + 1 + p·δ` with `rec ≤ δ` (`p = e/L`).
  -- Combines `hgX` (the `+R` glue) with the bundle's exact `hfrontpreX`/`hfrontepiX` closed forms
  -- and `barrierOp_recycleCount_le_batch` (`rec ≤ δ`).  All three Pfull bounds below specialize it.
  have hfrontPf : ∀ (t : ThreadId) (e : Nat) (cc : Cmd) (par : ℕ+),
      Xfull.cmdAt ⟨t, e⟩ = some cc → Cmd.barrierRef cc = some (b, par) →
      e < (n + 1) * (A.prog t).length →
      ∃ rec : Nat, pointGen Pfull τfull ⟨t, (Pre.prog t).length + e⟩
          = R + (rec + 1 + (e / (A.prog t).length) * δ) ∧ rec ≤ δ := by
    intro t e cc par hcX hbr heLt
    have hLpos : 0 < (A.prog t).length := by
      rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hp
      · rw [h0, Nat.mul_zero] at heLt; omega
      · exact hp
    have hjL : e % (A.prog t).length < (A.prog t).length := Nat.mod_lt _ hLpos
    have hpn1 : e / (A.prog t).length < n + 1 := by rw [Nat.div_lt_iff_lt_mul hLpos]; omega
    have hedecomp : e = e / (A.prog t).length * (A.prog t).length + e % (A.prog t).length := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod e _).symm
    have hbody : ((I ^ I.loopK h).prog t)[e % (A.prog t).length]? = some cc := by
      have h1 : (A ^ (n + 1)).cmdAt ⟨t, e⟩ = some cc := by
        have hx : ((A ^ (n + 1)).prog t ++ E.prog t)[e]? = some cc := hcX
        rwa [List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact heLt)] at hx
      have h2 : (A ^ (n + 1)).cmdAt ⟨t, e⟩
          = ((I ^ I.loopK h).prog t)[e % (A.prog t).length]? := by
        conv_lhs => rw [show (⟨t, e⟩ : ProgPoint)
          = ⟨t, e / (A.prog t).length * (A.prog t).length + e % (A.prog t).length⟩ from by
            rw [← hedecomp]]
        exact CTA.cmdAt_pow_batch_copy A hjL hpn1
      rw [← h2]; exact h1
    obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L
      (η := ⟨t, e % (A.prog t).length⟩) hjL
    refine ⟨recycleCount b t₁ (M₁ - 1), ?_,
      barrierOp_recycleCount_le_batch h ht₁ ht₁L hbody hbr hM₁ (hwf_any _) hfull⟩
    rw [hgX t e cc par hcX hbr]
    congr 1
    rw [show (⟨t, e⟩ : ProgPoint)
      = ⟨t, e / (A.prog t).length * (A.prog t).length + e % (A.prog t).length⟩ from by
        rw [← hedecomp]]
    rcases Nat.lt_or_ge (e / (A.prog t).length) n with hpltn | hpgen
    · exact hfrontpreX t (e % (A.prog t).length) (e / (A.prog t).length) cc b par M₁ hjL hpltn
        hbody hbr hM₁
    · have hpeqn : e / (A.prog t).length = n := by omega
      rw [hpeqn]
      exact hfrontepiX t (e % (A.prog t).length) cc b par M₁ hjL hbody hbr hM₁
  -- **(PU3)** a front (`idx < Lp + 3L`) barrier-`b` op has generation `≤ R + 3δ + 1`
  have hPU3 : ∀ (η : ProgPoint) (cc : Cmd) (par : ℕ+), Pfull.cmdAt η = some cc →
      Cmd.barrierRef cc = some (b, par) →
      η.idx < (Pre.prog η.thread).length + 3 * (A.prog η.thread).length →
      pointGen Pfull τfull η ≤ R + 3 * δ + 1 := by
    intro η cc par hcmd hbr hlt
    obtain ⟨t, idx⟩ := η; dsimp only at hcmd hlt ⊢
    by_cases hpre : idx < (Pre.prog t).length
    · rw [seq_glue_prefix_pointGen hpreXf htP htPL hτX (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr]
      have := barrierOp_gen_le_total htP htPL (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr
      omega
    · rw [Nat.not_lt] at hpre
      have hLpos : 0 < (A.prog t).length := by
        rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hp
        · rw [h0, Nat.mul_zero] at hlt; omega
        · exact hp
      have hcX := hcmdX ⟨t, idx⟩ cc hpre hcmd
      have heLt : idx - (Pre.prog t).length < (n + 1) * (A.prog t).length := by
        have : 3 * (A.prog t).length ≤ (n + 1) * (A.prog t).length :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨rec, hgen, hrecle⟩ := hfrontPf t (idx - (Pre.prog t).length) cc par hcX hbr heLt
      rw [show idx = (Pre.prog t).length + (idx - (Pre.prog t).length) from by omega, hgen]
      have hp3 : (idx - (Pre.prog t).length) / (A.prog t).length < 3 := by
        rw [Nat.div_lt_iff_lt_mul hLpos]; omega
      have hmul : ((idx - (Pre.prog t).length) / (A.prog t).length) * δ ≤ 2 * δ :=
        Nat.mul_le_mul_right δ (by omega)
      omega
  -- **(PB0)** a batch-0 (`idx < Lp + L`) barrier-`b` op has generation `≤ R + δ + 1` (any op)
  have hPB0 : ∀ (η : ProgPoint) (cc : Cmd) (par : ℕ+), Pfull.cmdAt η = some cc →
      Cmd.barrierRef cc = some (b, par) →
      η.idx < (Pre.prog η.thread).length + (A.prog η.thread).length →
      pointGen Pfull τfull η ≤ R + δ + 1 := by
    intro η cc par hcmd hbr hlt
    obtain ⟨t, idx⟩ := η; dsimp only at hcmd hlt ⊢
    by_cases hpre : idx < (Pre.prog t).length
    · rw [seq_glue_prefix_pointGen hpreXf htP htPL hτX (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr]
      have := barrierOp_gen_le_total htP htPL (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr
      clear_value δ; omega
    · rw [Nat.not_lt] at hpre
      have hLpos : 0 < (A.prog t).length := by omega
      have hcX := hcmdX ⟨t, idx⟩ cc hpre hcmd
      have heLt : idx - (Pre.prog t).length < (n + 1) * (A.prog t).length := by
        have : (A.prog t).length ≤ (n + 1) * (A.prog t).length :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      obtain ⟨rec, hgen, hrecle⟩ := hfrontPf t (idx - (Pre.prog t).length) cc par hcX hbr heLt
      rw [show idx = (Pre.prog t).length + (idx - (Pre.prog t).length) from by omega, hgen]
      have hp0 : (idx - (Pre.prog t).length) / (A.prog t).length = 0 :=
        Nat.div_eq_of_lt (by omega)
      rw [hp0]; omega
  -- **(PL3)** a `≥3`-batch (`idx ≥ Lp + 3L`) barrier-`b` op has generation `≥ R + 3δ + 1`.
  -- In-batch (`e < (n+1)L`): `hfrontPf` with batch `p = e/L ≥ 3`.  E-region (`e ≥ (n+1)L`): the
  -- epilogue bridge `hbridgeX` (`= pointGen B tE + n·δ`) plus `seq_epilogue_pointGen_lower`
  -- (`≥ δ+1`), giving `≥ (δ+1)+n·δ ≥ 3δ+1` since `n ≥ 3`.
  have hPL3 : b ∈ I.barriers → ∀ (η : ProgPoint) (cc : Cmd) (par : ℕ+), Pfull.cmdAt η = some cc →
      Cmd.barrierRef cc = some (b, par) →
      (Pre.prog η.thread).length + 3 * (A.prog η.thread).length ≤ η.idx →
      R + 3 * δ + 1 ≤ pointGen Pfull τfull η := by
    intro hbI η cc par hcmd hbr hge
    obtain ⟨t, idx⟩ := η; dsimp only at hcmd hge ⊢
    have hδ1 : 1 ≤ δ := by rw [hδ]; exact one_le_delta h rfl hbI
    have hpre : (Pre.prog t).length ≤ idx := by
      have h0 : 0 ≤ 3 * (A.prog t).length := Nat.zero_le _; omega
    have hcX := hcmdX ⟨t, idx⟩ cc hpre hcmd
    have hge3 : 3 * (A.prog t).length ≤ idx - (Pre.prog t).length := by omega
    by_cases hinb : idx - (Pre.prog t).length < (n + 1) * (A.prog t).length
    · obtain ⟨rec, hgen, hrecle⟩ := hfrontPf t (idx - (Pre.prog t).length) cc par hcX hbr hinb
      rw [show idx = (Pre.prog t).length + (idx - (Pre.prog t).length) from by omega, hgen]
      have hLpos : 0 < (A.prog t).length := by
        rcases Nat.eq_zero_or_pos (A.prog t).length with h0 | hp
        · rw [h0, Nat.mul_zero] at hinb; omega
        · exact hp
      have hp3 : 3 ≤ (idx - (Pre.prog t).length) / (A.prog t).length := by
        rw [Nat.le_div_iff_mul_le hLpos]; omega
      have hmul : 3 * δ ≤ ((idx - (Pre.prog t).length) / (A.prog t).length) * δ :=
        Nat.mul_le_mul_right δ hp3
      clear_value δ; omega
    · rw [Nat.not_lt] at hinb
      have hbA : b ∈ (I ^ I.loopK h).barrierSet := by
        rw [CTA.barriers, Finset.mem_biUnion] at hbI
        obtain ⟨i, hi, hbi⟩ := hbI
        rw [List.mem_toFinset, List.mem_map] at hbi
        obtain ⟨⟨b', n'⟩, hr, hb'⟩ := hbi
        simp only at hb'; subst hb'
        rw [List.mem_filterMap] at hr
        obtain ⟨c, hc, hcr⟩ := hr
        have hkpos : 1 ≤ I.loopK h := I.loopK_pos h
        have hcA : c ∈ (I ^ I.loopK h).prog i := by
          rw [show I.loopK h = (I.loopK h - 1) + 1 from by omega, CTA.pow_succ_prog,
            List.mem_append]
          exact Or.inl hc
        rw [CTA.barrierSet, Finset.mem_biUnion]
        refine ⟨i, ?_, List.mem_toFinset.mpr (List.mem_filterMap.mpr
          ⟨c, hcA, Cmd.barrier?_of_barrierRef hcr⟩)⟩
        rw [CTA.pow_ids]; exact hi
      have hmuln : (n + 1) * (A.prog t).length
          = n * (A.prog t).length + (A.prog t).length := by rw [Nat.succ_mul]
      set ee := idx - (Pre.prog t).length - n * (A.prog t).length with heedef
      have heeL : (A.prog t).length ≤ ee := by omega
      have heeeq : idx - (Pre.prog t).length = n * (A.prog t).length + ee := by omega
      have hcE_B : ((I ^ I.loopK h).seq E hids).cmdAt ⟨t, ee⟩ = some cc := by
        change ((I ^ I.loopK h).prog t ++ E.prog t)[ee]? = some cc
        rw [List.getElem?_append_right heeL,
          show ee - ((I ^ I.loopK h).prog t).length
            = (idx - (Pre.prog t).length) - (n + 1) * (A.prog t).length from by
            rw [show ((I ^ I.loopK h).prog t).length = (A.prog t).length from rfl]; omega]
        have hXE : Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩
            = (E.prog t)[(idx - (Pre.prog t).length) - (n + 1) * (A.prog t).length]? := by
          change ((A ^ (n + 1)).prog t ++ E.prog t)[idx - (Pre.prog t).length]? = _
          rw [List.getElem?_append_right (by rw [CTA.pow_prog_length]; exact hinb),
            CTA.pow_prog_length]
        rw [← hXE]; exact hcX
      have hgenE : pointGen Xfull τX ⟨t, idx - (Pre.prog t).length⟩
          = pointGen ((I ^ I.loopK h).seq E hids) tE ⟨t, ee⟩ + n * δ := by
        rw [show (⟨t, idx - (Pre.prog t).length⟩ : ProgPoint)
          = ⟨t, n * (A.prog t).length + ee⟩ from by rw [← heeeq]]
        exact hbridgeX t ee cc b par hcE_B hbr
      have hlow := seq_epilogue_pointGen_lower h ht₁ ht₁L hids htE htEpre heeL hcE_B hbr hbA
        (hwf_any _) hfull
      rw [← hδ] at hlow
      rw [show idx = (Pre.prog t).length + (idx - (Pre.prog t).length) from by omega,
        hgX t (idx - (Pre.prog t).length) cc par hcX hbr, hgenE]
      have hn3 : 2 * δ ≤ n * δ := Nat.mul_le_mul_right δ (by omega)
      clear_value δ; omega
  -- `c2`'s command is a barrier op on `b`
  obtain ⟨cc2, par2, hc2cmd, hc2ref⟩ : ∃ (cc2 : Cmd) (par2 : ℕ+),
      Pfull.cmdAt c2 = some cc2 ∧ Cmd.barrierRef cc2 = some (b, par2) := by
    cases hcmd2 : Pfull.cmdAt c2 with
    | none => rw [hcmd2] at hbar2; simp at hbar2
    | some cc2 =>
      cases cc2 with
      | read g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
      | write g => rw [hcmd2] at hbar2; simp [Cmd.barrier?] at hbar2
      | arrive bb mm =>
        rw [hcmd2] at hbar2; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
        subst hbar2; exact ⟨_, mm, rfl, rfl⟩
      | sync bb mm =>
        rw [hcmd2] at hbar2; simp only [Option.bind_some, Cmd.barrier?, Option.some.injEq] at hbar2
        subst hbar2; exact ⟨_, mm, rfl, rfl⟩
  -- index bounds for `c1`, `c2`
  have hc1lt : c1.idx < (Pfull.prog c1.thread).length :=
    ((mem_progPoints_iff _ c1).mp (mem_progPoints_of_cmdAt _ hc1cmd)).2
  have hc2lt : c2.idx < (Pfull.prog c2.thread).length :=
    ((mem_progPoints_iff _ c2).mp (mem_progPoints_of_cmdAt _ hc2cmd)).2
  -- **Co-location**: classify the flagged pair into front / core (3-batch front; arrives can span
  -- 3 batches, so the front threshold is `3L`).
  have hcoloc : (c1.idx < (Pre.prog c1.thread).length + 3 * (A.prog c1.thread).length ∧
        c2.idx < (Pre.prog c2.thread).length + 3 * (A.prog c2.thread).length) ∨
      ((c1.idx < (Pre.prog c1.thread).length ∨
          (Pre.prog c1.thread).length + (A.prog c1.thread).length ≤ c1.idx) ∧
        (Pre.prog c2.thread).length + 3 * (A.prog c2.thread).length ≤ c2.idx) := by
    obtain ⟨sdX, hτXlast⟩ := hτX.2
    -- an `Xfull`-region barrier-`b` op has generation `≥ R + 1`
    have hgXge1 : ∀ (η : ProgPoint) (cc : Cmd) (parr : ℕ+), Pfull.cmdAt η = some cc →
        Cmd.barrierRef cc = some (b, parr) → (Pre.prog η.thread).length ≤ η.idx →
        R + 1 ≤ pointGen Pfull τfull η := by
      intro η cc parr hcmd hbr hle
      obtain ⟨t, idx⟩ := η; dsimp only at hcmd hle ⊢
      have hcX : Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩ = some cc :=
        hcmdX ⟨t, idx⟩ cc hle hcmd
      have hidxeq : idx = (Pre.prog t).length + (idx - (Pre.prog t).length) := by omega
      rw [hidxeq, hgX t (idx - (Pre.prog t).length) cc parr hcX hbr]
      have := one_le_pointGen_barrierOp hτX hτXlast hcX hbr
      omega
    -- a `Pre`-region barrier-`b` op has generation `≤ R + 1`
    have hgPreLe : ∀ (η : ProgPoint) (cc : Cmd) (parr : ℕ+), Pfull.cmdAt η = some cc →
        Cmd.barrierRef cc = some (b, parr) → η.idx < (Pre.prog η.thread).length →
        pointGen Pfull τfull η ≤ R + 1 := by
      intro η cc parr hcmd hbr hltp
      obtain ⟨t, idx⟩ := η; dsimp only at hcmd hltp ⊢
      rw [seq_glue_prefix_pointGen hpreXf htP htPL hτX (hcmdPre ⟨t, idx⟩ cc hltp hcmd) hbr]
      have := barrierOp_gen_le_total htP htPL (hcmdPre ⟨t, idx⟩ cc hltp hcmd) hbr
      omega
    by_cases hbI : b ∈ I.barriers
    · have hδ1 : 1 ≤ δ := by rw [hδ]; exact one_le_delta h rfl hbI
      by_cases hc2front : c2.idx < (Pre.prog c2.thread).length + 3 * (A.prog c2.thread).length
      · -- `c2` front ⟹ `c1` front (else `c1 ≥ 3L` jumps gen above `c2`'s front bound)
        refine Or.inl ⟨?_, hc2front⟩
        by_contra hc1con
        rw [Nat.not_lt] at hc1con
        have hlow := hPL3 hbI c1 cc1 par1 hc1cmd hc1ref hc1con
        have hupp := hPU3 c2 cc2 par2 hc2cmd hc2ref hc2front
        omega
      · -- `c2` core ⟹ `c1` not in batch 0 (else batch-0 gen `≤ δ+1` can't reach `c2`'s `≥ 3δ+1`)
        rw [Nat.not_lt] at hc2front
        refine Or.inr ⟨?_, hc2front⟩
        by_contra hc1con
        rw [not_or, Nat.not_lt, Nat.not_le] at hc1con
        obtain ⟨_hc1a, hc1b⟩ := hc1con
        have hupp := hPB0 c1 cc1 par1 hc1cmd hc1ref (by omega)
        have hlow := hPL3 hbI c2 cc2 par2 hc2cmd hc2ref hc2front
        omega
    · -- `b ∉ I.barriers`: a barrier-`b` op of `Pfull` is in `Pre` or `E`, never in a batch
      have hloc : ∀ (η : ProgPoint) (cc : Cmd) (parr : ℕ+), Pfull.cmdAt η = some cc →
          Cmd.barrierRef cc = some (b, parr) →
          η.idx < (Pre.prog η.thread).length ∨
            (Pre.prog η.thread).length + (n + 1) * (A.prog η.thread).length ≤ η.idx := by
        intro η cc parr hcmd hbr
        by_contra hcon
        rw [not_or, Nat.not_lt, Nat.not_le] at hcon
        obtain ⟨hge, hlt⟩ := hcon
        have hcX := hcmdX η cc hge hcmd
        have hlen : ((A ^ (n + 1)).prog η.thread).length = (n + 1) * (A.prog η.thread).length :=
          CTA.pow_prog_length A (n + 1) η.thread
        have hcpow : (A ^ (n + 1)).cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩
            = some cc := by
          have hx : ((A ^ (n + 1)).prog η.thread ++ E.prog η.thread)[η.idx
              - (Pre.prog η.thread).length]? = some cc := hcX
          rwa [List.getElem?_append_left (by rw [hlen]; omega)] at hx
        exact absurd (mem_barriers_of_cmdAt_pow (k := I.loopK h) (m := n + 1) hcpow hbr) hbI
      by_cases hc2front : c2.idx < (Pre.prog c2.thread).length + 3 * (A.prog c2.thread).length
      · refine Or.inl ⟨?_, hc2front⟩
        have hc2pre : c2.idx < (Pre.prog c2.thread).length := by
          rcases hloc c2 cc2 par2 hc2cmd hc2ref with hh | hh
          · exact hh
          · exfalso
            have h2le : 3 * (A.prog c2.thread).length ≤ (n + 1) * (A.prog c2.thread).length :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        rcases hloc c1 cc1 par1 hc1cmd hc1ref with hh | hh
        · omega
        · exfalso
          have hg1 := hgXge1 c1 cc1 par1 hc1cmd hc1ref (by omega)
          have hg2 := hgPreLe c2 cc2 par2 hc2cmd hc2ref hc2pre
          omega
      · rw [Nat.not_lt] at hc2front
        refine Or.inr ⟨?_, hc2front⟩
        rcases hloc c1 cc1 par1 hc1cmd hc1ref with hh | hh
        · exact Or.inl hh
        · refine Or.inr ?_
          have : (A.prog c1.thread).length ≤ (n + 1) * (A.prog c1.thread).length :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
  rcases hcoloc with hfront | hcore
  · -- **Front case**: order the pair in the three-batch reference `ref = Pre ⨾ (A^3) ⨾ E_ref`,
    -- confine its chain to the front by soundness, and lift edge-by-edge via front agreement.
    obtain ⟨hc1f, hc2f⟩ := hfront
    obtain ⟨sdZ, hτZlast⟩ := hτZ.2
    have hpreZ :
        Pre.ids = ((A ^ (2 + 1)).seq E_ref ((CTA.pow_ids A (2 + 1)).trans hidsRef)).ids := by
      change Pre.ids = (A ^ (2 + 1)).ids; rw [CTA.pow_ids]; exact hpre
    set Z := (A ^ (2 + 1)).seq E_ref ((CTA.pow_ids A (2 + 1)).trans hidsRef) with hZdef
    set Pref := Pre.seq Z hpreZ with hPrefdef
    obtain ⟨hτref, -, -⟩ := glue_trace hpreZ htP htPL hτZ
    set τref := List.map (Config.seqLift Pre Z) tP.dropLast ++ τZ.tail with hτrefdef
    -- `Pref = loopProgram Pre A E_ref hpre hidsRef 3`, so `WS Pref` and `check Pref τref = true`
    have hPrefEq : CTA.loopProgram Pre A E_ref hpre hidsRef 3 = Pref := by
      apply CTA.ext
      · rfl
      · funext t
        change Pre.prog t ++ (A ^ 3).prog t ++ E_ref.prog t
          = Pre.prog t ++ ((A ^ (2 + 1)).prog t ++ E_ref.prog t)
        rw [List.append_assoc]
    rw [hPrefEq] at hPre3BatchRef
    have hcheckRef : (CheckWellSynchronized Pref τref).1 = true :=
      (checkWellSynchronized_correct_impl hτref).mpr hPre3BatchRef
    -- command agreement between `Pfull` and `Pref` on the front (`idx < Lp + 3L`)
    have hcmdfa : ∀ (η : ProgPoint), η.idx < (Pre.prog η.thread).length
        + 3 * (A.prog η.thread).length → Pfull.cmdAt η = Pref.cmdAt η := by
      intro η hη
      obtain ⟨t, idx⟩ := η; dsimp only at hη ⊢
      by_cases hpre : idx < (Pre.prog t).length
      · change (Pre.prog t ++ Xfull.prog t)[idx]? = (Pre.prog t ++ Z.prog t)[idx]?
        rw [List.getElem?_append_left hpre, List.getElem?_append_left hpre]
      · rw [Nat.not_lt] at hpre
        have hL0 : 0 < (A.prog t).length := by omega
        have he : idx - (Pre.prog t).length < 3 * (A.prog t).length := by omega
        have hmul21 : 3 * (A.prog t).length ≤ (n + 1) * (A.prog t).length :=
          Nat.mul_le_mul_right _ (by omega)
        have hjL : (idx - (Pre.prog t).length) % (A.prog t).length < (A.prog t).length :=
          Nat.mod_lt _ hL0
        have hp2 : (idx - (Pre.prog t).length) / (A.prog t).length < 3 := by
          rw [Nat.div_lt_iff_lt_mul hL0]; omega
        have hdec : idx - (Pre.prog t).length
            = (idx - (Pre.prog t).length) / (A.prog t).length * (A.prog t).length
              + (idx - (Pre.prog t).length) % (A.prog t).length := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
        have hXc : Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩
            = (A ^ (n + 1)).cmdAt ⟨t, idx - (Pre.prog t).length⟩ := by
          change ((A ^ (n + 1)).prog t ++ E.prog t)[idx - (Pre.prog t).length]?
            = ((A ^ (n + 1)).prog t)[idx - (Pre.prog t).length]?
          rw [List.getElem?_append_left (by rw [CTA.pow_prog_length]; omega)]
        have hZc : Z.cmdAt ⟨t, idx - (Pre.prog t).length⟩
            = (A ^ (2 + 1)).cmdAt ⟨t, idx - (Pre.prog t).length⟩ := by
          change ((A ^ (2 + 1)).prog t ++ E_ref.prog t)[idx - (Pre.prog t).length]?
            = ((A ^ (2 + 1)).prog t)[idx - (Pre.prog t).length]?
          rw [List.getElem?_append_left (by rw [CTA.pow_prog_length]; omega)]
        change (Pre.prog t ++ Xfull.prog t)[idx]? = (Pre.prog t ++ Z.prog t)[idx]?
        rw [List.getElem?_append_right hpre, List.getElem?_append_right hpre]
        change Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩ = Z.cmdAt ⟨t, idx - (Pre.prog t).length⟩
        rw [hXc, hZc, hdec,
          CTA.cmdAt_pow_batch_copy A hjL
            (show (idx - (Pre.prog t).length) / (A.prog t).length < n + 1 by omega),
          CTA.cmdAt_pow_batch_copy A hjL
            (show (idx - (Pre.prog t).length) / (A.prog t).length < 2 + 1 by omega)]
    -- front generation agreement (on barrier ops), via the `E`-independent closed form `rec+1+p·δ`
    have hfa : ∀ (η : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+), Pfull.cmdAt η = some cc →
        Cmd.barrierRef cc = some (bb, parr) →
        η.idx < (Pre.prog η.thread).length + 3 * (A.prog η.thread).length →
        pointGen Pfull τfull η = pointGen Pref τref η := by
      intro η cc bb parr hcmd hbr hη
      obtain ⟨t, idx⟩ := η; dsimp only at hcmd hη ⊢
      by_cases hpre : idx < (Pre.prog t).length
      · rw [seq_glue_prefix_pointGen hpreXf htP htPL hτX (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr,
          seq_glue_prefix_pointGen hpreZ htP htPL hτZ (hcmdPre ⟨t, idx⟩ cc hpre hcmd) hbr]
      · rw [Nat.not_lt] at hpre
        have hL0 : 0 < (A.prog t).length := by omega
        have he : idx - (Pre.prog t).length < 3 * (A.prog t).length := by omega
        have hmul21 : 3 * (A.prog t).length ≤ (n + 1) * (A.prog t).length :=
          Nat.mul_le_mul_right _ (by omega)
        have hjL : (idx - (Pre.prog t).length) % (A.prog t).length < (A.prog t).length :=
          Nat.mod_lt _ hL0
        have hp2 : (idx - (Pre.prog t).length) / (A.prog t).length < 3 := by
          rw [Nat.div_lt_iff_lt_mul hL0]; omega
        have hdec : idx - (Pre.prog t).length
            = (idx - (Pre.prog t).length) / (A.prog t).length * (A.prog t).length
              + (idx - (Pre.prog t).length) % (A.prog t).length := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
        have hXc : Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩ = some cc :=
          hcmdX ⟨t, idx⟩ cc hpre hcmd
        have hPrefcmd : Pref.cmdAt ⟨t, idx⟩ = some cc := by
          rw [← hcmdfa ⟨t, idx⟩ (by dsimp only; omega)]; exact hcmd
        have hZc : Z.cmdAt ⟨t, idx - (Pre.prog t).length⟩ = some cc := by
          have hx : (Pre.prog t ++ Z.prog t)[idx]? = some cc := hPrefcmd
          rwa [List.getElem?_append_right hpre] at hx
        have hbatch : (A.prog t)[(idx - (Pre.prog t).length) % (A.prog t).length]? = some cc := by
          have hcopy : (A ^ (n + 1)).cmdAt ⟨t, idx - (Pre.prog t).length⟩
              = (A.prog t)[(idx - (Pre.prog t).length) % (A.prog t).length]? := by
            conv_lhs => rw [hdec]
            exact CTA.cmdAt_pow_batch_copy A hjL (by omega)
          have hx : Xfull.cmdAt ⟨t, idx - (Pre.prog t).length⟩
              = (A ^ (n + 1)).cmdAt ⟨t, idx - (Pre.prog t).length⟩ := by
            change ((A ^ (n + 1)).prog t ++ E.prog t)[idx - (Pre.prog t).length]?
              = ((A ^ (n + 1)).prog t)[idx - (Pre.prog t).length]?
            rw [List.getElem?_append_left (by rw [CTA.pow_prog_length]; omega)]
          rw [hx, hcopy] at hXc; exact hXc
        obtain ⟨M₁, hM₁⟩ := exists_time_of_ends_done ht₁.1 ht₁L
          (η := ⟨t, (idx - (Pre.prog t).length) % (A.prog t).length⟩) hjL
        rw [show (⟨t, idx⟩ : ProgPoint)
            = ⟨t, (Pre.prog t).length + (idx - (Pre.prog t).length)⟩ from by congr 1; omega]
        rw [seq_glue_epilogue_pointGen hpreXf htP htPL hτX hXc hbr,
          seq_glue_epilogue_pointGen hpreZ htP htPL hτZ hZc hbr]
        congr 1
        -- Both `Pfull` and `Pref` carry the `E`-independent `rec+1+p·δ` for batch `p < 3`.  On the
        -- `Pfull` side `p < n` (n ≥ 3) uses `hfrontpreX`, `p = n` (n = 2) uses `hfrontepiX`; on the
        -- `Pref` side `p < 2` uses `hfrontpreZ`, `p = 2` uses `hfrontepiZ`.
        have hposX : pointGen Xfull τX ⟨t, idx - (Pre.prog t).length⟩
            = recycleCount bb t₁ (M₁ - 1) + 1
              + ((idx - (Pre.prog t).length) / (A.prog t).length)
                * (I.loopK h * I.arrivers bb / I.arrivalCount h bb) := by
          rw [show (⟨t, idx - (Pre.prog t).length⟩ : ProgPoint)
            = ⟨t, (idx - (Pre.prog t).length) / (A.prog t).length * (A.prog t).length
                + (idx - (Pre.prog t).length) % (A.prog t).length⟩ from by rw [← hdec]]
          rcases Nat.lt_or_ge ((idx - (Pre.prog t).length) / (A.prog t).length) n with hpn | hpn
          · exact hfrontpreX t ((idx - (Pre.prog t).length) % (A.prog t).length)
              ((idx - (Pre.prog t).length) / (A.prog t).length) cc bb parr M₁ hjL hpn hbatch hbr hM₁
          · have hpe : (idx - (Pre.prog t).length) / (A.prog t).length = n := by omega
            rw [hpe]
            exact hfrontepiX t ((idx - (Pre.prog t).length) % (A.prog t).length) cc bb parr M₁ hjL
              hbatch hbr hM₁
        have hposZ : pointGen Z τZ ⟨t, idx - (Pre.prog t).length⟩
            = recycleCount bb t₁ (M₁ - 1) + 1
              + ((idx - (Pre.prog t).length) / (A.prog t).length)
                * (I.loopK h * I.arrivers bb / I.arrivalCount h bb) := by
          rw [show (⟨t, idx - (Pre.prog t).length⟩ : ProgPoint)
            = ⟨t, (idx - (Pre.prog t).length) / (A.prog t).length * (A.prog t).length
                + (idx - (Pre.prog t).length) % (A.prog t).length⟩ from by rw [← hdec]]
          rcases Nat.lt_or_ge ((idx - (Pre.prog t).length) / (A.prog t).length) 2 with hp1 | hp1
          · exact hfrontpreZ t ((idx - (Pre.prog t).length) % (A.prog t).length)
              ((idx - (Pre.prog t).length) / (A.prog t).length) cc bb parr M₁ hjL hp1 hbatch hbr hM₁
          · have hpe : (idx - (Pre.prog t).length) / (A.prog t).length = 2 := by omega
            rw [hpe]
            exact hfrontepiZ t ((idx - (Pre.prog t).length) % (A.prog t).length) cc bb parr M₁ hjL
              hbatch hbr hM₁
        rw [hposX, hposZ]
    -- length facts for `Pfull`, `Pref`, and the `A := Pre ⨾ (A^3)` view of `ref`
    have hPfulllen : ∀ t, (Pfull.prog t).length
        = (Pre.prog t).length + (n + 1) * (A.prog t).length + (E.prog t).length := by
      intro t
      change (Pre.prog t ++ ((A ^ (n + 1)).prog t ++ E.prog t)).length = _
      rw [List.length_append, List.length_append, CTA.pow_prog_length]; omega
    have hfront_lt_full : ∀ (y : ProgPoint),
        y.idx < (Pre.prog y.thread).length + 3 * (A.prog y.thread).length →
        y.idx < (Pfull.prog y.thread).length := by
      intro y hy
      have h2 : 3 * (A.prog y.thread).length ≤ (n + 1) * (A.prog y.thread).length :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hPfulllen]; omega
    have hpre2 : Pre.ids = (A ^ 3).ids := by rw [CTA.pow_ids]; exact hpre
    have hids2' : (Pre.seq (A ^ 3) hpre2).ids = E_ref.ids := hpre.trans hidsRef
    have hAssoc : Pref = (Pre.seq (A ^ 3) hpre2).seq E_ref hids2' := by
      apply CTA.ext
      · rfl
      · funext t
        change Pre.prog t ++ ((A ^ (2 + 1)).prog t ++ E_ref.prog t)
          = Pre.prog t ++ (A ^ 3).prog t ++ E_ref.prog t
        rw [List.append_assoc]
    have hA'len : ∀ t, ((Pre.seq (A ^ 3) hpre2).prog t).length
        = (Pre.prog t).length + 3 * (A.prog t).length := by
      intro t
      change (Pre.prog t ++ (A ^ 3).prog t).length = _
      rw [List.length_append, CTA.pow_prog_length]
    have hPreflen : ∀ t, (Pref.prog t).length
        = (Pre.prog t).length + 3 * (A.prog t).length + (E_ref.prog t).length := by
      intro t
      change (Pre.prog t ++ ((A ^ (2 + 1)).prog t ++ E_ref.prog t)).length = _
      rw [List.length_append, List.length_append, CTA.pow_prog_length]; omega
    -- a predecessor of the front point `c3` is a valid program point of `Pref`
    have hppts : ∀ a, happensBefore Pref τref a ⟨c2.thread, c2.idx - 1⟩ → a ∈ Pref.progPoints := by
      intro a haR
      rcases haR.cases_head with heq | ⟨x, hedge, _⟩
      · rw [heq]
        refine (mem_progPoints_iff Pref ⟨c2.thread, c2.idx - 1⟩).mpr ⟨?_, ?_⟩
        · exact ((mem_progPoints_iff Pfull c2).mp hc2).1
        · dsimp only; rw [hPreflen]; have := hc2f; omega
      · exact (initRelation_cases hedge).1
    -- confinement: a predecessor of the front `c3` is front (soundness forbids `E_ref → front`)
    have hconf : ∀ a, happensBefore Pref τref a ⟨c2.thread, c2.idx - 1⟩ →
        a.idx < (Pre.prog a.thread).length + 3 * (A.prog a.thread).length := by
      intro a haR
      by_contra hcon
      rw [Nat.not_lt] at hcon
      have hapts := (mem_progPoints_iff Pref a).mp (hppts a haR)
      have haidx : a.idx < (Pre.prog a.thread).length + 3 * (A.prog a.thread).length
          + (E_ref.prog a.thread).length := by rw [← hPreflen]; exact hapts.2
      refine glue_no_happensBefore_B_to_A hids2' (hAssoc ▸ hPre3BatchRef) htAR htARlast
        (hAssoc ▸ hτref) ⟨a, ⟨c2.thread, c2.idx - 1⟩, hAssoc ▸ haR, ⟨?_, ?_⟩, ?_⟩
      · rw [hA'len]; exact hcon
      · rw [hA'len]; exact haidx
      · rw [hA'len]; have := hc2f; dsimp only; omega
    -- a front `initRelation Pref`-edge lifts to an `initRelation Pfull`-edge
    have hedgelift : ∀ x m, (x, m) ∈ initRelation Pref τref →
        x.idx < (Pre.prog x.thread).length + 3 * (A.prog x.thread).length →
        m.idx < (Pre.prog m.thread).length + 3 * (A.prog m.thread).length →
        (x, m) ∈ initRelation Pfull τfull := by
      intro x m hxm hxf hmf
      have hxpf : x ∈ Pfull.progPoints :=
        (mem_progPoints_iff Pfull x).mpr ⟨by
          have hxp : x ∈ Pref.progPoints := by
            rw [mem_initRelation_iff] at hxm
            rcases hxm with ⟨hh, _, _⟩ | ⟨_, _, hh, _⟩ | ⟨_, _, hh, _⟩ <;> exact hh
          rw [hPrefdef] at hxp; exact ((mem_progPoints_iff _ x).mp hxp).1, hfront_lt_full x hxf⟩
      have hmpf : m ∈ Pfull.progPoints :=
        (mem_progPoints_iff Pfull m).mpr ⟨by
          have hmp : m ∈ Pref.progPoints := by
            rw [mem_initRelation_iff] at hxm
            rcases hxm with ⟨hh, hlt, hbeq⟩ | ⟨_, _, _, hh, _⟩ | ⟨_, _, _, hh, _⟩
            · rw [hbeq]
              exact (mem_progPoints_iff Pref _).mpr
                ⟨((mem_progPoints_iff Pref x).mp hh).1, by omega⟩
            · exact hh
            · exact hh
          rw [hPrefdef] at hmp; exact ((mem_progPoints_iff _ m).mp hmp).1, hfront_lt_full m hmf⟩
      rw [mem_initRelation_iff] at hxm ⊢
      rcases hxm with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, mm, hxpts, hmpts, hca, hcb, hg⟩
          | ⟨bb, mm, hxpts, hmpts, hca, hcb, hg⟩
      · refine Or.inl ⟨hxpf, ?_, hbeq⟩
        have hm := hfront_lt_full m hmf
        rw [hbeq] at hm; exact hm
      · refine Or.inr (Or.inl ⟨bb, mm, hxpf, hmpf, ?_, ?_, ?_⟩)
        · rw [hcmdfa x hxf]; exact hca
        · rw [hcmdfa m hmf]; exact hcb
        · rw [hfa x (Cmd.arrive bb mm) bb mm (by rw [hcmdfa x hxf]; exact hca) rfl hxf,
            hfa m (Cmd.sync bb mm) bb mm (by rw [hcmdfa m hmf]; exact hcb) rfl hmf]; exact hg
      · refine Or.inr (Or.inr ⟨bb, mm, hxpf, hmpf, ?_, ?_, ?_⟩)
        · rw [hcmdfa x hxf]; exact hca
        · rw [hcmdfa m hmf]; exact hcb
        · rw [hfa x (Cmd.sync bb mm) bb mm (by rw [hcmdfa x hxf]; exact hca) rfl hxf,
            hfa m (Cmd.sync bb mm) bb mm (by rw [hcmdfa m hmf]; exact hcb) rfl hmf]; exact hg
    -- lift the whole `Pref`-chain to `Pfull` (each chain point is front by `hconf`)
    have hlift : ∀ a, happensBefore Pref τref a ⟨c2.thread, c2.idx - 1⟩ →
        happensBefore Pfull τfull a ⟨c2.thread, c2.idx - 1⟩ := by
      intro a haR
      induction haR using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head x m hedge hrest ih =>
        have hxf := hconf x (Relation.ReflTransGen.head hedge hrest)
        have hmf := hconf m hrest
        exact Relation.ReflTransGen.head (hedgelift x m hedge hxf hmf) ih
    -- order `(c1, c2)` in `Pref` (a flagged pair there by command/gen agreement), then lift
    have hc1cmdR : Pref.cmdAt c1 = some cc1 := by rw [← hcmdfa c1 hc1f]; exact hc1cmd
    have hbar1R : (Pref.cmdAt c1).bind Cmd.barrier? = some b := by
      rw [hc1cmdR]; exact Cmd.barrier?_of_barrierRef hc1ref
    have hc2cmdR : Pref.cmdAt c2 = some cc2 := by rw [← hcmdfa c2 hc2f]; exact hc2cmd
    have hbar2R : (Pref.cmdAt c2).bind Cmd.barrier? = some b := by
      rw [← hcmdfa c2 hc2f]; exact hbar2
    have hgenR : pointGen Pref τref c2 = pointGen Pref τref c1 + 1 := by
      rw [← hfa c1 cc1 b par1 hc1cmd hc1ref hc1f, ← hfa c2 cc2 b par2 hc2cmd hc2ref hc2f]
      exact hgen
    have hHBp := hlift c1 (happensBefore_of_check hcheckRef
      (mem_progPoints_of_cmdAt _ hc1cmdR) hbar1R (mem_progPoints_of_cmdAt _ hc2cmdR) hbar2R
      hgenR hidx)
    rw [happensBefore, Relation.reflTransGen_iff_eq_or_transGen] at hHBp
    rcases hHBp with heq | htg
    · exact absurd heq.symm hc1ne3
    · exact mem_transClosure_of_transGen _ hc1ne3 htg
  · -- **Core case**: shift down one batch, order via `hprev`, and lift through the loop+epilogue
    -- region (`back` strips `Pre`, the bundle's `hmonoX` shifts by `L`, `forward` re-adds `Pre`).
    obtain ⟨hc1core, hc2core⟩ := hcore
    have hpreXn : Pre.ids = (((A ^ n).seq E ((CTA.pow_ids A n).trans hids))).ids := by
      change Pre.ids = (A ^ n).ids; rw [CTA.pow_ids]; exact hpre
    set Xpref := (A ^ n).seq E ((CTA.pow_ids A n).trans hids) with hXprefdef
    set Ppref := Pre.seq Xpref hpreXn with hPprefdef
    obtain ⟨hτpref, -, -⟩ := glue_trace hpreXn htP htPL hτnX
    set τpref := List.map (Config.seqLift Pre Xpref) tP.dropLast ++ τnX.tail with hτprefdef
    have hPprefEq : CTA.loopProgram Pre A E hpre hids n = Ppref := by
      apply CTA.ext
      · rfl
      · funext t
        change Pre.prog t ++ (A ^ n).prog t ++ E.prog t
          = Pre.prog t ++ ((A ^ n).prog t ++ E.prog t)
        rw [List.append_assoc]
    rw [hPprefEq] at hprev
    have hcheckPref : (CheckWellSynchronized Ppref τpref).1 = true :=
      (checkWellSynchronized_correct_impl hτpref).mpr hprev
    obtain ⟨sdX, hτXlast⟩ := hτX.2
    obtain ⟨sdnX, hτnXlast⟩ := hτnX.2
    -- generation of an `Xfull`/`Xpref`-region point across the `Pre` glue (Step 0)
    have hgXf : ∀ (t : ThreadId) (e : Nat) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
        Xfull.cmdAt ⟨t, e⟩ = some cc → Cmd.barrierRef cc = some (bb, parr) →
        pointGen Pfull τfull ⟨t, (Pre.prog t).length + e⟩
          = recycleCount bb tP (tP.length - 2) + pointGen Xfull τX ⟨t, e⟩ :=
      fun t e cc bb parr hcE hbr => seq_glue_epilogue_pointGen hpreXf htP htPL hτX hcE hbr
    have hgXp : ∀ (t : ThreadId) (e : Nat) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
        Xpref.cmdAt ⟨t, e⟩ = some cc → Cmd.barrierRef cc = some (bb, parr) →
        pointGen Ppref τpref ⟨t, (Pre.prog t).length + e⟩
          = recycleCount bb tP (tP.length - 2) + pointGen Xpref τnX ⟨t, e⟩ :=
      fun t e cc bb parr hcE hbr => seq_glue_epilogue_pointGen hpreXn htP htPL hτnX hcE hbr
    -- command transfer (X-region) for `Pfull` and `Ppref`
    have hcmdXf : ∀ (η : ProgPoint) (cc : Cmd), (Pre.prog η.thread).length ≤ η.idx →
        Pfull.cmdAt η = some cc →
        Xfull.cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ = some cc := by
      intro η cc hle hcmd
      have : (Pre.prog η.thread ++ Xfull.prog η.thread)[η.idx]? = some cc := hcmd
      rwa [List.getElem?_append_right hle] at this
    have hcmdXp : ∀ (η : ProgPoint) (cc : Cmd), (Pre.prog η.thread).length ≤ η.idx →
        Ppref.cmdAt η = some cc →
        Xpref.cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ = some cc := by
      intro η cc hle hcmd
      have : (Pre.prog η.thread ++ Xpref.prog η.thread)[η.idx]? = some cc := hcmd
      rwa [List.getElem?_append_right hle] at this
    -- **forward**: a `happensBefore Xfull`-pair lifts to `Pfull` by `+Lp` (the `Pre` glue)
    have hforward : ∀ a d, happensBefore Xfull τX a d →
        happensBefore Pfull τfull ⟨a.thread, a.idx + (Pre.prog a.thread).length⟩
          ⟨d.thread, d.idx + (Pre.prog d.thread).length⟩ := by
      intro a d hR
      refine Relation.ReflTransGen.lift
        (fun p => (⟨p.thread, p.idx + (Pre.prog p.thread).length⟩ : ProgPoint))
        (fun x y hxy => ?_) hR
      rw [mem_initRelation_iff] at hxy ⊢
      have hcmdup : ∀ (p : ProgPoint), Pfull.cmdAt ⟨p.thread, p.idx + (Pre.prog p.thread).length⟩
          = Xfull.cmdAt p := by
        intro p
        change (Pre.prog p.thread ++ Xfull.prog p.thread)[p.idx + (Pre.prog p.thread).length]?
          = (Xfull.prog p.thread)[p.idx]?
        rw [List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
      have hmemup : ∀ (p : ProgPoint), p ∈ Xfull.progPoints →
          (⟨p.thread, p.idx + (Pre.prog p.thread).length⟩ : ProgPoint) ∈ Pfull.progPoints := by
        intro p hp
        refine (mem_progPoints_iff Pfull _).mpr
          ⟨hpreXf.symm ▸ ((mem_progPoints_iff Xfull p).mp hp).1, ?_⟩
        change p.idx + (Pre.prog p.thread).length
          < (Pre.prog p.thread ++ Xfull.prog p.thread).length
        rw [List.length_append]; have := ((mem_progPoints_iff Xfull p).mp hp).2; omega
      have hgenup : ∀ (p : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
          Xfull.cmdAt p = some cc → Cmd.barrierRef cc = some (bb, parr) →
          pointGen Pfull τfull ⟨p.thread, p.idx + (Pre.prog p.thread).length⟩
            = recycleCount bb tP (tP.length - 2) + pointGen Xfull τX p := by
        intro p cc bb parr hcp hbr
        obtain ⟨pt, pidx⟩ := p
        rw [show pidx + (Pre.prog pt).length = (Pre.prog pt).length + pidx from Nat.add_comm _ _]
        exact hgXf pt pidx cc bb parr hcp hbr
      rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
          | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
      · subst hbeq
        refine Or.inl ⟨hmemup x hxpts, ?_, by simp only [ProgPoint.mk.injEq, true_and]; omega⟩
        change x.idx + (Pre.prog x.thread).length + 1
          < (Pre.prog x.thread ++ Xfull.prog x.thread).length
        rw [List.length_append]; omega
      · refine Or.inr (Or.inl ⟨bb, mm, hmemup x hxpts, hmemup y hypts,
          by rw [hcmdup]; exact hca, by rw [hcmdup]; exact hcb, ?_⟩)
        rw [hgenup x (Cmd.arrive bb mm) bb mm hca rfl, hgenup y (Cmd.sync bb mm) bb mm hcb rfl, hg]
      · refine Or.inr (Or.inr ⟨bb, mm, hmemup x hxpts, hmemup y hypts,
          by rw [hcmdup]; exact hca, by rw [hcmdup]; exact hcb, ?_⟩)
        rw [hgenup x (Cmd.sync bb mm) bb mm hca rfl, hgenup y (Cmd.sync bb mm) bb mm hcb rfl, hg]
    -- `Xfull = A ⨾ Xpref` (one batch prepended), used for the X-region command/gen shift
    have hXfullsplit : ∀ t, Xfull.prog t = A.prog t ++ Xpref.prog t := by
      intro t
      change (A ^ (n + 1)).prog t ++ E.prog t = A.prog t ++ ((A ^ n).prog t ++ E.prog t)
      rw [CTA.pow_succ_prog, List.append_assoc]
    -- generation of a `Ppref` X-region barrier point across the `Pre` glue
    have hgenXp : ∀ (p : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
        (Pre.prog p.thread).length ≤ p.idx → Ppref.cmdAt p = some cc →
        Cmd.barrierRef cc = some (bb, parr) →
        pointGen Ppref τpref p = recycleCount bb tP (tP.length - 2)
          + pointGen Xpref τnX ⟨p.thread, p.idx - (Pre.prog p.thread).length⟩ := by
      intro p cc bb parr hle hcmd hbr
      have hg := hgXp p.thread (p.idx - (Pre.prog p.thread).length) cc bb parr
        (hcmdXp p cc hle hcmd) hbr
      rwa [show (Pre.prog p.thread).length + (p.idx - (Pre.prog p.thread).length) = p.idx from by
        omega] at hg
    -- **back** (per-edge): an `initRelation Ppref`-edge with an X-region source stays X-region
    -- and strips `Pre` (the target is a `sync`, whose generation `≤ R` can't match the source's
    -- `≥ R + 1`, so no edge leaves the loop+epilogue region)
    have hLx : ∀ (p : ProgPoint), (Pre.prog p.thread).length ≤ p.idx → p ∈ Ppref.progPoints →
        p.idx - (Pre.prog p.thread).length < (Xpref.prog p.thread).length := by
      intro p hle hp
      have hlt := ((mem_progPoints_iff Ppref p).mp hp).2
      have hPL : (Ppref.prog p.thread).length
          = (Pre.prog p.thread).length + (Xpref.prog p.thread).length := by
        change (Pre.prog p.thread ++ Xpref.prog p.thread).length = _; rw [List.length_append]
      omega
    have mkXpts : ∀ (p : ProgPoint), (Pre.prog p.thread).length ≤ p.idx → p ∈ Ppref.progPoints →
        (⟨p.thread, p.idx - (Pre.prog p.thread).length⟩ : ProgPoint) ∈ Xpref.progPoints := by
      intro p hle hp
      exact (mem_progPoints_iff Xpref _).mpr
        ⟨hpreXn ▸ ((mem_progPoints_iff Ppref p).mp hp).1, hLx p hle hp⟩
    have hbackedge : ∀ x y, (x, y) ∈ initRelation Ppref τpref → (Pre.prog x.thread).length ≤ x.idx →
        (Pre.prog y.thread).length ≤ y.idx ∧
          (⟨x.thread, x.idx - (Pre.prog x.thread).length⟩,
            ⟨y.thread, y.idx - (Pre.prog y.thread).length⟩) ∈ initRelation Xpref τnX := by
      intro x y hxy hxX
      rw [mem_initRelation_iff] at hxy
      rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
          | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
      · subst hbeq
        refine ⟨by dsimp only; omega, ?_⟩
        rw [mem_initRelation_iff]
        refine Or.inl ⟨mkXpts x hxX hxpts, ?_, by simp only [ProgPoint.mk.injEq, true_and]; omega⟩
        dsimp only
        have hPL : (Ppref.prog x.thread).length
            = (Pre.prog x.thread).length + (Xpref.prog x.thread).length := by
          change (Pre.prog x.thread ++ Xpref.prog x.thread).length = _; rw [List.length_append]
        omega
      · have hyX : (Pre.prog y.thread).length ≤ y.idx := by
          by_contra hyPre; rw [Nat.not_le] at hyPre
          have hcby : Pre.cmdAt y = some (Cmd.sync bb mm) := by
            have hh : (Pre.prog y.thread ++ Xpref.prog y.thread)[y.idx]?
                = some (Cmd.sync bb mm) := hcb
            rwa [List.getElem?_append_left hyPre] at hh
          have hgy : pointGen Ppref τpref y ≤ recycleCount bb tP (tP.length - 2) := by
            rw [seq_glue_prefix_pointGen hpreXn htP htPL hτnX hcby rfl]
            exact sync_gen_le_total htP htPL hcby
          have hgx := hgenXp x (Cmd.arrive bb mm) bb mm hxX hca rfl
          have h1le := one_le_pointGen_barrierOp hτnX hτnXlast (hcmdXp x _ hxX hca) rfl
          omega
        refine ⟨hyX, ?_⟩
        rw [mem_initRelation_iff]
        refine Or.inr (Or.inl ⟨bb, mm, mkXpts x hxX hxpts,
          mkXpts y hyX hypts, hcmdXp x _ hxX hca, hcmdXp y _ hyX hcb, ?_⟩)
        have hgx := hgenXp x (Cmd.arrive bb mm) bb mm hxX hca rfl
        have hgy := hgenXp y (Cmd.sync bb mm) bb mm hyX hcb rfl
        omega
      · have hyX : (Pre.prog y.thread).length ≤ y.idx := by
          by_contra hyPre; rw [Nat.not_le] at hyPre
          have hcby : Pre.cmdAt y = some (Cmd.sync bb mm) := by
            have hh : (Pre.prog y.thread ++ Xpref.prog y.thread)[y.idx]?
                = some (Cmd.sync bb mm) := hcb
            rwa [List.getElem?_append_left hyPre] at hh
          have hgy : pointGen Ppref τpref y ≤ recycleCount bb tP (tP.length - 2) := by
            rw [seq_glue_prefix_pointGen hpreXn htP htPL hτnX hcby rfl]
            exact sync_gen_le_total htP htPL hcby
          have hgx := hgenXp x (Cmd.sync bb mm) bb mm hxX hca rfl
          have h1le := one_le_pointGen_barrierOp hτnX hτnXlast (hcmdXp x _ hxX hca) rfl
          omega
        refine ⟨hyX, ?_⟩
        rw [mem_initRelation_iff]
        refine Or.inr (Or.inr ⟨bb, mm, mkXpts x hxX hxpts,
          mkXpts y hyX hypts, hcmdXp x _ hxX hca, hcmdXp y _ hyX hcb, ?_⟩)
        have hgx := hgenXp x (Cmd.sync bb mm) bb mm hxX hca rfl
        have hgy := hgenXp y (Cmd.sync bb mm) bb mm hyX hcb rfl
        omega
    -- **back** (chain)
    have hback : ∀ a d, happensBefore Ppref τpref a d → (Pre.prog a.thread).length ≤ a.idx →
        (Pre.prog d.thread).length ≤ d.idx ∧
          happensBefore Xpref τnX ⟨a.thread, a.idx - (Pre.prog a.thread).length⟩
            ⟨d.thread, d.idx - (Pre.prog d.thread).length⟩ := by
      intro a d hR ha
      induction hR with
      | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
      | tail _hrest hedge ih =>
        obtain ⟨hmX, hrestX⟩ := ih
        obtain ⟨hdX, hedgeX⟩ := hbackedge _ _ hedge hmX
        exact ⟨hdX, hrestX.tail hedgeX⟩
    -- remove-batch command/generation transfer (`Pfull` ↔ `Ppref`, off the inserted first batch)
    have hcmdrm : ∀ (p : ProgPoint) (cc : Cmd),
        (Pre.prog p.thread).length + (A.prog p.thread).length ≤ p.idx → Pfull.cmdAt p = some cc →
        Ppref.cmdAt ⟨p.thread, p.idx - (A.prog p.thread).length⟩ = some cc := by
      intro p cc hge hcmd
      change (Pre.prog p.thread ++ Xpref.prog p.thread)[p.idx - (A.prog p.thread).length]? = some cc
      rw [List.getElem?_append_right (by omega)]
      have hpf : (Pre.prog p.thread ++ Xfull.prog p.thread)[p.idx]? = some cc := hcmd
      rw [List.getElem?_append_right (by omega), hXfullsplit,
        List.getElem?_append_right (by omega)] at hpf
      rw [show p.idx - (A.prog p.thread).length - (Pre.prog p.thread).length
        = p.idx - (Pre.prog p.thread).length - (A.prog p.thread).length from by omega]
      exact hpf
    have hgenrm : ∀ (p : ProgPoint) (cc : Cmd) (parr : ℕ+),
        (Pre.prog p.thread).length + (A.prog p.thread).length ≤ p.idx → Pfull.cmdAt p = some cc →
        Cmd.barrierRef cc = some (b, parr) →
        pointGen Pfull τfull p
          = pointGen Ppref τpref ⟨p.thread, p.idx - (A.prog p.thread).length⟩ + δ := by
      intro p cc parr hge hcmd hbr
      have hxf := hgXf p.thread (p.idx - (Pre.prog p.thread).length) cc b parr
        (hcmdXf p cc (by omega) hcmd) hbr
      rw [show (Pre.prog p.thread).length + (p.idx - (Pre.prog p.thread).length) = p.idx from by
        omega] at hxf
      have hcmdrmp := hcmdrm p cc hge hcmd
      have hxp := hgenXp ⟨p.thread, p.idx - (A.prog p.thread).length⟩ cc b parr
        (by dsimp only; omega)
        hcmdrmp hbr
      dsimp only at hxp
      have hcXpref : Xpref.cmdAt ⟨p.thread,
          p.idx - (A.prog p.thread).length - (Pre.prog p.thread).length⟩ = some cc :=
        hcmdXp ⟨p.thread, p.idx - (A.prog p.thread).length⟩ cc (by dsimp only; omega) hcmdrmp
      have hshift := hshiftX ⟨p.thread,
          p.idx - (A.prog p.thread).length - (Pre.prog p.thread).length⟩ cc b parr hcXpref hbr
      dsimp only at hshift
      rw [show p.idx - (A.prog p.thread).length - (Pre.prog p.thread).length
            + (A.prog p.thread).length = p.idx - (Pre.prog p.thread).length from by omega] at hshift
      rw [hxf, hxp, hshift]; omega
    by_cases hc1pre : c1.idx < (Pre.prog c1.thread).length
    · -- **Mixed sub-case** (`c1` in `Pre`).  First `b ∉ I.barriers` (so `δ = 0`); then order the
      -- down-shifted pair in `Ppref` and lift the chain by `ψ` (identity on `Pre`, `+L` on the
      -- loop+epilogue), handling the single `Pre`→loop crossing edge specially.
      -- `c1` is a barrier op on `b` in `Pre`; its generation is its standalone `Pre` generation.
      have hc1Pre : Pre.cmdAt c1 = some cc1 := hcmdPre c1 _ hc1pre hc1cmd
      have hc1gen : pointGen Pfull τfull c1 = pointGen Pre tP c1 :=
        seq_glue_prefix_pointGen hpreXf htP htPL hτX hc1Pre hc1ref
      have hc1le : pointGen Pfull τfull c1 ≤ R + 1 := by
        rw [hc1gen, hR]; exact barrierOp_gen_le_total htP htPL hc1Pre hc1ref
      -- **`b ∉ I.barriers`** (else `c2`'s `≥ R+3δ+1` generation clashes with `c1`'s `≤ R+1`).
      have hbni : b ∉ I.barriers := by
        intro hbI
        have hlow := hPL3 hbI c2 cc2 par2 hc2cmd hc2ref hc2core
        have hδ1 : 1 ≤ δ := by rw [hδ]; exact one_le_delta h rfl hbI
        omega
      -- **`δ = 0`** for `b` (no arrives on `b` in `I`).
      have hδ0 : δ = 0 := by
        have harr0 : I.arrivers b = 0 := by
          rw [CTA.arrivers]
          apply Finset.sum_eq_zero
          intro i hi
          rw [List.countP_eq_zero]
          intro r hr hrb
          exact hbni (by
            rw [CTA.barriers, Finset.mem_biUnion]
            exact ⟨i, hi, List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, eq_of_beq hrb⟩)⟩)
        rw [hδ, harr0, Nat.mul_zero, Nat.zero_div]
      -- length facts
      have hPfulllen : ∀ t, (Pfull.prog t).length
          = (Pre.prog t).length + (n + 1) * (A.prog t).length + (E.prog t).length := by
        intro t
        change (Pre.prog t ++ ((A ^ (n + 1)).prog t ++ E.prog t)).length = _
        rw [List.length_append, List.length_append, CTA.pow_prog_length]; omega
      have hPpreflen : ∀ t, (Ppref.prog t).length
          = (Pre.prog t).length + n * (A.prog t).length + (E.prog t).length := by
        intro t
        change (Pre.prog t ++ ((A ^ n).prog t ++ E.prog t)).length = _
        rw [List.length_append, List.length_append, CTA.pow_prog_length]; omega
      -- `Ppref`↔`Pre` command restriction
      have hPreOfPpref : ∀ (η : ProgPoint) (cc : Cmd), η.idx < (Pre.prog η.thread).length →
          Ppref.cmdAt η = some cc → Pre.cmdAt η = some cc := by
        intro η cc hlt hcmd
        have : (Pre.prog η.thread ++ Xpref.prog η.thread)[η.idx]? = some cc := hcmd
        rwa [List.getElem?_append_left hlt] at this
      -- `Pfull`/`Ppref` agree on commands in the `Pre` region
      have hcmdPrePref : ∀ (η : ProgPoint), η.idx < (Pre.prog η.thread).length →
          Ppref.cmdAt η = Pfull.cmdAt η := by
        intro η hlt
        obtain ⟨t, idx⟩ := η; dsimp only at hlt ⊢
        change (Pre.prog t ++ Xpref.prog t)[idx]? = (Pre.prog t ++ Xfull.prog t)[idx]?
        rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      -- `Pfull`/`Ppref` agree on generations of `Pre`-region barrier ops
      have hgenPre : ∀ (η : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
          η.idx < (Pre.prog η.thread).length → Pre.cmdAt η = some cc →
          Cmd.barrierRef cc = some (bb, parr) →
          pointGen Pfull τfull η = pointGen Ppref τpref η := by
        intro η cc bb parr hlt hcmd hbr
        rw [seq_glue_prefix_pointGen hpreXf htP htPL hτX hcmd hbr,
          seq_glue_prefix_pointGen hpreXn htP htPL hτnX hcmd hbr]
      -- `Pfull`/`Ppref` agree on commands in the first `n` batches
      have hcmdLoopPref : ∀ (η : ProgPoint),
          η.idx < (Pre.prog η.thread).length + n * (A.prog η.thread).length →
          (Pre.prog η.thread).length ≤ η.idx → Ppref.cmdAt η = Pfull.cmdAt η := by
        intro η hlt hle
        obtain ⟨ηt, ηi⟩ := η; dsimp only at hlt hle ⊢
        have hLpos : 0 < (A.prog ηt).length := by
          rcases Nat.eq_zero_or_pos (A.prog ηt).length with h0 | h0
          · rw [h0, Nat.mul_zero] at hlt; omega
          · exact h0
        change (Pre.prog ηt ++ Xpref.prog ηt)[ηi]? = (Pre.prog ηt ++ Xfull.prog ηt)[ηi]?
        rw [List.getElem?_append_right hle, List.getElem?_append_right hle]
        set e := ηi - (Pre.prog ηt).length with hedef
        have heLt : e < n * (A.prog ηt).length := by omega
        set p := e / (A.prog ηt).length with hpdef
        set j := e % (A.prog ηt).length with hjdef
        have hjL : j < (A.prog ηt).length := Nat.mod_lt _ hLpos
        have hpn : p < n := by rw [hpdef, Nat.div_lt_iff_lt_mul hLpos]; omega
        have hedecomp : e = p * (A.prog ηt).length + j := by
          rw [hpdef, hjdef, Nat.mul_comm]; exact (Nat.div_add_mod e _).symm
        have hXp : (Xpref.prog ηt)[e]? = (A.prog ηt)[j]? := by
          have h1 : (Xpref.prog ηt)[e]? = ((A ^ n).prog ηt)[e]? := by
            change ((A ^ n).prog ηt ++ E.prog ηt)[e]? = _
            rw [List.getElem?_append_left (by rw [CTA.pow_prog_length]; exact heLt)]
          rw [h1, hedecomp]; exact CTA.cmdAt_pow_batch_copy A hjL hpn
        have hXf : (Xfull.prog ηt)[e]? = (A.prog ηt)[j]? := by
          have h1 : (Xfull.prog ηt)[e]? = ((A ^ (n + 1)).prog ηt)[e]? := by
            change ((A ^ (n + 1)).prog ηt ++ E.prog ηt)[e]? = _
            rw [List.getElem?_append_left (by
              rw [CTA.pow_prog_length]
              calc e < n * (A.prog ηt).length := heLt
                _ ≤ (n + 1) * (A.prog ηt).length := Nat.mul_le_mul_right _ (by omega))]
          rw [h1, hedecomp]; exact CTA.cmdAt_pow_batch_copy A hjL (by omega)
        rw [hXp, hXf]
      -- `Pfull`/`Ppref` agree on generations of first-`n`-batch barrier ops
      have hloopgen : ∀ (η : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
          (Pre.prog η.thread).length ≤ η.idx →
          η.idx < (Pre.prog η.thread).length + n * (A.prog η.thread).length →
          Pfull.cmdAt η = some cc → Cmd.barrierRef cc = some (bb, parr) →
          pointGen Pfull τfull η = pointGen Ppref τpref η := by
        intro η cc bb parr hle hlt hcmd hbr
        obtain ⟨ηt, ηi⟩ := η; dsimp only at hle hlt hcmd ⊢
        have hcXf : Xfull.cmdAt ⟨ηt, ηi - (Pre.prog ηt).length⟩ = some cc :=
          hcmdXf ⟨ηt, ηi⟩ cc hle hcmd
        have hcmdP : Ppref.cmdAt ⟨ηt, ηi⟩ = some cc := by
          rw [hcmdLoopPref ⟨ηt, ηi⟩ hlt hle]; exact hcmd
        have hLg := hgXf ηt (ηi - (Pre.prog ηt).length) cc bb parr hcXf hbr
        rw [show (Pre.prog ηt).length + (ηi - (Pre.prog ηt).length) = ηi from by omega] at hLg
        have hRg := hgenXp ⟨ηt, ηi⟩ cc bb parr hle hcmdP hbr
        have hag := hfcNX ηt (ηi - (Pre.prog ηt).length) cc bb parr (by rw [← hA]; omega) hcXf hbr
        rw [hLg, hRg, hag]
      -- command of an `E`-region point shifts by `+L`
      have hcmdEshift : ∀ (η : ProgPoint) (cc : Cmd), (Pre.prog η.thread).length ≤ η.idx →
          Ppref.cmdAt η = some cc →
          Pfull.cmdAt ⟨η.thread, η.idx + (A.prog η.thread).length⟩ = some cc := by
        intro η cc hle hcmd
        have hcXp : Xpref.cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ = some cc :=
          hcmdXp η cc hle hcmd
        change (Pre.prog η.thread ++ Xfull.prog η.thread)[η.idx + (A.prog η.thread).length]?
          = some cc
        rw [List.getElem?_append_right (by omega), hXfullsplit,
          List.getElem?_append_right (by omega),
          show η.idx + (A.prog η.thread).length - (Pre.prog η.thread).length
              - (A.prog η.thread).length = η.idx - (Pre.prog η.thread).length from by omega]
        exact hcXp
      -- generation of an `E`-region point shifts by `+δ_bb`
      have hgenEshift : ∀ (η : ProgPoint) (cc : Cmd) (bb : Barrier) (parr : ℕ+),
          (Pre.prog η.thread).length ≤ η.idx → Ppref.cmdAt η = some cc →
          Cmd.barrierRef cc = some (bb, parr) →
          pointGen Pfull τfull ⟨η.thread, η.idx + (A.prog η.thread).length⟩
            = pointGen Ppref τpref η + (I.loopK h * I.arrivers bb / I.arrivalCount h bb) := by
        intro η cc bb parr hle hcmd hbr
        have hcXp : Xpref.cmdAt ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ = some cc :=
          hcmdXp η cc hle hcmd
        have hcXf : Xfull.cmdAt ⟨η.thread, (η.idx - (Pre.prog η.thread).length)
            + (A.prog η.thread).length⟩ = some cc := by
          change (Xfull.prog η.thread)[(η.idx - (Pre.prog η.thread).length)
            + (A.prog η.thread).length]? = some cc
          rw [hXfullsplit, List.getElem?_append_right (by omega),
            show η.idx - (Pre.prog η.thread).length + (A.prog η.thread).length
                - (A.prog η.thread).length = η.idx - (Pre.prog η.thread).length from by omega]
          exact hcXp
        have hshift := hshiftX ⟨η.thread, η.idx - (Pre.prog η.thread).length⟩ cc bb parr hcXp hbr
        rw [← hA] at hshift
        have hLg := hgXf η.thread ((η.idx - (Pre.prog η.thread).length) + (A.prog η.thread).length)
          cc bb parr hcXf hbr
        rw [show (Pre.prog η.thread).length + ((η.idx - (Pre.prog η.thread).length)
            + (A.prog η.thread).length) = η.idx + (A.prog η.thread).length from by omega] at hLg
        have hRg := hgenXp η cc bb parr hle hcmd hbr
        rw [hLg, hshift, hRg]; omega
      -- a `Pre`-region program point of `Ppref` is one of `Pfull`
      have hPrePf : ∀ (η : ProgPoint), η ∈ Ppref.progPoints →
          η.idx < (Pre.prog η.thread).length → η ∈ Pfull.progPoints := by
        intro η hpp hlt
        refine (mem_progPoints_iff Pfull η).mpr ⟨((mem_progPoints_iff Ppref η).mp hpp).1, ?_⟩
        rw [hPfulllen]; omega
      -- **Pre→Pre edge lift** (`ψ` is the identity on `Pre`)
      have hPrePreEdge : ∀ (x y : ProgPoint), (x, y) ∈ initRelation Ppref τpref →
          x.idx < (Pre.prog x.thread).length → y.idx < (Pre.prog y.thread).length →
          happensBefore Pfull τfull x y := by
        intro x y hxy hx hy
        apply Relation.ReflTransGen.single
        rw [mem_initRelation_iff] at hxy ⊢
        rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
            | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
        · refine Or.inl ⟨hPrePf x hxpts hx, ?_, hbeq⟩
          rw [hbeq] at hy; dsimp only at hy; rw [hPfulllen]; omega
        · refine Or.inr (Or.inl ⟨bb, mm, hPrePf x hxpts hx, hPrePf y hypts hy, ?_, ?_, ?_⟩)
          · rw [← hcmdPrePref x hx]; exact hca
          · rw [← hcmdPrePref y hy]; exact hcb
          · rw [hgenPre x (Cmd.arrive bb mm) bb mm hx (hPreOfPpref x _ hx hca) rfl,
              hgenPre y (Cmd.sync bb mm) bb mm hy (hPreOfPpref y _ hy hcb) rfl]; exact hg
        · refine Or.inr (Or.inr ⟨bb, mm, hPrePf x hxpts hx, hPrePf y hypts hy, ?_, ?_, ?_⟩)
          · rw [← hcmdPrePref x hx]; exact hca
          · rw [← hcmdPrePref y hy]; exact hcb
          · rw [hgenPre x (Cmd.sync bb mm) bb mm hx (hPreOfPpref x _ hx hca) rfl,
              hgenPre y (Cmd.sync bb mm) bb mm hy (hPreOfPpref y _ hy hcb) rfl]; exact hg
      -- **crossing barrier edge lift** (`x` in `Pre`, `y` in the loop+epilogue): `ψ` sends the edge
      -- to a `Pfull` happens-before from `x` to `y + L`.
      have hcrossbar : ∀ (x y : ProgPoint) (cx : Cmd) (bb : Barrier) (mm : ℕ+),
          x.idx < (Pre.prog x.thread).length → (Pre.prog y.thread).length ≤ y.idx →
          x ∈ Ppref.progPoints → y ∈ Ppref.progPoints →
          Ppref.cmdAt x = some cx → Cmd.barrierRef cx = some (bb, mm) →
          Ppref.cmdAt y = some (Cmd.sync bb mm) →
          pointGen Ppref τpref x = pointGen Ppref τpref y →
          happensBefore Pfull τfull x ⟨y.thread, y.idx + (A.prog y.thread).length⟩ := by
        intro x y cx bb mm hx hy hxpp hypp hcx hbr hcy hg
        have hxPre : Pre.cmdAt x = some cx := hPreOfPpref x cx hx hcx
        have hxpf : x ∈ Pfull.progPoints := hPrePf x hxpp hx
        have hcmdPfx : Pfull.cmdAt x = some cx := by rw [← hcmdPrePref x hx]; exact hcx
        have hgenPfx : pointGen Pfull τfull x = pointGen Ppref τpref x :=
          hgenPre x cx bb mm hx hxPre hbr
        have hyLpf : (⟨y.thread, y.idx + (A.prog y.thread).length⟩ : ProgPoint)
            ∈ Pfull.progPoints :=
          (mem_progPoints_iff Pfull _).mpr ⟨((mem_progPoints_iff Ppref y).mp hypp).1, by
            dsimp only
            rw [hPfulllen]
            have := ((mem_progPoints_iff Ppref y).mp hypp).2; rw [hPpreflen] at this
            have hmul : (n + 1) * (A.prog y.thread).length
              = n * (A.prog y.thread).length + (A.prog y.thread).length := by
              rw [Nat.add_mul, one_mul]
            omega⟩
        by_cases hyloop : y.idx < (Pre.prog y.thread).length + n * (A.prog y.thread).length
        · -- `y` in the loop: `x → y` is a `Pfull` edge, then program order `y → y+L`
          have hcmdPfy : Pfull.cmdAt y = some (Cmd.sync bb mm) := by
            rw [← hcmdLoopPref y hyloop hy]; exact hcy
          have hgenPfy : pointGen Pfull τfull y = pointGen Ppref τpref y :=
            hloopgen y (Cmd.sync bb mm) bb mm hy hyloop hcmdPfy rfl
          have hypf : y ∈ Pfull.progPoints :=
            (mem_progPoints_iff Pfull y).mpr ⟨((mem_progPoints_iff Ppref y).mp hypp).1, by
              rw [hPfulllen]
              have := ((mem_progPoints_iff Ppref y).mp hypp).2; rw [hPpreflen] at this
              have hmul : (n + 1) * (A.prog y.thread).length
                = n * (A.prog y.thread).length + (A.prog y.thread).length := by
                rw [Nat.add_mul, one_mul]
              omega⟩
          have hstep : happensBefore Pfull τfull x y := by
            apply Relation.ReflTransGen.single
            rw [mem_initRelation_iff]
            cases cx with
            | read g => simp [Cmd.barrierRef] at hbr
            | write g => simp [Cmd.barrierRef] at hbr
            | arrive b' n' =>
              simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
              obtain ⟨rfl, rfl⟩ := hbr
              exact Or.inr (Or.inl ⟨b', n', hxpf, hypf, hcmdPfx, hcmdPfy,
                by rw [hgenPfx, hgenPfy]; exact hg⟩)
            | sync b' n' =>
              simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
              obtain ⟨rfl, rfl⟩ := hbr
              exact Or.inr (Or.inr ⟨b', n', hxpf, hypf, hcmdPfx, hcmdPfy,
                by rw [hgenPfx, hgenPfy]; exact hg⟩)
          refine hstep.trans (happensBefore_progOrder (by omega) ?_)
          rw [hPfulllen]; have := ((mem_progPoints_iff Ppref y).mp hypp).2; rw [hPpreflen] at this
          have hmul : (n + 1) * (A.prog y.thread).length
            = n * (A.prog y.thread).length + (A.prog y.thread).length := by
            rw [Nat.add_mul, one_mul]
          omega
        · -- `y` in `E`: rule out `bb ∈ I.barriers`; then `x → y+L` is a direct `Pfull` edge (`δ=0`)
          rw [Nat.not_lt] at hyloop
          have hbbni : bb ∉ I.barriers := by
            intro hbbI
            have hδbb1 : 1 ≤ I.loopK h * I.arrivers bb / I.arrivalCount h bb :=
              one_le_delta h rfl hbbI
            have hxle : pointGen Ppref τpref x ≤ recycleCount bb tP (tP.length - 2) + 1 := by
              rw [seq_glue_prefix_pointGen hpreXn htP htPL hτnX hxPre hbr]
              exact barrierOp_gen_le_total htP htPL hxPre hbr
            have hcXp : Xpref.cmdAt ⟨y.thread, y.idx - (Pre.prog y.thread).length⟩
                = some (Cmd.sync bb mm) := hcmdXp y _ hy hcy
            have hcXfL : Xfull.cmdAt ⟨y.thread, (y.idx - (Pre.prog y.thread).length)
                + (A.prog y.thread).length⟩ = some (Cmd.sync bb mm) := by
              change (Xfull.prog y.thread)[(y.idx - (Pre.prog y.thread).length)
                + (A.prog y.thread).length]? = _
              rw [hXfullsplit, List.getElem?_append_right (by omega),
                show y.idx - (Pre.prog y.thread).length + (A.prog y.thread).length
                    - (A.prog y.thread).length = y.idx - (Pre.prog y.thread).length from by omega]
              exact hcXp
            have hshift := hshiftX ⟨y.thread, y.idx - (Pre.prog y.thread).length⟩ (Cmd.sync bb mm)
              bb mm hcXp rfl
            rw [← hA] at hshift
            have hlow := (hgbX bb).2.2 hbbI ⟨y.thread, (y.idx - (Pre.prog y.thread).length)
              + (A.prog y.thread).length⟩ (Cmd.sync bb mm) mm hcXfL rfl (by
                dsimp only; rw [← hA]
                have hLloop : (A.prog y.thread).length ≤ n * (A.prog y.thread).length :=
                  Nat.le_mul_of_pos_left _ (by omega)
                omega)
            rw [hshift] at hlow
            have hgy := hgenXp y (Cmd.sync bb mm) bb mm hy hcy rfl
            omega
          have hδbb0 : I.loopK h * I.arrivers bb / I.arrivalCount h bb = 0 := by
            have harr0 : I.arrivers bb = 0 := by
              rw [CTA.arrivers]; apply Finset.sum_eq_zero
              intro i hi; rw [List.countP_eq_zero]; intro r hr hrb
              exact hbbni (by
                rw [CTA.barriers, Finset.mem_biUnion]
                exact ⟨i, hi, List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, eq_of_beq hrb⟩)⟩)
            rw [harr0, Nat.mul_zero, Nat.zero_div]
          have hcmdPfyL : Pfull.cmdAt ⟨y.thread, y.idx + (A.prog y.thread).length⟩
              = some (Cmd.sync bb mm) := hcmdEshift y (Cmd.sync bb mm) hy hcy
          have hgenPfyL : pointGen Pfull τfull ⟨y.thread, y.idx + (A.prog y.thread).length⟩
              = pointGen Ppref τpref y := by
            rw [hgenEshift y (Cmd.sync bb mm) bb mm hy hcy rfl, hδbb0, Nat.add_zero]
          apply Relation.ReflTransGen.single
          rw [mem_initRelation_iff]
          cases cx with
          | read g => simp [Cmd.barrierRef] at hbr
          | write g => simp [Cmd.barrierRef] at hbr
          | arrive b' n' =>
            simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
            obtain ⟨rfl, rfl⟩ := hbr
            exact Or.inr (Or.inl ⟨b', n', hxpf, hyLpf, hcmdPfx, hcmdPfyL,
              by rw [hgenPfx, hgenPfyL]; exact hg⟩)
          | sync b' n' =>
            simp only [Cmd.barrierRef, Option.some.injEq, Prod.mk.injEq] at hbr
            obtain ⟨rfl, rfl⟩ := hbr
            exact Or.inr (Or.inr ⟨b', n', hxpf, hyLpf, hcmdPfx, hcmdPfyL,
              by rw [hgenPfx, hgenPfyL]; exact hg⟩)
      -- **crossing edge lift** (any edge type): the single `Pre`→loop+epilogue boundary edge
      have hCrossEdge : ∀ (x y : ProgPoint), (x, y) ∈ initRelation Ppref τpref →
          x.idx < (Pre.prog x.thread).length → (Pre.prog y.thread).length ≤ y.idx →
          happensBefore Pfull τfull x ⟨y.thread, y.idx + (A.prog y.thread).length⟩ := by
        intro x y hxy hx hy
        rw [mem_initRelation_iff] at hxy
        rcases hxy with ⟨hxpts, hlt, hbeq⟩ | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
            | ⟨bb, mm, hxpts, hypts, hca, hcb, hg⟩
        · -- program-order seam: walk through the inserted batch
          subst hbeq; dsimp only at hy ⊢
          refine happensBefore_progOrder (by omega) ?_
          rw [hPfulllen]; rw [hPpreflen] at hlt
          have hmul : (n + 1) * (A.prog x.thread).length
              = n * (A.prog x.thread).length + (A.prog x.thread).length := by
            rw [Nat.add_mul, one_mul]
          omega
        · exact hcrossbar x y (Cmd.arrive bb mm) bb mm hx hy hxpts hypts hca rfl hcb hg
        · exact hcrossbar x y (Cmd.sync bb mm) bb mm hx hy hxpts hypts hca rfl hcb hg
      -- **the lift**: `happensBefore Ppref c1 c3'` ⟹ `happensBefore Pfull c1 (c2-1)`.  Peel the
      -- chain from `c1`; in `Pre` use `hPrePreEdge`, at the crossing use `hCrossEdge` then the
      -- X-region machinery (`hback`/`hmonoX`/`hforward`).
      have hPrefix : ∀ (a : ProgPoint),
          happensBefore Ppref τpref a ⟨c2.thread, c2.idx - (A.prog c2.thread).length - 1⟩ →
          a.idx < (Pre.prog a.thread).length →
          happensBefore Pfull τfull a ⟨c2.thread, c2.idx - 1⟩ := by
        intro a hR
        induction hR using Relation.ReflTransGen.head_induction_on with
        | refl => intro _; exact happensBefore_progOrder (by omega) (by omega)
        | @head x y hxy hrest ih =>
          intro hx
          by_cases hy : y.idx < (Pre.prog y.thread).length
          · exact (hPrePreEdge x y hxy hx hy).trans (ih hy)
          · rw [Nat.not_lt] at hy
            obtain ⟨hc3ge, hHBxpref⟩ := hback y _ hrest hy
            dsimp only at hc3ge hHBxpref
            have hHBxfull := hmonoX _ _ hHBxpref
            have hHBpfull := hforward _ _ hHBxfull
            dsimp only at hHBpfull
            rw [show y.idx - (Pre.prog y.thread).length + (A.prog y.thread).length
                    + (Pre.prog y.thread).length = y.idx + (A.prog y.thread).length from by omega,
              show c2.idx - (A.prog c2.thread).length - 1 - (Pre.prog c2.thread).length
                  + (A.prog c2.thread).length + (Pre.prog c2.thread).length = c2.idx - 1 from by
                omega] at hHBpfull
            exact (hCrossEdge x y hxy hx hy).trans hHBpfull
      -- order the down-shifted pair `(c1, c2-L)` in `Ppref`, then lift
      have hc2Lge : (Pre.prog c2.thread).length + (A.prog c2.thread).length ≤ c2.idx := by omega
      have hsync1P : Ppref.cmdAt c1 = some cc1 := by
        rw [hcmdPrePref c1 hc1pre]; exact hc1cmd
      have hbar1P : (Ppref.cmdAt c1).bind Cmd.barrier? = some b := by
        rw [hsync1P]; exact Cmd.barrier?_of_barrierRef hc1ref
      have hbar2P : (Ppref.cmdAt ⟨c2.thread, c2.idx - (A.prog c2.thread).length⟩).bind
          Cmd.barrier? = some b := by
        rw [hcmdrm c2 cc2 hc2Lge hc2cmd]; rw [hc2cmd] at hbar2; exact hbar2
      have hgenP : pointGen Ppref τpref ⟨c2.thread, c2.idx - (A.prog c2.thread).length⟩
          = pointGen Ppref τpref c1 + 1 := by
        have h2 := hgenrm c2 cc2 par2 hc2Lge hc2cmd hc2ref
        have hc1eqgen : pointGen Pfull τfull c1 = pointGen Ppref τpref c1 :=
          hgenPre c1 cc1 b par1 hc1pre hc1Pre hc1ref
        omega
      have hidxP : 1 ≤ c2.idx - (A.prog c2.thread).length := by omega
      have hHBppref : happensBefore Ppref τpref c1
          ⟨c2.thread, c2.idx - (A.prog c2.thread).length - 1⟩ :=
        happensBefore_of_check hcheckPref (mem_progPoints_of_cmdAt _ hsync1P) hbar1P
          (mem_progPoints_of_cmdAt _ (hcmdrm c2 cc2 hc2Lge hc2cmd)) hbar2P hgenP hidxP
      have hHB := hPrefix c1 hHBppref hc1pre
      rw [happensBefore, Relation.reflTransGen_iff_eq_or_transGen] at hHB
      rcases hHB with heq | htg
      · exact absurd heq.symm hc1ne3
      · exact mem_transClosure_of_transGen _ hc1ne3 htg
    · rw [Nat.not_lt] at hc1pre
      have hc1L : (Pre.prog c1.thread).length + (A.prog c1.thread).length ≤ c1.idx := by
        rcases hc1core with hh | hh
        · omega
        · exact hh
      have hc2L : (Pre.prog c2.thread).length + (A.prog c2.thread).length ≤ c2.idx := by omega
      -- the flagged pair shifted down by one batch is flagged in `Ppref`
      have hsync1P : Ppref.cmdAt ⟨c1.thread, c1.idx - (A.prog c1.thread).length⟩
          = some cc1 := hcmdrm c1 _ hc1L hc1cmd
      have hbar1P : (Ppref.cmdAt ⟨c1.thread, c1.idx - (A.prog c1.thread).length⟩).bind
          Cmd.barrier? = some b := by rw [hsync1P]; exact Cmd.barrier?_of_barrierRef hc1ref
      have hbar2P : (Ppref.cmdAt ⟨c2.thread, c2.idx - (A.prog c2.thread).length⟩).bind
          Cmd.barrier? = some b := by
        rw [hcmdrm c2 cc2 hc2L hc2cmd]; rw [hc2cmd] at hbar2; exact hbar2
      have hgenP : pointGen Ppref τpref ⟨c2.thread, c2.idx - (A.prog c2.thread).length⟩
          = pointGen Ppref τpref ⟨c1.thread, c1.idx - (A.prog c1.thread).length⟩ + 1 := by
        have h1 := hgenrm c1 cc1 par1 hc1L hc1cmd hc1ref
        have h2 := hgenrm c2 cc2 par2 hc2L hc2cmd hc2ref
        omega
      have hidxP : 1 ≤ c2.idx - (A.prog c2.thread).length := by omega
      have hHBppref : happensBefore Ppref τpref
          ⟨c1.thread, c1.idx - (A.prog c1.thread).length⟩
          ⟨c2.thread, c2.idx - (A.prog c2.thread).length - 1⟩ :=
        happensBefore_of_check hcheckPref (mem_progPoints_of_cmdAt _ hsync1P) hbar1P
          (mem_progPoints_of_cmdAt _ (hcmdrm c2 cc2 hc2L hc2cmd)) hbar2P hgenP hidxP
      have hc1Xge : (Pre.prog c1.thread).length ≤ c1.idx - (A.prog c1.thread).length := by omega
      obtain ⟨hc3Xge, hHBxpref⟩ := hback _ _ hHBppref hc1Xge
      dsimp only at hc3Xge hHBxpref
      have hHBxfull := hmonoX _ _ hHBxpref
      have hHBpfull := hforward _ _ hHBxfull
      dsimp only at hHBpfull
      rw [show c1.idx - (A.prog c1.thread).length - (Pre.prog c1.thread).length
            + (A.prog c1.thread).length + (Pre.prog c1.thread).length = c1.idx from by omega,
        show c2.idx - (A.prog c2.thread).length - 1 - (Pre.prog c2.thread).length
            + (A.prog c2.thread).length + (Pre.prog c2.thread).length = c2.idx - 1 from by omega]
        at hHBpfull
      rw [happensBefore, Relation.reflTransGen_iff_eq_or_transGen] at hHBpfull
      rcases hHBpfull with heq | htg
      · exact absurd heq.symm hc1ne3
      · exact mem_transClosure_of_transGen _ hc1ne3 htg

/-- **Loop-with-prefix-and-epilogue, generalized.** For a prefix `Pre`, body `I^k`
(`k = I.loopK h`) and epilogue `E`, every unrolling `Pre ⨾ (I^k)^n ⨾ E` (`n ≥ 1`) is
well-synchronized, given: `Pre` is well-synchronized (`hPre`), the single-batch unrolling
`Pre ⨾ (I^k) ⨾ E` is (`hPreBatchE`, the base case), and the two-batch front reference
`Pre ⨾ (I^k)^2 ⨾ E_ref` is (`hPre2BatchRef`; a *separate* epilogue `E_ref` because front pairs
are epilogue-independent). These three certifications are exactly what the loop check supplies
(`WS(P)`, the `i = k+r ≤ 2k` unrolling, the `i = 2k` unrolling). The prefix is carried through
the epilogue development of `loop_with_epilogue` by re-anchoring the replay construction at
`Pre`'s post-execution done state. -/
theorem CTA.WellSynchronized.loop_with_prefix_epilogue {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {Pre E E_ref : CTA}
    (hpre : Pre.ids = (I ^ k).ids) (hids : (I ^ k).ids = E.ids)
    (hidsRef : (I ^ k).ids = E_ref.ids)
    (hPre : Pre.WellSynchronized)
    (hPreBody : (Pre.seq (I ^ k) hpre).WellSynchronized)
    (hPreBatchE : (CTA.loopProgram Pre (I ^ k) E hpre hids 1).WellSynchronized)
    (hPreBatch2E : (CTA.loopProgram Pre (I ^ k) E hpre hids 2).WellSynchronized)
    (hPre3BatchRef : (CTA.loopProgram Pre (I ^ k) E_ref hpre hidsRef 3).WellSynchronized) :
    ∀ n, 1 ≤ n → (CTA.loopProgram Pre (I ^ k) E hpre hids n).WellSynchronized := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · rw [show n = 1 from by omega]; exact hPreBatchE
  · -- `n ≥ 2`: induct from the two-batch base, the step now requires `2 ≤ n`
    clear hn
    induction n, hge using Nat.le_induction with
    | base => exact hPreBatch2E
    | succ n hn ih =>
      exact CTA.WellSynchronized.loop_prefix_epilogue_inductive_step h hk hpre hids hidsRef hPre
        hPreBody hPreBatchE hPre3BatchRef hn ih

/-- **Correctness of the loop check.** The executable check
`checkLoopWellSynchronized P I E h h1 h2 τp τpk τ` returns `true` iff the prefix `P` is
well-synchronized, the prefix-plus-one-body `P ⨾ I^k` (`k = loopK`) is, *and* every unrolling
`loopProgram P I E h1 h2 n = P ⨾ I^n ⨾ E` (`n ≥ 0`) is — i.e. the loop runs safely for any
iteration count. `τp`/`τpk`/`τ i` are the standing successful traces `CheckWellSynchronized`
assumes of `P`, `P ⨾ I^k`, and each `i`-fold unrolling.

Two conjuncts are genuinely part of the spec, *not* implied by the unrollings (a program-prefix
of a WS CTA need not be WS):
* `WS(P)` — anchors the prefix in the trace construction;
* `WS(P ⨾ I^k)` — guarantees the loop body, run from `P`'s post-execution done-state `s_P`,
  *terminates on its own* (doesn't depend on the epilogue to complete a sync). Without it `I^k`
  from `s_P` can deadlock even though every `P ⨾ Iⁿ ⨾ E` is well-synchronized, and the
  replay-restores-`s_P` construction in `loop_with_prefix_epilogue` fails.
Both are checked separately and so appear in the conclusion.

* **(`←`)** trivial: the spec gives back each checked instance via
  `checkWellSynchronized_correct_impl`.
* **(`→`)** From `true`, `WS(P)`, `WS(P ⨾ I^k)`, and every checked unrolling `j ≤ 2k` hold.
  For `n ≤ 2k` the unrolling is the goal directly; for `n > 2k`, write `n = k * c + r`, regroup
  `I^r` into the epilogue (`loopProgram_regroup`), and apply `loop_with_prefix_epilogue` with
  `Pre := P`, body `I^k`, epilogue `I^r ⨾ E`. -/
theorem checkLoopWellSynchronized_correct_impl {P I E : CTA} (h : I.ConsistentArrivalCounts)
    (h1 : P.ids = I.ids) (h2 : I.ids = E.ids)
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
        ∧ ∀ n : Nat, (CTA.loopProgram P I E h1 h2 n).WellSynchronized := by
  -- Eliminate the checker: `check = true ↔ WS(P) ∧ WS(P ⨾ I^k) ∧ every unrolling in [0, 2k] is WS`.
  have hbridge : checkLoopWellSynchronized P I E h h1 h2 τp τpk τ = true ↔
      P.WellSynchronized
        ∧ (P.seq (I ^ I.loopK h) (h1.trans (CTA.pow_ids I (I.loopK h)).symm)).WellSynchronized
        ∧ ∀ i : Fin (3 * I.loopK h + 1), (CTA.loopProgram P I E h1 h2 i.val).WellSynchronized := by
    simp only [checkLoopWellSynchronized, Bool.and_eq_true, List.all_eq_true]
    constructor
    · rintro ⟨⟨hP, hPk⟩, hall⟩
      exact ⟨(checkWellSynchronized_correct_impl hτp).mp hP,
        (checkWellSynchronized_correct_impl hτpk).mp hPk,
        fun i => (checkWellSynchronized_correct_impl (hτ i)).mp (hall i (List.mem_finRange i))⟩
    · rintro ⟨hP, hPk, hall⟩
      exact ⟨⟨(checkWellSynchronized_correct_impl hτp).mpr hP,
          (checkWellSynchronized_correct_impl hτpk).mpr hPk⟩,
        fun i _ => (checkWellSynchronized_correct_impl (hτ i)).mpr (hall i)⟩
  rw [hbridge]
  constructor
  · -- forward: `WS(P)`, `WS(P ⨾ I^k)`, and the checked unrollings `[0, 2k]` force every `n`
    rintro ⟨hP, hPk, hchecked⟩
    refine ⟨hP, hPk, ?_⟩
    set k := I.loopK h with hk
    have hkpos : 0 < k := by rw [hk]; exact I.loopK_pos h
    intro n
    rcases Nat.lt_or_ge n (2 * k) with hsmall | hbig
    · exact hchecked ⟨n, by omega⟩
    · -- `n ≥ 2k`: write `n = k * c + r`, regroup `I^r` into the epilogue, apply the prefix lemma.
      set c := n / k with hc
      set r := n % k with hrdef
      have hr : r < k := Nat.mod_lt n hkpos
      have hsplit : n = k * c + r := by rw [hc, hrdef]; exact (Nat.div_add_mod n k).symm
      have hc1 : 1 ≤ c := by rw [hc, Nat.one_le_div_iff hkpos]; omega
      -- the `c = 1, 2` bases (epilogue `I^r ⨾ E`) and the `c = 3` front reference (`E_ref = E`)
      have hbe := hchecked ⟨k * 1 + r, by omega⟩
      rw [CTA.loopProgram_regroup P I E h1 h2 k 1 r] at hbe
      have hbe2 := hchecked ⟨k * 2 + r, by omega⟩
      rw [CTA.loopProgram_regroup P I E h1 h2 k 2 r] at hbe2
      have hbr := hchecked ⟨k * 3 + 0, by omega⟩
      rw [CTA.loopProgram_regroup P I E h1 h2 k 3 0] at hbr
      rw [hsplit, CTA.loopProgram_regroup P I E h1 h2 k c r]
      exact CTA.WellSynchronized.loop_with_prefix_epilogue
        (Pre := P) (E := (I ^ r).seq E ((CTA.pow_ids I r).trans h2))
        (E_ref := (I ^ 0).seq E ((CTA.pow_ids I 0).trans h2)) h hk
        (h1.trans (CTA.pow_ids I k).symm)
        ((CTA.pow_ids I k).trans (CTA.pow_ids I r).symm)
        ((CTA.pow_ids I k).trans (CTA.pow_ids I 0).symm)
        hP hPk hbe hbe2 hbr c hc1
  · -- reverse: the spec (incl. `WS(P)`, `WS(P ⨾ I^k)`) gives back the checked instances
    rintro ⟨hP, hPk, hall⟩
    exact ⟨hP, hPk, fun i => hall i.val⟩

/-- **Loop check for a bare loop (no prefix or epilogue).** Specializing `checkLoopWellSynchronized`
to an empty prefix and epilogue (`CTA.empty I.ids`), the check is correct iff *every* unrolling
`I ^ n` is well-synchronized. Unlike `checkLoopWellSynchronized_correct` it requires neither the
`WS(P)` nor the `WS(P ⨾ I^k)` certificate, and neither of their trace witnesses: an empty prefix is
trivially well-synchronized, while `P ⨾ I^k` is just the unrolling `I^k`, so its trace is the
unrolling `τ ⟨k, _⟩` already supplied (and the empty prefix's trace is the `0`-unrolling
`τ ⟨0, _⟩`). -/
theorem checkLoopWellSynchronized_correct_empty_impl {I : CTA} (h : I.ConsistentArrivalCounts)
    {τ : Fin (3 * I.loopK h + 1) → List Config}
    (hτ : ∀ i : Fin (3 * I.loopK h + 1),
      IsSuccessfulTraceFrom (Config.run State.initial
        (CTA.loopProgram (CTA.empty I.ids I.ids_nonempty) I (CTA.empty I.ids I.ids_nonempty)
          rfl rfl i.val)) (τ i)) :
    checkLoopWellSynchronized (CTA.empty I.ids I.ids_nonempty) I (CTA.empty I.ids I.ids_nonempty)
        h rfl rfl (τ ⟨0, by omega⟩) (τ ⟨I.loopK h, by omega⟩) τ = true
      ↔ ∀ n : Nat, (I ^ n).WellSynchronized := by
  have hOemp : ∀ t, (CTA.empty I.ids I.ids_nonempty).prog t = [] := fun _ => rfl
  -- the empty prefix's trace is the `0`-unrolling (which equals the empty CTA)
  have hτp : IsSuccessfulTraceFrom (Config.run State.initial (CTA.empty I.ids I.ids_nonempty))
      (τ ⟨0, by omega⟩) := hτ ⟨0, by omega⟩
  -- `P ⨾ I^k` is the `k`-unrolling with its trailing (empty) epilogue dropped
  have hloopk : CTA.loopProgram (CTA.empty I.ids I.ids_nonempty) I
        (CTA.empty I.ids I.ids_nonempty) rfl rfl (I.loopK h)
      = (CTA.empty I.ids I.ids_nonempty).seq (I ^ I.loopK h)
        (rfl.trans (CTA.pow_ids I (I.loopK h)).symm) := by
    apply CTA.ext
    · rfl
    · funext t
      change (CTA.empty I.ids I.ids_nonempty).prog t ++ (I ^ I.loopK h).prog t
          ++ (CTA.empty I.ids I.ids_nonempty).prog t
        = (CTA.empty I.ids I.ids_nonempty).prog t ++ (I ^ I.loopK h).prog t
      rw [hOemp, List.append_nil]
  have hτpk : IsSuccessfulTraceFrom (Config.run State.initial
      ((CTA.empty I.ids I.ids_nonempty).seq (I ^ I.loopK h)
        (rfl.trans (CTA.pow_ids I (I.loopK h)).symm))) (τ ⟨I.loopK h, by omega⟩) := by
    have ht := hτ ⟨I.loopK h, by omega⟩
    rwa [hloopk] at ht
  -- `P ⨾ I^k = I^k` (empty prefix) and `loopProgram (empty) I (empty) n = I^n`
  have hpkeq : (CTA.empty I.ids I.ids_nonempty).seq (I ^ I.loopK h)
        (rfl.trans (CTA.pow_ids I (I.loopK h)).symm) = I ^ I.loopK h := by
    apply CTA.ext
    · change I.ids = (I ^ I.loopK h).ids; rw [CTA.pow_ids]
    · funext t
      change (CTA.empty I.ids I.ids_nonempty).prog t ++ (I ^ I.loopK h).prog t
        = (I ^ I.loopK h).prog t
      rw [hOemp, List.nil_append]
  have hloopeq : ∀ n, CTA.loopProgram (CTA.empty I.ids I.ids_nonempty) I
      (CTA.empty I.ids I.ids_nonempty) rfl rfl n = I ^ n := by
    intro n
    apply CTA.ext
    · change I.ids = (I ^ n).ids; rw [CTA.pow_ids]
    · funext t
      rw [CTA.loopProgram_prog, hOemp, List.nil_append, List.append_nil]
  rw [checkLoopWellSynchronized_correct_impl (P := CTA.empty I.ids I.ids_nonempty)
    (E := CTA.empty I.ids I.ids_nonempty) h rfl rfl hτp hτpk hτ, hpkeq]
  simp only [hloopeq]
  exact ⟨fun ⟨_, _, hall⟩ => hall,
    fun hall => ⟨CTA.WellSynchronized.of_empty hOemp, hall (I.loopK h), hall⟩⟩

end Weft
