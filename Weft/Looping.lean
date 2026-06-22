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
moves a command into the arrived list (−1 command, +1 arrived); a `sync`-on-`b`
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
  | .run s _ => (s.B b).arrived.length
  | .done s  => (s.B b).arrived.length
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
        simp only [Function.update_self, hb0, BarrierState.unconfigured, List.length_cons,
          List.length_nil]
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
        simp only [Function.update_self, hb0, List.length_cons]
        omega
      · rw [if_neg (Ne.symm hbb)] at hsum
        simp only [Function.update_of_ne hbb]
        omega
    | sync_configure he hb0 =>
      rename_i b₀ n c
      by_cases hbb : b = b₀
      · subst hbb
        simp only [Function.update_self, hb0, BarrierState.unconfigured, List.length_nil]
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
`|I₀| + |A₀| = n₀`. Duplicate-freeness (`hnd`) is what makes the woken-thread command
drop equal to `I₀.length` rather than the number of *distinct* woken ids. -/
theorem barrierPotential_recycle_eq {s : State} {T : CTA} {b : Barrier}
    {I₀ A₀ : List ThreadId} {n₀ : ℕ+}
    (hb : s.B b = ⟨I₀, A₀, some n₀⟩) (hfull : I₀.length + A₀.length = (n₀ : Nat))
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
    Function.update_self, BarrierState.unconfigured, List.length_nil, Nat.zero_add, CTA.wake]
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
theorem bstate_frozen_step {b : Barrier} {nb : Nat} {I₀ A₀ : List ThreadId} {n₀ : ℕ+}
    (hlen : I₀.length + A₀.length ≠ (n₀ : Nat)) (hne : (n₀ : Nat) ≠ nb)
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
theorem bstate_frozen_chain {b : Barrier} {nb : Nat} {I₀ A₀ : List ThreadId} {n₀ : ℕ+}
    (hlen : I₀.length + A₀.length ≠ (n₀ : Nat)) (hne : (n₀ : Nat) ≠ nb) :
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
  have hlen : (s.B b).synced.length + (s.B b).arrived.length ≠ (n' : Nat) := by
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
  have hdonepot : (Config.done s_d).barrierPotential b = (s.B b).arrived.length := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount,
      Nat.add_zero, hbd]
  have hheadpot : (Config.run s (I ^ k)).barrierPotential b
      = (s.B b).arrived.length + (I ^ k).arrivers b := by
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
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived.length := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hdonepot] at hcons
  have harr : nb ≤ (s_d.B b).arrived.length := by rw [hcons]; exact le_trans hstep2 hC₀pot
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
      = (s.B b).arrived.length + (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived.length := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hC₀pot, hdonepot] at hcons
  -- both arrived lengths are below the arrival count
  have hA0 : (s.B b).arrived.length < nb := by
    by_cases hcfg : (s.B b).count = none
    · have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, none⟩ := by rw [← hcfg]
      have harr0 := (hwf.2.1 b (s.B b).synced (s.B b).arrived heq).2
      rw [harr0]; simpa using hnbpos
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hb0 n' hn'
      have hle := (hwf.1 b (s.B b).synced (s.B b).arrived n' heq).1
      have hne2 : (s.B b).synced.length + (s.B b).arrived.length ≠ (n' : Nat) := by
        intro he; rw [heq] at hfull; simp [BarrierState.isFull, he] at hfull
      omega
  have hAd : (s_d.B b).arrived.length < nb := by
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
  have hAeq : (s.B b).arrived.length = (s_d.B b).arrived.length := by
    have e : ((s.B b).arrived.length + nb * q) % nb
        = ((s_d.B b).arrived.length + nb * recycleCount b τ (τ.length - 1)) % nb := by rw [hcons]
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
`k · arrivers(b)` are a multiple of `arrival-count(b)`, and both arrived lengths are below
it, so they must be equal. -/
theorem arrivedLen_preserved {I : CTA} (h : I.ConsistentArrivalCounts) {s : State}
    {b : Barrier} (hwf : (Config.run s (I ^ I.loopK h)).WF)
    (hfull : (s.B b).isFull = false) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet)
    {s_d : State} (hlast : τ.getLast? = some (Config.done s_d)) :
    (s_d.B b).arrived.length = (s.B b).arrived.length := by
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
      = (s.B b).arrived.length + (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived.length := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hC₀pot, hdonepot] at hcons
  have hA0 : (s.B b).arrived.length < nb := by
    by_cases hcfg : (s.B b).count = none
    · have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, none⟩ := by rw [← hcfg]
      have harr0 := (hwf.2.1 b (s.B b).synced (s.B b).arrived heq).2
      rw [harr0]; simpa using hnbpos
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s.B b = ⟨(s.B b).synced, (s.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hb0 n' hn'
      have hle := (hwf.1 b (s.B b).synced (s.B b).arrived n' heq).1
      have hne2 : (s.B b).synced.length + (s.B b).arrived.length ≠ (n' : Nat) := by
        intro he; rw [heq] at hfull; simp [BarrierState.isFull, he] at hfull
      omega
  have hAd : (s_d.B b).arrived.length < nb := by
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
  have e : ((s.B b).arrived.length + nb * q) % nb
      = ((s_d.B b).arrived.length + nb * recycleCount b τ (τ.length - 1)) % nb := by rw [hcons]
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

end Weft
