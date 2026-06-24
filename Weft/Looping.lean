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
theorem seqLift_penultimate_gen {A B : CTA} (hids : A.ids = B.ids) {t : List Config}
    (hchain : List.IsChain CTAStep t) (hhead : t.head? = some (Config.run State.initial A))
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
      · show T.ids ∪ B.ids = B.ids; rw [hTids, hids, Finset.union_self]
      · funext i; show T.prog i ++ B.prog i = B.prog i; rw [hTprog i, List.nil_append]
    show Config.run sd (T.appendTail B) = Config.run sd B
    rw [hBeq]

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
theorem CTA.WellSynchronized.second_batch_recycle_offset {I : CTA}
    (h : I.ConsistentArrivalCounts) {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized)
    (hWS1 : ((I ^ k).seq (I ^ k) rfl).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (n : ℕ+) (m₁ m₂ : Nat),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, n) →
        IsTimeOf (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ⟨t, j⟩ m₁ →
        IsTimeOf (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ
            ⟨t, ((I ^ k).prog t).length + j⟩ m₂ →
        recycleCount b τ (m₂ - 1)
          = recycleCount b τ (m₁ - 1) + k * I.arrivers b / I.arrivalCount h b := by
  subst hk
  set A := I ^ I.loopK h with hA
  obtain ⟨t₁, ht₁⟩ := hWS0.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  refine ⟨_, replay_trace A ht₁ ht₁L, ?_⟩
  intro t j c b n m₁ m₂ hcj hbr ht1 ht2
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
  have hPLgl : (t₁.dropLast.map (Config.seqLift A A)).getLast hPLne = Config.run State.initial A := by
    have hg : (t₁.dropLast.map (Config.seqLift A A)).getLast? = some (Config.run State.initial A) := by
      rw [List.getLast?_map, List.getLast?_eq_some_getLast hdrop, Option.map_some, hCstar]
    have hh := List.getLast?_eq_some_getLast hPLne; rw [hg] at hh; exact (Option.some.injEq _ _).mp hh.symm
  have htlist : (t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail
      = (t₁.dropLast.map (Config.seqLift A A)).dropLast ++ t₁ := by
    conv_lhs => rw [← List.dropLast_concat_getLast hPLne]
    rw [hPLgl, List.append_assoc, List.singleton_append, ht₁cons]
  have hQlen : ((t₁.dropLast.map (Config.seqLift A A)).dropLast).length = t₁.length - 2 := by
    rw [List.length_dropLast, hPLlen]; omega
  -- suffix: the second batch of `τ` is exactly `t₁`
  have hsnd : ∀ r, ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail)[(t₁.length - 2) + r]? = t₁[r]? := by
    intro r
    rw [htlist, List.getElem?_append_right (by rw [hQlen]; omega), hQlen]
    congr 1; omega
  -- first batch agrees with the lifted `t₁`
  have hdropget : ∀ q, q < t₁.length - 1 → t₁.dropLast[q]? = t₁[q]? :=
    fun q hq => by rw [List.getElem?_dropLast, if_pos hq]
  have hfst : ∀ q, q ≤ t₁.length - 2 →
      ((t₁.dropLast.map (Config.seqLift A A)) ++ t₁.tail)[q]? = (t₁.map (Config.seqLift A A))[q]? := by
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
    push_neg at hcon
    have hCt : t₁[j₀ - (t₁.length - 2)]? = some C := by
      have := hsnd (j₀ - (t₁.length - 2)); rw [show (t₁.length - 2) + (j₀ - (t₁.length - 2)) = j₀ by omega, hCj] at this; exact this.symm
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
    push_neg at hcon
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
    have := hsnd (j₂ - (t₁.length - 2)); rw [show (t₁.length - 2) + (j₂ - (t₁.length - 2)) = j₂ by omega, hDj] at this; exact this.symm
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

/-- **Lemma 3, two-batch case.** Let `k = I.loopK h` be the §1 iteration count, and
assume both `I ^ k` and the two-batch program `I ^ k ⨾ I ^ k` are well-synchronized
(`hWS0`, `hWS1`). Then there is a successful trace `τ` of `I ^ k ⨾ I ^ k` whose recovered
generation mapping (`pointGen`) has the batch structure of the document's Lemma 3: every
barrier instruction of the **second** batch has the same generation as the corresponding
instruction of the **first** batch, incremented by `k · arrivers(b) / arrival-count(b)`,
the number of times one batch recycles that instruction's barrier `b`.

A program point `⟨t, j⟩` with `((I ^ k).prog t)[j]? = some c` is instruction `j` of thread
`t` in the first batch; since `(I ^ k ⨾ I ^ k).prog t = (I ^ k).prog t ++ (I ^ k).prog t`,
the *corresponding* instruction of the second batch is `⟨t, |(I ^ k).prog t| + j⟩` (the same
command `c`). The structure is stated only for barrier instructions (`Cmd.barrierRef c =
some (b, n)`), the ones generations are defined on.

Proof sketch (to fill in). By `seq_angelic_completion` (using `hWS0`, `hWS1`) there is a
successful trace of `I ^ k ⨾ I ^ k` that runs the first `I ^ k` to completion and then the
second. By `pow_barriers_restored` the state after the first batch agrees (on arrived
counts) with the initial state, so — `I ^ k` being well-synchronized — the *same* schedule
replays on the second batch, producing the same per-instruction generations offset by the
recycles accumulated in the first batch. That recycle count is
`k · arrivers(b) / arrival-count(b)` by `pow_barriers_advance_count`; the absence of
backward happens-before edges (`seq_no_happensBefore_B_to_A`) is what guarantees the second
batch cannot perturb the first batch's generations.
NOTE (rohany): This is the first step towards an important lemma.
-/
theorem CTA.WellSynchronized.second_batch_gen_offset {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized)
    (hWS1 : ((I ^ k).seq (I ^ k) rfl).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (n : ℕ+),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, n) →
        pointGen ((I ^ k).seq (I ^ k) rfl) τ ⟨t, ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k).seq (I ^ k) rfl) τ ⟨t, j⟩
            + k * I.arrivers b / I.arrivalCount h b := by
  -- The recycle-count core supplies the trace and the per-instruction offset.
  obtain ⟨τ, hτ, hrec⟩ := CTA.WellSynchronized.second_batch_recycle_offset h hk hWS0 hWS1
  refine ⟨τ, hτ, ?_⟩
  intro t j c b n hcj hbr
  -- the start configuration's program for thread `t` is `(I ^ k) ; (I ^ k)`
  have hprogt : (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)).progOf t
      = (I ^ k).prog t ++ (I ^ k).prog t := rfl
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hcj
  obtain ⟨sd, hlast⟩ := hτ.2
  -- both copies of the instruction execute in the successful trace `τ`
  obtain ⟨m₁, ht1⟩ := exists_time_of_ends_done hτ.1 hlast (η := ⟨t, j⟩)
    (by change j < ((Config.run State.initial ((I ^ k).seq (I ^ k) rfl)).progOf t).length
        rw [hprogt, List.length_append]; omega)
  obtain ⟨m₂, ht2⟩ := exists_time_of_ends_done hτ.1 hlast (η := ⟨t, ((I ^ k).prog t).length + j⟩)
    (by change ((I ^ k).prog t).length + j
            < ((Config.run State.initial ((I ^ k).seq (I ^ k) rfl)).progOf t).length
        rw [hprogt, List.length_append]; omega)
  -- the command at each point is `c`, a barrier op on `b`
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  have hcmd1 : ((I ^ k).seq (I ^ k) rfl).cmdAt ⟨t, j⟩ = some c := by
    change ((I ^ k).prog t ++ (I ^ k).prog t)[j]? = some c
    rw [List.getElem?_append_left hjlt]; exact hcj
  have hcmd2 : ((I ^ k).seq (I ^ k) rfl).cmdAt ⟨t, ((I ^ k).prog t).length + j⟩ = some c := by
    change ((I ^ k).prog t ++ (I ^ k).prog t)[((I ^ k).prog t).length + j]? = some c
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hcj
  -- each generation is its barrier's recycle count just before its execution time, plus one
  have hg1 : pointGen ((I ^ k).seq (I ^ k) rfl) τ ⟨t, j⟩ = recycleCount b τ (m₁ - 1) + 1 := by
    simp only [pointGen, hcmd1, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht1]
  have hg2 : pointGen ((I ^ k).seq (I ^ k) rfl) τ ⟨t, ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₂ - 1) + 1 := by
    simp only [pointGen, hcmd2, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht2]
  rw [hg1, hg2, hrec t j c b n m₁ m₂ hcj hbr ht1 ht2]; omega

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
  · show (A ^ 2).ids = A.ids; rw [CTA.pow_ids]
  · funext t; show (A ^ 2).prog t = A.prog t ++ A.prog t; rw [CTA.pow_two_prog]

/-- **Regroup the last two batches.** For `n ≥ 2`, the `n`-batch program `A ^ n` *is* the
first `n - 2` batches sequentially composed with the last two: `A ^ n = (A ^ (n-2)) ⨾ (A ⨾ A)`.
This is the structural identity that lets `last_batch_gen_offset` reuse the two-batch
`second_batch` machinery on the final `A ⨾ A`, with the first `n - 2` batches as an inert
prefix. -/
theorem CTA.pow_regroup_last_two (A : CTA) {n : Nat} (hn : 2 ≤ n) :
    A ^ n = (A ^ (n - 2)).seq (A.seq A rfl) (CTA.pow_ids A (n - 2)) := by
  apply CTA.ext
  · show (A ^ n).ids = (A ^ (n - 2)).ids; rw [CTA.pow_ids, CTA.pow_ids]
  · funext t
    show (A ^ n).prog t = (A ^ (n - 2)).prog t ++ (A.prog t ++ A.prog t)
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [CTA.pow_add_prog, CTA.pow_two_prog]

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
theorem glue_trace {A B : CTA} (hids : A.ids = B.ids) {t_A : List Config}
    (htA : IsSuccessfulTraceFrom (Config.run State.initial A) t_A)
    (hAlast : t_A.getLast? = some (Config.done State.initial))
    {τ_B : List Config} (hτB : IsSuccessfulTraceFrom (Config.run State.initial B) τ_B) :
    IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids))
        (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail) ∧
      (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail).getLast? = τ_B.getLast? ∧
      ∀ r, (t_A.dropLast.map (Config.seqLift A B) ++ τ_B.tail)[(t_A.length - 2) + r]?
          = τ_B[r]? := by
  have hchain : List.IsChain CTAStep t_A := htA.1.1.subtrace
  have hhead : t_A.head? = some (Config.run State.initial A) := htA.1.2
  obtain ⟨_, _, hteq⟩ : ∃ c1 trest, t_A = Config.run State.initial A :: c1 :: trest := by
    rcases t_A with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hhead
    · rw [List.head?_cons, Option.some.injEq] at hhead
      rw [List.getLast?_singleton, Option.some.injEq] at hAlast
      rw [hhead] at hAlast; exact absurd hAlast (by simp)
    · rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead; exact ⟨b, l, rfl⟩
  have hdrop : t_A.dropLast ≠ [] := by rw [hteq]; simp
  -- The boundary config `C⋆ = seqLift A B (penult t_A)` is `run init B` (full restoration),
  -- so the given B-trace `τ_B` is itself a complete continuation from `C⋆`; `seq_splice`
  -- glues it onto the lifted `A`-phase.
  have hCstar : Config.seqLift A B (t_A.dropLast.getLast hdrop) = Config.run State.initial B :=
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
    (hWS : (I ^ k).BatchesWellSynchronized n) :
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
  -- well-synchronization of one batch and of two batches, from the prefix hypothesis
  have hWSA : (I ^ I.loopK h).WellSynchronized := by
    have := hWS 1 (le_refl 1) (by omega); rwa [CTA.pow_one] at this
  have hWSAA : ((I ^ I.loopK h).seq (I ^ I.loopK h) rfl).WellSynchronized := by
    have := hWS 2 (by omega) hn; rwa [CTA.pow_two_eq_seq] at this
  -- single batch trace, restoring the state to `initial`
  obtain ⟨t₁, ht₁⟩ := hWSA.exists_successfulTrace
  obtain ⟨sd₁, ht₁L⟩ := ht₁.2
  have hinit : sd₁ = State.initial := pow_done_state_initial h ht₁ ht₁L
  rw [hinit] at ht₁L
  -- two-batch trace with the per-instruction offset (the hard two-batch case)
  obtain ⟨τAA, hτAA, hrecAA⟩ := CTA.WellSynchronized.second_batch_recycle_offset h rfl hWSA hWSAA
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
      show (A.prog t ++ A.prog t).length = _; rw [List.length_append]
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
      · show (n - 2) * (A.prog t).length + q < ((A ^ n).prog t).length
        rw [hnLen, hnL]; omega
      · exact (hsnd j').trans hDj
      · rw [show (tC.length - 2) + j' + 1 = (tC.length - 2) + (j' + 1) from by omega]
        exact (hsnd (j' + 1)).trans hDj1
      · show D.progOf t = ((A ^ n).prog t).drop ((n - 2) * (A.prog t).length + q)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 2) * (A.prog t).length + q - ((A ^ (n - 2)).prog t).length = q from by
            rw [hCLen]; omega]
        exact hDprog
      · show D'.progOf t = ((A ^ n).prog t).drop ((n - 2) * (A.prog t).length + q + 1)
        rw [hprogeq, List.drop_append, List.drop_eq_nil_of_le (by rw [hCLen]; omega),
          List.nil_append,
          show (n - 2) * (A.prog t).length + q + 1 - ((A ^ (n - 2)).prog t).length = q + 1 from by
            rw [hCLen]; omega]
        exact hD'prog
    -- the two corresponding instruction times in the two-batch trace
    obtain ⟨sdAA, hAAlast⟩ := hτAA.2
    obtain ⟨m₁', hT1'⟩ := exists_time_of_ends_done hτAA.1 hAAlast (η := ⟨t, j⟩)
      (by show j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
    obtain ⟨m₂', hT2'⟩ := exists_time_of_ends_done hτAA.1 hAAlast
      (η := ⟨t, (A.prog t).length + j⟩)
      (by show (A.prog t).length + j < ((A.seq A rfl).prog t).length; rw [hAAlen]; omega)
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
theorem CTA.WellSynchronized.last_batch_gen_offset {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h) {n : Nat} (hn : 2 ≤ n)
    (hWS : (I ^ k).BatchesWellSynchronized n) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k) ^ n)) τ ∧
      ∀ (t : ThreadId) (j : Nat) (c : Cmd) (b : Barrier) (m : ℕ+),
        ((I ^ k).prog t)[j]? = some c → Cmd.barrierRef c = some (b, m) →
        pointGen ((I ^ k) ^ n) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
          = pointGen ((I ^ k) ^ n) τ ⟨t, (n - 2) * ((I ^ k).prog t).length + j⟩
            + k * I.arrivers b / I.arrivalCount h b := by
  -- The recycle-count core supplies the trace and the per-instruction offset between the
  -- last two batches; this is the routine `pointGen`-to-`recycleCount` repackaging.
  obtain ⟨τ, hτ, hrec⟩ := CTA.WellSynchronized.last_batch_recycle_offset h hk hn hWS
  refine ⟨τ, hτ, ?_⟩
  intro t j c b par hcj hbr
  obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hcj
  obtain ⟨sd, hlast⟩ := hτ.2
  -- length bookkeeping for thread `t`'s `n`-batch program
  have hnLen : (((I ^ k) ^ n).prog t).length = n * ((I ^ k).prog t).length :=
    CTA.pow_prog_length (I ^ k) n t
  have hnL : n * ((I ^ k).prog t).length
      = (n - 2) * ((I ^ k).prog t).length
        + (((I ^ k).prog t).length + ((I ^ k).prog t).length) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.add_mul]
    omega
  have hn1L : (n - 1) * ((I ^ k).prog t).length
      = (n - 2) * ((I ^ k).prog t).length + ((I ^ k).prog t).length := by
    rw [show n - 1 = (n - 2) + 1 from by omega, Nat.succ_mul]
  -- the command at each of the two copies is `c`, a barrier op on `b`
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
  have hcmd1 : ((I ^ k) ^ n).cmdAt ⟨t, (n - 2) * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat (n - 2) (by omega)
  have hcmd2 : ((I ^ k) ^ n).cmdAt ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩ = some c :=
    hcmdat (n - 1) (by omega)
  have hbar : Cmd.barrier? c = some b := Cmd.barrier?_of_barrierRef hbr
  -- both copies execute in the successful trace `τ`
  obtain ⟨m₁, ht1⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, (n - 2) * ((I ^ k).prog t).length + j⟩)
    (by show (n - 2) * ((I ^ k).prog t).length + j < (((I ^ k) ^ n).prog t).length
        rw [hnLen, hnL]; omega)
  obtain ⟨m₂, ht2⟩ := exists_time_of_ends_done hτ.1 hlast
    (η := ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩)
    (by show (n - 1) * ((I ^ k).prog t).length + j < (((I ^ k) ^ n).prog t).length
        rw [hnLen, hnL, hn1L]; omega)
  -- each generation is its barrier's recycle count just before its execution time, plus one
  have hg1 : pointGen ((I ^ k) ^ n) τ ⟨t, (n - 2) * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₁ - 1) + 1 := by
    simp only [pointGen, hcmd1, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht1]
  have hg2 : pointGen ((I ^ k) ^ n) τ ⟨t, (n - 1) * ((I ^ k).prog t).length + j⟩
      = recycleCount b τ (m₂ - 1) + 1 := by
    simp only [pointGen, hcmd2, Option.bind_some, hbar, pointTime_eq_of_isTimeOf ht2]
  rw [hg1, hg2, hrec t j c b par m₁ m₂ hcj hbr ht1 ht2]; omega

/-- **Full membership characterization of `initRelation`** (the converse-complete form of
`initRelation_cases`, retaining the arrival count `n` that `initRelation_cases` drops). An
edge `(a, b)` of `initRelation T τ` is exactly one of:
* a program-order edge `b = ⟨a.thread, a.idx + 1⟩` (with `a.idx + 1` in range);
* an `arrive bb n → sync bb n` edge of equal generation (Figure 4 lines 7–11);
* a `sync bb n ↔ sync bb n` edge of equal generation (lines 12–16) — symmetric, so the
  same shape covers both endpoints being `sync`.

Keeping `n` is what lets `second_batch_hb_within` *reconstruct* the shifted edge in the
neighbouring batch (the generation offset is by-barrier, so equal generations stay equal). -/
theorem mem_initRelation_iff {T : CTA} {τ : List Config} {a b : ProgPoint} :
    (a, b) ∈ initRelation T τ ↔
      (a ∈ T.progPoints ∧ a.idx + 1 < (T.prog a.thread).length ∧ b = ⟨a.thread, a.idx + 1⟩)
      ∨ (∃ bb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.arrive bb n) ∧ T.cmdAt b = some (.sync bb n) ∧
          pointGen T τ a = pointGen T τ b)
      ∨ (∃ bb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.sync bb n) ∧ T.cmdAt b = some (.sync bb n) ∧
          pointGen T τ a = pointGen T τ b) := by
  constructor
  · intro hedge
    simp only [initRelation, List.mem_toFinset, List.mem_append] at hedge
    rcases hedge with (hpo | has) | hss
    · -- program order
      simp only [List.mem_filterMap] at hpo
      obtain ⟨c, hc, hceq⟩ := hpo
      split at hceq
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hceq
        obtain ⟨rfl, rfl⟩ := hceq
        exact Or.inl ⟨hc, hcond, rfl⟩
      · exact absurd hceq (by simp)
    · -- arrive → sync
      simp only [List.mem_flatMap] at has
      obtain ⟨c1, hc1, hin⟩ := has
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | sync bb n => simp [hcmd1] at hin
        | arrive bb n =>
          simp only [hcmd1, List.mem_filterMap] at hin
          obtain ⟨c2, hc2, hc2eq⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hc2eq
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hc2eq
            | write g => simp [hcmd2] at hc2eq
            | arrive b' n' => simp [hcmd2] at hc2eq
            | sync b' n' =>
              simp only [hcmd2] at hc2eq
              split at hc2eq
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
                obtain ⟨rfl, rfl⟩ := hc2eq
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                exact Or.inr (Or.inl ⟨bb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩)
              · exact absurd hc2eq (by simp)
    · -- sync ↔ sync
      simp only [List.mem_flatMap] at hss
      obtain ⟨c1, hc1, hin⟩ := hss
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | arrive bb n => simp [hcmd1] at hin
        | sync bb n =>
          simp only [hcmd1, List.mem_flatMap] at hin
          obtain ⟨c2, hc2, hin2⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hin2
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hin2
            | write g => simp [hcmd2] at hin2
            | arrive b' n' => simp [hcmd2] at hin2
            | sync b' n' =>
              simp only [hcmd2] at hin2
              split at hin2
              · rename_i hcond
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
                  Prod.mk.injEq] at hin2
                rcases hin2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr (Or.inr ⟨bb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩)
                · exact Or.inr (Or.inr ⟨bb, n, hc2, hc1, hcmd2, hcmd1, hgen.symm⟩)
              · simp at hin2
  · intro h
    rcases h with ⟨hapts, hlt, hbeq⟩ | ⟨bb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
        | ⟨bb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
    · -- program order
      obtain ⟨at', ai⟩ := a
      subst hbeq
      exact mem_initRelation_progOrder hlt
    · -- arrive → sync
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap,
        List.mem_filterMap]
      refine Or.inl (Or.inr ⟨a, hapts, ?_⟩)
      simp only [hcmda, List.mem_filterMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩
    · -- sync ↔ sync
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap]
      refine Or.inr ⟨a, hapts, ?_⟩
      simp only [hcmda, List.mem_flatMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩

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

/-- **Lemma 4.2, conclusion 1 (within-batch), two-batch case.** *Stated, not yet proved.*
For the two back-to-back batches `I ^ k ⨾ I ^ k`, there is a successful trace `τ` whose
happens-before relation agrees between the two batches *internally*: for any two body
instructions `⟨t₁, j₁⟩` and `⟨t₂, j₂⟩` of `I ^ k`, the first-batch copies are happens-before
related exactly when the second-batch copies are. This is conclusion 1 of
`structure-r-across-iterations` at `n = 0` (the first batch is `I_0^k`, the second `I_1^k`).

Unlike `second_batch_gen_offset`, this is stated for *all* instruction pairs (not only barrier
instructions): `R` orders read/write instructions too, via program order and the sync edges. -/
theorem CTA.WellSynchronized.second_batch_hb_within {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized)
    (hWS1 : ((I ^ k).seq (I ^ k) rfl).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom (Config.run State.initial ((I ^ k).seq (I ^ k) rfl)) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore ((I ^ k).seq (I ^ k) rfl) τ ⟨t₁, j₁⟩ ⟨t₂, j₂⟩
          ↔ happensBefore ((I ^ k).seq (I ^ k) rfl) τ
              ⟨t₁, ((I ^ k).prog t₁).length + j₁⟩ ⟨t₂, ((I ^ k).prog t₂).length + j₂⟩) := by
  -- the trace and the per-instruction generation offset (Lemma 4.1), and the absence of
  -- backward happens-before edges between the two batches
  obtain ⟨τ, hτ, hgen⟩ := CTA.WellSynchronized.second_batch_gen_offset h hk hWS0 hWS1
  have hnoback := CTA.WellSynchronized.seq_no_happensBefore_B_to_A rfl hWS0 hWS1 hτ
  refine ⟨τ, hτ, ?_⟩
  set A := I ^ k with hA
  -- commands agree between the two batches; program points of both batches are valid
  have hcmdfst : ∀ (t : ThreadId) (j : Nat), j < (A.prog t).length →
      (A.seq A rfl).cmdAt ⟨t, j⟩ = (A.prog t)[j]? := by
    intro t j hj
    show (A.prog t ++ A.prog t)[j]? = (A.prog t)[j]?
    rw [List.getElem?_append_left hj]
  have hcmdA : ∀ (t : ThreadId) (j : Nat), j < (A.prog t).length →
      (A.seq A rfl).cmdAt ⟨t, (A.prog t).length + j⟩ = (A.seq A rfl).cmdAt ⟨t, j⟩ := by
    intro t j hj
    show (A.prog t ++ A.prog t)[(A.prog t).length + j]? = (A.prog t ++ A.prog t)[j]?
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hj]
  have hppA : ∀ (t : ThreadId) (j : Nat), j < (A.prog t).length →
      (⟨t, j⟩ : ProgPoint) ∈ (A.seq A rfl).progPoints := by
    intro t j hj
    rw [mem_progPoints_iff]
    refine ⟨mem_ids_of_idx_lt A hj, ?_⟩
    show j < (A.prog t ++ A.prog t).length
    rw [List.length_append]; omega
  have hppB : ∀ (t : ThreadId) (j : Nat), j < (A.prog t).length →
      (⟨t, (A.prog t).length + j⟩ : ProgPoint) ∈ (A.seq A rfl).progPoints := by
    intro t j hj
    rw [mem_progPoints_iff]
    refine ⟨mem_ids_of_idx_lt A hj, ?_⟩
    show (A.prog t).length + j < (A.prog t ++ A.prog t).length
    rw [List.length_append]; omega
  have hPlen : ∀ (t : ThreadId), ((A.seq A rfl).prog t).length
      = (A.prog t).length + (A.prog t).length := by
    intro t; show (A.prog t ++ A.prog t).length = _; rw [List.length_append]
  -- **Edge shift.** An `initRelation` edge between two first-batch body points exists iff the
  -- edge between their second-batch copies does. The barrier edges hinge on generation
  -- *equality*, preserved because both endpoints shift by the *same* per-barrier offset.
  have hshift : ∀ (a b : ProgPoint), a.idx < (A.prog a.thread).length →
      b.idx < (A.prog b.thread).length →
      ((a, b) ∈ initRelation (A.seq A rfl) τ ↔
        (⟨a.thread, (A.prog a.thread).length + a.idx⟩,
          ⟨b.thread, (A.prog b.thread).length + b.idx⟩) ∈ initRelation (A.seq A rfl) τ) := by
    intro a b ha hb
    obtain ⟨s₁, i₁⟩ := a
    obtain ⟨s₂, i₂⟩ := b
    dsimp only at ha hb
    rw [mem_initRelation_iff, mem_initRelation_iff]
    constructor
    · rintro (⟨_, _, heq⟩ | ⟨bb, n, _, _, hc1, hc2, hg⟩ | ⟨bb, n, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        refine Or.inl ⟨hppB s₂ i₁ ha, ?_, ?_⟩
        · show (A.prog s₂).length + i₁ + 1 < ((A.seq A rfl).prog s₂).length
          rw [hPlen]; omega
        · show (⟨s₂, (A.prog s₂).length + (i₁ + 1)⟩ : ProgPoint)
              = ⟨s₂, (A.prog s₂).length + i₁ + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · refine Or.inr (Or.inl ⟨bb, n, hppB s₁ i₁ ha, hppB s₂ i₂ hb, ?_, ?_, ?_⟩)
        · rw [hcmdA s₁ i₁ ha]; exact hc1
        · rw [hcmdA s₂ i₂ hb]; exact hc2
        · have hcj1 : (A.prog s₁)[i₁]? = some (Cmd.arrive bb n) := by
            rw [← hcmdfst s₁ i₁ ha]; exact hc1
          have hcj2 : (A.prog s₂)[i₂]? = some (Cmd.sync bb n) := by
            rw [← hcmdfst s₂ i₂ hb]; exact hc2
          rw [hgen s₁ i₁ _ bb n hcj1 rfl, hgen s₂ i₂ _ bb n hcj2 rfl, hg]
      · refine Or.inr (Or.inr ⟨bb, n, hppB s₁ i₁ ha, hppB s₂ i₂ hb, ?_, ?_, ?_⟩)
        · rw [hcmdA s₁ i₁ ha]; exact hc1
        · rw [hcmdA s₂ i₂ hb]; exact hc2
        · have hcj1 : (A.prog s₁)[i₁]? = some (Cmd.sync bb n) := by
            rw [← hcmdfst s₁ i₁ ha]; exact hc1
          have hcj2 : (A.prog s₂)[i₂]? = some (Cmd.sync bb n) := by
            rw [← hcmdfst s₂ i₂ hb]; exact hc2
          rw [hgen s₁ i₁ _ bb n hcj1 rfl, hgen s₂ i₂ _ bb n hcj2 rfl, hg]
    · rintro (⟨_, _, heq⟩ | ⟨bb, n, _, _, hc1, hc2, hg⟩ | ⟨bb, n, _, _, hc1, hc2, hg⟩)
      · simp only [ProgPoint.mk.injEq] at heq
        obtain ⟨rfl, hidx⟩ := heq
        refine Or.inl ⟨hppA s₂ i₁ ha, ?_, ?_⟩
        · show i₁ + 1 < ((A.seq A rfl).prog s₂).length
          rw [hPlen]; omega
        · show (⟨s₂, i₂⟩ : ProgPoint) = ⟨s₂, i₁ + 1⟩
          exact congrArg (ProgPoint.mk s₂) (by omega)
      · have he1 : (A.seq A rfl).cmdAt ⟨s₁, i₁⟩ = some (Cmd.arrive bb n) := by
          rw [← hcmdA s₁ i₁ ha]; exact hc1
        have he2 : (A.seq A rfl).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb n) := by
          rw [← hcmdA s₂ i₂ hb]; exact hc2
        refine Or.inr (Or.inl ⟨bb, n, hppA s₁ i₁ ha, hppA s₂ i₂ hb, he1, he2, ?_⟩)
        have hcj1 : (A.prog s₁)[i₁]? = some (Cmd.arrive bb n) := by
          rw [← hcmdfst s₁ i₁ ha]; exact he1
        have hcj2 : (A.prog s₂)[i₂]? = some (Cmd.sync bb n) := by
          rw [← hcmdfst s₂ i₂ hb]; exact he2
        rw [hgen s₁ i₁ _ bb n hcj1 rfl, hgen s₂ i₂ _ bb n hcj2 rfl] at hg; omega
      · have he1 : (A.seq A rfl).cmdAt ⟨s₁, i₁⟩ = some (Cmd.sync bb n) := by
          rw [← hcmdA s₁ i₁ ha]; exact hc1
        have he2 : (A.seq A rfl).cmdAt ⟨s₂, i₂⟩ = some (Cmd.sync bb n) := by
          rw [← hcmdA s₂ i₂ hb]; exact hc2
        refine Or.inr (Or.inr ⟨bb, n, hppA s₁ i₁ ha, hppA s₂ i₂ hb, he1, he2, ?_⟩)
        have hcj1 : (A.prog s₁)[i₁]? = some (Cmd.sync bb n) := by
          rw [← hcmdfst s₁ i₁ ha]; exact he1
        have hcj2 : (A.prog s₂)[i₂]? = some (Cmd.sync bb n) := by
          rw [← hcmdfst s₂ i₂ hb]; exact he2
        rw [hgen s₁ i₁ _ bb n hcj1 rfl, hgen s₂ i₂ _ bb n hcj2 rfl] at hg; omega
  intro t₁ t₂ j₁ j₂ hj₁ hj₂
  -- **Confinement (A).** A happens-before path landing in the first batch stays in the first
  -- batch: no edge runs from the second batch back into the first (`seq_no_happensBefore`).
  have confA : ∀ (c : ProgPoint), happensBefore (A.seq A rfl) τ c ⟨t₂, j₂⟩ →
      c.idx < (A.prog c.thread).length →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A.seq A rfl) τ ∧
          x.idx < (A.prog x.thread).length ∧ y.idx < (A.prog y.thread).length) c ⟨t₂, j₂⟩ := by
    intro c hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxA
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyA : y.idx < (A.prog y.thread).length := by
        by_contra hcon
        exact hnoback ⟨y, ⟨t₂, j₂⟩, hyd, ⟨by omega, hypp.2⟩, hj₂⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxA, hyA⟩ (ih hyA)
  -- **Confinement (B).** A happens-before path leaving the second batch stays in the second
  -- batch (same fact, used from the other side).
  have confB : ∀ (c d : ProgPoint), happensBefore (A.seq A rfl) τ c d →
      (A.prog c.thread).length ≤ c.idx ∧
        c.idx < (A.prog c.thread).length + (A.prog c.thread).length →
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A.seq A rfl) τ ∧
          ((A.prog x.thread).length ≤ x.idx ∧
            x.idx < (A.prog x.thread).length + (A.prog x.thread).length) ∧
          ((A.prog y.thread).length ≤ y.idx ∧
            y.idx < (A.prog y.thread).length + (A.prog y.thread).length)) c d := by
    intro c d hcd
    induction hcd using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @head x y hxy hyd ih =>
      intro hxB
      obtain ⟨_, hypp, _⟩ := initRelation_cases hxy
      rw [mem_progPoints_iff, hPlen] at hypp
      have hyB : (A.prog y.thread).length ≤ y.idx ∧
          y.idx < (A.prog y.thread).length + (A.prog y.thread).length := by
        refine ⟨?_, hypp.2⟩
        by_contra hcon
        exact hnoback ⟨x, y, Relation.ReflTransGen.single hxy, hxB, by omega⟩
      exact Relation.ReflTransGen.head ⟨hxy, hxB, hyB⟩ (ih hyB)
  constructor
  · -- forward: confine to batch 1, shift edge-by-edge to batch 2, forget the confinement
    intro hHB
    have hB : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A.seq A rfl) τ ∧
          ((A.prog x.thread).length ≤ x.idx ∧
            x.idx < (A.prog x.thread).length + (A.prog x.thread).length) ∧
          ((A.prog y.thread).length ≤ y.idx ∧
            y.idx < (A.prog y.thread).length + (A.prog y.thread).length))
        ⟨t₁, (A.prog t₁).length + j₁⟩ ⟨t₂, (A.prog t₂).length + j₂⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, (A.prog η.thread).length + η.idx⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haA, hbA⟩ := hab
          dsimp only at haA hbA
          refine ⟨(hshift ⟨at', ai⟩ ⟨bt, bi⟩ haA hbA).mp hab',
            ⟨Nat.le_add_right _ _, ?_⟩, ⟨Nat.le_add_right _ _, ?_⟩⟩
          · show (A.prog at').length + ai < (A.prog at').length + (A.prog at').length
            omega
          · show (A.prog bt).length + bi < (A.prog bt).length + (A.prog bt).length
            omega)
        (confA ⟨t₁, j₁⟩ hHB hj₁)
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hB
  · -- backward: confine to batch 2, shift edge-by-edge back to batch 1
    intro hHB
    have hcb : (A.prog t₁).length ≤ (A.prog t₁).length + j₁ ∧
        (A.prog t₁).length + j₁ < (A.prog t₁).length + (A.prog t₁).length :=
      ⟨Nat.le_add_right _ _, by omega⟩
    have hA' : Relation.ReflTransGen
        (fun x y => (x, y) ∈ initRelation (A.seq A rfl) τ ∧
          x.idx < (A.prog x.thread).length ∧ y.idx < (A.prog y.thread).length)
        ⟨t₁, (A.prog t₁).length + j₁ - (A.prog t₁).length⟩
        ⟨t₂, (A.prog t₂).length + j₂ - (A.prog t₂).length⟩ :=
      Relation.ReflTransGen.lift
        (fun η => (⟨η.thread, η.idx - (A.prog η.thread).length⟩ : ProgPoint))
        (fun a b hab => by
          obtain ⟨at', ai⟩ := a; obtain ⟨bt, bi⟩ := b
          obtain ⟨hab', haB, hbB⟩ := hab
          dsimp only at haB hbB
          have hp1 : ai - (A.prog at').length < (A.prog at').length := by omega
          have hp2 : bi - (A.prog bt).length < (A.prog bt).length := by omega
          refine ⟨?_, hp1, hp2⟩
          rw [hshift ⟨at', ai - (A.prog at').length⟩ ⟨bt, bi - (A.prog bt).length⟩ hp1 hp2,
            show (A.prog at').length + (ai - (A.prog at').length) = ai by omega,
            show (A.prog bt).length + (bi - (A.prog bt).length) = bi by omega]
          exact hab')
        (confB ⟨t₁, (A.prog t₁).length + j₁⟩ ⟨t₂, (A.prog t₂).length + j₂⟩ hHB hcb)
    simp only [Nat.add_sub_cancel_left] at hA'
    exact Relation.ReflTransGen.mono (fun a b hab => hab.1) hA'

/-- **Lemma 4.2, conclusion 2 (across batches), three-batch case.** *Stated, not yet proved.*
This conclusion compares the happens-before edge running from batch `n` into batch `n + 1`
with the corresponding edge from batch `n - 1` into batch `n`. Those are *two distinct*
adjacent-batch pairs, so the simplest non-degenerate instance needs **three** consecutive
batches `I ^ k ⨾ I ^ k ⨾ I ^ k` (it cannot be expressed on only two): take `n = 1`, with the
middle batch `I_1^k`, its predecessor `I_0^k`, and its successor `I_2^k`.

With `L₁ = ((I ^ k).prog t₁).length` and `L₂ = ((I ^ k).prog t₂).length`, the claim is that the
edge from batch 1's copy of `⟨t₁, j₁⟩` (at index `L₁ + j₁`) into batch 2's copy of `⟨t₂, j₂⟩`
(at index `2 * L₂ + j₂`) holds exactly when the edge from batch 0's copy of `⟨t₁, j₁⟩`
(at index `j₁`) into batch 1's copy of `⟨t₂, j₂⟩` (at index `L₂ + j₂`) holds. -/
theorem CTA.WellSynchronized.second_batch_hb_across {I : CTA} (h : I.ConsistentArrivalCounts)
    {k : Nat} (hk : k = I.loopK h)
    (hWS0 : (I ^ k).WellSynchronized)
    (hWS1 : ((I ^ k).seq (I ^ k) rfl).WellSynchronized)
    (hWS2 : (((I ^ k).seq (I ^ k) rfl).seq (I ^ k) rfl).WellSynchronized) :
    ∃ τ, IsSuccessfulTraceFrom
        (Config.run State.initial (((I ^ k).seq (I ^ k) rfl).seq (I ^ k) rfl)) τ ∧
      ∀ (t₁ t₂ : ThreadId) (j₁ j₂ : Nat),
        j₁ < ((I ^ k).prog t₁).length → j₂ < ((I ^ k).prog t₂).length →
        (happensBefore (((I ^ k).seq (I ^ k) rfl).seq (I ^ k) rfl) τ
              ⟨t₁, ((I ^ k).prog t₁).length + j₁⟩
              ⟨t₂, 2 * ((I ^ k).prog t₂).length + j₂⟩
          ↔ happensBefore (((I ^ k).seq (I ^ k) rfl).seq (I ^ k) rfl) τ
              ⟨t₁, j₁⟩ ⟨t₂, ((I ^ k).prog t₂).length + j₂⟩) := by
  sorry

end Weft
