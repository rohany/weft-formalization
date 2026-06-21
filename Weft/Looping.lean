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

/-- **Theorem 1 (partial).** Let `k = I.loopK h` be the §1 iteration count (for a
consistency witness `h`). If `I ^ k` is run from a well-formed state `s` in which `b`
is unconfigured, then along any successful trace `τ` of `I ^ k` starting at `s`, every
barrier `b` used by `I ^ k` is recycled at least once — its generation increases by at
least one.

The hypotheses `hwf` (the start state is well-formed) and `hb0` (`b` has not yet been
touched) hold for free at the initial configuration (`WF_initial`, `State.initial`).
The argument is by contradiction: if `b` were never recycled, its *arrival potential*
(`barrierPotential_conservation`) pins the number of threads finally arrived at `b` to
`arrivers(I ^ k) b ≥ arrival-count(b)` (`arrivalCount_le_pow_arrivers`), while the
final `done` step's premise and the count-consistency invariant (`bcount_chain`) force
that number strictly below `arrival-count(b)` — a contradiction.
NOTE (rohany): This is an important, top-level theorem.
 -/
theorem Config.WellSynchronized.pow_barriers_advance {I : CTA}
    (h : I.ConsistentArrivalCounts) {s : State} {b : Barrier}
    (hwf : (Config.run s (I ^ I.loopK h)).WF)
    (hb0 : s.B b = BarrierState.unconfigured) {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run s (I ^ I.loopK h)) τ)
    (hb : b ∈ (I ^ I.loopK h).barrierSet) :
    1 ≤ recycleCount b τ (τ.length - 1) := by
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
  have hC₀pot : (Config.run s (I ^ k)).barrierPotential b = (I ^ k).arrivers b := by
    simp only [Config.barrierPotential, Config.arrivedLen, hb0, BarrierState.unconfigured,
      List.length_nil, Nat.zero_add, Config.barrierProgCount, CTA.arrivers]
  have hdonepot : (Config.done s_d).barrierPotential b = (s_d.B b).arrived.length := by
    simp [Config.barrierPotential, Config.arrivedLen, Config.barrierProgCount]
  rw [hdonepot, hC₀pot] at hcons
  have harr : nb ≤ (s_d.B b).arrived.length := by rw [hcons]; exact hstep2
  -- count consistency at `done s_d`
  have hbcount := bcount_chain hchain hhead
    (by intro n' hn'; simp [Config.bcount, hb0, BarrierState.unconfigured] at hn')
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
      have harr0 := (hwf_y.2 b (s_d.B b).synced (s_d.B b).arrived heq).2
      rw [harr0] at harr; simp at harr; omega
    · obtain ⟨n', hn'⟩ := Option.ne_none_iff_exists'.mp hcfg
      have heq : s_d.B b = ⟨(s_d.B b).synced, (s_d.B b).arrived, some n'⟩ := by rw [← hn']
      have hnn := hbcount n' (by simp only [Config.bcount]; exact hn')
      have hlt := (hwf_y.1 b (s_d.B b).synced (s_d.B b).arrived n' heq).1
      have hlt2 := hnofull b (s_d.B b).synced (s_d.B b).arrived n' heq
      omega

end Weft
