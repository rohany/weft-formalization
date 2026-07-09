/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.WellSynchronized
import Mathlib.Data.Finset.Sort

/-!
# The well-synchronization check with mbarriers (§5.2, Algorithm 2)

`CheckWellSynchronized` is the executable Algorithm 2 (`WellSync⁺`) of the
weft++ theorems document: given a CTA `T` and *one* concrete complete trace `τ`
that runs `(I, T)` to `done`, it returns a `Bool` that is `true` iff `T` is
well-synchronized (Definition 6), together with the computed happens-before
relation (the transitive closure of Algorithm 2 line 17).

As in the named-barrier check (Figure 4), the idea is to read the generation
map `Gen⁺(τ)` off the single concrete trace, build a static happens-before
relation `R` that every schedule must respect, close it transitively, and then
check that `R` already forces the orderings that make `Gen⁺` schedule-
independent. Algorithm 2 extends Figure 4 with the mbarrier edges and checks:

* **edges** — program order; `arrive_nb → sync_nb` (same barrier and count,
  equal generation); **`arrive_mb → wait_mb`** (same mbarrier, equal
  generation); `sync_nb ↔ sync_nb` (same barrier and count, equal generation,
  both directions). There are deliberately **no `wait ↔ wait` edges**: mbarrier
  waits of one generation need not resolve at the same instant (§5.2.4).
* **registrant check** (lines 19–22) — for registrants `c1 ∈ Reg(b, g)` and
  `c2 ∈ Reg(b, g+1)` with in-thread predecessor `c3 ; c2`, require
  `(c1, c3) ∈ R`: generation `g` completes before generation `g+1` starts.
  *Registrants* are the count-incrementing commands — `sync_nb`, `arrive_nb`,
  `arrive_mb` — Algorithm 2's `Reg`; note this already incorporates the fix
  applied to the named-barrier port (sources are *all* registering operations,
  not only `sync`s).
* **wait pinning** (lines 23–30) — for each `w ≡ wait_mb sb ph` of observed
  generation `g`: if `1 ≤ g`, `w` must have an in-thread predecessor `c3`
  (lines 25–26), and every registrant of `Reg(sb, g−1)` must happen-before
  `c3` (lines 27–28) — a lower bound: generation `g − 1` completes before `w`;
  and if the next generation *fills* (`|Reg(sb, g+1)| = n`, with `n` from the
  barrier's unique initialization), `w` must happen-before one of its
  registrants (lines 29–30, amended) — an upper bound pinning `w` before the
  completion of `g + 1`. A partial final generation never recycles, so it
  forces no ordering and the bound passes vacuously.
* **initialization ordering** (beyond Algorithm 2 as written) — every
  `init_mb sb _` must happen-before every *use* of `sb` (its `arrive_mb`s and
  `wait_mb`s): using an uninitialized mbarrier is an error, so a schedule that
  does not force a use after the initialization can err even though the
  witness trace succeeded.
* **unique initialization** (beyond Algorithm 2 as written; **temporary**) —
  each mbarrier has at most one `init_mb` in the whole CTA. Repeated
  initialization/destruction of an mbarrier is deliberately out of scope for
  now.

## Fixes carried over from the named-barrier port

* **Predecessor-less registrants reject** (the `c2.idx = 0` fix): a registrant
  of generation `g + 1` that is the *first* instruction of its thread has no
  predecessor `c3` on which to anchor the ordering; nothing forces it to wait
  for generation `g`, so a different schedule lands it in an earlier
  generation. Algorithm 2's line 19 loop silently skips such `c2`; the check
  rejects instead.
* **Reflexivity via the disjunct**: Algorithm 2 seeds `R` with the diagonal
  (line 8) because its checks read `R` as `≤`. The executable closure `hb`
  carries only the irreflexive part (a finite set cannot carry the diagonal of
  the infinite `ProgPoint`), so the registrant check and the wait lower bound
  accept `c1 = c3` (resp. `c = c3`) directly. The wait *upper* bound needs no
  such accommodation — a wait is never a registrant, so `w ≠ c⁺` always.

## Computable `Gen⁺(τ)` (`pointGen`)

`pointGen` turns `IsGenOf` into a function: `pointTime` locates the executing
step by remaining-program length (exactly as in the named-barrier check), the
recyclings of the command's barrier strictly before it are counted by
`recycleCount`, and `Cmd.genValue` applies §5.2.3's wait correction. Since
generations are `ℤ` with every value legitimate (waits can observe `−1`),
there is no sentinel: `pointGen` is `Option ℤ`-valued, `none` for a command
that never executes — mirroring `IsGenOf` exactly.
-/

namespace WeftMBarriers

export WeftCommon (transClosureStep transClosure mem_transClosure_imp_transGen
  mem_transClosure_of_transGen)

/-- The command at program point `η = ⟨i, k⟩`, read from `T`'s static programs:
command `k` of thread `i`, or `none` if out of range. Agrees with `η.cmd` at the
configuration `(I, T)`, since `(Config.run s T).progOf i = T.prog i`. -/
def CTA.cmdAt (T : CTA) (η : ProgPoint) : Option Cmd := (T.prog η.thread)[η.idx]?

/-- All program points of a CTA: every `⟨i, k⟩` with `i ∈ T.ids` and `k` a valid
index into thread `i`'s program. These are the "commands `c`" the algorithm ranges
over. -/
def CTA.progPoints (T : CTA) : List ProgPoint :=
  (T.ids.sort (· ≤ ·)).flatMap fun i =>
    (List.range (T.prog i).length).map fun k => ⟨i, k⟩

/-- `⟨i, k⟩` is a program point of `T` iff `i` is a thread and `k` indexes its
program. -/
theorem mem_progPoints_iff (T : CTA) (x : ProgPoint) :
    x ∈ T.progPoints ↔ x.thread ∈ T.ids ∧ x.idx < (T.prog x.thread).length := by
  unfold CTA.progPoints
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Finset.mem_sort]
  constructor
  · rintro ⟨i, hi, k, hk, rfl⟩; exact ⟨hi, hk⟩
  · rintro ⟨hi, hk⟩; exact ⟨x.thread, hi, x.idx, hk, rfl⟩

/-- A valid command index lands in `T.ids` (outside `ids` the program is empty). -/
theorem mem_ids_of_idx_lt (T : CTA) {i : ThreadId} {k : Nat}
    (h : k < (T.prog i).length) : i ∈ T.ids := by
  by_contra hni; rw [T.nil_outside_ids i hni] at h; simp at h

/-- If `T.cmdAt x` names a command, then `x` is a program point of `T`. -/
theorem mem_progPoints_of_cmdAt (T : CTA) {x : ProgPoint} {c : Cmd}
    (h : T.cmdAt x = some c) : x ∈ T.progPoints := by
  rw [CTA.cmdAt] at h
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
  exact (mem_progPoints_iff T x).2 ⟨mem_ids_of_idx_lt T hlt, hlt⟩

/-- The computable time `t(τ, η)` (Definition 3): the 1-indexed step of `τ` at
which `η = ⟨i, k⟩` executes, or `none` if it never does. Found by matching the
remaining-program *length* of thread `i` across consecutive configurations: the
step from `C` to `C'` runs `η` exactly when `C` still has the `|T.prog i| − k`-
length suffix and `C'` has the `(|T.prog i| − k − 1)`-length one. -/
def pointTime (T : CTA) (τ : List Config) (η : ProgPoint) : Option Nat :=
  let L := (T.prog η.thread).length
  if η.idx < L then
    (List.range (τ.length - 1)).findSome? fun j =>
      match τ[j]?, τ[j + 1]? with
      | some C, some C' =>
          if (C.progOf η.thread).length == L - η.idx
              && (C'.progOf η.thread).length == L - η.idx - 1 then
            some (j + 1)
          else
            none
      | _, _ => none
  else
    none

/-- The computable generation `Gen⁺(τ)(cη)` (Definition 5, §5.2.3), as a
function: for a synchronization command that executes at step `m`, `some` of
`Cmd.genValue` applied to the recyclings of its barrier strictly before `m`
(the §5.2.3 wait correction included); `none` for a command that never executes
or is not in `Gen`'s domain (`read`/`write`). Mirrors `IsGenOf`. -/
def pointGen (T : CTA) (τ : List Config) (η : ProgPoint) : Option ℤ :=
  match T.cmdAt η with
  | some c =>
      match c.barrier? with
      | some b =>
          match pointTime T τ η with
          | some m => some (c.genValue (recycleCount b τ (m - 1)))
          | none => none
      | none => none
  | none => none

/-- The *registrants* of Algorithm 2's `Reg`: the commands that increment a
barrier's registration count — `sync_nb`, `arrive_nb`, and `arrive_mb`. A
`wait_mb` blocks without registering, and `init_mb` configures without
registering; neither is a registrant. -/
def Cmd.isRegistrant : Cmd → Bool
  | .sync_nb .. | .arrive_nb .. | .arrive_mb .. => true
  | _ => false

/-- The registrant data of a program point: `some (b, g)` when `η`'s command is
a registrant (`Cmd.isRegistrant`) on barrier `b` that executes with generation
`g` in `τ`, and `none` otherwise (not a registrant, or never executes). This is
the membership function of Algorithm 2's `Reg`: `η ∈ Reg(b, g)` iff
`registrantGen T τ η = some (b, g)`. -/
def registrantGen (T : CTA) (τ : List Config) (η : ProgPoint) :
    Option ((NamedBarrier ⊕ SharedBarrier) × ℤ) :=
  match T.cmdAt η, pointGen T τ η with
  | some c, some g => if c.isRegistrant then c.barrier?.map fun b => (b, g) else none
  | _, _ => none

/-- The mbarrier a command *uses*: `some sb` for the arrivals and waits on
`sb`, and `none` otherwise. Initialization is not a use — it is what the uses
must be ordered after (`CheckWellSynchronized`'s initialization check). -/
def Cmd.usesMBarrier? : Cmd → Option SharedBarrier
  | .arrive_mb sb => some sb
  | .wait_mb sb _ => some sb
  | _ => none

/-- The arrival count of `sb`'s initialization: the `n` of the (unique, per
`CheckWellSynchronized`'s `okUniqueInit`) `init_mb sb n` in `T`, or `none` if
`sb` is never initialized. Used by the wait upper bound to decide whether a
next generation *fills* — a partial final generation forces no ordering. -/
def CTA.initCountOf (T : CTA) (sb : SharedBarrier) : Option ℕ+ :=
  T.progPoints.findSome? fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb' n) => if sb' = sb then some n else none
    | _ => none

/-- Step 1 of Algorithm 2 (lines 9–16): build the happens-before relation `R` as
a finite set of edges, using the generation map `G = pointGen T τ`.

* **lines 9–10** — intra-thread program order `⟨i, k⟩ → ⟨i, k+1⟩`;
* **lines 11–12** — `arrive_nb nb n → sync_nb nb n` of equal generation;
* **lines 13–14** — `arrive_mb sb → wait_mb sb ph` of equal generation (an
  mbarrier arrival happens-before the same-generation waits it releases);
* **lines 15–16** — `sync_nb nb n ↔ sync_nb nb n` of equal generation, both
  directions (named syncs of one generation all recycle together). There are
  no `wait ↔ wait` edges: mbarrier waits of one generation need not resolve
  simultaneously. -/
def initRelation (T : CTA) (τ : List Config) : Finset (ProgPoint × ProgPoint) :=
  let pts := T.progPoints
  let G : ProgPoint → Option ℤ := fun η => pointGen T τ η
  -- lines 9–10: program order `(c1 ; c2)`
  let progOrder : List (ProgPoint × ProgPoint) := pts.filterMap fun c =>
    if c.idx + 1 < (T.prog c.thread).length then some (c, ⟨c.thread, c.idx + 1⟩) else none
  -- lines 11–12: `arrive_nb nb n → sync_nb nb n` of the same generation
  let arriveSync : List (ProgPoint × ProgPoint) := pts.flatMap fun c1 =>
    match T.cmdAt c1 with
    | some (.arrive_nb b n) =>
        pts.filterMap fun c2 =>
          match T.cmdAt c2 with
          | some (.sync_nb b' n') =>
              if b = b' ∧ n = n' ∧ G c1 = G c2 then some (c1, c2) else none
          | _ => none
    | _ => []
  -- lines 13–14: `arrive_mb sb → wait_mb sb ph` of the same generation
  let arriveWait : List (ProgPoint × ProgPoint) := pts.flatMap fun c1 =>
    match T.cmdAt c1 with
    | some (.arrive_mb sb) =>
        pts.filterMap fun c2 =>
          match T.cmdAt c2 with
          | some (.wait_mb sb' _) =>
              if sb = sb' ∧ G c1 = G c2 then some (c1, c2) else none
          | _ => none
    | _ => []
  -- lines 15–16: `sync_nb nb n ↔ sync_nb nb n` of the same generation
  let syncSync : List (ProgPoint × ProgPoint) := pts.flatMap fun c1 =>
    match T.cmdAt c1 with
    | some (.sync_nb b n) =>
        pts.flatMap fun c2 =>
          match T.cmdAt c2 with
          | some (.sync_nb b' n') =>
              if b = b' ∧ n = n' ∧ G c1 = G c2 then [(c1, c2), (c2, c1)] else []
          | _ => []
    | _ => []
  (progOrder ++ arriveSync ++ arriveWait ++ syncSync).toFinset

/-- **Algorithm 2 (`WellSync⁺`).** Returns `(ok, hb)` where `ok = true` iff the
CTA `T` is well-synchronized (Definition 6), and `hb` is the computed
happens-before relation — the transitive closure (line 17) of the static edges
built from `Gen⁺(τ)`. (The relation is returned regardless of `ok`, e.g. for
downstream race-freedom analysis.)

`τ` is a concrete complete trace from `(I, T)` ending in `done` (the
algorithm's standing assumption — a `τ` that deadlocks or errors already
witnesses a violation and need not be checked).

The registrant check (lines 19–22) requires, for every registrant `c1` of
generation `g` on barrier `b` and every registrant `c2` of generation `g + 1`
on `b` with in-thread predecessor `c3`, that `hb` already orders `c1 ≤ c3`;
a predecessor-less such `c2` (`c2.idx = 0`) rejects outright (see the module
doc). The wait checks (lines 23–30) pin each `wait_mb`'s observed generation
from below (a generation `≥ 1` needs an in-thread predecessor, before which
every `Reg(sb, g−1)` registrant completes) and from above (the wait precedes
some next-generation registrant, when that generation fills). The
initialization check (beyond Algorithm 2 as written) requires every use of an
mbarrier to be ordered after its `init_mb`, and — a temporary restriction —
each mbarrier to be initialized by at most one `init_mb` in the whole CTA. -/
def CheckWellSynchronized (T : CTA) (τ : List Config) :
    Bool × Finset (ProgPoint × ProgPoint) :=
  -- Step 1 (lines 9–16): initialize R from the barrier generation counts.
  let R : Finset (ProgPoint × ProgPoint) := initRelation T τ
  -- Step 2 (line 17): the happens-before relation is the transitive closure of R.
  let hb : Finset (ProgPoint × ProgPoint) := transClosure R
  let G : ProgPoint → Option ℤ := fun η => pointGen T τ η
  -- Step 3 (lines 19–22): registrant pairs across consecutive generations.
  let okReg : Bool := T.progPoints.all fun c1 =>
    match registrantGen T τ c1 with
    | some (b, g) =>
        T.progPoints.all fun c2 =>
          if registrantGen T τ c2 = some (b, g + 1) then
            if 1 ≤ c2.idx then
              -- `c3 = ⟨c2.thread, c2.idx - 1⟩` is `c2`'s predecessor.
              -- The required ordering is the reflexive `c1 ≤ c3`; the
              -- `c1 = c3` disjunct accounts for reflexivity directly.
              decide (c1 = (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∨
                (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∈ hb)
            else
              -- a generation-`(g+1)` registrant with no in-thread
              -- predecessor: nothing anchors it after generation `g`.
              false
          else true
    | none => true
  -- Step 4 (lines 23–30): pin each wait's observed generation.
  let okWait : Bool := T.progPoints.all fun w =>
    match T.cmdAt w, G w with
    | some (.wait_mb sb _), some g =>
        -- lines 24–28: a wait observing generation `g ≥ 1` needs an in-thread
        -- predecessor `c3` (lines 25–26), and generation `g − 1` must complete
        -- before it: every registrant of `Reg(sb, g − 1)` happens-before `c3`
        -- (lines 27–28, the lower bound). As in the registrant check, `c3` may
        -- itself be the registrant (e.g. an `arrive_mb` immediately preceding
        -- the wait), so the reflexive `c = c3` disjunct is accepted directly.
        (decide (g < 1) ||
          (decide (1 ≤ w.idx) &&
            (T.progPoints.all fun c =>
              if registrantGen T τ c = some (.inr sb, g - 1) then
                decide (c = (⟨w.thread, w.idx - 1⟩ : ProgPoint) ∨
                  (c, (⟨w.thread, w.idx - 1⟩ : ProgPoint)) ∈ hb)
              else true))) &&
        -- lines 29–30 (amended): if the next generation *fills* — exactly `n`
        -- registrants, with `n` from the unique initialization — `w` must
        -- happen-before one of them (the upper bound; `w` is never a
        -- registrant, so no reflexivity accommodation is needed). A partial
        -- final generation forces no ordering: with fewer than `n`
        -- next-generation arrivals the `(g+2)`-th recycle never occurs, so `w`
        -- observes `g` regardless of the order.
        (let regNext : List ProgPoint := T.progPoints.filter fun cp =>
            registrantGen T τ cp = some (.inr sb, g + 1)
         match T.initCountOf sb with
         | some n =>
             if regNext.length = (n : Nat) then
               regNext.any fun cp => decide ((w, cp) ∈ hb)
             else true
         | none => true)
    | _, _ => true
  -- Step 5 (beyond Algorithm 2): every use of an mbarrier happens-after its
  -- initialization, anchored at the use's *in-thread predecessor*. An
  -- uninitialized `arrive_mb`/`wait_mb` is an error, and a thread errs the
  -- moment its control *reaches* the use with the barrier uninitialized — so
  -- the initialization must be forced before the point that gates the use,
  -- namely its predecessor `c3 = ⟨u.thread, u.idx − 1⟩` (the reflexive
  -- `ci = c3` disjunct accommodates an `init_mb` immediately preceding the
  -- use in the same thread). Anchoring at the use itself is *unsound*: an
  -- `hb`-path into `u` may route through an `arrive_mb → wait_mb` release
  -- edge, which does not gate `u`'s thread from reaching `u` early and
  -- erring. A use with no in-thread predecessor is reachable at the initial
  -- configuration — where every mbarrier is uninitialized — and rejects.
  let okInit : Bool := T.progPoints.all fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb _) =>
        T.progPoints.all fun u =>
          if (T.cmdAt u).bind Cmd.usesMBarrier? = some sb then
            if 1 ≤ u.idx then
              decide (ci = (⟨u.thread, u.idx - 1⟩ : ProgPoint) ∨
                (ci, (⟨u.thread, u.idx - 1⟩ : ProgPoint)) ∈ hb)
            else
              false
          else true
    | _ => true
  -- TEMPORARY (to be revisited): each mbarrier is initialized by at most *one*
  -- `init_mb` in the whole CTA — any two initializations of the same barrier
  -- must be the same program point. Repeated initialization/destruction cycles
  -- of an mbarrier are deliberately not handled yet; this restriction keeps a
  -- barrier's `init_mb` unique so the initialization-ordering check above pins
  -- every use against a single initialization.
  let okUniqueInit : Bool := T.progPoints.all fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb _) =>
        T.progPoints.all fun cj =>
          match T.cmdAt cj with
          | some (.init_mb sb' _) => if sb = sb' then decide (ci = cj) else true
          | _ => true
    | _ => true
  (okReg && okWait && okInit && okUniqueInit, hb)

/-- The happens-before relation of Algorithm 2, as a *relation* on program
points (the object Definition 4 talks about), rather than the executable
`Finset` returned by `CheckWellSynchronized`: the **reflexive**-transitive
closure of the static edge set `initRelation T τ`, via the canonical
`Relation.ReflTransGen`. As in the named-barrier development, the executable
`(CheckWellSynchronized T τ).2 = transClosure (initRelation T τ)` is the
irreflexive `Relation.TransGen` part; this adds the diagonal back. -/
def happensBefore (T : CTA) (τ : List Config) : ProgPoint → ProgPoint → Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ initRelation T τ)

/-- `pointTime` computes the time `t(τ, η)`: if `η` executes at step `m` in a
complete trace from `(I, T)`, then `pointTime T τ η = some m`. (The matcher returns
`some` only at genuine execution steps — `hfwd`, by suffix uniqueness of the
remaining program — and there is one, at `m - 1`; uniqueness of time pins the
`findSome?` result to `m`.) -/
theorem pointTime_eq_of_isTimeOf {T : CTA} {s : State} {τ : List Config} {η : ProgPoint}
    {m : Nat} (hexec : IsTimeOf (Config.run s T) τ η m) : pointTime T τ η = some m := by
  have hτ := hexec.1
  have hidxL : η.idx < (T.prog η.thread).length := hexec.2.1
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run s T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hC₀ : (Config.run s T).progOf η.thread = T.prog η.thread := rfl
  set f : Nat → Option Nat := fun j =>
    match τ[j]?, τ[j + 1]? with
    | some C, some C' =>
        if (C.progOf η.thread).length == (T.prog η.thread).length - η.idx
            && (C'.progOf η.thread).length == (T.prog η.thread).length - η.idx - 1 then
          some (j + 1) else none
    | _, _ => none with hf
  have hfwd : ∀ a x, f a = some x → IsTimeOf (Config.run s T) τ η x := by
    intro a x hfa
    simp only [hf] at hfa
    rcases hCa : τ[a]? with _ | C₁
    · simp [hCa] at hfa
    · rcases hCa1 : τ[a + 1]? with _ | C₂
      · simp [hCa, hCa1] at hfa
      · simp only [hCa, hCa1] at hfa
        split at hfa
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨hl1, hl2⟩ := hcond
          rw [Option.some.injEq] at hfa; subst hfa
          refine ⟨hτ, hidxL, a, C₁, C₂, rfl, hCa, hCa1, ?_, ?_⟩
          · have heq := List.IsSuffix.eq_drop
              (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le a) hCa)
            rw [hl1, hC₀] at heq
            rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
              by omega] at heq
          · have heq := List.IsSuffix.eq_drop
              (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le (a + 1)) hCa1)
            rw [hl2, hC₀] at heq
            rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx - 1)
              = η.idx + 1 by omega] at heq
        · simp at hfa
  have hex2 := hexec
  obtain ⟨_, _, j, C, C', hm, hCj, hCj1, hCeq, hC'eq⟩ := hex2
  have hj1lt : j + 1 < τ.length := (List.getElem?_eq_some_iff.mp hCj1).1
  have hfj : f j = some (j + 1) := by
    simp only [hf, hCj, hCj1]
    have h1 : (C.progOf η.thread).length = (T.prog η.thread).length - η.idx := by
      rw [hCeq, hC₀, List.length_drop]
    have h2 : (C'.progOf η.thread).length = (T.prog η.thread).length - η.idx - 1 := by
      rw [hC'eq, hC₀, List.length_drop]; omega
    rw [h1, h2]; simp
  have hpt : pointTime T τ η = (List.range (τ.length - 1)).findSome? f := by
    simp only [pointTime, hidxL, if_true, ← hf]
  rw [hpt]
  have hjmem : j ∈ List.range (τ.length - 1) := List.mem_range.mpr (by omega)
  have hne : (List.range (τ.length - 1)).findSome? f ≠ none := by
    rw [Ne, List.findSome?_eq_none_iff]
    push Not
    exact ⟨j, hjmem, by rw [hfj]; simp⟩
  obtain ⟨m'', hm''⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hm'']
  rw [List.findSome?_eq_some_iff] at hm''
  obtain ⟨_, a, _, _, hfa, _⟩ := hm''
  rw [IsTimeOf.unique (hfwd a m'' hfa) hexec]

/-- **Program order is respected in time**: in any complete trace, instruction
`a` of a thread executes no later than the next instruction of the same thread. -/
theorem progOrder_time_le {C₀ : Config} {τ' : List Config} {a : ProgPoint} {n₁ n₂ : Nat}
    (h₁ : IsTimeOf C₀ τ' a n₁)
    (h₂ : IsTimeOf C₀ τ' ⟨a.thread, a.idx + 1⟩ n₂) : n₁ ≤ n₂ := by
  obtain ⟨hτ, _, j, C, _C', hm₁, hCj, _, hCeq, _⟩ := h₁
  obtain ⟨_, hlt₂, j', _D, D', hm₂, _, hDj1, _, hD'eq⟩ := h₂
  subst hm₁; subst hm₂
  have hchain := hτ.1.subtrace
  have hCe : C.progOf a.thread = (C₀.progOf a.thread).drop a.idx := hCeq
  have hD'e : D'.progOf a.thread = (C₀.progOf a.thread).drop (a.idx + 1 + 1) := hD'eq
  have hlt₂' : a.idx + 1 < (C₀.progOf a.thread).length := hlt₂
  by_contra hcon
  have hji : j' + 1 ≤ j := by omega
  have hsuf := progOf_suffix_index_le hchain a.thread hDj1 hji hCj
  have hle := suffix_length_le hsuf
  rw [hCe, hD'e, List.length_drop, List.length_drop] at hle
  omega

/-- The computable `pointGen` *is* the generation: for a barrier command `a` that
executes in `τ`, `IsGenOf (I, T) τ a (pointGen T τ a)` holds. -/
theorem isGenOf_pointGen {T : CTA} {τ : List Config} {a : ProgPoint} {c : Cmd}
    {b : NamedBarrier ⊕ SharedBarrier} {ma : Nat}
    (hc : T.cmdAt a = some c) (hb : c.barrier? = some b)
    (hma : IsTimeOf (Config.run State.initial T) τ a ma) :
    IsGenOf (Config.run State.initial T) τ a (pointGen T τ a) := by
  have hpt : pointTime T τ a = some ma := pointTime_eq_of_isTimeOf hma
  have hpg : pointGen T τ a = some (c.genValue (recycleCount b τ (ma - 1))) := by
    simp only [pointGen, hc, hb, hpt]
  rw [hpg]
  exact ⟨hma.1, c, hc, b, hb, Or.inl ⟨ma, hma, rfl⟩⟩

/-- Classification of `initRelation` edges. Both endpoints are program points,
and the edge is intra-thread program order, a named-barrier edge (the target a
`sync_nb`, the source a same-barrier named operation, equal generations), or an
mbarrier edge (the target a `wait_mb`, the source a same-barrier `arrive_mb`,
equal generations). -/
theorem initRelation_cases {T : CTA} {τ : List Config} {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) :
    a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
    (b = ⟨a.thread, a.idx + 1⟩ ∨
      (∃ nb n, T.cmdAt b = some (.sync_nb nb n) ∧
        (T.cmdAt a).bind Cmd.barrier? = some (.inl nb) ∧
        pointGen T τ a = pointGen T τ b) ∨
      (∃ sb ph, T.cmdAt b = some (.wait_mb sb ph) ∧
        T.cmdAt a = some (.arrive_mb sb) ∧
        pointGen T τ a = pointGen T τ b)) := by
  simp only [initRelation, List.mem_toFinset, List.mem_append] at hedge
  rcases hedge with ((hpo | has) | haw) | hss
  · -- program order
    simp only [List.mem_filterMap] at hpo
    obtain ⟨c, hc, hceq⟩ := hpo
    split at hceq
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hceq
      obtain ⟨rfl, rfl⟩ := hceq
      have hth : c.thread ∈ T.ids := ((mem_progPoints_iff T c).mp hc).1
      exact ⟨hc, (mem_progPoints_iff T _).mpr ⟨hth, hcond⟩, Or.inl rfl⟩
    · exact absurd hceq (by simp)
  · -- arrive_nb → sync_nb
    simp only [List.mem_flatMap] at has
    obtain ⟨c1, hc1, hin⟩ := has
    cases hcmd1 : T.cmdAt c1 with
    | none => simp [hcmd1] at hin
    | some cmd1 =>
      cases cmd1 with
      | read g => simp [hcmd1] at hin
      | write g => simp [hcmd1] at hin
      | sync_nb nb n => simp [hcmd1] at hin
      | init_mb sb n => simp [hcmd1] at hin
      | arrive_mb sb => simp [hcmd1] at hin
      | wait_mb sb ph => simp [hcmd1] at hin
      | arrive_nb nb n =>
        simp only [hcmd1, List.mem_filterMap] at hin
        obtain ⟨c2, hc2, hc2eq⟩ := hin
        cases hcmd2 : T.cmdAt c2 with
        | none => simp [hcmd2] at hc2eq
        | some cmd2 =>
          cases cmd2 with
          | read g => simp [hcmd2] at hc2eq
          | write g => simp [hcmd2] at hc2eq
          | arrive_nb nb' n' => simp [hcmd2] at hc2eq
          | init_mb sb n' => simp [hcmd2] at hc2eq
          | arrive_mb sb => simp [hcmd2] at hc2eq
          | wait_mb sb ph => simp [hcmd2] at hc2eq
          | sync_nb nb' n' =>
            simp only [hcmd2] at hc2eq
            split at hc2eq
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
              obtain ⟨rfl, rfl⟩ := hc2eq
              obtain ⟨hbb, _, hgen⟩ := hcond
              refine ⟨hc1, hc2, Or.inr (Or.inl ⟨nb', n', hcmd2, ?_, hgen⟩)⟩
              rw [hcmd1]
              simp [Cmd.barrier?, hbb]
            · exact absurd hc2eq (by simp)
  · -- arrive_mb → wait_mb
    simp only [List.mem_flatMap] at haw
    obtain ⟨c1, hc1, hin⟩ := haw
    cases hcmd1 : T.cmdAt c1 with
    | none => simp [hcmd1] at hin
    | some cmd1 =>
      cases cmd1 with
      | read g => simp [hcmd1] at hin
      | write g => simp [hcmd1] at hin
      | arrive_nb nb n => simp [hcmd1] at hin
      | sync_nb nb n => simp [hcmd1] at hin
      | init_mb sb n => simp [hcmd1] at hin
      | wait_mb sb ph => simp [hcmd1] at hin
      | arrive_mb sb =>
        simp only [hcmd1, List.mem_filterMap] at hin
        obtain ⟨c2, hc2, hc2eq⟩ := hin
        cases hcmd2 : T.cmdAt c2 with
        | none => simp [hcmd2] at hc2eq
        | some cmd2 =>
          cases cmd2 with
          | read g => simp [hcmd2] at hc2eq
          | write g => simp [hcmd2] at hc2eq
          | arrive_nb nb' n' => simp [hcmd2] at hc2eq
          | sync_nb nb' n' => simp [hcmd2] at hc2eq
          | init_mb sb' n' => simp [hcmd2] at hc2eq
          | arrive_mb sb' => simp [hcmd2] at hc2eq
          | wait_mb sb' ph =>
            simp only [hcmd2] at hc2eq
            split at hc2eq
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
              obtain ⟨rfl, rfl⟩ := hc2eq
              obtain ⟨hbb, hgen⟩ := hcond
              refine ⟨hc1, hc2, Or.inr (Or.inr ⟨sb', ph, hcmd2, ?_, hgen⟩)⟩
              rw [hcmd1, hbb]
            · exact absurd hc2eq (by simp)
  · -- sync_nb ↔ sync_nb
    simp only [List.mem_flatMap] at hss
    obtain ⟨c1, hc1, hin⟩ := hss
    cases hcmd1 : T.cmdAt c1 with
    | none => simp [hcmd1] at hin
    | some cmd1 =>
      cases cmd1 with
      | read g => simp [hcmd1] at hin
      | write g => simp [hcmd1] at hin
      | arrive_nb nb n => simp [hcmd1] at hin
      | init_mb sb n => simp [hcmd1] at hin
      | arrive_mb sb => simp [hcmd1] at hin
      | wait_mb sb ph => simp [hcmd1] at hin
      | sync_nb nb n =>
        simp only [hcmd1, List.mem_flatMap] at hin
        obtain ⟨c2, hc2, hin2⟩ := hin
        cases hcmd2 : T.cmdAt c2 with
        | none => simp [hcmd2] at hin2
        | some cmd2 =>
          cases cmd2 with
          | read g => simp [hcmd2] at hin2
          | write g => simp [hcmd2] at hin2
          | arrive_nb nb' n' => simp [hcmd2] at hin2
          | init_mb sb' n' => simp [hcmd2] at hin2
          | arrive_mb sb' => simp [hcmd2] at hin2
          | wait_mb sb' ph => simp [hcmd2] at hin2
          | sync_nb nb' n' =>
            simp only [hcmd2] at hin2
            split at hin2
            · rename_i hcond
              obtain ⟨hbb, _, hgen⟩ := hcond
              simp only [List.mem_cons, List.not_mem_nil, or_false,
                Prod.mk.injEq] at hin2
              rcases hin2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · refine ⟨hc1, hc2, Or.inr (Or.inl ⟨nb', n', hcmd2, ?_, hgen⟩)⟩
                rw [hcmd1]
                simp [Cmd.barrier?, hbb]
              · refine ⟨hc2, hc1, Or.inr (Or.inl ⟨nb, n, hcmd1, ?_, hgen.symm⟩)⟩
                rw [hcmd2]
                simp [Cmd.barrier?, hbb]
            · simp at hin2

/-- Per-edge soundness (the core semantic content). Each edge of `initRelation T τ`
is a genuine ordering in every complete trace from `(I, T)`:

* **program-order** edges — no out-of-order execution within a thread;
* **named-barrier** edges (`arrive_nb → sync_nb`, `sync_nb ↔ sync_nb`, equal
  generation) — well-synchronization fixes both generations across traces, and
  the target `sync_nb`'s step *is* its barrier's recycle, which would out-run
  the shared recycle count if it came first;
* **mbarrier** edges (`arrive_mb → wait_mb`, equal generation) — with a matched
  phase the wait is a woken block, whose step is a recycle (the pass case is
  refuted by the phase invariant), and the sync argument applies; with a
  mismatched phase the wait observes `r − 1`, so its position has strictly more
  recycles before it than the arrival's, and monotonicity orders the times. -/
theorem initRelation_edge_sound {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) :
    ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' a n₁ →
        IsTimeOf (Config.run State.initial T) τ' b n₂ → n₁ ≤ n₂ := by
  intro τ' hτ' n₁ n₂ ht₁ ht₂
  obtain ⟨ha, hb, hcase⟩ := initRelation_cases hedge
  rcases hcase with hpo | ⟨nb, nn, hbsync, habar, hgen⟩ | ⟨sb, ph, hbwait, hacmd, hgen⟩
  · -- program order
    subst hpo; exact progOrder_time_le ht₁ ht₂
  · -- named-barrier edge
    obtain ⟨sd, hdone⟩ := hτ.2
    have hma : ∃ n, IsTimeOf (Config.run State.initial T) τ a n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T a).mp ha).2
    have hmb : ∃ n, IsTimeOf (Config.run State.initial T) τ b n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T b).mp hb).2
    obtain ⟨ca, hca, hcabar⟩ : ∃ ca, T.cmdAt a = some ca ∧
        ca.barrier? = some (.inl nb) := by
      cases hcm : T.cmdAt a with
      | none => rw [hcm] at habar; exact absurd habar (by simp)
      | some ca => rw [hcm] at habar; exact ⟨ca, rfl, habar⟩
    have hbbar : (T.cmdAt b).bind Cmd.barrier? = some (.inl nb) := by rw [hbsync]; rfl
    have hgenA := isGenOf_pointGen hca hcabar hma.choose_spec
    have hgenB := isGenOf_pointGen hbsync
      (show (Cmd.sync_nb nb nn).barrier? = some (.inl nb) from rfl) hmb.choose_spec
    obtain ⟨ga, hgaτ, hgaτ'⟩ := hws.2 τ τ' hτ.1 hτ' a ⟨.inl nb, habar⟩
    obtain ⟨gb, hgbτ, hgbτ'⟩ := hws.2 τ τ' hτ.1 hτ' b ⟨.inl nb, hbbar⟩
    have hgab : ga = gb := Option.some.inj
      ((IsGenOf.unique hgaτ hgenA).trans (hgen.trans (IsGenOf.unique hgbτ hgenB).symm))
    have hva : ga = ca.genValue (recycleCount (.inl nb) τ' (n₁ - 1)) :=
      isGenOf_genValue hgaτ' hca hcabar ht₁
    have hvb : gb = (Cmd.sync_nb nb nn).genValue (recycleCount (.inl nb) τ' (n₂ - 1)) :=
      isGenOf_genValue hgbτ' hbsync rfl ht₂
    rw [Cmd.genValue_of_inl hcabar] at hva
    rw [Cmd.genValue_of_inl (show (Cmd.sync_nb nb nn).barrier? = some (.inl nb)
      from rfl)] at hvb
    by_contra hcon
    have hn2 : 1 ≤ n₂ := by obtain ⟨_, _, j, _, _, h, _⟩ := ht₂; omega
    obtain ⟨Cb, Cb', hCb, hCb', hrec⟩ := sync_time_recycles ht₂ hbsync
    have hCb2 : τ'[n₂ - 1 + 1]? = some Cb' := by
      rw [show n₂ - 1 + 1 = n₂ by omega]; exact hCb'
    have hsucc : recycleCount (.inl nb) τ' n₂
        = recycleCount (.inl nb) τ' (n₂ - 1) + 1 := by
      have h := recycleCount_succ_of_recycle _ τ' hCb hCb2 hrec
      rwa [show n₂ - 1 + 1 = n₂ by omega] at h
    have hmono : recycleCount (.inl nb) τ' n₂ ≤ recycleCount (.inl nb) τ' (n₁ - 1) :=
      recycleCount_mono _ τ' (by omega)
    have hr : (recycleCount (.inl nb) τ' (n₁ - 1) : ℤ)
        = (recycleCount (.inl nb) τ' (n₂ - 1) : ℤ) := by
      rw [← hva, hgab, hvb]
    have hrn : recycleCount (.inl nb) τ' (n₁ - 1)
        = recycleCount (.inl nb) τ' (n₂ - 1) := by exact_mod_cast hr
    omega
  · -- mbarrier edge: `a ≡ arrive_mb sb`, `b ≡ wait_mb sb ph`
    obtain ⟨sd, hdone⟩ := hτ.2
    have hma : ∃ n, IsTimeOf (Config.run State.initial T) τ a n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T a).mp ha).2
    have hmb : ∃ n, IsTimeOf (Config.run State.initial T) τ b n :=
      exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T b).mp hb).2
    have habar : (T.cmdAt a).bind Cmd.barrier? = some (.inr sb) := by rw [hacmd]; rfl
    have hbbar : (T.cmdAt b).bind Cmd.barrier? = some (.inr sb) := by rw [hbwait]; rfl
    have hgenA := isGenOf_pointGen hacmd
      (show (Cmd.arrive_mb sb).barrier? = some (.inr sb) from rfl) hma.choose_spec
    have hgenB := isGenOf_pointGen hbwait
      (show (Cmd.wait_mb sb ph).barrier? = some (.inr sb) from rfl) hmb.choose_spec
    obtain ⟨ga, hgaτ, hgaτ'⟩ := hws.2 τ τ' hτ.1 hτ' a ⟨.inr sb, habar⟩
    obtain ⟨gb, hgbτ, hgbτ'⟩ := hws.2 τ τ' hτ.1 hτ' b ⟨.inr sb, hbbar⟩
    have hgab : ga = gb := Option.some.inj
      ((IsGenOf.unique hgaτ hgenA).trans (hgen.trans (IsGenOf.unique hgbτ hgenB).symm))
    have hva : ga = (Cmd.arrive_mb sb).genValue (recycleCount (.inr sb) τ' (n₁ - 1)) :=
      isGenOf_genValue hgaτ' hacmd rfl ht₁
    have hvb : gb = (Cmd.wait_mb sb ph).genValue (recycleCount (.inr sb) τ' (n₂ - 1)) :=
      isGenOf_genValue hgbτ' hbwait rfl ht₂
    have hva' : ga = (recycleCount (.inr sb) τ' (n₁ - 1) : ℤ) := hva
    by_contra hcon
    have hn2 : 1 ≤ n₂ := by obtain ⟨_, _, j, _, _, h, _⟩ := ht₂; omega
    by_cases hph : phaseAfter (recycleCount (.inr sb) τ' (n₂ - 1)) = ph
    · -- matched phase: the wait is a woken block, its step recycles `sb`
      have hvb' : gb = (recycleCount (.inr sb) τ' (n₂ - 1) : ℤ) := by
        rw [hvb]; simp [Cmd.genValue, hph]
      rcases wait_time_recycles_or_pass ht₂ hbwait with
        ⟨Cb, Cb', hCb, hCb', hrec⟩ | ⟨sp, Tp, hCp, -, hphase⟩
      · have hCb2 : τ'[n₂ - 1 + 1]? = some Cb' := by
          rw [show n₂ - 1 + 1 = n₂ by omega]; exact hCb'
        have hsucc : recycleCount (.inr sb) τ' n₂
            = recycleCount (.inr sb) τ' (n₂ - 1) + 1 := by
          have h := recycleCount_succ_of_recycle _ τ' hCb hCb2 hrec
          rwa [show n₂ - 1 + 1 = n₂ by omega] at h
        have hmono : recycleCount (.inr sb) τ' n₂
            ≤ recycleCount (.inr sb) τ' (n₁ - 1) :=
          recycleCount_mono _ τ' (by omega)
        have hr : (recycleCount (.inr sb) τ' (n₁ - 1) : ℤ)
            = (recycleCount (.inr sb) τ' (n₂ - 1) : ℤ) := by
          rw [← hva', hgab, hvb']
        have hrn : recycleCount (.inr sb) τ' (n₁ - 1)
            = recycleCount (.inr sb) τ' (n₂ - 1) := by exact_mod_cast hr
        omega
      · -- the pass case contradicts the phase invariant
        have hchain' : List.IsChain CTAStep τ' := hτ'.1.subtrace
        have h0' : τ'[0]? = some (Config.run State.initial T) := by
          have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
          rw [hgen0]; exact hτ'.2
        have hinv := phase_eq_phaseAfter hchain' h0' sb (n₂ - 1)
          (Config.run sp Tp) sp hCp rfl
        rw [hinv] at hphase
        exact hphase hph
    · -- mismatched phase: the wait observes `r₂ − 1`, so `r₂ = r₁ + 1`
      have hvb' : gb = (recycleCount (.inr sb) τ' (n₂ - 1) : ℤ) - 1 := by
        rw [hvb]; simp [Cmd.genValue, hph]
      have hr : (recycleCount (.inr sb) τ' (n₁ - 1) : ℤ)
          = (recycleCount (.inr sb) τ' (n₂ - 1) : ℤ) - 1 := by
        rw [← hva', hgab, hvb']
      have hmono : recycleCount (.inr sb) τ' (n₂ - 1)
          ≤ recycleCount (.inr sb) τ' (n₁ - 1) :=
        recycleCount_mono _ τ' (by omega)
      omega

/-- Every `initRelation` edge whose target executes has an executing source: a
program-order predecessor has already run when its successor runs, and a
barrier-edge source is a synchronization command, which well-synchronization
forces to execute in every complete trace. -/
theorem initRelation_src_timed {T : CTA} {τ : List Config}
    (hws : T.WellSynchronized) {a b : ProgPoint}
    (hedge : (a, b) ∈ initRelation T τ) {τ' : List Config}
    (hτ' : IsCompleteTraceFrom (Config.run State.initial T) τ')
    {n₂ : Nat} (ht₂ : IsTimeOf (Config.run State.initial T) τ' b n₂) :
    ∃ n, IsTimeOf (Config.run State.initial T) τ' a n := by
  obtain ⟨ha, hbmem, hcase⟩ := initRelation_cases hedge
  rcases hcase with hpo | ⟨nb, nn, hbsync, habar, -⟩ | ⟨sb, ph, hbwait, hacmd, -⟩
  · -- program order: when the successor ran, the program had already dropped
    -- past the predecessor
    subst hpo
    obtain ⟨_, hlt, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := ht₂
    refine exists_time_of_progOf_lt hτ' ((mem_progPoints_iff T a).mp ha).2 hCj1 ?_
    have hC'e : C'.progOf a.thread =
        ((Config.run State.initial T).progOf a.thread).drop (a.idx + 1 + 1) := hC'eq
    have hlt' : a.idx + 1 < ((Config.run State.initial T).progOf a.thread).length := hlt
    rw [hC'e, List.length_drop]
    omega
  · -- named-barrier edge source: a synchronization command, forced to execute
    obtain ⟨g, hgτ', -⟩ := hws.2 τ' τ' hτ' hτ' a ⟨.inl nb, habar⟩
    obtain ⟨-, c, -, bb, -, hcase2⟩ := hgτ'
    rcases hcase2 with ⟨m, hm, -⟩ | ⟨hnone, -⟩
    · exact ⟨m, hm⟩
    · exact absurd hnone (by simp)
  · -- mbarrier edge source: same argument
    have habar : (T.cmdAt a).bind Cmd.barrier? = some (.inr sb) := by rw [hacmd]; rfl
    obtain ⟨g, hgτ', -⟩ := hws.2 τ' τ' hτ' hτ' a ⟨.inr sb, habar⟩
    obtain ⟨-, c, -, bb, -, hcase2⟩ := hgτ'
    rcases hcase2 with ⟨m, hm, -⟩ | ⟨hnone, -⟩
    · exact ⟨m, hm⟩
    · exact absurd hnone (by simp)

/-! ## Completeness extraction

Boolean decodes of the four checker conjuncts: a `false` result exhibits a
concrete failing witness. These support `not_wellSynchronized_of_check_false`.
-/

/-! ### Proof-side names for the checker's conjuncts

`CheckWellSynchronized` above is a verbatim transcription of Algorithm 2 — its
four checks are `let`-bound inside the definition, exactly as presented. The
definitions below are **proof scaffolding only**: definitionally equal copies
of those `let`-bindings (the `fst_checkWellSynchronized` bridge is `rfl`),
giving the extraction lemmas names to decompose a failing check by. They are
not part of the algorithm. -/

/-- Proof-side name for Step 3 (lines 19–22), the registrant check. Not part of
the algorithm — see the section doc. -/
def okRegCheck (T : CTA) (τ : List Config) : Bool :=
  T.progPoints.all fun c1 =>
    match registrantGen T τ c1 with
    | some (b, g) =>
        T.progPoints.all fun c2 =>
          if registrantGen T τ c2 = some (b, g + 1) then
            if 1 ≤ c2.idx then
              decide (c1 = (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∨
                (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∈
                  transClosure (initRelation T τ))
            else
              false
          else true
    | none => true

/-- Proof-side name for Step 4 (lines 23–30), the wait checks. Not part of the
algorithm — see the section doc. -/
def okWaitCheck (T : CTA) (τ : List Config) : Bool :=
  T.progPoints.all fun w =>
    match T.cmdAt w, pointGen T τ w with
    | some (.wait_mb sb _), some g =>
        (decide (g < 1) ||
          (decide (1 ≤ w.idx) &&
            (T.progPoints.all fun c =>
              if registrantGen T τ c = some (.inr sb, g - 1) then
                decide (c = (⟨w.thread, w.idx - 1⟩ : ProgPoint) ∨
                  (c, (⟨w.thread, w.idx - 1⟩ : ProgPoint)) ∈
                    transClosure (initRelation T τ))
              else true))) &&
        (let regNext : List ProgPoint := T.progPoints.filter fun cp =>
            registrantGen T τ cp = some (.inr sb, g + 1)
         match T.initCountOf sb with
         | some n =>
             if regNext.length = (n : Nat) then
               regNext.any fun cp => decide ((w, cp) ∈ transClosure (initRelation T τ))
             else true
         | none => true)
    | _, _ => true

/-- Proof-side name for Step 5, the initialization-ordering check. Not part of
the algorithm — see the section doc. -/
def okInitCheck (T : CTA) (τ : List Config) : Bool :=
  T.progPoints.all fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb _) =>
        T.progPoints.all fun u =>
          if (T.cmdAt u).bind Cmd.usesMBarrier? = some sb then
            if 1 ≤ u.idx then
              decide (ci = (⟨u.thread, u.idx - 1⟩ : ProgPoint) ∨
                (ci, (⟨u.thread, u.idx - 1⟩ : ProgPoint)) ∈
                  transClosure (initRelation T τ))
            else
              false
          else true
    | _ => true

/-- Proof-side name for the (temporary) unique-initialization check. Not part
of the algorithm — see the section doc. -/
def okUniqueInitCheck (T : CTA) (_τ : List Config) : Bool :=
  T.progPoints.all fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb _) =>
        T.progPoints.all fun cj =>
          match T.cmdAt cj with
          | some (.init_mb sb' _) => if sb = sb' then decide (ci = cj) else true
          | _ => true
    | _ => true

/-- The definitional bridge: the algorithm's verdict is the conjunction of the
four proof-side checks. Holds by `rfl` — the scaffolding definitions are exact
copies of the algorithm's `let`-bindings. -/
theorem fst_checkWellSynchronized (T : CTA) (τ : List Config) :
    (CheckWellSynchronized T τ).1 = (okRegCheck T τ && okWaitCheck T τ
      && okInitCheck T τ && okUniqueInitCheck T τ) := rfl

/-- `(CheckWellSynchronized T τ).2` is, by definition, the executable closure. -/
theorem snd_checkWellSynchronized (T : CTA) (τ : List Config) :
    (CheckWellSynchronized T τ).2 = transClosure (initRelation T τ) := rfl

/-- **`Finset` non-membership ⇒ no `happensBefore`** (uses Pillar A, the
`transClosure` converse). If `a ≠ b` and the algorithm's relation does not
contain `(a, b)`, then `a` does not happen-before `b`. -/
theorem not_happensBefore_of_not_mem {T : CTA} {τ : List Config} {a b : ProgPoint}
    (hne : a ≠ b) (hnotmem : (a, b) ∉ (CheckWellSynchronized T τ).2) :
    ¬ happensBefore T τ a b := by
  intro hhb
  apply hnotmem
  rw [snd_checkWellSynchronized]
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hhb with heq | htg
  · exact absurd heq.symm hne
  · exact mem_transClosure_of_transGen (initRelation T τ) hne htg

/-- A failing check fails in one of its four conjuncts. -/
theorem check_false_cases {T : CTA} {τ : List Config}
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    okRegCheck T τ = false ∨ okWaitCheck T τ = false ∨
      okInitCheck T τ = false ∨ okUniqueInitCheck T τ = false := by
  have h : (okRegCheck T τ && okWaitCheck T τ && okInitCheck T τ
      && okUniqueInitCheck T τ) = false := hcheck
  revert h
  cases okRegCheck T τ <;> cases okWaitCheck T τ <;> cases okInitCheck T τ <;>
    cases okUniqueInitCheck T τ <;> simp

/-- **Extract a failing pair from `okRegCheck = false`** (mode 1): a registrant
`c1 ∈ Reg(b, g)` and a registrant `c2 ∈ Reg(b, g+1)` that either has an
in-thread predecessor `c3` the relation fails to order after `c1` (with
`c1 ≠ c3`, delivered by the reflexive disjunct), or is a first instruction. -/
theorem exists_failing_reg_pair {T : CTA} {τ : List Config}
    (hcheck : okRegCheck T τ = false) :
    ∃ c1 ∈ T.progPoints, ∃ b g, registrantGen T τ c1 = some (b, g) ∧
      ∃ c2 ∈ T.progPoints, registrantGen T τ c2 = some (b, g + 1) ∧
        ((1 ≤ c2.idx ∧
            c1 ≠ (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∧
            (c1, (⟨c2.thread, c2.idx - 1⟩ : ProgPoint)) ∉ (CheckWellSynchronized T τ).2) ∨
          c2.idx = 0) := by
  rw [snd_checkWellSynchronized]
  simp only [okRegCheck] at hcheck
  obtain ⟨c1, hc1, hf1⟩ := List.all_eq_false.mp hcheck
  refine ⟨c1, hc1, ?_⟩
  obtain ⟨b, g, hreg1⟩ : ∃ b g, registrantGen T τ c1 = some (b, g) := by
    cases hr : registrantGen T τ c1 with
    | none => simp [hr] at hf1
    | some bg =>
      obtain ⟨b', g'⟩ := bg
      exact ⟨b', g', rfl⟩
  refine ⟨b, g, hreg1, ?_⟩
  simp only [hreg1, Bool.not_eq_true] at hf1
  obtain ⟨c2, hc2, hf2⟩ := List.all_eq_false.mp hf1
  refine ⟨c2, hc2, ?_⟩
  by_cases hr2 : registrantGen T τ c2 = some (b, g + 1)
  · rw [if_pos hr2] at hf2
    refine ⟨hr2, ?_⟩
    by_cases hidx : 1 ≤ c2.idx
    · rw [if_pos hidx] at hf2
      simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or] at hf2
      exact Or.inl ⟨hidx, hf2.1, hf2.2⟩
    · exact Or.inr (by omega)
  · rw [if_neg hr2] at hf2
    exact absurd hf2 (by simp)

/-- **Extract a failing wait from `okWaitCheck = false`** (mode 2), as a
three-way disjunction: a first-instruction wait of positive generation
(lines 25–26); a lower-bound violation — some `Reg(sb, g−1)` registrant not
ordered before the wait's predecessor (lines 27–28); or an upper-bound
violation — the next generation fills but the wait precedes none of its
registrants (lines 29–30, amended). -/
theorem exists_failing_wait {T : CTA} {τ : List Config}
    (hcheck : okWaitCheck T τ = false) :
    ∃ w ∈ T.progPoints, ∃ sb ph g, T.cmdAt w = some (.wait_mb sb ph) ∧
      pointGen T τ w = some g ∧
      ((1 ≤ g ∧ w.idx = 0) ∨
        (1 ≤ g ∧ 1 ≤ w.idx ∧ ∃ c ∈ T.progPoints,
          registrantGen T τ c = some (.inr sb, g - 1) ∧
          c ≠ (⟨w.thread, w.idx - 1⟩ : ProgPoint) ∧
          (c, (⟨w.thread, w.idx - 1⟩ : ProgPoint)) ∉ (CheckWellSynchronized T τ).2) ∨
        (∃ n, T.initCountOf sb = some n ∧
          (T.progPoints.filter fun cp =>
              registrantGen T τ cp = some (.inr sb, g + 1)).length = (n : Nat) ∧
          ∀ cp ∈ T.progPoints.filter fun cp =>
              registrantGen T τ cp = some (.inr sb, g + 1),
            (w, cp) ∉ (CheckWellSynchronized T τ).2)) := by
  rw [snd_checkWellSynchronized]
  simp only [okWaitCheck] at hcheck
  obtain ⟨w, hw, hfw⟩ := List.all_eq_false.mp hcheck
  refine ⟨w, hw, ?_⟩
  -- both scrutinees of the outer match must be `some` (else the entry is `true`)
  obtain ⟨sb, ph, hcmd⟩ : ∃ sb ph, T.cmdAt w = some (.wait_mb sb ph) := by
    cases hc : T.cmdAt w with
    | none => simp [hc] at hfw
    | some cmd =>
      cases cmd with
      | wait_mb sb ph => exact ⟨sb, ph, rfl⟩
      | read g => simp [hc] at hfw
      | write g => simp [hc] at hfw
      | arrive_nb nb n => simp [hc] at hfw
      | sync_nb nb n => simp [hc] at hfw
      | init_mb sb n => simp [hc] at hfw
      | arrive_mb sb => simp [hc] at hfw
  obtain ⟨g, hgen⟩ : ∃ g, pointGen T τ w = some g := by
    cases hg : pointGen T τ w with
    | none => simp [hcmd, hg] at hfw
    | some g => exact ⟨g, rfl⟩
  refine ⟨sb, ph, g, hcmd, hgen, ?_⟩
  simp only [hcmd, hgen, Bool.not_eq_true] at hfw
  rcases Bool.and_eq_false_iff.mp hfw with hA | hB
  · -- lower half fails
    rcases Bool.or_eq_false_iff.mp hA with ⟨hg1, hBC⟩
    have hg1' : 1 ≤ g := by
      rw [decide_eq_false_iff_not] at hg1
      omega
    cases hidx : decide (1 ≤ w.idx) with
    | false =>
      rw [decide_eq_false_iff_not] at hidx
      exact Or.inl ⟨hg1', by omega⟩
    | true =>
      rw [hidx, Bool.true_and] at hBC
      obtain ⟨c, hcmem, hfc⟩ := List.all_eq_false.mp hBC
      rw [decide_eq_true_eq] at hidx
      by_cases hrc : registrantGen T τ c = some (.inr sb, g - 1)
      · rw [if_pos hrc] at hfc
        simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or] at hfc
        exact Or.inr (Or.inl ⟨hg1', hidx, c, hcmem, hrc, hfc.1, hfc.2⟩)
      · rw [if_neg hrc] at hfc
        exact absurd hfc (by simp)
  · -- upper half fails
    cases hio : T.initCountOf sb with
    | none => simp [hio] at hB
    | some n =>
      simp only [hio] at hB
      by_cases hlen : (T.progPoints.filter fun cp =>
          registrantGen T τ cp = some (.inr sb, g + 1)).length = (n : Nat)
      · rw [if_pos hlen] at hB
        refine Or.inr (Or.inr ⟨n, rfl, hlen, ?_⟩)
        intro cp hcp
        have := List.any_eq_false.mp hB cp hcp
        simpa using this
      · rw [if_neg hlen] at hB
        exact absurd hB (by simp)

/-- **Extract a failing init/use pair from `okInitCheck = false`** (mode 3). -/
theorem exists_failing_init_pair {T : CTA} {τ : List Config}
    (hcheck : okInitCheck T τ = false) :
    ∃ ci ∈ T.progPoints, ∃ sb n, T.cmdAt ci = some (.init_mb sb n) ∧
      ∃ u ∈ T.progPoints, (T.cmdAt u).bind Cmd.usesMBarrier? = some sb ∧
        ((1 ≤ u.idx ∧ ci ≠ (⟨u.thread, u.idx - 1⟩ : ProgPoint) ∧
          (ci, (⟨u.thread, u.idx - 1⟩ : ProgPoint)) ∉ (CheckWellSynchronized T τ).2) ∨
          u.idx = 0) := by
  rw [snd_checkWellSynchronized]
  simp only [okInitCheck] at hcheck
  obtain ⟨ci, hci, hf1⟩ := List.all_eq_false.mp hcheck
  refine ⟨ci, hci, ?_⟩
  obtain ⟨sb, n, hcmd⟩ : ∃ sb n, T.cmdAt ci = some (.init_mb sb n) := by
    cases hc : T.cmdAt ci with
    | none => simp [hc] at hf1
    | some cmd =>
      cases cmd with
      | init_mb sb n => exact ⟨sb, n, rfl⟩
      | read g => simp [hc] at hf1
      | write g => simp [hc] at hf1
      | arrive_nb nb n => simp [hc] at hf1
      | sync_nb nb n => simp [hc] at hf1
      | arrive_mb sb => simp [hc] at hf1
      | wait_mb sb ph => simp [hc] at hf1
  refine ⟨sb, n, hcmd, ?_⟩
  simp only [hcmd, Bool.not_eq_true] at hf1
  obtain ⟨u, hu, hf2⟩ := List.all_eq_false.mp hf1
  by_cases huse : (T.cmdAt u).bind Cmd.usesMBarrier? = some sb
  · rw [if_pos huse] at hf2
    by_cases hidx : 1 ≤ u.idx
    · rw [if_pos hidx] at hf2
      simp only [Bool.not_eq_true, decide_eq_false_iff_not, not_or] at hf2
      exact ⟨u, hu, huse, Or.inl ⟨hidx, hf2.1, hf2.2⟩⟩
    · exact ⟨u, hu, huse, Or.inr (by omega)⟩
  · rw [if_neg huse] at hf2
    exact absurd hf2 (by simp)

/-- **Extract duplicate initializations from `okUniqueInitCheck = false`**
(mode 4): two *distinct* `init_mb` program points for the same mbarrier. -/
theorem exists_failing_dup_init {T : CTA} {τ : List Config}
    (hcheck : okUniqueInitCheck T τ = false) :
    ∃ ci ∈ T.progPoints, ∃ sb n, T.cmdAt ci = some (.init_mb sb n) ∧
      ∃ cj ∈ T.progPoints, ∃ n', T.cmdAt cj = some (.init_mb sb n') ∧ ci ≠ cj := by
  simp only [okUniqueInitCheck] at hcheck
  obtain ⟨ci, hci, hf1⟩ := List.all_eq_false.mp hcheck
  refine ⟨ci, hci, ?_⟩
  obtain ⟨sb, n, hcmd⟩ : ∃ sb n, T.cmdAt ci = some (.init_mb sb n) := by
    cases hc : T.cmdAt ci with
    | none => simp [hc] at hf1
    | some cmd =>
      cases cmd with
      | init_mb sb n => exact ⟨sb, n, rfl⟩
      | read g => simp [hc] at hf1
      | write g => simp [hc] at hf1
      | arrive_nb nb n => simp [hc] at hf1
      | sync_nb nb n => simp [hc] at hf1
      | arrive_mb sb => simp [hc] at hf1
      | wait_mb sb ph => simp [hc] at hf1
  refine ⟨sb, n, hcmd, ?_⟩
  simp only [hcmd, Bool.not_eq_true] at hf1
  obtain ⟨cj, hcj, hf2⟩ := List.all_eq_false.mp hf1
  obtain ⟨sb', n', hcmd2⟩ : ∃ sb' n', T.cmdAt cj = some (.init_mb sb' n') := by
    cases hc : T.cmdAt cj with
    | none => simp [hc] at hf2
    | some cmd =>
      cases cmd with
      | init_mb sb' n' => exact ⟨sb', n', rfl⟩
      | read g => simp [hc] at hf2
      | write g => simp [hc] at hf2
      | arrive_nb nb n => simp [hc] at hf2
      | sync_nb nb n => simp [hc] at hf2
      | arrive_mb sb => simp [hc] at hf2
      | wait_mb sb ph => simp [hc] at hf2
  simp only [hcmd2] at hf2
  by_cases hbb : sb = sb'
  · subst hbb
    rw [if_pos rfl] at hf2
    simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hf2
    exact ⟨cj, hcj, n', hcmd2, hf2⟩
  · rw [if_neg hbb] at hf2
    exact absurd hf2 (by simp)

/-- **Only program order enters an `arrive_nb`.** If `c2` is an `arrive_nb` and
`c1` happens-before `c2`, then either `c1 = c2` or `c1` already happens-before
`c2`'s in-thread predecessor — every barrier edge of `initRelation` targets a
`sync_nb` or a `wait_mb`. -/
theorem happensBefore_arrive_nb {T : CTA} {τ : List Config} {c1 c2 : ProgPoint}
    {nb : NamedBarrier} {m : ℕ+} (hc2 : T.cmdAt c2 = some (.arrive_nb nb m))
    (hidx : 1 ≤ c2.idx) (h : happensBefore T τ c1 c2) :
    c1 = c2 ∨ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ := by
  rw [happensBefore] at h
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨d, hd, hdc2⟩
  · exact Or.inl heq.symm
  · refine Or.inr ?_
    obtain ⟨_, _, hcase⟩ := initRelation_cases hdc2
    rcases hcase with hpo | ⟨nb', n, hsync, _, _⟩ | ⟨sb, ph, hwait, _, _⟩
    · have hdeq : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) = d := by
        have h1 : c2.thread = d.thread := by rw [hpo]
        have h2 : c2.idx = d.idx + 1 := by rw [hpo]
        obtain ⟨dt, di⟩ := d
        simp only [ProgPoint.mk.injEq] at h1 h2 ⊢
        exact ⟨h1, by omega⟩
      rw [hdeq]
      exact hd
    · rw [hc2] at hsync
      exact absurd hsync (by simp)
    · rw [hc2] at hwait
      exact absurd hwait (by simp)

/-- **Only program order enters an `arrive_mb`** — the mbarrier sibling of
`happensBefore_arrive_nb`. -/
theorem happensBefore_arrive_mb {T : CTA} {τ : List Config} {c1 c2 : ProgPoint}
    {sb : SharedBarrier} (hc2 : T.cmdAt c2 = some (.arrive_mb sb))
    (hidx : 1 ≤ c2.idx) (h : happensBefore T τ c1 c2) :
    c1 = c2 ∨ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ := by
  rw [happensBefore] at h
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨d, hd, hdc2⟩
  · exact Or.inl heq.symm
  · refine Or.inr ?_
    obtain ⟨_, _, hcase⟩ := initRelation_cases hdc2
    rcases hcase with hpo | ⟨nb', n, hsync, _, _⟩ | ⟨sb', ph, hwait, _, _⟩
    · have hdeq : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) = d := by
        have h1 : c2.thread = d.thread := by rw [hpo]
        have h2 : c2.idx = d.idx + 1 := by rw [hpo]
        obtain ⟨dt, di⟩ := d
        simp only [ProgPoint.mk.injEq] at h1 h2 ⊢
        exact ⟨h1, by omega⟩
      rw [hdeq]
      exact hd
    · rw [hc2] at hsync
      exact absurd hsync (by simp)
    · rw [hc2] at hwait
      exact absurd hwait (by simp)

/-- A configured-and-full named barrier is incompatible with the `interleave`
guard `hbar` (every named barrier unconfigured or strictly under-full). -/
theorem interleaveGuard_full_absurd {S : State} {nb : NamedBarrier} {I : List ThreadId}
    {A : ℕ} {n : ℕ+} (hb : S.BN nb = ⟨I, A, some n⟩) (hfull : I.length + A = (n : Nat))
    (hbar : ∀ nb', S.BN nb' = NamedBarrierState.unconfigured ∨
        ∃ I' A' n', S.BN nb' = ⟨I', A', some n'⟩ ∧ I'.length + A' < (n' : Nat)) :
    False := by
  rcases hbar nb with h | ⟨I', A', n', hb', hlt⟩
  · rw [hb] at h
    simp [NamedBarrierState.unconfigured] at h
  · rw [hb] at hb'
    simp only [NamedBarrierState.mk.injEq, Option.some.injEq] at hb'
    obtain ⟨rfl, rfl, rfl⟩ := hb'
    omega

/-- An initialized-and-full mbarrier is incompatible with the `interleave`
guard `hmbar` (every mbarrier uninitialized or strictly under-full in
arrivals). -/
theorem interleaveGuard_mbfull_absurd {S : State} {sb : SharedBarrier}
    {I : List ThreadId} {A : ℕ} {n : ℕ+} {ph : Phase}
    (hb : S.BM sb = ⟨I, A, some n, ph⟩) (hfull : A = (n : Nat))
    (hmbar : ∀ sb', S.BM sb' = MBarrierState.uninitialized ∨
        ∃ I' A' n' ph', S.BM sb' = ⟨I', A', some n', ph'⟩ ∧ A' < (n' : Nat)) :
    False := by
  rcases hmbar sb with h | ⟨I', A', n', ph', hb', hlt⟩
  · rw [hb] at h
    simp [MBarrierState.uninitialized] at h
  · rw [hb] at hb'
    simp only [MBarrierState.mk.injEq, Option.some.injEq] at hb'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb'
    omega

/-- A command's observed generation is at most its recycle count: registrants
observe exactly `r`, waits observe `r` or `r − 1`. -/
theorem le_of_genValue {c : Cmd} {r : Nat} {g : ℤ} (h : c.genValue r = g) : g ≤ (r : ℤ) := by
  cases c with
  | wait_mb sb ph =>
    simp only [Cmd.genValue] at h
    split at h <;> omega
  | read l => simp only [Cmd.genValue] at h; omega
  | write l => simp only [Cmd.genValue] at h; omega
  | arrive_nb nb n => simp only [Cmd.genValue] at h; omega
  | sync_nb nb n => simp only [Cmd.genValue] at h; omega
  | init_mb sb n => simp only [Cmd.genValue] at h; omega
  | arrive_mb sb => simp only [Cmd.genValue] at h; omega

/-- A registrant observes exactly its recycle count (no wait correction). -/
theorem genValue_of_isRegistrant {c : Cmd} (h : c.isRegistrant = true) (r : Nat) :
    c.genValue r = (r : ℤ) := by
  cases c with
  | arrive_nb nb n => rfl
  | sync_nb nb n => rfl
  | arrive_mb sb => rfl
  | read l => simp [Cmd.isRegistrant] at h
  | write l => simp [Cmd.isRegistrant] at h
  | init_mb sb n => simp [Cmd.isRegistrant] at h
  | wait_mb sb ph => simp [Cmd.isRegistrant] at h

/-- Decode a `Reg`-membership: the point carries a registrant command on the
right barrier whose generation is `g`. -/
theorem registrantGen_some {T : CTA} {τ : List Config} {c : ProgPoint}
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℤ}
    (h : registrantGen T τ c = some (b, g)) :
    ∃ cmd, T.cmdAt c = some cmd ∧ cmd.isRegistrant = true ∧
      cmd.barrier? = some b ∧ pointGen T τ c = some g := by
  unfold registrantGen at h
  cases hc : T.cmdAt c with
  | none => simp only [hc] at h; exact absurd h (by simp)
  | some cmd =>
    simp only [hc] at h
    cases hg : pointGen T τ c with
    | none => simp only [hg] at h; exact absurd h (by simp)
    | some g' =>
      simp only [hg] at h
      by_cases hr : cmd.isRegistrant
      · rw [if_pos hr] at h
        cases hb : cmd.barrier? with
        | none => rw [hb] at h; exact absurd h (by simp)
        | some b' =>
          rw [hb] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨cmd, rfl, hr, hb, rfl⟩
      · rw [if_neg hr] at h
        exact absurd h (by simp)

/-! ## The reversing-schedule construction (preciseness support)

The ideal `G = {η | ¬ happensBefore T τ η₁ η}` is down-closed under
`initRelation` edges, hence a per-thread program prefix (the *cut*). The
lemmas here support running all of `G` first: the cut, the `G`-bounded
invariant, and the operational facts about parked threads that the progress
lemma (`gstep`) needs. -/

/-- A program-order edge `⟨i, m⟩ → ⟨i, m+1⟩` belongs to `initRelation T τ` whenever
`m + 1` indexes thread `i`'s program (Algorithm 2 lines 9–10). -/
theorem mem_initRelation_progOrder {T : CTA} {τ : List Config} {i m : Nat}
    (h : m + 1 < (T.prog i).length) :
    ((⟨i, m⟩ : ProgPoint), (⟨i, m + 1⟩ : ProgPoint)) ∈ initRelation T τ := by
  have hpt : (⟨i, m⟩ : ProgPoint) ∈ T.progPoints := by
    rw [mem_progPoints_iff]
    exact ⟨mem_ids_of_idx_lt T (show m < (T.prog i).length by omega),
      show m < (T.prog i).length by omega⟩
  simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inl (Or.inl ⟨⟨i, m⟩, hpt, by rw [if_pos h]⟩))

/-- **Full membership characterization of `initRelation`** (the converse-complete
form of `initRelation_cases`, retaining the arrival count `n` that
`initRelation_cases` drops). An edge `(a, b)` is exactly one of: program order;
`arrive_nb → sync_nb` of equal generation; `arrive_mb → wait_mb` of equal
generation; `sync_nb ↔ sync_nb` of equal generation (symmetric, so one shape
covers both endpoints being `sync_nb`). -/
theorem mem_initRelation_iff {T : CTA} {τ : List Config} {a b : ProgPoint} :
    (a, b) ∈ initRelation T τ ↔
      (a ∈ T.progPoints ∧ a.idx + 1 < (T.prog a.thread).length ∧ b = ⟨a.thread, a.idx + 1⟩)
      ∨ (∃ nb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.arrive_nb nb n) ∧ T.cmdAt b = some (.sync_nb nb n) ∧
          pointGen T τ a = pointGen T τ b)
      ∨ (∃ sb ph, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.arrive_mb sb) ∧ T.cmdAt b = some (.wait_mb sb ph) ∧
          pointGen T τ a = pointGen T τ b)
      ∨ (∃ nb n, a ∈ T.progPoints ∧ b ∈ T.progPoints ∧
          T.cmdAt a = some (.sync_nb nb n) ∧ T.cmdAt b = some (.sync_nb nb n) ∧
          pointGen T τ a = pointGen T τ b) := by
  constructor
  · intro hedge
    simp only [initRelation, List.mem_toFinset, List.mem_append] at hedge
    rcases hedge with ((hpo | has) | haw) | hss
    · -- program order
      simp only [List.mem_filterMap] at hpo
      obtain ⟨c, hc, hceq⟩ := hpo
      split at hceq
      · rename_i hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hceq
        obtain ⟨rfl, rfl⟩ := hceq
        exact Or.inl ⟨hc, hcond, rfl⟩
      · exact absurd hceq (by simp)
    · -- arrive_nb → sync_nb
      simp only [List.mem_flatMap] at has
      obtain ⟨c1, hc1, hin⟩ := has
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | sync_nb nb n => simp [hcmd1] at hin
        | init_mb sb n => simp [hcmd1] at hin
        | arrive_mb sb => simp [hcmd1] at hin
        | wait_mb sb ph => simp [hcmd1] at hin
        | arrive_nb nb n =>
          simp only [hcmd1, List.mem_filterMap] at hin
          obtain ⟨c2, hc2, hc2eq⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hc2eq
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hc2eq
            | write g => simp [hcmd2] at hc2eq
            | arrive_nb nb' n' => simp [hcmd2] at hc2eq
            | init_mb sb n' => simp [hcmd2] at hc2eq
            | arrive_mb sb => simp [hcmd2] at hc2eq
            | wait_mb sb ph => simp [hcmd2] at hc2eq
            | sync_nb nb' n' =>
              simp only [hcmd2] at hc2eq
              split at hc2eq
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
                obtain ⟨rfl, rfl⟩ := hc2eq
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                exact Or.inr (Or.inl ⟨nb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩)
              · exact absurd hc2eq (by simp)
    · -- arrive_mb → wait_mb
      simp only [List.mem_flatMap] at haw
      obtain ⟨c1, hc1, hin⟩ := haw
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | arrive_nb nb n => simp [hcmd1] at hin
        | sync_nb nb n => simp [hcmd1] at hin
        | init_mb sb n => simp [hcmd1] at hin
        | wait_mb sb ph => simp [hcmd1] at hin
        | arrive_mb sb =>
          simp only [hcmd1, List.mem_filterMap] at hin
          obtain ⟨c2, hc2, hc2eq⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hc2eq
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hc2eq
            | write g => simp [hcmd2] at hc2eq
            | arrive_nb nb' n' => simp [hcmd2] at hc2eq
            | sync_nb nb' n' => simp [hcmd2] at hc2eq
            | init_mb sb' n' => simp [hcmd2] at hc2eq
            | arrive_mb sb' => simp [hcmd2] at hc2eq
            | wait_mb sb' ph =>
              simp only [hcmd2] at hc2eq
              split at hc2eq
              · rename_i hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at hc2eq
                obtain ⟨rfl, rfl⟩ := hc2eq
                obtain ⟨rfl, hgen⟩ := hcond
                exact Or.inr (Or.inr (Or.inl ⟨sb, ph, hc1, hc2, hcmd1, hcmd2, hgen⟩))
              · exact absurd hc2eq (by simp)
    · -- sync_nb ↔ sync_nb
      simp only [List.mem_flatMap] at hss
      obtain ⟨c1, hc1, hin⟩ := hss
      cases hcmd1 : T.cmdAt c1 with
      | none => simp [hcmd1] at hin
      | some cmd1 => cases cmd1 with
        | read g => simp [hcmd1] at hin
        | write g => simp [hcmd1] at hin
        | arrive_nb nb n => simp [hcmd1] at hin
        | init_mb sb n => simp [hcmd1] at hin
        | arrive_mb sb => simp [hcmd1] at hin
        | wait_mb sb ph => simp [hcmd1] at hin
        | sync_nb nb n =>
          simp only [hcmd1, List.mem_flatMap] at hin
          obtain ⟨c2, hc2, hin2⟩ := hin
          cases hcmd2 : T.cmdAt c2 with
          | none => simp [hcmd2] at hin2
          | some cmd2 => cases cmd2 with
            | read g => simp [hcmd2] at hin2
            | write g => simp [hcmd2] at hin2
            | arrive_nb nb' n' => simp [hcmd2] at hin2
            | init_mb sb' n' => simp [hcmd2] at hin2
            | arrive_mb sb' => simp [hcmd2] at hin2
            | wait_mb sb' ph => simp [hcmd2] at hin2
            | sync_nb nb' n' =>
              simp only [hcmd2] at hin2
              split at hin2
              · rename_i hcond
                obtain ⟨rfl, rfl, hgen⟩ := hcond
                simp only [List.mem_cons, List.not_mem_nil, or_false,
                  Prod.mk.injEq] at hin2
                rcases hin2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inr (Or.inr (Or.inr ⟨nb, n, hc1, hc2, hcmd1, hcmd2, hgen⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨nb, n, hc2, hc1, hcmd2, hcmd1, hgen.symm⟩))
              · simp at hin2
  · intro h
    rcases h with ⟨hapts, hlt, hbeq⟩ | ⟨nb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
        | ⟨sb, ph, hapts, hbpts, hcmda, hcmdb, hgen⟩
        | ⟨nb, n, hapts, hbpts, hcmda, hcmdb, hgen⟩
    · -- program order
      obtain ⟨at', ai⟩ := a
      subst hbeq
      exact mem_initRelation_progOrder hlt
    · -- arrive_nb → sync_nb
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap,
        List.mem_filterMap]
      refine Or.inl (Or.inl (Or.inr ⟨a, hapts, ?_⟩))
      simp only [hcmda, List.mem_filterMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩
    · -- arrive_mb → wait_mb
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap,
        List.mem_filterMap]
      refine Or.inl (Or.inr ⟨a, hapts, ?_⟩)
      simp only [hcmda, List.mem_filterMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩
    · -- sync_nb ↔ sync_nb
      simp only [initRelation, List.mem_toFinset, List.mem_append, List.mem_flatMap]
      refine Or.inr ⟨a, hapts, ?_⟩
      simp only [hcmda, List.mem_flatMap]
      exact ⟨b, hbpts, by simp [hcmdb, hgen]⟩

/-- **Program order is captured by `happensBefore`.** Within a single thread `i`,
any earlier point is happens-before any later valid point. -/
theorem progOrder_happensBefore {T : CTA} {τ : List Config} {i a : Nat} :
    ∀ {b : Nat}, a ≤ b → b < (T.prog i).length → happensBefore T τ ⟨i, a⟩ ⟨i, b⟩ := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact Relation.ReflTransGen.refl
  | succ m hm ih =>
      intro hlt
      exact (ih (by omega)).tail (mem_initRelation_progOrder (by omega))

/-- **Strict monotonicity of time within a thread.** In any complete trace, an
earlier instruction of a thread executes strictly before a later one. -/
theorem time_lt_of_idx_lt {C₀ : Config} {τ : List Config} {η ξ : ProgPoint} {nη nξ : Nat}
    (hη : IsTimeOf C₀ τ η nη) (hξ : IsTimeOf C₀ τ ξ nξ)
    (hthread : η.thread = ξ.thread) (hidx : η.idx < ξ.idx) : nη < nξ := by
  obtain ⟨hτ, _, jη, Cη, _, rfl, hCjη, _, hCηeq, _⟩ := hη
  obtain ⟨_, hξL, jξ, Cξ, _, rfl, hCjξ, _, hCξeq, _⟩ := hξ
  rw [← hthread] at hCξeq hξL
  have hchain := hτ.1.subtrace
  rcases Nat.lt_or_ge jη jξ with h | h
  · omega
  · exfalso
    have hsuf := progOf_suffix_index_le hchain η.thread hCjξ h hCjη
    have hle := suffix_length_le hsuf
    rw [hCηeq, hCξeq, List.length_drop, List.length_drop] at hle
    omega

section IdealCut

open Classical in
/-- The **cut** for thread `i` (relative to `η₁`): the least index of a point that
is happens-before-after `η₁` — an `F`-position — or the program length if none.
It splits thread `i` into the ideal `G`-prefix `[0, cut)` and the `F`-suffix. -/
noncomputable def fcut (T : CTA) (τ : List Config) (η₁ : ProgPoint) (i : ThreadId) : Nat :=
  if h : ∃ k, happensBefore T τ η₁ ⟨i, k⟩ ∧ k < (T.prog i).length
  then Nat.find h else (T.prog i).length

/-- An `F`-point (happens-before-after `η₁`) sits at or beyond its thread's cut —
in particular `η₁` itself does (reflexively), so `η₁ ∉ G`. -/
theorem fcut_le_of_hb {T : CTA} {τ : List Config} {η₁ η : ProgPoint}
    (h : happensBefore T τ η₁ η) (hv : η ∈ T.progPoints) :
    fcut T τ η₁ η.thread ≤ η.idx := by
  classical
  have hηeq : (⟨η.thread, η.idx⟩ : ProgPoint) = η := rfl
  have hex : ∃ k, happensBefore T τ η₁ ⟨η.thread, k⟩ ∧ k < (T.prog η.thread).length :=
    ⟨η.idx, by rw [hηeq]; exact h, ((mem_progPoints_iff T η).mp hv).2⟩
  unfold fcut
  rw [dif_pos hex]
  exact Nat.find_le ⟨by rw [hηeq]; exact h, ((mem_progPoints_iff T η).mp hv).2⟩

/-- A `G`-point (not happens-before-after `η₁`) sits strictly below its thread's
cut — in particular `η₂` does, so `η₂ ∈ G`. -/
theorem lt_fcut_of_not_hb {T : CTA} {τ : List Config} {η₁ η : ProgPoint}
    (h : ¬ happensBefore T τ η₁ η) (hv : η ∈ T.progPoints) :
    η.idx < fcut T τ η₁ η.thread := by
  classical
  have hηeq : (⟨η.thread, η.idx⟩ : ProgPoint) = η := rfl
  have hvlt : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hv).2
  by_contra hle
  push Not at hle
  unfold fcut at hle
  split at hle
  · rename_i hex
    obtain ⟨hhb, _⟩ := Nat.find_spec hex
    exact h (hηeq ▸ hhb.trans (progOrder_happensBefore hle hvlt))
  · omega

/-- The cut never exceeds the program length. -/
theorem fcut_le_length (T : CTA) (τ : List Config) (η₁ : ProgPoint) (i : ThreadId) :
    fcut T τ η₁ i ≤ (T.prog i).length := by
  classical
  unfold fcut
  split
  · rename_i h; exact le_of_lt (Nat.find_spec h).2
  · exact le_refl _

end IdealCut

/-- The clean-state invariant for the run-`G` construction: configuration `C` has
executed only the ideal `G` so far. Two clauses:

* **program bound** — each thread's remaining program is `T`'s with at most `cut`
  commands dropped, so no `F`-command (index `≥ cut`) has run;
* **barrier purity** — every blocked thread (parked at a `sync_nb` or a
  `wait_mb` — `State.blocked` covers both kinds) sits at a `G`-command (its
  executed count is strictly below its cut). Without this an `F`-command could
  park into a `G`-round and the round's recycle would push that thread past its
  cut. -/
def GBounded (T : CTA) (τ : List Config) (η₁ : ProgPoint) (C : Config) : Prop :=
  ∃ s T_C, C = Config.run s T_C ∧
    (∀ i, ∃ e, e ≤ fcut T τ η₁ i ∧ T_C.prog i = (T.prog i).drop e) ∧
    (∀ b i, i ∈ s.blocked b →
      (T.prog i).length - (T_C.prog i).length < fcut T τ η₁ i)

/-- The initial configuration is `G`-bounded: nothing has executed and no thread
is blocked. -/
theorem GBounded_init (T : CTA) (τ : List Config) (η₁ : ProgPoint) :
    GBounded T τ η₁ (Config.run State.initial T) :=
  ⟨State.initial, T, rfl, fun i => ⟨0, Nat.zero_le _, by simp⟩,
    fun b i hi => by
      exfalso
      cases b <;> simp [State.blocked, State.initial, NamedBarrierState.unconfigured,
        MBarrierState.uninitialized] at hi⟩

/-- If `η` has *already executed* by configuration index `p` (its remaining
program is short enough at `p`), then its time is `≤ p`. -/
theorem time_le_of_progOf_le {C₀ : Config} {τ' : List Config} {η : ProgPoint} {n p : Nat}
    {C : Config} (ht : IsTimeOf C₀ τ' η n) (hp : τ'[p]? = some C)
    (hlen : (C.progOf η.thread).length ≤ (C₀.progOf η.thread).length - η.idx - 1) :
    n ≤ p := by
  obtain ⟨hcomp, _, j, Cj, _, rfl, hCj, _, hCjeq, _⟩ := ht
  have hchain := hcomp.1.subtrace
  by_contra hlt
  push Not at hlt
  have hsuf := progOf_suffix_index_le hchain η.thread hp (by omega : p ≤ j) hCj
  have := suffix_length_le hsuf
  rw [hCjeq, List.length_drop] at this
  omega

/-- If `η` has *not yet executed* by configuration index `p` (its remaining
program is still long at `p`), then its time is `> p`. -/
theorem lt_time_of_lt_progOf {C₀ : Config} {τ' : List Config} {η : ProgPoint} {n p : Nat}
    {C : Config} (ht : IsTimeOf C₀ τ' η n) (hp : τ'[p]? = some C)
    (hlen : (C₀.progOf η.thread).length - η.idx - 1 < (C.progOf η.thread).length) :
    p < n := by
  obtain ⟨hcomp, _, j, _, Cj', rfl, _, hCj1, _, hCj1eq⟩ := ht
  have hchain := hcomp.1.subtrace
  by_contra hle
  push Not at hle
  have hsuf := progOf_suffix_index_le hchain η.thread hCj1 (by omega : j + 1 ≤ p) hp
  have := suffix_length_le hsuf
  rw [hCj1eq, List.length_drop] at this
  omega

/-- The barrier-support invariant propagates to every reachable configuration. -/
theorem barriersWithin_of_reaches {T : CTA} {C : Config}
    (h : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) :
    C.barriersWithin T.barrierSet := by
  induction h with
  | refl => exact barriersWithin_initial
  | tail _ hstep ih => exact inv_preserved T.barrierSet hstep ih

/-- `G` is exhausted at `C`: every (in-domain) thread has run exactly its
`fcut`-prefix. -/
def Gdone (T : CTA) (τ : List Config) (η₁ : ProgPoint) (C : Config) : Prop :=
  ∀ i ∈ T.ids, (C.progOf i).length = (T.prog i).length - fcut T τ η₁ i

/-! ### Operational support: parked threads persist until their recycle -/

/-- A full named barrier is never unconfigured, so a step that leaves it
unchanged does not recycle it. -/
theorem isFull_and_unconfigured_false (β : NamedBarrierState) :
    (β.isFull && decide (β = NamedBarrierState.unconfigured)) = false := by
  unfold NamedBarrierState.isFull
  cases hc : β.count with
  | none => simp
  | some n =>
    have hne : β ≠ NamedBarrierState.unconfigured := by
      intro h; rw [h] at hc; simp [NamedBarrierState.unconfigured] at hc
    simp [decide_eq_false hne]

/-- No mbarrier state equals its own phase-flip — the recycle signature is
never satisfied by an unchanged barrier. -/
theorem mb_flip_ne (β : MBarrierState) : β ≠ ⟨[], 0, β.count, !β.phase⟩ := by
  intro h
  have hph := congrArg MBarrierState.phase h
  simp at hph

/-- **Only a `b`-recycle removes a thread from `b`'s blocking list.** If `t` is
blocked at `b` in `C` and the step `C ⤳ C'` is *not* a recycle of `b`, then `t`
is still blocked at `b` in `C'`. -/
theorem blocked_persists {C C' : Config} (hstep : CTAStep C C')
    {b : NamedBarrier ⊕ SharedBarrier} {t : ThreadId}
    {s : State} (hCs : C.state? = some s) (hBI : s.BlockInv) (ht : t ∈ s.blocked b)
    (hnorec : stepRecyclesBarrier b C C' = false) {s' : State} (hCs' : C'.state? = some s') :
    t ∈ s'.blocked b := by
  cases hstep with
  | @interleave s₀ s₁ T i P' hi hbar hmbar hth =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    generalize hpi : T.prog i = Pi at hth
    cases hth with
    | read_noop => exact ht
    | write_noop => exact ht
    | mb_wait_pass he hb0 hnep => exact ht
    | @arrive_configure _ _ nb₀ n _ he hb0 =>
      cases b with
      | inr sb => exact ht
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          change t ∈ (s₀.BN nb).synced at ht
          rw [hb0] at ht
          simp [NamedBarrierState.unconfigured] at ht
        · change t ∈ (Function.update s₀.BN nb₀ ⟨[], 1, some n⟩ nb).synced
          rw [Function.update_of_ne hbb]
          exact ht
    | @arrive_register _ _ nb₀ n _ I A he hb0 hpos hlt =>
      cases b with
      | inr sb => exact ht
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          change t ∈ (Function.update s₀.BN nb ⟨I, A + 1, some n⟩ nb).synced
          rw [Function.update_self]
          change t ∈ (s₀.BN nb).synced at ht
          rw [hb0] at ht
          exact ht
        · change t ∈ (Function.update s₀.BN nb₀ ⟨I, A + 1, some n⟩ nb).synced
          rw [Function.update_of_ne hbb]
          exact ht
    | @sync_configure _ _ nb₀ n _ he hb0 =>
      cases b with
      | inr sb => exact ht
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          change t ∈ (s₀.BN nb).synced at ht
          rw [hb0] at ht
          simp [NamedBarrierState.unconfigured] at ht
        · change t ∈ (Function.update s₀.BN nb₀ ⟨[i], 0, some n⟩ nb).synced
          rw [Function.update_of_ne hbb]
          exact ht
    | @sync_block _ _ nb₀ n _ I A he hb0 hpos hlt =>
      cases b with
      | inr sb => exact ht
      | inl nb =>
        by_cases hbb : nb = nb₀
        · subst hbb
          change t ∈ (Function.update s₀.BN nb ⟨i :: I, A, some n⟩ nb).synced
          rw [Function.update_self]
          change t ∈ (s₀.BN nb).synced at ht
          rw [hb0] at ht
          exact List.mem_cons_of_mem _ ht
        · change t ∈ (Function.update s₀.BN nb₀ ⟨i :: I, A, some n⟩ nb).synced
          rw [Function.update_of_ne hbb]
          exact ht
    | @mb_init _ _ sb₀ n _ he hb0 =>
      cases b with
      | inl nb => exact ht
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          change t ∈ (s₀.BM sb).waiting at ht
          rw [hb0] at ht
          simp [MBarrierState.uninitialized] at ht
        · change t ∈ (Function.update s₀.BM sb₀ ⟨[], 0, some n, false⟩ sb).waiting
          rw [Function.update_of_ne hbb]
          exact ht
    | @mb_arrive _ _ sb₀ _ I A n ph he hb0 =>
      cases b with
      | inl nb => exact ht
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          change t ∈ (Function.update s₀.BM sb ⟨I, A + 1, some n, ph⟩ sb).waiting
          rw [Function.update_self]
          change t ∈ (s₀.BM sb).waiting at ht
          rw [hb0] at ht
          exact ht
        · change t ∈ (Function.update s₀.BM sb₀ ⟨I, A + 1, some n, ph⟩ sb).waiting
          rw [Function.update_of_ne hbb]
          exact ht
    | @mb_wait_block _ _ sb₀ ph _ I A n he hb0 =>
      cases b with
      | inl nb => exact ht
      | inr sb =>
        by_cases hbb : sb = sb₀
        · subst hbb
          change t ∈ (Function.update s₀.BM sb ⟨i :: I, A, some n, ph⟩ sb).waiting
          rw [Function.update_self]
          change t ∈ (s₀.BM sb).waiting at ht
          rw [hb0] at ht
          exact List.mem_cons_of_mem _ ht
        · change t ∈ (Function.update s₀.BM sb₀ ⟨i :: I, A, some n, ph⟩ sb).waiting
          rw [Function.update_of_ne hbb]
          exact ht
  | @recycle s₀ T nb₀ I A n hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    cases b with
    | inr sb => exact ht
    | inl nb =>
      by_cases hbb : nb = nb₀
      · subst hbb
        exfalso
        revert hnorec
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb, NamedBarrierState.isFull,
          hfull, Function.update_self, NamedBarrierState.unconfigured]
      · change t ∈ (Function.update s₀.BN nb₀ NamedBarrierState.unconfigured nb).synced
        rw [Function.update_of_ne hbb]
        exact ht
  | @mb_recycle s₀ T sb₀ I A n ph hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    cases b with
    | inl nb => exact ht
    | inr sb =>
      by_cases hbb : sb = sb₀
      · subst hbb
        exfalso
        revert hnorec
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb, MBarrierState.isFull,
          hfull, Function.update_self]
      · change t ∈ (Function.update s₀.BM sb₀ ⟨[], 0, some n, !ph⟩ sb).waiting
        rw [Function.update_of_ne hbb]
        exact ht
  | @done s₀ T hdone _ _ =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    exact ht
  | @error s₀ T i P' _ _ hth =>
    exact absurd hCs' (by simp [WeftCommon.Config.state?])

/-- **A `b`-recycle advances every thread parked at `b`.** If `t` is blocked at
`b` in `C` and the step `C ⤳ C'` *is* a recycle of `b`, then `t`'s remaining
program drops its parked head. -/
theorem recycle_advances_blocked {C C' : Config} (hstep : CTAStep C C')
    {b : NamedBarrier ⊕ SharedBarrier} {t : ThreadId} {s : State}
    (hCs : C.state? = some s) (ht : t ∈ s.blocked b)
    (hrec : stepRecyclesBarrier b C C' = true) :
    C'.progOf t = (C.progOf t).tail := by
  cases hstep with
  | @interleave s₀ s₁ T i P' hi hbar hmbar hth =>
    exfalso
    obtain rfl : s₀ = s := by simpa [WeftCommon.Config.state?] using hCs
    cases b with
    | inl nb =>
      have hnf : (s₀.BN nb).isFull = false := by
        rcases hbar nb with h | ⟨I, A, n, hbn, hlt⟩
        · rw [h]; simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured]
        · rw [hbn]; simp only [NamedBarrierState.isFull, beq_eq_false_iff_ne]; omega
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf] at hrec
    | inr sb =>
      have hnf : (s₀.BM sb).isFull = false := by
        rcases hmbar sb with h | ⟨I, A, n, ph, hbn, hlt⟩
        · rw [h]; simp [MBarrierState.isFull, MBarrierState.uninitialized]
        · rw [hbn]; simp only [MBarrierState.isFull, beq_eq_false_iff_ne]; omega
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf] at hrec
  | @recycle s₀ T nb₀ I A n hb hfull hpark =>
    obtain rfl : s₀ = s := by simpa [WeftCommon.Config.state?] using hCs
    cases b with
    | inl nb =>
      by_cases hbb : nb = nb₀
      · subst hbb
        have htI : t ∈ I := by
          change t ∈ (s₀.BN nb).synced at ht
          rw [hb] at ht
          exact ht
        simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake, if_pos htI]
      · exfalso
        have hne : Function.update s₀.BN nb₀ NamedBarrierState.unconfigured nb
            = s₀.BN nb := Function.update_of_ne hbb _ _
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hne,
          isFull_and_unconfigured_false] at hrec
    | inr sb =>
      exfalso
      simp [stepRecyclesBarrier, WeftCommon.Config.state?,
        decide_eq_false (mb_flip_ne (s₀.BM sb))] at hrec
  | @mb_recycle s₀ T sb₀ I A n ph hb hfull hpark =>
    obtain rfl : s₀ = s := by simpa [WeftCommon.Config.state?] using hCs
    cases b with
    | inr sb =>
      by_cases hbb : sb = sb₀
      · subst hbb
        have htI : t ∈ I := by
          change t ∈ (s₀.BM sb).waiting at ht
          rw [hb] at ht
          exact ht
        simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake, if_pos htI]
      · exfalso
        have hne : Function.update s₀.BM sb₀ ⟨[], 0, some n, !ph⟩ sb
            = s₀.BM sb := Function.update_of_ne hbb _ _
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hne,
          decide_eq_false (mb_flip_ne (s₀.BM sb))] at hrec
    | inl nb =>
      exfalso
      simp [stepRecyclesBarrier, WeftCommon.Config.state?,
        isFull_and_unconfigured_false] at hrec
  | @done s₀ T hdone _ _ =>
    exfalso
    obtain rfl : s₀ = s := by simpa [WeftCommon.Config.state?] using hCs
    cases b with
    | inl nb =>
      simp [stepRecyclesBarrier, WeftCommon.Config.state?,
        isFull_and_unconfigured_false] at hrec
    | inr sb =>
      simp [stepRecyclesBarrier, WeftCommon.Config.state?,
        decide_eq_false (mb_flip_ne (s₀.BM sb))] at hrec
  | @error s₀ T i P' _ _ hth =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?] at hrec

/-- **A parked thread's command recycles at the next `b`-recycle.** If `t` is
blocked at `b` (head `= η`) at config `p`, and `η` executes at time `n > p`,
then `b` does not recycle between `p` and `n`: the recycle count is unchanged. -/
theorem parked_blocked_recycleCount {C₀ : Config} {τ : List Config}
    (hBI : ∀ C ∈ τ, ∀ s, C.state? = some s → s.BlockInv)
    {b : NamedBarrier ⊕ SharedBarrier} {t : ThreadId} {η : ProgPoint} {p n : Nat}
    (hηt : η.thread = t) (hη : IsTimeOf C₀ τ η n)
    {sp : State} {Tp : CTA} (hCp : τ[p]? = some (Config.run sp Tp))
    (hpark : t ∈ sp.blocked b)
    (hprog : Tp.prog t = (C₀.progOf t).drop η.idx) (hpn : p < n) :
    recycleCount b τ (n - 1) = recycleCount b τ p := by
  obtain ⟨hcomplete, hidxL, j₀, Cn1, Cn, hn, hCn1, hCn, hCn1prog, hCnprog⟩ := hη
  have hchain := hcomplete.1.subtrace
  subst hn
  rw [hηt] at hCn1prog
  simp only [Nat.add_sub_cancel]
  have hprogj : ∀ j, p ≤ j → j ≤ j₀ → ∀ Cj, τ[j]? = some Cj →
      Cj.progOf t = (C₀.progOf t).drop η.idx := by
    intro j hpj hjj Cj hCj
    have hsuf1 : Cj.progOf t <:+ (C₀.progOf t).drop η.idx := by
      have := progOf_suffix_index_le hchain t hCp hpj hCj
      rwa [show (Config.run sp Tp).progOf t = (C₀.progOf t).drop η.idx from hprog] at this
    have hsuf2 : (C₀.progOf t).drop η.idx <:+ Cj.progOf t := by
      have := progOf_suffix_index_le hchain t hCj hjj hCn1
      rwa [hCn1prog] at this
    have hle1 := suffix_length_le hsuf1
    have hle2 := suffix_length_le hsuf2
    exact (hsuf1.sublist.eq_of_length (by omega))
  have hQ : ∀ d, p + d ≤ j₀ →
      (∃ s' T', τ[p + d]? = some (Config.run s' T') ∧ t ∈ s'.blocked b) ∧
        recycleCount b τ (p + d) = recycleCount b τ p := by
    intro d
    induction d with
    | zero => intro _; exact ⟨⟨sp, Tp, hCp, hpark⟩, rfl⟩
    | succ e ih =>
        intro hle
        obtain ⟨⟨s', T', hCe, hblk⟩, hrc⟩ := ih (by omega)
        have hj₀lt : j₀ + 1 < τ.length := (List.getElem?_eq_some_iff.mp hCn).1
        obtain ⟨Cnext, hCnext⟩ : ∃ C, τ[p + e + 1]? = some C :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hstep : CTAStep (Config.run s' T') Cnext := chain_step hchain hCe hCnext
        have hpe : (Config.run s' T').progOf t = (C₀.progOf t).drop η.idx :=
          hprogj (p + e) (by omega) (by omega) _ hCe
        have hnr : stepRecyclesBarrier b (Config.run s' T') Cnext = false := by
          by_contra hrec
          rw [Bool.not_eq_false] at hrec
          have hadv : Cnext.progOf t = ((C₀.progOf t).drop η.idx).tail := by
            rw [← hpe]; exact recycle_advances_blocked hstep rfl hblk hrec
          rw [List.tail_drop] at hadv
          have htime : IsTimeOf C₀ τ η (p + e + 1) :=
            ⟨hcomplete, hidxL, p + e, _, _, rfl, hCe, hCnext,
              by rw [hηt]; exact hpe, by rw [hηt]; exact hadv⟩
          have huniq := IsTimeOf.unique htime
            ⟨hcomplete, hidxL, j₀, Cn1, Cn, rfl, hCn1, hCn,
              by rw [hηt]; exact hCn1prog, hCnprog⟩
          omega
        obtain ⟨s'', T'', rfl⟩ : ∃ s'' T'', Cnext = Config.run s'' T'' := by
          obtain ⟨Cnn, hCnn⟩ : ∃ C, τ[p + e + 1 + 1]? = some C :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          cases chain_step hchain hCnext hCnn <;> exact ⟨_, _, rfl⟩
        refine ⟨⟨s'', T'', hCnext, blocked_persists hstep rfl ?_ hblk hnr rfl⟩, ?_⟩
        · exact hBI _ (List.mem_of_getElem? hCe) s' rfl
        · have hidx : p + (e + 1) = (p + e) + 1 := rfl
          have hrc' : recycleCount b τ ((p + e) + 1) = recycleCount b τ (p + e) :=
            recycleCount_succ_of_not_recycle b hCe hCnext hnr
          rw [hidx, hrc', hrc]
  obtain ⟨_, hfin⟩ := hQ (j₀ - p) (by omega)
  rw [show p + (j₀ - p) = j₀ from by omega] at hfin
  exact hfin

/-- **A `sync_nb`'s thread is parked in `nb.synced` just before its recycle.** At
the configuration preceding `η`'s execution time, `η.thread` is in `nb`'s synced
list (its sync head is dropped only by the recycle that wakes the synced
list). -/
theorem synced_before_recycle {C₀ : Config} {τ : List Config} {nb : NamedBarrier}
    {t : ThreadId} {η : ProgPoint} {nn : ℕ+} {n : Nat}
    (hm : IsTimeOf C₀ τ η n) (hηt : η.thread = t)
    (hcmd : η.cmd C₀ = some (Cmd.sync_nb nb nn)) {sm : State} {Tm : CTA}
    (hCm : τ[n - 1]? = some (Config.run sm Tm)) : t ∈ (sm.BN nb).synced := by
  obtain ⟨hτ, hidxL, j, C, C', hn, hCj, hCj1, hCeq, hC'eq⟩ := hm
  subst hn
  simp only [Nat.add_sub_cancel] at hCm
  rw [hCm, Option.some.injEq] at hCj
  subst hCj
  have hstep : CTAStep (Config.run sm Tm) C' := chain_step hτ.1.subtrace hCm hCj1
  have hhead : (C₀.progOf η.thread)[η.idx]'hidxL = Cmd.sync_nb nb nn := by
    have hc := hcmd
    simp only [ProgPoint.cmd] at hc
    rw [List.getElem?_eq_getElem hidxL, Option.some.injEq] at hc
    exact hc
  have hCsync : (Config.run sm Tm).progOf t = Cmd.sync_nb nb nn :: C'.progOf t := by
    rw [← hηt]
    rw [hCeq, hC'eq, List.drop_eq_getElem_cons hidxL, hhead]
  have hsmprog : Tm.prog t = Cmd.sync_nb nb nn :: C'.progOf t := hCsync
  have hrec : stepRecyclesBarrier (.inl nb) (Config.run sm Tm) C' = true :=
    sync_drop_recycles hstep hCsync rfl
  cases hstep with
  | @interleave _ s'' _ i P' hi hbar hmbar hth =>
    exfalso
    have hnf : (sm.BN nb).isFull = false := by
      rcases hbar nb with h | ⟨I, A, n₀, hbn, hlt⟩
      · rw [h]
        simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured]
      · rw [hbn]
        simp only [NamedBarrierState.isFull, beq_eq_false_iff_ne]
        omega
    simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf] at hrec
  | @recycle _ _ nb₀ I A m hb hfull hpark =>
    by_cases hit : t ∈ I
    · have hp := hpark t hit
      rw [hsmprog] at hp
      simp only [List.head?_cons, Option.some.injEq, Cmd.sync_nb.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      rw [hb]
      exact hit
    · exfalso
      simp [WeftCommon.Config.progOf, WeftCommon.CTA.wake, hit] at hsmprog
  | @mb_recycle _ _ sb₀ I A m ph hb hfull hpark =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?,
      isFull_and_unconfigured_false] at hrec
  | @done _ _ hdone _ _ =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?,
      isFull_and_unconfigured_false] at hrec
  | @error _ _ i P' _ _ hth =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?] at hrec

/-- **A thread joining a blocking list witnesses both interleave guards.** If
`t` is *not* blocked at `b` in `C` but *is* in `C'`, the step is an
`interleave` (only the parking rules add to a blocking list), so its `hbar` and
`hmbar` premises hold at `C`. -/
theorem guards_of_joins_blocked {C C' : Config} (hstep : CTAStep C C')
    {b : NamedBarrier ⊕ SharedBarrier} {t : ThreadId}
    {s : State} (hCs : C.state? = some s) {s' : State} (hCs' : C'.state? = some s')
    (hnotin : t ∉ s.blocked b) (hin : t ∈ s'.blocked b) :
    (∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
        ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat)) ∧
    (∀ sb, s.BM sb = MBarrierState.uninitialized ∨
        ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat)) := by
  cases hstep with
  | @interleave s₀ s₁ T i P' hi hbar hmbar hth =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs
    subst hCs
    exact ⟨hbar, hmbar⟩
  | @recycle s₀ T nb₀ I A n hb hfull hpark =>
    exfalso
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    cases b with
    | inr sb => exact hnotin hin
    | inl nb =>
      by_cases hbb : nb = nb₀
      · subst hbb
        change t ∈ (Function.update s₀.BN nb NamedBarrierState.unconfigured nb).synced at hin
        rw [Function.update_self] at hin
        simp [NamedBarrierState.unconfigured] at hin
      · change t ∈ (Function.update s₀.BN nb₀ NamedBarrierState.unconfigured nb).synced at hin
        rw [Function.update_of_ne hbb] at hin
        exact hnotin hin
  | @mb_recycle s₀ T sb₀ I A n ph hb hfull hpark =>
    exfalso
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    cases b with
    | inl nb => exact hnotin hin
    | inr sb =>
      by_cases hbb : sb = sb₀
      · subst hbb
        change t ∈ (Function.update s₀.BM sb ⟨[], 0, some n, !ph⟩ sb).waiting at hin
        rw [Function.update_self] at hin
        simp at hin
      · change t ∈ (Function.update s₀.BM sb₀ ⟨[], 0, some n, !ph⟩ sb).waiting at hin
        rw [Function.update_of_ne hbb] at hin
        exact hnotin hin
  | @done s₀ T hdone _ _ =>
    exfalso
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
    subst hCs; subst hCs'
    exact hnotin hin
  | @error s₀ T i P' _ _ hth =>
    exact absurd hCs' (by simp [WeftCommon.Config.state?])

/-- A reachability witness `C₀ ⤳* C` is realized by an actual chain (subtrace)
from `C₀` ending at `C`. -/
theorem exists_chain_of_reaches {C₀ C : Config}
    (h : Relation.ReflTransGen CTAStep C₀ C) :
    ∃ l : List Config, List.IsChain CTAStep l ∧ l.head? = some C₀ ∧ l.getLast? = some C := by
  induction h with
  | refl => exact ⟨[C₀], List.isChain_singleton _, rfl, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨l, hchain, hhd, hlast⟩ := ih
    have hne : l ≠ [] := by intro hl; rw [hl] at hhd; simp at hhd
    refine ⟨l ++ [c], ?_, ?_, ?_⟩
    · refine List.IsChain.append hchain (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [hlast, Option.mem_some_iff] at hx; subst hx
      rw [List.head?_cons, Option.mem_some_iff] at hy; subst hy
      exact hbc
    · rw [List.head?_append_of_ne_nil _ hne]; exact hhd
    · simp

/-- From a reachable configuration of a well-synchronized CTA, no thread step
produces `err`: such a step would extend the reaching trace to a complete trace
ending in `err`, contradicting `completeTrace_ends_done`. -/
theorem no_err_of_reach {T : CTA} (hws : T.WellSynchronized) {C : Config}
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C) :
    ¬ ∃ T', CTAStep C (Config.err T') := by
  rintro ⟨T', herr⟩
  obtain ⟨l, hchain, hhd, hlast⟩ := exists_chain_of_reaches (hreach.tail herr)
  obtain ⟨sd, hd⟩ := CTA.WellSynchronized.completeTrace_ends_done hws
    ⟨⟨hchain, Config.err T', hlast, Or.inr (Or.inl ⟨T', rfl⟩)⟩, hhd⟩
  rw [hlast] at hd; simp at hd

/-- **Progress** (the operational crux). From a `G`-bounded, reachable
configuration at which `G` is not yet exhausted, there is a step that keeps the
configuration `G`-bounded — a `G`-step that makes progress without touching
`F`. -/
theorem gstep {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {C : Config} (hGB : GBounded T τ η₁ C)
    (hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T) C)
    (hnotdone : ¬ Gdone T τ η₁ C) :
    ∃ C', CTAStep C C' ∧ GBounded T τ η₁ C' := by
  classical
  obtain ⟨s, T_C, rfl, hbound, hpurity⟩ := hGB
  have hwf : (Config.WF (Config.run s T_C)) := WF_of_reaches hreach
  have hBIs : s.BlockInv := hwf.2.2.2.2.2
  simp only [Gdone, not_forall] at hnotdone
  obtain ⟨i₀, hi₀ids, hi₀ne⟩ := hnotdone
  obtain ⟨e₀, he₀le, he₀prog⟩ := hbound i₀
  have hi₀G : e₀ < fcut T τ η₁ i₀ := by
    simp only [WeftCommon.Config.progOf] at hi₀ne
    rw [he₀prog, List.length_drop] at hi₀ne
    have hcl := fcut_le_length T τ η₁ i₀
    omega
  by_cases hfullN : ∃ nb I A n, s.BN nb = (⟨I, A, some n⟩ : NamedBarrierState) ∧
      I.length + A = (n : Nat)
  · -- **Case A (named)**: a named barrier is full — recycle it.
    obtain ⟨nb, I, A, n, hbeq, hbfull⟩ := hfullN
    have hpark : ∀ j ∈ I, (T_C.prog j).head? = some (Cmd.sync_nb nb n) :=
      (hwf.1 nb I A n hbeq).2.1
    refine ⟨_, CTAStep.recycle hbeq hbfull hpark, _, _, rfl, ?_, ?_⟩
    · intro j
      obtain ⟨e, hele, heprog⟩ := hbound j
      by_cases hjI : j ∈ I
      · have hpj := hpurity (.inl nb) j
          (by change j ∈ (s.BN nb).synced; rw [hbeq]; exact hjI)
        rw [heprog, List.length_drop] at hpj
        have hcl := fcut_le_length T τ η₁ j
        refine ⟨e + 1, by omega, ?_⟩
        simp only [WeftCommon.CTA.wake, hjI, if_true]
        rw [heprog, List.tail_drop]
      · exact ⟨e, hele, by simp only [WeftCommon.CTA.wake, hjI, if_false]; exact heprog⟩
    · intro b' j hj'
      have hpre : j ∈ s.blocked b' ∧ b' ≠ (.inl nb) := by
        cases b' with
        | inl nb' =>
          by_cases hbb : nb' = nb
          · subst hbb
            exfalso
            change j ∈ (Function.update s.BN nb' NamedBarrierState.unconfigured nb').synced
              at hj'
            rw [Function.update_self] at hj'
            simp [NamedBarrierState.unconfigured] at hj'
          · refine ⟨?_, fun h => hbb (Sum.inl.inj h)⟩
            change j ∈ (Function.update s.BN nb NamedBarrierState.unconfigured nb').synced
              at hj'
            rw [Function.update_of_ne hbb] at hj'
            exact hj'
        | inr sb' => exact ⟨hj', fun h => nomatch h⟩
      obtain ⟨hjpre, hb'ne⟩ := hpre
      have hjnotI : j ∉ I := by
        intro hjI
        have hjb : j ∈ s.blocked (.inl nb) := by
          change j ∈ (s.BN nb).synced; rw [hbeq]; exact hjI
        exact hb'ne (hBIs.2.2 b' (.inl nb) j hjpre hjb)
      have hpj := hpurity b' j hjpre
      simpa only [WeftCommon.CTA.wake, hjnotI, if_false] using hpj
  by_cases hfullM : ∃ sb I A n ph, s.BM sb = (⟨I, A, some n, ph⟩ : MBarrierState) ∧
      A = (n : Nat)
  · -- **Case A (mbarrier)**: an mbarrier is full in arrivals — mb-recycle it.
    obtain ⟨sb, I, A, n, ph, hbeq, hbfull⟩ := hfullM
    have hpark : ∀ j ∈ I, (T_C.prog j).head? = some (Cmd.wait_mb sb ph) :=
      (hwf.2.2.1 sb I A n ph hbeq).2
    refine ⟨_, CTAStep.mb_recycle hbeq hbfull hpark, _, _, rfl, ?_, ?_⟩
    · intro j
      obtain ⟨e, hele, heprog⟩ := hbound j
      by_cases hjI : j ∈ I
      · have hpj := hpurity (.inr sb) j
          (by change j ∈ (s.BM sb).waiting; rw [hbeq]; exact hjI)
        rw [heprog, List.length_drop] at hpj
        have hcl := fcut_le_length T τ η₁ j
        refine ⟨e + 1, by omega, ?_⟩
        simp only [WeftCommon.CTA.wake, hjI, if_true]
        rw [heprog, List.tail_drop]
      · exact ⟨e, hele, by simp only [WeftCommon.CTA.wake, hjI, if_false]; exact heprog⟩
    · intro b' j hj'
      have hpre : j ∈ s.blocked b' ∧ b' ≠ (.inr sb) := by
        cases b' with
        | inr sb' =>
          by_cases hbb : sb' = sb
          · subst hbb
            exfalso
            change j ∈ (Function.update s.BM sb' ⟨[], 0, some n, !ph⟩ sb').waiting at hj'
            rw [Function.update_self] at hj'
            simp at hj'
          · refine ⟨?_, fun h => hbb (Sum.inr.inj h)⟩
            change j ∈ (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb').waiting at hj'
            rw [Function.update_of_ne hbb] at hj'
            exact hj'
        | inl nb' => exact ⟨hj', fun h => nomatch h⟩
      obtain ⟨hjpre, hb'ne⟩ := hpre
      have hjnotI : j ∉ I := by
        intro hjI
        have hjb : j ∈ s.blocked (.inr sb) := by
          change j ∈ (s.BM sb).waiting; rw [hbeq]; exact hjI
        exact hb'ne (hBIs.2.2 b' (.inr sb) j hjpre hjb)
      have hpj := hpurity b' j hjpre
      simpa only [WeftCommon.CTA.wake, hjnotI, if_false] using hpj
  · -- **Case B**: no barrier of either kind is full, so both guards hold.
    push Not at hfullN hfullM
    have hbar : ∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
        ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
      intro nb
      obtain ⟨bI, bA, bcnt, hbc⟩ : ∃ bI bA bcnt, s.BN nb = ⟨bI, bA, bcnt⟩ := ⟨_, _, _, rfl⟩
      cases bcnt with
      | none =>
        obtain ⟨rfl, rfl⟩ := hwf.2.1 nb bI bA hbc
        exact Or.inl hbc
      | some n =>
        obtain ⟨hle, _, _⟩ := hwf.1 nb bI bA n hbc
        exact Or.inr ⟨bI, bA, n, hbc, lt_of_le_of_ne hle (hfullN nb bI bA n hbc)⟩
    have hmbar : ∀ sb, s.BM sb = MBarrierState.uninitialized ∨
        ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat) := by
      intro sb
      obtain ⟨bI, bA, bcnt, bph, hbc⟩ : ∃ bI bA bcnt bph, s.BM sb = ⟨bI, bA, bcnt, bph⟩ :=
        ⟨_, _, _, _, rfl⟩
      cases bcnt with
      | none =>
        obtain ⟨rfl, rfl, rfl⟩ := hwf.2.2.2.1 sb bI bA bph hbc
        exact Or.inl hbc
      | some n =>
        obtain ⟨hle, _⟩ := hwf.2.2.1 sb bI bA n bph hbc
        exact Or.inr ⟨bI, bA, n, bph, hbc, lt_of_le_of_ne hle (hfullM sb bI bA n bph hbc)⟩
    by_cases hen : ∃ i e, e < fcut T τ η₁ i ∧ T_C.prog i = (T.prog i).drop e ∧ s.E i = true
    · -- **Case B1**: an enabled `G`-thread can step.
      obtain ⟨i, e, helt, heprog, hien⟩ := hen
      have hi_len : e < (T.prog i).length := lt_of_lt_of_le helt (fcut_le_length T τ η₁ i)
      have hiids : i ∈ T_C.ids := by
        by_contra hni
        have h0 := T_C.nil_outside_ids i hni
        rw [heprog, List.drop_eq_nil_iff] at h0
        omega
      have hhead : T_C.prog i = (T.prog i)[e]'hi_len :: (T.prog i).drop (e + 1) := by
        rw [heprog, List.drop_eq_getElem_cons hi_len]
      have gbAdvance : ∀ s', (∀ b'', s'.blocked b'' = s.blocked b'') →
          GBounded T τ η₁ (Config.run s' (T_C.set i hiids ((T.prog i).drop (e + 1)))) := by
        intro s' hblk
        refine ⟨s', _, rfl, ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst hji
            exact ⟨e + 1, by omega, by simp [WeftCommon.CTA.set, Function.update_self]⟩
          · obtain ⟨ej, hjle, hjprog⟩ := hbound j
            exact ⟨ej, hjle, by
              simp only [WeftCommon.CTA.set, Function.update_of_ne hji]; exact hjprog⟩
        · intro b'' j hj
          rw [hblk] at hj
          have hjnoti : j ≠ i := by
            intro hji
            subst hji
            rw [hBIs.2.1 b'' j hj] at hien
            exact absurd hien (by simp)
          have hpj := hpurity b'' j hj
          simp only [WeftCommon.CTA.set, Function.update_of_ne hjnoti]
          exact hpj
      have gbPark : ∀ (s' : State) (T' : CTA), (∀ j, T'.prog j = T_C.prog j) →
          (∀ b'' j, j ∈ s'.blocked b'' → j = i ∨ j ∈ s.blocked b'') →
          GBounded T τ η₁ (Config.run s' T') := by
        intro s' T' hprogeq hblk
        refine ⟨s', T', rfl, fun j => ?_, ?_⟩
        · obtain ⟨ej, hjle, hjprog⟩ := hbound j
          exact ⟨ej, hjle, by rw [hprogeq]; exact hjprog⟩
        · intro b'' j hj
          rw [hprogeq]
          rcases hblk b'' j hj with rfl | hjold
          · rw [heprog, List.length_drop]
            have hcl := fcut_le_length T τ η₁ j
            omega
          · exact hpurity b'' j hjold
      cases hcmd : (T.prog i)[e]'hi_len with
      | read g =>
        exact ⟨_, CTAStep.interleave hiids hbar hmbar
          (by rw [hhead, hcmd]; exact ThreadStep.read_noop), gbAdvance s (fun _ => rfl)⟩
      | write g =>
        exact ⟨_, CTAStep.interleave hiids hbar hmbar
          (by rw [hhead, hcmd]; exact ThreadStep.write_noop), gbAdvance s (fun _ => rfl)⟩
      | arrive_nb nb n =>
        rcases hbar nb with hbu | ⟨I, A, n', hbcfg, hlt⟩
        · refine ⟨_, CTAStep.interleave hiids hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.arrive_configure hien hbu), gbAdvance _ ?_⟩
          intro b''
          cases b'' with
          | inr sb' => rfl
          | inl nb' =>
            by_cases hbb : nb' = nb
            · subst hbb
              change (Function.update s.BN nb' ⟨[], 1, some n⟩ nb').synced
                = (s.BN nb').synced
              rw [Function.update_self, hbu]
              rfl
            · change (Function.update s.BN nb ⟨[], 1, some n⟩ nb').synced
                = (s.BN nb').synced
              rw [Function.update_of_ne hbb]
        · by_cases hn : n = n'
          · subst hn
            have hApos : 0 < I.length + A := (hwf.1 nb I A n hbcfg).2.2
            refine ⟨_, CTAStep.interleave hiids hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.arrive_register hien hbcfg hApos hlt),
              gbAdvance _ ?_⟩
            intro b''
            cases b'' with
            | inr sb' => rfl
            | inl nb' =>
              by_cases hbb : nb' = nb
              · subst hbb
                change (Function.update s.BN nb' ⟨I, A + 1, some n⟩ nb').synced
                  = (s.BN nb').synced
                rw [Function.update_self, hbcfg]
              · change (Function.update s.BN nb ⟨I, A + 1, some n⟩ nb').synced
                  = (s.BN nb').synced
                rw [Function.update_of_ne hbb]
          · exact absurd ⟨_, CTAStep.error hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.arrive_err_count hien hbcfg (Ne.symm hn))⟩
              (no_err_of_reach hws hreach)
      | sync_nb nb n =>
        have hprogeq : ∀ j, (T_C.set i hiids
            (Cmd.sync_nb nb n :: (T.prog i).drop (e + 1))).prog j = T_C.prog j := by
          intro j
          by_cases hj : j = i
          · subst hj
            simp only [WeftCommon.CTA.set, Function.update_self]
            rw [hhead, hcmd]
          · simp only [WeftCommon.CTA.set, Function.update_of_ne hj]
        rcases hbar nb with hbu | ⟨I, A, n', hbcfg, hlt⟩
        · refine ⟨_, CTAStep.interleave hiids hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.sync_configure hien hbu),
            gbPark _ _ hprogeq ?_⟩
          intro b'' j hj
          cases b'' with
          | inr sb' => exact Or.inr hj
          | inl nb' =>
            by_cases hbb : nb' = nb
            · subst hbb
              change j ∈ (Function.update s.BN nb' ⟨[i], 0, some n⟩ nb').synced at hj
              rw [Function.update_self] at hj
              simp only [List.mem_singleton] at hj
              exact Or.inl hj
            · change j ∈ (Function.update s.BN nb ⟨[i], 0, some n⟩ nb').synced at hj
              rw [Function.update_of_ne hbb] at hj
              exact Or.inr hj
        · by_cases hn : n = n'
          · subst hn
            have hApos : 0 < I.length + A := (hwf.1 nb I A n hbcfg).2.2
            refine ⟨_, CTAStep.interleave hiids hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.sync_block hien hbcfg hApos hlt),
              gbPark _ _ hprogeq ?_⟩
            intro b'' j hj
            cases b'' with
            | inr sb' => exact Or.inr hj
            | inl nb' =>
              by_cases hbb : nb' = nb
              · subst hbb
                change j ∈ (Function.update s.BN nb' ⟨i :: I, A, some n⟩ nb').synced at hj
                rw [Function.update_self] at hj
                simp only [List.mem_cons] at hj
                rcases hj with rfl | hj
                · exact Or.inl rfl
                · exact Or.inr (by change j ∈ (s.BN nb').synced; rw [hbcfg]; exact hj)
              · change j ∈ (Function.update s.BN nb ⟨i :: I, A, some n⟩ nb').synced at hj
                rw [Function.update_of_ne hbb] at hj
                exact Or.inr hj
          · exact absurd ⟨_, CTAStep.error hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.sync_err_count hien hbcfg (Ne.symm hn))⟩
              (no_err_of_reach hws hreach)
      | init_mb sb n =>
        rcases hmbar sb with hbu | ⟨I, A, n', ph, hbcfg, hlt⟩
        · refine ⟨_, CTAStep.interleave hiids hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.mb_init hien hbu), gbAdvance _ ?_⟩
          intro b''
          cases b'' with
          | inl nb' => rfl
          | inr sb' =>
            by_cases hbb : sb' = sb
            · subst hbb
              change (Function.update s.BM sb' ⟨[], 0, some n, false⟩ sb').waiting
                = (s.BM sb').waiting
              rw [Function.update_self, hbu]
              rfl
            · change (Function.update s.BM sb ⟨[], 0, some n, false⟩ sb').waiting
                = (s.BM sb').waiting
              rw [Function.update_of_ne hbb]
        · exact absurd ⟨_, CTAStep.error hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.mb_init_err hien hbcfg)⟩
            (no_err_of_reach hws hreach)
      | arrive_mb sb =>
        rcases hmbar sb with hbu | ⟨I, A, n', ph, hbcfg, hlt⟩
        · exact absurd ⟨_, CTAStep.error hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.mb_arrive_err hien hbu)⟩
            (no_err_of_reach hws hreach)
        · refine ⟨_, CTAStep.interleave hiids hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.mb_arrive hien hbcfg), gbAdvance _ ?_⟩
          intro b''
          cases b'' with
          | inl nb' => rfl
          | inr sb' =>
            by_cases hbb : sb' = sb
            · subst hbb
              change (Function.update s.BM sb' ⟨I, A + 1, some n', ph⟩ sb').waiting
                = (s.BM sb').waiting
              rw [Function.update_self, hbcfg]
            · change (Function.update s.BM sb ⟨I, A + 1, some n', ph⟩ sb').waiting
                = (s.BM sb').waiting
              rw [Function.update_of_ne hbb]
      | wait_mb sb ph =>
        rcases hmbar sb with hbu | ⟨I, A, n', ph', hbcfg, hlt⟩
        · exact absurd ⟨_, CTAStep.error hbar hmbar
            (by rw [hhead, hcmd]; exact ThreadStep.mb_wait_err hien hbu)⟩
            (no_err_of_reach hws hreach)
        · by_cases hph : ph = ph'
          · -- matched phase: the wait blocks (parks)
            subst hph
            have hprogeq : ∀ j, (T_C.set i hiids
                (Cmd.wait_mb sb ph :: (T.prog i).drop (e + 1))).prog j = T_C.prog j := by
              intro j
              by_cases hj : j = i
              · subst hj
                simp only [WeftCommon.CTA.set, Function.update_self]
                rw [hhead, hcmd]
              · simp only [WeftCommon.CTA.set, Function.update_of_ne hj]
            refine ⟨_, CTAStep.interleave hiids hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.mb_wait_block hien hbcfg),
              gbPark _ _ hprogeq ?_⟩
            intro b'' j hj
            cases b'' with
            | inl nb' => exact Or.inr hj
            | inr sb' =>
              by_cases hbb : sb' = sb
              · subst hbb
                change j ∈ (Function.update s.BM sb' ⟨i :: I, A, some n', ph⟩ sb').waiting
                  at hj
                rw [Function.update_self] at hj
                simp only [List.mem_cons] at hj
                rcases hj with rfl | hj
                · exact Or.inl rfl
                · exact Or.inr (by change j ∈ (s.BM sb').waiting; rw [hbcfg]; exact hj)
              · change j ∈ (Function.update s.BM sb ⟨i :: I, A, some n', ph⟩ sb').waiting
                  at hj
                rw [Function.update_of_ne hbb] at hj
                exact Or.inr hj
          · -- mismatched phase: the wait passes through
            exact ⟨_, CTAStep.interleave hiids hbar hmbar
              (by rw [hhead, hcmd]; exact ThreadStep.mb_wait_pass hien hbcfg hph),
              gbAdvance s (fun _ => rfl)⟩
    · -- **Case B2**: every `G`-thread is parked — impossible by deadlock-freedom.
      exfalso
      -- `i₀` is a `G`-thread, so by `hen` it is disabled, hence blocked (`EnabledInv`).
      have hi₀dis : s.E i₀ = false := by
        by_contra h
        rw [Bool.not_eq_false] at h
        exact hen ⟨i₀, e₀, hi₀G, he₀prog, h⟩
      obtain ⟨lc, hlchain, hlhd, hllast⟩ := exists_chain_of_reaches hreach
      have hei : ∀ C ∈ lc, ∀ s', C.state? = some s' → s'.EnabledInv :=
        enabledInv_chain hlchain hlhd (by
          intro s' hs'
          simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'
          subst hs'
          exact State.EnabledInv.initial)
      have hCmem : Config.run s T_C ∈ lc := List.mem_of_mem_getLast? hllast
      obtain ⟨b₁, hi₀b₁⟩ := hei _ hCmem s rfl i₀ hi₀dis
      -- Build the full trace `tr` from `initial` through `C` to a terminal state.
      have hbwC : (Config.barriersWithin T.barrierSet (Config.run s T_C)) :=
        barriersWithin_of_reaches hreach
      obtain ⟨σ, hσIC, hσhd⟩ := exists_completeTrace T.barrierSet (Config.run s T_C) hbwC
      obtain ⟨σtail, rfl⟩ : ∃ l, σ = Config.run s T_C :: l := by
        cases σ with
        | nil => simp at hσhd
        | cons a l =>
          simp only [List.head?_cons, Option.some.injEq] at hσhd
          exact ⟨l, hσhd ▸ rfl⟩
      have hlne : lc ≠ [] := by intro h; rw [h] at hlhd; simp at hlhd
      have hσchain : List.IsChain CTAStep (Config.run s T_C :: σtail) := hσIC.subtrace
      rw [List.isChain_cons] at hσchain
      set tr := lc ++ σtail with htrdef
      have htrIC : IsCompleteTraceFrom (Config.run State.initial T) tr := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · refine List.IsChain.append hlchain hσchain.2 ?_
          intro x hx y hy
          rw [hllast, Option.mem_some_iff] at hx
          subst hx
          exact hσchain.1 y hy
        · obtain ⟨Cₙ, hτlast, hterm⟩ := hσIC.ends
          refine ⟨Cₙ, ?_, hterm⟩
          have hgl : lc.getLast hlne = Config.run s T_C := by
            have h := List.getLast?_eq_some_getLast hlne
            rw [hllast] at h
            exact (Option.some.injEq _ _).mp h.symm
          have hsplit : lc ++ σtail = lc.dropLast ++ (Config.run s T_C :: σtail) := by
            conv_lhs => rw [← List.dropLast_concat_getLast hlne, hgl]
            simp
          rw [htrdef, hsplit]
          exact List.mem_getLast?_append_of_mem_getLast? hτlast
        · rw [htrdef, List.head?_append_of_ne_nil _ hlne]
          exact hlhd
      obtain ⟨sdone, htrdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrIC
      set pc := lc.length - 1 with hpcdef
      have htrpc : tr[pc]? = some (Config.run s T_C) := by
        rw [htrdef, List.getElem?_append_left
          (by have := List.length_pos_of_ne_nil hlne; omega),
          ← List.getLast?_eq_getElem?]
        exact hllast
      have hBItr : ∀ C ∈ tr, ∀ s', C.state? = some s' → s'.BlockInv :=
        blockInv_chain htrIC.1.subtrace htrIC.2 (by
          intro s' hs'
          simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'
          subst hs'
          exact State.BlockInv.initial)
      have hi₀L : e₀ < (T.prog i₀).length := lt_of_lt_of_le hi₀G (fcut_le_length T τ η₁ i₀)
      have hb₁ne : s.blocked b₁ ≠ [] := by
        intro h
        rw [h] at hi₀b₁
        exact absurd hi₀b₁ (by simp)
      -- `dw` = first recycle (after `pc`) of a barrier holding a `C`-blocked thread.
      have hPex : ∃ d, pc ≤ d ∧ ∃ b C C', s.blocked b ≠ [] ∧
          tr[d]? = some C ∧ tr[d + 1]? = some C' ∧ stepRecyclesBarrier b C C' = true := by
        by_contra hno
        push Not at hno
        -- `i₀` stays blocked at `b₁` while no `b₁`-recycle fires
        have hstay : ∀ M, (∃ CM, tr[M + 1]? = some CM) → ∀ d, pc + d ≤ M →
            ∃ sd Td, tr[pc + d]? = some (Config.run sd Td) ∧ i₀ ∈ sd.blocked b₁ := by
          intro M hM d
          induction d with
          | zero => intro _; exact ⟨s, T_C, htrpc, hi₀b₁⟩
          | succ e ih =>
            intro hle
            obtain ⟨sd, Td, hCe, hblk⟩ := ih (by omega)
            obtain ⟨CM, hCM⟩ := hM
            have hMlt : M + 1 < tr.length := (List.getElem?_eq_some_iff.mp hCM).1
            obtain ⟨Cnext, hCnext⟩ : ∃ C, tr[pc + e + 1]? = some C :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            have hstep := chain_step htrIC.1.subtrace hCe hCnext
            have hnr : stepRecyclesBarrier b₁ (Config.run sd Td) Cnext = false := by
              by_contra hrec
              rw [Bool.not_eq_false] at hrec
              exact hno (pc + e) (by omega) b₁ _ _ hb₁ne hCe hCnext hrec
            obtain ⟨s'', T'', rfl⟩ : ∃ s'' T'', Cnext = Config.run s'' T'' := by
              obtain ⟨Cnn, hCnn⟩ : ∃ C, tr[pc + e + 1 + 1]? = some C :=
                ⟨_, List.getElem?_eq_getElem (by omega)⟩
              cases chain_step htrIC.1.subtrace hCnext hCnn <;> exact ⟨_, _, rfl⟩
            refine ⟨s'', T'', hCnext, blocked_persists hstep rfl ?_ hblk hnr rfl⟩
            exact hBItr _ (List.mem_of_getElem? hCe) sd rfl
        cases b₁ with
        | inl nb₁ =>
          rcases hbar nb₁ with hbu | ⟨I₁, A₁, n₁, hb₁eq, hb₁lt⟩
          · change i₀ ∈ (s.BN nb₁).synced at hi₀b₁
            rw [hbu] at hi₀b₁
            simp [NamedBarrierState.unconfigured] at hi₀b₁
          · have hi₀head : (T_C.prog i₀).head? = some (Cmd.sync_nb nb₁ n₁) :=
              (hwf.1 nb₁ I₁ A₁ n₁ hb₁eq).2.1 i₀ (by
                change i₀ ∈ (s.BN nb₁).synced at hi₀b₁
                rw [hb₁eq] at hi₀b₁
                exact hi₀b₁)
            have hi₀cmd : (T.prog i₀)[e₀]'hi₀L = Cmd.sync_nb nb₁ n₁ := by
              have hdr : T_C.prog i₀ = (T.prog i₀)[e₀]'hi₀L :: (T.prog i₀).drop (e₀ + 1) := by
                rw [he₀prog, List.drop_eq_getElem_cons hi₀L]
              rw [hdr, List.head?_cons, Option.some.injEq] at hi₀head
              exact hi₀head
            have hci₀cmd : T.cmdAt (⟨i₀, e₀⟩ : ProgPoint) = some (Cmd.sync_nb nb₁ n₁) := by
              simp only [CTA.cmdAt]
              rw [List.getElem?_eq_getElem hi₀L, hi₀cmd]
            have hci₀L : (⟨i₀, e₀⟩ : ProgPoint).idx <
                ((Config.run State.initial T).progOf (⟨i₀, e₀⟩ : ProgPoint).thread).length :=
              hi₀L
            obtain ⟨m₀, hm₀⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨i₀, e₀⟩) hci₀L
            have hpcm₀ : pc < m₀ := by
              refine lt_time_of_lt_progOf hm₀ htrpc ?_
              change ((Config.run State.initial T).progOf i₀).length - e₀ - 1
                < (T_C.prog i₀).length
              rw [he₀prog, List.length_drop]
              change (T.prog i₀).length - e₀ - 1 < (T.prog i₀).length - e₀
              omega
            obtain ⟨Cm, Cm', hCm, hCm', hrecm⟩ := sync_time_recycles hm₀ hci₀cmd
            have hCm2 : tr[m₀ - 1 + 1]? = some Cm' := by
              rw [show m₀ - 1 + 1 = m₀ by omega]
              exact hCm'
            exact hno (m₀ - 1) (by omega) (.inl nb₁) Cm Cm' hb₁ne hCm hCm2 hrecm
        | inr sb₁ =>
          rcases hmbar sb₁ with hbu | ⟨I₁, A₁, n₁, ph₁, hb₁eq, hb₁lt⟩
          · change i₀ ∈ (s.BM sb₁).waiting at hi₀b₁
            rw [hbu] at hi₀b₁
            simp [MBarrierState.uninitialized] at hi₀b₁
          · have hi₀head : (T_C.prog i₀).head? = some (Cmd.wait_mb sb₁ ph₁) :=
              (hwf.2.2.1 sb₁ I₁ A₁ n₁ ph₁ hb₁eq).2 i₀ (by
                change i₀ ∈ (s.BM sb₁).waiting at hi₀b₁
                rw [hb₁eq] at hi₀b₁
                exact hi₀b₁)
            have hi₀cmd : (T.prog i₀)[e₀]'hi₀L = Cmd.wait_mb sb₁ ph₁ := by
              have hdr : T_C.prog i₀ = (T.prog i₀)[e₀]'hi₀L :: (T.prog i₀).drop (e₀ + 1) := by
                rw [he₀prog, List.drop_eq_getElem_cons hi₀L]
              rw [hdr, List.head?_cons, Option.some.injEq] at hi₀head
              exact hi₀head
            have hci₀cmd : T.cmdAt (⟨i₀, e₀⟩ : ProgPoint) = some (Cmd.wait_mb sb₁ ph₁) := by
              simp only [CTA.cmdAt]
              rw [List.getElem?_eq_getElem hi₀L, hi₀cmd]
            have hci₀L : (⟨i₀, e₀⟩ : ProgPoint).idx <
                ((Config.run State.initial T).progOf (⟨i₀, e₀⟩ : ProgPoint).thread).length :=
              hi₀L
            obtain ⟨m₀, hm₀⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨i₀, e₀⟩) hci₀L
            have hpcm₀ : pc < m₀ := by
              refine lt_time_of_lt_progOf hm₀ htrpc ?_
              change ((Config.run State.initial T).progOf i₀).length - e₀ - 1
                < (T_C.prog i₀).length
              rw [he₀prog, List.length_drop]
              change (T.prog i₀).length - e₀ - 1 < (T.prog i₀).length - e₀
              omega
            have hm₀valid : ∃ CM, tr[m₀ - 1 + 1]? = some CM := by
              obtain ⟨_, _, j, C1, C2, hj, hC1, hC2, _, _⟩ := hm₀
              refine ⟨C2, ?_⟩
              rw [show m₀ - 1 + 1 = m₀ by omega, hj]
              exact hC2
            rcases wait_time_recycles_or_pass hm₀ hci₀cmd with
              ⟨Cm, Cm', hCm, hCm', hrecm⟩ | ⟨sp, Tp, hCp, hEp, hphp⟩
            · have hCm2 : tr[m₀ - 1 + 1]? = some Cm' := by
                rw [show m₀ - 1 + 1 = m₀ by omega]
                exact hCm'
              exact hno (m₀ - 1) (by omega) (.inr sb₁) Cm Cm' hb₁ne hCm hCm2 hrecm
            · -- the pass needs `i₀` enabled, but it is still blocked at `m₀ - 1`
              obtain ⟨sp', Tp', hCp', hblk'⟩ := hstay (m₀ - 1) hm₀valid (m₀ - 1 - pc)
                (by omega)
              rw [show pc + (m₀ - 1 - pc) = m₀ - 1 by omega] at hCp'
              rw [hCp] at hCp'
              have heq := Option.some.inj hCp'
              rw [WeftCommon.Config.run.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              have hdis : sp.E i₀ = false :=
                (hBItr _ (List.mem_of_getElem? hCp) sp rfl).2.1 (.inr sb₁) i₀ hblk'
              simp [hdis] at hEp
      set dw := Nat.find hPex with hdwdef
      obtain ⟨hpcdw, b'', Cd, Cd', hb''ne, hCd, hCd', hrecd⟩ := Nat.find_spec hPex
      have hnorec : ∀ d, pc ≤ d → d < dw → ∀ b, s.blocked b ≠ [] → ∀ C C',
          tr[d]? = some C → tr[d + 1]? = some C' → stepRecyclesBarrier b C C' = false := by
        intro d hpcd hddw b hbne C C' hC hC'
        by_contra hrec
        rw [Bool.not_eq_false] at hrec
        exact Nat.find_min hPex hddw ⟨hpcd, b, C, C', hbne, hC, hC', hrec⟩
      obtain ⟨t'', ht''⟩ : ∃ t, t ∈ s.blocked b'' := by
        rcases h : s.blocked b'' with _ | ⟨a, l⟩
        · exact absurd h hb''ne
        · exact ⟨a, by simp⟩
      have htrlen : dw + 1 < tr.length := (List.getElem?_eq_some_iff.mp hCd').1
      have htrget : ∀ d, d ≤ dw + 1 → ∃ C, tr[d]? = some C :=
        fun d hd => ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hrcc : ∀ d, pc ≤ d → d ≤ dw → recycleCount b'' tr d = recycleCount b'' tr pc := by
        intro d hpcd
        induction d, hpcd using Nat.le_induction with
        | base => intro _; rfl
        | succ d hpcd ih =>
          intro hsucc
          obtain ⟨Cd0, hCd0⟩ := htrget d (by omega)
          obtain ⟨Cd1, hCd1⟩ := htrget (d + 1) (by omega)
          have hnor := hnorec d hpcd (by omega) b'' hb''ne Cd0 Cd1 hCd0 hCd1
          rw [recycleCount_succ_of_not_recycle b'' hCd0 hCd1 hnor, ih (by omega)]
      have htr0 : tr[0]? = some (Config.run State.initial T) := by
        rw [← List.head?_eq_getElem?]
        exact htrIC.2
      -- `pointGen` transfers to `tr` via well-synchronization.
      have hgenTr : ∀ (c : ProgPoint) (cc : Cmd) (bb : NamedBarrier ⊕ SharedBarrier)
          (mc : Nat), T.cmdAt c = some cc → cc.barrier? = some bb → c ∈ T.progPoints →
          IsTimeOf (Config.run State.initial T) tr c mc →
          pointGen T τ c = some (cc.genValue (recycleCount bb tr (mc - 1))) := by
        intro c cc bb mc hccmd hcbar hcpt hmc
        obtain ⟨sdτ, hdτ⟩ := hτ.2
        obtain ⟨mτ, hmτ⟩ :=
          exists_time_of_ends_done hτ.1 hdτ ((mem_progPoints_iff T c).mp hcpt).2
        obtain ⟨g, hg1, hg2⟩ := hws.2 τ tr hτ.1 htrIC c
          ⟨bb, by change (T.cmdAt c).bind Cmd.barrier? = some bb; rw [hccmd]; exact hcbar⟩
        have hpg : some g = pointGen T τ c :=
          IsGenOf.unique hg1 (isGenOf_pointGen hccmd hcbar hmτ)
        have hval : g = cc.genValue (recycleCount bb tr (mc - 1)) :=
          isGenOf_genValue hg2 hccmd hcbar hmc
        rw [← hpg, hval]
      -- `t''`'s parked position is a `G`-point.
      obtain ⟨et, hetle, hetprog⟩ := hbound t''
      have hetG : et < fcut T τ η₁ t'' := by
        have hp := hpurity b'' t'' ht''
        rw [hetprog, List.length_drop] at hp
        have := fcut_le_length T τ η₁ t''
        omega
      have htL : et < (T.prog t'').length := lt_of_lt_of_le hetG (fcut_le_length T τ η₁ t'')
      -- every config in `[pc, dw]` is a `run`, and blocked threads stay blocked there
      have hrunC : ∀ d, pc ≤ d → d ≤ dw → ∃ sd Td, tr[d]? = some (Config.run sd Td) := by
        intro d hpcd hddw
        obtain ⟨C0, hC0⟩ := htrget d (by omega)
        obtain ⟨C1, hC1⟩ := htrget (d + 1) (by omega)
        have hstep := chain_step htrIC.1.subtrace hC0 hC1
        obtain ⟨sd, Td, rfl⟩ : ∃ sd Td, C0 = Config.run sd Td := by
          cases hstep <;> exact ⟨_, _, rfl⟩
        exact ⟨sd, Td, hC0⟩
      have hpers : ∀ (b : NamedBarrier ⊕ SharedBarrier) (t : ThreadId), t ∈ s.blocked b →
          ∀ d, pc ≤ d → d ≤ dw → ∀ sd Td, tr[d]? = some (Config.run sd Td) →
          t ∈ sd.blocked b := by
        intro b t ht d hpcd
        induction d, hpcd using Nat.le_induction with
        | base =>
          intro _ sd Td hsd
          rw [htrpc, Option.some.injEq, WeftCommon.Config.run.injEq] at hsd
          obtain ⟨rfl, rfl⟩ := hsd
          exact ht
        | succ d hpcd ih =>
          intro hd1dw sd' Td' hsd'
          obtain ⟨sd, Td, hsd⟩ := hrunC d hpcd (by omega)
          have htd : t ∈ sd.blocked b := ih (by omega) sd Td hsd
          have hbne : s.blocked b ≠ [] := fun h => by
            rw [h] at ht
            exact absurd ht (by simp)
          have hstep := chain_step htrIC.1.subtrace hsd hsd'
          exact blocked_persists hstep rfl (hBItr _ (List.mem_of_getElem? hsd) sd rfl) htd
            (hnorec d hpcd (by omega) b hbne _ _ hsd hsd') rfl
      -- a registrant enabled at a config of `[pc, dw]` whose point is hb-before
      -- `⟨t'', et⟩` would be an enabled `G`-thread — impossible in Case B2.
      have hregfalse : ∀ (d' : Nat) (sd : State) (Td : CTA), pc ≤ d' → d' ≤ dw →
          tr[d']? = some (Config.run sd Td) →
          ∀ (ii : ThreadId) (ed : Nat),
          ((⟨ii, ed⟩ : ProgPoint), (⟨t'', et⟩ : ProgPoint)) ∈ initRelation T τ →
          (⟨ii, ed⟩ : ProgPoint) ∈ T.progPoints →
          Td.prog ii = (T.prog ii).drop ed → sd.E ii = true → False := by
        intro d' sd Td hpcd' hd'dw hsd ii ed hedge hcipt hedprog hien
        have hctpt : (⟨t'', et⟩ : ProgPoint) ∈ T.progPoints :=
          (mem_progPoints_iff T _).mpr ⟨mem_ids_of_idx_lt T htL, htL⟩
        have hnotht : ¬ happensBefore T τ η₁ (⟨t'', et⟩ : ProgPoint) := fun hhb =>
          absurd (fcut_le_of_hb hhb hctpt) (not_le.mpr hetG)
        have hnothi : ¬ happensBefore T τ η₁ (⟨ii, ed⟩ : ProgPoint) := fun hhb =>
          hnotht (hhb.tail hedge)
        have hedfcut : ed < fcut T τ η₁ ii := lt_fcut_of_not_hb hnothi hcipt
        obtain ⟨ep, heple, hepprog⟩ := hbound ii
        have hsuf : (Config.run sd Td).progOf ii <:+ (Config.run s T_C).progOf ii :=
          progOf_suffix_index_le htrIC.1.subtrace ii htrpc hpcd' hsd
        have hepled : ep ≤ ed := by
          have hle : (Td.prog ii).length ≤ (T_C.prog ii).length := suffix_length_le hsuf
          rw [hedprog, hepprog, List.length_drop, List.length_drop] at hle
          have hedlen : ed ≤ (T.prog ii).length :=
            le_of_lt (lt_of_lt_of_le hedfcut (fcut_le_length _ _ _ _))
          have heplen : ep ≤ (T.prog ii).length := le_trans heple (fcut_le_length _ _ _ _)
          omega
        have hepfcut : ep < fcut T τ η₁ ii := lt_of_le_of_lt hepled hedfcut
        have hidisC : s.E ii = false := by
          by_contra h
          rw [Bool.not_eq_false] at h
          exact hen ⟨ii, ep, hepfcut, hepprog, h⟩
        obtain ⟨bi, hibi⟩ := hei (Config.run s T_C) hCmem s rfl ii hidisC
        have hidblk : ii ∈ sd.blocked bi := hpers bi ii hibi d' hpcd' hd'dw sd Td hsd
        have hidisd : sd.E ii = false :=
          (hBItr (Config.run sd Td) (List.mem_of_getElem? hsd) sd rfl).2.1 bi ii hidblk
        rw [hien] at hidisd
        exact absurd hidisd (by decide)
      -- Split on the kind of the recycled barrier `b''`.
      cases b'' with
      | inl nb'' =>
        -- `t''` is parked at a `sync_nb nb'' n₂` of `b''`'s current round.
        rcases hbar nb'' with hbu | ⟨I₂, A₂, n₂, hb''eq, hb''lt⟩
        · change t'' ∈ (s.BN nb'').synced at ht''
          rw [hbu] at ht''
          simp [NamedBarrierState.unconfigured] at ht''
        · have hthead : (T_C.prog t'').head? = some (Cmd.sync_nb nb'' n₂) :=
            (hwf.1 nb'' I₂ A₂ n₂ hb''eq).2.1 t'' (by
              change t'' ∈ (s.BN nb'').synced at ht''
              rw [hb''eq] at ht''
              exact ht'')
          have htcmd : (T.prog t'')[et]'htL = Cmd.sync_nb nb'' n₂ := by
            have hdr : T_C.prog t'' = (T.prog t'')[et]'htL :: (T.prog t'').drop (et + 1) := by
              rw [hetprog, List.drop_eq_getElem_cons htL]
            rw [hdr, List.head?_cons, Option.some.injEq] at hthead
            exact hthead
          have hctcmd : T.cmdAt (⟨t'', et⟩ : ProgPoint) = some (Cmd.sync_nb nb'' n₂) := by
            simp only [CTA.cmdAt]
            rw [List.getElem?_eq_getElem htL, htcmd]
          have hctpt : (⟨t'', et⟩ : ProgPoint) ∈ T.progPoints :=
            mem_progPoints_of_cmdAt T hctcmd
          obtain ⟨mt, hmt⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨t'', et⟩)
            (show et < ((Config.run State.initial T).progOf t'').length from htL)
          have hpcmt : pc < mt := by
            refine lt_time_of_lt_progOf hmt htrpc ?_
            change ((Config.run State.initial T).progOf t'').length - et - 1
              < (T_C.prog t'').length
            rw [hetprog, List.length_drop]
            change (T.prog t'').length - et - 1 < (T.prog t'').length - et
            omega
          have hrct'' : recycleCount (.inl nb'') tr (mt - 1)
              = recycleCount (.inl nb'') tr pc :=
            parked_blocked_recycleCount hBItr rfl hmt htrpc ht'' hetprog hpcmt
          have hgent'' : pointGen T τ (⟨t'', et⟩ : ProgPoint)
              = some ((recycleCount (.inl nb'') tr pc : ℤ)) := by
            rw [hgenTr _ _ (.inl nb'') mt hctcmd rfl hctpt hmt, hrct'',
              Cmd.genValue_of_inl (show (Cmd.sync_nb nb'' n₂).barrier?
                = some (.inl nb'') from rfl)]
          -- the `count` of `nb''` is frozen across `[pc, dw]`
          have hcount_step : ∀ {C C' : Config}, CTAStep C C' → ∀ {sa : State},
              C.state? = some sa → ∀ {nc : ℕ+}, (sa.BN nb'').count = some nc →
              stepRecyclesBarrier (.inl nb'') C C' = false →
              ∀ {sa' : State}, C'.state? = some sa' → (sa'.BN nb'').count = some nc := by
            intro C C' hstep sa hCs nc hcnt hnr sa' hCs'
            cases hstep with
            | @interleave s₀ s₀' T₀ i₃ P₃ hi₃ hbar₃ hmbar₃ hth =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              generalize hpi : T₀.prog i₃ = Pi at hth
              cases hth with
              | read_noop => exact hcnt
              | write_noop => exact hcnt
              | mb_wait_pass he hb0 hnep => exact hcnt
              | @mb_init _ _ sb₀ n₃ _ he hb0 => exact hcnt
              | @mb_arrive _ _ sb₀ _ I₃ A₃ n₃ ph₃ he hb0 => exact hcnt
              | @mb_wait_block _ _ sb₀ ph₃ _ I₃ A₃ n₃ he hb0 => exact hcnt
              | @arrive_configure _ _ b₀ n₃ _ he hb0 =>
                by_cases hbb : nb'' = b₀
                · subst hbb
                  rw [hb0] at hcnt
                  simp [NamedBarrierState.unconfigured] at hcnt
                · change (Function.update s₀.BN b₀ ⟨[], 1, some n₃⟩ nb'').count = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
              | @arrive_register _ _ b₀ n₃ _ I₃ A₃ he hb0 hpos hlt =>
                by_cases hbb : nb'' = b₀
                · subst hbb
                  change (Function.update s₀.BN nb'' ⟨I₃, A₃ + 1, some n₃⟩ nb'').count
                    = some nc
                  rw [Function.update_self]
                  rw [hb0] at hcnt
                  exact hcnt
                · change (Function.update s₀.BN b₀ ⟨I₃, A₃ + 1, some n₃⟩ nb'').count
                    = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
              | @sync_configure _ _ b₀ n₃ _ he hb0 =>
                by_cases hbb : nb'' = b₀
                · subst hbb
                  rw [hb0] at hcnt
                  simp [NamedBarrierState.unconfigured] at hcnt
                · change (Function.update s₀.BN b₀ ⟨[i₃], 0, some n₃⟩ nb'').count = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
              | @sync_block _ _ b₀ n₃ _ I₃ A₃ he hb0 hpos hlt =>
                by_cases hbb : nb'' = b₀
                · subst hbb
                  change (Function.update s₀.BN nb'' ⟨i₃ :: I₃, A₃, some n₃⟩ nb'').count
                    = some nc
                  rw [Function.update_self]
                  rw [hb0] at hcnt
                  exact hcnt
                · change (Function.update s₀.BN b₀ ⟨i₃ :: I₃, A₃, some n₃⟩ nb'').count
                    = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
            | @recycle s₀ T₀ b₀ I₃ A₃ n₃ hb hfull hpark₃ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              by_cases hbb : nb'' = b₀
              · subst hbb
                exfalso
                revert hnr
                simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
                  NamedBarrierState.isFull, hfull, Function.update_self,
                  NamedBarrierState.unconfigured]
              · change (Function.update s₀.BN b₀ NamedBarrierState.unconfigured nb'').count
                  = some nc
                rw [Function.update_of_ne hbb]
                exact hcnt
            | @mb_recycle s₀ T₀ sb₀ I₃ A₃ n₃ ph₃ hb hfull hpark₃ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              exact hcnt
            | @done s₀ T₀ hdone _ _ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              exact hcnt
            | @error s₀ T₀ i₃ P₃ _ _ hth =>
              exact absurd hCs' (by simp [WeftCommon.Config.state?])
          have hcountconst : ∀ d, pc ≤ d → d ≤ dw → ∀ sd Td,
              tr[d]? = some (Config.run sd Td) → (sd.BN nb'').count = some n₂ := by
            intro d hpcd
            induction d, hpcd using Nat.le_induction with
            | base =>
              intro _ sd Td hsd
              rw [htrpc, Option.some.injEq, WeftCommon.Config.run.injEq] at hsd
              obtain ⟨rfl, rfl⟩ := hsd
              rw [hb''eq]
            | succ d hpcd ih =>
              intro hd1dw sd' Td' hsd'
              obtain ⟨sd, Td, hsd⟩ := hrunC d hpcd (by omega)
              have hstep := chain_step htrIC.1.subtrace hsd hsd'
              exact hcount_step hstep rfl (ih (by omega) sd Td hsd)
                (hnorec d hpcd (by omega) (.inl nb'') hb''ne _ _ hsd hsd') rfl
          -- `nb''` is full at `dw` but under-full at `pc`
          obtain ⟨sdw, Tdw, hsdw⟩ := hrunC dw hpcdw le_rfl
          have hCdeq : Cd = Config.run sdw Tdw := Option.some_injective _ (hCd.symm.trans hsdw)
          have hfullaux : ∀ {C C' : Config} {sc : State}, C.state? = some sc →
              stepRecyclesBarrier (.inl nb'') C C' = true → (sc.BN nb'').isFull = true := by
            intro C C' sc hsc hrec
            rcases hc' : C'.state? with _ | sc'
            · simp [stepRecyclesBarrier, hsc, hc'] at hrec
            · simp only [stepRecyclesBarrier, hsc, hc', Bool.and_eq_true] at hrec
              exact hrec.1
          have hfulldw : (sdw.BN nb'').synced.length + (sdw.BN nb'').arrived = (n₂ : Nat) := by
            have hcnt := hcountconst dw hpcdw le_rfl sdw Tdw hsdw
            have hisfull := hfullaux (C := Config.run sdw Tdw) rfl (hCdeq ▸ hrecd)
            simp only [NamedBarrierState.isFull, hcnt, beq_iff_eq] at hisfull
            exact hisfull
          -- hence some step in `[pc, dw)` increases `nb''`'s registration count
          have hinc : ∃ d sd Td sd' Td', pc ≤ d ∧ d < dw ∧
              tr[d]? = some (Config.run sd Td) ∧
              tr[d + 1]? = some (Config.run sd' Td') ∧
              (sd.BN nb'').synced.length + (sd.BN nb'').arrived <
                (sd'.BN nb'').synced.length + (sd'.BN nb'').arrived := by
            by_contra hcon
            push Not at hcon
            have hmono : ∀ e, pc ≤ e → e ≤ dw → ∀ se Te,
                tr[e]? = some (Config.run se Te) →
                (se.BN nb'').synced.length + (se.BN nb'').arrived ≤
                  (s.BN nb'').synced.length + (s.BN nb'').arrived := by
              intro e hpce
              induction e, hpce using Nat.le_induction with
              | base =>
                intro _ se Te hse
                rw [htrpc, Option.some.injEq, WeftCommon.Config.run.injEq] at hse
                obtain ⟨rfl, rfl⟩ := hse
                exact le_rfl
              | succ e hpce ih =>
                intro he1 se' Te' hse'
                obtain ⟨se, Te, hse⟩ := hrunC e hpce (by omega)
                exact le_trans (hcon e se Te se' Te' hpce (by omega) hse hse')
                  (ih (by omega) se Te hse)
            have hdwle := hmono dw hpcdw le_rfl sdw Tdw hsdw
            rw [hb''eq] at hdwle
            simp only [hfulldw] at hdwle
            omega
          obtain ⟨d, sd, Td, sd', Td', hpcd, hd_dw, hsd, hsd', hcntlt⟩ := hinc
          -- a count-increasing step must register into `nb''`; analyse it
          have hstepd := chain_step htrIC.1.subtrace hsd hsd'
          cases hstepd with
          | @interleave s₃ s₃' T₃ ii P₃ hii hbar₃ hmbar₃ hth =>
            generalize hpi : Td.prog ii = Pi at hth
            cases hth with
            | read_noop => omega
            | write_noop => omega
            | mb_wait_pass he hb0 hnep => omega
            | @mb_init _ _ sb₀ n₃ _ he hb0 =>
              have hBN : ({sd with BM := Function.update sd.BM sb₀ ⟨[], 0, some n₃, false⟩}
                  : State).BN = sd.BN := rfl
              rw [hBN] at hcntlt
              omega
            | @mb_arrive _ _ sb₀ _ I₃ A₃ n₃ ph₃ he hb0 =>
              have hBN : ({sd with BM := Function.update sd.BM sb₀ ⟨I₃, A₃ + 1, some n₃, ph₃⟩}
                  : State).BN = sd.BN := rfl
              rw [hBN] at hcntlt
              omega
            | @mb_wait_block _ _ sb₀ ph₃ _ I₃ A₃ n₃ he hb0 =>
              have hBN : (State.mk (Function.update sd.E ii false) sd.BN
                  (Function.update sd.BM sb₀ ⟨ii :: I₃, A₃, some n₃, ph₃⟩)).BN = sd.BN := rfl
              rw [hBN] at hcntlt
              omega
            | @arrive_configure _ _ b₀ n₃ _ he hb0 =>
              by_cases hbb : nb'' = b₀
              · subst hbb
                have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
                rw [hb0] at hc
                simp [NamedBarrierState.unconfigured] at hc
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
            | @sync_configure _ _ b₀ n₃ _ he hb0 =>
              by_cases hbb : nb'' = b₀
              · subst hbb
                have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
                rw [hb0] at hc
                simp [NamedBarrierState.unconfigured] at hc
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
            | @arrive_register _ _ b₀ n₃ _ I₃ A₃ he hb0 hpos hlt =>
              by_cases hbb : nb'' = b₀
              · subst hbb
                have hsuf0 := progOf_suffix_index_le htrIC.1.subtrace ii htr0
                  (Nat.zero_le d) hsd
                have hedprog : Td.prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) :=
                  List.IsSuffix.eq_drop hsuf0
                have hn2 : n₃ = n₂ := by
                  have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
                  rw [hb0] at hc
                  exact Option.some.inj hc
                subst hn2
                have hcicmd : T.cmdAt (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩
                    : ProgPoint) = some (Cmd.arrive_nb nb'' n₃) := cmd_at_last hsuf0 hpi
                have htdlen : 0 < (Td.prog ii).length := by rw [hpi]; simp
                have hsuflen : (Td.prog ii).length ≤ (T.prog ii).length :=
                  suffix_length_le hsuf0
                have hLcfg : (T.prog ii).length - (Td.prog ii).length
                    < (T.prog ii).length := by omega
                have hC'eq : (Td.set ii hii P₃).prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length + 1) := by
                  simp only [WeftCommon.CTA.set, Function.update_self]
                  rw [← List.drop_drop, ← hedprog, hpi, List.drop_one, List.tail_cons]
                have hmi : IsTimeOf (Config.run State.initial T) tr
                    (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) (d + 1) :=
                  ⟨htrIC, hLcfg, d, _, _, rfl, hsd, hsd', hedprog, hC'eq⟩
                have hgenci : pointGen T τ
                    (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint)
                    = some ((recycleCount (.inl nb'') tr pc : ℤ)) := by
                  rw [hgenTr _ _ (.inl nb'') (d + 1) hcicmd rfl
                    (mem_progPoints_of_cmdAt T hcicmd) hmi, Nat.add_sub_cancel,
                    hrcc d hpcd (le_of_lt hd_dw),
                    Cmd.genValue_of_inl (show (Cmd.arrive_nb nb'' n₃).barrier?
                      = some (.inl nb'') from rfl)]
                have hedge : ((⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint),
                    (⟨t'', et⟩ : ProgPoint)) ∈ initRelation T τ := by
                  rw [mem_initRelation_iff]
                  exact Or.inr (Or.inl ⟨nb'', n₃, mem_progPoints_of_cmdAt T hcicmd, hctpt,
                    hcicmd, hctcmd, by rw [hgenci, hgent'']⟩)
                exact hregfalse d sd Td hpcd (le_of_lt hd_dw) hsd ii _ hedge
                  (mem_progPoints_of_cmdAt T hcicmd) hedprog he
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
            | @sync_block _ _ b₀ n₃ c₃ I₃ A₃ he hb0 hpos hlt =>
              by_cases hbb : nb'' = b₀
              · subst hbb
                have hsuf0 := progOf_suffix_index_le htrIC.1.subtrace ii htr0
                  (Nat.zero_le d) hsd
                have hedprog : Td.prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) :=
                  List.IsSuffix.eq_drop hsuf0
                have hn2 : n₃ = n₂ := by
                  have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
                  rw [hb0] at hc
                  exact Option.some.inj hc
                subst hn2
                have hcicmd : T.cmdAt (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩
                    : ProgPoint) = some (Cmd.sync_nb nb'' n₃) := cmd_at_last hsuf0 hpi
                have hii_blk : ii ∈ (State.mk (Function.update sd.E ii false)
                    (Function.update sd.BN nb'' ⟨ii :: I₃, A₃, some n₃⟩) sd.BM).blocked
                    (.inl nb'') := by
                  change ii ∈ (Function.update sd.BN nb'' ⟨ii :: I₃, A₃, some n₃⟩ nb'').synced
                  rw [Function.update_self]
                  exact List.mem_cons_self
                have hprog' : (Td.set ii hii (Cmd.sync_nb nb'' n₃ :: c₃)).prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) := by
                  rw [← hedprog]
                  simp only [WeftCommon.CTA.set, Function.update_self]
                  exact hpi.symm
                have htdlen : 0 < (Td.prog ii).length := by rw [hpi]; simp
                have hsuflen : (Td.prog ii).length ≤ (T.prog ii).length :=
                  suffix_length_le hsuf0
                have hLcfg : (T.prog ii).length - (Td.prog ii).length
                    < (T.prog ii).length := by omega
                obtain ⟨mi, hmi⟩ := exists_time_of_ends_done htrIC htrdone
                  (η := ⟨ii, (T.prog ii).length - (Td.prog ii).length⟩) hLcfg
                have hd1mi : d + 1 < mi := by
                  refine lt_time_of_lt_progOf hmi hsd' ?_
                  change ((Config.run State.initial T).progOf ii).length -
                      ((T.prog ii).length - (Td.prog ii).length) - 1 <
                      ((Td.set ii hii (Cmd.sync_nb nb'' n₃ :: c₃)).prog ii).length
                  rw [hprog', List.length_drop]
                  change (T.prog ii).length - ((T.prog ii).length - (Td.prog ii).length) - 1
                    < (T.prog ii).length - ((T.prog ii).length - (Td.prog ii).length)
                  omega
                have hrcmi : recycleCount (.inl nb'') tr (mi - 1)
                    = recycleCount (.inl nb'') tr pc := by
                  rw [parked_blocked_recycleCount hBItr rfl hmi hsd' hii_blk hprog' hd1mi,
                    hrcc (d + 1) (by omega) (by omega)]
                have hgenci : pointGen T τ
                    (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint)
                    = some ((recycleCount (.inl nb'') tr pc : ℤ)) := by
                  rw [hgenTr _ _ (.inl nb'') mi hcicmd rfl
                    (mem_progPoints_of_cmdAt T hcicmd) hmi, hrcmi,
                    Cmd.genValue_of_inl (show (Cmd.sync_nb nb'' n₃).barrier?
                      = some (.inl nb'') from rfl)]
                have hedge : ((⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint),
                    (⟨t'', et⟩ : ProgPoint)) ∈ initRelation T τ := by
                  rw [mem_initRelation_iff]
                  exact Or.inr (Or.inr (Or.inr ⟨nb'', n₃,
                    mem_progPoints_of_cmdAt T hcicmd, hctpt, hcicmd, hctcmd,
                    by rw [hgenci, hgent'']⟩))
                exact hregfalse d sd Td hpcd (le_of_lt hd_dw) hsd ii _ hedge
                  (mem_progPoints_of_cmdAt T hcicmd) hedprog he
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
          | @recycle s₃ T₃ b₀ I₃ A₃ n₃ hb hfull hpark₃ =>
            by_cases hbb : nb'' = b₀
            · subst hbb
              simp only [Function.update_self, NamedBarrierState.unconfigured] at hcntlt
              simp at hcntlt
            · simp only [Function.update_of_ne hbb] at hcntlt
              omega
          | @mb_recycle s₃ T₃ sb₀ I₃ A₃ n₃ ph₃ hb hfull hpark₃ =>
            have hBN : (State.mk (updateMapOn sd.E I₃ true) sd.BN
                (Function.update sd.BM sb₀ ⟨[], 0, some n₃, !ph₃⟩)).BN = sd.BN := rfl
            rw [hBN] at hcntlt
            omega
      | inr sb'' =>
        -- `t''` is parked at a `wait_mb sb'' ph₂` of `sb''`'s current phase.
        rcases hmbar sb'' with hbu | ⟨I₂, A₂, n₂, ph₂, hb''eq, hb''lt⟩
        · change t'' ∈ (s.BM sb'').waiting at ht''
          rw [hbu] at ht''
          simp [MBarrierState.uninitialized] at ht''
        · have hthead : (T_C.prog t'').head? = some (Cmd.wait_mb sb'' ph₂) :=
            (hwf.2.2.1 sb'' I₂ A₂ n₂ ph₂ hb''eq).2 t'' (by
              change t'' ∈ (s.BM sb'').waiting at ht''
              rw [hb''eq] at ht''
              exact ht'')
          have htcmd : (T.prog t'')[et]'htL = Cmd.wait_mb sb'' ph₂ := by
            have hdr : T_C.prog t'' = (T.prog t'')[et]'htL :: (T.prog t'').drop (et + 1) := by
              rw [hetprog, List.drop_eq_getElem_cons htL]
            rw [hdr, List.head?_cons, Option.some.injEq] at hthead
            exact hthead
          have hctcmd : T.cmdAt (⟨t'', et⟩ : ProgPoint) = some (Cmd.wait_mb sb'' ph₂) := by
            simp only [CTA.cmdAt]
            rw [List.getElem?_eq_getElem htL, htcmd]
          have hctpt : (⟨t'', et⟩ : ProgPoint) ∈ T.progPoints :=
            mem_progPoints_of_cmdAt T hctcmd
          obtain ⟨mt, hmt⟩ := exists_time_of_ends_done htrIC htrdone (η := ⟨t'', et⟩)
            (show et < ((Config.run State.initial T).progOf t'').length from htL)
          have hpcmt : pc < mt := by
            refine lt_time_of_lt_progOf hmt htrpc ?_
            change ((Config.run State.initial T).progOf t'').length - et - 1
              < (T_C.prog t'').length
            rw [hetprog, List.length_drop]
            change (T.prog t'').length - et - 1 < (T.prog t'').length - et
            omega
          have hrct'' : recycleCount (.inr sb'') tr (mt - 1)
              = recycleCount (.inr sb'') tr pc :=
            parked_blocked_recycleCount hBItr rfl hmt htrpc ht'' hetprog hpcmt
          -- the parked phase is the parity of the recycle count at `pc`
          have hph₂ : ph₂ = phaseAfter (recycleCount (.inr sb'') tr pc) := by
            have hinv := phase_eq_phaseAfter htrIC.1.subtrace htr0 sb'' pc
              (Config.run s T_C) s htrpc rfl
            rw [hb''eq] at hinv
            exact hinv
          have hgent'' : pointGen T τ (⟨t'', et⟩ : ProgPoint)
              = some ((recycleCount (.inr sb'') tr pc : ℤ)) := by
            rw [hgenTr _ _ (.inr sb'') mt hctcmd rfl hctpt hmt, hrct'']
            have hgv : (Cmd.wait_mb sb'' ph₂).genValue (recycleCount (.inr sb'') tr pc)
                = ((recycleCount (.inr sb'') tr pc : ℤ)) := by
              simp only [Cmd.genValue]
              rw [if_pos hph₂.symm]
            rw [hgv]
          -- the `count` of `sb''` is frozen across `[pc, dw]`
          have hcount_step : ∀ {C C' : Config}, CTAStep C C' → ∀ {sa : State},
              C.state? = some sa → ∀ {nc : ℕ+}, (sa.BM sb'').count = some nc →
              stepRecyclesBarrier (.inr sb'') C C' = false →
              ∀ {sa' : State}, C'.state? = some sa' → (sa'.BM sb'').count = some nc := by
            intro C C' hstep sa hCs nc hcnt hnr sa' hCs'
            cases hstep with
            | @interleave s₀ s₀' T₀ i₃ P₃ hi₃ hbar₃ hmbar₃ hth =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              generalize hpi : T₀.prog i₃ = Pi at hth
              cases hth with
              | read_noop => exact hcnt
              | write_noop => exact hcnt
              | mb_wait_pass he hb0 hnep => exact hcnt
              | @arrive_configure _ _ b₀ n₃ _ he hb0 => exact hcnt
              | @arrive_register _ _ b₀ n₃ _ I₃ A₃ he hb0 hpos hlt => exact hcnt
              | @sync_configure _ _ b₀ n₃ _ he hb0 => exact hcnt
              | @sync_block _ _ b₀ n₃ c₃ I₃ A₃ he hb0 hpos hlt => exact hcnt
              | @mb_init _ _ sb₀ n₃ _ he hb0 =>
                by_cases hbb : sb'' = sb₀
                · subst hbb
                  rw [hb0] at hcnt
                  simp [MBarrierState.uninitialized] at hcnt
                · change (Function.update s₀.BM sb₀ ⟨[], 0, some n₃, false⟩ sb'').count
                    = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
              | @mb_arrive _ _ sb₀ _ I₃ A₃ n₃ ph₃ he hb0 =>
                by_cases hbb : sb'' = sb₀
                · subst hbb
                  change (Function.update s₀.BM sb'' ⟨I₃, A₃ + 1, some n₃, ph₃⟩ sb'').count
                    = some nc
                  rw [Function.update_self]
                  rw [hb0] at hcnt
                  exact hcnt
                · change (Function.update s₀.BM sb₀ ⟨I₃, A₃ + 1, some n₃, ph₃⟩ sb'').count
                    = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
              | @mb_wait_block _ _ sb₀ ph₃ _ I₃ A₃ n₃ he hb0 =>
                by_cases hbb : sb'' = sb₀
                · subst hbb
                  change (Function.update s₀.BM sb'' ⟨i₃ :: I₃, A₃, some n₃, ph₃⟩ sb'').count
                    = some nc
                  rw [Function.update_self]
                  rw [hb0] at hcnt
                  exact hcnt
                · change (Function.update s₀.BM sb₀ ⟨i₃ :: I₃, A₃, some n₃, ph₃⟩ sb'').count
                    = some nc
                  rw [Function.update_of_ne hbb]
                  exact hcnt
            | @recycle s₀ T₀ b₀ I₃ A₃ n₃ hb hfull hpark₃ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              exact hcnt
            | @mb_recycle s₀ T₀ sb₀ I₃ A₃ n₃ ph₃ hb hfull hpark₃ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              by_cases hbb : sb'' = sb₀
              · subst hbb
                exfalso
                revert hnr
                simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
                  MBarrierState.isFull, hfull, Function.update_self]
              · change (Function.update s₀.BM sb₀ ⟨[], 0, some n₃, !ph₃⟩ sb'').count
                  = some nc
                rw [Function.update_of_ne hbb]
                exact hcnt
            | @done s₀ T₀ hdone _ _ =>
              simp only [WeftCommon.Config.state?, Option.some.injEq] at hCs hCs'
              subst hCs; subst hCs'
              exact hcnt
            | @error s₀ T₀ i₃ P₃ _ _ hth =>
              exact absurd hCs' (by simp [WeftCommon.Config.state?])
          have hcountconst : ∀ d, pc ≤ d → d ≤ dw → ∀ sd Td,
              tr[d]? = some (Config.run sd Td) → (sd.BM sb'').count = some n₂ := by
            intro d hpcd
            induction d, hpcd using Nat.le_induction with
            | base =>
              intro _ sd Td hsd
              rw [htrpc, Option.some.injEq, WeftCommon.Config.run.injEq] at hsd
              obtain ⟨rfl, rfl⟩ := hsd
              rw [hb''eq]
            | succ d hpcd ih =>
              intro hd1dw sd' Td' hsd'
              obtain ⟨sd, Td, hsd⟩ := hrunC d hpcd (by omega)
              have hstep := chain_step htrIC.1.subtrace hsd hsd'
              exact hcount_step hstep rfl (ih (by omega) sd Td hsd)
                (hnorec d hpcd (by omega) (.inr sb'') hb''ne _ _ hsd hsd') rfl
          -- `sb''` is full in arrivals at `dw` but under-full at `pc`
          obtain ⟨sdw, Tdw, hsdw⟩ := hrunC dw hpcdw le_rfl
          have hCdeq : Cd = Config.run sdw Tdw := Option.some_injective _ (hCd.symm.trans hsdw)
          have hfullaux : ∀ {C C' : Config} {sc : State}, C.state? = some sc →
              stepRecyclesBarrier (.inr sb'') C C' = true → (sc.BM sb'').isFull = true := by
            intro C C' sc hsc hrec
            rcases hc' : C'.state? with _ | sc'
            · simp [stepRecyclesBarrier, hsc, hc'] at hrec
            · simp only [stepRecyclesBarrier, hsc, hc', Bool.and_eq_true] at hrec
              exact hrec.1
          have hfulldw : (sdw.BM sb'').arrived = (n₂ : Nat) := by
            have hcnt := hcountconst dw hpcdw le_rfl sdw Tdw hsdw
            have hisfull := hfullaux (C := Config.run sdw Tdw) rfl (hCdeq ▸ hrecd)
            simp only [MBarrierState.isFull, hcnt, beq_iff_eq] at hisfull
            exact hisfull
          -- hence some step in `[pc, dw)` increases `sb''`'s arrival count
          have hinc : ∃ d sd Td sd' Td', pc ≤ d ∧ d < dw ∧
              tr[d]? = some (Config.run sd Td) ∧
              tr[d + 1]? = some (Config.run sd' Td') ∧
              (sd.BM sb'').arrived < (sd'.BM sb'').arrived := by
            by_contra hcon
            push Not at hcon
            have hmono : ∀ e, pc ≤ e → e ≤ dw → ∀ se Te,
                tr[e]? = some (Config.run se Te) →
                (se.BM sb'').arrived ≤ (s.BM sb'').arrived := by
              intro e hpce
              induction e, hpce using Nat.le_induction with
              | base =>
                intro _ se Te hse
                rw [htrpc, Option.some.injEq, WeftCommon.Config.run.injEq] at hse
                obtain ⟨rfl, rfl⟩ := hse
                exact le_rfl
              | succ e hpce ih =>
                intro he1 se' Te' hse'
                obtain ⟨se, Te, hse⟩ := hrunC e hpce (by omega)
                exact le_trans (hcon e se Te se' Te' hpce (by omega) hse hse')
                  (ih (by omega) se Te hse)
            have hdwle := hmono dw hpcdw le_rfl sdw Tdw hsdw
            rw [hb''eq] at hdwle
            simp only [hfulldw] at hdwle
            omega
          obtain ⟨d, sd, Td, sd', Td', hpcd, hd_dw, hsd, hsd', hcntlt⟩ := hinc
          -- an arrival-increasing step must be an `mb_arrive` into `sb''`; analyse it
          have hstepd := chain_step htrIC.1.subtrace hsd hsd'
          cases hstepd with
          | @interleave s₃ s₃' T₃ ii P₃ hii hbar₃ hmbar₃ hth =>
            generalize hpi : Td.prog ii = Pi at hth
            cases hth with
            | read_noop => omega
            | write_noop => omega
            | mb_wait_pass he hb0 hnep => omega
            | @arrive_configure _ _ b₀ n₃ _ he hb0 =>
              have hBM : ({sd with BN := Function.update sd.BN b₀ ⟨[], 1, some n₃⟩}
                  : State).BM = sd.BM := rfl
              rw [hBM] at hcntlt
              omega
            | @arrive_register _ _ b₀ n₃ _ I₃ A₃ he hb0 hpos hlt =>
              have hBM : ({sd with BN := Function.update sd.BN b₀ ⟨I₃, A₃ + 1, some n₃⟩}
                  : State).BM = sd.BM := rfl
              rw [hBM] at hcntlt
              omega
            | @sync_configure _ _ b₀ n₃ _ he hb0 =>
              have hBM : (State.mk (Function.update sd.E ii false)
                  (Function.update sd.BN b₀ ⟨[ii], 0, some n₃⟩) sd.BM).BM = sd.BM := rfl
              rw [hBM] at hcntlt
              omega
            | @sync_block _ _ b₀ n₃ c₃ I₃ A₃ he hb0 hpos hlt =>
              have hBM : (State.mk (Function.update sd.E ii false)
                  (Function.update sd.BN b₀ ⟨ii :: I₃, A₃, some n₃⟩) sd.BM).BM = sd.BM := rfl
              rw [hBM] at hcntlt
              omega
            | @mb_init _ _ sb₀ n₃ _ he hb0 =>
              by_cases hbb : sb'' = sb₀
              · subst hbb
                have hc := hcountconst d hpcd (le_of_lt hd_dw) sd Td hsd
                rw [hb0] at hc
                simp [MBarrierState.uninitialized] at hc
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
            | @mb_wait_block _ _ sb₀ ph₃ _ I₃ A₃ n₃ he hb0 =>
              by_cases hbb : sb'' = sb₀
              · subst hbb
                simp only [Function.update_self, hb0] at hcntlt
                omega
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
            | @mb_arrive _ _ sb₀ _ I₃ A₃ n₃ ph₃ he hb0 =>
              by_cases hbb : sb'' = sb₀
              · subst hbb
                have hsuf0 := progOf_suffix_index_le htrIC.1.subtrace ii htr0
                  (Nat.zero_le d) hsd
                have hedprog : Td.prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length) :=
                  List.IsSuffix.eq_drop hsuf0
                have hcicmd : T.cmdAt (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩
                    : ProgPoint) = some (Cmd.arrive_mb sb'') := cmd_at_last hsuf0 hpi
                have htdlen : 0 < (Td.prog ii).length := by rw [hpi]; simp
                have hsuflen : (Td.prog ii).length ≤ (T.prog ii).length :=
                  suffix_length_le hsuf0
                have hLcfg : (T.prog ii).length - (Td.prog ii).length
                    < (T.prog ii).length := by omega
                have hC'eq : (Td.set ii hii P₃).prog ii
                    = (T.prog ii).drop ((T.prog ii).length - (Td.prog ii).length + 1) := by
                  simp only [WeftCommon.CTA.set, Function.update_self]
                  rw [← List.drop_drop, ← hedprog, hpi, List.drop_one, List.tail_cons]
                have hmi : IsTimeOf (Config.run State.initial T) tr
                    (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint) (d + 1) :=
                  ⟨htrIC, hLcfg, d, _, _, rfl, hsd, hsd', hedprog, hC'eq⟩
                have hgenci : pointGen T τ
                    (⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint)
                    = some ((recycleCount (.inr sb'') tr pc : ℤ)) := by
                  rw [hgenTr _ _ (.inr sb'') (d + 1) hcicmd rfl
                    (mem_progPoints_of_cmdAt T hcicmd) hmi, Nat.add_sub_cancel,
                    hrcc d hpcd (le_of_lt hd_dw)]
                  rfl
                have hedge : ((⟨ii, (T.prog ii).length - (Td.prog ii).length⟩ : ProgPoint),
                    (⟨t'', et⟩ : ProgPoint)) ∈ initRelation T τ := by
                  rw [mem_initRelation_iff]
                  exact Or.inr (Or.inr (Or.inl ⟨sb'', ph₂,
                    mem_progPoints_of_cmdAt T hcicmd, hctpt, hcicmd, hctcmd,
                    by rw [hgenci, hgent'']⟩))
                exact hregfalse d sd Td hpcd (le_of_lt hd_dw) hsd ii _ hedge
                  (mem_progPoints_of_cmdAt T hcicmd) hedprog he
              · simp only [Function.update_of_ne hbb] at hcntlt
                omega
          | @recycle s₃ T₃ b₀ I₃ A₃ n₃ hb hfull hpark₃ =>
            have hBM : (State.mk (updateMapOn sd.E I₃ true)
                (Function.update sd.BN b₀ NamedBarrierState.unconfigured) sd.BM).BM
                = sd.BM := rfl
            rw [hBM] at hcntlt
            omega
          | @mb_recycle s₃ T₃ sb₀ I₃ A₃ n₃ ph₃ hb hfull hpark₃ =>
            by_cases hbb : sb'' = sb₀
            · subst hbb
              simp only [Function.update_self] at hcntlt
              simp at hcntlt
            · simp only [Function.update_of_ne hbb] at hcntlt
              omega

/-- Run `G` to the cut configuration: from any reachable `G`-bounded `C`, there is
a chain (executing only `G`-steps) to a configuration whose every thread sits
exactly at its cut. By well-founded recursion on `cfgMeasure`, taking a `G`-step
(`gstep`) until `G` is exhausted. -/
theorem reach_cut_aux {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized) :
    ∀ n, ∀ C, GBounded T τ η₁ C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C →
      C.cfgMeasure T.barrierSet = n →
      ∃ (pre : List Config) (s_G : State) (T_G : CTA),
        pre.head? = some C ∧ List.IsChain CTAStep pre ∧
        pre.getLast? = some (Config.run s_G T_G) ∧
        (∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i)) ∧
        Relation.ReflTransGen CTAStep (Config.run State.initial T) (Config.run s_G T_G) ∧
        (∀ b i, i ∉ s_G.blocked b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hGB hreach hmeas
    by_cases hdone : Gdone T τ η₁ C
    · -- cut configuration reached
      obtain ⟨s, T_C, rfl, he, hpure⟩ := hGB
      refine ⟨[Config.run s T_C], s, T_C, rfl, List.isChain_singleton _, rfl, fun i => ?_,
        hreach, fun b i hmem => ?_⟩
      · obtain ⟨e, hele, hprog⟩ := he i
        by_cases hi : i ∈ T.ids
        · have hd := hdone i hi
          simp only [WeftCommon.Config.progOf] at hd
          rw [hprog, List.length_drop] at hd
          have hcl := fcut_le_length T τ η₁ i
          rw [hprog, show e = fcut T τ η₁ i by omega]
        · rw [hprog, T.nil_outside_ids i hi]
          simp
      · -- blocked lists empty: barrier purity contradicts the cut's exact execution
        have hp := hpure b i hmem
        obtain ⟨e, hele, hprog⟩ := he i
        have heq : (T.prog i).length - (T_C.prog i).length = fcut T τ η₁ i := by
          by_cases hi : i ∈ T.ids
          · have hd := hdone i hi
            simp only [WeftCommon.Config.progOf] at hd
            rw [hprog, List.length_drop] at hd ⊢
            have hcl := fcut_le_length T τ η₁ i
            omega
          · have hnil := T.nil_outside_ids i hi
            have h0 : fcut T τ η₁ i = 0 := by
              have := fcut_le_length T τ η₁ i
              rw [hnil] at this
              simpa using this
            simp [hprog, hnil, h0]
        omega
    · -- progress: take a `G`-step and recurse
      obtain ⟨C', hstep, hGB'⟩ := gstep hτ hws hGB hreach hdone
      have hbw : C.barriersWithin T.barrierSet := barriersWithin_of_reaches hreach
      have hlt : C'.cfgMeasure T.barrierSet < n := by
        rw [← hmeas]
        exact step_decreases T.barrierSet hstep hbw
      obtain ⟨pre', s_G, T_G, hhd', hch', hlast', hcut', hreach', hbempty⟩ :=
        ih _ hlt C' hGB' (hreach.tail hstep) rfl
      have hpne : pre' ≠ [] := by intro h; rw [h] at hhd'; simp at hhd'
      refine ⟨C :: pre', s_G, T_G, rfl, ?_, ?_, hcut', hreach', hbempty⟩
      · rw [List.isChain_cons]
        exact ⟨fun y hy => by rw [hhd', Option.mem_some_iff] at hy; exact hy ▸ hstep, hch'⟩
      · rw [List.getLast?_cons_of_ne_nil hpne]
        exact hlast'

/-- **Run the ideal `G` first.** There is a complete trace `τ'` from `(I, T)` and
a configuration index `p` at which *exactly* the ideal `G` has executed — every
thread's remaining program is `T`'s with its `fcut`-prefix dropped. -/
theorem run_ideal {T : CTA} {τ : List Config} {η₁ : ProgPoint}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized) :
    ∃ (τ' : List Config) (p : Nat) (s_G : State) (T_G : CTA),
      IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      τ'[p]? = some (Config.run s_G T_G) ∧
      (∀ i, T_G.prog i = (T.prog i).drop (fcut T τ η₁ i)) ∧
      (∀ b i, i ∉ s_G.blocked b) := by
  obtain ⟨pre, s_G, T_G, hhd, hch, hlast, hcut, hreachG, hbempty⟩ :=
    reach_cut_aux hτ hws ((Config.cfgMeasure T.barrierSet (Config.run State.initial T)))
      (Config.run State.initial T) (GBounded_init T τ η₁) Relation.ReflTransGen.refl rfl
  have hpne : pre ≠ [] := by intro h; rw [h] at hhd; simp at hhd
  have hpos : 0 < pre.length := List.length_pos_of_ne_nil hpne
  have hgl : pre.getLast hpne = Config.run s_G T_G := by
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h
    exact (Option.some.injEq _ _).mp h.symm
  have hbwG : (Config.barriersWithin T.barrierSet (Config.run s_G T_G)) :=
    barriersWithin_of_reaches hreachG
  obtain ⟨σ, hσIC, hσhead⟩ := exists_completeTrace T.barrierSet (Config.run s_G T_G) hbwG
  obtain ⟨σtail, rfl⟩ : ∃ l, σ = Config.run s_G T_G :: l := by
    cases σ with
    | nil => simp at hσhead
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hσhead
      exact ⟨l, hσhead ▸ rfl⟩
  have hσchain : List.IsChain CTAStep (Config.run s_G T_G :: σtail) := hσIC.subtrace
  rw [List.isChain_cons] at hσchain
  refine ⟨pre ++ σtail, pre.length - 1, s_G, T_G, ⟨⟨?_, ?_⟩, ?_⟩, ?_, hcut, hbempty⟩
  · refine List.IsChain.append hch hσchain.2 ?_
    intro x hx y hy
    rw [hlast, Option.mem_some_iff] at hx
    subst hx
    exact hσchain.1 y hy
  · obtain ⟨Cₙ, hτlast, hterm⟩ := hσIC.ends
    refine ⟨Cₙ, ?_, hterm⟩
    have hsplit : pre ++ σtail = pre.dropLast ++ (Config.run s_G T_G :: σtail) := by
      conv_lhs => rw [← List.dropLast_concat_getLast hpne, hgl]
      simp
    rw [hsplit]
    exact List.mem_getLast?_append_of_mem_getLast? hτlast
  · rw [List.head?_append_of_ne_nil _ hpne]
    exact hhd
  · rw [List.getElem?_append_left (by omega : pre.length - 1 < pre.length)]
    rw [← List.getLast?_eq_getElem?]
    exact hlast

/-- **Realizability / reversing-schedule lemma** — the heart of preciseness. If
`η₁` is *not* happens-before `η₂`, then some complete trace from `(I, T)` runs
`η₂` strictly before `η₁`: run the down-closed ideal
`G = {η | ¬ happensBefore T τ η₁ η}` to its cut first (`run_ideal`); `η₂ ∈ G`
executes in the `G`-prefix and `η₁ ∉ G` in the `F`-suffix. -/
theorem exists_reversing_trace {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {η₁ η₂ : ProgPoint} (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hcon : ¬ happensBefore T τ η₁ η₂) :
    ∃ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' ∧
      ∃ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ ∧
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ ∧ n₂ < n₁ := by
  obtain ⟨τ', p, s_G, T_G, hcomp, hpcfg, hGdone, _⟩ :=
    run_ideal (T := T) (τ := τ) (η₁ := η₁) hτ hws
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hv₁L : η₁.idx < (T.prog η₁.thread).length := ((mem_progPoints_iff T η₁).mp hv₁).2
  have hv₂L : η₂.idx < (T.prog η₂.thread).length := ((mem_progPoints_iff T η₂).mp hv₂).2
  obtain ⟨n₁, ht₁⟩ := exists_time_of_ends_done hcomp hdone (η := η₁) hv₁L
  obtain ⟨n₂, ht₂⟩ := exists_time_of_ends_done hcomp hdone (η := η₂) hv₂L
  refine ⟨τ', hcomp, n₁, n₂, ht₁, ht₂, ?_⟩
  have hcut₁ : fcut T τ η₁ η₁.thread ≤ η₁.idx := fcut_le_of_hb Relation.ReflTransGen.refl hv₁
  have hcut₂ : η₂.idx < fcut T τ η₁ η₂.thread := lt_fcut_of_not_hb hcon hv₂
  have hn₂ : n₂ ≤ p := by
    refine time_le_of_progOf_le ht₂ hpcfg ?_
    change (T_G.prog η₂.thread).length ≤ _
    rw [hGdone η₂.thread, List.length_drop]
    change _ ≤ (T.prog η₂.thread).length - η₂.idx - 1
    omega
  have hn₁ : p < n₁ := by
    refine lt_time_of_lt_progOf ht₁ hpcfg ?_
    change ((Config.run State.initial T).progOf η₁.thread).length - η₁.idx - 1 <
      (T_G.prog η₁.thread).length
    rw [hGdone η₁.thread, List.length_drop]
    change (T.prog η₁.thread).length - η₁.idx - 1 <
      (T.prog η₁.thread).length - fcut T τ η₁ η₁.thread
    omega
  omega

/-! ## Lemma 1 for Algorithm 2 — the happens-before relation is sound and precise

The two directions and their assembly, mirroring the named-barrier development.
The proofs are the mbarrier port's core semantic obligations (§5.2.4, §5.2.5):

* **soundness** — every `initRelation` edge is a genuine ordering in every
  complete trace: program order because threads execute in order; the
  registration edges (`arrive_nb → sync_nb`, `arrive_mb → wait_mb`) because
  well-synchronization pins both endpoints to the same generation in every
  schedule, and a generation's registrations complete before anything of that
  generation is released; `sync_nb ↔ sync_nb` because same-generation named
  syncs are all released by the same recycle. Note there are no `wait ↔ wait`
  edges to justify — mbarrier waits of one generation need not resolve
  simultaneously.
* **preciseness** — any ordering that holds in *every* schedule is already in
  the closure: reflexivity and same-thread orderings reduce to program order;
  for points on different threads one exhibits a *reversing schedule* for any
  pair the relation does not order (§5.2.5's swap argument, whose case
  analysis for mbarriers includes the wait pairs). -/

/-- **Soundness half of Lemma 1** (Algorithm 2): every `happensBefore` ordering
is respected by every complete trace — if `happensBefore T τ η₁ η₂`, then in
every complete trace from `(I, T)` where both points execute, `η₁` executes no
later than `η₂`. -/
theorem happensBefore_sound {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hR : happensBefore T τ η₁ η₂) :
    ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂ := by
  intro τ' hτ'
  induction hR with
  | refl => intro n₁ n₂ h1 h2; exact le_of_eq (IsTimeOf.unique h1 h2)
  | tail _hab hbc ih =>
      intro n₁ nc ht₁ htc
      obtain ⟨nb, htb⟩ := initRelation_src_timed hws hbc hτ' htc
      exact le_trans (ih n₁ nb ht₁ htb)
        (initRelation_edge_sound hτ hws hbc τ' hτ' nb nc htb htc)

/-- **Preciseness half of Lemma 1** (Algorithm 2): every ordering that holds in
*all* complete traces is already in `happensBefore`. The valid-point premises
are required — for a never-executing point the timing side is vacuously true
while `happensBefore` cannot relate it. -/
theorem happensBefore_precise {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) {η₁ η₂ : ProgPoint}
    (hv₁ : η₁ ∈ T.progPoints) (hv₂ : η₂ ∈ T.progPoints)
    (hle : ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
      ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
        IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) :
    happensBefore T τ η₁ η₂ := by
  by_cases hη : η₁ = η₂
  · -- reflexive corner: every point is happens-before itself
    subst hη
    exact Relation.ReflTransGen.refl
  · by_cases hthread : η₁.thread = η₂.thread
    · -- same thread: forced order is program order
      obtain ⟨i₁, k₁⟩ := η₁
      obtain ⟨i₂, k₂⟩ := η₂
      replace hthread : i₁ = i₂ := hthread
      subst hthread
      replace hη : k₁ ≠ k₂ := fun h => hη (by rw [h])
      obtain ⟨hcomplete, sd, hdone⟩ := hτ
      obtain ⟨n₁, ht₁⟩ :=
        exists_time_of_ends_done hcomplete hdone ((mem_progPoints_iff T _).mp hv₁).2
      obtain ⟨n₂, ht₂⟩ :=
        exists_time_of_ends_done hcomplete hdone ((mem_progPoints_iff T _).mp hv₂).2
      have hn : n₁ ≤ n₂ := hle τ hcomplete n₁ n₂ ht₁ ht₂
      have hidx : k₁ < k₂ := by
        rcases Nat.lt_trichotomy k₁ k₂ with h | h | h
        · exact h
        · exact absurd h hη
        · exact absurd (time_lt_of_idx_lt ht₂ ht₁ rfl h) (by omega)
      exact progOrder_happensBefore (le_of_lt hidx) ((mem_progPoints_iff T _).mp hv₂).2
    · -- different threads: contrapositive via the reversing-schedule lemma
      by_contra hcon
      obtain ⟨τ', hτ'c, n₁, n₂, ht₁, ht₂, hlt⟩ := exists_reversing_trace hτ hws hv₁ hv₂ hcon
      exact absurd (hle τ' hτ'c n₁ n₂ ht₁ ht₂) (by omega)

/-- **Lemma 1** for the mbarrier-extended language. For a well-synchronized
configuration `(I, T)`, the static happens-before relation constructed by
Algorithm 2 — `happensBefore T τ`, the reflexive-transitive closure of
`initRelation T τ` — is sound and precise in the sense of Definition 4
(`WeftCommon.SoundAndPrecise`), **on program points**.

The valid-point restriction (`η₁ η₂ ∈ T.progPoints`) is required: the
unrestricted `SoundAndPrecise` is false, because for a never-executing point
the timing side is vacuously true while `happensBefore` cannot relate it (see
`happensBefore_precise`). Assembled from the two directions
`happensBefore_sound` and `happensBefore_precise`.

Implementation of the top-level `WeftMBarriers.soundAndPrecise_happensBefore`
(in `WeftMBarriers.lean`). -/
theorem soundAndPrecise_happensBefore_impl {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) :
    ∀ η₁ η₂ : ProgPoint, η₁ ∈ T.progPoints → η₂ ∈ T.progPoints →
      (happensBefore T τ η₁ η₂ ↔
        ∀ τ', IsCompleteTraceFrom (Config.run State.initial T) τ' →
          ∀ n₁ n₂, IsTimeOf (Config.run State.initial T) τ' η₁ n₁ →
            IsTimeOf (Config.run State.initial T) τ' η₂ n₂ → n₁ ≤ n₂) := by
  intro η₁ η₂ hv₁ hv₂
  exact ⟨happensBefore_sound hτ hws, happensBefore_precise hτ hws hv₁ hv₂⟩

/-- `progPoints` enumerates each program point exactly once. -/
theorem progPoints_nodup (T : CTA) : T.progPoints.Nodup := by
  unfold CTA.progPoints
  rw [List.nodup_flatMap]
  constructor
  · intro i _
    exact List.nodup_range.map fun a b hab => by simpa using congrArg ProgPoint.idx hab
  · refine (Finset.sort_nodup T.ids (· ≤ ·)).imp ?_
    intro i i' hne x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨k', -, hkk⟩ := hx'
    exact hne (by simpa using congrArg ProgPoint.thread hkk.symm)

/-- Counting after enlarging a predicate at exactly one list element. -/
theorem countP_succ_of_unique {α : Type*} {l : List α} (hnd : l.Nodup)
    {p q : α → Bool} {a₀ : α} (ha₀ : a₀ ∈ l) (hqa : q a₀ = true) (hpa : p a₀ = false)
    (hpq : ∀ x ∈ l, x ≠ a₀ → q x = p x) :
    l.countP q = l.countP p + 1 := by
  induction l with
  | nil => simp at ha₀
  | cons a t ih =>
    obtain ⟨hna, hndt⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha₀ with rfl | hmem
    · have htail : t.countP q = t.countP p :=
        List.countP_congr fun x hx => by
          rw [hpq x (List.mem_cons_of_mem _ hx) (fun h => hna (h ▸ hx))]
      simp [htail, hqa, hpa]
    · have hne : a ≠ a₀ := fun h => hna (h ▸ hmem)
      have hqp := hpq a (List.mem_cons_self ..) hne
      have iht := ih hndt hmem fun x hx hxne => hpq x (List.mem_cons_of_mem _ hx) hxne
      simp only [List.countP_cons, iht, hqp]
      omega

/-- Decode `initCountOf`: `some n` names an `init_mb sb n` program point. -/
theorem initCountOf_some {T : CTA} {sb : SharedBarrier} {n : ℕ+}
    (h : T.initCountOf sb = some n) :
    ∃ ip ∈ T.progPoints, T.cmdAt ip = some (.init_mb sb n) := by
  unfold CTA.initCountOf at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, ip, l₂, hsplit, hf, -⟩ := h
  refine ⟨ip, by rw [hsplit]; simp, ?_⟩
  cases hc : T.cmdAt ip with
  | none => simp [hc] at hf
  | some cmd =>
    cases cmd with
    | read l => simp [hc] at hf
    | write l => simp [hc] at hf
    | arrive_nb nb m => simp [hc] at hf
    | sync_nb nb m => simp [hc] at hf
    | arrive_mb sb' => simp [hc] at hf
    | wait_mb sb' ph => simp [hc] at hf
    | init_mb sb' n' =>
      simp only [hc] at hf
      by_cases hbb : sb' = sb
      · subst hbb
        rw [if_pos rfl] at hf
        obtain rfl := Option.some.inj hf
        rfl
      · rw [if_neg hbb] at hf
        exact absurd hf (by simp)

/-! ## Reading a passing check (soundness support)

Duals of the completeness extractors: from `check = true`, every flagged
ordering is already in the closure. -/

/-- A passing check passes each of its four conjuncts. -/
theorem check_true_parts {T : CTA} {τ : List Config}
    (h : (CheckWellSynchronized T τ).1 = true) :
    okRegCheck T τ = true ∧ okWaitCheck T τ = true ∧
      okInitCheck T τ = true ∧ okUniqueInitCheck T τ = true := by
  have h' : (okRegCheck T τ && okWaitCheck T τ && okInitCheck T τ
      && okUniqueInitCheck T τ) = true := h
  simp only [Bool.and_eq_true] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- **The registrant check, read forward**: every flagged pair is ordered —
a generation-`g` registrant happens-before the predecessor of every
generation-`(g+1)` registrant of the same barrier. -/
theorem happensBefore_of_check {T : CTA} {τ : List Config}
    (hcheck : okRegCheck T τ = true)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b : NamedBarrier ⊕ SharedBarrier}
    {g : ℤ} (hreg1 : registrantGen T τ c1 = some (b, g))
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hreg2 : registrantGen T τ c2 = some (b, g + 1)) (hidx : 1 ≤ c2.idx) :
    happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ := by
  simp only [okRegCheck] at hcheck
  have hf1 := List.all_eq_true.mp hcheck c1 hc1
  simp only [hreg1] at hf1
  have hf2 := List.all_eq_true.mp hf1 c2 hc2
  rw [if_pos hreg2, if_pos hidx, decide_eq_true_eq] at hf2
  rcases hf2 with heq | hmem
  · rw [heq]
    exact Relation.ReflTransGen.refl
  · exact (mem_transClosure_imp_transGen _ hmem).to_reflTransGen

/-- **The idx-0 rejection, read forward**: a flagged pair never has a
first-instruction target. -/
theorem idx_pos_of_check {T : CTA} {τ : List Config}
    (hcheck : okRegCheck T τ = true)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b : NamedBarrier ⊕ SharedBarrier}
    {g : ℤ} (hreg1 : registrantGen T τ c1 = some (b, g))
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hreg2 : registrantGen T τ c2 = some (b, g + 1)) : 1 ≤ c2.idx := by
  by_contra hidx
  simp only [okRegCheck] at hcheck
  have hf1 := List.all_eq_true.mp hcheck c1 hc1
  simp only [hreg1] at hf1
  have hf2 := List.all_eq_true.mp hf1 c2 hc2
  rw [if_pos hreg2, if_neg hidx] at hf2
  exact absurd hf2 (by simp)

/-- **The wait lower bound, read forward**: a wait of generation `g ≥ 1` has an
in-thread predecessor after every `Reg(sb, g−1)` registrant. -/
theorem wait_lower_of_check {T : CTA} {τ : List Config}
    (hcheck : okWaitCheck T τ = true)
    {w : ProgPoint} (hw : w ∈ T.progPoints) {sb : SharedBarrier} {ph : Phase} {g : ℤ}
    (hcmdw : T.cmdAt w = some (.wait_mb sb ph)) (hgenw : pointGen T τ w = some g)
    (hg1 : 1 ≤ g) :
    1 ≤ w.idx ∧ ∀ c ∈ T.progPoints, registrantGen T τ c = some (.inr sb, g - 1) →
      happensBefore T τ c ⟨w.thread, w.idx - 1⟩ := by
  simp only [okWaitCheck] at hcheck
  have hf := List.all_eq_true.mp hcheck w hw
  simp only [hcmdw, hgenw] at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨hlow, -⟩ := hf
  rw [Bool.or_eq_true] at hlow
  rcases hlow with hglt | hrest
  · rw [decide_eq_true_eq] at hglt
    omega
  · rw [Bool.and_eq_true] at hrest
    obtain ⟨hidx, hall⟩ := hrest
    rw [decide_eq_true_eq] at hidx
    refine ⟨hidx, ?_⟩
    intro c hcmem hcreg
    have hc := List.all_eq_true.mp hall c hcmem
    rw [if_pos hcreg, decide_eq_true_eq] at hc
    rcases hc with heq | hmem
    · rw [heq]
      exact Relation.ReflTransGen.refl
    · exact (mem_transClosure_imp_transGen _ hmem).to_reflTransGen

/-- **The wait upper bound, read forward**: when generation `g + 1` fills, the
wait happens-before one of its registrants. -/
theorem wait_upper_of_check {T : CTA} {τ : List Config}
    (hcheck : okWaitCheck T τ = true)
    {w : ProgPoint} (hw : w ∈ T.progPoints) {sb : SharedBarrier} {ph : Phase} {g : ℤ}
    (hcmdw : T.cmdAt w = some (.wait_mb sb ph)) (hgenw : pointGen T τ w = some g)
    {n : ℕ+} (hn : T.initCountOf sb = some n)
    (hfill : (T.progPoints.filter fun cp =>
      registrantGen T τ cp = some (.inr sb, g + 1)).length = (n : Nat)) :
    ∃ cp ∈ T.progPoints.filter (fun cp =>
      registrantGen T τ cp = some (.inr sb, g + 1)), happensBefore T τ w cp := by
  simp only [okWaitCheck] at hcheck
  have hf := List.all_eq_true.mp hcheck w hw
  simp only [hcmdw, hgenw] at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨-, hup⟩ := hf
  simp only [hn] at hup
  rw [if_pos hfill] at hup
  obtain ⟨cp, hcpmem, hcp⟩ := List.any_eq_true.mp hup
  rw [decide_eq_true_eq] at hcp
  exact ⟨cp, hcpmem, (mem_transClosure_imp_transGen _ hcp).to_reflTransGen⟩

/-- **The initialization-ordering check, read forward**: every use of an
mbarrier has an in-thread predecessor, after which its initialization is
forced (reflexively — the `init_mb` may itself be the predecessor). -/
theorem init_hb_of_check {T : CTA} {τ : List Config}
    (hcheck : okInitCheck T τ = true)
    {ip : ProgPoint} (hip : ip ∈ T.progPoints) {sb : SharedBarrier} {n : ℕ+}
    (hcmdip : T.cmdAt ip = some (.init_mb sb n))
    {u : ProgPoint} (hu : u ∈ T.progPoints)
    (huse : (T.cmdAt u).bind Cmd.usesMBarrier? = some sb) :
    1 ≤ u.idx ∧ happensBefore T τ ip ⟨u.thread, u.idx - 1⟩ := by
  simp only [okInitCheck] at hcheck
  have hf1 := List.all_eq_true.mp hcheck ip hip
  simp only [hcmdip] at hf1
  have hf2 := List.all_eq_true.mp hf1 u hu
  rw [if_pos huse] at hf2
  by_cases hidx : 1 ≤ u.idx
  · rw [if_pos hidx, decide_eq_true_eq] at hf2
    refine ⟨hidx, ?_⟩
    rcases hf2 with heq | hmem
    · rw [heq]
      exact Relation.ReflTransGen.refl
    · exact (mem_transClosure_imp_transGen _ hmem).to_reflTransGen
  · rw [if_neg hidx] at hf2
    exact absurd hf2 (by simp)

/-! ## Trace-time support (soundness)

The `pointTime`/`pointGen` toolkit the conformance induction reads challenger
traces with: behavior under appending one configuration (`τ' ++ [C']` — the
snoc workhorses), decodes of computed times on *partial* traces, and the
counting helpers. Ports of the named-barrier lemmas of the same names. -/

/-- `findSome?` respects pointwise-equal functions. -/
theorem findSome?_congr {α : Type*} {β : Type*} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.findSome?_cons]
    rw [h a (List.mem_cons_self ..)]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some b => rfl

/-- `recycleCount` ignores an appended configuration while the bound stays within the
original trace. -/
theorem recycleCount_append (b : NamedBarrier ⊕ SharedBarrier) (τ' : List Config)
    (C' : Config) {j : Nat} (hj : j + 1 ≤ τ'.length) :
    recycleCount b (τ' ++ [C']) j = recycleCount b τ' j := by
  unfold recycleCount
  refine List.countP_congr fun i hi => ?_
  rw [List.mem_range] at hi
  have h1 : (τ' ++ [C'])[i]? = τ'[i]? := List.getElem?_append_left (by omega)
  have h2 : (τ' ++ [C'])[i + 1]? = τ'[i + 1]? := List.getElem?_append_left (by omega)
  rw [h1, h2]

/-- A computed time survives appending a configuration. -/
theorem pointTime_append_some {T : CTA} {τ' : List Config} {C' : Config}
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m) :
    pointTime T (τ' ++ [C']) η = some m := by
  have hne : τ' ≠ [] := by
    intro h
    rw [h] at hpt
    simp [pointTime] at hpt
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime, if_pos hidx] at hpt ⊢
    have hlen : (τ' ++ [C']).length - 1 = (τ'.length - 1) + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlen, List.range_succ, List.findSome?_append]
    have hcongr : List.findSome? (fun j =>
        match (τ' ++ [C'])[j]?, (τ' ++ [C'])[j + 1]? with
        | some C, some C'' =>
            if (C.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx &&
                (C''.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx - 1 then
              some (j + 1) else none
        | _, _ => none) (List.range (τ'.length - 1)) = some m := by
      rw [findSome?_congr (g := fun j =>
        match τ'[j]?, τ'[j + 1]? with
        | some C, some C'' =>
            if (C.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx &&
                (C''.progOf η.thread).length ==
                  (T.prog η.thread).length - η.idx - 1 then
              some (j + 1) else none
        | _, _ => none) ?_]
      · exact hpt
      · intro a ha
        rw [List.mem_range] at ha
        have h1 : (τ' ++ [C'])[a]? = τ'[a]? := List.getElem?_append_left (by omega)
        have h2 : (τ' ++ [C'])[a + 1]? = τ'[a + 1]? := List.getElem?_append_left (by omega)
        rw [h1, h2]
    rw [hcongr]
    rfl
  · simp only [pointTime, if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- A computed time on `τ' ++ [C']` is either an old time of `τ'` or the appended step
itself. -/
theorem pointTime_append_cases {T : CTA} {τ' : List Config} {C' : Config}
    (hne : τ' ≠ []) {η : ProgPoint} {m : Nat}
    (hpt : pointTime T (τ' ++ [C']) η = some m) :
    pointTime T τ' η = some m ∨ (pointTime T τ' η = none ∧ m = τ'.length) := by
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  cases hptτ : pointTime T τ' η with
  | some m' =>
    have hσ := pointTime_append_some (C' := C') hptτ
    rw [hpt, Option.some.injEq] at hσ
    subst hσ
    exact Or.inl rfl
  | none =>
    refine Or.inr ⟨rfl, ?_⟩
    by_cases hidx : η.idx < (T.prog η.thread).length
    · simp only [pointTime, if_pos hidx] at hpt hptτ
      have hlen : (τ' ++ [C']).length - 1 = (τ'.length - 1) + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hlen, List.range_succ, List.findSome?_append] at hpt
      have hcongr : List.findSome? (fun j =>
          match (τ' ++ [C'])[j]?, (τ' ++ [C'])[j + 1]? with
          | some C, some C'' =>
              if (C.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx &&
                  (C''.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx - 1 then
                some (j + 1) else none
          | _, _ => none) (List.range (τ'.length - 1)) = none := by
        rw [findSome?_congr (g := fun j =>
          match τ'[j]?, τ'[j + 1]? with
          | some C, some C'' =>
              if (C.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx &&
                  (C''.progOf η.thread).length ==
                    (T.prog η.thread).length - η.idx - 1 then
                some (j + 1) else none
          | _, _ => none) ?_]
        · exact hptτ
        · intro a ha
          rw [List.mem_range] at ha
          have h1 : (τ' ++ [C'])[a]? = τ'[a]? := List.getElem?_append_left (by omega)
          have h2 : (τ' ++ [C'])[a + 1]? = τ'[a + 1]? :=
            List.getElem?_append_left (by omega)
          rw [h1, h2]
      rw [hcongr, Option.none_or, List.findSome?_cons] at hpt
      split at hpt
      · rename_i b₀ hb₀
        rw [Option.some.injEq] at hpt
        -- the matcher value is `some (τ'.length - 1 + 1)`
        split at hb₀
        · rename_i C₁ C₂ hC₁ hC₂
          split at hb₀
          · rw [Option.some.injEq] at hb₀
            omega
          · simp at hb₀
        · simp at hb₀
      · simp at hpt
    · simp only [pointTime, if_neg hidx] at hpt
      exact absurd hpt (by simp)

/-- Counting forces pointwise agreement: if `p` implies `q` on `l` and `q`'s count does
not exceed `p`'s, then `q` implies `p` on `l`. -/
theorem countP_eq_all {α : Type*} : ∀ {l : List α} {p q : α → Bool},
    (∀ x ∈ l, p x = true → q x = true) → l.countP q ≤ l.countP p →
    ∀ x ∈ l, q x = true → p x = true := by
  intro l
  induction l with
  | nil => intro p q _ _ x hx; simp at hx
  | cons a t ih =>
    intro p q himp hle x hx hqx
    have himpt : ∀ y ∈ t, p y = true → q y = true :=
      fun y hy => himp y (List.mem_cons_of_mem _ hy)
    have hmt : t.countP p ≤ t.countP q := List.countP_mono_left himpt
    simp only [List.countP_cons] at hle
    rcases List.mem_cons.mp hx with rfl | hxt
    · by_contra hpx
      rw [Bool.not_eq_true] at hpx
      rw [hqx, hpx] at hle
      simp at hle
      omega
    · refine ih himpt ?_ x hxt hqx
      by_cases hpa : p a = true
      · rw [hpa, himp a (List.mem_cons_self ..) hpa] at hle
        simpa using hle
      · rw [Bool.not_eq_true] at hpa
        rw [hpa] at hle
        cases hqa : q a
        · rw [hqa] at hle
          simpa using hle
        · rw [hqa] at hle
          simp at hle
          omega

/-- **Lift a head-dropping step to a static program point.** If at step `j → j+1` thread
`i`'s remaining program goes from `c :: rest` to `rest`, then the static point
`⟨i, |T.prog i| - |C.progOf i|⟩` executes at time `j + 1`, and its static command is
`c`. -/
theorem exec_step_time {T : CTA} {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ)
    {j : Nat} {C C' : Config} (hCj : τ[j]? = some C) (hCj1 : τ[j + 1]? = some C')
    {i : ThreadId} {c : Cmd} {rest : Prog}
    (hC : C.progOf i = c :: rest) (hC' : C'.progOf i = rest) :
    IsTimeOf (Config.run State.initial T) τ
        ⟨i, (T.prog i).length - (C.progOf i).length⟩ (j + 1) ∧
      T.cmdAt ⟨i, (T.prog i).length - (C.progOf i).length⟩ = some c := by
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hsuf : C.progOf i <:+ (Config.run State.initial T).progOf i :=
    progOf_suffix_index_le hchain i h0 (Nat.zero_le j) hCj
  have hlen : (C.progOf i).length ≤ (T.prog i).length := suffix_length_le hsuf
  have hpos : 0 < (C.progOf i).length := by rw [hC]; simp
  have hdropk : C.progOf i = (T.prog i).drop ((T.prog i).length - (C.progOf i).length) :=
    List.IsSuffix.eq_drop hsuf
  have hkL : (T.prog i).length - (C.progOf i).length < (T.prog i).length := by omega
  have hdropk1 : C'.progOf i =
      (T.prog i).drop ((T.prog i).length - (C.progOf i).length + 1) := by
    rw [hC', ← List.tail_drop, ← hdropk, hC, List.tail_cons]
  exact ⟨⟨hτ, hkL, j, C, C', rfl, hCj, hCj1, hdropk, hdropk1⟩, cmd_at_last hsuf hC⟩

/-- Discrete search: a `ℕ`-valued function that grows over an interval increases at some
step inside it. -/
theorem exists_step_increase (f : Nat → Nat) :
    ∀ (hi lo : Nat), lo ≤ hi → f lo < f hi →
      ∃ j, lo ≤ j ∧ j < hi ∧ f j < f (j + 1) := by
  intro hi
  induction hi with
  | zero =>
    intro lo hle hlt
    obtain rfl : lo = 0 := Nat.le_zero.mp hle
    exact absurd hlt (lt_irrefl _)
  | succ k ih =>
    intro lo hle hlt
    by_cases hlo : lo ≤ k
    · by_cases hk : f k < f (k + 1)
      · exact ⟨k, hlo, Nat.lt_succ_self k, hk⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih lo hlo (by omega)
        exact ⟨j, h1, by omega, h3⟩
    · obtain rfl : lo = k + 1 := by omega
      exact absurd hlt (lt_irrefl _)

/-- A computed `pointTime` is a genuine `IsTimeOf` (converse of
`pointTime_eq_of_isTimeOf`). -/
theorem isTimeOf_of_pointTime {T : CTA} {τ : List Config}
    (hτ : IsCompleteTraceFrom (Config.run State.initial T) τ)
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ η = some m) :
    IsTimeOf (Config.run State.initial T) τ η m := by
  have hchain := hτ.1.subtrace
  have h0 : τ[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hC₀ : (Config.run State.initial T).progOf η.thread = T.prog η.thread := rfl
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime] at hpt
    rw [if_pos hidx] at hpt
    rw [List.findSome?_eq_some_iff] at hpt
    obtain ⟨l₁, a, l₂, -, hfa, -⟩ := hpt
    split at hfa
    · rename_i C C' hCa hCa1
      split at hfa
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hl1, hl2⟩ := hcond
        rw [Option.some.injEq] at hfa
        subst hfa
        refine ⟨hτ, hidx, a, C, C', rfl, hCa, hCa1, ?_, ?_⟩
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le a) hCa)
          rw [hl1, hC₀] at heq
          rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
            from by omega] at heq
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0 (Nat.zero_le (a + 1)) hCa1)
          rw [hl2, hC₀] at heq
          rwa [show (T.prog η.thread).length -
              ((T.prog η.thread).length - η.idx - 1) = η.idx + 1
            from by omega] at heq
      · simp at hfa
    · simp at hfa
  · simp only [pointTime] at hpt
    rw [if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- `pointGen` read off a computed `pointTime` (works on partial traces). -/
theorem pointGen_eq_of_pointTime {T : CTA} {τ' : List Config} {η : ProgPoint}
    {c : Cmd} {b : NamedBarrier ⊕ SharedBarrier}
    (hcm : T.cmdAt η = some c) (hbar : c.barrier? = some b) {m : Nat}
    (hpt : pointTime T τ' η = some m) :
    pointGen T τ' η = some (c.genValue (recycleCount b τ' (m - 1))) := by
  simp only [pointGen, hcm, hbar, hpt]

/-- Unpack a computed `pointTime` on a *partial* trace into the executing step's drop
facts. (`IsTimeOf` requires a complete trace; this is the raw content, available on any
chain from the initial configuration.) -/
theorem pointTime_spec {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m) :
    1 ≤ m ∧ m < τ'.length ∧ η.idx < (T.prog η.thread).length ∧
    ∃ C C', τ'[m - 1]? = some C ∧ τ'[m]? = some C' ∧
      C.progOf η.thread = (T.prog η.thread).drop η.idx ∧
      C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) := by
  have h0' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact h0
  have hC₀ : (Config.run State.initial T).progOf η.thread = T.prog η.thread := rfl
  by_cases hidx : η.idx < (T.prog η.thread).length
  · simp only [pointTime] at hpt
    rw [if_pos hidx] at hpt
    rw [List.findSome?_eq_some_iff] at hpt
    obtain ⟨l₁, a, l₂, -, hfa, -⟩ := hpt
    split at hfa
    · rename_i C C' hCa hCa1
      split at hfa
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hl1, hl2⟩ := hcond
        rw [Option.some.injEq] at hfa
        subst hfa
        have hmlt : a + 1 < τ'.length := (List.getElem?_eq_some_iff.mp hCa1).1
        refine ⟨by omega, hmlt, hidx, C, C',
          by rw [show a + 1 - 1 = a by omega]; exact hCa, hCa1, ?_, ?_⟩
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0' (Nat.zero_le a) hCa)
          rw [hl1, hC₀] at heq
          rwa [show (T.prog η.thread).length - ((T.prog η.thread).length - η.idx) = η.idx
            from by omega] at heq
        · have heq := List.IsSuffix.eq_drop
            (progOf_suffix_index_le hchain η.thread h0' (Nat.zero_le (a + 1)) hCa1)
          rw [hl2, hC₀] at heq
          rwa [show (T.prog η.thread).length -
              ((T.prog η.thread).length - η.idx - 1) = η.idx + 1
            from by omega] at heq
      · simp at hfa
    · simp at hfa
  · simp only [pointTime] at hpt
    rw [if_neg hidx] at hpt
    exact absurd hpt (by simp)

/-- A `sync_nb`'s computed time on a partial trace is a recycle of its barrier
(`sync_time_recycles` without the completeness packaging). -/
theorem pointTime_sync_recycles {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m)
    {bb : NamedBarrier} {nn : ℕ+} (hcm : T.cmdAt η = some (.sync_nb bb nn)) :
    ∃ C C', τ'[m - 1]? = some C ∧ τ'[m]? = some C' ∧
      stepRecyclesBarrier (.inl bb) C C' = true := by
  obtain ⟨hm1, hmlt, hidx, C, C', hC, hC', hCdrop, hC'drop⟩ := pointTime_spec hchain h0 hpt
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm
  have hcons : C.progOf η.thread =
      Cmd.sync_nb bb nn :: (T.prog η.thread).drop (η.idx + 1) := by
    rw [hCdrop, List.drop_eq_getElem_cons hidx, hget0]
  have hCC' : τ'[m - 1 + 1]? = some C' := by
    rw [show m - 1 + 1 = m by omega]; exact hC'
  have hstep := chain_step hchain hC hCC'
  exact ⟨C, C', hC, hC', sync_drop_recycles hstep hcons hC'drop⟩

/-- A `wait_mb`'s computed time on a partial trace is either a recycle of its barrier
(the wait was parked and is being woken) or a pass at a mismatched phase
(`wait_time_recycles_or_pass` without the completeness packaging). -/
theorem pointTime_wait_recycles_or_pass {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {η : ProgPoint} {m : Nat} (hpt : pointTime T τ' η = some m)
    {sb : SharedBarrier} {ph : Phase} (hcm : T.cmdAt η = some (.wait_mb sb ph)) :
    (∃ C C', τ'[m - 1]? = some C ∧ τ'[m]? = some C' ∧
      stepRecyclesBarrier (.inr sb) C C' = true) ∨
    (∃ s Tc, τ'[m - 1]? = some (Config.run s Tc) ∧ s.E η.thread = true ∧
      (s.BM sb).phase ≠ ph) := by
  obtain ⟨hm1, hmlt, hidx, C, C', hC, hC', hCdrop, hC'drop⟩ := pointTime_spec hchain h0 hpt
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcm
  have hcons : C.progOf η.thread =
      Cmd.wait_mb sb ph :: (T.prog η.thread).drop (η.idx + 1) := by
    rw [hCdrop, List.drop_eq_getElem_cons hidx, hget0]
  have hCC' : τ'[m - 1 + 1]? = some C' := by
    rw [show m - 1 + 1 = m by omega]; exact hC'
  have hstep := chain_step hchain hC hCC'
  rcases wait_drop_recycles_or_pass hstep hcons hC'drop with
    hrec | ⟨s, Tc, hCrun, hE, hph⟩
  · exact Or.inl ⟨C, C', hC, hC', hrec⟩
  · exact Or.inr ⟨s, Tc, by rw [hCrun] at hC; exact hC, hE, hph⟩

/-- **A passed instruction has executed** (partial-trace variant of
`exists_time_of_ends_done`): if the last configuration's remaining program for thread
`i` has length at most `|T.prog i| - (k + 1)`, the pointer moved past instruction `k`,
so point `⟨i, k⟩` has a computed time. Intermediate-value argument on program lengths. -/
theorem exists_pointTime_of_passed {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {C : Config} (hlast : τ'.getLast? = some C) {i : ThreadId} {k : Nat}
    (hk : k < (T.prog i).length)
    (hpassed : (C.progOf i).length + (k + 1) ≤ (T.prog i).length) :
    ∃ m, pointTime T τ' ⟨i, k⟩ = some m := by
  have h0' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact h0
  have hlastidx : τ'[τ'.length - 1]? = some C := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlen1 : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at h0
    | cons a l => simp
  have hsuffix : ∀ {j} {D : Config}, τ'[j]? = some D →
      D.progOf i <:+ (Config.run State.initial T).progOf i :=
    fun {j D} hD => progOf_suffix_index_le hchain i h0' (Nat.zero_le j) hD
  have hQlast : ((τ'[τ'.length - 1]?).map (fun D => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := by
    rw [hlastidx]
    change (C.progOf i).length < (T.prog i).length - k
    omega
  have hex : ∃ j, ((τ'[j]?).map (fun (D : Config) => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := ⟨τ'.length - 1, hQlast⟩
  have hQj0 := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ τ'.length - 1 := Nat.find_le hQlast
  have hQ0 : ¬ ((τ'[0]?).map (fun D => (D.progOf i).length)).getD 0
      < (T.prog i).length - k := by
    rw [h0']
    change ¬ (T.prog i).length < (T.prog i).length - k
    omega
  have hj0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hQj0; exact absurd hQj0 hQ0
    · exact h
  have hminj := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have hj0lt : Nat.find hex < τ'.length := by omega
  obtain ⟨D, hD⟩ : ∃ D, τ'[Nat.find hex - 1]? = some D :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨D', hD'⟩ : ∃ D', τ'[Nat.find hex]? = some D' :=
    ⟨_, List.getElem?_eq_getElem hj0lt⟩
  have hDD' : τ'[Nat.find hex - 1 + 1]? = some D' := by
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hD'
  have hub : (D.progOf i).length ≤ (D'.progOf i).length + 1 :=
    (chain_step hchain hD hDD').progOf_length_le_succ i
  have e1 : ((τ'[Nat.find hex - 1]?).map (fun D => (D.progOf i).length)).getD 0
      = (D.progOf i).length := by rw [hD]; rfl
  have e2 : ((τ'[Nat.find hex]?).map (fun D => (D.progOf i).length)).getD 0
      = (D'.progOf i).length := by rw [hD']; rfl
  rw [e1] at hminj
  rw [e2] at hQj0
  have hlenD : (D.progOf i).length = (T.prog i).length - k := by omega
  have hlenD' : (D'.progOf i).length = (T.prog i).length - k - 1 := by omega
  have hne : pointTime T τ' ⟨i, k⟩ ≠ none := by
    intro hnone
    simp only [pointTime] at hnone
    rw [if_pos hk] at hnone
    rw [List.findSome?_eq_none_iff] at hnone
    have hjmem : Nat.find hex - 1 ∈ List.range (τ'.length - 1) :=
      List.mem_range.mpr (by omega)
    have hmatch := hnone _ hjmem
    simp only [hD, hDD', hlenD, hlenD'] at hmatch
    simp at hmatch
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨m, hm⟩

/-- Thread `η.thread`'s control sits exactly *at* instruction `η` in configuration `C`:
its remaining program is the suffix of its initial program starting at `η.idx`
(length-based, matching the repo's program-position idiom). For a parked `sync_nb` or
`wait_mb` this is where the pointer stays until the recycle. -/
def pointerAt (T : CTA) (η : ProgPoint) (C : Config) : Prop :=
  (C.progOf η.thread).length = (T.prog η.thread).length - η.idx

/-- A point whose thread's control still sits *at* it in the trace's last configuration
has no computed time. -/
theorem pointTime_none_of_pointerAt {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {C : Config} (hlast : τ'.getLast? = some C)
    {η : ProgPoint} (hat : pointerAt T η C) :
    pointTime T τ' η = none := by
  cases hpt : pointTime T τ' η with
  | none => rfl
  | some m =>
    exfalso
    obtain ⟨hm1, hmlt, hidx, C₁, C₂, hC₁, hC₂, -, hdrop2⟩ := pointTime_spec hchain h0 hpt
    have hlastidx : τ'[τ'.length - 1]? = some C := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    have hsuf := progOf_suffix_index_le hchain η.thread hC₂
      (show m ≤ τ'.length - 1 by omega) hlastidx
    have hle := suffix_length_le hsuf
    rw [hdrop2] at hle
    simp only [List.length_drop] at hle
    have hat' : (C.progOf η.thread).length = (T.prog η.thread).length - η.idx := hat
    omega

/-! ## Generation fibers (soundness support)

The **generation fiber** `F_g(b)`: the registrants of `b` to which the
reference trace assigns generation `g` — Algorithm 2's `Reg(b, g)` as a list.
The rounds of `b` in any conforming challenger trace consume exactly these,
one fiber per recycle. Fibers are kind-pure: an `.inl nb` fiber holds
`arrive_nb`/`sync_nb`s and an `.inr sb` fiber holds only `arrive_mb`s (a
`wait_mb` blocks without registering; an `init_mb` configures without
registering). ℤ-indexed to match `pointGen`; registrant fibers at negative
generations are empty (`pointGen_registrant_nonneg`), so the counting lemmas
take a `ℕ` round index and cast. -/

/-- The expected-count parameter of the counted barrier commands
(`arrive_nb`/`sync_nb` carry `n`); `none` for everything else. An `arrive_mb`
carries no count — its barrier's capacity lives in the unique `init_mb`
(`CTA.initCountOf`). -/
def Cmd.count? : Cmd → Option ℕ+
  | .arrive_nb _ n => some n
  | .sync_nb _ n => some n
  | _ => none

/-- The generation fiber `F_g(b)` of the reference trace. -/
def genFiber (T : CTA) (τ : List Config) (b : NamedBarrier ⊕ SharedBarrier) (g : ℤ) :
    List ProgPoint :=
  T.progPoints.filter fun η => decide (registrantGen T τ η = some (b, g))

/-- Fiber membership, unfolded. -/
theorem mem_genFiber {T : CTA} {τ : List Config} {b : NamedBarrier ⊕ SharedBarrier}
    {g : ℤ} {η : ProgPoint} :
    η ∈ genFiber T τ b g ↔ η ∈ T.progPoints ∧ registrantGen T τ η = some (b, g) := by
  simp [genFiber, List.mem_filter]

/-- Fibers inherit `Nodup` from `progPoints`. -/
theorem genFiber_nodup (T : CTA) (τ : List Config) (b : NamedBarrier ⊕ SharedBarrier)
    (g : ℤ) : (genFiber T τ b g).Nodup :=
  (progPoints_nodup T).filter _

/-- `pointGen` read off at a known execution time. -/
theorem pointGen_eq_of_time {T : CTA} {τ : List Config} {η : ProgPoint} {c : Cmd}
    (hcm : T.cmdAt η = some c) {b : NamedBarrier ⊕ SharedBarrier}
    (hbar : c.barrier? = some b) {m : Nat}
    (hm : IsTimeOf (Config.run State.initial T) τ η m) :
    pointGen T τ η = some (c.genValue (recycleCount b τ (m - 1))) := by
  simp only [pointGen, hcm, hbar, pointTime_eq_of_isTimeOf hm]

/-- A registrant's generation at a known execution time is the plain recycle
count (no wait correction). -/
theorem pointGen_registrant_eq_of_time {T : CTA} {τ : List Config} {η : ProgPoint}
    {c : Cmd} (hcm : T.cmdAt η = some c) (hreg : c.isRegistrant = true)
    {b : NamedBarrier ⊕ SharedBarrier} (hbar : c.barrier? = some b) {m : Nat}
    (hm : IsTimeOf (Config.run State.initial T) τ η m) :
    pointGen T τ η = some ((recycleCount b τ (m - 1) : ℕ) : ℤ) := by
  rw [pointGen_eq_of_time hcm hbar hm, genValue_of_isRegistrant hreg]

/-- A `some`-generation registrant has a nonnegative generation (it observes the
plain recycle count). -/
theorem pointGen_registrant_nonneg {T : CTA} {τ : List Config} {c : ProgPoint}
    {cmd : Cmd} (hcmd : T.cmdAt c = some cmd) (hreg : cmd.isRegistrant = true)
    {k : ℤ} (hpg : pointGen T τ c = some k) : 0 ≤ k := by
  unfold pointGen at hpg
  simp only [hcmd] at hpg
  cases hb : cmd.barrier? with
  | none => simp only [hb] at hpg; exact absurd hpg (by simp)
  | some b =>
    simp only [hb] at hpg
    cases ht : pointTime T τ c with
    | none => simp only [ht] at hpg; exact absurd hpg (by simp)
    | some m =>
      simp only [ht, Option.some.injEq] at hpg
      rw [genValue_of_isRegistrant hreg] at hpg
      omega


/-- Build fiber membership from an execution time: a registrant executing with
`g` recycles of its barrier strictly before it lies in `F_g(b)`. -/
theorem mem_genFiber_of_time {T : CTA} {τ : List Config} {η : ProgPoint}
    {c : Cmd} (hcm : T.cmdAt η = some c) (hreg : c.isRegistrant = true)
    {b : NamedBarrier ⊕ SharedBarrier} (hbar : c.barrier? = some b) {m : Nat}
    (hm : IsTimeOf (Config.run State.initial T) τ η m) {g : ℕ}
    (hg : recycleCount b τ (m - 1) = g) :
    η ∈ genFiber T τ b (g : ℤ) := by
  have hpg := pointGen_registrant_eq_of_time hcm hreg hbar hm
  rw [hg] at hpg
  refine mem_genFiber.mpr ⟨mem_progPoints_of_cmdAt T hcm, ?_⟩
  unfold registrantGen
  simp [hcm, hpg, if_pos hreg, hbar]

/-- Decode a fiber member in a successful trace: its command is a registrant on
`b`, it executes at some time `m`, and exactly `g` recycles of `b` precede `m`. -/
theorem genFiber_time_data {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℕ} {η : ProgPoint}
    (hη : η ∈ genFiber T τ b (g : ℤ)) :
    ∃ (c : Cmd) (m : Nat), T.cmdAt η = some c ∧ c.isRegistrant = true ∧
      c.barrier? = some b ∧ IsTimeOf (Config.run State.initial T) τ η m ∧
      pointTime T τ η = some m ∧ 1 ≤ m ∧ m < τ.length ∧
      recycleCount b τ (m - 1) = g := by
  obtain ⟨hmem, hregmem⟩ := mem_genFiber.mp hη
  obtain ⟨c, hcm, hisreg, hbar, hpg⟩ := registrantGen_some hregmem
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  have hpg' := pointGen_registrant_eq_of_time hcm hisreg hbar hm
  rw [hpg] at hpg'
  have hgm : recycleCount b τ (m - 1) = g := by
    have := Option.some.inj hpg'
    omega
  have hm1 : 1 ≤ m := by
    obtain ⟨-, -, j, -, -, hj, -, -, -, -⟩ := hm
    omega
  have hmlt : m < τ.length := by
    obtain ⟨-, -, j, C₁, C₂, hj, -, hCj1, -, -⟩ := hm
    have := (List.getElem?_eq_some_iff.mp hCj1).1
    omega
  exact ⟨c, m, hcm, hisreg, hbar, hm, pointTime_eq_of_isTimeOf hm, hm1, hmlt, hgm⟩

/-- Configuration `j` of a chain is reachable from the chain's start — bridges trace
indices to the `WF_of_reaches` machinery. -/
theorem reaches_of_chain_getElem {τ : List Config} (hchain : List.IsChain CTAStep τ)
    {C₀ : Config} (h0 : τ[0]? = some C₀) :
    ∀ (j : Nat) (C : Config), τ[j]? = some C → Relation.ReflTransGen CTAStep C₀ C := by
  intro j
  induction j with
  | zero =>
    intro C hC
    rw [h0] at hC
    obtain rfl := Option.some.inj hC
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro C hC
    have hlt : k + 1 < τ.length := (List.getElem?_eq_some_iff.mp hC).1
    have hklt : k < τ.length := by omega
    have hCk : τ[k]? = some τ[k] := List.getElem?_eq_getElem hklt
    exact (ih _ hCk).tail (chain_step hchain hCk hC)

/-- Each step adds at most one recycle of `b`. -/
theorem recycleCount_le_succ (b : NamedBarrier ⊕ SharedBarrier) (τ : List Config)
    (j : Nat) : recycleCount b τ (j + 1) ≤ recycleCount b τ j + 1 := by
  unfold recycleCount
  rw [List.range_succ, List.countP_append]
  exact Nat.add_le_add_left (List.countP_le_length.trans (by simp)) _

/-- Locate the `g`-th recycle of `b`: if at least `g ≥ 1` recycles occur within the
first `M` steps, some step `p < M` is the `g`-th — the count is `g - 1` before it and
`g` after. -/
theorem recycleCount_hits (b : NamedBarrier ⊕ SharedBarrier) (τ : List Config)
    {g M : Nat} (hg : 1 ≤ g) (hM : g ≤ recycleCount b τ M) :
    ∃ p, p < M ∧ recycleCount b τ p = g - 1 ∧ recycleCount b τ (p + 1) = g := by
  induction M with
  | zero =>
    exfalso
    have h0 : recycleCount b τ 0 = 0 := by unfold recycleCount; simp
    omega
  | succ k ih =>
    by_cases hk : g ≤ recycleCount b τ k
    · obtain ⟨p, hp, h1, h2⟩ := ih hk
      exact ⟨p, by omega, h1, h2⟩
    · have hle := recycleCount_le_succ b τ k
      exact ⟨k, by omega, by omega, by omega⟩

/-- Extract the recycling step at a `recycleCount` increase. -/
theorem recycle_step_of_count_lt {b : NamedBarrier ⊕ SharedBarrier} {τ : List Config}
    {p : Nat} (h : recycleCount b τ p < recycleCount b τ (p + 1)) :
    ∃ C C', τ[p]? = some C ∧ τ[p + 1]? = some C' ∧ stepRecyclesBarrier b C C' = true := by
  obtain ⟨C, hC⟩ : ∃ C, τ[p]? = some C := by
    rcases hex : τ[p]? with _ | C
    · exfalso
      have heq : recycleCount b τ (p + 1) = recycleCount b τ p := by
        unfold recycleCount
        rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
        simp [hex]
      omega
    · exact ⟨C, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C', τ[p + 1]? = some C' := by
    rcases hex : τ[p + 1]? with _ | C'
    · exfalso
      have heq : recycleCount b τ (p + 1) = recycleCount b τ p := by
        unfold recycleCount
        rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
        simp [hC, hex]
      omega
    · exact ⟨C', rfl⟩
  refine ⟨C, C', hC, hC', ?_⟩
  by_contra hf
  rw [Bool.not_eq_true] at hf
  have := recycleCount_succ_of_not_recycle b hC hC' hf
  omega

/-- **Decode a named recycling step.** The `CTAStep` behind
`stepRecyclesBarrier (.inl nb)` is necessarily `CTAStep.recycle` *of `nb`*:
`interleave`/`error`'s guards keep every barrier under-full, `done` and the
mbarrier rules keep `BN`, and a recycle of another barrier leaves `nb` untouched.
Exposes the full pre-step barrier state — full, with every parked thread's head
at the matching `sync_nb nb n` — and the exact post-step configuration. -/
theorem stepRecyclesBarrier_elim_nb {C C' : Config} (hstep : CTAStep C C')
    {nb : NamedBarrier} (hrec : stepRecyclesBarrier (.inl nb) C C' = true) :
    ∃ s Tc I A n, C = Config.run s Tc ∧ s.BN nb = ⟨I, A, some n⟩ ∧
      I.length + A = (n : ℕ) ∧ (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.sync_nb nb n)) ∧
      C' = Config.run
        ({ s with E := updateMapOn s.E I true,
                  BN := Function.update s.BN nb NamedBarrierState.unconfigured })
        (Tc.wake I) := by
  cases hstep with
  | @interleave s s' Tc i P' hi hbar hmbar hth =>
    exfalso
    have hnf : (s.BN nb).isFull = false := by
      rcases hbar nb with hu | ⟨I, A, n, hcfg, hlt⟩
      · rw [hu]; rfl
      · rw [hcfg]; simp only [NamedBarrierState.isFull]
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf] at hrec
  | @recycle s Tc nb' I A n hb hfull hpark =>
    by_cases hbb : nb' = nb
    · subst hbb
      exact ⟨s, Tc, I, A, n, rfl, hb, hfull, hpark, rfl⟩
    · exfalso
      have hupd : (Function.update s.BN nb' NamedBarrierState.unconfigured) nb =
          s.BN nb := Function.update_of_ne (Ne.symm hbb) _ _
      simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true, hupd,
        decide_eq_true_eq] at hrec
      obtain ⟨hfl, hunc⟩ := hrec
      rw [hunc] at hfl
      simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
  | @mb_recycle s Tc sb I A n ph hb hfull hpark =>
    exfalso
    simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true,
      decide_eq_true_eq] at hrec
    obtain ⟨hfl, hunc⟩ := hrec
    rw [hunc] at hfl
    simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
  | done hdone hnofull hmbnofull =>
    exfalso
    simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true,
      decide_eq_true_eq] at hrec
    obtain ⟨hfl, hunc⟩ := hrec
    rw [hunc] at hfl
    simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
  | error hbar hmbar hth =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?] at hrec

/-- **Decode an mbarrier recycling step.** The `CTAStep` behind
`stepRecyclesBarrier (.inr sb)` is necessarily `CTAStep.mb_recycle` *of `sb`*:
the guards keep every barrier under-full, and every other rule leaves `sb`'s
state fixed — which the required `⟨[], 0, count, !phase⟩` shape never is
(`mb_flip_ne`). Exposes the full pre-step barrier state — arrivals at capacity,
every parked waiter's head at the matching `wait_mb sb ph` — and the exact
post-step configuration (count kept, phase flipped). -/
theorem stepRecyclesBarrier_elim_mb {C C' : Config} (hstep : CTAStep C C')
    {sb : SharedBarrier} (hrec : stepRecyclesBarrier (.inr sb) C C' = true) :
    ∃ s Tc I A n ph, C = Config.run s Tc ∧ s.BM sb = ⟨I, A, some n, ph⟩ ∧
      A = (n : ℕ) ∧ (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.wait_mb sb ph)) ∧
      C' = Config.run
        ({ s with E := updateMapOn s.E I true,
                  BM := Function.update s.BM sb ⟨[], 0, some n, !ph⟩ })
        (Tc.wake I) := by
  cases hstep with
  | @interleave s s' Tc i P' hi hbar hmbar hth =>
    exfalso
    have hnf : (s.BM sb).isFull = false := by
      rcases hmbar sb with hu | ⟨I, A, n, ph, hcfg, hlt⟩
      · rw [hu]; rfl
      · rw [hcfg]; simp only [MBarrierState.isFull]
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf] at hrec
  | @recycle s Tc nb I A n hb hfull hpark =>
    exfalso
    simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true,
      decide_eq_true_eq] at hrec
    exact mb_flip_ne (s.BM sb) hrec.2
  | @mb_recycle s Tc sb' I A n ph hb hfull hpark =>
    by_cases hbb : sb' = sb
    · subst hbb
      exact ⟨s, Tc, I, A, n, ph, rfl, hb, hfull, hpark, rfl⟩
    · exfalso
      have hupd : (Function.update s.BM sb' ⟨[], 0, some n, !ph⟩) sb = s.BM sb :=
        Function.update_of_ne (Ne.symm hbb) _ _
      simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true, hupd,
        decide_eq_true_eq] at hrec
      exact mb_flip_ne (s.BM sb) hrec.2
  | done hdone hnofull hmbnofull =>
    exfalso
    simp only [stepRecyclesBarrier, WeftCommon.Config.state?, Bool.and_eq_true,
      decide_eq_true_eq] at hrec
    exact mb_flip_ne _ hrec.2
  | error hbar hmbar hth =>
    exfalso
    simp [stepRecyclesBarrier, WeftCommon.Config.state?] at hrec

/-- Classify a step's effect on named barrier `nb`'s arrival count: unchanged, an
`arrive_nb nb _` execution (head dropped), or a recycle of `nb`. -/
theorem arrived_step_nb {C C' : Config} (hstep : CTAStep C C') {nb : NamedBarrier}
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s') :
    (s'.BN nb).arrived = (s.BN nb).arrived ∨
    (∃ (i : ThreadId) (n' : ℕ+) (rest : Prog),
      C.progOf i = Cmd.arrive_nb nb n' :: rest ∧ C'.progOf i = rest) ∨
    stepRecyclesBarrier (.inl nb) C C' = true := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hmbar hth =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPi] at hth
    cases hth with
    | read_noop => exact Or.inl rfl
    | write_noop => exact Or.inl rfl
    | @arrive_configure _ _ ba na _ he hb =>
      by_cases hbb : nb = ba
      · subst hbb
        refine Or.inr (Or.inl ⟨t, na, P', hPi, ?_⟩)
        simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self]
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @arrive_register _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : nb = ba
      · subst hbb
        refine Or.inr (Or.inl ⟨t, na, P', hPi, ?_⟩)
        simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self]
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @sync_configure _ _ ba na _ he hb =>
      by_cases hbb : nb = ba
      · subst hbb
        exact Or.inl (by
          simp [Function.update_self, hb, NamedBarrierState.unconfigured])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @sync_block _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : nb = ba
      · subst hbb
        exact Or.inl (by simp [Function.update_self, hb])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | mb_init he hb => exact Or.inl rfl
    | mb_arrive he hb => exact Or.inl rfl
    | mb_wait_block he hb => exact Or.inl rfl
    | mb_wait_pass he hb hne => exact Or.inl rfl
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    by_cases hbb : ba = nb
    · subst hbb
      refine Or.inr (Or.inr ?_)
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb, NamedBarrierState.isFull, hfull,
        Function.update_self]
    · exact Or.inl (by simp only [Function.update_of_ne (Ne.symm hbb)])
  | @mb_recycle s₀ Tc sb I A na ph hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact Or.inl rfl
  | done hdone hnofull hmbnofull =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact Or.inl rfl
  | error hbar hmbar hth =>
    simp [WeftCommon.Config.state?] at hs'

/-- Classify a step's effect on mbarrier `sb`'s arrival count: unchanged, an
`arrive_mb sb` execution (head dropped), or a recycle of `sb`. -/
theorem arrived_step_mb {C C' : Config} (hstep : CTAStep C C') {sb : SharedBarrier}
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s') :
    (s'.BM sb).arrived = (s.BM sb).arrived ∨
    (∃ (i : ThreadId) (rest : Prog),
      C.progOf i = Cmd.arrive_mb sb :: rest ∧ C'.progOf i = rest) ∨
    stepRecyclesBarrier (.inr sb) C C' = true := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hmbar hth =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPi] at hth
    cases hth with
    | read_noop => exact Or.inl rfl
    | write_noop => exact Or.inl rfl
    | arrive_configure he hb => exact Or.inl rfl
    | arrive_register he hb hpos hlt => exact Or.inl rfl
    | sync_configure he hb => exact Or.inl rfl
    | sync_block he hb hpos hlt => exact Or.inl rfl
    | @mb_init _ _ ba na _ he hb =>
      by_cases hbb : sb = ba
      · subst hbb
        exact Or.inl (by
          simp [Function.update_self, hb, MBarrierState.uninitialized])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @mb_arrive _ _ ba _ I A na ph he hb =>
      by_cases hbb : sb = ba
      · subst hbb
        refine Or.inr (Or.inl ⟨t, P', hPi, ?_⟩)
        simp [WeftCommon.Config.progOf, WeftCommon.CTA.set, Function.update_self]
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | @mb_wait_block _ _ ba ph _ I A na he hb =>
      by_cases hbb : sb = ba
      · subst hbb
        exact Or.inl (by simp [Function.update_self, hb])
      · exact Or.inl (by simp only [Function.update_of_ne hbb])
    | mb_wait_pass he hb hne => exact Or.inl rfl
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact Or.inl rfl
  | @mb_recycle s₀ Tc sb' I A na ph hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    by_cases hbb : sb' = sb
    · subst hbb
      refine Or.inr (Or.inr ?_)
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb, MBarrierState.isFull, hfull,
        Function.update_self]
    · exact Or.inl (by simp only [Function.update_of_ne (Ne.symm hbb)])
  | done hdone hnofull hmbnofull =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact Or.inl rfl
  | error hbar hmbar hth =>
    simp [WeftCommon.Config.state?] at hs'

/-- **Decode an `arrive_nb` execution.** A step that drops a thread's
`arrive_nb nb n'` head is an `interleave` running that arrive; the rule premise
ties `n'` to the barrier — it either configures `nb` or registers into a
count-`n'` state — and afterwards `nb` is configured with count `n'` and one
more arrival. -/
theorem arrive_nb_exec_decode {C C' : Config} (hstep : CTAStep C C') {i : ThreadId}
    {nb : NamedBarrier} {n' : ℕ+} {rest : Prog}
    (hC : C.progOf i = Cmd.arrive_nb nb n' :: rest) (hC' : C'.progOf i = rest) :
    ∃ s s', C.state? = some s ∧ C'.state? = some s' ∧
      (s.BN nb = NamedBarrierState.unconfigured ∨ (s.BN nb).count = some n') ∧
      (s'.BN nb).count = some n' ∧ (s'.BN nb).arrived = (s.BN nb).arrived + 1 := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hmbar hth =>
    by_cases hti : t = i
    · subst hti
      obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
      rw [hPi] at hth
      have hC0 : Pi = Cmd.arrive_nb nb n' :: rest := by rw [← hPi]; exact hC
      subst hC0
      cases hth with
      | arrive_configure he hb =>
        refine ⟨s₀, _, rfl, rfl, Or.inl hb, ?_, ?_⟩
        · simp [Function.update_self]
        · rw [hb]
          simp [Function.update_self, NamedBarrierState.unconfigured]
      | arrive_register he hb hpos hlt =>
        refine ⟨s₀, _, rfl, rfl, Or.inr (by rw [hb]), ?_, ?_⟩
        · simp [Function.update_self]
        · rw [hb]
          simp [Function.update_self]
    · exfalso
      have hsame : (Tc.set t ht P').prog i = Tc.prog i := by
        simp [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hti)]
      have hc : Tc.prog i = Cmd.arrive_nb nb n' :: rest := hC
      have hc' : Tc.prog i = rest := by rw [← hsame]; exact hC'
      rw [hc'] at hc
      have hlen := congrArg List.length hc
      simp at hlen
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    exfalso
    have hc : Tc.prog i = Cmd.arrive_nb nb n' :: rest := hC
    by_cases hi : i ∈ I
    · have hhd := hpark i hi
      rw [hc] at hhd
      simp at hhd
    · have hsame : (Tc.wake I).prog i = Tc.prog i := by
        simp [WeftCommon.CTA.wake, if_neg hi]
      have hc' : (Tc.wake I).prog i = rest := hC'
      rw [hsame, hc] at hc'
      have hlen := congrArg List.length hc'
      simp at hlen
  | @mb_recycle s₀ Tc sb I A na ph hb hfull hpark =>
    exfalso
    have hc : Tc.prog i = Cmd.arrive_nb nb n' :: rest := hC
    by_cases hi : i ∈ I
    · have hhd := hpark i hi
      rw [hc] at hhd
      simp at hhd
    · have hsame : (Tc.wake I).prog i = Tc.prog i := by
        simp [WeftCommon.CTA.wake, if_neg hi]
      have hc' : (Tc.wake I).prog i = rest := hC'
      rw [hsame, hc] at hc'
      have hlen := congrArg List.length hc'
      simp at hlen
  | @done s₀ Tc hdone hnofull hmbnofull =>
    exfalso
    have hc : Tc.prog i = Cmd.arrive_nb nb n' :: rest := hC
    have hnil : Tc.prog i = [] := by
      by_cases hi : i ∈ Tc.ids
      · exact hdone i hi
      · exact Tc.nil_outside_ids i hi
    rw [hnil] at hc
    simp at hc
  | @error s₀ Tc t P' hbar hmbar hth =>
    exfalso
    have hc : Tc.prog i = Cmd.arrive_nb nb n' :: rest := hC
    have hc' : Tc.prog i = rest := hC'
    rw [hc'] at hc
    have hlen := congrArg List.length hc
    simp at hlen

/-- A step preserves a configured named-barrier count unless it recycles the
barrier. -/
theorem count_step_nb {C C' : Config} (hstep : CTAStep C C') {nb : NamedBarrier}
    {n : ℕ+} {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s')
    (hn : (s.BN nb).count = some n)
    (hnorec : stepRecyclesBarrier (.inl nb) C C' = false) :
    (s'.BN nb).count = some n := by
  cases hstep with
  | @interleave s₀ sn Tc t P' ht hbar hmbar hth =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    obtain ⟨Pi, hPi⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPi] at hth
    cases hth with
    | read_noop => exact hn
    | write_noop => exact hn
    | @arrive_configure _ _ ba na _ he hb =>
      by_cases hbb : nb = ba
      · subst hbb; rw [hb] at hn; simp [NamedBarrierState.unconfigured] at hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @arrive_register _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : nb = ba
      · subst hbb
        rw [hb] at hn
        simp only [Function.update_self]
        simpa using hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @sync_configure _ _ ba na _ he hb =>
      by_cases hbb : nb = ba
      · subst hbb; rw [hb] at hn; simp [NamedBarrierState.unconfigured] at hn
      · simpa only [Function.update_of_ne hbb] using hn
    | @sync_block _ _ ba na _ I A he hb hpos hlt =>
      by_cases hbb : nb = ba
      · subst hbb
        rw [hb] at hn
        simp only [Function.update_self]
        simpa using hn
      · simpa only [Function.update_of_ne hbb] using hn
    | mb_init he hb => exact hn
    | mb_arrive he hb => exact hn
    | mb_wait_block he hb => exact hn
    | mb_wait_pass he hb hne => exact hn
  | @recycle s₀ Tc ba I A na hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    by_cases hbb : ba = nb
    · subst hbb
      exfalso
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb, NamedBarrierState.isFull, hfull,
        Function.update_self] at hnorec
    · simpa only [Function.update_of_ne (Ne.symm hbb)] using hn
  | @mb_recycle s₀ Tc sb I A na ph hb hfull hpark =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact hn
  | done hdone hnofull hmbnofull =>
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs hs'
    subst hs; subst hs'
    exact hn
  | error hbar hmbar hth =>
    simp [WeftCommon.Config.state?] at hs'

/-- **Count persistence** (named). Over a recycle-free stretch of the trace
(equal `recycleCount` at both ends), a configured count survives. -/
theorem count_persists_nb {τ : List Config} (hchain : List.IsChain CTAStep τ)
    {nb : NamedBarrier} {n : ℕ+} :
    ∀ (k j : Nat), j ≤ k → recycleCount (.inl nb) τ j = recycleCount (.inl nb) τ k →
    ∀ {C : Config} {s : State}, τ[j]? = some C → C.state? = some s →
      (s.BN nb).count = some n →
    ∀ {C' : Config} {s' : State}, τ[k]? = some C' → C'.state? = some s' →
      (s'.BN nb).count = some n := by
  intro k
  induction k with
  | zero =>
    intro j hjk _ C s hC hs hn C' s' hC' hs'
    obtain rfl : j = 0 := by omega
    rw [hC] at hC'
    obtain rfl := Option.some.inj hC'
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    exact hn
  | succ k ih =>
    intro j hjk hrc C s hC hs hn C' s' hC' hs'
    by_cases hje : j = k + 1
    · subst hje
      rw [hC] at hC'
      obtain rfl := Option.some.inj hC'
      rw [hs] at hs'
      obtain rfl := Option.some.inj hs'
      exact hn
    · have hjk' : j ≤ k := by omega
      have hklt : k < τ.length := by
        have := (List.getElem?_eq_some_iff.mp hC').1
        omega
      have hCk : τ[k]? = some τ[k] := List.getElem?_eq_getElem hklt
      have hstepk := chain_step hchain hCk hC'
      obtain ⟨sk, hsk⟩ : ∃ sk, (τ[k]).state? = some sk := by
        rcases hkc : τ[k] with ⟨s₁, T₁⟩ | s₁ | T₁
        · exact ⟨s₁, rfl⟩
        · rw [hkc] at hstepk; cases hstepk
        · rw [hkc] at hstepk; cases hstepk
      have hm1 := recycleCount_mono (.inl nb) τ hjk'
      have hm2 := recycleCount_mono (.inl nb) τ (show k ≤ k + 1 by omega)
      have hrcjk : recycleCount (.inl nb) τ j = recycleCount (.inl nb) τ k := by omega
      have hnorec : stepRecyclesBarrier (.inl nb) τ[k] C' = false := by
        by_contra hrec
        rw [Bool.not_eq_false] at hrec
        have := recycleCount_succ_of_recycle (.inl nb) τ hCk hC' hrec
        omega
      exact count_step_nb hstepk hsk hs' (ih j hjk' hrcjk hC hs hn hCk hsk) hnorec

/-- Kind purity: an `.inr sb` fiber contains only `arrive_mb sb`s — the only
registrant on a shared barrier. -/
theorem genFiber_mb_arrive {T : CTA} {τ : List Config} {sb : SharedBarrier} {g : ℤ}
    {η : ProgPoint} (hη : η ∈ genFiber T τ (.inr sb) g) :
    T.cmdAt η = some (.arrive_mb sb) := by
  obtain ⟨-, hregmem⟩ := mem_genFiber.mp hη
  obtain ⟨c, hcm, hisreg, hbar, -⟩ := registrantGen_some hregmem
  cases c with
  | arrive_nb nb n => simp [Cmd.barrier?] at hbar
  | sync_nb nb n => simp [Cmd.barrier?] at hbar
  | arrive_mb sb' =>
    simp only [Cmd.barrier?, Option.some.injEq, Sum.inr.injEq] at hbar
    rw [hcm, hbar]
  | read l => simp [Cmd.isRegistrant] at hisreg
  | write l => simp [Cmd.isRegistrant] at hisreg
  | init_mb sb' n => simp [Cmd.isRegistrant] at hisreg
  | wait_mb sb' ph => simp [Cmd.isRegistrant] at hisreg

/-- Kind purity: an `.inl nb` fiber member is an `arrive_nb nb _` or a
`sync_nb nb _`. -/
theorem genFiber_nb_cases {T : CTA} {τ : List Config} {nb : NamedBarrier} {g : ℤ}
    {η : ProgPoint} (hη : η ∈ genFiber T τ (.inl nb) g) :
    (∃ n : ℕ+, T.cmdAt η = some (.arrive_nb nb n)) ∨
    (∃ n : ℕ+, T.cmdAt η = some (.sync_nb nb n)) := by
  obtain ⟨-, hregmem⟩ := mem_genFiber.mp hη
  obtain ⟨c, hcm, hisreg, hbar, -⟩ := registrantGen_some hregmem
  cases c with
  | arrive_nb nb' n =>
    simp only [Cmd.barrier?, Option.some.injEq, Sum.inl.injEq] at hbar
    exact Or.inl ⟨n, by rw [hcm, hbar]⟩
  | sync_nb nb' n =>
    simp only [Cmd.barrier?, Option.some.injEq, Sum.inl.injEq] at hbar
    exact Or.inr ⟨n, by rw [hcm, hbar]⟩
  | arrive_mb sb' => simp [Cmd.barrier?] at hbar
  | read l => simp [Cmd.isRegistrant] at hisreg
  | write l => simp [Cmd.isRegistrant] at hisreg
  | init_mb sb' n => simp [Cmd.isRegistrant] at hisreg
  | wait_mb sb' ph => simp [Cmd.isRegistrant] at hisreg

/-- **The partial round is `sync`-free.** The fiber of the round after the last
completed one (ops the reference trace ran in a round that never recycled)
contains no `sync_nb`: a `sync_nb`'s execution step *is* a recycle of its
barrier, which would push the recycle count past the total. -/
theorem genFiber_partial_no_sync {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {η : ProgPoint}
    (hη : η ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)) :
    ∀ n : ℕ+, T.cmdAt η ≠ some (.sync_nb nb n) := by
  intro n hcmd
  obtain ⟨c, m, -, -, -, hm, -, hm1, hmlt, hgm⟩ := genFiber_time_data hτ hη
  have hcmd' : η.cmd (Config.run State.initial T) = some (Cmd.sync_nb nb n) := hcmd
  obtain ⟨C, C', hC, hC', hrec⟩ := sync_time_recycles hm hcmd'
  have hC'' : τ[m - 1 + 1]? = some C' := by
    rw [show m - 1 + 1 = m by omega]; exact hC'
  have hsucc := recycleCount_succ_of_recycle (.inl nb) τ hC hC'' hrec
  have hmono : recycleCount (.inl nb) τ (m - 1 + 1) ≤
      recycleCount (.inl nb) τ (τ.length - 1) :=
    recycleCount_mono (.inl nb) τ (by omega)
  omega

/-- An `arrive_nb` member of a fiber leaves `nb` configured with *its own
parameter* right after its execution step: at index `m` (its time), the count is
`some na`, and the recycle count strictly before it is `g`. The seed of every
parameter-agreement argument. -/
theorem genFiber_arrive_post_count {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {g : ℕ} {η : ProgPoint}
    (hη : η ∈ genFiber T τ (.inl nb) (g : ℤ))
    {na : ℕ+} (hcm : T.cmdAt η = some (.arrive_nb nb na)) :
    ∃ (m : Nat) (C' : Config) (s' : State),
      1 ≤ m ∧ m < τ.length ∧ pointTime T τ η = some m ∧ τ[m]? = some C' ∧
      C'.state? = some s' ∧
      (s'.BN nb).count = some na ∧ recycleCount (.inl nb) τ (m - 1) = g := by
  obtain ⟨c, m, -, -, -, hm, hptm, hm1, hmlt, hgm⟩ := genFiber_time_data hτ hη
  obtain ⟨-, -, j, D, D', hjm, hD, hD', hDdrop, hD'drop⟩ := hm
  subst hjm
  have hcmg : ((Config.run State.initial T).progOf η.thread)[η.idx]? =
      some (Cmd.arrive_nb nb na) := hcm
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcmg
  have hDcons : D.progOf η.thread = Cmd.arrive_nb nb na ::
      ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := by
    rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
  have hD'rest : D'.progOf η.thread =
      ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := hD'drop
  have hstepD := chain_step hτ.1.1.subtrace hD hD'
  obtain ⟨s₁, s₂, hs₁, hs₂, hpre, hpost, hinc⟩ :=
    arrive_nb_exec_decode hstepD hDcons hD'rest
  exact ⟨j + 1, D', s₂, by omega, hmlt, hptm, hD', hs₂, hpost, hgm⟩

/-- **The round data of a completed named generation.** For a round `g` that
completes (`g + 1 ≤` the total recycles of `nb`), locate the recycle that closes
it: at step `p` the barrier holds a full round `⟨I, A, some n⟩` whose parked
threads sit at `sync_nb nb n` heads, the recycle wakes them — and, the
fiber-parameter fact, every member of `F_g(nb)` carries the count `n` (`sync`s
read it off `hpark`; `arrive`s configure/match it at their own step, and it
persists through the recycle-free window to `p`). -/
theorem genFiber_round_data {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {g : ℕ}
    (hcomplete : g + 1 ≤ recycleCount (.inl nb) τ (τ.length - 1)) :
    ∃ (p : Nat) (s : State) (Tc : CTA) (I : List ThreadId) (A : Nat) (n : ℕ+),
      recycleCount (.inl nb) τ p = g ∧ recycleCount (.inl nb) τ (p + 1) = g + 1 ∧
      τ[p]? = some (Config.run s Tc) ∧ s.BN nb = ⟨I, A, some n⟩ ∧
      I.length + A = (n : ℕ) ∧
      (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.sync_nb nb n)) ∧
      τ[p + 1]? = some (Config.run
        ({ s with E := updateMapOn s.E I true,
                  BN := Function.update s.BN nb NamedBarrierState.unconfigured })
        (Tc.wake I)) ∧
      (∀ η ∈ genFiber T τ (.inl nb) (g : ℤ), (T.cmdAt η).bind Cmd.count? = some n) ∧
      (∀ η ∈ genFiber T τ (.inl nb) (g : ℤ), ∀ nn : ℕ+,
        T.cmdAt η = some (.sync_nb nb nn) →
        η.thread ∈ I ∧ Tc.prog η.thread = (T.prog η.thread).drop η.idx) ∧
      (∀ i ∈ I, ∃ η ∈ genFiber T τ (.inl nb) (g : ℤ), η.thread = i ∧
        ∃ nn : ℕ+, T.cmdAt η = some (.sync_nb nb nn)) := by
  obtain ⟨p, hpM, hrc1, hrc2⟩ := recycleCount_hits (.inl nb) τ
    (show 1 ≤ g + 1 by omega) hcomplete
  simp only [Nat.add_sub_cancel] at hrc1
  obtain ⟨C, C', hC, hC', hrecb⟩ := recycle_step_of_count_lt
    (b := .inl nb) (τ := τ) (p := p) (by omega)
  have hstep := chain_step hτ.1.1.subtrace hC hC'
  obtain ⟨s, Tc, I, A, n, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
    stepRecyclesBarrier_elim_nb hstep hrecb
  subst hCeq; subst hC'eq
  -- sync members are parked in `I`, control at the member
  have hsync_data : ∀ η ∈ genFiber T τ (.inl nb) (g : ℤ), ∀ nn : ℕ+,
      T.cmdAt η = some (.sync_nb nb nn) →
      η.thread ∈ I ∧ Tc.prog η.thread = (T.prog η.thread).drop η.idx := by
    intro η hη nn hcmd
    obtain ⟨c, m, -, -, -, hm, -, hm1, hmlt, hgm⟩ := genFiber_time_data hτ hη
    have hcmd' : η.cmd (Config.run State.initial T) = some (Cmd.sync_nb nb nn) := hcmd
    obtain ⟨E, E', hE, hE', hrecE⟩ := sync_time_recycles hm hcmd'
    have hEsucc : recycleCount (.inl nb) τ (m - 1 + 1) =
        recycleCount (.inl nb) τ (m - 1) + 1 := by
      refine recycleCount_succ_of_recycle (.inl nb) τ hE ?_ hrecE
      rw [show m - 1 + 1 = m by omega]; exact hE'
    have hup : m - 1 = p := by
      rcases Nat.lt_trichotomy (m - 1) p with hlt | heq | hgt
      · exfalso
        have := recycleCount_mono (.inl nb) τ (show m - 1 + 1 ≤ p by omega)
        omega
      · exact heq
      · exfalso
        have := recycleCount_mono (.inl nb) τ (show p + 1 ≤ m - 1 by omega)
        omega
    obtain ⟨-, -, j', D, D', hj'm, hD, hD', hDdrop, hD'drop⟩ := hm
    have hj'p : j' = p := by omega
    subst hj'p
    have hDeq : D = Config.run s Tc := by
      rw [hD] at hC
      exact Option.some.inj hC
    subst hDeq
    have hD'eq : D' = Config.run
        ({ s with E := updateMapOn s.E I true,
                  BN := Function.update s.BN nb NamedBarrierState.unconfigured })
        (Tc.wake I) := by
      rw [hD'] at hC'
      exact Option.some.inj hC'
    subst hD'eq
    have htI : η.thread ∈ I := by
      by_contra htn
      have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
        simp [WeftCommon.CTA.wake, if_neg htn]
      have h1 : Tc.prog η.thread =
          ((Config.run State.initial T).progOf η.thread).drop η.idx := hDdrop
      have h2 : (Tc.wake I).prog η.thread =
          ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := hD'drop
      rw [hsame, h1] at h2
      have hlen := congrArg List.length h2
      simp only [List.length_drop] at hlen
      have hidx0 : η.idx < ((Config.run State.initial T).progOf η.thread).length := by
        have hmem := (mem_genFiber.mp hη).1
        exact ((mem_progPoints_iff T η).mp hmem).2
      omega
    exact ⟨htI, hDdrop⟩
  -- every parked thread contributes a sync member
  have hsurj : ∀ i ∈ I, ∃ η ∈ genFiber T τ (.inl nb) (g : ℤ), η.thread = i ∧
      ∃ nn : ℕ+, T.cmdAt η = some (.sync_nb nb nn) := by
    intro i hi
    have hhead := hpark i hi
    obtain ⟨rest, hrest⟩ : ∃ rest, Tc.prog i = Cmd.sync_nb nb n :: rest := by
      cases hTt : Tc.prog i with
      | nil => rw [hTt] at hhead; simp at hhead
      | cons a l =>
        rw [hTt] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨l, by rw [hhead]⟩
    have hCprog : (Config.run s Tc).progOf i = Cmd.sync_nb nb n :: rest := hrest
    have hC'prog : (Config.run
        ({ s with E := updateMapOn s.E I true,
                  BN := Function.update s.BN nb NamedBarrierState.unconfigured })
        (Tc.wake I)).progOf i = rest := by
      simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake, if_pos hi, hrest,
        List.tail_cons]
    obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hC hC' hCprog hC'prog
    refine ⟨_, mem_genFiber_of_time hcmd rfl rfl htime (by simpa using hrc1),
      rfl, n, hcmd⟩
  refine ⟨p, s, Tc, I, A, n, hrc1, hrc2, hC, hbst, hfull, hpark, hC', ?_,
    hsync_data, hsurj⟩
  intro η hη
  rcases genFiber_nb_cases hη with ⟨na, hcmd⟩ | ⟨na, hcmd⟩
  · -- an `arrive_nb`: its post-step count persists through the window to `p`
    obtain ⟨m, D', s₂, hm1, hmlen, -, hD', hs₂, hpost, hrcm⟩ :=
      genFiber_arrive_post_count hτ hη hcmd
    -- `m ≠ p + 1`: the post-arrive state is configured, the post-recycle one is not
    have hmp : m ≠ p + 1 := by
      intro hmeq
      subst hmeq
      rw [hD'] at hC'
      obtain rfl := Option.some.inj hC'
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs₂
      subst hs₂
      simp [Function.update_self, NamedBarrierState.unconfigured] at hpost
    -- `m ≤ p`: a later registration would sit past the round's recycle
    have hmle : m ≤ p := by
      by_contra hcon
      have hple : p + 1 ≤ m - 1 := by omega
      have := recycleCount_mono (.inl nb) τ hple
      omega
    -- the window `[m, p]` is recycle-free: persist the count to the recycle
    have hrcmp : recycleCount (.inl nb) τ m = recycleCount (.inl nb) τ p := by
      have h1 := recycleCount_mono (.inl nb) τ (show m - 1 ≤ m by omega)
      have h2 := recycleCount_mono (.inl nb) τ hmle
      omega
    have hcount := count_persists_nb hτ.1.1.subtrace p m hmle hrcmp hD' hs₂ hpost hC rfl
    rw [hbst] at hcount
    rw [hcmd]
    simpa [Cmd.count?] using hcount.symm
  · -- a `sync_nb`: parked at the recycle, its head carries the round count
    obtain ⟨htI, hpt⟩ := hsync_data η hη na hcmd
    have hidx : η.idx < (T.prog η.thread).length := by
      have hmem := (mem_genFiber.mp hη).1
      exact ((mem_progPoints_iff T η).mp hmem).2
    have hhd := hpark η.thread htI
    rw [hpt, List.drop_eq_getElem_cons hidx, List.head?_cons] at hhd
    have hcm2 : (T.prog η.thread)[η.idx]? = some (Cmd.sync_nb nb na) := hcmd
    obtain ⟨hlt2, hget⟩ := List.getElem?_eq_some_iff.mp hcm2
    rw [hget] at hhd
    simp only [Option.some.injEq, Cmd.sync_nb.injEq] at hhd
    rw [hcmd]
    simp [Cmd.count?, hhd.2]

/-- The arrive commands — the head drops that bump an arrival counter
(`arrive_nb`/`arrive_mb`). -/
def Cmd.isArrive : Cmd → Bool
  | .arrive_nb _ _ => true
  | .arrive_mb _ => true
  | _ => false

/-- Arrives are registrants. -/
theorem Cmd.isRegistrant_of_isArrive {c : Cmd} (h : c.isArrive = true) :
    c.isRegistrant = true := by
  cases c <;> first | rfl | simp [Cmd.isArrive] at h

/-- The arrival counter of barrier `b` — of either kind — in state `s`. Lets
the window/census arguments run once over the sum instead of per kind. -/
def State.arrivedAt (s : State) : NamedBarrier ⊕ SharedBarrier → ℕ
  | .inl nb => (s.BN nb).arrived
  | .inr sb => (s.BM sb).arrived

/-- Classify a step's effect on `b`'s arrival counter (either kind): unchanged,
an arrive on `b` executed (head dropped), or a recycle of `b`. -/
theorem arrivedAt_step {C C' : Config} (hstep : CTAStep C C')
    {b : NamedBarrier ⊕ SharedBarrier}
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s') :
    s'.arrivedAt b = s.arrivedAt b ∨
    (∃ (i : ThreadId) (c : Cmd) (rest : Prog), c.isArrive = true ∧
      c.barrier? = some b ∧ C.progOf i = c :: rest ∧ C'.progOf i = rest) ∨
    stepRecyclesBarrier b C C' = true := by
  cases b with
  | inl nb =>
    rcases arrived_step_nb hstep hs hs' with heq | ⟨i, n', rest, h1, h2⟩ | hrec
    · exact Or.inl heq
    · exact Or.inr (Or.inl ⟨i, .arrive_nb nb n', rest, rfl, rfl, h1, h2⟩)
    · exact Or.inr (Or.inr hrec)
  | inr sb =>
    rcases arrived_step_mb hstep hs hs' with heq | ⟨i, rest, h1, h2⟩ | hrec
    · exact Or.inl heq
    · exact Or.inr (Or.inl ⟨i, .arrive_mb sb, rest, rfl, rfl, h1, h2⟩)
    · exact Or.inr (Or.inr hrec)

/-- Executing an arrive on `b` bumps `b`'s arrival counter by exactly one. -/
theorem arrive_exec_arrivedAt {C C' : Config} (hstep : CTAStep C C') {i : ThreadId}
    {c : Cmd} (hcarr : c.isArrive = true) {b : NamedBarrier ⊕ SharedBarrier}
    (hcbar : c.barrier? = some b) {rest : Prog}
    (hC : C.progOf i = c :: rest) (hC' : C'.progOf i = rest)
    {s s' : State} (hs : C.state? = some s) (hs' : C'.state? = some s') :
    s'.arrivedAt b = s.arrivedAt b + 1 := by
  cases c with
  | arrive_nb nb n' =>
    simp only [Cmd.barrier?, Option.some.injEq] at hcbar
    subst hcbar
    obtain ⟨s₁, s₂, hs₁, hs₂, -, -, hinc⟩ := arrive_nb_exec_decode hstep hC hC'
    rw [hs] at hs₁
    obtain rfl := Option.some.inj hs₁
    rw [hs'] at hs₂
    obtain rfl := Option.some.inj hs₂
    exact hinc
  | arrive_mb sb =>
    simp only [Cmd.barrier?, Option.some.injEq] at hcbar
    subst hcbar
    exact arrive_mb_drop_arrived hstep hC hC' hs hs'
  | read l => simp [Cmd.isArrive] at hcarr
  | write l => simp [Cmd.isArrive] at hcarr
  | sync_nb nb n => simp [Cmd.isArrive] at hcarr
  | wait_mb sb ph => simp [Cmd.isArrive] at hcarr
  | init_mb sb n => simp [Cmd.isArrive] at hcarr

/-- Two head drops at one step share a thread when (at least) one of the heads
is an arrive: only a single `interleave` thread advances past an arrive (the
recycles drop only parked `sync_nb`/`wait_mb`s, and every non-woken program is
untouched). -/
theorem arrive_head_drop_same_thread {C C' : Config} (hstep : CTAStep C C')
    {t t' : ThreadId} {c c' : Cmd} (hc : c.isArrive = true) {r r' : Prog}
    (h1 : C.progOf t = c :: r) (h1' : C'.progOf t = r)
    (h2 : C.progOf t' = c' :: r') (h2' : C'.progOf t' = r') : t = t' := by
  cases hstep with
  | @interleave s s₁ Tc i P' hi hbar hmbar hth =>
    simp only [WeftCommon.Config.progOf] at h1 h1' h2 h2'
    by_cases ht : t = i
    · by_cases ht' : t' = i
      · rw [ht, ht']
      · exfalso
        simp only [WeftCommon.CTA.set, Function.update_of_ne ht'] at h2'
        rw [h2] at h2'
        simp at h2'
    · exfalso
      simp only [WeftCommon.CTA.set, Function.update_of_ne ht] at h1'
      rw [h1] at h1'
      simp at h1'
  | @recycle s Tc nb₀ I A n₀ hb hfull hpark =>
    exfalso
    simp only [WeftCommon.Config.progOf] at h1 h1'
    by_cases h : t ∈ I
    · have hpk := hpark t h
      rw [h1] at hpk
      simp only [List.head?_cons, Option.some.injEq] at hpk
      rw [hpk] at hc
      simp [Cmd.isArrive] at hc
    · simp only [WeftCommon.CTA.wake, if_neg h] at h1'
      rw [h1] at h1'
      simp at h1'
  | @mb_recycle s Tc sb₀ I A n₀ ph hb hfull hpark =>
    exfalso
    simp only [WeftCommon.Config.progOf] at h1 h1'
    by_cases h : t ∈ I
    · have hpk := hpark t h
      rw [h1] at hpk
      simp only [List.head?_cons, Option.some.injEq] at hpk
      rw [hpk] at hc
      simp [Cmd.isArrive] at hc
    · simp only [WeftCommon.CTA.wake, if_neg h] at h1'
      rw [h1] at h1'
      simp at h1'
  | @done s Tc hdone _ _ =>
    exfalso
    simp only [WeftCommon.Config.progOf] at h1
    have hnil : Tc.prog t = [] := by
      by_cases hti : t ∈ Tc.ids
      · exact hdone t hti
      · exact Tc.nil_outside_ids t hti
    rw [hnil] at h1
    simp at h1
  | @error s Tc i P' _ _ hth =>
    exfalso
    simp only [WeftCommon.Config.progOf] at h1 h1'
    rw [h1] at h1'
    simp at h1'

/-- A recycling step exposes states on both sides. -/
theorem exists_state_of_stepRecycles {b : NamedBarrier ⊕ SharedBarrier}
    {C C' : Config} (hrec : stepRecyclesBarrier b C C' = true) :
    (∃ s, C.state? = some s) ∧ ∃ s', C'.state? = some s' := by
  cases hs : C.state? with
  | none => simp [stepRecyclesBarrier, hs] at hrec
  | some s =>
    cases hs' : C'.state? with
    | none => simp [stepRecyclesBarrier, hs, hs'] at hrec
    | some s' => exact ⟨⟨s, rfl⟩, ⟨s', rfl⟩⟩

/-- Right after a recycle of `b`, `b`'s arrival counter is zero (the named reset
clears it to the unconfigured state; the mbarrier reset clears it in place). -/
theorem arrivedAt_zero_after_recycle {C C' : Config} (hstep : CTAStep C C')
    {b : NamedBarrier ⊕ SharedBarrier} (hrec : stepRecyclesBarrier b C C' = true)
    {s' : State} (hs' : C'.state? = some s') : s'.arrivedAt b = 0 := by
  cases b with
  | inl nb =>
    obtain ⟨s, Tc, I, A, n, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
      stepRecyclesBarrier_elim_nb hstep hrec
    subst hC'eq
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'
    subst hs'
    simp [State.arrivedAt, Function.update_self, NamedBarrierState.unconfigured]
  | inr sb =>
    obtain ⟨s, Tc, I, A, n, ph, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
      stepRecyclesBarrier_elim_mb hstep hrec
    subst hC'eq
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'
    subst hs'
    simp [State.arrivedAt, Function.update_self]

/-- **Trace one arrival.** If `b`'s arrival counter is zero at `w` and positive
at `p ≥ w`, with `g` recycles of `b` done at both ends, some arrive on `b`
executes strictly inside the window — a fiber member of round `g`. -/
theorem genFiber_exists_of_arrive_window {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℕ} {w p : Nat} (hwp : w ≤ p)
    {Cw : Config} {sw : State} (hCw : τ[w]? = some Cw) (hsw : Cw.state? = some sw)
    (hw0 : sw.arrivedAt b = 0)
    {Cp : Config} {sp : State} (hCp : τ[p]? = some Cp) (hsp : Cp.state? = some sp)
    (hppos : 0 < sp.arrivedAt b)
    (hwrc : recycleCount b τ w = g) (hprc : recycleCount b τ p = g) :
    ∃ η', η' ∈ genFiber T τ b (g : ℤ) := by
  set f : Nat → Nat := fun l =>
    (((τ[l]?).bind WeftCommon.Config.state?).map fun st => st.arrivedAt b).getD 0
    with hf
  have hfw : f w = 0 := by simp [hf, hCw, hsw, hw0]
  have hfp : f p = sp.arrivedAt b := by simp [hf, hCp, hsp]
  obtain ⟨j, hjw, hjp, hjlt⟩ := exists_step_increase f p w hwp (by omega)
  have hplt : p < τ.length := (List.getElem?_eq_some_iff.mp hCp).1
  have hCj : τ[j]? = some τ[j] := List.getElem?_eq_getElem (by omega)
  have hCj1 : τ[j + 1]? = some τ[j + 1] := List.getElem?_eq_getElem (by omega)
  have hstepj := chain_step hτ.1.1.subtrace hCj hCj1
  obtain ⟨sj, hsj⟩ : ∃ sj, (τ[j]).state? = some sj := by
    rcases hj : τ[j] with ⟨s₁, T₁⟩ | s₁ | T₁
    · exact ⟨s₁, rfl⟩
    · rw [hj] at hstepj; cases hstepj
    · rw [hj] at hstepj; cases hstepj
  obtain ⟨sj1, hsj1⟩ : ∃ sj1, (τ[j + 1]).state? = some sj1 := by
    rcases hj1 : τ[j + 1] with ⟨s₁, T₁⟩ | s₁ | T₁
    · exact ⟨s₁, rfl⟩
    · exact ⟨s₁, rfl⟩
    · exfalso
      have hzero : f (j + 1) = 0 := by
        simp [hf, hCj1, hj1, WeftCommon.Config.state?]
      omega
  have hlt' : sj.arrivedAt b < sj1.arrivedAt b := by
    have h1 : f j = sj.arrivedAt b := by simp [hf, hCj, hsj]
    have h2 : f (j + 1) = sj1.arrivedAt b := by simp [hf, hCj1, hsj1]
    omega
  rcases arrivedAt_step (b := b) hstepj hsj hsj1 with
    heq | ⟨i, c, rest, hcarr, hcbar, hCi, hC'i⟩ | hrecj
  · exfalso; omega
  · obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hCj hCj1 hCi hC'i
    refine ⟨_, mem_genFiber_of_time hcmd (Cmd.isRegistrant_of_isArrive hcarr)
      hcbar htime ?_⟩
    have hm1 := recycleCount_mono b τ hjw
    have hm2 := recycleCount_mono b τ (Nat.le_of_lt hjp)
    simp only [Nat.add_sub_cancel]
    omega
  · exfalso
    have hsucc := recycleCount_succ_of_recycle b τ hCj hCj1 hrecj
    have hm1 := recycleCount_mono b τ hjw
    have hm2 := recycleCount_mono b τ (show j + 1 ≤ p by omega)
    omega

/-- **Fiber parameter agreement.** Any two members of an `.inl nb` fiber of the
successful reference trace carry the same count parameter: all of `F_g(nb)`
registered into `τ`'s round `g` of `nb`, whose configured count every
registration matched without error. Completed rounds read the common count off
`genFiber_round_data`; the partial round is all-`arrive`s, each of whose
parameters persists to the final configuration. -/
theorem genFiber_count_eq {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {g : ℕ} {η₁ η₂ : ProgPoint}
    (h₁ : η₁ ∈ genFiber T τ (.inl nb) (g : ℤ))
    (h₂ : η₂ ∈ genFiber T τ (.inl nb) (g : ℤ)) :
    (T.cmdAt η₁).bind Cmd.count? = (T.cmdAt η₂).bind Cmd.count? := by
  by_cases hcomp : g + 1 ≤ recycleCount (.inl nb) τ (τ.length - 1)
  · obtain ⟨p, s, Tc, I, A, n, -, -, -, -, -, -, -, hall, -, -⟩ :=
      genFiber_round_data hτ hcomp
    rw [hall η₁ h₁, hall η₂ h₂]
  · obtain ⟨sd, hdone⟩ := hτ.2
    have hR : g = recycleCount (.inl nb) τ (τ.length - 1) := by
      obtain ⟨c, m, -, -, -, hm, -, hm1, hmlt, hgm⟩ := genFiber_time_data hτ h₁
      have := recycleCount_mono (.inl nb) τ (show m - 1 ≤ τ.length - 1 by omega)
      omega
    have hkey : ∀ η' ∈ genFiber T τ (.inl nb) (g : ℤ), ∃ na : ℕ+,
        (T.cmdAt η').bind Cmd.count? = some na ∧ (sd.BN nb).count = some na := by
      intro η' hη'
      rcases genFiber_nb_cases hη' with ⟨na, hcmd⟩ | ⟨na, hcmd⟩
      · obtain ⟨m, D', s₂, hm1, hmlen, -, hD', hs₂, hpost, hrcm⟩ :=
          genFiber_arrive_post_count hτ hη' hcmd
        have hlast : τ[τ.length - 1]? = some (Config.done sd) := by
          rw [← List.getLast?_eq_getElem?]; exact hdone
        have hrcend : recycleCount (.inl nb) τ m =
            recycleCount (.inl nb) τ (τ.length - 1) := by
          have hmn1 := recycleCount_mono (.inl nb) τ (show m - 1 ≤ m by omega)
          have hmn2 := recycleCount_mono (.inl nb) τ (show m ≤ τ.length - 1 by omega)
          omega
        have hcount := count_persists_nb hτ.1.1.subtrace (τ.length - 1) m
          (by omega) hrcend hD' hs₂ hpost hlast rfl
        exact ⟨na, by rw [hcmd]; simp [Cmd.count?], hcount⟩
      · exfalso
        exact genFiber_partial_no_sync hτ (hR ▸ hη') na hcmd
    obtain ⟨n₁, hc₁, he₁⟩ := hkey η₁ h₁
    obtain ⟨n₂, hc₂, he₂⟩ := hkey η₂ h₂
    rw [hc₁, hc₂, ← he₁, he₂]

/-- **Lower fibers are inhabited.** If some op has generation `g + 1` on `b` in
the reference trace, then `b` recycled at least `g + 1` times before it, and the
recycle closing round `g` consumed at least one registration — an op of
generation `g`. Supplies the checker pair's source `c1` in the "early"
contradiction. -/
theorem genFiber_nonempty_of_recycles {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℕ}
    (hrec : g + 1 ≤ recycleCount b τ (τ.length - 1)) :
    ∃ η', η' ∈ genFiber T τ b (g : ℤ) := by
  obtain ⟨p, hpm, hrc1, hrc2⟩ := recycleCount_hits b τ (show 1 ≤ g + 1 by omega) hrec
  simp only [Nat.add_sub_cancel] at hrc1
  obtain ⟨C, C', hC, hC', hrecb⟩ := recycle_step_of_count_lt (b := b) (τ := τ)
    (p := p) (by omega)
  have hstep := chain_step hτ.1.1.subtrace hC hC'
  -- a window start: `g` recycles of `b` done, `b`'s arrival counter zero
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc⟩ :
      ∃ w, w ≤ p ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ sw.arrivedAt b = 0 ∧
        recycleCount b τ w = g := by
    rcases Nat.eq_zero_or_pos g with rfl | hgpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, ?_, ?_⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · cases b <;> rfl
      · unfold recycleCount; simp
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits b τ hgpos
        (show g ≤ recycleCount b τ p by omega)
      obtain ⟨D, D', hD, hD', hrecD⟩ := recycle_step_of_count_lt (b := b) (τ := τ)
        (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hD'
      obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrecD
      exact ⟨q + 1, by omega, D', sD', hD', hsD',
        arrivedAt_zero_after_recycle hstepD hrecD hsD', by omega⟩
  cases b with
  | inl nb =>
    obtain ⟨s, Tc, I, A, n, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
      stepRecyclesBarrier_elim_nb hstep hrecb
    subst hCeq
    rcases hI : I with _ | ⟨t, I'⟩
    · -- the round was all-`arrive`s: trace one arrival back through the window
      subst hI
      refine genFiber_exists_of_arrive_window hτ hwp hCw hsw hw0 hC rfl ?_ hwrc hrc1
      change 0 < (s.BN nb).arrived
      rw [hbst]
      simp only [List.length_nil] at hfull
      have := n.pos
      change 0 < A
      omega
    · -- a parked sync: woken at this recycle, generation `g`
      subst hI
      subst hC'eq
      have hhead := hpark t (List.mem_cons_self ..)
      obtain ⟨rest, hrest⟩ : ∃ rest, Tc.prog t = Cmd.sync_nb nb n :: rest := by
        cases hTt : Tc.prog t with
        | nil => rw [hTt] at hhead; simp at hhead
        | cons a l =>
          rw [hTt] at hhead
          simp only [List.head?_cons, Option.some.injEq] at hhead
          exact ⟨l, by rw [hhead]⟩
      have hCprog : (Config.run s Tc).progOf t = Cmd.sync_nb nb n :: rest := hrest
      have hC'prog : (Config.run
          ({ s with E := updateMapOn s.E (t :: I') true,
                    BN := Function.update s.BN nb NamedBarrierState.unconfigured })
          (Tc.wake (t :: I'))).progOf t = rest := by
        simp only [WeftCommon.Config.progOf, WeftCommon.CTA.wake,
          if_pos (List.mem_cons_self ..), hrest, List.tail_cons]
      obtain ⟨htime, hcmd⟩ := exec_step_time hτ.1 hC hC' hCprog hC'prog
      exact ⟨_, mem_genFiber_of_time hcmd rfl rfl htime (by simpa using hrc1)⟩
  | inr sb =>
    -- mbarrier rounds are all-arrivals: at `p` the counter sits at `n ≥ 1`
    obtain ⟨s, Tc, I, A, n, ph, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
      stepRecyclesBarrier_elim_mb hstep hrecb
    subst hCeq
    refine genFiber_exists_of_arrive_window hτ hwp hCw hsw hw0 hC rfl ?_ hwrc hrc1
    change 0 < (s.BM sb).arrived
    rw [hbst]
    have := n.pos
    change 0 < A
    omega

/-- **Lower fibers are inhabited**, membership form: a fiber-`(g+1)` member
puts `g + 1` recycles before its time. -/
theorem genFiber_nonempty_of_succ {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℕ} {η : ProgPoint}
    (hη : η ∈ genFiber T τ b ((g + 1 : ℕ) : ℤ)) :
    ∃ η', η' ∈ genFiber T τ b (g : ℤ) := by
  obtain ⟨c, m, hcm, hreg, hbar, hm, hptm, hm1, hmlt, hgm⟩ := genFiber_time_data hτ hη
  refine genFiber_nonempty_of_recycles hτ ?_
  have := recycleCount_mono b τ (show m - 1 ≤ τ.length - 1 by omega)
  omega

/-- Arrive-command classifier (top-level, so its `match` auxiliary is shared
between the census lemma and its consumers). Covers both kinds
(`arrive_nb`/`arrive_mb`). -/
def isArriveCmd (T : CTA) (η : ProgPoint) : Bool :=
  match T.cmdAt η with
  | some c => c.isArrive
  | none => false

/-- `sync_nb`-command classifier; see `isArriveCmd`. -/
def isSyncCmd (T : CTA) (η : ProgPoint) : Bool :=
  match T.cmdAt η with
  | some (.sync_nb _ _) => true
  | _ => false

/-- The census predicate: an arrive member already executed by step `j`. -/
def arriveBy (T : CTA) (τ : List Config) (j : Nat) (η : ProgPoint) : Bool :=
  isArriveCmd T η &&
    (match pointTime T τ η with | some m => decide (m ≤ j) | none => false)

/-- **The window census.** From the start `w` of `b`'s round `g` (arrival
counter zero, `g` recycles done, every fiber time still ahead) to any index `j`
still inside the round, `b`'s arrival counter equals the number of fiber
arrives executed by `j`: each counter increment is an arrive execution whose
static point is a fresh fiber member, and nothing else moves the counter
(recycles of `b` lie outside the window). Uniform in the barrier kind. -/
theorem arrived_census {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {b : NamedBarrier ⊕ SharedBarrier} {g : ℕ}
    {w : Nat} {Cw : Config} {sw : State} (hCw : τ[w]? = some Cw)
    (hsw : Cw.state? = some sw) (hw0 : sw.arrivedAt b = 0)
    (hwrc : recycleCount b τ w = g)
    (hlate : ∀ η ∈ genFiber T τ b (g : ℤ), ∀ m, pointTime T τ η = some m → w < m) :
    ∀ (j : Nat), w ≤ j → recycleCount b τ j = g →
    ∀ (Cj : Config) (sj : State), τ[j]? = some Cj → Cj.state? = some sj →
    sj.arrivedAt b = (genFiber T τ b (g : ℤ)).countP (arriveBy T τ j) := by
  intro j hwj
  induction j, hwj using Nat.le_induction with
  | base =>
    intro _ Cj sj hCj hsj
    rw [hCw] at hCj
    obtain rfl := Option.some.inj hCj
    rw [hsw] at hsj
    obtain rfl := Option.some.inj hsj
    rw [hw0]
    symm
    rw [List.countP_eq_zero]
    intro η hη
    simp only [arriveBy, Bool.and_eq_true, not_and]
    intro _
    cases hpt : pointTime T τ η with
    | none => simp
    | some m =>
      have := hlate η hη m hpt
      simp only [decide_eq_true_eq]
      omega
  | succ j hwj ih =>
    intro hrcj1 Cj1 sj1 hCj1 hsj1
    have hjlt : j < τ.length := by
      have := (List.getElem?_eq_some_iff.mp hCj1).1
      omega
    obtain ⟨Dj, hCj⟩ : ∃ Dj, τ[j]? = some Dj :=
      ⟨τ[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
    have hstepj := chain_step hτ.1.1.subtrace hCj hCj1
    obtain ⟨sj, hsj⟩ : ∃ sj, Dj.state? = some sj := by
      rcases hjc : Dj with ⟨s₁, T₁⟩ | s₁ | T₁
      · exact ⟨s₁, rfl⟩
      · rw [hjc] at hstepj; cases hstepj
      · rw [hjc] at hstepj; cases hstepj
    have hrcj : recycleCount b τ j = g := by
      have h1 := recycleCount_mono b τ hwj
      have h2 := recycleCount_mono b τ (show j ≤ j + 1 by omega)
      omega
    have hprev := ih hrcj Dj sj hCj hsj
    -- executing a fiber arrive at this very step bumps the counter
    have hexec_inc : ∀ η ∈ genFiber T τ b (g : ℤ), ∀ c, T.cmdAt η = some c →
        c.isArrive = true → pointTime T τ η = some (j + 1) →
        sj1.arrivedAt b = sj.arrivedAt b + 1 := by
      intro η hη c hcm hcarr hpt
      obtain ⟨c', hcm', -, hbar', -⟩ := registrantGen_some (mem_genFiber.mp hη).2
      rw [hcm] at hcm'
      obtain rfl := Option.some.inj hcm'
      have htime := isTimeOf_of_pointTime hτ.1 hpt
      obtain ⟨-, hidxlt, j₀, D, D', hj₀, hD, hD', hDdrop, hD'drop⟩ := htime
      have hj₀j : j₀ = j := by omega
      subst hj₀j
      have hDeq : Dj = D := by
        have h := hD
        rw [hCj] at h
        exact Option.some.inj h
      subst hDeq
      have hD'eq : D' = Cj1 := by
        have h := hD'
        rw [hCj1] at h
        exact (Option.some.inj h).symm
      subst hD'eq
      have hcmg : ((Config.run State.initial T).progOf η.thread)[η.idx]? =
          some c := hcm
      obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcmg
      have hDcons : Dj.progOf η.thread = c ::
          ((Config.run State.initial T).progOf η.thread).drop (η.idx + 1) := by
        rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
      exact arrive_exec_arrivedAt hstepj hcarr hbar' hDcons hD'drop hsj hsj1
    rcases arrivedAt_step (b := b) hstepj hsj hsj1 with
      heq | ⟨i, c, rest, hcarr, hcbar, hCi, hC'i⟩ | hrecj
    · -- counter unchanged: no fiber arrive executed at `j + 1`
      rw [heq, hprev]
      refine List.countP_congr fun η hη => ?_
      cases hcm : T.cmdAt η with
      | none => simp [arriveBy, isArriveCmd, hcm]
      | some cmd =>
        cases hcarr' : cmd.isArrive with
        | false => simp [arriveBy, isArriveCmd, hcm, hcarr']
        | true =>
          simp only [arriveBy, isArriveCmd, hcm, hcarr', Bool.true_and]
          cases hpt : pointTime T τ η with
          | none => rfl
          | some m =>
            by_cases hmj : m = j + 1
            · exfalso
              subst hmj
              have := hexec_inc η hη cmd hcm hcarr' hpt
              omega
            · simp only [decide_eq_true_eq]
              constructor
              · intro; omega
              · intro; omega
    · -- the counter grew: exactly one fresh census member, the executed arrive
      obtain ⟨htimeN, hcmdN⟩ := exec_step_time hτ.1 hCj hCj1 hCi hC'i
      have hinc := arrive_exec_arrivedAt hstepj hcarr hcbar hCi hC'i hsj hsj1
      have hηmem : (⟨i, (T.prog i).length - (Dj.progOf i).length⟩ : ProgPoint) ∈
          genFiber T τ b (g : ℤ) :=
        mem_genFiber_of_time hcmdN (Cmd.isRegistrant_of_isArrive hcarr) hcbar htimeN
          (by simpa using hrcj)
      have hptN : pointTime T τ ⟨i, (T.prog i).length - (Dj.progOf i).length⟩ =
          some (j + 1) := pointTime_eq_of_isTimeOf htimeN
      rw [hinc, hprev]
      symm
      refine countP_succ_of_unique (genFiber_nodup T τ b (g : ℤ)) hηmem ?_ ?_ ?_
      · simp only [arriveBy, isArriveCmd, hcmdN, hptN, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨hcarr, le_refl _⟩
      · simp only [arriveBy, isArriveCmd, hcmdN, hptN]
        simp
      · intro x hx hxne
        cases hcmx : T.cmdAt x with
        | none => simp [arriveBy, isArriveCmd, hcmx]
        | some cmd =>
          cases hcarrx : cmd.isArrive with
          | false => simp [arriveBy, isArriveCmd, hcmx, hcarrx]
          | true =>
            simp only [arriveBy, isArriveCmd, hcmx, hcarrx, Bool.true_and]
            cases hpt : pointTime T τ x with
            | none => rfl
            | some m =>
              by_cases hmj : m = j + 1
              · exfalso
                subst hmj
                have htimeX := isTimeOf_of_pointTime hτ.1 hpt
                obtain ⟨-, hidxX, j₀, D, D', hj₀, hD, hD', hXdrop, hX'drop⟩ := htimeX
                have hj₀j : j₀ = j := by omega
                subst hj₀j
                have hDeq : Dj = D := by
                  have h := hD
                  rw [hCj] at h
                  exact Option.some.inj h
                subst hDeq
                have hD'eq : D' = Cj1 := by
                  have h := hD'
                  rw [hCj1] at h
                  exact (Option.some.inj h).symm
                subst hD'eq
                have hcmx' : ((Config.run State.initial T).progOf x.thread)[x.idx]? =
                    some cmd := hcmx
                obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcmx'
                have hXcons : Dj.progOf x.thread = cmd ::
                    ((Config.run State.initial T).progOf x.thread).drop (x.idx + 1) := by
                  rw [hXdrop, List.drop_eq_getElem_cons hlt0, hget0]
                have hthread : x.thread = i :=
                  arrive_head_drop_same_thread hstepj hcarrx hXcons hX'drop hCi hC'i
                have hidxeq : x.idx = (T.prog i).length - (Dj.progOf i).length := by
                  have hXdrop' : Dj.progOf i =
                      ((Config.run State.initial T).progOf i).drop x.idx := by
                    rw [← hthread]; exact hXdrop
                  have hlenX := congrArg List.length hXdrop'
                  have hidxX' : x.idx <
                      ((Config.run State.initial T).progOf i).length := by
                    rw [← hthread]; exact hidxX
                  have hTlen : ((Config.run State.initial T).progOf i).length =
                      (T.prog i).length := rfl
                  simp only [List.length_drop] at hlenX
                  omega
                exact hxne (by
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  rw [hxeta, hthread, hidxeq])
              · simp only [decide_eq_decide]
                constructor
                · intro; omega
                · intro; omega
    · exfalso
      have := recycleCount_succ_of_recycle b τ hCj hCj1 hrecj
      omega

/-- **The round data of a completed mbarrier generation.** For a round `g` that
completes, locate the `mb_recycle` that closes it: at step `p` the barrier
holds exactly `n` arrivals, the parked waiters sit at `wait_mb sb ph` heads,
and the recycle wakes them, keeping the count and flipping the phase. (Unlike
the named round data there is no fiber-parameter clause — `arrive_mb`s carry no
count; the capacity is pinned by `count_some_persists_le` against any
initialized state.) -/
theorem genFiber_round_data_mb {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {sb : SharedBarrier} {g : ℕ}
    (hcomplete : g + 1 ≤ recycleCount (.inr sb) τ (τ.length - 1)) :
    ∃ (p : Nat) (s : State) (Tc : CTA) (I : List ThreadId) (n : ℕ+) (ph : Phase),
      recycleCount (.inr sb) τ p = g ∧ recycleCount (.inr sb) τ (p + 1) = g + 1 ∧
      τ[p]? = some (Config.run s Tc) ∧ s.BM sb = ⟨I, (n : ℕ), some n, ph⟩ ∧
      (∀ i ∈ I, (Tc.prog i).head? = some (Cmd.wait_mb sb ph)) ∧
      τ[p + 1]? = some (Config.run
        ({ s with E := updateMapOn s.E I true,
                  BM := Function.update s.BM sb ⟨[], 0, some n, !ph⟩ })
        (Tc.wake I)) := by
  obtain ⟨p, hpM, hrc1, hrc2⟩ := recycleCount_hits (.inr sb) τ
    (show 1 ≤ g + 1 by omega) hcomplete
  simp only [Nat.add_sub_cancel] at hrc1
  obtain ⟨C, C', hC, hC', hrecb⟩ := recycle_step_of_count_lt
    (b := .inr sb) (τ := τ) (p := p) (by omega)
  have hstep := chain_step hτ.1.1.subtrace hC hC'
  obtain ⟨s, Tc, I, A, n, ph, hCeq, hbst, hfull, hpark, hC'eq⟩ :=
    stepRecyclesBarrier_elim_mb hstep hrecb
  subst hCeq; subst hC'eq
  subst hfull
  exact ⟨p, s, Tc, I, n, ph, hrc1, hrc2, hC, hbst, hpark, hC'⟩

/-- Multi-step mbarrier count persistence: once initialized with count `n`, the
count stays `some n` forever (`init_mb` errs on re-initialization and
`mb_recycle` keeps the count). -/
theorem count_some_persists_le {τ : List Config} (hchain : List.IsChain CTAStep τ)
    {sb : SharedBarrier} {n : ℕ+} :
    ∀ (k j : Nat), j ≤ k →
    ∀ {C : Config} {s : State}, τ[j]? = some C → C.state? = some s →
      (s.BM sb).count = some n →
    ∀ {C' : Config} {s' : State}, τ[k]? = some C' → C'.state? = some s' →
      (s'.BM sb).count = some n := by
  intro k
  induction k with
  | zero =>
    intro j hjk C s hC hs hn C' s' hC' hs'
    obtain rfl : j = 0 := by omega
    rw [hC] at hC'
    obtain rfl := Option.some.inj hC'
    rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    exact hn
  | succ k ih =>
    intro j hjk C s hC hs hn C' s' hC' hs'
    by_cases hje : j = k + 1
    · subst hje
      rw [hC] at hC'
      obtain rfl := Option.some.inj hC'
      rw [hs] at hs'
      obtain rfl := Option.some.inj hs'
      exact hn
    · have hjk' : j ≤ k := by omega
      have hklt : k < τ.length := by
        have := (List.getElem?_eq_some_iff.mp hC').1
        omega
      have hCk : τ[k]? = some τ[k] := List.getElem?_eq_getElem hklt
      have hstepk := chain_step hchain hCk hC'
      obtain ⟨sk, hsk⟩ : ∃ sk, (τ[k]).state? = some sk := by
        rcases hkc : τ[k] with ⟨s₁, T₁⟩ | s₁ | T₁
        · exact ⟨s₁, rfl⟩
        · rw [hkc] at hstepk; cases hstepk
        · rw [hkc] at hstepk; cases hstepk
      exact count_some_persists hstepk hsk hs' (ih j hjk' hC hs hn hCk hsk)

/-- **Fiber size = round capacity** (named). If `nb`'s round `g` completes in
the reference trace, the fiber `F_g(nb)` has exactly `n` members, `n` the
common parameter of its members: the round consumed exactly `n` registrations,
each a distinct program point, and every fiber member was among them. -/
theorem genFiber_length {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {g : ℕ}
    (hcomplete : g + 1 ≤ recycleCount (.inl nb) τ (τ.length - 1))
    {η : ProgPoint} (hη : η ∈ genFiber T τ (.inl nb) (g : ℤ)) {n : ℕ+}
    (hn : (T.cmdAt η).bind Cmd.count? = some n) :
    (genFiber T τ (.inl nb) (g : ℤ)).length = (n : Nat) := by
  obtain ⟨p, s, Tc, I, A, n₀, hrc1, hrc2, hCp, hbst, hfull, hpark, hCp1, hall,
    hsyncD, hsurj⟩ := genFiber_round_data hτ hcomplete
  -- the given member pins `n` to the round count
  have hnn : n = n₀ := by
    have h := hall η hη
    rw [hn] at h
    exact Option.some.inj h
  subst hnn
  -- decoding sync members off the fiber
  have hdecode_sync : ∀ x ∈ genFiber T τ (.inl nb) (g : ℤ), isSyncCmd T x = true →
      ∃ nx : ℕ+, T.cmdAt x = some (.sync_nb nb nx) := by
    intro x hxF hxs
    rcases genFiber_nb_cases hxF with ⟨nx, hcmd⟩ | ⟨nx, hcmd⟩
    · exfalso
      simp [isSyncCmd, hcmd] at hxs
    · exact ⟨nx, hcmd⟩
  -- window start `w`: zero arrivals, `g` recycles done, all member times ahead
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ p ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ sw.arrivedAt (.inl nb) = 0 ∧
        recycleCount (.inl nb) τ w = g ∧
        (w = 0 ∨ (1 ≤ g ∧ recycleCount (.inl nb) τ (w - 1) = g - 1)) := by
    rcases Nat.eq_zero_or_pos g with rfl | hgpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · unfold recycleCount; simp
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits (.inl nb) τ hgpos
        (show g ≤ recycleCount (.inl nb) τ p by omega)
      obtain ⟨D, D', hD, hD', hrecD⟩ := recycle_step_of_count_lt (b := .inl nb)
        (τ := τ) (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hD'
      obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrecD
      refine ⟨q + 1, by omega, D', sD', hD', hsD',
        arrivedAt_zero_after_recycle hstepD hrecD hsD', by omega,
        Or.inr ⟨hgpos, ?_⟩⟩
      simp only [Nat.add_sub_cancel]
      omega
  -- fiber times lie strictly beyond `w`
  have hlate : ∀ η' ∈ genFiber T τ (.inl nb) (g : ℤ), ∀ m,
      pointTime T τ η' = some m → w < m := by
    intro η' hη' m hpt
    obtain ⟨c', m', -, -, -, -, hpt', hm'1, -, hgm'⟩ := genFiber_time_data hτ hη'
    rw [hpt] at hpt'
    obtain rfl := Option.some.inj hpt'
    by_contra hcon
    rcases hwlow with rfl | ⟨hgpos, hw2⟩
    · omega
    · have hmono : recycleCount (.inl nb) τ (m - 1) ≤
          recycleCount (.inl nb) τ (w - 1) :=
        recycleCount_mono (.inl nb) τ (by omega)
      omega
  -- the census at the recycle instant: `A` counts the executed fiber arrives
  have hcensus := arrived_census hτ hCw hsw hw0 hwrc hlate p hwp hrc1
    (Config.run s Tc) s hCp rfl
  have hA : A = (genFiber T τ (.inl nb) (g : ℤ)).countP (arriveBy T τ p) := by
    have h := hcensus
    simp only [State.arrivedAt] at h
    rw [hbst] at h
    simpa using h
  -- every fiber arrive has executed by `p`
  have harr : (genFiber T τ (.inl nb) (g : ℤ)).countP (arriveBy T τ p) =
      (genFiber T τ (.inl nb) (g : ℤ)).countP (isArriveCmd T) := by
    refine List.countP_congr fun η' hη' => ?_
    simp only [arriveBy, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, -⟩
      exact h1
    · intro h1
      refine ⟨h1, ?_⟩
      obtain ⟨na, hcm⟩ : ∃ na : ℕ+, T.cmdAt η' = some (.arrive_nb nb na) := by
        rcases genFiber_nb_cases hη' with ⟨na, hcmd⟩ | ⟨na, hcmd⟩
        · exact ⟨na, hcmd⟩
        · exfalso
          simp [isArriveCmd, hcmd, Cmd.isArrive] at h1
      obtain ⟨m₀, D', s₂, hm₀1, hm₀len, hptm₀, hD', hs₂, hpost, hrcm₀⟩ :=
        genFiber_arrive_post_count hτ hη' hcm
      rw [hptm₀]
      -- `m₀ ≠ p + 1`: post-arrive is configured, post-recycle is not
      have hmp : m₀ ≠ p + 1 := by
        intro hmeq
        subst hmeq
        rw [hD'] at hCp1
        obtain rfl := Option.some.inj hCp1
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hs₂
        subst hs₂
        simp [Function.update_self, NamedBarrierState.unconfigured] at hpost
      have hm₀le : m₀ ≤ p := by
        by_contra hcon
        have hple : p + 1 ≤ m₀ - 1 := by omega
        have := recycleCount_mono (.inl nb) τ hple
        omega
      simp only [decide_eq_true_eq]
      omega
  -- the sync members are exactly the parked threads
  have hsync_len : (genFiber T τ (.inl nb) (g : ℤ)).countP (isSyncCmd T) =
      I.length := by
    have hndF : ((genFiber T τ (.inl nb) (g : ℤ)).filter (isSyncCmd T)).Nodup :=
      (genFiber_nodup T τ (.inl nb) (g : ℤ)).filter _
    have hreach : Relation.ReflTransGen CTAStep (Config.run State.initial T)
        (Config.run s Tc) := by
      refine reaches_of_chain_getElem hτ.1.1.subtrace ?_ p _ hCp
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact hτ.1.2
    have hwf := WF_of_reaches hreach
    have hndI : I.Nodup := by
      have h := hwf.2.2.2.2.2.1 (Sum.inl nb)
      have hb : s.blocked (Sum.inl nb) = I := by
        simp [State.blocked, hbst]
      rwa [hb] at h
    rw [List.countP_eq_length_filter]
    rw [← List.toFinset_card_of_nodup hndF, ← List.toFinset_card_of_nodup hndI]
    refine Finset.card_bij (fun η' _ => η'.thread) ?_ ?_ ?_
    · intro η' hη'
      simp only [List.mem_toFinset, List.mem_filter] at hη'
      obtain ⟨hmemF, hsync⟩ := hη'
      obtain ⟨nx, hcm⟩ := hdecode_sync η' hmemF hsync
      exact List.mem_toFinset.mpr ((hsyncD η' hmemF nx hcm).1)
    · intro x hx y hy hxy
      simp only [List.mem_toFinset, List.mem_filter] at hx hy
      obtain ⟨hxF, hxs⟩ := hx
      obtain ⟨hyF, hys⟩ := hy
      obtain ⟨nx, hcmx⟩ := hdecode_sync x hxF hxs
      obtain ⟨ny, hcmy⟩ := hdecode_sync y hyF hys
      obtain ⟨-, hptx⟩ := hsyncD x hxF nx hcmx
      obtain ⟨-, hpty⟩ := hsyncD y hyF ny hcmy
      have hxi : x.idx < (T.prog x.thread).length :=
        ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
      have hyi : y.idx < (T.prog y.thread).length :=
        ((mem_progPoints_iff T y).mp (mem_genFiber.mp hyF).1).2
      rw [hxy] at hptx hxi
      have hdd := hptx.symm.trans hpty
      have hlen := congrArg List.length hdd
      simp only [List.length_drop] at hlen
      have hxid : x.idx = y.idx := by omega
      have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
      have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
      rw [hxeta, hyeta, hxy, hxid]
    · intro i hi
      obtain ⟨η', hη'F, hth, nn, hcm⟩ := hsurj i (List.mem_toFinset.mp hi)
      refine ⟨η', ?_, hth⟩
      simp only [List.mem_toFinset, List.mem_filter]
      refine ⟨hη'F, ?_⟩
      simp [isSyncCmd, hcm]
  -- partition the fiber into syncs and arrives
  have hpartition : (genFiber T τ (.inl nb) (g : ℤ)).length =
      (genFiber T τ (.inl nb) (g : ℤ)).countP (isSyncCmd T) +
      (genFiber T τ (.inl nb) (g : ℤ)).countP (isArriveCmd T) := by
    rw [List.length_eq_countP_add_countP (isSyncCmd T)]
    congr 1
    refine List.countP_congr fun η' hη' => ?_
    rcases genFiber_nb_cases hη' with ⟨na, hcmd⟩ | ⟨na, hcmd⟩ <;>
      simp [isSyncCmd, isArriveCmd, hcmd, Cmd.isArrive]
  rw [hpartition, hsync_len, ← harr, ← hA]
  exact hfull

/-- Sync members of a completed round's fiber have pairwise-distinct threads:
both are woken by the same recycle with control at themselves, so equal threads
force equal positions. -/
theorem genFiber_sync_thread_inj {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {g : ℕ}
    (hcomplete : g + 1 ≤ recycleCount (.inl nb) τ (τ.length - 1))
    {x y : ProgPoint} (hx : x ∈ genFiber T τ (.inl nb) (g : ℤ))
    (hy : y ∈ genFiber T τ (.inl nb) (g : ℤ))
    {nx ny : ℕ+} (hcx : T.cmdAt x = some (.sync_nb nb nx))
    (hcy : T.cmdAt y = some (.sync_nb nb ny))
    (hthread : x.thread = y.thread) : x = y := by
  obtain ⟨p, s, Tc, I, A, n, -, -, -, -, -, -, -, -, hsyncD, -⟩ :=
    genFiber_round_data hτ hcomplete
  obtain ⟨-, hpx⟩ := hsyncD x hx nx hcx
  obtain ⟨-, hpy⟩ := hsyncD y hy ny hcy
  have hxi : x.idx < (T.prog x.thread).length :=
    ((mem_progPoints_iff T x).mp (mem_genFiber.mp hx).1).2
  have hyi : y.idx < (T.prog y.thread).length :=
    ((mem_progPoints_iff T y).mp (mem_genFiber.mp hy).1).2
  rw [hthread] at hpx hxi
  have hdd := hpx.symm.trans hpy
  have hlen := congrArg List.length hdd
  simp only [List.length_drop] at hlen
  have hxid : x.idx = y.idx := by omega
  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
  have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
  rw [hxeta, hyeta, hthread, hxid]

/-- **Fiber size = round capacity** (mbarrier). If `sb`'s round `g` completes in
the reference trace, the fiber `F_g(sb)` has exactly `n` members, `n` the
barrier's (persistent) initialized count, witnessed at any state of the trace:
the round consumed exactly `n` arrivals, each a distinct `arrive_mb` point, and
every fiber member was among them. -/
theorem genFiber_length_mb {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {sb : SharedBarrier} {g : ℕ}
    (hcomplete : g + 1 ≤ recycleCount (.inr sb) τ (τ.length - 1))
    {n : ℕ+} {m : Nat} {C : Config} {st : State} (hC : τ[m]? = some C)
    (hst : C.state? = some st) (hcnt : (st.BM sb).count = some n) :
    (genFiber T τ (.inr sb) (g : ℤ)).length = (n : Nat) := by
  obtain ⟨p, s, Tc, I, n', ph, hrc1, hrc2, hCp, hbst, hpark, hCp1⟩ :=
    genFiber_round_data_mb hτ hcomplete
  -- the round capacity is the (persistent) count `n`
  have hn'n : n = n' := by
    rcases Nat.le_total m p with hmp | hpm
    · have h := count_some_persists_le hτ.1.1.subtrace p m hmp hC hst hcnt hCp rfl
      rw [hbst] at h
      exact (Option.some.inj h).symm
    · have h := count_some_persists_le hτ.1.1.subtrace m p hpm hCp rfl
        (show (s.BM sb).count = some n' by rw [hbst]) hC hst
      rw [hcnt] at h
      exact Option.some.inj h
  subst hn'n
  -- window start `w`: zero arrivals, `g` recycles done, all member times ahead
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ p ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ sw.arrivedAt (.inr sb) = 0 ∧
        recycleCount (.inr sb) τ w = g ∧
        (w = 0 ∨ (1 ≤ g ∧ recycleCount (.inr sb) τ (w - 1) = g - 1)) := by
    rcases Nat.eq_zero_or_pos g with rfl | hgpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · unfold recycleCount; simp
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits (.inr sb) τ hgpos
        (show g ≤ recycleCount (.inr sb) τ p by omega)
      obtain ⟨D, D', hD, hD', hrecD⟩ := recycle_step_of_count_lt (b := .inr sb)
        (τ := τ) (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hD'
      obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrecD
      refine ⟨q + 1, by omega, D', sD', hD', hsD',
        arrivedAt_zero_after_recycle hstepD hrecD hsD', by omega,
        Or.inr ⟨hgpos, ?_⟩⟩
      simp only [Nat.add_sub_cancel]
      omega
  -- fiber times lie strictly beyond `w`
  have hlate : ∀ η' ∈ genFiber T τ (.inr sb) (g : ℤ), ∀ m',
      pointTime T τ η' = some m' → w < m' := by
    intro η' hη' m' hpt
    obtain ⟨c', m'', -, -, -, -, hpt', hm'1, -, hgm'⟩ := genFiber_time_data hτ hη'
    rw [hpt] at hpt'
    obtain rfl := Option.some.inj hpt'
    by_contra hcon
    rcases hwlow with rfl | ⟨hgpos, hw2⟩
    · omega
    · have hmono : recycleCount (.inr sb) τ (m' - 1) ≤
          recycleCount (.inr sb) τ (w - 1) :=
        recycleCount_mono (.inr sb) τ (by omega)
      omega
  -- the census at the recycle instant
  have hcensus := arrived_census hτ hCw hsw hw0 hwrc hlate p hwp hrc1
    (Config.run s Tc) s hCp rfl
  have hA : (n : ℕ) = (genFiber T τ (.inr sb) (g : ℤ)).countP (arriveBy T τ p) := by
    have h := hcensus
    simp only [State.arrivedAt] at h
    rw [hbst] at h
    simpa using h
  -- every member is an arrive executed by `p`
  have hfilterall : (genFiber T τ (.inr sb) (g : ℤ)).countP (arriveBy T τ p) =
      (genFiber T τ (.inr sb) (g : ℤ)).length := by
    conv_rhs => rw [← List.countP_true]
    refine List.countP_congr fun x hx => ?_
    have hcmx := genFiber_mb_arrive hx
    obtain ⟨c', m₀, -, -, -, hm₀time, hptm₀, hm₀1, hm₀lt, hgm₀⟩ :=
      genFiber_time_data hτ hx
    -- `m₀ ≠ p + 1`: the recycle step drops no arrive head (the counter resets)
    have hmp : m₀ ≠ p + 1 := by
      intro hmeq
      subst hmeq
      obtain ⟨-, -, j₀, D, D', hj₀, hD, hD', hXdrop, hX'drop⟩ := hm₀time
      have hj₀p : j₀ = p := by omega
      subst hj₀p
      have hDeq : D = Config.run s Tc := by
        rw [hD] at hCp
        exact Option.some.inj hCp
      subst hDeq
      have hD'eq : D' = Config.run
          ({ s with E := updateMapOn s.E I true,
                    BM := Function.update s.BM sb ⟨[], 0, some n, !ph⟩ })
          (Tc.wake I) := by
        rw [hD'] at hCp1
        exact Option.some.inj hCp1
      subst hD'eq
      have hcmg : ((Config.run State.initial T).progOf x.thread)[x.idx]? =
          some (Cmd.arrive_mb sb) := hcmx
      obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcmg
      have hXcons : (Config.run s Tc).progOf x.thread = Cmd.arrive_mb sb ::
          ((Config.run State.initial T).progOf x.thread).drop (x.idx + 1) := by
        rw [hXdrop, List.drop_eq_getElem_cons hlt0, hget0]
      have hstepp := chain_step hτ.1.1.subtrace hCp hCp1
      have hbump := arrive_mb_drop_arrived hstepp hXcons hX'drop rfl rfl
      rw [hbst] at hbump
      simp only [Function.update_self] at hbump
      omega
    have hm₀le : m₀ ≤ p := by
      by_contra hcon
      have hple : p + 1 ≤ m₀ - 1 := by omega
      have := recycleCount_mono (.inr sb) τ hple
      omega
    simp [arriveBy, isArriveCmd, hcmx, Cmd.isArrive, hptm₀, hm₀le]
  rw [← hfilterall, ← hA]

/-- **The partial named round is under-full.** The fiber of the round past the
last completed one has strictly fewer members than its count parameter: all its
members are executed `arrive_nb`s (the trace ends `done`), the census equates
their number with the final arrival counter, and the `done` step's premise
keeps every configured barrier strictly under-full. -/
theorem genFiber_partial_length_lt {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {nb : NamedBarrier} {η : ProgPoint}
    (hη : η ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)) {n : ℕ+}
    (hn : (T.cmdAt η).bind Cmd.count? = some n) :
    (genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)).length < (n : ℕ) := by
  obtain ⟨sd, hdone⟩ := hτ.2
  -- η is an arrive with parameter `n`
  obtain ⟨na, hcm⟩ : ∃ na : ℕ+, T.cmdAt η = some (.arrive_nb nb na) := by
    rcases genFiber_nb_cases hη with ⟨na, hcmd⟩ | ⟨na, hcmd⟩
    · exact ⟨na, hcmd⟩
    · exact absurd hcmd (genFiber_partial_no_sync hτ hη na)
  have hna : n = na := by
    rw [hcm] at hn
    simpa [Cmd.count?] using hn.symm
  subst hna
  -- the configured count at the end of τ is `some n`
  obtain ⟨m, D', s₂, hm1, hmlen, hptm, hD', hs₂, hpost, hrcm⟩ :=
    genFiber_arrive_post_count hτ hη hcm
  have hlast : τ[τ.length - 1]? = some (Config.done sd) := by
    rw [← List.getLast?_eq_getElem?]; exact hdone
  have hrcend : recycleCount (.inl nb) τ m =
      recycleCount (.inl nb) τ (τ.length - 1) := by
    have h1 := recycleCount_mono (.inl nb) τ (show m - 1 ≤ m by omega)
    have h2 := recycleCount_mono (.inl nb) τ (show m ≤ τ.length - 1 by omega)
    omega
  have hcount := count_persists_nb hτ.1.1.subtrace (τ.length - 1) m (by omega)
    hrcend hD' hs₂ hpost hlast rfl
  -- the final `done` step keeps every configured named barrier under-full
  have hlen2 : 2 ≤ τ.length := by
    by_contra hcon
    have hne : τ ≠ [] := fun h => by rw [h] at hdone; simp at hdone
    have hlen1 : τ.length = 1 := by
      have h1 : 1 ≤ τ.length := by
        cases τ with
        | nil => simp at hne
        | cons _ _ => simp
      omega
    have h0 : τ[0]? = some (Config.run State.initial T) := by
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact hτ.1.2
    rw [hlen1] at hlast
    rw [show (1 : ℕ) - 1 = 0 from rfl, h0] at hlast
    simp at hlast
  obtain ⟨Cpre, hCpre⟩ : ∃ Cpre, τ[τ.length - 2]? = some Cpre :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hClast : τ[τ.length - 2 + 1]? = some (Config.done sd) := by
    rw [show τ.length - 2 + 1 = τ.length - 1 by omega]; exact hlast
  have hstepd := chain_step hτ.1.1.subtrace hCpre hClast
  have hnofull : ∀ (nb' : NamedBarrier) (I : List ThreadId) (A : Nat) (n' : ℕ+),
      sd.BN nb' = ⟨I, A, some n'⟩ → I.length + A < (n' : ℕ) := by
    cases hstepd with
    | done hdone' hnofull' hmbnofull' => exact hnofull'
  obtain ⟨Id, Ad, hsb⟩ : ∃ Id Ad, sd.BN nb = ⟨Id, Ad, some n⟩ := by
    rcases hsb : sd.BN nb with ⟨Id, Ad, cnt⟩
    rw [hsb] at hcount
    have hcnt : cnt = some n := hcount
    exact ⟨Id, Ad, by rw [hcnt]⟩
  have hAd := hnofull nb Id Ad n hsb
  -- window start for the partial round
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ τ.length - 1 ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ sw.arrivedAt (.inl nb) = 0 ∧
        recycleCount (.inl nb) τ w = recycleCount (.inl nb) τ (τ.length - 1) ∧
        (w = 0 ∨ (1 ≤ recycleCount (.inl nb) τ (τ.length - 1) ∧
          recycleCount (.inl nb) τ (w - 1) =
            recycleCount (.inl nb) τ (τ.length - 1) - 1)) := by
    rcases Nat.eq_zero_or_pos (recycleCount (.inl nb) τ (τ.length - 1)) with
      hR0 | hRpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · have h00 : recycleCount (.inl nb) τ 0 = 0 := by unfold recycleCount; simp
        omega
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits (.inl nb) τ hRpos (le_refl _)
      obtain ⟨D, Dn, hD, hDn, hrecD⟩ := recycle_step_of_count_lt (b := .inl nb)
        (τ := τ) (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hDn
      obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrecD
      refine ⟨q + 1, by omega, Dn, sD', hDn, hsD',
        arrivedAt_zero_after_recycle hstepD hrecD hsD', by omega,
        Or.inr ⟨hRpos, ?_⟩⟩
      simp only [Nat.add_sub_cancel]
      omega
  -- fiber times lie strictly beyond `w`
  have hlate : ∀ η' ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ), ∀ m',
      pointTime T τ η' = some m' → w < m' := by
    intro η' hη' m' hpt
    obtain ⟨c', m'', -, -, -, -, hpt', hm''1, -, hgm'⟩ := genFiber_time_data hτ hη'
    rw [hpt] at hpt'
    obtain rfl := Option.some.inj hpt'
    by_contra hcon
    rcases hwlow with rfl | ⟨hRpos, hw2⟩
    · omega
    · have hmono : recycleCount (.inl nb) τ (m' - 1) ≤
          recycleCount (.inl nb) τ (w - 1) :=
        recycleCount_mono (.inl nb) τ (by omega)
      omega
  -- the census at the final index counts the whole fiber
  have hcensus := arrived_census hτ hCw hsw hw0 hwrc hlate (τ.length - 1) hwp rfl
    (Config.done sd) sd hlast rfl
  have hAd' : Ad = (genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)).countP
        (arriveBy T τ (τ.length - 1)) := by
    have h := hcensus
    simp only [State.arrivedAt] at h
    rw [hsb] at h
    simpa using h
  have hfilterall : (genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)).countP
        (arriveBy T τ (τ.length - 1)) =
      (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)).length := by
    conv_rhs => rw [← List.countP_true]
    refine List.countP_congr fun x hx => ?_
    obtain ⟨nx, hcmx⟩ : ∃ nx : ℕ+, T.cmdAt x = some (.arrive_nb nb nx) := by
      rcases genFiber_nb_cases hx with ⟨nx, hcmd⟩ | ⟨nx, hcmd⟩
      · exact ⟨nx, hcmd⟩
      · exact absurd hcmd (genFiber_partial_no_sync hτ hx nx)
    obtain ⟨c', mx, -, -, -, -, hptx, hmx1, hmxlt, -⟩ := genFiber_time_data hτ hx
    have hmx' : mx ≤ τ.length - 1 := by omega
    simp [arriveBy, isArriveCmd, hcmx, Cmd.isArrive, hptx, hmx']
  omega

/-- **The partial mbarrier round is under-full.** The fiber of the round past
the last completed one has strictly fewer members than the barrier's
initialized count: all its members are executed `arrive_mb`s, the census
equates their number with the final arrival counter, and the `done` step's
premise keeps every initialized mbarrier strictly under-full in arrivals. -/
theorem genFiber_partial_length_lt_mb {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {sb : SharedBarrier} {n : ℕ+} {m : Nat} {C : Config} {st : State}
    (hC : τ[m]? = some C) (hst : C.state? = some st)
    (hcnt : (st.BM sb).count = some n) :
    (genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ)).length < (n : ℕ) := by
  obtain ⟨sd, hdone⟩ := hτ.2
  have hlast : τ[τ.length - 1]? = some (Config.done sd) := by
    rw [← List.getLast?_eq_getElem?]; exact hdone
  have hmlt : m < τ.length := (List.getElem?_eq_some_iff.mp hC).1
  have hcount := count_some_persists_le hτ.1.1.subtrace (τ.length - 1) m (by omega)
    hC hst hcnt hlast rfl
  -- the final `done` step keeps every initialized mbarrier under-full
  have hlen2 : 2 ≤ τ.length := by
    by_contra hcon
    have hne : τ ≠ [] := fun h => by rw [h] at hdone; simp at hdone
    have hlen1 : τ.length = 1 := by
      have h1 : 1 ≤ τ.length := by
        cases τ with
        | nil => simp at hne
        | cons _ _ => simp
      omega
    have h0 : τ[0]? = some (Config.run State.initial T) := by
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact hτ.1.2
    rw [hlen1] at hlast
    rw [show (1 : ℕ) - 1 = 0 from rfl, h0] at hlast
    simp at hlast
  obtain ⟨Cpre, hCpre⟩ : ∃ Cpre, τ[τ.length - 2]? = some Cpre :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hClast : τ[τ.length - 2 + 1]? = some (Config.done sd) := by
    rw [show τ.length - 2 + 1 = τ.length - 1 by omega]; exact hlast
  have hstepd := chain_step hτ.1.1.subtrace hCpre hClast
  have hmbnofull : ∀ (sb' : SharedBarrier) (I : List ThreadId) (A : Nat) (n' : ℕ+)
      (ph : Phase), sd.BM sb' = ⟨I, A, some n', ph⟩ → A < (n' : ℕ) := by
    cases hstepd with
    | done hdone' hnofull' hmbnofull' => exact hmbnofull'
  obtain ⟨Id, Ad, phd, hsb⟩ : ∃ Id Ad phd, sd.BM sb = ⟨Id, Ad, some n, phd⟩ := by
    rcases hsb : sd.BM sb with ⟨Id, Ad, cnt, phd⟩
    rw [hsb] at hcount
    have hcnt' : cnt = some n := hcount
    exact ⟨Id, Ad, phd, by rw [hcnt']⟩
  have hAd := hmbnofull sb Id Ad n phd hsb
  -- window start for the partial round
  obtain ⟨w, hwp, Cw, sw, hCw, hsw, hw0, hwrc, hwlow⟩ :
      ∃ w, w ≤ τ.length - 1 ∧ ∃ (Cw : Config) (sw : State),
        τ[w]? = some Cw ∧ Cw.state? = some sw ∧ sw.arrivedAt (.inr sb) = 0 ∧
        recycleCount (.inr sb) τ w = recycleCount (.inr sb) τ (τ.length - 1) ∧
        (w = 0 ∨ (1 ≤ recycleCount (.inr sb) τ (τ.length - 1) ∧
          recycleCount (.inr sb) τ (w - 1) =
            recycleCount (.inr sb) τ (τ.length - 1) - 1)) := by
    rcases Nat.eq_zero_or_pos (recycleCount (.inr sb) τ (τ.length - 1)) with
      hR0 | hRpos
    · refine ⟨0, by omega, Config.run State.initial T, State.initial, ?_, rfl, rfl,
        ?_, Or.inl rfl⟩
      · have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen0]; exact hτ.1.2
      · have h00 : recycleCount (.inr sb) τ 0 = 0 := by unfold recycleCount; simp
        omega
    · obtain ⟨q, hqp, hq1, hq2⟩ := recycleCount_hits (.inr sb) τ hRpos (le_refl _)
      obtain ⟨D, Dn, hD, hDn, hrecD⟩ := recycle_step_of_count_lt (b := .inr sb)
        (τ := τ) (p := q) (by omega)
      have hstepD := chain_step hτ.1.1.subtrace hD hDn
      obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrecD
      refine ⟨q + 1, by omega, Dn, sD', hDn, hsD',
        arrivedAt_zero_after_recycle hstepD hrecD hsD', by omega,
        Or.inr ⟨hRpos, ?_⟩⟩
      simp only [Nat.add_sub_cancel]
      omega
  -- fiber times lie strictly beyond `w`
  have hlate : ∀ η' ∈ genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ), ∀ m',
      pointTime T τ η' = some m' → w < m' := by
    intro η' hη' m' hpt
    obtain ⟨c', m'', -, -, -, -, hpt', hm''1, -, hgm'⟩ := genFiber_time_data hτ hη'
    rw [hpt] at hpt'
    obtain rfl := Option.some.inj hpt'
    by_contra hcon
    rcases hwlow with rfl | ⟨hRpos, hw2⟩
    · omega
    · have hmono : recycleCount (.inr sb) τ (m' - 1) ≤
          recycleCount (.inr sb) τ (w - 1) :=
        recycleCount_mono (.inr sb) τ (by omega)
      omega
  -- the census at the final index counts the whole fiber
  have hcensus := arrived_census hτ hCw hsw hw0 hwrc hlate (τ.length - 1) hwp rfl
    (Config.done sd) sd hlast rfl
  have hAd' : Ad = (genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ)).countP
        (arriveBy T τ (τ.length - 1)) := by
    have h := hcensus
    simp only [State.arrivedAt] at h
    rw [hsb] at h
    simpa using h
  have hfilterall : (genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ)).countP
        (arriveBy T τ (τ.length - 1)) =
      (genFiber T τ (.inr sb)
        ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ)).length := by
    conv_rhs => rw [← List.countP_true]
    refine List.countP_congr fun x hx => ?_
    have hcmx := genFiber_mb_arrive hx
    obtain ⟨c', mx, -, -, -, -, hptx, hmx1, hmxlt, -⟩ := genFiber_time_data hτ hx
    have hmx' : mx ≤ τ.length - 1 := by omega
    simp [arriveBy, isArriveCmd, hcmx, Cmd.isArrive, hptx, hmx']
  omega

/-- Two program points with control parked at both in one configuration and on
the same thread coincide (given both index into their thread's program) — the
thread injectivity behind the parked-waiter clause. -/
theorem pointerAt_thread_inj {T : CTA} {C : Config} {η η' : ProgPoint}
    (h : pointerAt T η C) (h' : pointerAt T η' C) (hth : η.thread = η'.thread)
    (hidx : η.idx ≤ (T.prog η.thread).length)
    (hidx' : η'.idx ≤ (T.prog η'.thread).length) : η = η' := by
  unfold pointerAt at h h'
  rw [hth] at h hidx
  have hxid : η.idx = η'.idx := by omega
  have hxeta : η = ⟨η.thread, η.idx⟩ := rfl
  have hyeta : η' = ⟨η'.thread, η'.idx⟩ := rfl
  rw [hxeta, hyeta, hth, hxid]

/-- No recycle of `sb` can precede an index at which `sb` is uninitialized:
a recycle leaves the count `some`, which persists forever. -/
theorem recycleCount_zero_of_count_none {τ : List Config}
    (hchain : List.IsChain CTAStep τ) {j : Nat} {C : Config} {st : State}
    (hC : τ[j]? = some C) (hst : C.state? = some st)
    {sb : SharedBarrier} (hun : (st.BM sb).count = none) :
    recycleCount (.inr sb) τ j = 0 := by
  by_contra h
  have h1 : 1 ≤ recycleCount (.inr sb) τ j := by omega
  obtain ⟨p, hpj, hp0, hp1⟩ := recycleCount_hits (.inr sb) τ (le_refl 1) h1
  obtain ⟨D, D', hD, hD', hrec⟩ := recycle_step_of_count_lt
    (b := .inr sb) (τ := τ) (p := p) (by omega)
  have hstep := chain_step hchain hD hD'
  obtain ⟨sB, TB, IB, AB, nB, phB, hDeq, hbst, hfull, hpark, hD'eq⟩ :=
    stepRecyclesBarrier_elim_mb hstep hrec
  obtain ⟨-, sD', hsD'⟩ := exists_state_of_stepRecycles hrec
  have hcnt : (sD'.BM sb).count = some nB := by
    have h := hsD'
    rw [hD'eq] at h
    simp only [WeftCommon.Config.state?, Option.some.injEq] at h
    rw [← h]
    simp [Function.update_self]
  have hper := count_some_persists_le hchain j (p + 1) (by omega) hD' hsD' hcnt hC hst
  rw [hun] at hper
  exact absurd hper (by simp)

/-- Dual reading of the unique-initialization check: from
`okUniqueInitCheck = true`, any two `init_mb` points of one mbarrier
coincide. -/
theorem unique_init_of_check {T : CTA} {τ : List Config}
    (h : okUniqueInitCheck T τ = true) {ci cj : ProgPoint} {sb : SharedBarrier}
    {n n' : ℕ+} (hci : ci ∈ T.progPoints) (hcj : cj ∈ T.progPoints)
    (hcmdi : T.cmdAt ci = some (.init_mb sb n))
    (hcmdj : T.cmdAt cj = some (.init_mb sb n')) : ci = cj := by
  simp only [okUniqueInitCheck] at h
  have h1 := List.all_eq_true.mp h ci hci
  simp only [hcmdi] at h1
  have h2 := List.all_eq_true.mp h1 cj hcj
  simp only [hcmdj] at h2
  exact of_decide_eq_true h2

/-- Any `init_mb sb n` program point pins `CTA.initCountOf sb` to `n`, given the
unique-initialization check. -/
theorem initCountOf_eq_of_cmdAt {T : CTA} {τ : List Config}
    (huniq : okUniqueInitCheck T τ = true) {ip : ProgPoint} {sb : SharedBarrier}
    {n : ℕ+} (hip : ip ∈ T.progPoints) (hcm : T.cmdAt ip = some (.init_mb sb n)) :
    T.initCountOf sb = some n := by
  cases hio : T.initCountOf sb with
  | none =>
    exfalso
    unfold CTA.initCountOf at hio
    rw [List.findSome?_eq_none_iff] at hio
    have h := hio ip hip
    rw [hcm] at h
    simp at h
  | some n' =>
    obtain ⟨ip', hip', hcm'⟩ := initCountOf_some hio
    have hipeq := unique_init_of_check huniq hip' hip hcm' hcm
    subst hipeq
    rw [hcm'] at hcm
    have hn := Option.some.inj hcm
    simp only [Cmd.init_mb.injEq] at hn
    rw [hn.2]

/-- An initialized count is preceded by an `init_mb` head drop: walking back
from a `count = some` state, the first `none → some` transition is an
`mb_init` execution. -/
theorem exists_init_drop_of_count_some {T : CTA} {τ' : List Config}
    (hchain : List.IsChain CTAStep τ')
    (h0idx' : τ'[0]? = some (Config.run State.initial T)) {sb : SharedBarrier} :
    ∀ (j : Nat) (Cj : Config) (stj : State), τ'[j]? = some Cj →
      Cj.state? = some stj → ∀ {n : ℕ+}, (stj.BM sb).count = some n →
      ∃ (p : Nat) (i : ThreadId) (ninit : ℕ+) (D D' : Config) (rest : Prog),
        p + 1 ≤ j ∧ τ'[p]? = some D ∧ τ'[p + 1]? = some D' ∧
        D.progOf i = Cmd.init_mb sb ninit :: rest ∧ D'.progOf i = rest := by
  intro j
  induction j with
  | zero =>
    intro Cj stj hCj hstj n hcnt
    exfalso
    rw [h0idx'] at hCj
    obtain rfl := Option.some.inj hCj
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hstj
    subst hstj
    simp [State.initial, MBarrierState.uninitialized] at hcnt
  | succ p ih =>
    intro Cj stj hCj hstj n hcnt
    have hplt : p < τ'.length := by
      have := (List.getElem?_eq_some_iff.mp hCj).1
      omega
    obtain ⟨D, hD⟩ : ∃ D, τ'[p]? = some D := ⟨_, List.getElem?_eq_getElem hplt⟩
    have hstep := chain_step hchain hD hCj
    obtain ⟨sD, TD, rfl⟩ := hstep.source_run
    cases hsc : (sD.BM sb).count with
    | some n'' =>
      obtain ⟨p', i, ninit, D₁, D₂, rest, hp'p, hD₁, hD₂, hd, hd'⟩ :=
        ih _ sD hD rfl hsc
      exact ⟨p', i, ninit, D₁, D₂, rest, by omega, hD₁, hD₂, hd, hd'⟩
    | none =>
      -- the source is pristine (WF's count-none normalization), and the step
      -- initializes: it drops an `init_mb sb` head
      have hreach := reaches_of_chain_getElem hchain h0idx' p _ hD
      have hwfD := WF_of_reaches hreach
      have hun : sD.BM sb = MBarrierState.uninitialized := by
        rcases hsb : sD.BM sb with ⟨I', A', cnt', ph'⟩
        have hcnt' : cnt' = none := by
          rw [hsb] at hsc
          exact hsc
        subst hcnt'
        obtain ⟨hI0, hA0, hph0⟩ := hwfD.2.2.2.1 sb I' A' ph' hsb
        rw [hI0, hA0, hph0]
        rfl
      rcases uninit_step hstep rfl hstj hun with h | ⟨i, ninit, rest, hdrop, hdrop'⟩
      · exfalso
        rw [h] at hcnt
        simp [MBarrierState.uninitialized] at hcnt
      · exact ⟨p, i, ninit, _, _, rest, le_refl _, hD, hCj, hdrop, hdrop'⟩

/-- A use of `sb` in a *successful* CTA forces an `init_mb sb` program point to
exist: the use executed in the reference trace, which required the barrier
initialized, which required an initialization to have run. -/
theorem exists_init_point_of_use {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {u : ProgPoint} (hu : u ∈ T.progPoints) {sb : SharedBarrier}
    (huse : (T.cmdAt u).bind Cmd.usesMBarrier? = some sb) :
    ∃ ip ∈ T.progPoints, ∃ n₀ : ℕ+, T.cmdAt ip = some (.init_mb sb n₀) := by
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : u.idx < (T.prog u.thread).length := ((mem_progPoints_iff T u).mp hu).2
  obtain ⟨mu, hmu⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  obtain ⟨-, -, ju, D, D', hju, hD, hD', hDdrop, hD'drop⟩ := hmu
  -- decode the use command at the head of `D`
  obtain ⟨cu, hcu, hcuse⟩ : ∃ cu, T.cmdAt u = some cu ∧
      cu.usesMBarrier? = some sb := by
    cases hc : T.cmdAt u with
    | none => rw [hc] at huse; exact absurd huse (by simp)
    | some c =>
      rw [hc] at huse
      exact ⟨c, rfl, by simpa using huse⟩
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp
    (show ((Config.run State.initial T).progOf u.thread)[u.idx]? = some cu from hcu)
  have hDcons : D.progOf u.thread = cu ::
      ((Config.run State.initial T).progOf u.thread).drop (u.idx + 1) := by
    rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
  have hstepD := chain_step hτ.1.1.subtrace hD hD'
  -- the pre-state is initialized, whichever use it is
  obtain ⟨sD, TD, hDeq, ID, AD, nD, phD, hbD⟩ :
      ∃ sD TD, D = Config.run sD TD ∧ ∃ I A n ph, sD.BM sb = ⟨I, A, some n, ph⟩ := by
    cases cu with
    | arrive_mb sb' =>
      have hsb' : sb' = sb := by simpa [Cmd.usesMBarrier?] using hcuse
      subst hsb'
      obtain ⟨sD, TD, ID, AD, nD, phD, hDeq, hbD⟩ :=
        arrive_mb_drop_initialized hstepD hDcons hD'drop
      exact ⟨sD, TD, hDeq, ID, AD, nD, phD, hbD⟩
    | wait_mb sb' ph =>
      have hsb' : sb' = sb := by simpa [Cmd.usesMBarrier?] using hcuse
      subst hsb'
      obtain ⟨sD, TD, ID, AD, nD, phD, hDeq, hbD⟩ :=
        wait_mb_drop_initialized hstepD hDcons hD'drop
      exact ⟨sD, TD, hDeq, ID, AD, nD, phD, hbD⟩
    | read l => simp [Cmd.usesMBarrier?] at hcuse
    | write l => simp [Cmd.usesMBarrier?] at hcuse
    | arrive_nb nb n => simp [Cmd.usesMBarrier?] at hcuse
    | sync_nb nb n => simp [Cmd.usesMBarrier?] at hcuse
    | init_mb sb' n => simp [Cmd.usesMBarrier?] at hcuse
  subst hDeq
  have h0τ : τ[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact hτ.1.2
  obtain ⟨p, i, ninit, D₁, D₂, rest, hp1, hD₁, hD₂, hd, hd'⟩ :=
    exists_init_drop_of_count_some hτ.1.1.subtrace h0τ ju _ sD hD rfl
      (show (sD.BM sb).count = some nD by rw [hbD])
  have hsufi : D₁.progOf i <:+ (Config.run State.initial T).progOf i :=
    progOf_suffix_index_le hτ.1.1.subtrace i h0τ (Nat.zero_le p) hD₁
  have hcmdi := cmd_at_last hsufi hd
  exact ⟨_, mem_progPoints_of_cmdAt T hcmdi, ninit, hcmdi⟩

/-- An initialized mbarrier in the challenger trace means the *unique*
`init_mb sb` point has executed there (with a computed time). -/
theorem exists_init_time_of_count_some {T : CTA} {τ τ' : List Config}
    (huniq : okUniqueInitCheck T τ = true)
    (hchain : List.IsChain CTAStep τ')
    (h0 : τ'.head? = some (Config.run State.initial T))
    {Cl : Config} (hlast : τ'.getLast? = some Cl)
    {j : Nat} {Cj : Config} {stj : State} (hCj : τ'[j]? = some Cj)
    (hstj : Cj.state? = some stj)
    {sb : SharedBarrier} {n : ℕ+} (hcnt : (stj.BM sb).count = some n)
    {ip : ProgPoint} (hipmem : ip ∈ T.progPoints) {n' : ℕ+}
    (hcmdip : T.cmdAt ip = some (.init_mb sb n')) :
    ∃ m, pointTime T τ' ip = some m := by
  have h0idx' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact h0
  obtain ⟨p, i, ninit, D, D', rest, hp1, hD, hD', hd, hd'⟩ :=
    exists_init_drop_of_count_some hchain h0idx' j _ stj hCj hstj hcnt
  have hsufi : D.progOf i <:+ (Config.run State.initial T).progOf i :=
    progOf_suffix_index_le hchain i h0idx' (Nat.zero_le p) hD
  have hcmdi := cmd_at_last hsufi hd
  have hipeq : (⟨i, ((Config.run State.initial T).progOf i).length -
      (D.progOf i).length⟩ : ProgPoint) = ip :=
    unique_init_of_check huniq (mem_progPoints_of_cmdAt T hcmdi) hipmem hcmdi hcmdip
  -- `ip`'s thread has moved past it by the last configuration
  have hjlt : j < τ'.length := (List.getElem?_eq_some_iff.mp hCj).1
  have hlastidx' : τ'[τ'.length - 1]? = some Cl := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hsuflast : Cl.progOf i <:+ D'.progOf i :=
    progOf_suffix_index_le hchain i hD' (show p + 1 ≤ τ'.length - 1 by omega)
      hlastidx'
  have hlenlast : (Cl.progOf i).length ≤ rest.length := by
    have := suffix_length_le hsuflast
    rw [hd'] at this
    exact this
  have hlenD : (D.progOf i).length = rest.length + 1 := by rw [hd]; simp
  have hlenD_le : (D.progOf i).length ≤
      ((Config.run State.initial T).progOf i).length := suffix_length_le hsufi
  rw [← hipeq]
  refine exists_pointTime_of_passed hchain h0 hlast
    (i := i)
    (k := ((Config.run State.initial T).progOf i).length - (D.progOf i).length)
    (by
      have hTlen : ((Config.run State.initial T).progOf i).length =
        (T.prog i).length := rfl
      omega) ?_
  have hTlen : ((Config.run State.initial T).progOf i).length =
      (T.prog i).length := rfl
  omega

/-! ## The conformance invariant (soundness, §5.2.6)

`Conforms T τ τ'`: the challenger trace `τ'` agrees with the successful
reference trace `τ`. The named-barrier clauses port from the named library
(with the mb 0-indexed fiber: the open round of `b` is
`recycleCount b τ' (|τ'| - 1)`); the mbarrier state clause is new
(`MBarrierConforms`), including the **parked-waiter clause** — the mechanized
form of the paper's "prove separately" remark at MBarrier-Recycle. -/

/-- **Named-barrier state clause** of `Conforms` (paper §5.2.6), for one
barrier `nb`: in the last configuration `C` (state `s`) of the challenger
trace `τ'`, with `r` recycles of `nb` so far and `F := genFiber T τ (.inl nb) r`
the current fiber,

* `count` — if `nb` is configured, its count is the parameter of every member
  of `F`;
* `arrived` — the arrival count is the number of `arrive_nb`s of `F` already
  executed;
* `synced` — the parked list holds exactly the threads of `F`'s `sync_nb`s
  whose control is parked at them *and which are disabled*;
* `unconfigured` — a `⊥` count means the pristine unconfigured state. -/
def BarrierConforms (T : CTA) (τ τ' : List Config) (C : Config) (s : State)
    (nb : NamedBarrier) : Prop :=
  (∀ n : ℕ+, (s.BN nb).count = some n →
    ∀ η ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ),
      (T.cmdAt η).bind Cmd.count? = some n) ∧
  ((s.BN nb).arrived =
    ((genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter fun η =>
      isArriveCmd T η && (pointTime T τ' η).isSome).length) ∧
  (∀ i, i ∈ (s.BN nb).synced ↔
    ∃ η ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ),
      η.thread = i ∧ (∃ n : ℕ+, T.cmdAt η = some (.sync_nb nb n)) ∧
        pointerAt T η C ∧ s.E i = false) ∧
  ((s.BN nb).count = none → s.BN nb = NamedBarrierState.unconfigured)

/-- **Mbarrier state clause** of `Conforms` (new; paper §5.2.6 extended), for
one mbarrier `sb`, with `r` the recycles of `sb` in `τ'` so far:

* `count` — an initialized count is *the* count of `sb`'s unique `init_mb`
  (`CTA.initCountOf`);
* `arrived` — the arrival count is the number of current-round fiber members
  (all `arrive_mb`s) already executed — the paper's "we only make sure that the
  arrival counts conform"; waiters do **not** count;
* `waiting` — the **parked-waiter clause** (beyond the paper's invariant, the
  mechanized form of its "prove separately" remark): every parked waiter is a
  disabled thread whose control sits at a `wait_mb sb _` point whose *reference*
  generation is the current round `r` — established by the Wait-Block case,
  consumed at MBarrier-Recycle to give the woken waits their `gen_eq`;
* `uninitialized` — a `⊥` count means the pristine uninitialized state.

(No phase clause: `phase = phaseAfter r` holds on any trace from the initial
configuration — `phase_eq_phaseAfter` — so it is derived, not carried.) -/
def MBarrierConforms (T : CTA) (τ τ' : List Config) (C : Config) (s : State)
    (sb : SharedBarrier) : Prop :=
  (∀ n : ℕ+, (s.BM sb).count = some n → T.initCountOf sb = some n) ∧
  ((s.BM sb).arrived =
    ((genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter fun η =>
      isArriveCmd T η && (pointTime T τ' η).isSome).length) ∧
  (∀ i ∈ (s.BM sb).waiting, ∃ η, η ∈ T.progPoints ∧ η.thread = i ∧
    (∃ ph, T.cmdAt η = some (.wait_mb sb ph)) ∧ pointerAt T η C ∧
    s.E i = false ∧
    pointGen T τ η =
      some ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)) ∧
  ((s.BM sb).count = none → s.BM sb = MBarrierState.uninitialized)

/-- **The conformance invariant** `Conforms(τ, τ')` (paper §5.2.6): the
challenger trace `τ'` agrees with the successful reference trace `τ`.
Clause 0: `τ'` has not errored. Clause 1: executed instructions carry their
reference generations. Clauses 2/2m: each barrier's state is the image of its
current fiber's progress, per kind. Clause 3: `initRelation` edges with an
executed target have an executed source, no later. Clause 4: closed rounds are
complete. -/
structure Conforms (T : CTA) (τ τ' : List Config) : Prop where
  /-- Clause 0: the challenger trace has not reached the error configuration. -/
  no_err : ∀ T'', τ'.getLast? ≠ some (Config.err T'')
  /-- Clause 1: generation agreement for every executed instruction. -/
  gen_eq : ∀ η ∈ T.progPoints, ∀ m, pointTime T τ' η = some m →
    pointGen T τ' η = pointGen T τ η
  /-- Clause 2: each named barrier's state is the image of its current fiber's
  progress. -/
  state : ∀ C, τ'.getLast? = some C → ∀ s, C.state? = some s →
    ∀ nb, BarrierConforms T τ τ' C s nb
  /-- Clause 2m: each mbarrier's state conforms (`MBarrierConforms`). -/
  mstate : ∀ C, τ'.getLast? = some C → ∀ s, C.state? = some s →
    ∀ sb, MBarrierConforms T τ τ' C s sb
  /-- Clause 3: generating-edge soundness inside `τ'`. -/
  edge_sound : ∀ x y, (x, y) ∈ initRelation T τ →
    ∀ m, pointTime T τ' y = some m → ∃ m' ≤ m, pointTime T τ' x = some m'
  /-- Clause 4: **closed rounds are complete** — once `b` has recycled `g + 1`
  times in `τ'`, every member of the reference fiber `F_g(b)` has executed. -/
  rounds_complete : ∀ (b : NamedBarrier ⊕ SharedBarrier) (g : ℕ),
    g + 1 ≤ recycleCount b τ' (τ'.length - 1) →
    ∀ η ∈ genFiber T τ b (g : ℤ), ∃ m, pointTime T τ' η = some m
  /-- Clause 5: **closed mbarrier rounds were full** — once `sb` has recycled
  `g + 1` times in `τ'`, the round-`g` fiber holds exactly the barrier's
  initialized capacity. Established at each `mb_recycle` by the clause-2m
  census; consumed by the wait-targeting lemmas' fill conditions. -/
  rounds_full : ∀ (sb : SharedBarrier) (g : ℕ),
    g + 1 ≤ recycleCount (.inr sb) τ' (τ'.length - 1) →
    ∀ n : ℕ+, T.initCountOf sb = some n →
    (genFiber T τ (.inr sb) (g : ℤ)).length = (n : ℕ)

/-- **The closure lift** (clause 3 for `happensBefore` paths): walking an
`R`-path backward from an executed endpoint pulls every node on it — in
particular the source — into the executed part of `τ'`, no later. -/
theorem Conforms.happensBefore_sound {T : CTA} {τ τ' : List Config}
    (h : Conforms T τ τ') {x y : ProgPoint} (hxy : happensBefore T τ x y) :
    ∀ m, pointTime T τ' y = some m → ∃ m' ≤ m, pointTime T τ' x = some m' := by
  induction hxy with
  | refl => exact fun m hy => ⟨m, le_rfl, hy⟩
  | tail _hab hbc ih =>
    intro m hy
    obtain ⟨mb, hmb_le, hmb⟩ := h.edge_sound _ _ hbc _ hy
    obtain ⟨mx, hmx_le, hmx⟩ := ih _ hmb
    exact ⟨mx, hmx_le.trans hmb_le, hmx⟩

/-- **Base case of Theorem 6**: the singleton initial trace conforms — nothing
has executed, no recycles have happened, and every barrier of either kind is
pristine. -/
theorem conforms_init (T : CTA) (τ : List Config) :
    Conforms T τ [Config.run State.initial T] := by
  have hpt : ∀ η, pointTime T [Config.run State.initial T] η = none := by
    intro η; simp [pointTime]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 0: the singleton's last configuration is `run`, not `err`
    intro T'' h
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    exact absurd h (by simp)
  · -- clause 1: vacuous — nothing has a time yet
    intro η _ m hm
    rw [hpt η] at hm
    exact absurd hm (by simp)
  · -- clause 2: the initial state is pristine and the fiber has no progress
    intro C hC s hs nb
    simp only [List.getLast?_singleton, Option.some.injEq] at hC
    subst hC
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    refine ⟨?_, ?_, ?_, fun _ => rfl⟩
    · intro n hn
      exact absurd hn (by simp [State.initial, NamedBarrierState.unconfigured])
    · simp only [hpt, Option.isSome_none, Bool.and_false, List.filter_false,
        List.length_nil]
      rfl
    · intro i
      simp only [State.initial, NamedBarrierState.unconfigured, List.not_mem_nil,
        false_iff]
      rintro ⟨η, -, rfl, -, -, hE⟩
      simp at hE
  · -- clause 2m: the initial mbarrier state is pristine
    intro C hC s hs sb
    simp only [List.getLast?_singleton, Option.some.injEq] at hC
    subst hC
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    refine ⟨?_, ?_, ?_, fun _ => rfl⟩
    · intro n hn
      exact absurd hn (by simp [State.initial, MBarrierState.uninitialized])
    · simp only [hpt, Option.isSome_none, Bool.and_false, List.filter_false,
        List.length_nil]
      rfl
    · intro i hi
      exact absurd hi (by simp [State.initial, MBarrierState.uninitialized])
  · -- clause 3: vacuous — no target has a time yet
    intro x y _ m hm
    rw [hpt y] at hm
    exact absurd hm (by simp)
  · -- clause 4: vacuous — nothing has recycled yet
    intro b g hgle η hη
    exfalso
    have h0 : recycleCount b [Config.run State.initial T]
        ([Config.run State.initial T].length - 1) = 0 := by
      unfold recycleCount; simp
    omega
  · -- clause 5: vacuous — nothing has recycled yet
    intro sb g hgle n hinit
    exfalso
    have h0 : recycleCount (.inr sb) [Config.run State.initial T]
        ([Config.run State.initial T].length - 1) = 0 := by
      unfold recycleCount; simp
    omega

/-- An initialized count is witnessed by a state of the *reference* trace: the
unique `init_mb sb n` executes in the successful `τ`, and right after its step
the count is `some n`. Bridges `CTA.initCountOf` to the `genFiber_length_mb`
capacity arguments. -/
theorem exists_count_state_of_initCountOf {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {sb : SharedBarrier} {n : ℕ+} (hinit : T.initCountOf sb = some n) :
    ∃ (m : Nat) (C : Config) (st : State),
      τ[m]? = some C ∧ C.state? = some st ∧ (st.BM sb).count = some n := by
  obtain ⟨ip, hipmem, hipcm⟩ := initCountOf_some hinit
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidx : ip.idx < (T.prog ip.thread).length :=
    ((mem_progPoints_iff T ip).mp hipmem).2
  obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  obtain ⟨-, -, j, D, D', hjm, hD, hD', hDdrop, hD'drop⟩ := hm
  have hcmg : ((Config.run State.initial T).progOf ip.thread)[ip.idx]? =
      some (Cmd.init_mb sb n) := hipcm
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hcmg
  have hDcons : D.progOf ip.thread = Cmd.init_mb sb n ::
      ((Config.run State.initial T).progOf ip.thread).drop (ip.idx + 1) := by
    rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
  have hstepD := chain_step hτ.1.1.subtrace hD hD'
  obtain ⟨s', T', hD'eq, hcnt⟩ := init_drop_target_initialized hstepD hDcons hD'drop
  exact ⟨j + 1, D', s', hD', by rw [hD'eq]; rfl, hcnt⟩

/-- **The round-targeting lemma** — the `k = g` core of Theorem 6's induction
step for *registrants*: in a conforming trace whose last configuration
satisfies the all-barriers-under-full guards, a thread whose control sits at a
registrant `η` on `b` can only be facing round `pointGen T τ η` (the open round
index `r` equals `η`'s reference generation `g`).

* `g < r` ("late") is impossible: round `g` closed, so clause 4 says `η` itself
  executed — but its pointer is still at `η`.
* `r < g` ("early") is impossible: `g ≥ 1`, the checker supplies `η.idx ≥ 1`
  and, for every `c1 ∈ F_{g-1}`, a path `c1 ⤳ pred(η)`; `pred(η)` executed, so
  the closure lift forces each `c1` executed at τ'-depth `g - 1`; hence
  `r = g - 1` and the census makes the open round hold the whole fiber
  `F_{g-1}` — full, contradicting the guard (named: `|I| + A = n`; shared: the
  fiber is all-`arrive`s and `A = n` with `n` the initialized capacity). -/
theorem conforms_reg_round {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    (hguard : ∀ nb', s.BN nb' = NamedBarrierState.unconfigured ∨
      ∃ I A n, s.BN nb' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
    (hmguard : ∀ sb', s.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A n ph, s.BM sb' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
    {η : ProgPoint} (hmem : η ∈ T.progPoints) {c : Cmd}
    (hcm : T.cmdAt η = some c) (hreg : c.isRegistrant = true)
    {b : NamedBarrier ⊕ SharedBarrier} (hbar : c.barrier? = some b)
    (hat : pointerAt T η (Config.run s Tc)) :
    pointGen T τ η = some ((recycleCount b τ' (τ'.length - 1) : ℕ) : ℤ) := by
  obtain ⟨hokReg, hokWait, hokInit, hokUniq⟩ := check_true_parts hcheck
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidxL : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hidxL
  have hgτ := pointGen_registrant_eq_of_time hcm hreg hbar hmτ
  set gN := recycleCount b τ (mτ - 1) with hgNdef
  have hmτlt : mτ < τ.length := by
    obtain ⟨-, -, j₀, -, C₂, hj₀, -, hC₂, -, -⟩ := hmτ
    have := (List.getElem?_eq_some_iff.mp hC₂).1
    omega
  have hchain' := htr.1
  have h0' : τ'.head? = some (Config.run State.initial T) := htr.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hat' : (Tc.prog η.thread).length = (T.prog η.thread).length - η.idx := hat
  have hηreg : registrantGen T τ η = some (b, (gN : ℤ)) := by
    unfold registrantGen
    simp [hcm, hgτ, if_pos hreg, hbar]
  have hηfib : η ∈ genFiber T τ b (gN : ℤ) := mem_genFiber.mpr ⟨hmem, hηreg⟩
  set r := recycleCount b τ' (τ'.length - 1) with hrdef
  rcases Nat.lt_trichotomy gN r with hlt | heq | hgt
  · -- LATE: `gN < r` — the closed round consumed `η`, but its pointer is still at `η`
    exfalso
    obtain ⟨m, hpt⟩ := hconf.rounds_complete b gN (by omega) η hηfib
    obtain ⟨hm1, hmlt, -, C₁, C₂, hC₁, hC₂, -, hdrop2⟩ := pointTime_spec hchain' h0' hpt
    have hsuf := progOf_suffix_index_le hchain' η.thread hC₂
      (show m ≤ τ'.length - 1 by omega) hlastidx
    have hle := suffix_length_le hsuf
    rw [hdrop2] at hle
    simp only [List.length_drop] at hle
    have hcast : ((Config.run s Tc).progOf η.thread).length =
        (Tc.prog η.thread).length := rfl
    omega
  · rw [hgτ, heq]
  · -- EARLY: `r < gN`
    exfalso
    have hg1 : 1 ≤ gN := by omega
    obtain ⟨c0, hc0⟩ := genFiber_nonempty_of_succ hτ
      (show η ∈ genFiber T τ b (((gN - 1) + 1 : ℕ) : ℤ) from by
        rw [show gN - 1 + 1 = gN by omega]; exact hηfib)
    obtain ⟨hc0mem, hc0reg⟩ := mem_genFiber.mp hc0
    have hcast1 : ((gN - 1 : ℕ) : ℤ) + 1 = (gN : ℤ) := by omega
    have hηreg' : registrantGen T τ η = some (b, ((gN - 1 : ℕ) : ℤ) + 1) := by
      rw [hcast1]; exact hηreg
    have hidx1 : 1 ≤ η.idx := idx_pos_of_check hokReg hc0mem hc0reg hmem hηreg'
    -- `pred(η)` has executed in `τ'` (the pointer moved past it)
    obtain ⟨m3, hptc3⟩ : ∃ m3, pointTime T τ' ⟨η.thread, η.idx - 1⟩ = some m3 := by
      refine exists_pointTime_of_passed hchain' h0' hlast (by omega) ?_
      change (Tc.prog η.thread).length + (η.idx - 1 + 1) ≤ (T.prog η.thread).length
      omega
    -- every `F_{gN-1}` member executed in `τ'`, at τ'-recycle-depth `gN - 1`
    have hall : ∀ c1 ∈ genFiber T τ b ((gN - 1 : ℕ) : ℤ), ∃ m1, m1 ≤ m3 ∧
        pointTime T τ' c1 = some m1 ∧ recycleCount b τ' (m1 - 1) = gN - 1 := by
      intro c1 hc1
      obtain ⟨hc1mem, hc1reg⟩ := mem_genFiber.mp hc1
      have hpath := happensBefore_of_check hokReg hc1mem hc1reg hmem hηreg' hidx1
      obtain ⟨m1, hm1le, hm1⟩ := hconf.happensBefore_sound hpath m3 hptc3
      refine ⟨m1, hm1le, hm1, ?_⟩
      have hgen1 : pointGen T τ' c1 = pointGen T τ c1 := hconf.gen_eq c1 hc1mem m1 hm1
      obtain ⟨c1c, hc1cm, hc1isreg, hc1bar, hc1pg⟩ := registrantGen_some hc1reg
      have hunf := pointGen_eq_of_pointTime hc1cm hc1bar hm1
      rw [genValue_of_isRegistrant hc1isreg] at hunf
      rw [hunf, hc1pg] at hgen1
      have := Option.some.inj hgen1
      omega
    -- the open round sits exactly at `gN - 1`
    have hrg : r = gN - 1 := by
      obtain ⟨m1, -, hm1, hrc1⟩ := hall c0 hc0
      have hm1lt : m1 < τ'.length := (pointTime_spec hchain' h0' hm1).2.1
      have hmono := recycleCount_mono b τ' (show m1 - 1 ≤ τ'.length - 1 by omega)
      omega
    -- `F_{gN-1}` is complete in the reference
    have hτcomplete : (gN - 1) + 1 ≤ recycleCount b τ (τ.length - 1) := by
      have hmono := recycleCount_mono b τ (show mτ - 1 ≤ τ.length - 1 by omega)
      omega
    cases b with
    | inl nb =>
      -- a sync in `F_{gN-1}` would already have recycled `nb` past `r`
      have hnosync : ∀ c1 ∈ genFiber T τ (.inl nb) ((gN - 1 : ℕ) : ℤ), ∀ nn : ℕ+,
          T.cmdAt c1 ≠ some (.sync_nb nb nn) := by
        intro c1 hc1 nn hcmx
        obtain ⟨m1, hm1le, hm1, hrc1⟩ := hall c1 hc1
        obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ := pointTime_sync_recycles hchain' h0' hm1 hcmx
        obtain ⟨hm1a, hm1lt, -⟩ := pointTime_spec hchain' h0' hm1
        have hCC' : τ'[m1 - 1 + 1]? = some C₂ := by
          rw [show m1 - 1 + 1 = m1 by omega]; exact hC₂
        have hsucc := recycleCount_succ_of_recycle (.inl nb) τ' hC₁ hCC' hrec
        have hmono := recycleCount_mono (.inl nb) τ'
          (show m1 - 1 + 1 ≤ τ'.length - 1 by omega)
        omega
      -- the census filter is the whole fiber
      have hfilter : (genFiber T τ (.inl nb) ((gN - 1 : ℕ) : ℤ)).filter (fun η' =>
          isArriveCmd T η' && (pointTime T τ' η').isSome) =
          genFiber T τ (.inl nb) ((gN - 1 : ℕ) : ℤ) := by
        rw [List.filter_eq_self]
        intro c1 hc1
        obtain ⟨m1, -, hm1, -⟩ := hall c1 hc1
        rcases genFiber_nb_cases hc1 with ⟨nn, hcmx⟩ | ⟨nn, hcmx⟩
        · simp [isArriveCmd, hcmx, Cmd.isArrive, hm1]
        · exact absurd hcmx (hnosync c1 hc1 nn)
      obtain ⟨nn₀, hcm₀⟩ : ∃ nn₀ : ℕ+, T.cmdAt c0 = some (.arrive_nb nb nn₀) := by
        rcases genFiber_nb_cases hc0 with ⟨nn, hcmx⟩ | ⟨nn, hcmx⟩
        · exact ⟨nn, hcmx⟩
        · exact absurd hcmx (hnosync c0 hc0 nn)
      have hlen := genFiber_length hτ hτcomplete hc0
        (show (T.cmdAt c0).bind Cmd.count? = some nn₀ from by rw [hcm₀]; rfl)
      obtain ⟨hcount, harr, -, -⟩ := hconf.state _ hlast s rfl nb
      rw [← hrdef, hrg] at harr hcount
      rw [hfilter, hlen] at harr
      rcases hguard nb with hbu | ⟨I', A', n', hbeq, hltn⟩
      · rw [hbu] at harr
        have hpos := nn₀.pos
        simp [NamedBarrierState.unconfigured] at harr
        omega
      · have hn' : (T.cmdAt c0).bind Cmd.count? = some n' :=
          hcount n' (by rw [hbeq]) c0 hc0
        rw [hcm₀] at hn'
        simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hn'
        rw [hbeq] at harr
        have harr' : A' = (nn₀ : ℕ) := harr
        have hn'' : (nn₀ : ℕ) = (n' : ℕ) := by rw [hn']
        omega
    | inr sb =>
      -- the fiber is all-`arrive`s, so the census filter is the whole fiber
      have hfilter : (genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ)).filter (fun η' =>
          isArriveCmd T η' && (pointTime T τ' η').isSome) =
          genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ) := by
        rw [List.filter_eq_self]
        intro c1 hc1
        obtain ⟨m1, -, hm1, -⟩ := hall c1 hc1
        have hcmx := genFiber_mb_arrive hc1
        simp [isArriveCmd, hcmx, Cmd.isArrive, hm1]
      obtain ⟨hcount, harr, hwait, -⟩ := hconf.mstate _ hlast s rfl sb
      rw [← hrdef, hrg] at harr
      rw [hfilter] at harr
      rcases hmguard sb with hbu | ⟨I', A', n', ph', hbeq, hltn⟩
      · -- uninitialized: zero arrivals yet a nonempty, fully-executed fiber
        rw [hbu] at harr
        have hpos : 0 < (genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ)).length :=
          List.length_pos_of_mem hc0
        simp [MBarrierState.uninitialized] at harr
        omega
      · -- initialized: the count pins the capacity; the round is full
        have hinitc : T.initCountOf sb = some n' := hcount n' (by rw [hbeq])
        obtain ⟨mI, CI, stI, hCI, hstI, hcntI⟩ :=
          exists_count_state_of_initCountOf hτ hinitc
        have hlen := genFiber_length_mb hτ hτcomplete hCI hstI hcntI
        rw [hbeq] at harr
        have harr' : A' = (genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ)).length := harr
        omega

/-- **The fullness pigeonhole** (named): in a conforming trace whose last
configuration holds a *full* round of `nb`, the round has consumed the entire
current fiber — every `arrive_nb` member has executed, and every `sync_nb`
member is parked (its thread in the synced list, control at the member).
Counting: clause 2 bounds the parked threads by the fiber's syncs
(thread-image) and the arrival counter by its executed arrives; fullness plus
`|F| = n₀` forces both bounds tight. A full *partial* round is impossible
outright (all-`arrive`s yet strictly under-full in the reference). -/
theorem conforms_full_fiber {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    {nb : NamedBarrier} {I : List ThreadId} {A : Nat} {n₀ : ℕ+}
    (hb : s.BN nb = ⟨I, A, some n₀⟩) (hfull : I.length + A = (n₀ : ℕ)) :
    ∀ η ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ),
      ((∃ nn : ℕ+, T.cmdAt η = some (.arrive_nb nb nn)) →
        ∃ m, pointTime T τ' η = some m) ∧
      (∀ nn : ℕ+, T.cmdAt η = some (.sync_nb nb nn) →
        η.thread ∈ I ∧ pointerAt T η (Config.run s Tc)) := by
  obtain ⟨hcount, harr, hsync, -⟩ := hconf.state _ hlast s rfl nb
  have hparam : ∀ x ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ),
      (T.cmdAt x).bind Cmd.count? = some n₀ :=
    fun x hx => hcount n₀ (by rw [hb]) x hx
  have harr' : A = ((genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
      fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
    rw [hb] at harr
    exact harr
  -- the fiber is nonempty (the full round has registrants, all of them members)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ genFiber T τ (.inl nb)
      ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
    by_contra hno
    push Not at hno
    have hFnil : genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) = [] := by
      cases hFcase : genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) with
      | nil => rfl
      | cons a l => exact absurd (hFcase ▸ List.mem_cons_self ..) (hno a)
    have hI0 : I = [] := by
      cases hI : I with
      | nil => rfl
      | cons t I'' =>
        exfalso
        have htI : t ∈ (s.BN nb).synced := by
          rw [hb, hI]; exact List.mem_cons_self ..
        obtain ⟨x, hxF, -, -, -, -⟩ := (hsync t).mp htI
        rw [hFnil] at hxF
        simp at hxF
    rw [hFnil] at harr'
    simp at harr'
    have hpos := n₀.pos
    rw [hI0] at hfull
    simp at hfull
    omega
  by_cases hcomp : recycleCount (.inl nb) τ' (τ'.length - 1) + 1 ≤
      recycleCount (.inl nb) τ (τ.length - 1)
  case neg =>
    -- a full partial round is impossible: all-`arrive`s yet strictly under-full
    exfalso
    have hRge : recycleCount (.inl nb) τ' (τ'.length - 1) ≤
        recycleCount (.inl nb) τ (τ.length - 1) := by
      obtain ⟨c', mx, -, -, -, -, -, hmx1, hmxlt, hgmx⟩ := genFiber_time_data hτ hx₀
      have := recycleCount_mono (.inl nb) τ (show mx - 1 ≤ τ.length - 1 by omega)
      omega
    have hreq : recycleCount (.inl nb) τ' (τ'.length - 1) =
        recycleCount (.inl nb) τ (τ.length - 1) := by omega
    rw [hreq] at hx₀ harr' hparam
    have hlt := genFiber_partial_length_lt hτ hx₀ (hparam x₀ hx₀)
    have hI0 : I = [] := by
      cases hI : I with
      | nil => rfl
      | cons t I'' =>
        exfalso
        have htI : t ∈ (s.BN nb).synced := by
          rw [hb, hI]; exact List.mem_cons_self ..
        obtain ⟨x, hxF, -, hsx, -, -⟩ := (hsync t).mp htI
        obtain ⟨nx, hcx⟩ := hsx
        rw [hreq] at hxF
        exact genFiber_partial_no_sync hτ hxF nx hcx
    have hAle : A ≤ (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ (τ.length - 1) : ℕ) : ℤ)).length := by
      rw [harr']
      exact List.length_filter_le _ _
    rw [hI0] at hfull
    simp at hfull
    omega
  case pos =>
    -- the complete round: `|F| = n₀`, and the two counting bounds are tight
    have hlen := genFiber_length hτ hcomp hx₀ (hparam x₀ hx₀)
    have hndF : ((genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
        (isSyncCmd T)).Nodup :=
      (genFiber_nodup T τ (.inl nb) _).filter _
    have h0 : τ'[0]? = some (Config.run State.initial T) := by
      have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
      rw [hgen0]; exact htr.2
    have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
      rw [← List.getLast?_eq_getElem?]; exact hlast
    have hreach := reaches_of_chain_getElem htr.1 h0 (τ'.length - 1) _ hlastidx
    have hwf := WF_of_reaches hreach
    have hndI : I.Nodup := by
      have h := hwf.2.2.2.2.2.1 (Sum.inl nb)
      have hbk : s.blocked (Sum.inl nb) = I := by
        simp [State.blocked, hb]
      rwa [hbk] at h
    have hcardI : I.toFinset.card = I.length := List.toFinset_card_of_nodup hndI
    have hcardsync : ((genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
        (isSyncCmd T)).toFinset.card =
        (genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
          (isSyncCmd T) := by
      rw [List.toFinset_card_of_nodup hndF]
      exact List.countP_eq_length_filter.symm
    have hIsub : I.toFinset ⊆
        (((genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
          (isSyncCmd T)).toFinset.image ProgPoint.thread) := by
      intro i hi
      have hiI : i ∈ (s.BN nb).synced := by
        rw [hb]; exact List.mem_toFinset.mp hi
      obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hiI
      rw [Finset.mem_image]
      refine ⟨x, ?_, hthx⟩
      rw [List.mem_toFinset, List.mem_filter]
      obtain ⟨nx, hcx⟩ := hsx
      exact ⟨hxF, by simp [isSyncCmd, hcx]⟩
    have hIle : I.length ≤
        (genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
          (isSyncCmd T) := by
      calc I.length = I.toFinset.card := hcardI.symm
        _ ≤ _ := Finset.card_le_card hIsub
        _ ≤ _ := Finset.card_image_le
        _ = _ := hcardsync
    have harrc : A = (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
        (fun η => isArriveCmd T η && (pointTime T τ' η).isSome) := by
      rw [List.countP_eq_length_filter]
      exact harr'
    have hAle : A ≤ (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
        (isArriveCmd T) := by
      rw [harrc]
      exact List.countP_mono_left fun x hx h => by
        simp only [Bool.and_eq_true] at h
        exact h.1
    have hpartition : (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).length =
        (genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
          (isSyncCmd T) +
        (genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
          (isArriveCmd T) := by
      rw [List.length_eq_countP_add_countP (isSyncCmd T)]
      congr 1
      refine List.countP_congr fun x hx => ?_
      rcases genFiber_nb_cases hx with ⟨nx, hcmx⟩ | ⟨nx, hcmx⟩ <;>
        simp [isSyncCmd, isArriveCmd, hcmx, Cmd.isArrive]
    have hIeq : I.length =
        (genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
          (isSyncCmd T) := by
      omega
    have hAeq : A = (genFiber T τ (.inl nb)
        ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
        (isArriveCmd T) := by
      omega
    intro η hη
    refine ⟨?_, ?_⟩
    · rintro ⟨nn, hcm⟩
      have hqp := countP_eq_all
        (l := genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ))
        (p := fun x => isArriveCmd T x && (pointTime T τ' x).isSome)
        (q := isArriveCmd T)
        (fun x hx h => by
          simp only [Bool.and_eq_true] at h
          exact h.1)
        (by omega) η hη (by simp [isArriveCmd, hcm, Cmd.isArrive])
      simp only [Bool.and_eq_true] at hqp
      obtain ⟨-, hsome⟩ := hqp
      exact Option.isSome_iff_exists.mp hsome
    · intro nn hcm
      have himg : (((genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
          (isSyncCmd T)).toFinset.image ProgPoint.thread) = I.toFinset := by
        symm
        refine Finset.eq_of_subset_of_card_le hIsub ?_
        calc (((genFiber T τ (.inl nb)
              ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
              (isSyncCmd T)).toFinset.image ProgPoint.thread).card
            ≤ _ := Finset.card_image_le
          _ = _ := hcardsync
          _ = I.length := hIeq.symm
          _ = I.toFinset.card := hcardI.symm
      have hηimg : η.thread ∈
          (((genFiber T τ (.inl nb)
            ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
            (isSyncCmd T)).toFinset.image ProgPoint.thread) := by
        rw [Finset.mem_image]
        refine ⟨η, ?_, rfl⟩
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨hη, by simp [isSyncCmd, hcm]⟩
      have hηI : η.thread ∈ I := by
        rw [himg] at hηimg
        exact List.mem_toFinset.mp hηimg
      refine ⟨hηI, ?_⟩
      have hηsy : η.thread ∈ (s.BN nb).synced := by rw [hb]; exact hηI
      obtain ⟨x, hxF, hthx, hsx, hpx, -⟩ := (hsync η.thread).mp hηsy
      obtain ⟨nx, hcx⟩ := hsx
      have hxη : x = η :=
        genFiber_sync_thread_inj hτ hcomp hxF hη hcx hcm hthx
      rw [← hxη]
      exact hpx

/-- **The fullness pigeonhole** (mbarrier): in a conforming trace whose last
configuration holds a *full* mbarrier round of `sb` (arrivals at capacity),
the round has consumed the entire current fiber — every member (an
`arrive_mb`) has executed. -/
theorem conforms_full_fiber_mb {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (_htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    {sb : SharedBarrier} {I : List ThreadId} {A : Nat} {n₀ : ℕ+} {ph : Phase}
    (hb : s.BM sb = ⟨I, A, some n₀, ph⟩) (hfull : A = (n₀ : ℕ)) :
    ∀ η ∈ genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ),
      ∃ m, pointTime T τ' η = some m := by
  obtain ⟨hcount, harr, hwait, -⟩ := hconf.mstate _ hlast s rfl sb
  have hinitc : T.initCountOf sb = some n₀ := hcount n₀ (by rw [hb])
  obtain ⟨mI, CI, stI, hCI, hstI, hcntI⟩ :=
    exists_count_state_of_initCountOf hτ hinitc
  have harrA : A = ((genFiber T τ (.inr sb)
      ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
      fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
    rw [hb] at harr
    exact harr
  by_cases hcomp : recycleCount (.inr sb) τ' (τ'.length - 1) + 1 ≤
      recycleCount (.inr sb) τ (τ.length - 1)
  case pos =>
    have hlen := genFiber_length_mb hτ hcomp hCI hstI hcntI
    intro η hη
    have hcountP : (genFiber T τ (.inr sb)
        ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).countP
        (fun η => isArriveCmd T η && (pointTime T τ' η).isSome) =
        (genFiber T τ (.inr sb)
          ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).length := by
      rw [List.countP_eq_length_filter]
      omega
    have hallp := List.countP_eq_length.mp hcountP η hη
    simp only [Bool.and_eq_true] at hallp
    exact Option.isSome_iff_exists.mp hallp.2
  case neg =>
    -- the open round is the reference's partial round: it can never fill
    exfalso
    have hApos : 0 < A := by
      have := n₀.pos
      omega
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ genFiber T τ (.inr sb)
        ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
      rcases hF : genFiber T τ (.inr sb)
          ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) with _ | ⟨a, l⟩
      · exfalso
        rw [hF] at harrA
        simp at harrA
        omega
      · exact ⟨a, List.mem_cons_self ..⟩
    have hRge : recycleCount (.inr sb) τ' (τ'.length - 1) ≤
        recycleCount (.inr sb) τ (τ.length - 1) := by
      obtain ⟨c', mx, -, -, -, -, -, hmx1, hmxlt, hgmx⟩ := genFiber_time_data hτ hx₀
      have := recycleCount_mono (.inr sb) τ (show mx - 1 ≤ τ.length - 1 by omega)
      omega
    have hreq : recycleCount (.inr sb) τ' (τ'.length - 1) =
        recycleCount (.inr sb) τ (τ.length - 1) := by omega
    have hlt := genFiber_partial_length_lt_mb hτ (sb := sb) hCI hstI hcntI
    rw [hreq] at harrA
    have hle := List.length_filter_le (fun η => isArriveCmd T η &&
      (pointTime T τ' η).isSome) (genFiber T τ (.inr sb)
        ((recycleCount (.inr sb) τ (τ.length - 1) : ℕ) : ℤ))
    omega

/-- A wait's `some`-generation pins the phase parity: for `η = wait_mb sb ph`
with `pointGen T τ η = some g` and `0 ≤ g`, the phase after `g` recycles is
`ph` (a matching wait observed `g` directly; a mismatched one observed `g + 1`
with the opposite parity). -/
theorem wait_gen_phase {T : CTA} {τ : List Config} {η : ProgPoint}
    {sb : SharedBarrier} {ph : Phase}
    (hcm : T.cmdAt η = some (.wait_mb sb ph)) {g : ℤ}
    (hpg : pointGen T τ η = some g) (hg0 : 0 ≤ g) :
    phaseAfter g.toNat = ph := by
  unfold pointGen at hpg
  simp only [hcm, Cmd.barrier?] at hpg
  cases hpt : pointTime T τ η with
  | none =>
    rw [hpt] at hpg
    exact absurd hpg (by simp)
  | some m =>
    rw [hpt] at hpg
    simp only [Option.some.injEq] at hpg
    set r := recycleCount (.inr sb) τ (m - 1) with hr
    by_cases hph : phaseAfter r = ph
    · have hgr : g = (r : ℤ) := by
        rw [← hpg]
        simp [Cmd.genValue, hph]
      have htn : g.toNat = r := by omega
      rw [htn]
      exact hph
    · have hgr : g = (r : ℤ) - 1 := by
        rw [← hpg]
        simp [Cmd.genValue, hph]
      have hr1 : 1 ≤ r := by omega
      have htn : g.toNat = r - 1 := by omega
      rw [htn]
      have hsucc := phaseAfter_succ (r - 1)
      rw [show r - 1 + 1 = r by omega] at hsucc
      rw [hsucc] at hph
      cases h1 : phaseAfter (r - 1) <;> cases h2 : ph <;> simp_all

/-- **The wait-targeting lemma** — the `k = g` core for waits, unified: in a
conforming trace under the guards, a thread whose control sits at
`wait_mb sb ph` on an initialized barrier carries the reference generation it
would observe *right now* (`genValue` at the current open round `r`).

* `r < g` ("early") refutes via the wait check's **lower bound**: every
  `Reg(sb, g−1)` registrant reaches `pred(η)`, hence executed at τ'-depth
  `g − 1`, pinning `r = g − 1`; the census then holds the *entire* (full,
  capacity-`n`) fiber — contradicting the under-full guard.
* `g + 2 ≤ r` ("late") refutes via the **upper bound**: round `g + 1` closed
  in `τ'`, so its fiber is full (clause 5) — the fill condition holds — and
  the upper edge `η ⤳ c⁺ ∈ Reg(sb, g+1)` plus clause 4 force `η` itself to
  have executed, though its pointer still sits at it.
* the leftover `g ∈ {r−1, r}` resolves by **phase parity**: a wait's
  generation determines `phaseAfter` at it, matching `genValue`'s case split
  at `r`. -/
theorem conforms_wait_gen {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    (hmguard : ∀ sb', s.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A n ph, s.BM sb' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
    {η : ProgPoint} (hmem : η ∈ T.progPoints) {sb : SharedBarrier} {ph : Phase}
    (hcm : T.cmdAt η = some (.wait_mb sb ph))
    (hat : pointerAt T η (Config.run s Tc))
    {I : List ThreadId} {A : Nat} {n : ℕ+} {phb : Phase}
    (hb : s.BM sb = ⟨I, A, some n, phb⟩) :
    pointGen T τ η = some ((Cmd.wait_mb sb ph).genValue
      (recycleCount (.inr sb) τ' (τ'.length - 1))) := by
  obtain ⟨hokReg, hokWait, hokInit, hokU⟩ := check_true_parts hcheck
  obtain ⟨sd, hdone⟩ := hτ.2
  have hidxL : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hidxL
  have hgτ := pointGen_eq_of_time hcm rfl hmτ
  set g : ℤ := (Cmd.wait_mb sb ph).genValue (recycleCount (.inr sb) τ (mτ - 1))
    with hgdef
  set r : ℕ := recycleCount (.inr sb) τ' (τ'.length - 1) with hrdef
  have hmτlt : mτ < τ.length := by
    obtain ⟨-, -, j₀, -, C₂, hj₀, -, hC₂, -, -⟩ := hmτ
    have := (List.getElem?_eq_some_iff.mp hC₂).1
    omega
  have hmτ1 : 1 ≤ mτ := by
    obtain ⟨-, -, j₀, -, -, hj₀, -, -, -, -⟩ := hmτ
    omega
  have hchain' := htr.1
  have h0' : τ'.head? = some (Config.run State.initial T) := htr.2
  have h0idx' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact h0'
  have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hat' : (Tc.prog η.thread).length = (T.prog η.thread).length - η.idx := hat
  have hgle : g ≤ (recycleCount (.inr sb) τ (mτ - 1) : ℤ) :=
    le_of_genValue hgdef.symm
  have hgm1 : -1 ≤ g := by
    rw [hgdef]
    simp only [Cmd.genValue]
    split <;> omega
  -- the under-full guard at `sb`
  have hAn : A < (n : ℕ) := by
    rcases hmguard sb with hu | ⟨I2, A2, n2, ph2, hcfg, hlt⟩
    · rw [hb] at hu
      exact absurd hu (by simp [MBarrierState.uninitialized])
    · rw [hb] at hcfg
      simp only [MBarrierState.mk.injEq, Option.some.injEq] at hcfg
      obtain ⟨-, rfl, rfl, -⟩ := hcfg
      exact hlt
  -- the invariant's mbarrier clause and the capacity witness
  obtain ⟨hcount, harr, hwait, -⟩ := hconf.mstate _ hlast s rfl sb
  have hinitc : T.initCountOf sb = some n := hcount n (by rw [hb])
  obtain ⟨mI, CI, stI, hCI, hstI, hcntI⟩ :=
    exists_count_state_of_initCountOf hτ hinitc
  -- EARLY: `r < g` is impossible
  have hearly : ¬ ((r : ℤ) < g) := by
    intro hlt
    have hg1' : (1 : ℤ) ≤ g := by omega
    set gN := g.toNat with hgN
    have hgNg : (gN : ℤ) = g := Int.toNat_of_nonneg (by omega)
    have hgN1 : 1 ≤ gN := by omega
    obtain ⟨hidx1, hlow⟩ := wait_lower_of_check hokWait hmem hcm hgτ hg1'
    obtain ⟨m3, hptc3⟩ : ∃ m3, pointTime T τ' ⟨η.thread, η.idx - 1⟩ = some m3 := by
      refine exists_pointTime_of_passed hchain' h0' hlast (by omega) ?_
      change (Tc.prog η.thread).length + (η.idx - 1 + 1) ≤ (T.prog η.thread).length
      omega
    have hτcomplete : (gN - 1) + 1 ≤ recycleCount (.inr sb) τ (τ.length - 1) := by
      have := recycleCount_mono (.inr sb) τ (show mτ - 1 ≤ τ.length - 1 by omega)
      omega
    obtain ⟨c0, hc0⟩ := genFiber_nonempty_of_recycles hτ hτcomplete
    have hall : ∀ c1 ∈ genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ), ∃ m1, m1 ≤ m3 ∧
        pointTime T τ' c1 = some m1 ∧
        recycleCount (.inr sb) τ' (m1 - 1) = gN - 1 := by
      intro c1 hc1
      obtain ⟨hc1mem, hc1reg⟩ := mem_genFiber.mp hc1
      have hc1reg' : registrantGen T τ c1 = some (.inr sb, g - 1) := by
        rw [show g - 1 = ((gN - 1 : ℕ) : ℤ) by omega]
        exact hc1reg
      have hpath := hlow c1 hc1mem hc1reg'
      obtain ⟨m1, hm1le, hm1⟩ := hconf.happensBefore_sound hpath m3 hptc3
      refine ⟨m1, hm1le, hm1, ?_⟩
      have hgen1 : pointGen T τ' c1 = pointGen T τ c1 := hconf.gen_eq c1 hc1mem m1 hm1
      obtain ⟨c1c, hc1cm, hc1isreg, hc1bar, hc1pg⟩ := registrantGen_some hc1reg
      have hunf := pointGen_eq_of_pointTime hc1cm hc1bar hm1
      rw [genValue_of_isRegistrant hc1isreg] at hunf
      rw [hunf, hc1pg] at hgen1
      have := Option.some.inj hgen1
      omega
    have hrg : r = gN - 1 := by
      obtain ⟨m1, -, hm1, hrc1⟩ := hall c0 hc0
      have hm1lt : m1 < τ'.length := (pointTime_spec hchain' h0' hm1).2.1
      have hmono := recycleCount_mono (.inr sb) τ'
        (show m1 - 1 ≤ τ'.length - 1 by omega)
      omega
    have hfilter : (genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ)).filter (fun η' =>
        isArriveCmd T η' && (pointTime T τ' η').isSome) =
        genFiber T τ (.inr sb) ((gN - 1 : ℕ) : ℤ) := by
      rw [List.filter_eq_self]
      intro c1 hc1
      obtain ⟨m1, -, hm1, -⟩ := hall c1 hc1
      have hcmx := genFiber_mb_arrive hc1
      simp [isArriveCmd, hcmx, Cmd.isArrive, hm1]
    have hlen := genFiber_length_mb hτ hτcomplete hCI hstI hcntI
    have harrA : A = ((genFiber T τ (.inr sb) ((r : ℕ) : ℤ)).filter
        fun η' => isArriveCmd T η' && (pointTime T τ' η').isSome).length := by
      rw [hb] at harr
      exact harr
    rw [hrg] at harrA
    rw [hfilter, hlen] at harrA
    omega
  -- LATE: `g + 2 ≤ r` is impossible
  have hlate : ¬ (g + 2 ≤ (r : ℤ)) := by
    intro hle
    set g1 := (g + 1).toNat with hg1N
    have hg1g : (g1 : ℤ) = g + 1 := Int.toNat_of_nonneg (by omega)
    have hfull := hconf.rounds_full sb g1 (by omega) n hinitc
    have hfill : (T.progPoints.filter fun cp =>
        registrantGen T τ cp = some (.inr sb, g + 1)).length = (n : ℕ) := by
      have h := hfull
      rw [show ((g1 : ℕ) : ℤ) = g + 1 from hg1g] at h
      exact h
    obtain ⟨cp, hcpmem, hcphb⟩ := wait_upper_of_check hokWait hmem hcm hgτ hinitc hfill
    have hcpF : cp ∈ genFiber T τ (.inr sb) ((g1 : ℕ) : ℤ) := by
      rw [mem_genFiber]
      have h := List.mem_filter.mp hcpmem
      refine ⟨h.1, ?_⟩
      have h2 := of_decide_eq_true h.2
      rw [hg1g]
      exact h2
    obtain ⟨mc, hmc⟩ := hconf.rounds_complete (.inr sb) g1 (by omega) cp hcpF
    obtain ⟨mη, -, hmη⟩ := hconf.happensBefore_sound hcphb mc hmc
    have hnone := pointTime_none_of_pointerAt hchain' h0' hlast hat
    rw [hnone] at hmη
    exact absurd hmη (by simp)
  -- endgame: `g ∈ {r − 1, r}`; parity picks `genValue r`
  have hgr : g = (r : ℤ) ∨ g = (r : ℤ) - 1 := by omega
  rcases hgr with hgr | hgr
  · have hg0 : (0 : ℤ) ≤ g := by omega
    have hph := wait_gen_phase hcm hgτ hg0
    have htn : g.toNat = r := by omega
    rw [htn] at hph
    rw [hgτ]
    congr 1
    simp only [Cmd.genValue, if_pos hph]
    omega
  · by_cases hg0 : (0 : ℤ) ≤ g
    · have hph := wait_gen_phase hcm hgτ hg0
      have hr1 : 1 ≤ r := by omega
      have htn : g.toNat = r - 1 := by omega
      rw [htn] at hph
      have hsucc := phaseAfter_succ (r - 1)
      rw [show r - 1 + 1 = r by omega] at hsucc
      have hphr : ¬ (phaseAfter r = ph) := by
        rw [hsucc, ← hph]
        cases phaseAfter (r - 1) <;> simp
      rw [hgτ]
      congr 1
      simp only [Cmd.genValue, if_neg hphr]
      omega
    · -- `g = −1`: the wait mismatched at recycle count `0` in `τ`, so `ph = true`
      have hgm1' : g = -1 := by omega
      have hr0 : r = 0 := by omega
      have hpht : ph = true := by
        have hgv := hgdef
        by_cases hphm : phaseAfter (recycleCount (.inr sb) τ (mτ - 1)) = ph
        · exfalso
          rw [hgm1'] at hgv
          simp only [Cmd.genValue, if_pos hphm] at hgv
          omega
        · rw [hgm1'] at hgv
          simp only [Cmd.genValue, if_neg hphm] at hgv
          have hrτ0 : recycleCount (.inr sb) τ (mτ - 1) = 0 := by omega
          rw [hrτ0] at hphm
          cases hphc : ph
          · exfalso
            apply hphm
            rw [hphc]
            rfl
          · rfl
      rw [hgτ]
      congr 1
      rw [hr0, hpht]
      simp only [Cmd.genValue]
      rw [if_neg (by simp [phaseAfter])]
      omega

/-- **The wait-targeting lemma, block flavor**: the barrier's phase matches
`ph`, so the wait observes the open round `r` itself. -/
theorem conforms_wait_gen_block {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    (_hguard : ∀ nb', s.BN nb' = NamedBarrierState.unconfigured ∨
      ∃ I A n, s.BN nb' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
    (hmguard : ∀ sb', s.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A n ph, s.BM sb' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
    {η : ProgPoint} (hmem : η ∈ T.progPoints) {sb : SharedBarrier} {ph : Phase}
    (hcm : T.cmdAt η = some (.wait_mb sb ph))
    (hat : pointerAt T η (Config.run s Tc))
    {I : List ThreadId} {A : Nat} {n : ℕ+}
    (hb : s.BM sb = ⟨I, A, some n, ph⟩) :
    pointGen T τ η =
      some ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
  have hcore := conforms_wait_gen hτ hcheck htr hconf hlast hmguard hmem hcm hat hb
  have h0idx' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact htr.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hphm : phaseAfter (recycleCount (.inr sb) τ' (τ'.length - 1)) = ph := by
    have hph := phase_eq_phaseAfter htr.1 h0idx' sb (τ'.length - 1) _ s hlastidx rfl
    rw [hb] at hph
    exact hph.symm
  rw [hcore]
  congr 1
  simp [Cmd.genValue, hphm]

/-- **The wait-targeting lemma, pass flavor**: the barrier's phase mismatches
`ph` — the wait's round already completed — so it observes `r − 1`. -/
theorem conforms_wait_gen_pass {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {s : State} {Tc : CTA} (hlast : τ'.getLast? = some (Config.run s Tc))
    (_hguard : ∀ nb', s.BN nb' = NamedBarrierState.unconfigured ∨
      ∃ I A n, s.BN nb' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
    (hmguard : ∀ sb', s.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A n ph, s.BM sb' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
    {η : ProgPoint} (hmem : η ∈ T.progPoints) {sb : SharedBarrier} {ph : Phase}
    (hcm : T.cmdAt η = some (.wait_mb sb ph))
    (hat : pointerAt T η (Config.run s Tc))
    {I : List ThreadId} {A : Nat} {n : ℕ+} {ph' : Phase}
    (hb : s.BM sb = ⟨I, A, some n, ph'⟩) (hne : ph ≠ ph') :
    pointGen T τ η =
      some (((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) - 1) := by
  have hcore := conforms_wait_gen hτ hcheck htr hconf hlast hmguard hmem hcm hat hb
  have h0idx' : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact htr.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.run s Tc) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hph'' : ph' = phaseAfter (recycleCount (.inr sb) τ' (τ'.length - 1)) := by
    have hph := phase_eq_phaseAfter htr.1 h0idx' sb (τ'.length - 1) _ s hlastidx rfl
    rw [hb] at hph
    exact hph
  have hphm : ¬ (phaseAfter (recycleCount (.inr sb) τ' (τ'.length - 1)) = ph) := by
    intro hcon
    exact hne (hph'' ▸ hcon).symm
  rw [hcore]
  congr 1
  simp [Cmd.genValue, hphm]

/-- **Theorem 6, induction step** (paper §5.2.6): extending a conforming trace
by one CTA step preserves conformance. Case analysis on `hstep`:

* `interleave`/`read_noop`,`write_noop` — no barrier effect; clause 3's new
  target receives only its program-order edge.
* `interleave`/named registration (`arrive_configure`, `arrive_register`,
  `sync_configure`, `sync_block`) — `conforms_reg_round` pins the round to the
  op's reference generation; clauses 1/2 update mechanically.
* `interleave`/`mb_init` — the barrier was uninitialized, so no recycle of it
  has ever happened in either trace; generation `0 = 0`; the state moves
  pristine → `⟨[], 0, some n, false⟩` with `initCountOf` pinning `n`.
* `interleave`/`mb_arrive` — mirror of `arrive_register`:
  `conforms_reg_round` gives the round, the census gains exactly the executed
  member.
* `interleave`/`mb_wait_block` — `conforms_wait_gen_block` pins the waiter's
  reference generation to the open round; the parked-waiter clause extends
  with the new waiter; nothing is retired.
* `interleave`/`mb_wait_pass` — `conforms_wait_gen_pass` gives the retired
  wait generation `r − 1` = its observed value; its arriveWait in-edges come
  from the closed round `r − 1` (clause 4).
* `recycle` — the round was full, so `conforms_full_fiber` identifies the
  woken syncs with the fiber's syncs and the counted arrives with the fiber's
  arrives; the barrier resets and the *next* fiber has no executed members.
* `mb_recycle` — the round was full, so `conforms_full_fiber_mb` says the
  fiber is consumed; the woken waiters are parked at their reference
  generation (the parked-waiter clause), giving each retiree its `gen_eq`;
  the count survives, the phase flips, and clause 4 extends to the newly
  closed round.
* `done` — state and times unchanged.
* `error` — impossible: the guard supplies all-barriers-under-full;
  `conforms_reg_round` refutes the count-mismatch productions, and
  `init_hb_of_check` + the closure lift refute the uninitialized-use and
  double-init productions. -/
theorem conforms_snoc {T : CTA} {τ τ' : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    (htr : IsTraceFrom (Config.run State.initial T) τ')
    (hconf : Conforms T τ τ')
    {C C' : Config} (hlast : τ'.getLast? = some C) (hstep : CTAStep C C') :
    Conforms T τ (τ' ++ [C']) := by
  -- ## Preamble: the appended trace and its bookkeeping
  have hne : τ' ≠ [] := fun h => by rw [h] at hlast; simp at hlast
  have hNpos : 1 ≤ τ'.length := by
    cases τ' with
    | nil => simp at hne
    | cons _ _ => simp
  have hchain : List.IsChain CTAStep τ' := htr.1
  have h0 : τ'.head? = some (Config.run State.initial T) := htr.2
  have h0idx : τ'[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact h0
  have hchainσ : List.IsChain CTAStep (τ' ++ [C']) := by
    refine List.IsChain.append hchain (List.isChain_singleton _) ?_
    intro x hx y hy
    rw [Option.mem_def, hlast, Option.some.injEq] at hx
    rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hy
    rw [← hx, ← hy]
    exact hstep
  have h0σ : (τ' ++ [C']).head? = some (Config.run State.initial T) := by
    rw [List.head?_append_of_ne_nil _ hne]; exact h0
  have hlastidx : τ'[τ'.length - 1]? = some C := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hσlast : (τ' ++ [C']).length - 1 = τ'.length := by simp
  have hσN1 : (τ' ++ [C'])[τ'.length - 1]? = some C := by
    rw [List.getElem?_append_left (by omega)]; exact hlastidx
  have hσN : (τ' ++ [C'])[τ'.length]? = some C' := List.getElem?_concat_length
  obtain ⟨s, Tc, rfl⟩ : ∃ sx Tcx, C = Config.run sx Tcx := by
    cases hstep <;> exact ⟨_, _, rfl⟩
  have hreach := reaches_of_chain_getElem hchain h0idx (τ'.length - 1) _ hlastidx
  have hwf := WF_of_reaches hreach
  have hei : s.EnabledInv := by
    have hall := enabledInv_chain hchain h0 (by
      intro sx hsx
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsx
      subst hsx
      exact State.EnabledInv.initial)
    exact hall _ (List.mem_of_mem_getLast? hlast) s rfl
  -- new-time decomposition
  have htime_cases : ∀ (η : ProgPoint) (m : Nat),
      pointTime T (τ' ++ [C']) η = some m →
      pointTime T τ' η = some m ∨
      (pointTime T τ' η = none ∧ m = τ'.length ∧
        η.idx < (T.prog η.thread).length ∧
        Tc.prog η.thread = (T.prog η.thread).drop η.idx ∧
        C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1)) := by
    intro η m hpt
    rcases pointTime_append_cases hne hpt with h | ⟨hnone, hm⟩
    · exact Or.inl h
    · subst hm
      obtain ⟨hm1, hmlt, hidx, C₁, C₂, hC₁, hC₂, hd1, hd2⟩ :=
        pointTime_spec hchainσ h0σ hpt
      rw [hσN1] at hC₁
      obtain rfl := Option.some.inj hC₁
      rw [hσN] at hC₂
      obtain rfl := Option.some.inj hC₂
      exact Or.inr ⟨hnone, rfl, hidx, hd1, hd2⟩
  -- old times keep their generations
  have hgen_old : ∀ (η : ProgPoint) (m : Nat), pointTime T τ' η = some m →
      pointGen T (τ' ++ [C']) η = pointGen T τ η := by
    intro η m hpt
    have hmem : η ∈ T.progPoints := by
      obtain ⟨-, -, hidx, -⟩ := pointTime_spec hchain h0 hpt
      exact (mem_progPoints_iff T η).mpr ⟨mem_ids_of_idx_lt T hidx, hidx⟩
    have hold := hconf.gen_eq η hmem m hpt
    have hσpt := pointTime_append_some (C' := C') hpt
    have hmlt : m < τ'.length := (pointTime_spec hchain h0 hpt).2.1
    cases hcm : T.cmdAt η with
    | none => simp only [pointGen, hcm]
    | some cmd =>
      cases hbar : cmd.barrier? with
      | none => simp only [pointGen, hcm, hbar]
      | some b =>
        have h1 := pointGen_eq_of_pointTime hcm hbar hσpt
        have h2 := pointGen_eq_of_pointTime hcm hbar hpt
        have hrc : recycleCount b (τ' ++ [C']) (m - 1) = recycleCount b τ' (m - 1) :=
          recycleCount_append b τ' C' (by omega)
        rw [h1, hrc, ← h2]
        exact hold
  -- old edges keep their soundness
  have hedge_old : ∀ x y, (x, y) ∈ initRelation T τ → ∀ (m : Nat),
      pointTime T τ' y = some m →
      ∃ mx ≤ m, pointTime T (τ' ++ [C']) x = some mx := by
    intro x y hxy m hpt
    obtain ⟨mx, hle, hx⟩ := hconf.edge_sound x y hxy m hpt
    exact ⟨mx, hle, pointTime_append_some hx⟩
  -- a newly executed instruction's program-order predecessor already executed
  have hedge_new_po : ∀ (y : ProgPoint), 1 ≤ y.idx →
      y.idx < (T.prog y.thread).length →
      Tc.prog y.thread = (T.prog y.thread).drop y.idx →
      ∃ mx ≤ τ'.length,
        pointTime T (τ' ++ [C']) ⟨y.thread, y.idx - 1⟩ = some mx := by
    intro y hidx1 hidxL hdrop
    obtain ⟨mx, hmx⟩ : ∃ mx, pointTime T τ' ⟨y.thread, y.idx - 1⟩ = some mx := by
      refine exists_pointTime_of_passed hchain h0 hlast (i := y.thread)
        (k := y.idx - 1) (by omega) ?_
      change (Tc.prog y.thread).length + (y.idx - 1 + 1) ≤ (T.prog y.thread).length
      rw [hdrop]
      simp only [List.length_drop]
      omega
    have hmlt : mx < τ'.length := (pointTime_spec hchain h0 hmx).2.1
    exact ⟨mx, by omega, pointTime_append_some hmx⟩
  -- per-barrier recycle-count bookkeeping across the appended step
  have hrc_same : ∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = false →
      recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) =
      recycleCount b τ' (τ'.length - 1) := by
    intro b hnr
    rw [hσlast, show τ'.length = (τ'.length - 1) + 1 by omega]
    have hσN' : (τ' ++ [C'])[τ'.length - 1 + 1]? = some C' := by
      rw [show τ'.length - 1 + 1 = τ'.length by omega]; exact hσN
    rw [recycleCount_succ_of_not_recycle b hσN1 hσN' hnr]
    exact recycleCount_append b τ' C' (by omega)
  have hrc_incr : ∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = true →
      recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) =
      recycleCount b τ' (τ'.length - 1) + 1 := by
    intro b hr
    rw [hσlast, show τ'.length = (τ'.length - 1) + 1 by omega]
    have hσN' : (τ' ++ [C'])[τ'.length - 1 + 1]? = some C' := by
      rw [show τ'.length - 1 + 1 = τ'.length by omega]; exact hσN
    rw [recycleCount_succ_of_recycle b (τ' ++ [C']) hσN1 hσN' hr]
    congr 1
    exact recycleCount_append b τ' C' (by omega)
  -- assemblers for the invariant's clauses
  have hgen_all :
      (∀ (η : ProgPoint), pointTime T τ' η = none →
        η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        C'.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) →
        pointGen T (τ' ++ [C']) η = pointGen T τ η) →
      ∀ η ∈ T.progPoints, ∀ m, pointTime T (τ' ++ [C']) η = some m →
        pointGen T (τ' ++ [C']) η = pointGen T τ η := by
    intro hnew η _ m hpt
    rcases htime_cases η m hpt with hold | ⟨hnone, -, hidx, hd1, hd2⟩
    · exact hgen_old η m hold
    · exact hnew η hnone hidx hd1 hd2
  have hedge_all :
      (∀ (y : ProgPoint), y.idx < (T.prog y.thread).length →
        Tc.prog y.thread = (T.prog y.thread).drop y.idx →
        C'.progOf y.thread = (T.prog y.thread).drop (y.idx + 1) →
        ∀ x ∈ T.progPoints,
          ((∃ nb n, T.cmdAt x = some (.arrive_nb nb n) ∧
             T.cmdAt y = some (.sync_nb nb n)) ∨
           (∃ sb ph, T.cmdAt x = some (.arrive_mb sb) ∧
             T.cmdAt y = some (.wait_mb sb ph)) ∨
           (∃ nb n, T.cmdAt x = some (.sync_nb nb n) ∧
             T.cmdAt y = some (.sync_nb nb n))) →
          pointGen T τ x = pointGen T τ y →
          ∃ mx ≤ τ'.length, pointTime T (τ' ++ [C']) x = some mx) →
      ∀ x y, (x, y) ∈ initRelation T τ → ∀ m,
        pointTime T (τ' ++ [C']) y = some m →
        ∃ mx ≤ m, pointTime T (τ' ++ [C']) x = some mx := by
    intro hbarnew x y hxy m hpt
    rcases htime_cases y m hpt with hold | ⟨hnone, hm, hidx, hd1, hd2⟩
    · exact hedge_old x y hxy m hold
    · subst hm
      rcases mem_initRelation_iff.mp hxy with
        ⟨hxpts, hidx1, rfl⟩ | ⟨nb, n, hxpts, hypts, hxc, hyc, hg⟩ |
        ⟨sb, ph, hxpts, hypts, hxc, hyc, hg⟩ | ⟨nb, n, hxpts, hypts, hxc, hyc, hg⟩
      · exact hedge_new_po ⟨x.thread, x.idx + 1⟩ (by simp) hidx hd1
      · exact hbarnew y hidx hd1 hd2 x hxpts (Or.inl ⟨nb, n, hxc, hyc⟩) hg
      · exact hbarnew y hidx hd1 hd2 x hxpts (Or.inr (Or.inl ⟨sb, ph, hxc, hyc⟩)) hg
      · exact hbarnew y hidx hd1 hd2 x hxpts (Or.inr (Or.inr ⟨nb, n, hxc, hyc⟩)) hg
  have hrounds_all :
      (∀ b, stepRecyclesBarrier b (Config.run s Tc) C' = true →
        ∀ η ∈ genFiber T τ b ((recycleCount b τ' (τ'.length - 1) : ℕ) : ℤ),
          ∃ m, pointTime T (τ' ++ [C']) η = some m) →
      ∀ (b : NamedBarrier ⊕ SharedBarrier) (g : ℕ),
        g + 1 ≤ recycleCount b (τ' ++ [C']) ((τ' ++ [C']).length - 1) →
        ∀ η ∈ genFiber T τ b (g : ℤ), ∃ m, pointTime T (τ' ++ [C']) η = some m := by
    intro hnew b g hgle η hη
    cases hrb : stepRecyclesBarrier b (Config.run s Tc) C' with
    | false =>
      rw [hrc_same b hrb] at hgle
      obtain ⟨m, hm⟩ := hconf.rounds_complete b g hgle η hη
      exact ⟨m, pointTime_append_some hm⟩
    | true =>
      rw [hrc_incr b hrb] at hgle
      rcases Nat.lt_or_ge (g + 1) (recycleCount b τ' (τ'.length - 1) + 1) with hlt | hge
      · obtain ⟨m, hm⟩ := hconf.rounds_complete b g (by omega) η hη
        exact ⟨m, pointTime_append_some hm⟩
      · have hgeq : g = recycleCount b τ' (τ'.length - 1) := by omega
        subst hgeq
        exact hnew b hrb η hη
  -- the arrival-census filter is stable when the step executes no arrive on `b`
  have hfilter_same : ∀ (b : NamedBarrier ⊕ SharedBarrier) (g : ℤ),
      (∀ η ∈ genFiber T τ b g, ∀ c, T.cmdAt η = some c → c.isArrive = true →
        pointTime T (τ' ++ [C']) η = some τ'.length → False) →
      ((genFiber T τ b g).filter fun η =>
        isArriveCmd T η && (pointTime T (τ' ++ [C']) η).isSome).length =
      ((genFiber T τ b g).filter fun η =>
        isArriveCmd T η && (pointTime T τ' η).isSome).length := by
    intro b g hnonew
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    refine List.countP_congr fun η hη => ?_
    cases hcm : T.cmdAt η with
    | none => simp [isArriveCmd, hcm]
    | some cmd =>
      cases hcarr : cmd.isArrive with
      | false => simp [isArriveCmd, hcm, hcarr]
      | true =>
        simp only [isArriveCmd, hcm, hcarr, Bool.true_and]
        constructor
        · intro hsome
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
          rcases pointTime_append_cases hne hm with hold | ⟨-, hmN⟩
          · rw [hold]; rfl
          · exfalso
            subst hmN
            exact hnonew η hη cmd hcm hcarr hm
        · intro hsome
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
          rw [pointTime_append_some (C' := C') hm]
          rfl
  cases hstep with
  | @interleave s₀ sn Tc₀ t P' ht hbar hmbar hth =>
    -- the guard keeps every barrier under-full: this step recycles nothing
    have hnorec : ∀ b, stepRecyclesBarrier b (Config.run s Tc)
        (Config.run sn (Tc.set t ht P')) = false := by
      intro b
      cases b with
      | inl nb =>
        have hnf : (s.BN nb).isFull = false := by
          rcases hbar nb with hu | ⟨I, A, n, hcfg, hlt⟩
          · rw [hu]; rfl
          · rw [hcfg]; simp only [NamedBarrierState.isFull]
            exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf]
      | inr sb =>
        have hnf : (s.BM sb).isFull = false := by
          rcases hmbar sb with hu | ⟨I, A, n, ph, hcfg, hlt⟩
          · rw [hu]; rfl
          · rw [hcfg]; simp only [MBarrierState.isFull]
            exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlt)
        simp [stepRecyclesBarrier, WeftCommon.Config.state?, hnf]
    -- a dropped head belongs to the stepping thread
    have hident_thread : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        (Config.run sn (Tc.set t ht P')).progOf η.thread =
          (T.prog η.thread).drop (η.idx + 1) →
        η.thread = t := by
      intro η hidx hd1 hd2
      by_contra hηt
      have hsame : (Tc.set t ht P').prog η.thread = Tc.prog η.thread := by
        simp [WeftCommon.CTA.set, Function.update_of_ne hηt]
      have hd2' : (Tc.set t ht P').prog η.thread =
          (T.prog η.thread).drop (η.idx + 1) := hd2
      rw [hsame, hd1] at hd2'
      have hlen := congrArg List.length hd2'
      simp only [List.length_drop] at hlen
      omega
    -- ... and is the thread's static head command
    have hident_cmd : ∀ (η : ProgPoint) (c₀ : Cmd) (rest : Prog), η.thread = t →
        Tc.prog t = c₀ :: rest →
        η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        T.cmdAt η = some c₀ := by
      intro η c₀ rest hηt hcons hidx hd1
      rw [hηt] at hd1 hidx
      have hdd : (T.prog t).drop η.idx =
          (T.prog t)[η.idx]'hidx :: (T.prog t).drop (η.idx + 1) :=
        List.drop_eq_getElem_cons hidx
      rw [← hd1, hcons] at hdd
      injection hdd with hhead htail
      have hgoal : (T.prog η.thread)[η.idx]? = some c₀ := by
        rw [hηt, List.getElem?_eq_getElem hidx, ← hhead]
      exact hgoal
    -- the executing point is pinned to the head position
    have huniq : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        (Config.run sn (Tc.set t ht P')).progOf η.thread =
          (T.prog η.thread).drop (η.idx + 1) →
        η = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
      intro η hidx hd1 hd2
      have hηt := hident_thread η hidx hd1 hd2
      rw [hηt] at hd1 hidx
      have hlen := congrArg List.length hd1
      simp only [List.length_drop] at hlen
      have hidxeq : η.idx = (T.prog t).length - (Tc.prog t).length := by omega
      have hηeta : η = ⟨η.thread, η.idx⟩ := rfl
      rw [hηeta, hηt, hidxeq]
    -- a thread whose head is neither a `sync_nb` nor a `wait_mb` is enabled
    have ht_enabled_of_head : ∀ (c₀ : Cmd) (rest : Prog), Tc.prog t = c₀ :: rest →
        (∀ bx (nx : ℕ+), c₀ ≠ Cmd.sync_nb bx nx) →
        (∀ sx px, c₀ ≠ Cmd.wait_mb sx px) → s.E t = true := by
      intro c₀ rest hcons hnsync hnwait
      by_contra hf
      rw [Bool.not_eq_true] at hf
      obtain ⟨b', hib'⟩ := hei t hf
      cases b' with
      | inl nb' =>
        rcases hsb' : s.BN nb' with ⟨I', A', cnt'⟩
        cases cnt' with
        | none =>
          obtain ⟨hI0, -⟩ := hwf.2.1 nb' I' A' hsb'
          have hib'' : t ∈ I' := by
            have h : t ∈ (s.BN nb').synced := hib'
            rw [hsb'] at h
            exact h
          rw [hI0] at hib''
          simp at hib''
        | some n' =>
          have hpk := (hwf.1 nb' I' A' n' hsb').2.1 t (by
            have h : t ∈ (s.BN nb').synced := hib'
            rw [hsb'] at h
            exact h)
          rw [hcons] at hpk
          simp only [List.head?_cons, Option.some.injEq] at hpk
          exact hnsync nb' n' hpk
      | inr sb' =>
        rcases hsb' : s.BM sb' with ⟨I', A', cnt', ph'⟩
        cases cnt' with
        | none =>
          obtain ⟨hI0, -, -⟩ := hwf.2.2.2.1 sb' I' A' ph' hsb'
          have hib'' : t ∈ I' := by
            have h : t ∈ (s.BM sb').waiting := hib'
            rw [hsb'] at h
            exact h
          rw [hI0] at hib''
          simp at hib''
        | some n' =>
          have hpk := (hwf.2.2.1 sb' I' A' n' ph' hsb').2 t (by
            have h : t ∈ (s.BM sb').waiting := hib'
            rw [hsb'] at h
            exact h)
          rw [hcons] at hpk
          simp only [List.head?_cons, Option.some.injEq] at hpk
          exact hnwait sb' ph' hpk
    -- pointer positions of other threads are untouched
    have hpointer_ne : ∀ (x : ProgPoint) (sl : State) (P₂ : Prog) (htx : t ∈ Tc.ids),
        x.thread ≠ t →
        (pointerAt T x (Config.run sl (Tc.set t htx P₂)) ↔
          pointerAt T x (Config.run s Tc)) := by
      intro x sl P₂ htx hxt
      have hsame : (Tc.set t htx P₂).prog x.thread = Tc.prog x.thread := by
        simp [WeftCommon.CTA.set, Function.update_of_ne hxt]
      simp [pointerAt, WeftCommon.Config.progOf, hsame]
    obtain ⟨Pt, hPt⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPt] at hth
    cases hth with
    | @read_noop _ _ g₀ _ =>
      have hte : s.E t = true := ht_enabled_of_head _ _ hPt
        (by intro bx nx h; cases h) (by intro sx px h; cases h)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hcm := hident_cmd η _ _ hηt hPt hidx hd1
        simp only [pointGen, hcm, Cmd.barrier?]
      · intro Cl hCl sl hsl nb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl nb
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl nb) (hnorec (.inl nb))]
          exact hcount
        · rw [hrc_same (.inl nb) (hnorec (.inl nb)), hfilter_same (.inl nb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              have hcr : c = Cmd.read g₀ := Option.some.inj hcm'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i
          rw [hrc_same (.inl nb) (hnorec (.inl nb))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              have hcr : c = Cmd.read g₀ := Option.some.inj hcm'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hηgen⟩ := hwait i hi
          have hit : η.thread ≠ t := by
            intro h
            have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
            rw [h, hte] at hEth
            exact absurd hEth (by simp)
          refine ⟨η, hηpts, hηth, hηcmd,
            (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
          rw [hrc_same (.inr sb) (hnorec (.inr sb))]
          exact hηgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηt := hident_thread y hidx hd1 hd2
        have hcm' := hident_cmd y _ _ hηt hPt hidx hd1
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph, -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcm'; exact absurd (Option.some.inj hcm') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @write_noop _ _ g₀ _ =>
      have hte : s.E t = true := ht_enabled_of_head _ _ hPt
        (by intro bx nx h; cases h) (by intro sx px h; cases h)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hcm := hident_cmd η _ _ hηt hPt hidx hd1
        simp only [pointGen, hcm, Cmd.barrier?]
      · intro Cl hCl sl hsl nb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl nb
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl nb) (hnorec (.inl nb))]
          exact hcount
        · rw [hrc_same (.inl nb) (hnorec (.inl nb)), hfilter_same (.inl nb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              have hcr : c = Cmd.write g₀ := Option.some.inj hcm'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i
          rw [hrc_same (.inl nb) (hnorec (.inl nb))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, hte] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηt := hident_thread η hidx hd1 hd2
              have hcm' := hident_cmd η _ _ hηt hPt hidx hd1
              rw [hcm] at hcm'
              have hcr : c = Cmd.write g₀ := Option.some.inj hcm'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hηgen⟩ := hwait i hi
          have hit : η.thread ≠ t := by
            intro h
            have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
            rw [h, hte] at hEth
            exact absurd hEth (by simp)
          refine ⟨η, hηpts, hηth, hηcmd,
            (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
          rw [hrc_same (.inr sb) (hnorec (.inr sb))]
          exact hηgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηt := hident_thread y hidx hd1 hd2
        have hcm' := hident_cmd y _ _ hηt hPt hidx hd1
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph, -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcm'; exact absurd (Option.some.inj hcm') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @arrive_configure _ _ ba na _ he hbcfg =>
      set Cn := Config.run
        ({ s with BN := Function.update s.BN ba ⟨[], 1, some na⟩ })
        (Tc.set t ht P') with hCndef
      -- the newly executing point: `t`'s head `arrive_nb ba na`
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive_nb ba na :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive_nb ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmemN
        hcmdN' rfl rfl hatN
      have hregN : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdN', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmemN, hregN⟩
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T (τ' ++ [Cn])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hcmdN' rfl hmN
          simp only [Cmd.genValue] at hpgσ
          have hrca := recycleCount_append (.inl ba) τ' Cn
            (j := τ'.length - 1) (by omega)
          rw [hpgσ, hrca, hrr]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            have hna : na = n := by
              have h : (Function.update s.BN b ⟨[], 1, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same (.inl b) (hnorec (.inl b))]
            have harr0 : (0 : ℕ) =
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              have h := harr
              rw [hbcfg] at h
              exact h
            have hLHS : ((Function.update s.BN b ⟨[], 1, some na⟩) b).arrived = 1 := by
              rw [Function.update_self]
            have hcnt_new :
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η &&
                    (pointTime T (τ' ++ [Cn]) η).isSome).length =
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length + 1 := by
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              refine countP_succ_of_unique (genFiber_nodup T τ (.inl b) _) hfibN ?_ ?_ ?_
              · obtain ⟨mN, hmN⟩ := hσNt
                simp [isArriveCmd, hcmdN', Cmd.isArrive, hmN]
              · simp [isArriveCmd, hcmdN', Cmd.isArrive, hτ'N]
              · intro x hx hxne
                cases hcmx : T.cmdAt x with
                | none => simp [isArriveCmd, hcmx]
                | some cmd =>
                  cases hcarrx : cmd.isArrive with
                  | false => simp [isArriveCmd, hcmx, hcarrx]
                  | true =>
                    simp only [isArriveCmd, hcmx, hcarrx, Bool.true_and]
                    cases hptx : pointTime T (τ' ++ [Cn]) x with
                    | none =>
                      cases hptx' : pointTime T τ' x with
                      | none => rfl
                      | some mx =>
                        have h := pointTime_append_some (C' := Cn) hptx'
                        rw [hptx] at h
                        exact absurd h (by simp)
                    | some mx =>
                      rcases htime_cases x mx hptx with hold | ⟨-, -, hidx, hd1, hd2⟩
                      · rw [hold]
                      · exact absurd (huniq x hidx hd1 hd2) hxne
            rw [hLHS, hcnt_new, ← harr0]
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              exfalso
              have h : i ∈ (Function.update s.BN b ⟨[], 1, some na⟩ b).synced := hi
              rw [Function.update_self] at h
              simp at h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              exfalso
              have hex' : s.E i = false := hex
              by_cases hxt : x.thread = t
              · rw [← hthx, hxt, he] at hex'
                exact absurd hex' (by simp)
              · have hpx' := (hpointer_ne x _ _ ht hxt).mp hpx
                have hi' : i ∈ (s.BN b).synced :=
                  (hsync i).mpr ⟨x, hxF, hthx, hsx, hpx', hex'⟩
                rw [hbcfg] at hi'
                have hi'' : i ∈ ([] : List ThreadId) := hi'
                simp at hi''
          · intro hcnone
            exfalso
            have h : (Function.update s.BN b ⟨[], 1, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BN ba ⟨[], 1, some na⟩) b = s.BN b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.BN ba ⟨[], 1, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN ba ⟨[], 1, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                have hreg' := (mem_genFiber.mp hη).2
                rw [hregN] at hreg'
                have hpair := Option.some.inj hreg'
                have hfst : (Sum.inl ba : NamedBarrier ⊕ SharedBarrier) = .inl b :=
                  congrArg Prod.fst hpair
                simp only [Sum.inl.injEq] at hfst
                exact hbba hfst.symm
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (s.BN b).synced := by
                have h : i ∈ (Function.update s.BN ba ⟨[], 1, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have hgoal : i ∈ (Function.update s.BN ba ⟨[], 1, some na⟩ b).synced := by
                rw [hBb]
                exact hi'
              exact hgoal
          · intro hcnone
            have h : (Function.update s.BN ba ⟨[], 1, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BN ba ⟨[], 1, some na⟩) b =
                NamedBarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              have hcmη := genFiber_mb_arrive hη
              rw [hcmdN'] at hcmη
              exact absurd (Option.some.inj hcmη) (by simp)
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
          have hit : η.thread ≠ t := by
            intro h
            have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
            rw [h, he] at hEth
            exact absurd hEth (by simp)
          refine ⟨η, hηpts, hηth, hηcmd,
            (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
          rw [hrc_same (.inr sb) (hnorec (.inr sb))]
          exact hEgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph, -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcmdN'; exact absurd (Option.some.inj hcmdN') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @arrive_register _ _ ba na _ I A he hbcfg hpos hlt =>
      set Cn := Config.run
        ({ s with BN := Function.update s.BN ba ⟨I, A + 1, some na⟩ })
        (Tc.set t ht P') with hCndef
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive_nb ba na :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive_nb ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmemN
        hcmdN' rfl rfl hatN
      have hregN : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdN', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmemN, hregN⟩
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T (τ' ++ [Cn])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hcmdN' rfl hmN
          simp only [Cmd.genValue] at hpgσ
          have hrca := recycleCount_append (.inl ba) τ' Cn
            (j := τ'.length - 1) (by omega)
          rw [hpgσ, hrca, hrr]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            have hna : na = n := by
              have h : (Function.update s.BN b ⟨I, A + 1, some na⟩ b).count =
                  some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same (.inl b) (hnorec (.inl b))]
            have harrA : A =
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              have h := harr
              rw [hbcfg] at h
              exact h
            have hLHS : ((Function.update s.BN b ⟨I, A + 1, some na⟩) b).arrived =
                A + 1 := by
              rw [Function.update_self]
            have hcnt_new :
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η &&
                    (pointTime T (τ' ++ [Cn]) η).isSome).length =
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length + 1 := by
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              refine countP_succ_of_unique (genFiber_nodup T τ (.inl b) _) hfibN ?_ ?_ ?_
              · obtain ⟨mN, hmN⟩ := hσNt
                simp [isArriveCmd, hcmdN', Cmd.isArrive, hmN]
              · simp [isArriveCmd, hcmdN', Cmd.isArrive, hτ'N]
              · intro x hx hxne
                cases hcmx : T.cmdAt x with
                | none => simp [isArriveCmd, hcmx]
                | some cmd =>
                  cases hcarrx : cmd.isArrive with
                  | false => simp [isArriveCmd, hcmx, hcarrx]
                  | true =>
                    simp only [isArriveCmd, hcmx, hcarrx, Bool.true_and]
                    cases hptx : pointTime T (τ' ++ [Cn]) x with
                    | none =>
                      cases hptx' : pointTime T τ' x with
                      | none => rfl
                      | some mx =>
                        have h := pointTime_append_some (C' := Cn) hptx'
                        rw [hptx] at h
                        exact absurd h (by simp)
                    | some mx =>
                      rcases htime_cases x mx hptx with hold | ⟨-, -, hidx, hd1, hd2⟩
                      · rw [hold]
                      · exact absurd (huniq x hidx hd1 hd2) hxne
            rw [hLHS, hcnt_new, ← harrA]
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (s.BN b).synced := by
                have h : i ∈ (Function.update s.BN b ⟨I, A + 1, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                rw [hbcfg]
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have h : i ∈ (Function.update s.BN b ⟨I, A + 1, some na⟩ b).synced := by
                rw [Function.update_self]
                rw [hbcfg] at hi'
                exact hi'
              exact h
          · intro hcnone
            exfalso
            have h : (Function.update s.BN b ⟨I, A + 1, some na⟩ b).count =
                none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BN ba ⟨I, A + 1, some na⟩) b = s.BN b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.BN ba ⟨I, A + 1, some na⟩ b).count =
                some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN ba ⟨I, A + 1, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                have hreg' := (mem_genFiber.mp hη).2
                rw [hregN] at hreg'
                have hpair := Option.some.inj hreg'
                have hfst : (Sum.inl ba : NamedBarrier ⊕ SharedBarrier) = .inl b :=
                  congrArg Prod.fst hpair
                simp only [Sum.inl.injEq] at hfst
                exact hbba hfst.symm
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (s.BN b).synced := by
                have h : i ∈ (Function.update s.BN ba ⟨I, A + 1, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex
                exact absurd hex (by simp)
              exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              have hex' : s.E i = false := hex
              have hxt : x.thread ≠ t := by
                intro h
                rw [← hthx, h, he] at hex'
                exact absurd hex' (by simp)
              have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex'⟩
              have hgoal : i ∈ (Function.update s.BN ba ⟨I, A + 1, some na⟩ b).synced := by
                rw [hBb]
                exact hi'
              exact hgoal
          · intro hcnone
            have h : (Function.update s.BN ba ⟨I, A + 1, some na⟩ b).count =
                none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BN ba ⟨I, A + 1, some na⟩) b =
                NamedBarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              have hcmη := genFiber_mb_arrive hη
              rw [hcmdN'] at hcmη
              exact absurd (Option.some.inj hcmη) (by simp)
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
          have hit : η.thread ≠ t := by
            intro h
            have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
            rw [h, he] at hEth
            exact absurd hEth (by simp)
          refine ⟨η, hηpts, hηth, hηcmd,
            (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
          rw [hrc_same (.inr sb) (hnorec (.inr sb))]
          exact hEgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph, -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcmdN'; exact absurd (Option.some.inj hcmdN') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @sync_configure _ _ ba na cc he hbcfg =>
      set Cn := Config.run
        ({ s with E := Function.update s.E t false,
                  BN := Function.update s.BN ba ⟨[t], 0, some na⟩ })
        (Tc.set t ht (Cmd.sync_nb ba na :: cc)) with hCndef
      -- the `sync_nb` parks: nothing executes, `t` enters `ba`'s synced list
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync_nb ba na :: cc := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync_nb ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmemN
        hcmdN' rfl rfl hatN
      have hregN : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdN', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmemN, hregN⟩
      -- the stepping thread's program is unchanged (control stays at the sync)
      have hsetsame : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog t = Tc.prog t := by
        simp only [WeftCommon.CTA.set, Function.update_self]
        rw [hPt]
      have hnodrop : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          Tc.prog η.thread = (T.prog η.thread).drop η.idx →
          Cn.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) → False := by
        intro η hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hd2' : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hηt] at hd2' hd1
        rw [hsetsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        rw [hηt] at hidx
        omega
      -- pointer transfer for every thread (t's program is unchanged too)
      have hpointer_all : ∀ (x : ProgPoint),
          (pointerAt T x Cn ↔ pointerAt T x (Config.run s Tc)) := by
        intro x
        by_cases hxt : x.thread = t
        · have hsame : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog x.thread =
              Tc.prog x.thread := by
            rw [hxt, hsetsame]
          simp [hCndef, pointerAt, WeftCommon.Config.progOf, hsame]
        · exact hpointer_ne x _ _ ht hxt
      have hEeq : ∀ i, i ≠ t →
          (Function.update s.E t false) i = s.E i := fun i hi =>
        Function.update_of_ne hi _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        exact absurd hd2 (fun h => hnodrop η hidx hd1 h)
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            have hna : na = n := by
              have h : (Function.update s.BN b ⟨[t], 0, some na⟩ b).count = some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN b ⟨[t], 0, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ ([t] : List ThreadId) := by
                have h : i ∈ (Function.update s.BN b ⟨[t], 0, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                exact h
              have hit : i = t := by simpa using hi'
              refine ⟨⟨t, (T.prog t).length - (Tc.prog t).length⟩, hfibN, hit.symm,
                ⟨na, hcmdN'⟩, ?_, ?_⟩
              · exact (hpointer_all _).mpr hatN
              · rw [hit]
                exact Function.update_self ..
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · have h : i ∈ (Function.update s.BN b ⟨[t], 0, some na⟩ b).synced := by
                  rw [Function.update_self, hit]
                  simp
                exact h
              · exfalso
                have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hxt : x.thread ≠ t := by
                  intro h
                  rw [h] at hthx
                  exact hit hthx.symm
                have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                rw [hbcfg] at hi'
                have hi'' : i ∈ ([] : List ThreadId) := hi'
                simp at hi''
          · intro hcnone
            exfalso
            have h : (Function.update s.BN b ⟨[t], 0, some na⟩ b).count = none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BN ba ⟨[t], 0, some na⟩) b = s.BN b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.BN ba ⟨[t], 0, some na⟩ b).count = some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN ba ⟨[t], 0, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (s.BN b).synced := by
                have h : i ∈ (Function.update s.BN ba ⟨[t], 0, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hit : i ≠ t := by
                intro h
                rw [h, he] at hex
                exact absurd hex (by simp)
              refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
              have h : (Function.update s.E t false) i = false := by
                rw [hEeq i hit]
                exact hex
              exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · exfalso
                have hxt : x.thread = t := hthx.trans hit
                have hpx' := (hpointer_all x).mp hpx
                have hpxlen : (Tc.prog x.thread).length =
                    (T.prog x.thread).length - x.idx := hpx'
                rw [hxt] at hpxlen
                have hidxx : x.idx < (T.prog x.thread).length :=
                  ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
                rw [hxt] at hidxx
                have hxidx : x.idx = (T.prog t).length - (Tc.prog t).length := by
                  omega
                have hxeq : x = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  rw [hxeta, hxt, hxidx]
                have hreg' := (mem_genFiber.mp hxF).2
                rw [hxeq, hregN] at hreg'
                have hpair := Option.some.inj hreg'
                have hfst : (Sum.inl ba : NamedBarrier ⊕ SharedBarrier) = .inl b :=
                  congrArg Prod.fst hpair
                simp only [Sum.inl.injEq] at hfst
                exact hbba hfst.symm
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.BN ba ⟨[t], 0, some na⟩ b).synced := by
                  rw [hBb]
                  exact hi'
                exact hgoal
          · intro hcnone
            have h : (Function.update s.BN ba ⟨[t], 0, some na⟩ b).count = none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BN ba ⟨[t], 0, some na⟩) b =
                NamedBarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · exact hnodrop η hidx hd1 hd2
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
          have hit : i ≠ t := by
            intro h
            rw [h, he] at hEi
            exact absurd hEi (by simp)
          refine ⟨η, hηpts, hηth, hηcmd, (hpointer_all η).mpr hηat, ?_, ?_⟩
          · have h : (Function.update s.E t false) i = false := by
              rw [hEeq i hit]
              exact hEi
            exact h
          · rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            exact hEgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exact absurd hd2 (fun h => hnodrop y hidx hd1 h)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @sync_block _ _ ba na cc I A he hbcfg hpos hlt =>
      set Cn := Config.run
        ({ s with E := Function.update s.E t false,
                  BN := Function.update s.BN ba ⟨t :: I, A, some na⟩ })
        (Tc.set t ht (Cmd.sync_nb ba na :: cc)) with hCndef
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync_nb ba na :: cc := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync_nb ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmemN
        hcmdN' rfl rfl hatN
      have hregN : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdN', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmemN, hregN⟩
      have hsetsame : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog t = Tc.prog t := by
        simp only [WeftCommon.CTA.set, Function.update_self]
        rw [hPt]
      have hnodrop : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          Tc.prog η.thread = (T.prog η.thread).drop η.idx →
          Cn.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) → False := by
        intro η hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hd2' : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hηt] at hd2' hd1
        rw [hsetsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        rw [hηt] at hidx
        omega
      have hpointer_all : ∀ (x : ProgPoint),
          (pointerAt T x Cn ↔ pointerAt T x (Config.run s Tc)) := by
        intro x
        by_cases hxt : x.thread = t
        · have hsame : (Tc.set t ht (Cmd.sync_nb ba na :: cc)).prog x.thread =
              Tc.prog x.thread := by
            rw [hxt, hsetsame]
          simp [hCndef, pointerAt, WeftCommon.Config.progOf, hsame]
        · exact hpointer_ne x _ _ ht hxt
      have hEeq : ∀ i, i ≠ t →
          (Function.update s.E t false) i = s.E i := fun i hi =>
        Function.update_of_ne hi _ _
      have htnI : t ∉ I := by
        intro htI
        have hib : t ∈ s.blocked (Sum.inl ba) := by
          have h : t ∈ (s.BN ba).synced := by rw [hbcfg]; exact htI
          exact h
        have hef := hwf.2.2.2.2.2.2.1 (Sum.inl ba) t hib
        rw [he] at hef
        exact absurd hef (by simp)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        exact absurd hd2 (fun h => hnodrop η hidx hd1 h)
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        by_cases hbba : b = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            have hna : na = n := by
              have h : (Function.update s.BN b ⟨t :: I, A, some na⟩ b).count =
                  some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            have hcnt_eq := genFiber_count_eq hτ hη hfibN
            rw [hcmdN'] at hcnt_eq
            rw [hcnt_eq]
            simp only [Option.bind_some, Cmd.count?, Option.some.injEq]
            exact hna
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN b ⟨t :: I, A, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (t :: I) := by
                have h : i ∈ (Function.update s.BN b ⟨t :: I, A, some na⟩ b).synced := hi
                rw [Function.update_self] at h
                exact h
              rcases List.mem_cons.mp hi' with hit | hiI
              · refine ⟨⟨t, (T.prog t).length - (Tc.prog t).length⟩, hfibN, hit.symm,
                  ⟨na, hcmdN'⟩, ?_, ?_⟩
                · exact (hpointer_all _).mpr hatN
                · rw [hit]
                  exact Function.update_self ..
              · have hiI' : i ∈ (s.BN b).synced := by rw [hbcfg]; exact hiI
                obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hiI'
                have hit : i ≠ t := fun h => htnI (h ▸ hiI)
                refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
                have h : (Function.update s.E t false) i = false := by
                  rw [hEeq i hit]
                  exact hex
                exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · have h : i ∈ (Function.update s.BN b ⟨t :: I, A, some na⟩ b).synced := by
                  rw [Function.update_self, hit]
                  exact List.mem_cons_self ..
                exact h
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.BN b ⟨t :: I, A, some na⟩ b).synced := by
                  rw [Function.update_self]
                  rw [hbcfg] at hi'
                  exact List.mem_cons_of_mem _ hi'
                exact hgoal
          · intro hcnone
            exfalso
            have h : (Function.update s.BN b ⟨t :: I, A, some na⟩ b).count =
                none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BN ba ⟨t :: I, A, some na⟩) b = s.BN b :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn η hη
            rw [hrc_same (.inl b) (hnorec (.inl b))] at hη
            refine hcount n ?_ η hη
            have h : (Function.update s.BN ba ⟨t :: I, A, some na⟩ b).count =
                some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
            · have hgoal : ((Function.update s.BN ba ⟨t :: I, A, some na⟩) b).arrived =
                  ((genFiber T τ (.inl b)
                    ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i
            rw [hrc_same (.inl b) (hnorec (.inl b))]
            constructor
            · intro hi
              have hi' : i ∈ (s.BN b).synced := by
                have h : i ∈ (Function.update s.BN ba ⟨t :: I, A, some na⟩ b).synced := hi
                rw [hBb] at h
                exact h
              obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
              have hit : i ≠ t := by
                intro h
                rw [h, he] at hex
                exact absurd hex (by simp)
              refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
              have h : (Function.update s.E t false) i = false := by
                rw [hEeq i hit]
                exact hex
              exact h
            · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
              by_cases hit : i = t
              · exfalso
                have hxt : x.thread = t := hthx.trans hit
                have hpx' := (hpointer_all x).mp hpx
                have hpxlen : (Tc.prog x.thread).length =
                    (T.prog x.thread).length - x.idx := hpx'
                rw [hxt] at hpxlen
                have hidxx : x.idx < (T.prog x.thread).length :=
                  ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
                rw [hxt] at hidxx
                have hxidx : x.idx = (T.prog t).length - (Tc.prog t).length := by
                  omega
                have hxeq : x = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  rw [hxeta, hxt, hxidx]
                have hreg' := (mem_genFiber.mp hxF).2
                rw [hxeq, hregN] at hreg'
                have hpair := Option.some.inj hreg'
                have hfst : (Sum.inl ba : NamedBarrier ⊕ SharedBarrier) = .inl b :=
                  congrArg Prod.fst hpair
                simp only [Sum.inl.injEq] at hfst
                exact hbba hfst.symm
              · have hex' : s.E i = false := by
                  have h : (Function.update s.E t false) i = false := hex
                  rw [hEeq i hit] at h
                  exact h
                have hi' : i ∈ (s.BN b).synced := (hsync i).mpr
                  ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
                have hgoal : i ∈ (Function.update s.BN ba ⟨t :: I, A, some na⟩ b).synced := by
                  rw [hBb]
                  exact hi'
                exact hgoal
          · intro hcnone
            have h : (Function.update s.BN ba ⟨t :: I, A, some na⟩ b).count =
                none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BN ba ⟨t :: I, A, some na⟩) b =
                NamedBarrierState.unconfigured := by
              rw [hBb]
              exact hunc h
            exact hgoal
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · exact hnodrop η hidx hd1 hd2
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
          have hit : i ≠ t := by
            intro h
            rw [h, he] at hEi
            exact absurd hEi (by simp)
          refine ⟨η, hηpts, hηth, hηcmd, (hpointer_all η).mpr hηat, ?_, ?_⟩
          · have h : (Function.update s.E t false) i = false := by
              rw [hEeq i hit]
              exact hEi
            exact h
          · rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            exact hEgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exact absurd hd2 (fun h => hnodrop y hidx hd1 h)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @mb_init _ _ ba na _ he hbcfg =>
      set Cn := Config.run
        ({ s with BM := Function.update s.BM ba ⟨[], 0, some na, false⟩ })
        (Tc.set t ht P') with hCndef
      obtain ⟨-, -, -, hokU⟩ := check_true_parts hcheck
      -- the newly executing point: `t`'s head `init_mb ba na`
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.init_mb ba na :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.init_mb ba na) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T (τ' ++ [Cn])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      -- `ba` is uninitialized here, so no recycle of it ever happened in `τ'`
      have hrc0 : recycleCount (.inr ba) τ' (τ'.length - 1) = 0 :=
        recycleCount_zero_of_count_none hchain hlastidx rfl (by rw [hbcfg]; rfl)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hcmdN' rfl hmN
          simp only [Cmd.genValue] at hpgσ
          have hrca := recycleCount_append (.inr ba) τ' Cn
            (j := τ'.length - 1) (by omega)
          -- the reference-side generation is zero too
          obtain ⟨sd, hdone⟩ := hτ.2
          have hidxN : (T.prog t).length - (Tc.prog t).length <
              (T.prog t).length := by omega
          obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone
            (η := ⟨t, (T.prog t).length - (Tc.prog t).length⟩) hidxN
          have hpgτ := pointGen_eq_of_time hcmdN' rfl hmτ
          simp only [Cmd.genValue] at hpgτ
          obtain ⟨-, -, jτ, D, D', hjτ, hD, hD', hDdrop, hD'drop⟩ := hmτ
          obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp
            (show ((Config.run State.initial T).progOf t)[(T.prog t).length -
              (Tc.prog t).length]? = some (Cmd.init_mb ba na) from hcmdN')
          have hDcons : D.progOf t = Cmd.init_mb ba na ::
              ((Config.run State.initial T).progOf t).drop
                ((T.prog t).length - (Tc.prog t).length + 1) := by
            rw [hDdrop, List.drop_eq_getElem_cons hlt0, hget0]
          have hstepτ := chain_step hτ.1.1.subtrace hD hD'
          obtain ⟨sD, TD, hDeq, hDun⟩ := init_drop_uninitialized hstepτ hDcons hD'drop
          subst hDeq
          have hrcτ0 : recycleCount (.inr ba) τ jτ = 0 :=
            recycleCount_zero_of_count_none hτ.1.1.subtrace hD rfl
              (by rw [hDun]; rfl)
          subst hjτ
          simp only [Nat.add_sub_cancel] at hpgτ
          rw [hrcτ0] at hpgτ
          rw [hpgσ, hrca, hrc0, hpgτ]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl b) (hnorec (.inl b))]
          exact hcount
        · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              rw [hcm] at hcmdN'
              have hcr : c = Cmd.init_mb ba na := Option.some.inj hcmdN'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i
          rw [hrc_same (.inl b) (hnorec (.inl b))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        by_cases hbba : sb = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            have hna : na = n := by
              have h : (Function.update s.BM sb ⟨[], 0, some na, false⟩ sb).count =
                  some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            rw [← hna]
            exact initCountOf_eq_of_cmdAt hokU hmemN hcmdN'
          · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
            · have hgoal : ((Function.update s.BM sb ⟨[], 0, some na, false⟩) sb).arrived =
                  ((genFiber T τ (.inr sb)
                    ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                rw [hcm] at hcmdN'
                have hcr : c = Cmd.init_mb sb na := Option.some.inj hcmdN'
                rw [hcr] at hcarr
                simp [Cmd.isArrive] at hcarr
          · intro i hi
            exfalso
            have h : i ∈ (Function.update s.BM sb ⟨[], 0, some na, false⟩ sb).waiting := hi
            rw [Function.update_self] at h
            simp at h
          · intro hcnone
            exfalso
            have h : (Function.update s.BM sb ⟨[], 0, some na, false⟩ sb).count =
                none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BM ba ⟨[], 0, some na, false⟩) sb = s.BM sb :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            refine hcount n ?_
            have h : (Function.update s.BM ba ⟨[], 0, some na, false⟩ sb).count =
                some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
            · have hgoal : ((Function.update s.BM ba ⟨[], 0, some na, false⟩) sb).arrived =
                  ((genFiber T τ (.inr sb)
                    ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                rw [hcm] at hcmdN'
                have hcr : c = Cmd.init_mb ba na := Option.some.inj hcmdN'
                rw [hcr] at hcarr
                simp [Cmd.isArrive] at hcarr
          · intro i hi
            have hi' : i ∈ (s.BM sb).waiting := by
              have h : i ∈ (Function.update s.BM ba ⟨[], 0, some na, false⟩ sb).waiting := hi
              rw [hBb] at h
              exact h
            obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi'
            have hit : η.thread ≠ t := by
              intro h
              have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
              rw [h, he] at hEth
              exact absurd hEth (by simp)
            refine ⟨η, hηpts, hηth, hηcmd,
              (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
            rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            exact hEgen
          · intro hcnone
            have h : (Function.update s.BM ba ⟨[], 0, some na, false⟩ sb).count =
                none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BM ba ⟨[], 0, some na, false⟩) sb =
                MBarrierState.uninitialized := by
              rw [hBb]
              exact hunin h
            exact hgoal
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph, -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcmdN'; exact absurd (Option.some.inj hcmdN') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @mb_arrive _ _ ba _ I A na ph he hbcfg =>
      set Cn := Config.run
        ({ s with BM := Function.update s.BM ba ⟨I, A + 1, some na, ph⟩ })
        (Tc.set t ht P') with hCndef
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive_mb ba :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive_mb ba) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmemN
        hcmdN' rfl rfl hatN
      have hregN : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inr ba,
            ((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdN', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hfibN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inr ba)
            ((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmemN, hregN⟩
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T (τ' ++ [Cn])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hcmdN' rfl hmN
          simp only [Cmd.genValue] at hpgσ
          have hrca := recycleCount_append (.inr ba) τ' Cn
            (j := τ'.length - 1) (by omega)
          rw [hpgσ, hrca, hrr]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl b) (hnorec (.inl b))]
          exact hcount
        · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              have hreg' := (mem_genFiber.mp hη).2
              rw [hregN] at hreg'
              have hpair := Option.some.inj hreg'
              have hfst : (Sum.inr ba : NamedBarrier ⊕ SharedBarrier) = .inl b :=
                congrArg Prod.fst hpair
              simp at hfst
        · intro i
          rw [hrc_same (.inl b) (hnorec (.inl b))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        by_cases hbba : sb = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            have hna : na = n := by
              have h : (Function.update s.BM sb ⟨I, A + 1, some na, ph⟩ sb).count =
                  some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            rw [← hna]
            exact hcount na (by rw [hbcfg])
          · rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            have harrA : A =
                ((genFiber T τ (.inr sb)
                  ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              have h := harr
              rw [hbcfg] at h
              exact h
            have hLHS : ((Function.update s.BM sb ⟨I, A + 1, some na, ph⟩) sb).arrived =
                A + 1 := by
              rw [Function.update_self]
            have hcnt_new :
                ((genFiber T τ (.inr sb)
                  ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η &&
                    (pointTime T (τ' ++ [Cn]) η).isSome).length =
                ((genFiber T τ (.inr sb)
                  ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length + 1 := by
              rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
              refine countP_succ_of_unique (genFiber_nodup T τ (.inr sb) _) hfibN ?_ ?_ ?_
              · obtain ⟨mN, hmN⟩ := hσNt
                simp [isArriveCmd, hcmdN', Cmd.isArrive, hmN]
              · simp [isArriveCmd, hcmdN', Cmd.isArrive, hτ'N]
              · intro x hx hxne
                cases hcmx : T.cmdAt x with
                | none => simp [isArriveCmd, hcmx]
                | some cmd =>
                  cases hcarrx : cmd.isArrive with
                  | false => simp [isArriveCmd, hcmx, hcarrx]
                  | true =>
                    simp only [isArriveCmd, hcmx, hcarrx, Bool.true_and]
                    cases hptx : pointTime T (τ' ++ [Cn]) x with
                    | none =>
                      cases hptx' : pointTime T τ' x with
                      | none => rfl
                      | some mx =>
                        have h := pointTime_append_some (C' := Cn) hptx'
                        rw [hptx] at h
                        exact absurd h (by simp)
                    | some mx =>
                      rcases htime_cases x mx hptx with hold | ⟨-, -, hidx, hd1, hd2⟩
                      · rw [hold]
                      · exact absurd (huniq x hidx hd1 hd2) hxne
            rw [hLHS, hcnt_new, ← harrA]
          · intro i hi
            have hiI : i ∈ I := by
              have h : i ∈ (Function.update s.BM sb ⟨I, A + 1, some na, ph⟩ sb).waiting := hi
              rw [Function.update_self] at h
              exact h
            have hiold : i ∈ (s.BM sb).waiting := by rw [hbcfg]; exact hiI
            obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hiold
            have hit : η.thread ≠ t := by
              intro h
              have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
              rw [h, he] at hEth
              exact absurd hEth (by simp)
            refine ⟨η, hηpts, hηth, hηcmd,
              (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
            rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            exact hEgen
          · intro hcnone
            exfalso
            have h : (Function.update s.BM sb ⟨I, A + 1, some na, ph⟩ sb).count =
                none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BM ba ⟨I, A + 1, some na, ph⟩) sb = s.BM sb :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            refine hcount n ?_
            have h : (Function.update s.BM ba ⟨I, A + 1, some na, ph⟩ sb).count =
                some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
            · have hgoal : ((Function.update s.BM ba ⟨I, A + 1, some na, ph⟩) sb).arrived =
                  ((genFiber T τ (.inr sb)
                    ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · have hηeq := huniq η hidx hd1 hd2
                subst hηeq
                have hcmη := genFiber_mb_arrive hη
                rw [hcmdN'] at hcmη
                have hinj := Option.some.inj hcmη
                simp only [Cmd.arrive_mb.injEq] at hinj
                exact hbba hinj.symm
          · intro i hi
            have hi' : i ∈ (s.BM sb).waiting := by
              have h : i ∈ (Function.update s.BM ba ⟨I, A + 1, some na, ph⟩ sb).waiting := hi
              rw [hBb] at h
              exact h
            obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi'
            have hit : η.thread ≠ t := by
              intro h
              have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
              rw [h, he] at hEth
              exact absurd hEth (by simp)
            refine ⟨η, hηpts, hηth, hηcmd,
              (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
            rw [hrc_same (.inr sb) (hnorec (.inr sb))]
            exact hEgen
          · intro hcnone
            have h : (Function.update s.BM ba ⟨I, A + 1, some na, ph⟩ sb).count =
                none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BM ba ⟨I, A + 1, some na, ph⟩) sb =
                MBarrierState.uninitialized := by
              rw [hBb]
              exact hunin h
            exact hgoal
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exfalso
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb, ph', -, hyc⟩ | ⟨nb, n, -, hyc⟩ <;>
          (rw [hyc] at hcmdN'; exact absurd (Option.some.inj hcmdN') (by simp))
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @mb_wait_block _ _ ba ph cc I A na he hbcfg =>
      set Cn := Config.run
        ({ s with E := Function.update s.E t false,
                  BM := Function.update s.BM ba ⟨t :: I, A, some na, ph⟩ })
        (Tc.set t ht (Cmd.wait_mb ba ph :: cc)) with hCndef
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.wait_mb ba ph :: cc := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.wait_mb ba ph) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hwg := conforms_wait_gen_block hτ hcheck htr hconf hlast hbar hmbar
        hmemN hcmdN' hatN hbcfg
      have hsetsame : (Tc.set t ht (Cmd.wait_mb ba ph :: cc)).prog t = Tc.prog t := by
        simp only [WeftCommon.CTA.set, Function.update_self]
        rw [hPt]
      have hnodrop : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          Tc.prog η.thread = (T.prog η.thread).drop η.idx →
          Cn.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) → False := by
        intro η hidx hd1 hd2
        have hηt := hident_thread η hidx hd1 hd2
        have hd2' : (Tc.set t ht (Cmd.wait_mb ba ph :: cc)).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hηt] at hd2' hd1
        rw [hsetsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        rw [hηt] at hidx
        omega
      have hpointer_all : ∀ (x : ProgPoint),
          (pointerAt T x Cn ↔ pointerAt T x (Config.run s Tc)) := by
        intro x
        by_cases hxt : x.thread = t
        · have hsame : (Tc.set t ht (Cmd.wait_mb ba ph :: cc)).prog x.thread =
              Tc.prog x.thread := by
            rw [hxt, hsetsame]
          simp [hCndef, pointerAt, WeftCommon.Config.progOf, hsame]
        · exact hpointer_ne x _ _ ht hxt
      have hEeq : ∀ i, i ≠ t →
          (Function.update s.E t false) i = s.E i := fun i hi =>
        Function.update_of_ne hi _ _
      have htnI : t ∉ I := by
        intro htI
        have hib : t ∈ s.blocked (Sum.inr ba) := by
          have h : t ∈ (s.BM ba).waiting := by rw [hbcfg]; exact htI
          exact h
        have hef := hwf.2.2.2.2.2.2.1 (Sum.inr ba) t hib
        rw [he] at hef
        exact absurd hef (by simp)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        exact absurd hd2 (fun h => hnodrop η hidx hd1 h)
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl b) (hnorec (.inl b))]
          exact hcount
        · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · exact hnodrop η hidx hd1 hd2
        · intro i
          rw [hrc_same (.inl b) (hnorec (.inl b))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hit : i ≠ t := by
              intro h
              rw [h, he] at hex
              exact absurd hex (by simp)
            refine ⟨x, hxF, hthx, hsx, (hpointer_all x).mpr hpx, ?_⟩
            have h : (Function.update s.E t false) i = false := by
              rw [hEeq i hit]
              exact hex
            exact h
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            by_cases hit : i = t
            · exfalso
              have hxt : x.thread = t := hthx.trans hit
              have hpx' := (hpointer_all x).mp hpx
              have hpxlen : (Tc.prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx'
              rw [hxt] at hpxlen
              have hidxx : x.idx < (T.prog x.thread).length :=
                ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
              rw [hxt] at hidxx
              have hxidx : x.idx = (T.prog t).length - (Tc.prog t).length := by
                omega
              have hxeq : x = ⟨t, (T.prog t).length - (Tc.prog t).length⟩ := by
                have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                rw [hxeta, hxt, hxidx]
              obtain ⟨nx, hcx⟩ := hsx
              rw [hxeq, hcmdN'] at hcx
              exact absurd (Option.some.inj hcx) (by simp)
            · have hex' : s.E i = false := by
                have h : (Function.update s.E t false) i = false := hex
                rw [hEeq i hit] at h
                exact h
              exact (hsync i).mpr
                ⟨x, hxF, hthx, hsx, (hpointer_all x).mp hpx, hex'⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        by_cases hbba : sb = ba
        · subst hbba
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            have hna : na = n := by
              have h : (Function.update s.BM sb ⟨t :: I, A, some na, ph⟩ sb).count =
                  some n := hn
              rw [Function.update_self] at h
              exact Option.some.inj h
            rw [← hna]
            exact hcount na (by rw [hbcfg])
          · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
            · have hgoal : ((Function.update s.BM sb ⟨t :: I, A, some na, ph⟩) sb).arrived =
                  ((genFiber T τ (.inr sb)
                    ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [Function.update_self]
                have h := harr
                rw [hbcfg] at h
                exact h
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i hi
            have hi' : i ∈ (t :: I) := by
              have h : i ∈ (Function.update s.BM sb ⟨t :: I, A, some na, ph⟩ sb).waiting := hi
              rw [Function.update_self] at h
              exact h
            rcases List.mem_cons.mp hi' with hit | hiI
            · subst hit
              refine ⟨⟨i, (T.prog i).length - (Tc.prog i).length⟩, hmemN, rfl,
                ⟨ph, hcmdN'⟩, (hpointer_all _).mpr hatN, Function.update_self .., ?_⟩
              rw [hrc_same (.inr sb) (hnorec (.inr sb))]
              exact hwg
            · have hiold : i ∈ (s.BM sb).waiting := by rw [hbcfg]; exact hiI
              obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hiold
              have hit : i ≠ t := fun h => htnI (h ▸ hiI)
              refine ⟨η, hηpts, hηth, hηcmd, (hpointer_all η).mpr hηat, ?_, ?_⟩
              · have h : (Function.update s.E t false) i = false := by
                  rw [hEeq i hit]
                  exact hEi
                exact h
              · rw [hrc_same (.inr sb) (hnorec (.inr sb))]
                exact hEgen
          · intro hcnone
            exfalso
            have h : (Function.update s.BM sb ⟨t :: I, A, some na, ph⟩ sb).count =
                none := hcnone
            rw [Function.update_self] at h
            simp at h
        · have hBb : (Function.update s.BM ba ⟨t :: I, A, some na, ph⟩) sb = s.BM sb :=
            Function.update_of_ne hbba _ _
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n hn
            refine hcount n ?_
            have h : (Function.update s.BM ba ⟨t :: I, A, some na, ph⟩ sb).count =
                some n := hn
            rw [hBb] at h
            exact h
          · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
            · have hgoal : ((Function.update s.BM ba ⟨t :: I, A, some na, ph⟩) sb).arrived =
                  ((genFiber T τ (.inr sb)
                    ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
                rw [hBb]
                exact harr
              exact hgoal
            · intro η hη c hcm hcarr hpt
              rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
              · have := (pointTime_spec hchain h0 hold).2.1
                omega
              · exact hnodrop η hidx hd1 hd2
          · intro i hi
            have hi' : i ∈ (s.BM sb).waiting := by
              have h : i ∈ (Function.update s.BM ba ⟨t :: I, A, some na, ph⟩ sb).waiting := hi
              rw [hBb] at h
              exact h
            obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi'
            have hit : i ≠ t := by
              intro h
              rw [h] at hEi
              rw [he] at hEi
              exact absurd hEi (by simp)
            refine ⟨η, hηpts, hηth, hηcmd, (hpointer_all η).mpr hηat, ?_, ?_⟩
            · have h : (Function.update s.E t false) i = false := by
                rw [hEeq i hit]
                exact hEi
              exact h
            · rw [hrc_same (.inr sb) (hnorec (.inr sb))]
              exact hEgen
          · intro hcnone
            have h : (Function.update s.BM ba ⟨t :: I, A, some na, ph⟩ sb).count =
                none := hcnone
            rw [hBb] at h
            have hgoal : (Function.update s.BM ba ⟨t :: I, A, some na, ph⟩) sb =
                MBarrierState.uninitialized := by
              rw [hBb]
              exact hunin h
            exact hgoal
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        exact absurd hd2 (fun h => hnodrop y hidx hd1 h)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
    | @mb_wait_pass _ _ ba ph _ I A na ph' he hbcfg hnep =>
      set Cn := Config.run s (Tc.set t ht P') with hCndef
      have hsuf : (Config.run s Tc).progOf t <:+
          (Config.run State.initial T).progOf t :=
        progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
      have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hPt' : (Config.run s Tc).progOf t = Cmd.wait_mb ba ph :: P' := hPt
      have hcmdN := cmd_at_last hsuf hPt'
      have hcmdN' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.wait_mb ba ph) := hcmdN
      have hatN : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmemN : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdN
      have hwgp := conforms_wait_gen_pass hτ hcheck htr hconf hlast hbar hmbar
        hmemN hcmdN' hatN hbcfg hnep
      have hτ'N : pointTime T τ' ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = none :=
        pointTime_none_of_pointerAt hchain h0 hlast hatN
      have hσNt : ∃ mN, pointTime T (τ' ++ [Cn])
          ⟨t, (T.prog t).length - (Tc.prog t).length⟩ = some mN := by
        refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
          (i := t) (k := (T.prog t).length - (Tc.prog t).length) (by omega) ?_
        change ((Tc.set t ht P').prog t).length +
          ((T.prog t).length - (Tc.prog t).length + 1) ≤ (T.prog t).length
        have hset : (Tc.set t ht P').prog t = P' := by
          simp [WeftCommon.CTA.set, Function.update_self]
        rw [hset]
        have hcclen : (Tc.prog t).length = P'.length + 1 := by rw [hPt]; simp
        omega
      -- the barrier's phase mismatches `ph` at the last configuration
      have hph'' : ph' = phaseAfter (recycleCount (.inr ba) τ' (τ'.length - 1)) := by
        have hph := phase_eq_phaseAfter hchain h0idx ba (τ'.length - 1) _ s
          hlastidx rfl
        rw [hbcfg] at hph
        exact hph
      have hphase : ¬ (phaseAfter (recycleCount (.inr ba) τ' (τ'.length - 1)) = ph) := by
        intro hcon
        exact hnep (hph''.trans hcon).symm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Te h
        rw [List.getLast?_concat, Option.some.injEq] at h
        exact absurd h (by simp)
      · refine hgen_all ?_
        intro η hnone hidx hd1 hd2
        have hηeq := huniq η hidx hd1 hd2
        subst hηeq
        obtain ⟨mN, hmN⟩ := hσNt
        rcases pointTime_append_cases hne hmN with hold | ⟨-, hmNN⟩
        · rw [hτ'N] at hold
          exact absurd hold (by simp)
        · subst hmNN
          have hpgσ := pointGen_eq_of_pointTime hcmdN' rfl hmN
          have hrca := recycleCount_append (.inr ba) τ' Cn
            (j := τ'.length - 1) (by omega)
          rw [hrca] at hpgσ
          have hgv : (Cmd.wait_mb ba ph).genValue
              (recycleCount (.inr ba) τ' (τ'.length - 1)) =
              ((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ) - 1 := by
            simp [Cmd.genValue, hphase]
          rw [hgv] at hpgσ
          rw [hpgσ, hwgp]
      · intro Cl hCl sl hsl b
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
        refine ⟨?_, ?_, ?_, hunc⟩
        · rw [hrc_same (.inl b) (hnorec (.inl b))]
          exact hcount
        · rw [hrc_same (.inl b) (hnorec (.inl b)), hfilter_same (.inl b) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              rw [hcm] at hcmdN'
              have hcr : c = Cmd.wait_mb ba ph := Option.some.inj hcmdN'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i
          rw [hrc_same (.inl b) (hnorec (.inl b))]
          constructor
          · intro hi
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mpr hpx, hex⟩
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            have hxt : x.thread ≠ t := by
              intro h
              rw [← hthx, h, he] at hex
              exact absurd hex (by simp)
            exact (hsync i).mpr
              ⟨x, hxF, hthx, hsx, (hpointer_ne x _ _ ht hxt).mp hpx, hex⟩
      · intro Cl hCl sl hsl sb
        rw [List.getLast?_concat, Option.some.injEq] at hCl
        subst hCl
        rw [hCndef] at hsl
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
        subst hsl
        obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
        refine ⟨hcount, ?_, ?_, hunin⟩
        · rw [hrc_same (.inr sb) (hnorec (.inr sb)), hfilter_same (.inr sb) _ ?_]
          · exact harr
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · have hηeq := huniq η hidx hd1 hd2
              subst hηeq
              rw [hcm] at hcmdN'
              have hcr : c = Cmd.wait_mb ba ph := Option.some.inj hcmdN'
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i hi
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
          have hit : η.thread ≠ t := by
            intro h
            have hEth : s.E η.thread = false := by rw [hηth]; exact hEi
            rw [h, he] at hEth
            exact absurd hEth (by simp)
          refine ⟨η, hηpts, hηth, hηcmd,
            (hpointer_ne η _ _ ht hit).mpr hηat, hEi, ?_⟩
          rw [hrc_same (.inr sb) (hnorec (.inr sb))]
          exact hEgen
      · refine hedge_all ?_
        intro y hidx hd1 hd2 x hxpts hcases hgenxy
        have hηeq := huniq y hidx hd1 hd2
        subst hηeq
        rcases hcases with ⟨nb, n, -, hyc⟩ | ⟨sb', ph₂, hxc, hyc⟩ | ⟨nb, n, -, hyc⟩
        · exfalso
          rw [hyc] at hcmdN'
          exact absurd (Option.some.inj hcmdN') (by simp)
        · -- the arriveWait in-edge: `x` sits in the closed round `r − 1`
          rw [hcmdN'] at hyc
          have hy := Option.some.inj hyc
          simp only [Cmd.wait_mb.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          have hgx : pointGen T τ x =
              some (((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ) - 1) := by
            rw [hgenxy, hwgp]
          have hnn : 0 ≤ ((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ) - 1 :=
            pointGen_registrant_nonneg hxc rfl hgx
          have hr1 : 1 ≤ recycleCount (.inr ba) τ' (τ'.length - 1) := by omega
          have hregx : registrantGen T τ x = some (.inr ba,
              ((recycleCount (.inr ba) τ' (τ'.length - 1) - 1 : ℕ) : ℤ)) := by
            unfold registrantGen
            have hcast : ((recycleCount (.inr ba) τ' (τ'.length - 1) - 1 : ℕ) : ℤ) =
                ((recycleCount (.inr ba) τ' (τ'.length - 1) : ℕ) : ℤ) - 1 := by
              omega
            simp [hxc, hgx, Cmd.isRegistrant, Cmd.barrier?, hcast]
          have hxfib : x ∈ genFiber T τ (.inr ba)
              ((recycleCount (.inr ba) τ' (τ'.length - 1) - 1 : ℕ) : ℤ) :=
            mem_genFiber.mpr ⟨hxpts, hregx⟩
          obtain ⟨mx, hmx⟩ := hconf.rounds_complete (.inr ba)
            (recycleCount (.inr ba) τ' (τ'.length - 1) - 1) (by omega) x hxfib
          have hmxlt : mx < τ'.length := (pointTime_spec hchain h0 hmx).2.1
          exact ⟨mx, by omega, pointTime_append_some hmx⟩
        · exfalso
          rw [hyc] at hcmdN'
          exact absurd (Option.some.inj hcmdN') (by simp)
      · refine hrounds_all ?_
        intro b hrb
        exact absurd hrb (by rw [hnorec b]; simp)
      · intro sb' g' hgle n₀ hinit
        rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
  | @recycle s₀ Tc₀ nb I A n hb hfull hpark =>
    set Cn := Config.run
      ({ s with E := updateMapOn s.E I true,
                BN := Function.update s.BN nb NamedBarrierState.unconfigured })
      (Tc.wake I) with hCndef
    -- this step is exactly a recycle of `nb`
    have hrecb : stepRecyclesBarrier (.inl nb) (Config.run s Tc) Cn = true := by
      rw [hCndef]
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
        NamedBarrierState.isFull, hfull, Function.update_self]
    have hnorecb : ∀ b, b ≠ Sum.inl nb →
        stepRecyclesBarrier b (Config.run s Tc) Cn = false := by
      intro b hbne
      cases b with
      | inl nb' =>
        have hne' : nb' ≠ nb := fun h => hbne (by rw [h])
        have hupd : (Function.update s.BN nb NamedBarrierState.unconfigured) nb' =
            s.BN nb' := Function.update_of_ne hne' _ _
        rw [hCndef]
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BN nb').isFull
        · simp
        · simp only [Bool.true_and, hupd, decide_eq_false_iff_not]
          intro hunc
          rw [hunc] at hfl
          simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
      | inr sb =>
        rw [hCndef]
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BM sb).isFull
        · simp
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          intro hflip
          exact mb_flip_ne (s.BM sb) hflip
    -- the fullness pigeonhole: the round holds its entire fiber
    have hff := conforms_full_fiber hτ htr hconf hlast hb hfull
    -- a disabled thread after the wake was disabled before and is not woken
    have hEfalse : ∀ i, updateMapOn s.E I true i = false → i ∉ I ∧ s.E i = false := by
      intro i hEi
      rw [updateMapOn_apply] at hEi
      by_cases hiI : i ∈ I
      · rw [if_pos hiI] at hEi
        exact absurd hEi (by simp)
      · rw [if_neg hiI] at hEi
        exact ⟨hiI, hEi⟩
    -- a pointer sitting at a thread's head names the head command
    have hhead_cmd : ∀ (x : ProgPoint), pointerAt T x (Config.run s Tc) →
        x.idx < (T.prog x.thread).length →
        ∀ (c₀ : Cmd), (Tc.prog x.thread).head? = some c₀ → T.cmdAt x = some c₀ := by
      intro x hpx hidx c₀ hhd
      have hsufx : (Config.run s Tc).progOf x.thread <:+
          (Config.run State.initial T).progOf x.thread :=
        progOf_suffix_index_le hchain x.thread h0idx (Nat.zero_le _) hlastidx
      have hdrop : Tc.prog x.thread =
          (T.prog x.thread).drop
            ((T.prog x.thread).length - (Tc.prog x.thread).length) :=
        List.IsSuffix.eq_drop hsufx
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hidxeq : (T.prog x.thread).length - (Tc.prog x.thread).length = x.idx := by
        omega
      rw [hidxeq] at hdrop
      have hdd : (T.prog x.thread).drop x.idx =
          (T.prog x.thread)[x.idx]'hidx :: (T.prog x.thread).drop (x.idx + 1) :=
        List.drop_eq_getElem_cons hidx
      rw [hdrop, hdd] at hhd
      simp only [List.head?_cons, Option.some.injEq] at hhd
      have hg : (T.prog x.thread)[x.idx]? = some c₀ := by
        rw [List.getElem?_eq_getElem hidx, hhd]
      exact hg
    -- the appended step's drops are exactly the woken parked syncs
    have hnew_char : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        Cn.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) →
        η.thread ∈ I ∧ T.cmdAt η = some (Cmd.sync_nb nb n) ∧
          pointerAt T η (Config.run s Tc) := by
      intro η hidx hd1 hd2
      by_cases hηI : η.thread ∈ I
      · have hhd := hpark η.thread hηI
        have hdd : (T.prog η.thread).drop η.idx =
            (T.prog η.thread)[η.idx]'hidx :: (T.prog η.thread).drop (η.idx + 1) :=
          List.drop_eq_getElem_cons hidx
        rw [hd1, hdd] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        refine ⟨hηI, ?_, ?_⟩
        · have hg : (T.prog η.thread)[η.idx]? = some (Cmd.sync_nb nb n) := by
            rw [List.getElem?_eq_getElem hidx, hhd]
          exact hg
        · have hg : (Tc.prog η.thread).length =
              (T.prog η.thread).length - η.idx := by
            rw [hd1]
            simp [List.length_drop]
          exact hg
      · exfalso
        have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
          simp [WeftCommon.CTA.wake, if_neg hηI]
        have hd2' : (Tc.wake I).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        omega
    -- a woken parked sync executes in the appended trace
    have hnewtime : ∀ (x : ProgPoint), x.thread ∈ I →
        pointerAt T x (Config.run s Tc) → x.idx < (T.prog x.thread).length →
        ∃ m, pointTime T (τ' ++ [Cn]) x = some m := by
      intro x hxI hpx hidx
      refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
        (i := x.thread) (k := x.idx) hidx ?_
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hposx : 0 < (Tc.prog x.thread).length := by
        have hhd := hpark x.thread hxI
        cases hTt : Tc.prog x.thread with
        | nil => rw [hTt] at hhd; simp at hhd
        | cons a l => simp
      have hwake : (Tc.wake I).prog x.thread = (Tc.prog x.thread).tail := by
        simp [WeftCommon.CTA.wake, if_pos hxI]
      change ((Tc.wake I).prog x.thread).length + (x.idx + 1) ≤
        (T.prog x.thread).length
      rw [hwake]
      have htl : ((Tc.prog x.thread).tail).length = (Tc.prog x.thread).length - 1 := by
        simp [List.length_tail]
      omega
    -- a parked sync of the closing round is a fiber member
    have hgen_of_park : ∀ (η : ProgPoint), η.thread ∈ I →
        pointerAt T η (Config.run s Tc) → η.idx < (T.prog η.thread).length →
        η ∈ genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
      intro η hηI hpη hidx
      obtain ⟨hcount, harr, hsync, -⟩ := hconf.state _ hlast s rfl nb
      have hiI : η.thread ∈ (s.BN nb).synced := by rw [hb]; exact hηI
      obtain ⟨x, hxF, hthx, hsx, hpx', hex⟩ := (hsync η.thread).mp hiI
      have hxeq : x = η := by
        have hpxlen : (Tc.prog x.thread).length =
            (T.prog x.thread).length - x.idx := hpx'
        have hηlen : (Tc.prog η.thread).length =
            (T.prog η.thread).length - η.idx := hpη
        have hidxx : x.idx < (T.prog x.thread).length :=
          ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
        rw [hthx] at hpxlen hidxx
        have hxidx : x.idx = η.idx := by omega
        have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
        have hηeta : η = ⟨η.thread, η.idx⟩ := rfl
        rw [hxeta, hηeta, hthx, hxidx]
      rw [hxeq] at hxF
      exact hxF
    -- clause 4's fresh round: everything in the closing fiber has now executed
    have hround_new : ∀ b, stepRecyclesBarrier b (Config.run s Tc) Cn = true →
        ∀ η ∈ genFiber T τ b ((recycleCount b τ' (τ'.length - 1) : ℕ) : ℤ),
          ∃ m, pointTime T (τ' ++ [Cn]) η = some m := by
      intro b hrb η hη
      have hbb : b = Sum.inl nb := by
        by_contra hne'
        rw [hnorecb b hne'] at hrb
        exact absurd hrb (by simp)
      subst hbb
      have hidx : η.idx < (T.prog η.thread).length :=
        ((mem_progPoints_iff T η).mp (mem_genFiber.mp hη).1).2
      obtain ⟨harr_ex, hsyn_park⟩ := hff η hη
      rcases genFiber_nb_cases hη with ⟨nn, hcm⟩ | ⟨nn, hcm⟩
      · obtain ⟨m, hm⟩ := harr_ex ⟨nn, hcm⟩
        exact ⟨m, pointTime_append_some hm⟩
      · obtain ⟨hI, hpx⟩ := hsyn_park nn hcm
        exact hnewtime η hI hpx hidx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Te h
      rw [List.getLast?_concat, Option.some.injEq] at h
      exact absurd h (by simp)
    · -- gen_eq: the new executions are the woken syncs, whose generation the old
      -- clause 2 already pinned to the closing round
      refine hgen_all ?_
      intro η hnone hidx hd1 hd2
      obtain ⟨hηI, hcm, hpη⟩ := hnew_char η hidx hd1 hd2
      have hηF := hgen_of_park η hηI hpη hidx
      obtain ⟨cy, hcy, -, -, hgenη⟩ := registrantGen_some (mem_genFiber.mp hηF).2
      obtain ⟨m, hm⟩ := hnewtime η hηI hpη hidx
      rcases pointTime_append_cases hne hm with hold | ⟨-, hmN⟩
      · rw [hnone] at hold
        exact absurd hold (by simp)
      · subst hmN
        have hpgσ := pointGen_eq_of_pointTime hcm rfl hm
        simp only [Cmd.genValue] at hpgσ
        have hrca := recycleCount_append (.inl nb) τ' Cn
          (j := τ'.length - 1) (by omega)
        rw [hpgσ, hrca, hgenη]
    · -- named-barrier state
      intro Cl hCl sl hsl b
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      rw [hCndef] at hsl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
      by_cases hbb : b = nb
      · subst hbb
        have hBb : (Function.update s.BN b NamedBarrierState.unconfigured) b =
            NamedBarrierState.unconfigured := Function.update_self ..
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n' hn
          exfalso
          have h : (Function.update s.BN b NamedBarrierState.unconfigured b).count =
              some n' := hn
          rw [hBb] at h
          simp [NamedBarrierState.unconfigured] at h
        · -- arrived 0: nothing of the next fiber has executed
          have hLHS : ((Function.update s.BN b NamedBarrierState.unconfigured) b).arrived =
              0 := by
            rw [hBb]
            rfl
          rw [hrc_incr (.inl b) hrecb, hLHS]
          symm
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro x hx
          simp only [Bool.and_eq_true, not_and]
          intro hxarr hxsome
          obtain ⟨mx, hmx⟩ := Option.isSome_iff_exists.mp hxsome
          have hxmem := (mem_genFiber.mp hx).1
          obtain ⟨cx, hcx, hcxreg, hcxbar, hcxgen⟩ :=
            registrantGen_some (mem_genFiber.mp hx).2
          rcases pointTime_append_cases hne hmx with hold | ⟨-, hmN⟩
          · -- an executed member of the *next* round outruns the recycle count
            have hgx := hconf.gen_eq x hxmem mx hold
            have hpg := pointGen_eq_of_pointTime hcx hcxbar hold
            rw [genValue_of_isRegistrant hcxreg] at hpg
            rw [hpg, hcxgen] at hgx
            have hinj := Option.some.inj hgx
            have hmlt : mx < τ'.length := (pointTime_spec hchain h0 hold).2.1
            have hmono := recycleCount_mono (.inl b) τ'
              (show mx - 1 ≤ τ'.length - 1 by omega)
            omega
          · -- the new executions are syncs, not arrives
            subst hmN
            obtain ⟨hspec1, hspec2, hidxx, C₁, C₂, hC₁, hC₂, hdx1, hdx2⟩ :=
              pointTime_spec hchainσ h0σ hmx
            rw [hσN1] at hC₁
            obtain rfl := Option.some.inj hC₁
            rw [hσN] at hC₂
            obtain rfl := Option.some.inj hC₂
            obtain ⟨-, hcmx, -⟩ := hnew_char x hidxx hdx1 hdx2
            simp only [isArriveCmd, hcmx] at hxarr
            exact absurd hxarr (by simp [Cmd.isArrive])
        · -- synced: empty, and nothing of the next fiber can be parked
          intro i
          rw [hrc_incr (.inl b) hrecb]
          constructor
          · intro hi
            exfalso
            have h : i ∈ (Function.update s.BN b NamedBarrierState.unconfigured b).synced :=
              hi
            rw [hBb] at h
            simp [NamedBarrierState.unconfigured] at h
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            exfalso
            obtain ⟨hiI, hex'⟩ := hEfalse i hex
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            have hpxC : pointerAt T x (Config.run s Tc) := by
              have hpx' : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              rw [hsame] at hpx'
              exact hpx'
            have hidxx : x.idx < (T.prog x.thread).length :=
              ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
            -- `i` is disabled, so it is parked somewhere, at its head — which is `x`
            obtain ⟨b', hib'⟩ := hei i hex'
            cases b' with
            | inl nb'' =>
              rcases hsb' : s.BN nb'' with ⟨I', A', cnt'⟩
              cases cnt' with
              | none =>
                obtain ⟨hI0, -⟩ := hwf.2.1 nb'' I' A' hsb'
                have hib'' : i ∈ I' := by
                  have h : i ∈ (s.BN nb'').synced := hib'
                  rw [hsb'] at h
                  exact h
                rw [hI0] at hib''
                simp at hib''
              | some n' =>
                have hpk := (hwf.1 nb'' I' A' n' hsb').2.1 i (by
                  have h : i ∈ (s.BN nb'').synced := hib'
                  rw [hsb'] at h
                  exact h)
                have hcmx : T.cmdAt x = some (Cmd.sync_nb nb'' n') := by
                  refine hhead_cmd x hpxC hidxx _ ?_
                  rw [hthx]
                  exact hpk
                obtain ⟨sx, hsxc⟩ := hsx
                rw [hcmx] at hsxc
                have hinj := Option.some.inj hsxc
                simp only [Cmd.sync_nb.injEq] at hinj
                have hiI' : i ∈ I := by
                  have h : i ∈ (s.BN nb'').synced := hib'
                  rw [hinj.1, hb] at h
                  exact h
                exact hiI hiI'
            | inr sb'' =>
              rcases hsb' : s.BM sb'' with ⟨I', A', cnt', ph'⟩
              cases cnt' with
              | none =>
                obtain ⟨hI0, -, -⟩ := hwf.2.2.2.1 sb'' I' A' ph' hsb'
                have hib'' : i ∈ I' := by
                  have h : i ∈ (s.BM sb'').waiting := hib'
                  rw [hsb'] at h
                  exact h
                rw [hI0] at hib''
                simp at hib''
              | some n' =>
                have hpk := (hwf.2.2.1 sb'' I' A' n' ph' hsb').2 i (by
                  have h : i ∈ (s.BM sb'').waiting := hib'
                  rw [hsb'] at h
                  exact h)
                have hcmx : T.cmdAt x = some (Cmd.wait_mb sb'' ph') := by
                  refine hhead_cmd x hpxC hidxx _ ?_
                  rw [hthx]
                  exact hpk
                obtain ⟨sx, hsxc⟩ := hsx
                rw [hcmx] at hsxc
                exact absurd (Option.some.inj hsxc) (by simp)
        · intro hcnone
          have hg : (Function.update s.BN b NamedBarrierState.unconfigured) b =
              NamedBarrierState.unconfigured := hBb
          exact hg
      · -- b ≠ nb: state untouched, times untouched (the new executions live on nb)
        have hBb : (Function.update s.BN nb NamedBarrierState.unconfigured) b =
            s.BN b := Function.update_of_ne hbb _ _
        have hrcs := hrc_same (.inl b)
          (hnorecb (.inl b) (fun h => hbb (Sum.inl.inj h)))
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n' hn η hη
          rw [hrcs] at hη
          refine hcount n' ?_ η hη
          have h : (Function.update s.BN nb NamedBarrierState.unconfigured b).count =
              some n' := hn
          rw [hBb] at h
          exact h
        · rw [hrcs, hfilter_same (.inl b) _ ?_]
          · have hgoal : ((Function.update s.BN nb NamedBarrierState.unconfigured) b).arrived =
                ((genFiber T τ (.inl b)
                  ((recycleCount (.inl b) τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              rw [hBb]
              exact harr
            exact hgoal
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · obtain ⟨-, hcmη, -⟩ := hnew_char η hidx hd1 hd2
              rw [hcm] at hcmη
              have hcr : c = Cmd.sync_nb nb n := Option.some.inj hcmη
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i
          rw [hrcs]
          constructor
          · intro hi
            have hi' : i ∈ (s.BN b).synced := by
              have h : i ∈ (Function.update s.BN nb
                  NamedBarrierState.unconfigured b).synced := hi
              rw [hBb] at h
              exact h
            obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi'
            -- `i` is not woken: it is parked on `b ≠ nb` (one list per thread)
            have hiI : i ∉ I := by
              intro hiI
              have hib₀ : i ∈ s.blocked (Sum.inl nb) := by
                have h : i ∈ (s.BN nb).synced := by rw [hb]; exact hiI
                exact h
              have hibb : i ∈ s.blocked (Sum.inl b) := hi'
              have := hwf.2.2.2.2.2.2.2 (Sum.inl b) (Sum.inl nb) i hibb hib₀
              simp only [Sum.inl.injEq] at this
              exact hbb this
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            refine ⟨x, hxF, hthx, hsx, ?_, ?_⟩
            · have hpx' : (Tc.prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              have hg : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := by
                rw [hsame]
                exact hpx'
              exact hg
            · have hg : updateMapOn s.E I true i = false := by
                rw [updateMapOn_apply, if_neg hiI]
                exact hex
              exact hg
          · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
            obtain ⟨hiI, hex'⟩ := hEfalse i hex
            have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
              have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
              simp [WeftCommon.CTA.wake, if_neg hxIn]
            have hpxC : pointerAt T x (Config.run s Tc) := by
              have hpx' : ((Tc.wake I).prog x.thread).length =
                  (T.prog x.thread).length - x.idx := hpx
              rw [hsame] at hpx'
              exact hpx'
            have hi' : i ∈ (s.BN b).synced :=
              (hsync i).mpr ⟨x, hxF, hthx, hsx, hpxC, hex'⟩
            have hgoal : i ∈
                (Function.update s.BN nb NamedBarrierState.unconfigured b).synced := by
              rw [hBb]
              exact hi'
            exact hgoal
        · intro hcnone
          have h : (s.BN b).count = none := by
            have hg : (Function.update s.BN nb
                NamedBarrierState.unconfigured b).count = none := hcnone
            rw [hBb] at hg
            exact hg
          have hg : (Function.update s.BN nb NamedBarrierState.unconfigured) b =
              NamedBarrierState.unconfigured := by
            rw [hBb]
            exact hunc h
          exact hg
    · -- mbarrier state: untouched (the wake only re-enables `nb`'s syncers)
      intro Cl hCl sl hsl sb
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      rw [hCndef] at hsl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
      have hrcs := hrc_same (.inr sb) (hnorecb (.inr sb) (by simp))
      refine ⟨hcount, ?_, ?_, hunin⟩
      · rw [hrcs, hfilter_same (.inr sb) _ ?_]
        · exact harr
        · intro η hη c hcm hcarr hpt
          rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
          · have := (pointTime_spec hchain h0 hold).2.1
            omega
          · obtain ⟨-, hcmη, -⟩ := hnew_char η hidx hd1 hd2
            rw [hcm] at hcmη
            have hcr : c = Cmd.sync_nb nb n := Option.some.inj hcmη
            rw [hcr] at hcarr
            simp [Cmd.isArrive] at hcarr
      · intro i hi
        obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi
        have hiI : i ∉ I := by
          intro hiI
          have h1 : i ∈ s.blocked (Sum.inr sb) := hi
          have h2 : i ∈ s.blocked (Sum.inl nb) := by
            have h : i ∈ (s.BN nb).synced := by rw [hb]; exact hiI
            exact h
          have := hwf.2.2.2.2.2.2.2 (Sum.inr sb) (Sum.inl nb) i h1 h2
          exact absurd this (by simp)
        have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
          have hxIn : η.thread ∉ I := by rw [hηth]; exact hiI
          simp [WeftCommon.CTA.wake, if_neg hxIn]
        refine ⟨η, hηpts, hηth, hηcmd, ?_, ?_, ?_⟩
        · have hpx' : (Tc.prog η.thread).length =
              (T.prog η.thread).length - η.idx := hηat
          have hg : ((Tc.wake I).prog η.thread).length =
              (T.prog η.thread).length - η.idx := by
            rw [hsame]
            exact hpx'
          exact hg
        · have hg : updateMapOn s.E I true i = false := by
            rw [updateMapOn_apply, if_neg hiI]
            exact hEi
          exact hg
        · rw [hrcs]
          exact hEgen
    · -- edge_sound: a new sync target's whole fiber has executed (clause 4)
      refine hedge_all ?_
      intro y hidx hd1 hd2 x hxpts hcases hgenxy
      obtain ⟨hyI, hcmy, hpy⟩ := hnew_char y hidx hd1 hd2
      have hyF := hgen_of_park y hyI hpy hidx
      obtain ⟨cy, hcy, -, -, hygen⟩ := registrantGen_some (mem_genFiber.mp hyF).2
      obtain ⟨cx, hxc, hxreg, hxbar⟩ : ∃ cx, T.cmdAt x = some cx ∧
          cx.isRegistrant = true ∧ cx.barrier? = some (Sum.inl nb) := by
        rcases hcases with ⟨nb', n', hxc, hyc⟩ | ⟨sb', ph', hxc, hyc⟩ |
          ⟨nb', n', hxc, hyc⟩
        · rw [hcmy] at hyc
          have hinj := Option.some.inj hyc
          simp only [Cmd.sync_nb.injEq] at hinj
          obtain ⟨rfl, -⟩ := hinj
          exact ⟨_, hxc, rfl, rfl⟩
        · exfalso
          rw [hcmy] at hyc
          exact absurd (Option.some.inj hyc) (by simp)
        · rw [hcmy] at hyc
          have hinj := Option.some.inj hyc
          simp only [Cmd.sync_nb.injEq] at hinj
          obtain ⟨rfl, -⟩ := hinj
          exact ⟨_, hxc, rfl, rfl⟩
      have hxgen : pointGen T τ x =
          some ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
        rw [hgenxy]
        exact hygen
      have hxregG : registrantGen T τ x = some (.inl nb,
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hxc, hxgen, hxreg, hxbar]
      have hxF : x ∈ genFiber T τ (.inl nb)
          ((recycleCount (.inl nb) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hxpts, hxregG⟩
      obtain ⟨mx, hmx⟩ := hround_new (Sum.inl nb) hrecb x hxF
      have hmxlt := (pointTime_spec hchainσ h0σ hmx).2.1
      have hmxle : mx ≤ τ'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hmxlt
        omega
      exact ⟨mx, hmxle, hmx⟩
    · exact hrounds_all hround_new
    · intro sb' g' hgle n₀ hinit
      rw [hrc_same (.inr sb') (hnorecb (.inr sb') (by simp))] at hgle
      exact hconf.rounds_full sb' g' hgle n₀ hinit
  | @mb_recycle s₀ Tc₀ sb I A n ph hb hfull hpark =>
    set Cn := Config.run
      ({ s with E := updateMapOn s.E I true,
                BM := Function.update s.BM sb ⟨[], 0, some n, !ph⟩ })
      (Tc.wake I) with hCndef
    -- this step is exactly an mb-recycle of `sb`
    have hrecb : stepRecyclesBarrier (.inr sb) (Config.run s Tc) Cn = true := by
      rw [hCndef]
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hb,
        MBarrierState.isFull, hfull, Function.update_self]
    have hnorecb : ∀ b, b ≠ Sum.inr sb →
        stepRecyclesBarrier b (Config.run s Tc) Cn = false := by
      intro b hbne
      cases b with
      | inl nb' =>
        rw [hCndef]
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BN nb').isFull
        · simp
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          intro hunc
          rw [hunc] at hfl
          simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
      | inr sb' =>
        have hne' : sb' ≠ sb := fun h => hbne (by rw [h])
        have hupd : (Function.update s.BM sb ⟨[], 0, some n, !ph⟩) sb' = s.BM sb' :=
          Function.update_of_ne hne' _ _
        rw [hCndef]
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BM sb').isFull
        · simp
        · simp only [Bool.true_and, hupd, decide_eq_false_iff_not]
          intro hflip
          exact mb_flip_ne (s.BM sb') hflip
    -- the fullness pigeonhole: the closing fiber (all arrives) is consumed
    have hff := conforms_full_fiber_mb hτ htr hconf hlast hb hfull
    have hEfalse : ∀ i, updateMapOn s.E I true i = false → i ∉ I ∧ s.E i = false := by
      intro i hEi
      rw [updateMapOn_apply] at hEi
      by_cases hiI : i ∈ I
      · rw [if_pos hiI] at hEi
        exact absurd hEi (by simp)
      · rw [if_neg hiI] at hEi
        exact ⟨hiI, hEi⟩
    have hhead_cmd : ∀ (x : ProgPoint), pointerAt T x (Config.run s Tc) →
        x.idx < (T.prog x.thread).length →
        ∀ (c₀ : Cmd), (Tc.prog x.thread).head? = some c₀ → T.cmdAt x = some c₀ := by
      intro x hpx hidx c₀ hhd
      have hsufx : (Config.run s Tc).progOf x.thread <:+
          (Config.run State.initial T).progOf x.thread :=
        progOf_suffix_index_le hchain x.thread h0idx (Nat.zero_le _) hlastidx
      have hdrop : Tc.prog x.thread =
          (T.prog x.thread).drop
            ((T.prog x.thread).length - (Tc.prog x.thread).length) :=
        List.IsSuffix.eq_drop hsufx
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hidxeq : (T.prog x.thread).length - (Tc.prog x.thread).length = x.idx := by
        omega
      rw [hidxeq] at hdrop
      have hdd : (T.prog x.thread).drop x.idx =
          (T.prog x.thread)[x.idx]'hidx :: (T.prog x.thread).drop (x.idx + 1) :=
        List.drop_eq_getElem_cons hidx
      rw [hdrop, hdd] at hhd
      simp only [List.head?_cons, Option.some.injEq] at hhd
      have hg : (T.prog x.thread)[x.idx]? = some c₀ := by
        rw [List.getElem?_eq_getElem hidx, hhd]
      exact hg
    -- the appended step's drops are exactly the woken parked waits
    have hnew_char : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
        Tc.prog η.thread = (T.prog η.thread).drop η.idx →
        Cn.progOf η.thread = (T.prog η.thread).drop (η.idx + 1) →
        η.thread ∈ I ∧ T.cmdAt η = some (Cmd.wait_mb sb ph) ∧
          pointerAt T η (Config.run s Tc) := by
      intro η hidx hd1 hd2
      by_cases hηI : η.thread ∈ I
      · have hhd := hpark η.thread hηI
        have hdd : (T.prog η.thread).drop η.idx =
            (T.prog η.thread)[η.idx]'hidx :: (T.prog η.thread).drop (η.idx + 1) :=
          List.drop_eq_getElem_cons hidx
        rw [hd1, hdd] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        refine ⟨hηI, ?_, ?_⟩
        · have hg : (T.prog η.thread)[η.idx]? = some (Cmd.wait_mb sb ph) := by
            rw [List.getElem?_eq_getElem hidx, hhd]
          exact hg
        · have hg : (Tc.prog η.thread).length =
              (T.prog η.thread).length - η.idx := by
            rw [hd1]
            simp [List.length_drop]
          exact hg
      · exfalso
        have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
          simp [WeftCommon.CTA.wake, if_neg hηI]
        have hd2' : (Tc.wake I).prog η.thread =
            (T.prog η.thread).drop (η.idx + 1) := hd2
        rw [hsame, hd1] at hd2'
        have hlen := congrArg List.length hd2'
        simp only [List.length_drop] at hlen
        omega
    -- a woken parked wait executes in the appended trace
    have hnewtime : ∀ (x : ProgPoint), x.thread ∈ I →
        pointerAt T x (Config.run s Tc) → x.idx < (T.prog x.thread).length →
        ∃ m, pointTime T (τ' ++ [Cn]) x = some m := by
      intro x hxI hpx hidx
      refine exists_pointTime_of_passed hchainσ h0σ List.getLast?_concat
        (i := x.thread) (k := x.idx) hidx ?_
      have hpx' : (Tc.prog x.thread).length = (T.prog x.thread).length - x.idx := hpx
      have hposx : 0 < (Tc.prog x.thread).length := by
        have hhd := hpark x.thread hxI
        cases hTt : Tc.prog x.thread with
        | nil => rw [hTt] at hhd; simp at hhd
        | cons a l => simp
      have hwake : (Tc.wake I).prog x.thread = (Tc.prog x.thread).tail := by
        simp [WeftCommon.CTA.wake, if_pos hxI]
      change ((Tc.wake I).prog x.thread).length + (x.idx + 1) ≤
        (T.prog x.thread).length
      rw [hwake]
      have htl : ((Tc.prog x.thread).tail).length = (Tc.prog x.thread).length - 1 := by
        simp [List.length_tail]
      omega
    -- a woken parked wait carries its reference generation (the parked-waiter clause)
    have hwoken_data : ∀ (η : ProgPoint), η.thread ∈ I →
        pointerAt T η (Config.run s Tc) → η.idx < (T.prog η.thread).length →
        pointGen T τ η =
          some ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
      intro η hηI hpη hidx
      obtain ⟨hcount, harr, hwait, -⟩ := hconf.mstate _ hlast s rfl sb
      have hiW : η.thread ∈ (s.BM sb).waiting := by rw [hb]; exact hηI
      obtain ⟨η', hη'pts, hη'th, hη'cmd, hη'at, hEi, hEgen⟩ := hwait η.thread hiW
      have hη'idx : η'.idx < (T.prog η'.thread).length :=
        ((mem_progPoints_iff T η').mp hη'pts).2
      have heq : η' = η :=
        pointerAt_thread_inj hη'at hpη hη'th (by omega) (by omega)
      rw [heq] at hEgen
      exact hEgen
    -- clause 4's fresh round: the closing fiber has now executed
    have hround_new : ∀ b, stepRecyclesBarrier b (Config.run s Tc) Cn = true →
        ∀ η ∈ genFiber T τ b ((recycleCount b τ' (τ'.length - 1) : ℕ) : ℤ),
          ∃ m, pointTime T (τ' ++ [Cn]) η = some m := by
      intro b hrb η hη
      have hbb : b = Sum.inr sb := by
        by_contra hne'
        rw [hnorecb b hne'] at hrb
        exact absurd hrb (by simp)
      subst hbb
      obtain ⟨m, hm⟩ := hff η hη
      exact ⟨m, pointTime_append_some hm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Te h
      rw [List.getLast?_concat, Option.some.injEq] at h
      exact absurd h (by simp)
    · -- gen_eq: the new executions are the woken waits, parked at their
      -- reference generation — which they observe (the phase matches)
      refine hgen_all ?_
      intro η hnone hidx hd1 hd2
      obtain ⟨hηI, hcm, hpη⟩ := hnew_char η hidx hd1 hd2
      have hηgen := hwoken_data η hηI hpη hidx
      obtain ⟨m, hm⟩ := hnewtime η hηI hpη hidx
      rcases pointTime_append_cases hne hm with hold | ⟨-, hmN⟩
      · rw [hnone] at hold
        exact absurd hold (by simp)
      · subst hmN
        have hpgσ := pointGen_eq_of_pointTime hcm rfl hm
        have hrca := recycleCount_append (.inr sb) τ' Cn
          (j := τ'.length - 1) (by omega)
        rw [hrca] at hpgσ
        have hphm : phaseAfter (recycleCount (.inr sb) τ' (τ'.length - 1)) = ph := by
          have hph := phase_eq_phaseAfter hchain h0idx sb (τ'.length - 1) _ s
            hlastidx rfl
          rw [hb] at hph
          exact hph.symm
        have hgv : (Cmd.wait_mb sb ph).genValue
            (recycleCount (.inr sb) τ' (τ'.length - 1)) =
            ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
          simp [Cmd.genValue, hphm]
        rw [hgv] at hpgσ
        rw [hpgσ, hηgen]
    · -- named-barrier state: untouched (the wake only re-enables `sb`'s waiters)
      intro Cl hCl sl hsl b
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      rw [hCndef] at hsl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl b
      have hrcs := hrc_same (.inl b) (hnorecb (.inl b) (by simp))
      refine ⟨?_, ?_, ?_, hunc⟩
      · rw [hrcs]
        exact hcount
      · rw [hrcs, hfilter_same (.inl b) _ ?_]
        · exact harr
        · intro η hη c hcm hcarr hpt
          rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
          · have := (pointTime_spec hchain h0 hold).2.1
            omega
          · obtain ⟨-, hcmη, -⟩ := hnew_char η hidx hd1 hd2
            rw [hcm] at hcmη
            have hcr : c = Cmd.wait_mb sb ph := Option.some.inj hcmη
            rw [hcr] at hcarr
            simp [Cmd.isArrive] at hcarr
      · intro i
        rw [hrcs]
        constructor
        · intro hi
          obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
          have hiI : i ∉ I := by
            intro hiI
            have h1 : i ∈ s.blocked (Sum.inl b) := hi
            have h2 : i ∈ s.blocked (Sum.inr sb) := by
              have h : i ∈ (s.BM sb).waiting := by rw [hb]; exact hiI
              exact h
            have := hwf.2.2.2.2.2.2.2 (Sum.inl b) (Sum.inr sb) i h1 h2
            exact absurd this (by simp)
          have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
            have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
            simp [WeftCommon.CTA.wake, if_neg hxIn]
          refine ⟨x, hxF, hthx, hsx, ?_, ?_⟩
          · have hpx' : (Tc.prog x.thread).length =
                (T.prog x.thread).length - x.idx := hpx
            have hg : ((Tc.wake I).prog x.thread).length =
                (T.prog x.thread).length - x.idx := by
              rw [hsame]
              exact hpx'
            exact hg
          · have hg : updateMapOn s.E I true i = false := by
              rw [updateMapOn_apply, if_neg hiI]
              exact hex
            exact hg
        · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
          obtain ⟨hiI, hex'⟩ := hEfalse i hex
          have hsame : (Tc.wake I).prog x.thread = Tc.prog x.thread := by
            have hxIn : x.thread ∉ I := by rw [hthx]; exact hiI
            simp [WeftCommon.CTA.wake, if_neg hxIn]
          have hpxC : pointerAt T x (Config.run s Tc) := by
            have hpx' : ((Tc.wake I).prog x.thread).length =
                (T.prog x.thread).length - x.idx := hpx
            rw [hsame] at hpx'
            exact hpx'
          exact (hsync i).mpr ⟨x, hxF, hthx, hsx, hpxC, hex'⟩
    · -- mbarrier state
      intro Cl hCl sl hsl sb'
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      rw [hCndef] at hsl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb'
      by_cases hbb : sb' = sb
      · subst hbb
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n' hn
          have hna : n = n' := by
            have h : (Function.update s.BM sb' ⟨[], 0, some n, !ph⟩ sb').count =
                some n' := hn
            rw [Function.update_self] at h
            exact Option.some.inj h
          rw [← hna]
          exact hcount n (by rw [hb])
        · -- arrived 0: nothing of the next fiber has executed
          have hLHS : ((Function.update s.BM sb' ⟨[], 0, some n, !ph⟩) sb').arrived =
              0 := by
            rw [Function.update_self]
          rw [hrc_incr (.inr sb') hrecb, hLHS]
          symm
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro x hx
          simp only [Bool.and_eq_true, not_and]
          intro hxarr hxsome
          obtain ⟨mx, hmx⟩ := Option.isSome_iff_exists.mp hxsome
          have hxmem := (mem_genFiber.mp hx).1
          obtain ⟨cx, hcx, hcxreg, hcxbar, hcxgen⟩ :=
            registrantGen_some (mem_genFiber.mp hx).2
          rcases pointTime_append_cases hne hmx with hold | ⟨-, hmN⟩
          · have hgx := hconf.gen_eq x hxmem mx hold
            have hpg := pointGen_eq_of_pointTime hcx hcxbar hold
            rw [genValue_of_isRegistrant hcxreg] at hpg
            rw [hpg, hcxgen] at hgx
            have hinj := Option.some.inj hgx
            have hmlt : mx < τ'.length := (pointTime_spec hchain h0 hold).2.1
            have hmono := recycleCount_mono (.inr sb') τ'
              (show mx - 1 ≤ τ'.length - 1 by omega)
            omega
          · subst hmN
            obtain ⟨hspec1, hspec2, hidxx, C₁, C₂, hC₁, hC₂, hdx1, hdx2⟩ :=
              pointTime_spec hchainσ h0σ hmx
            rw [hσN1] at hC₁
            obtain rfl := Option.some.inj hC₁
            rw [hσN] at hC₂
            obtain rfl := Option.some.inj hC₂
            obtain ⟨-, hcmx, -⟩ := hnew_char x hidxx hdx1 hdx2
            rw [hcx] at hcmx
            have hcr : cx = Cmd.wait_mb sb' ph := Option.some.inj hcmx
            rw [hcr] at hcxreg
            simp [Cmd.isRegistrant] at hcxreg
        · intro i hi
          exfalso
          have h : i ∈ (Function.update s.BM sb' ⟨[], 0, some n, !ph⟩ sb').waiting := hi
          rw [Function.update_self] at h
          simp at h
        · intro hcnone
          exfalso
          have h : (Function.update s.BM sb' ⟨[], 0, some n, !ph⟩ sb').count =
              none := hcnone
          rw [Function.update_self] at h
          simp at h
      · -- sb' ≠ sb: state untouched
        have hBb : (Function.update s.BM sb ⟨[], 0, some n, !ph⟩) sb' = s.BM sb' :=
          Function.update_of_ne hbb _ _
        have hrcs := hrc_same (.inr sb')
          (hnorecb (.inr sb') (fun h => hbb (Sum.inr.inj h)))
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro n' hn
          refine hcount n' ?_
          have h : (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb').count =
              some n' := hn
          rw [hBb] at h
          exact h
        · rw [hrcs, hfilter_same (.inr sb') _ ?_]
          · have hgoal : ((Function.update s.BM sb ⟨[], 0, some n, !ph⟩) sb').arrived =
                ((genFiber T τ (.inr sb')
                  ((recycleCount (.inr sb') τ' (τ'.length - 1) : ℕ) : ℤ)).filter
                  fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
              rw [hBb]
              exact harr
            exact hgoal
          · intro η hη c hcm hcarr hpt
            rcases htime_cases η _ hpt with hold | ⟨-, -, hidx, hd1, hd2⟩
            · have := (pointTime_spec hchain h0 hold).2.1
              omega
            · obtain ⟨-, hcmη, -⟩ := hnew_char η hidx hd1 hd2
              rw [hcm] at hcmη
              have hcr : c = Cmd.wait_mb sb ph := Option.some.inj hcmη
              rw [hcr] at hcarr
              simp [Cmd.isArrive] at hcarr
        · intro i hi
          have hi' : i ∈ (s.BM sb').waiting := by
            have h : i ∈ (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb').waiting := hi
            rw [hBb] at h
            exact h
          obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hEgen⟩ := hwait i hi'
          have hiI : i ∉ I := by
            intro hiI
            have h1 : i ∈ s.blocked (Sum.inr sb') := hi'
            have h2 : i ∈ s.blocked (Sum.inr sb) := by
              have h : i ∈ (s.BM sb).waiting := by rw [hb]; exact hiI
              exact h
            have := hwf.2.2.2.2.2.2.2 (Sum.inr sb') (Sum.inr sb) i h1 h2
            simp only [Sum.inr.injEq] at this
            exact hbb this
          have hsame : (Tc.wake I).prog η.thread = Tc.prog η.thread := by
            have hxIn : η.thread ∉ I := by rw [hηth]; exact hiI
            simp [WeftCommon.CTA.wake, if_neg hxIn]
          refine ⟨η, hηpts, hηth, hηcmd, ?_, ?_, ?_⟩
          · have hpx' : (Tc.prog η.thread).length =
                (T.prog η.thread).length - η.idx := hηat
            have hg : ((Tc.wake I).prog η.thread).length =
                (T.prog η.thread).length - η.idx := by
              rw [hsame]
              exact hpx'
            exact hg
          · have hg : updateMapOn s.E I true i = false := by
              rw [updateMapOn_apply, if_neg hiI]
              exact hEi
            exact hg
          · rw [hrcs]
            exact hEgen
        · intro hcnone
          have h : (s.BM sb').count = none := by
            have hg : (Function.update s.BM sb ⟨[], 0, some n, !ph⟩ sb').count =
                none := hcnone
            rw [hBb] at hg
            exact hg
          have hg : (Function.update s.BM sb ⟨[], 0, some n, !ph⟩) sb' =
              MBarrierState.uninitialized := by
            rw [hBb]
            exact hunin h
          exact hg
    · -- edge_sound: a new wait target's arriveWait sources sit in the closed fiber
      refine hedge_all ?_
      intro y hidx hd1 hd2 x hxpts hcases hgenxy
      obtain ⟨hyI, hcmy, hpy⟩ := hnew_char y hidx hd1 hd2
      have hygen := hwoken_data y hyI hpy hidx
      rcases hcases with ⟨nb', n', hxc, hyc⟩ | ⟨sb₂, ph₂, hxc, hyc⟩ |
        ⟨nb', n', hxc, hyc⟩
      · exfalso
        rw [hcmy] at hyc
        exact absurd (Option.some.inj hyc) (by simp)
      · -- tie the edge's barrier to `sb`
        rw [hcmy] at hyc
        have hinj := Option.some.inj hyc
        simp only [Cmd.wait_mb.injEq] at hinj
        obtain ⟨rfl, -⟩ := hinj
        have hxgen : pointGen T τ x =
            some ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) := by
          rw [hgenxy]
          exact hygen
        have hxregG : registrantGen T τ x = some (.inr sb,
            ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
          unfold registrantGen
          simp [hxc, hxgen, Cmd.isRegistrant, Cmd.barrier?]
        have hxF : x ∈ genFiber T τ (.inr sb)
            ((recycleCount (.inr sb) τ' (τ'.length - 1) : ℕ) : ℤ) :=
          mem_genFiber.mpr ⟨hxpts, hxregG⟩
        obtain ⟨mx, hmx⟩ := hround_new (Sum.inr sb) hrecb x hxF
        have hmxlt := (pointTime_spec hchainσ h0σ hmx).2.1
        have hmxle : mx ≤ τ'.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hmxlt
          omega
        exact ⟨mx, hmxle, hmx⟩
      · exfalso
        rw [hcmy] at hyc
        exact absurd (Option.some.inj hyc) (by simp)
    · exact hrounds_all hround_new
    · intro sb' g' hgle n₀ hinit
      by_cases hbb : sb' = sb
      · subst hbb
        rw [hrc_incr (.inr sb') hrecb] at hgle
        rcases Nat.lt_or_ge g' (recycleCount (.inr sb') τ' (τ'.length - 1)) with
          hlt | hge
        · exact hconf.rounds_full sb' g' (by omega) n₀ hinit
        · have hgeq : g' = recycleCount (.inr sb') τ' (τ'.length - 1) := by omega
          subst hgeq
          obtain ⟨hcount, harr, hwait, -⟩ := hconf.mstate _ hlast s rfl sb'
          have hinitc : T.initCountOf sb' = some n := hcount n (by rw [hb])
          have hnn : n₀ = n := by
            rw [hinitc] at hinit
            exact (Option.some.inj hinit).symm
          rw [hnn]
          obtain ⟨mI, CI, stI, hCI, hstI, hcntI⟩ :=
            exists_count_state_of_initCountOf hτ hinitc
          have harrA : A = ((genFiber T τ (.inr sb')
              ((recycleCount (.inr sb') τ' (τ'.length - 1) : ℕ) : ℤ)).filter
              fun η => isArriveCmd T η && (pointTime T τ' η).isSome).length := by
            rw [hb] at harr
            exact harr
          by_cases hcomp : recycleCount (.inr sb') τ' (τ'.length - 1) + 1 ≤
              recycleCount (.inr sb') τ (τ.length - 1)
          · exact genFiber_length_mb hτ hcomp hCI hstI hcntI
          · exfalso
            have hApos : 0 < A := by
              have := n.pos
              omega
            obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ genFiber T τ (.inr sb')
                ((recycleCount (.inr sb') τ' (τ'.length - 1) : ℕ) : ℤ) := by
              rcases hF : genFiber T τ (.inr sb')
                  ((recycleCount (.inr sb') τ' (τ'.length - 1) : ℕ) : ℤ) with
                _ | ⟨a, l⟩
              · exfalso
                rw [hF] at harrA
                simp at harrA
                omega
              · exact ⟨a, List.mem_cons_self ..⟩
            have hRge : recycleCount (.inr sb') τ' (τ'.length - 1) ≤
                recycleCount (.inr sb') τ (τ.length - 1) := by
              obtain ⟨c', mx, -, -, -, -, -, hmx1, hmxlt, hgmx⟩ :=
                genFiber_time_data hτ hx₀
              have := recycleCount_mono (.inr sb') τ
                (show mx - 1 ≤ τ.length - 1 by omega)
              omega
            have hreq : recycleCount (.inr sb') τ' (τ'.length - 1) =
                recycleCount (.inr sb') τ (τ.length - 1) := by omega
            have hlt' := genFiber_partial_length_lt_mb hτ (sb := sb') hCI hstI hcntI
            rw [hreq] at harrA
            have hle := List.length_filter_le (fun η => isArriveCmd T η &&
              (pointTime T τ' η).isSome) (genFiber T τ (.inr sb')
                ((recycleCount (.inr sb') τ (τ.length - 1) : ℕ) : ℤ))
            omega
      · rw [hrc_same (.inr sb')
          (hnorecb (.inr sb') (fun h => hbb (Sum.inr.inj h)))] at hgle
        exact hconf.rounds_full sb' g' hgle n₀ hinit
  | @done s₀ Tc₀ hdone hnofull hmbnofull =>
    have hnonew : ∀ (η : ProgPoint) (m : Nat),
        pointTime T (τ' ++ [Config.done s]) η = some m →
        pointTime T τ' η = some m := by
      intro η m hpt
      rcases htime_cases η m hpt with h | ⟨-, -, hidx, hd1, -⟩
      · exact h
      · exfalso
        have hnil : Tc.prog η.thread = [] := by
          by_cases hi : η.thread ∈ Tc.ids
          · exact hdone η.thread hi
          · exact Tc.nil_outside_ids η.thread hi
        rw [hnil] at hd1
        have hlen := congrArg List.length hd1
        simp only [List.length_nil, List.length_drop] at hlen
        omega
    have hnorec : ∀ b,
        stepRecyclesBarrier b (Config.run s Tc) (Config.done s) = false := by
      intro b
      cases b with
      | inl nb =>
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BN nb).isFull
        · simp
        · simp only [Bool.true_and]
          rw [decide_eq_false_iff_not]
          intro hunc
          rw [hunc] at hfl
          simp [NamedBarrierState.isFull, NamedBarrierState.unconfigured] at hfl
      | inr sb =>
        simp only [stepRecyclesBarrier, WeftCommon.Config.state?]
        cases hfl : (s.BM sb).isFull
        · simp
        · simp only [Bool.true_and]
          rw [decide_eq_false_iff_not]
          intro hflip
          exact mb_flip_ne (s.BM sb) hflip
    have hnilprog : ∀ (i : ThreadId), Tc.prog i = [] := by
      intro i
      by_cases hi : i ∈ Tc.ids
      · exact hdone i hi
      · exact Tc.nil_outside_ids i hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Te h
      rw [List.getLast?_concat, Option.some.injEq] at h
      exact absurd h (by simp)
    · refine hgen_all ?_
      intro η hnone hidx hd1 hd2
      exfalso
      rw [hnilprog η.thread] at hd1
      have hlen := congrArg List.length hd1
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    · intro Cl hCl sl hsl nb
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hsync, hunc⟩ := hconf.state _ hlast s rfl nb
      have hrc := hrc_same (.inl nb) (hnorec (.inl nb))
      refine ⟨?_, ?_, ?_, hunc⟩
      · rw [hrc]
        exact hcount
      · rw [hrc, hfilter_same (.inl nb) _ ?_]
        · exact harr
        · intro η hη c hcm hcarr hpt
          have hpt' := hnonew η _ hpt
          have hlt := (pointTime_spec hchain h0 hpt').2.1
          omega
      · intro i
        rw [hrc]
        constructor
        · intro hi
          obtain ⟨x, hxF, hthx, hsx, hpx, hex⟩ := (hsync i).mp hi
          exfalso
          have hpx' : (Tc.prog x.thread).length =
              (T.prog x.thread).length - x.idx := hpx
          have hidxx : x.idx < (T.prog x.thread).length :=
            ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
          rw [hnilprog x.thread] at hpx'
          simp only [List.length_nil] at hpx'
          omega
        · rintro ⟨x, hxF, hthx, hsx, hpx, hex⟩
          exfalso
          have hpx' : ((Config.done s).progOf x.thread).length =
              (T.prog x.thread).length - x.idx := hpx
          have hidxx : x.idx < (T.prog x.thread).length :=
            ((mem_progPoints_iff T x).mp (mem_genFiber.mp hxF).1).2
          simp only [WeftCommon.Config.progOf, List.length_nil] at hpx'
          omega
    · intro Cl hCl sl hsl sb
      rw [List.getLast?_concat, Option.some.injEq] at hCl
      subst hCl
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨hcount, harr, hwait, hunin⟩ := hconf.mstate _ hlast s rfl sb
      have hrc := hrc_same (.inr sb) (hnorec (.inr sb))
      refine ⟨hcount, ?_, ?_, hunin⟩
      · rw [hrc, hfilter_same (.inr sb) _ ?_]
        · exact harr
        · intro η hη c hcm hcarr hpt
          have hpt' := hnonew η _ hpt
          have hlt := (pointTime_spec hchain h0 hpt').2.1
          omega
      · intro i hi
        exfalso
        obtain ⟨η, hηpts, hηth, hηcmd, hηat, hEi, hηgen⟩ := hwait i hi
        have hat' : (Tc.prog η.thread).length =
            (T.prog η.thread).length - η.idx := hηat
        have hidxη : η.idx < (T.prog η.thread).length :=
          ((mem_progPoints_iff T η).mp hηpts).2
        rw [hnilprog η.thread] at hat'
        simp only [List.length_nil] at hat'
        omega
    · refine hedge_all ?_
      intro y hidx hd1 hd2 x hxpts hcases hgenxy
      exfalso
      rw [hnilprog y.thread] at hd1
      have hlen := congrArg List.length hd1
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    · refine hrounds_all ?_
      intro b hrb
      exact absurd hrb (by rw [hnorec b]; simp)
    · intro sb' g' hgle n₀ hinit
      rw [hrc_same (.inr sb') (hnorec (.inr sb'))] at hgle
      exact hconf.rounds_full sb' g' hgle n₀ hinit
  | @error s₀ Tc₀ t P' hbar hmbar hth =>
    exfalso
    obtain ⟨hokReg, hokWait, hokInit, hokU⟩ := check_true_parts hcheck
    obtain ⟨Pt, hPt⟩ : ∃ P, Tc.prog t = P := ⟨_, rfl⟩
    rw [hPt] at hth
    have hsuf : (Config.run s Tc).progOf t <:+
        (Config.run State.initial T).progOf t :=
      progOf_suffix_index_le hchain t h0idx (Nat.zero_le _) hlastidx
    have hlen_le : (Tc.prog t).length ≤ (T.prog t).length := suffix_length_le hsuf
    cases hth with
    | @sync_err_count _ _ ba mm nn cc II AA he hbcfg hnem =>
      have hPt' : (Config.run s Tc).progOf t = Cmd.sync_nb ba mm :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hcmdη' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.sync_nb ba mm) := hcmdη
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hat : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmem
        hcmdη' rfl rfl hat
      have hregη : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdη', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hηfib : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmem, hregη⟩
      obtain ⟨hcount, -, -, -⟩ := hconf.state _ hlast s rfl ba
      have hcnt := hcount nn (by rw [hbcfg]) _ hηfib
      rw [hcmdη'] at hcnt
      simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hcnt
      exact hnem hcnt.symm
    | @arrive_err_count _ _ ba mm nn cc II AA he hbcfg hnem =>
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive_nb ba mm :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hcmdη' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive_nb ba mm) := hcmdη
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hat : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have hrr := conforms_reg_round hτ hcheck htr hconf hlast hbar hmbar hmem
        hcmdη' rfl rfl hat
      have hregη : registrantGen T τ ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (.inl ba,
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ)) := by
        unfold registrantGen
        simp [hcmdη', hrr, Cmd.isRegistrant, Cmd.barrier?]
      have hηfib : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          genFiber T τ (.inl ba)
            ((recycleCount (.inl ba) τ' (τ'.length - 1) : ℕ) : ℤ) :=
        mem_genFiber.mpr ⟨hmem, hregη⟩
      obtain ⟨hcount, -, -, -⟩ := hconf.state _ hlast s rfl ba
      have hcnt := hcount nn (by rw [hbcfg]) _ hηfib
      rw [hcmdη'] at hcnt
      simp only [Option.bind_some, Cmd.count?, Option.some.injEq] at hcnt
      exact hnem hcnt.symm
    | @mb_init_err _ _ ba na cc II AA n' ph he hbcfg =>
      -- `ba` is already initialized: its unique init executed in `τ'`, yet the
      -- erring thread's control still sits at an `init_mb ba` — the same point
      have hPt' : (Config.run s Tc).progOf t = Cmd.init_mb ba na :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hcmdη' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.init_mb ba na) := hcmdη
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hat : pointerAt T ⟨t, (T.prog t).length - (Tc.prog t).length⟩
          (Config.run s Tc) := by
        change (Tc.prog t).length =
          (T.prog t).length - ((T.prog t).length - (Tc.prog t).length)
        omega
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      obtain ⟨m, hm⟩ := exists_init_time_of_count_some hokU hchain h0 hlast
        hlastidx rfl (show (s.BM ba).count = some n' by rw [hbcfg]) hmem hcmdη'
      have hnone := pointTime_none_of_pointerAt hchain h0 hlast hat
      rw [hnone] at hm
      exact absurd hm (by simp)
    | @mb_arrive_err _ _ ba cc he hbcfg =>
      -- an uninitialized use: the check anchors the init before the use's
      -- predecessor, which has executed — so the init executed, initializing `ba`
      have hPt' : (Config.run s Tc).progOf t = Cmd.arrive_mb ba :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hcmdη' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.arrive_mb ba) := hcmdη
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have husebind : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.usesMBarrier? = some ba := by
        rw [hcmdη']
        rfl
      obtain ⟨ip, hipmem, n₀, hipcmd⟩ := exists_init_point_of_use hτ hmem husebind
      obtain ⟨hidx1, hpred⟩ := init_hb_of_check hokInit hipmem hipcmd hmem husebind
      obtain ⟨m3, hptc3⟩ : ∃ m3, pointTime T τ'
          ⟨t, (T.prog t).length - (Tc.prog t).length - 1⟩ = some m3 := by
        refine exists_pointTime_of_passed hchain h0 hlast (by omega) ?_
        change (Tc.prog t).length +
          ((T.prog t).length - (Tc.prog t).length - 1 + 1) ≤ (T.prog t).length
        have hidx1' : 1 ≤ (T.prog t).length - (Tc.prog t).length := hidx1
        omega
      obtain ⟨mip, -, hmip⟩ := hconf.happensBefore_sound hpred m3 hptc3
      -- decode `ip`'s execution: it initializes `ba`, which persists to `s`
      obtain ⟨hm1, hmlt, hidxip, D, D', hD, hD', hdrop1, hdrop2⟩ :=
        pointTime_spec hchain h0 hmip
      obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp
        (show (T.prog ip.thread)[ip.idx]? =
          some (Cmd.init_mb ba n₀) from hipcmd)
      have hDcons : D.progOf ip.thread = Cmd.init_mb ba n₀ ::
          (T.prog ip.thread).drop (ip.idx + 1) := by
        rw [hdrop1, List.drop_eq_getElem_cons hlt0, hget0]
      have hDD' : τ'[mip - 1 + 1]? = some D' := by
        rw [show mip - 1 + 1 = mip by omega]; exact hD'
      have hstepD := chain_step hchain hD hDD'
      obtain ⟨sD', TD', hD'eq, hcntD'⟩ :=
        init_drop_target_initialized hstepD hDcons hdrop2
      have hper := count_some_persists_le hchain (τ'.length - 1) mip (by omega)
        hD' (by rw [hD'eq]; rfl) hcntD' hlastidx rfl
      rw [hbcfg] at hper
      exact absurd hper (by simp [MBarrierState.uninitialized])
    | @mb_wait_err _ _ ba ph cc he hbcfg =>
      have hPt' : (Config.run s Tc).progOf t = Cmd.wait_mb ba ph :: cc := hPt
      have hcmdη := cmd_at_last hsuf hPt'
      have hcmdη' : T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩ =
          some (Cmd.wait_mb ba ph) := hcmdη
      have hlen_pos : 0 < (Tc.prog t).length := by rw [hPt]; simp
      have hmem : (⟨t, (T.prog t).length - (Tc.prog t).length⟩ : ProgPoint) ∈
          T.progPoints := mem_progPoints_of_cmdAt T hcmdη
      have husebind : (T.cmdAt ⟨t, (T.prog t).length - (Tc.prog t).length⟩).bind
          Cmd.usesMBarrier? = some ba := by
        rw [hcmdη']
        rfl
      obtain ⟨ip, hipmem, n₀, hipcmd⟩ := exists_init_point_of_use hτ hmem husebind
      obtain ⟨hidx1, hpred⟩ := init_hb_of_check hokInit hipmem hipcmd hmem husebind
      obtain ⟨m3, hptc3⟩ : ∃ m3, pointTime T τ'
          ⟨t, (T.prog t).length - (Tc.prog t).length - 1⟩ = some m3 := by
        refine exists_pointTime_of_passed hchain h0 hlast (by omega) ?_
        change (Tc.prog t).length +
          ((T.prog t).length - (Tc.prog t).length - 1 + 1) ≤ (T.prog t).length
        have hidx1' : 1 ≤ (T.prog t).length - (Tc.prog t).length := hidx1
        omega
      obtain ⟨mip, -, hmip⟩ := hconf.happensBefore_sound hpred m3 hptc3
      obtain ⟨hm1, hmlt, hidxip, D, D', hD, hD', hdrop1, hdrop2⟩ :=
        pointTime_spec hchain h0 hmip
      obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp
        (show (T.prog ip.thread)[ip.idx]? =
          some (Cmd.init_mb ba n₀) from hipcmd)
      have hDcons : D.progOf ip.thread = Cmd.init_mb ba n₀ ::
          (T.prog ip.thread).drop (ip.idx + 1) := by
        rw [hdrop1, List.drop_eq_getElem_cons hlt0, hget0]
      have hDD' : τ'[mip - 1 + 1]? = some D' := by
        rw [show mip - 1 + 1 = mip by omega]; exact hD'
      have hstepD := chain_step hchain hD hDD'
      obtain ⟨sD', TD', hD'eq, hcntD'⟩ :=
        init_drop_target_initialized hstepD hDcons hdrop2
      have hper := count_some_persists_le hchain (τ'.length - 1) mip (by omega)
        hD' (by rw [hD'eq]; rfl) hcntD' hlastidx rfl
      rw [hbcfg] at hper
      exact absurd hper (by simp [MBarrierState.uninitialized])

/-- **Theorem 6** (paper §5.2.6): every partial trace of the checked CTA
conforms to the reference — induction over the trace via `conforms_snoc`. -/
theorem conforms_of_traceFrom {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true)
    {τ' : List Config} (htr : IsTraceFrom (Config.run State.initial T) τ') :
    Conforms T τ τ' := by
  revert htr
  induction τ' using List.reverseRecOn with
  | nil =>
    intro htr
    exact absurd htr.2 (by simp)
  | append_singleton l c ih =>
    intro htr
    obtain ⟨hchain, hhead⟩ := htr
    by_cases hl : l = []
    · subst hl
      simp only [List.nil_append] at hhead ⊢
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact conforms_init T τ
    · have hchain' : List.IsChain CTAStep (l ++ [c]) := hchain
      rw [List.isChain_append] at hchain'
      obtain ⟨hchain_l, -, hconn⟩ := hchain'
      have hhead_l : l.head? = some (Config.run State.initial T) := by
        rwa [List.head?_append_of_ne_nil _ hl] at hhead
      have htr_l : IsTraceFrom (Config.run State.initial T) l := ⟨hchain_l, hhead_l⟩
      obtain ⟨x, hx⟩ : ∃ x, l.getLast? = some x := by
        cases hgl : l.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hgl) hl
        | some x => exact ⟨x, rfl⟩
      have hstep : CTAStep x c :=
        hconn x (Option.mem_def.mpr hx) c (Option.mem_def.mpr rfl)
      exact conforms_snoc hτ hcheck htr_l (ih htr_l) hx hstep

/-- **Theorem 7** (paper §5.2.6): a conforming *complete* trace ends in `done`.
`err` is clause 0. For a deadlock: every unfinished thread is parked at a
`sync_nb` or a `wait_mb` (an enabled thread always has a step under the
recycle-priority semantics), so take the parked op `u` of **minimal τ-time**:
its open round (= `pointGen T τ u` by conformance) is missing a fiber member
`d` (for waits: a gen-`r` arrive), whose thread is parked at an op `e` strictly
before `d` — and `t_τ(e) < t_τ(d) ≤ t_τ(u)` breaks minimality. -/
theorem conforms_complete_done {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {σ : List Config} (hσ : IsCompleteTraceFrom (Config.run State.initial T) σ)
    (hconf : Conforms T τ σ) :
    ∃ s, σ.getLast? = some (Config.done s) := by
  obtain ⟨hct, h0⟩ := hσ
  obtain ⟨Cn, hlast, hends⟩ := hct.ends
  rcases hends with ⟨sd, rfl⟩ | ⟨Te, rfl⟩ | hstuck
  · exact ⟨sd, hlast⟩
  · exact absurd hlast (hconf.no_err Te)
  · cases Cn with
    | done sd => exact ⟨sd, hlast⟩
    | err Te => exact absurd hlast (hconf.no_err Te)
    | run s Tc =>
      exfalso
      -- ## trace facts
      have hchain : List.IsChain CTAStep σ := hct.subtrace
      have h0idx : σ[0]? = some (Config.run State.initial T) := by
        have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen]; exact h0
      have hlastidx : σ[σ.length - 1]? = some (Config.run s Tc) := by
        rw [← List.getLast?_eq_getElem?]; exact hlast
      have hreach := reaches_of_chain_getElem hchain h0idx _ _ hlastidx
      have hwf : (Config.WF (Config.run s Tc)) := WF_of_reaches hreach
      have hei : s.EnabledInv :=
        enabledInv_chain hchain h0
          (fun s₀ hs₀ => by
            simp only [WeftCommon.Config.state?, Option.some.injEq] at hs₀
            subst hs₀
            exact State.EnabledInv.initial)
          _ (List.mem_of_mem_getLast? hlast) s rfl
      have hchainτ : List.IsChain CTAStep τ := hτ.1.1.subtrace
      have h0τ : τ.head? = some (Config.run State.initial T) := hτ.1.2
      have h0τidx : τ[0]? = some (Config.run State.initial T) := by
        have hgen : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
        rw [hgen]; exact h0τ
      obtain ⟨sdτ, hdτ⟩ := hτ.2
      -- every valid point executes in the successful reference trace
      have hτtime : ∀ (η : ProgPoint), η.idx < (T.prog η.thread).length →
          ∃ m, pointTime T τ η = some m := by
        intro η hidx
        have hidx' : η.idx < ((Config.run State.initial T).progOf η.thread).length :=
          hidx
        obtain ⟨m, hm⟩ := exists_time_of_ends_done hτ.1 hdτ hidx'
        exact ⟨m, pointTime_eq_of_isTimeOf hm⟩
      -- ## the stuck configuration: no barrier full, every unfinished thread parked
      have hguard : ∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
          ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) := by
        intro nb
        rcases hsb : s.BN nb with ⟨I, A, cnt⟩
        cases cnt with
        | none =>
          obtain ⟨hI, hA⟩ := hwf.2.1 nb I A hsb
          left
          rw [hI, hA]
          rfl
        | some n =>
          right
          obtain ⟨hle, hpark, -⟩ := hwf.1 nb I A n hsb
          refine ⟨I, A, n, rfl, ?_⟩
          rcases Nat.lt_or_ge (I.length + A) (n : Nat) with h | h
          · exact h
          · exact absurd ⟨_, CTAStep.recycle hsb (by omega) hpark⟩ hstuck
      have hmguard : ∀ sb, s.BM sb = MBarrierState.uninitialized ∨
          ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat) := by
        intro sb
        rcases hsb : s.BM sb with ⟨I, A, cnt, ph⟩
        cases cnt with
        | none =>
          obtain ⟨hI, hA, hph⟩ := hwf.2.2.2.1 sb I A ph hsb
          left
          rw [hI, hA, hph]
          rfl
        | some n =>
          right
          obtain ⟨hle, hpark⟩ := hwf.2.2.1 sb I A n ph hsb
          refine ⟨I, A, n, ph, rfl, ?_⟩
          rcases Nat.lt_or_ge A (n : Nat) with h | h
          · exact h
          · exact absurd ⟨_, CTAStep.mb_recycle hsb (by omega) hpark⟩ hstuck
      have hstep_of_enabled : ∀ (i : ThreadId) (c₀ : Cmd) (rest : Prog),
          Tc.prog i = c₀ :: rest → s.E i = true → False := by
        intro i c₀ rest hcons he
        have hi : i ∈ Tc.ids := by
          by_contra hni
          rw [Tc.nil_outside_ids i hni] at hcons
          exact absurd hcons (by simp)
        apply hstuck
        cases c₀ with
        | read g =>
          exact ⟨_, CTAStep.interleave hi hguard hmguard
            (by rw [hcons]; exact ThreadStep.read_noop)⟩
        | write g =>
          exact ⟨_, CTAStep.interleave hi hguard hmguard
            (by rw [hcons]; exact ThreadStep.write_noop)⟩
        | arrive_nb b' n' =>
          rcases hguard b' with hu | ⟨I', A', m', hcfg, hlt⟩
          · exact ⟨_, CTAStep.interleave hi hguard hmguard
              (by rw [hcons]; exact ThreadStep.arrive_configure he hu)⟩
          · by_cases hmn : m' = n'
            · subst hmn
              have hpos : 0 < I'.length + A' := (hwf.1 b' I' A' m' hcfg).2.2
              exact ⟨_, CTAStep.interleave hi hguard hmguard
                (by rw [hcons]; exact ThreadStep.arrive_register he hcfg hpos hlt)⟩
            · exact ⟨_, CTAStep.error hguard hmguard
                (by rw [hcons]; exact ThreadStep.arrive_err_count he hcfg hmn)⟩
        | sync_nb b' n' =>
          rcases hguard b' with hu | ⟨I', A', m', hcfg, hlt⟩
          · exact ⟨_, CTAStep.interleave hi hguard hmguard
              (by rw [hcons]; exact ThreadStep.sync_configure he hu)⟩
          · by_cases hmn : m' = n'
            · subst hmn
              have hpos : 0 < I'.length + A' := (hwf.1 b' I' A' m' hcfg).2.2
              exact ⟨_, CTAStep.interleave hi hguard hmguard
                (by rw [hcons]; exact ThreadStep.sync_block he hcfg hpos hlt)⟩
            · exact ⟨_, CTAStep.error hguard hmguard
                (by rw [hcons]; exact ThreadStep.sync_err_count he hcfg hmn)⟩
        | init_mb b' n' =>
          rcases hmguard b' with hu | ⟨I', A', m', ph', hcfg, hlt⟩
          · exact ⟨_, CTAStep.interleave hi hguard hmguard
              (by rw [hcons]; exact ThreadStep.mb_init he hu)⟩
          · exact ⟨_, CTAStep.error hguard hmguard
              (by rw [hcons]; exact ThreadStep.mb_init_err he hcfg)⟩
        | arrive_mb b' =>
          rcases hmguard b' with hu | ⟨I', A', m', ph', hcfg, hlt⟩
          · exact ⟨_, CTAStep.error hguard hmguard
              (by rw [hcons]; exact ThreadStep.mb_arrive_err he hu)⟩
          · exact ⟨_, CTAStep.interleave hi hguard hmguard
              (by rw [hcons]; exact ThreadStep.mb_arrive he hcfg)⟩
        | wait_mb b' ph' =>
          rcases hmguard b' with hu | ⟨I', A', m', ph₂, hcfg, hlt⟩
          · exact ⟨_, CTAStep.error hguard hmguard
              (by rw [hcons]; exact ThreadStep.mb_wait_err he hu)⟩
          · by_cases hph : ph₂ = ph'
            · subst hph
              exact ⟨_, CTAStep.interleave hi hguard hmguard
                (by rw [hcons]; exact ThreadStep.mb_wait_block he hcfg)⟩
            · exact ⟨_, CTAStep.interleave hi hguard hmguard
                (by
                  rw [hcons]
                  exact ThreadStep.mb_wait_pass he hcfg (fun h => hph h.symm))⟩
      -- ## program order in the reference trace
      have hpo : ∀ (x y : ProgPoint), x.thread = y.thread → x.idx < y.idx →
          ∀ mx my, pointTime T τ x = some mx → pointTime T τ y = some my →
          mx < my := by
        intro x y hth hidx mx my hmx hmy
        by_contra hge
        obtain ⟨hx1, hxlt, hxidx, C₁, C₂, hC₁, hC₂, hdropx, -⟩ :=
          pointTime_spec hchainτ h0τ hmx
        obtain ⟨hy1, hylt, hyidx, D₁, D₂, hD₁, hD₂, hdropy, -⟩ :=
          pointTime_spec hchainτ h0τ hmy
        have hsuf := progOf_suffix_index_le hchainτ x.thread hD₁
          (show my - 1 ≤ mx - 1 by omega) hC₁
        have hle := suffix_length_le hsuf
        rw [← hth] at hdropy hyidx
        rw [hdropx, hdropy] at hle
        simp only [List.length_drop] at hle
        omega
      -- ## a disabled unfinished thread is parked at its head — a `sync_nb`
      -- fiber member or a `wait_mb` at its reference generation
      have hparked_point : ∀ (i : ThreadId), Tc.prog i ≠ [] → s.E i = false →
          ∃ (x : ProgPoint),
            ((∃ (bx : NamedBarrier) (nx : ℕ+), T.cmdAt x = some (.sync_nb bx nx) ∧
              x ∈ genFiber T τ (.inl bx)
                ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)) ∨
             (∃ (bx : SharedBarrier) (phx : Phase),
              T.cmdAt x = some (.wait_mb bx phx) ∧
              pointGen T τ x =
                some ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ) ∧
              x.thread ∈ (s.BM bx).waiting)) ∧
            x ∈ T.progPoints ∧
            pointerAt T x (Config.run s Tc) ∧ s.E x.thread = false ∧
            x.thread = i ∧
            x.idx = (T.prog i).length - (Tc.prog i).length := by
        intro i hne hE
        obtain ⟨b_e, hdsy⟩ := hei i hE
        have hsufi : (Config.run s Tc).progOf i <:+
            (Config.run State.initial T).progOf i :=
          progOf_suffix_index_le hchain i h0idx (Nat.zero_le _) hlastidx
        have hlen_le : (Tc.prog i).length ≤ (T.prog i).length :=
          suffix_length_le hsufi
        have hlen_pos : 0 < (Tc.prog i).length := by
          cases hTt : Tc.prog i with
          | nil => exact absurd hTt hne
          | cons a l => simp
        cases b_e with
        | inl nb_e =>
          rcases hsb_e : s.BN nb_e with ⟨I_e, A_e, cnt_e⟩
          cases cnt_e with
          | none =>
            exfalso
            obtain ⟨hI0, -⟩ := hwf.2.1 nb_e I_e A_e hsb_e
            have hdsy' : i ∈ I_e := by
              have h : i ∈ (s.BN nb_e).synced := hdsy
              rw [hsb_e] at h
              exact h
            rw [hI0] at hdsy'
            simp at hdsy'
          | some n_e =>
            obtain ⟨-, -, hsync_e, -⟩ := hconf.state _ hlast s rfl nb_e
            obtain ⟨x, hxF, hthx, ⟨n_x, hcmx⟩, hpx, hEx⟩ :=
              (hsync_e i).mp (by
                have h : i ∈ (s.BN nb_e).synced := hdsy
                exact h)
            have hxpts := (mem_genFiber.mp hxF).1
            have hxidx : x.idx < (T.prog x.thread).length :=
              ((mem_progPoints_iff T x).mp hxpts).2
            have hpx' : (Tc.prog x.thread).length =
                (T.prog x.thread).length - x.idx := hpx
            rw [hthx] at hpx' hxidx
            have hxid : x.idx = (T.prog i).length - (Tc.prog i).length := by omega
            refine ⟨x, Or.inl ⟨nb_e, n_x, hcmx, hxF⟩, hxpts, hpx, ?_, hthx, hxid⟩
            rw [hthx]
            exact hE
        | inr sb_e =>
          rcases hsb_e : s.BM sb_e with ⟨I_e, A_e, cnt_e, ph_e⟩
          cases cnt_e with
          | none =>
            exfalso
            obtain ⟨hI0, -, -⟩ := hwf.2.2.2.1 sb_e I_e A_e ph_e hsb_e
            have hdsy' : i ∈ I_e := by
              have h : i ∈ (s.BM sb_e).waiting := hdsy
              rw [hsb_e] at h
              exact h
            rw [hI0] at hdsy'
            simp at hdsy'
          | some n_e =>
            obtain ⟨-, -, hwait_e, -⟩ := hconf.mstate _ hlast s rfl sb_e
            obtain ⟨x, hxpts, hthx, ⟨phx, hcmx⟩, hpx, hEx, hgx⟩ :=
              hwait_e i (by
                have h : i ∈ (s.BM sb_e).waiting := hdsy
                exact h)
            have hxidx : x.idx < (T.prog x.thread).length :=
              ((mem_progPoints_iff T x).mp hxpts).2
            have hpx' : (Tc.prog x.thread).length =
                (T.prog x.thread).length - x.idx := hpx
            rw [hthx] at hpx' hxidx
            have hxid : x.idx = (T.prog i).length - (Tc.prog i).length := by omega
            refine ⟨x, Or.inr ⟨sb_e, phx, hcmx, hgx, ?_⟩, hxpts, hpx, ?_, hthx, hxid⟩
            · rw [hthx]
              exact hdsy
            · rw [hthx]
              exact hE
      -- ## the descent: no parked op has a τ-time (strong induction on that time)
      have hdescend : ∀ (nt : Nat) (u : ProgPoint),
          ((∃ (bx : NamedBarrier) (nx : ℕ+), T.cmdAt u = some (.sync_nb bx nx) ∧
            u ∈ genFiber T τ (.inl bx)
              ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)) ∨
           (∃ (bx : SharedBarrier) (phx : Phase),
            T.cmdAt u = some (.wait_mb bx phx) ∧
            pointGen T τ u =
              some ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ) ∧
            u.thread ∈ (s.BM bx).waiting)) →
          pointerAt T u (Config.run s Tc) → s.E u.thread = false →
          pointTime T τ u = some nt → False := by
        intro nt
        induction nt using Nat.strong_induction_on with
        | _ nt ih =>
          intro u hflavor hupt huE htu
          -- per flavor: a fiber member `d` of the open round with no σ-time,
          -- and a cap `m_d ≤ nt` on its τ-time
          obtain ⟨b_u, d, hdF, hdnotd, hd_cap⟩ :
              ∃ (b_u : NamedBarrier ⊕ SharedBarrier) (d : ProgPoint),
                d ∈ genFiber T τ b_u
                  ((recycleCount b_u σ (σ.length - 1) : ℕ) : ℤ) ∧
                ((isArriveCmd T d && (pointTime T σ d).isSome) = false ∧
                  ¬ (isSyncCmd T d = true ∧ pointerAt T d (Config.run s Tc) ∧
                    s.E d.thread = false)) ∧
                (∀ m_d, pointTime T τ d = some m_d → m_d ≤ nt) := by
            rcases hflavor with ⟨bx, nx, hcmu, hufib⟩ | ⟨bx, phx, hcmu, hgenu, huW⟩
            · -- SYNC flavor: the named-barrier pigeonhole
              obtain ⟨hcount, harr, hsyncb, -⟩ := hconf.state _ hlast s rfl bx
              have huI : u.thread ∈ (s.BN bx).synced :=
                (hsyncb u.thread).mpr ⟨u, hufib, rfl, ⟨nx, hcmu⟩, hupt, huE⟩
              rcases hguard bx with hu | ⟨I, A, n, hcfg, hlt⟩
              · rw [hu] at huI
                simp [NamedBarrierState.unconfigured] at huI
              -- the sync's τ-time is the recycle closing the open round
              obtain ⟨cu', mu', -, -, -, -, hpt', hmu'1, hmu'lt, hgu⟩ :=
                genFiber_time_data hτ hufib
              have hmu'nt : nt = mu' := by
                rw [htu] at hpt'
                exact Option.some.inj hpt'
              subst hmu'nt
              obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ :=
                pointTime_sync_recycles hchainτ h0τ htu hcmu
              have hsucc := recycleCount_succ_of_recycle (.inl bx) τ hC₁
                (by rw [show nt - 1 + 1 = nt by omega]; exact hC₂) hrec
              rw [show nt - 1 + 1 = nt by omega] at hsucc
              have hntrc : recycleCount (.inl bx) σ (σ.length - 1) + 1 ≤
                  recycleCount (.inl bx) τ nt := by
                omega
              have hcomplete : recycleCount (.inl bx) σ (σ.length - 1) + 1 ≤
                  recycleCount (.inl bx) τ (τ.length - 1) := by
                have hmono := recycleCount_mono (.inl bx) τ
                  (show nt ≤ τ.length - 1 by omega)
                omega
              have hcnt : ∀ η ∈ genFiber T τ (.inl bx)
                  ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ),
                  (T.cmdAt η).bind Cmd.count? = some n := fun η hη =>
                hcount n (by rw [hcfg]) η hη
              have hlen := genFiber_length hτ hcomplete hufib (hcnt u hufib)
              have harrA : A = ((genFiber T τ (.inl bx)
                  ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T σ η).isSome).length := by
                have h := harr
                rw [hcfg] at h
                exact h
              have hsplitF : (genFiber T τ (.inl bx)
                  ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).length =
                  ((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T σ η).isSome).length +
                  ((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    fun η =>
                      !(isArriveCmd T η && (pointTime T σ η).isSome)).length := by
                rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
                  List.length_eq_countP_add_countP
                    (p := fun η => isArriveCmd T η && (pointTime T σ η).isSome)]
                congr 1
                refine List.countP_congr fun x hx => ?_
                cases hpx : (isArriveCmd T x && (pointTime T σ x).isSome) <;>
                  simp_all
              by_cases hex_d : ∃ d ∈ (genFiber T τ (.inl bx)
                  ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    fun η => !(isArriveCmd T η && (pointTime T σ η).isSome),
                  ¬(isSyncCmd T d = true ∧ pointerAt T d (Config.run s Tc) ∧
                    s.E d.thread = false)
              case neg =>
                exfalso
                have hallp : ∀ x ∈ (genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η => !(isArriveCmd T η && (pointTime T σ η).isSome),
                    isSyncCmd T x = true ∧ pointerAt T x (Config.run s Tc) ∧
                      s.E x.thread = false := by
                  intro x hx
                  by_contra hnx
                  exact hex_d ⟨x, hx, hnx⟩
                have hmapsub : ∀ a ∈ ((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η => !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                        ProgPoint.thread, a ∈ I := by
                  intro a ha
                  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
                  obtain ⟨hxsy, hxpt, hxE⟩ := hallp x hx
                  have hxF := (List.mem_filter.mp hx).1
                  obtain ⟨n_x, hcmx⟩ : ∃ n_x : ℕ+,
                      T.cmdAt x = some (.sync_nb bx n_x) := by
                    rcases genFiber_nb_cases hxF with ⟨n_x, hcm⟩ | ⟨n_x, hcm⟩
                    · exfalso
                      simp [isSyncCmd, hcm] at hxsy
                    · exact ⟨n_x, hcm⟩
                  have hmem : x.thread ∈ (s.BN bx).synced :=
                    (hsyncb x.thread).mpr ⟨x, hxF, rfl, ⟨n_x, hcmx⟩, hxpt, hxE⟩
                  rw [hcfg] at hmem
                  exact hmem
                have hmapnodup : (((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η => !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                        ProgPoint.thread).Nodup := by
                  refine List.Nodup.map_on ?_
                    (List.Nodup.filter _ (genFiber_nodup T τ (.inl bx) _))
                  intro x hx y hy hxy
                  obtain ⟨-, hxpt, -⟩ := hallp x hx
                  obtain ⟨-, hypt, -⟩ := hallp y hy
                  have hxidx : x.idx < (T.prog x.thread).length :=
                    ((mem_progPoints_iff T x).mp
                      (mem_genFiber.mp (List.mem_filter.mp hx).1).1).2
                  have hyidx : y.idx < (T.prog y.thread).length :=
                    ((mem_progPoints_iff T y).mp
                      (mem_genFiber.mp (List.mem_filter.mp hy).1).1).2
                  have hxpt' : (Tc.prog x.thread).length =
                      (T.prog x.thread).length - x.idx := hxpt
                  have hypt' : (Tc.prog y.thread).length =
                      (T.prog y.thread).length - y.idx := hypt
                  rw [hxy] at hxpt' hxidx
                  have hid : x.idx = y.idx := by omega
                  have hxeta : x = ⟨x.thread, x.idx⟩ := rfl
                  have hyeta : y = ⟨y.thread, y.idx⟩ := rfl
                  rw [hxeta, hyeta, hxy, hid]
                have hcard1 : (((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η => !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                        ProgPoint.thread).toFinset.card =
                    ((genFiber T τ (.inl bx)
                      ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η =>
                        !(isArriveCmd T η && (pointTime T σ η).isSome)).length := by
                  rw [List.toFinset_card_of_nodup hmapnodup, List.length_map]
                have hcard2 : (((genFiber T τ (.inl bx)
                    ((recycleCount (.inl bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                      fun η => !(isArriveCmd T η && (pointTime T σ η).isSome)).map
                        ProgPoint.thread).toFinset ⊆ I.toFinset := by
                  intro a ha
                  rw [List.mem_toFinset] at ha ⊢
                  exact hmapsub a ha
                have hcard3 := Finset.card_le_card hcard2
                have hcard4 := List.toFinset_card_le I
                omega
              case pos =>
                obtain ⟨d, hdF2, hdnp⟩ := hex_d
                have hdF := (List.mem_filter.mp hdF2).1
                have hdcen : (isArriveCmd T d && (pointTime T σ d).isSome) = false := by
                  have h := (List.mem_filter.mp hdF2).2
                  cases hbo : (isArriveCmd T d && (pointTime T σ d).isSome) with
                  | false => rfl
                  | true => rw [hbo] at h; simp at h
                refine ⟨.inl bx, d, hdF, ⟨hdcen, hdnp⟩, ?_⟩
                intro m_d hmd
                obtain ⟨cd', md', -, -, -, -, hptd', -, -, hgd⟩ :=
                  genFiber_time_data hτ hdF
                have hmdeq : md' = m_d := by
                  rw [hmd] at hptd'
                  exact (Option.some.inj hptd').symm
                subst hmdeq
                by_contra hgt
                have hmono := recycleCount_mono (.inl bx) τ
                  (show nt ≤ md' - 1 by omega)
                omega
            · -- WAIT flavor: the mbarrier pigeonhole
              obtain ⟨hcount, harr, hwaitb, -⟩ := hconf.mstate _ hlast s rfl bx
              rcases hmguard bx with hu | ⟨I, A, n, ph, hcfg, hlt⟩
              · exfalso
                obtain ⟨hI0, -, -⟩ := hwf.2.2.2.1 bx _ _ _ (by rw [hu]; rfl)
                have hW : u.thread ∈ ([] : List ThreadId) := by
                  have h := huW
                  rw [hu] at h
                  exact h
                simp at hW
              have hinitc : T.initCountOf bx = some n := hcount n (by rw [hcfg])
              obtain ⟨mI, CI, stI, hCI, hstI, hcntI⟩ :=
                exists_count_state_of_initCountOf hτ hinitc
              -- the wait's τ-time closes (or already saw closed) the open round
              have hnt1 : 1 ≤ nt := (pointTime_spec hchainτ h0τ htu).1
              have hntlt : nt < τ.length := (pointTime_spec hchainτ h0τ htu).2.1
              have hpgu := pointGen_eq_of_time hcmu rfl
                (isTimeOf_of_pointTime hτ.1 htu)
              have hgv : (Cmd.wait_mb bx phx).genValue
                  (recycleCount (.inr bx) τ (nt - 1)) =
                  ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ) := by
                rw [hgenu] at hpgu
                exact (Option.some.inj hpgu).symm
              have hnt_rc : recycleCount (.inr bx) σ (σ.length - 1) + 1 ≤
                  recycleCount (.inr bx) τ nt := by
                by_cases hphm : phaseAfter (recycleCount (.inr bx) τ (nt - 1)) = phx
                · have hrτσ : recycleCount (.inr bx) τ (nt - 1) =
                      recycleCount (.inr bx) σ (σ.length - 1) := by
                    simp only [Cmd.genValue, if_pos hphm] at hgv
                    omega
                  rcases wait_time_recycles_or_pass
                      (isTimeOf_of_pointTime hτ.1 htu) hcmu with
                    ⟨C₁, C₂, hC₁, hC₂, hrec⟩ | ⟨s₂, T₂, hC₁, hE₂, hph₂⟩
                  · have hsucc := recycleCount_succ_of_recycle (.inr bx) τ hC₁
                      (by rw [show nt - 1 + 1 = nt by omega]; exact hC₂) hrec
                    rw [show nt - 1 + 1 = nt by omega] at hsucc
                    omega
                  · exfalso
                    have hph := phase_eq_phaseAfter hchainτ h0τidx bx (nt - 1) _ s₂
                      hC₁ rfl
                    rw [hph] at hph₂
                    exact hph₂ hphm
                · have hrτσ : recycleCount (.inr bx) τ (nt - 1) =
                      recycleCount (.inr bx) σ (σ.length - 1) + 1 := by
                    simp only [Cmd.genValue, if_neg hphm] at hgv
                    omega
                  have := recycleCount_mono (.inr bx) τ (show nt - 1 ≤ nt by omega)
                  omega
              have hcomplete : recycleCount (.inr bx) σ (σ.length - 1) + 1 ≤
                  recycleCount (.inr bx) τ (τ.length - 1) := by
                have hmono := recycleCount_mono (.inr bx) τ
                  (show nt ≤ τ.length - 1 by omega)
                omega
              have hlen := genFiber_length_mb hτ hcomplete hCI hstI hcntI
              have harrA : A = ((genFiber T τ (.inr bx)
                  ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    fun η => isArriveCmd T η && (pointTime T σ η).isSome).length := by
                have h := harr
                rw [hcfg] at h
                exact h
              obtain ⟨d, hdF, hdcen⟩ : ∃ d ∈ genFiber T τ (.inr bx)
                  ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ),
                  (isArriveCmd T d && (pointTime T σ d).isSome) = false := by
                by_contra hno
                push Not at hno
                have hfe : (genFiber T τ (.inr bx)
                    ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ)).filter
                    (fun η => isArriveCmd T η && (pointTime T σ η).isSome) =
                    genFiber T τ (.inr bx)
                      ((recycleCount (.inr bx) σ (σ.length - 1) : ℕ) : ℤ) := by
                  rw [List.filter_eq_self]
                  intro x hx
                  have h := hno x hx
                  cases hb : (isArriveCmd T x && (pointTime T σ x).isSome)
                  · exact absurd hb h
                  · rfl
                rw [hfe, hlen] at harrA
                omega
              have hdarr := genFiber_mb_arrive hdF
              refine ⟨.inr bx, d, hdF, ⟨hdcen, ?_⟩, ?_⟩
              · rintro ⟨hdsy, -, -⟩
                simp [isSyncCmd, hdarr] at hdsy
              · intro m_d hmd
                obtain ⟨cd', md', -, -, -, -, hptd', -, -, hgd⟩ :=
                  genFiber_time_data hτ hdF
                have hmdeq : md' = m_d := by
                  rw [hmd] at hptd'
                  exact (Option.some.inj hptd').symm
                subst hmdeq
                by_contra hgt
                have hmono := recycleCount_mono (.inr bx) τ
                  (show nt ≤ md' - 1 by omega)
                omega
          -- ## `d` has no σ-time, so its thread is unfinished, disabled, parked
          have hdmem := (mem_genFiber.mp hdF).1
          have hdidx : d.idx < (T.prog d.thread).length :=
            ((mem_progPoints_iff T d).mp hdmem).2
          obtain ⟨hdcen, hdnp⟩ := hdnotd
          have hdtime : pointTime T σ d = none := by
            rcases hbu : b_u with nbu | sbu
            · rw [hbu] at hdF
              rcases genFiber_nb_cases hdF with ⟨n_d, hcmd⟩ | ⟨n_d, hcmd⟩
              · cases hpt : pointTime T σ d with
                | none => rfl
                | some m =>
                  exfalso
                  simp [isArriveCmd, hcmd, Cmd.isArrive, hpt] at hdcen
              · cases hpt : pointTime T σ d with
                | none => rfl
                | some m =>
                  exfalso
                  -- an executed sync of the *open* round out-runs the recycle count
                  obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ :=
                    pointTime_sync_recycles hchain h0 hpt hcmd
                  have hspecd := pointTime_spec hchain h0 hpt
                  have hsuccd := recycleCount_succ_of_recycle (.inl nbu) σ hC₁
                    (by rw [show m - 1 + 1 = m by omega]; exact hC₂) hrec
                  rw [show m - 1 + 1 = m by omega] at hsuccd
                  obtain ⟨cd', md', hcd', -, -, -, hptd', -, -, hgd⟩ :=
                    genFiber_time_data hτ hdF
                  have hgeq := hconf.gen_eq d hdmem m hpt
                  have hpgd := pointGen_eq_of_pointTime hcd'
                    (by rw [hcd'] at hcmd; rw [Option.some.inj hcmd]; rfl) hpt
                  rw [hcd'] at hcmd
                  obtain rfl := Option.some.inj hcmd
                  rw [genValue_of_isRegistrant rfl] at hpgd
                  have hpgτ := pointGen_registrant_eq_of_time hcd' rfl rfl
                    (isTimeOf_of_pointTime hτ.1 hptd')
                  rw [hpgd, hpgτ] at hgeq
                  have hinj := Option.some.inj hgeq
                  have hmono := recycleCount_mono (.inl nbu) σ
                    (show m ≤ σ.length - 1 by omega)
                  omega
            · rw [hbu] at hdF
              have hdarr := genFiber_mb_arrive hdF
              cases hpt : pointTime T σ d with
              | none => rfl
              | some m =>
                exfalso
                simp [isArriveCmd, hdarr, Cmd.isArrive, hpt] at hdcen
          have hnpassed : (T.prog d.thread).length - d.idx ≤
              (Tc.prog d.thread).length := by
            by_contra hlt'
            obtain ⟨m, hm⟩ := exists_pointTime_of_passed hchain h0 hlast hdidx
              (by change (Tc.prog d.thread).length + (d.idx + 1) ≤ _; omega)
            rw [hdtime] at hm
            exact absurd hm (by simp)
          have hdne : Tc.prog d.thread ≠ [] := by
            intro h0'
            rw [h0'] at hnpassed
            simp at hnpassed
            omega
          have hdE : s.E d.thread = false := by
            cases hE : s.E d.thread with
            | false => rfl
            | true =>
              obtain ⟨c₀, rest, hcons⟩ : ∃ c₀ rest,
                  Tc.prog d.thread = c₀ :: rest := by
                cases hTt : Tc.prog d.thread with
                | nil => exact absurd hTt hdne
                | cons a l => exact ⟨a, l, rfl⟩
              exact (hstep_of_enabled d.thread c₀ rest hcons hE).elim
          obtain ⟨e, heflavor, hepts, hept, heE, heth, heidx⟩ :=
            hparked_point d.thread hdne hdE
          -- `e ≠ d`: at equality `d` would be a parked sync (excluded) or a
          -- wait/sync command clash with its fiber kind
          have hlt_idx : e.idx < d.idx := by
            have hle_idx : e.idx ≤ d.idx := by
              rw [heidx]
              omega
            rcases Nat.lt_or_ge e.idx d.idx with h | h
            · exact h
            · exfalso
              have hed : e = d := by
                have heeta : e = ⟨e.thread, e.idx⟩ := rfl
                have hdeta : d = ⟨d.thread, d.idx⟩ := rfl
                rw [heeta, hdeta, heth, show e.idx = d.idx by omega]
              rcases heflavor with ⟨b_e2, n_e2, hcme, heF⟩ | ⟨b_e2, ph_e2, hcme, -, -⟩
              · rw [hed] at hcme hept
                exact hdnp ⟨by simp [isSyncCmd, hcme], hept, hdE⟩
              · rw [hed] at hcme
                rcases hbu : b_u with nbu | sbu
                · rw [hbu] at hdF
                  rcases genFiber_nb_cases hdF with ⟨n_d, hcmd⟩ | ⟨n_d, hcmd⟩ <;>
                    (rw [hcmd] at hcme; exact absurd (Option.some.inj hcme) (by simp))
                · rw [hbu] at hdF
                  have hdarr := genFiber_mb_arrive hdF
                  rw [hdarr] at hcme
                  exact absurd (Option.some.inj hcme) (by simp)
          obtain ⟨m_d, hmd⟩ := hτtime d hdidx
          have heidx' : e.idx < (T.prog e.thread).length :=
            ((mem_progPoints_iff T e).mp hepts).2
          obtain ⟨m_e, hme⟩ := hτtime e heidx'
          have hlt_time : m_e < m_d := hpo e d heth hlt_idx m_e m_d hme hmd
          have hle_time : m_d ≤ nt := hd_cap m_d hmd
          exact ih m_e (by omega) e heflavor hept heE hme
      -- ## seed the descent: the stuck non-`done` configuration has a parked op
      have hndone : ¬ CTA.IsDone Tc := by
        intro hdone
        refine hstuck ⟨_, CTAStep.done hdone ?_ ?_⟩
        · intro b I A n hbeq
          rcases hguard b with hu | ⟨I', A', n', hcfg, hlt⟩
          · rw [hu] at hbeq
            exact absurd (congrArg NamedBarrierState.count hbeq)
              (by simp [NamedBarrierState.unconfigured])
          · rw [hcfg] at hbeq
            have hI : I' = I := congrArg NamedBarrierState.synced hbeq
            have hA : A' = A := congrArg NamedBarrierState.arrived hbeq
            have hn : (some n' : Option ℕ+) = some n :=
              congrArg NamedBarrierState.count hbeq
            obtain rfl := Option.some.inj hn
            have hIlen : I'.length = I.length := congrArg List.length hI
            omega
        · intro sb I A n ph hbeq
          rcases hmguard sb with hu | ⟨I', A', n', ph', hcfg, hlt⟩
          · rw [hu] at hbeq
            exact absurd (congrArg MBarrierState.count hbeq)
              (by simp [MBarrierState.uninitialized])
          · rw [hcfg] at hbeq
            have hA : A' = A := congrArg MBarrierState.arrived hbeq
            have hn : (some n' : Option ℕ+) = some n :=
              congrArg MBarrierState.count hbeq
            obtain rfl := Option.some.inj hn
            omega
      obtain ⟨i₀, hi₀ne⟩ : ∃ i, Tc.prog i ≠ [] := by
        by_contra hall
        apply hndone
        intro i hi
        by_contra hne'
        exact hall ⟨i, hne'⟩
      have hE₀ : s.E i₀ = false := by
        cases hE : s.E i₀ with
        | false => rfl
        | true =>
          obtain ⟨c₀, rest, hcons⟩ : ∃ c₀ rest, Tc.prog i₀ = c₀ :: rest := by
            cases hTt : Tc.prog i₀ with
            | nil => exact absurd hTt hi₀ne
            | cons a l => exact ⟨a, l, rfl⟩
          exact (hstep_of_enabled i₀ c₀ rest hcons hE).elim
      obtain ⟨x₀, hflavor₀, hpts₀, hpt₀, hE₀', -, -⟩ :=
        hparked_point i₀ hi₀ne hE₀
      have hx₀idx : x₀.idx < (T.prog x₀.thread).length :=
        ((mem_progPoints_iff T x₀).mp hpts₀).2
      obtain ⟨n_t, hnt⟩ := hτtime x₀ hx₀idx
      exact hdescend n_t x₀ hflavor₀ hpt₀ hE₀' hnt

/-! ## Completeness contradiction lemmas

The per-mode refutations consumed by `not_wellSynchronized_of_check_false`:
each turns a failing-check witness plus `hws : T.WellSynchronized` into
`False`. -/

/-- **Generation contradiction** (the heart of completeness). In a
well-synchronized CTA, a *registrant* `c1` on `b` of generation `k` and any
barrier op `ca` on `b` of generation `k + 1` must be ordered `c1` before `ca`:
otherwise the realizability lemma produces a complete trace running `ca`
*before* `c1`, where `ca` sees at most `k` recyclings of `b` — but a
generation-`(k + 1)` op sees at least `k + 1` (`le_of_genValue`). -/
theorem reverse_barrier_contradiction {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 ca : ProgPoint} {b : NamedBarrier ⊕ SharedBarrier} {k : ℤ}
    (hc1 : c1 ∈ T.progPoints) (hca : ca ∈ T.progPoints)
    {cmd1 : Cmd} (hcmd1 : T.cmdAt c1 = some cmd1) (hreg1 : cmd1.isRegistrant = true)
    (hc1bar : cmd1.barrier? = some b)
    {cmda : Cmd} (hcmda : T.cmdAt ca = some cmda) (hcabar : cmda.barrier? = some b)
    (hgen1 : pointGen T τ c1 = some k) (hgena : pointGen T τ ca = some (k + 1))
    (hnothb : ¬ happensBefore T τ c1 ca) : False := by
  obtain ⟨τ', hτ'c, n1, n2, ht1, ht2, hlt⟩ := exists_reversing_trace hτ hws hc1 hca hnothb
  obtain ⟨sd, hdone⟩ := hτ.2
  obtain ⟨m1, hm1⟩ :=
    exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨m2, hm2⟩ :=
    exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T ca).mp hca).2
  have hgenc1 : IsGenOf (Config.run State.initial T) τ c1 (pointGen T τ c1) :=
    isGenOf_pointGen hcmd1 hc1bar hm1
  have hgenca : IsGenOf (Config.run State.initial T) τ ca (pointGen T τ ca) :=
    isGenOf_pointGen hcmda hcabar hm2
  obtain ⟨g1, hg1τ, hg1τ'⟩ := hws.2 τ τ' hτ.1 hτ'c c1
    ⟨b, by change (T.cmdAt c1).bind Cmd.barrier? = some b; rw [hcmd1]; exact hc1bar⟩
  obtain ⟨g2, hg2τ, hg2τ'⟩ := hws.2 τ τ' hτ.1 hτ'c ca
    ⟨b, by change (T.cmdAt ca).bind Cmd.barrier? = some b; rw [hcmda]; exact hcabar⟩
  have hg1k : g1 = k :=
    Option.some.inj ((IsGenOf.unique hg1τ hgenc1).trans hgen1)
  have hg2k : g2 = k + 1 :=
    Option.some.inj ((IsGenOf.unique hg2τ hgenca).trans hgena)
  have hv1 : g1 = cmd1.genValue (recycleCount b τ' (n1 - 1)) :=
    isGenOf_genValue hg1τ' hcmd1 hc1bar ht1
  have hv2 : g2 = cmda.genValue (recycleCount b τ' (n2 - 1)) :=
    isGenOf_genValue hg2τ' hcmda hcabar ht2
  rw [genValue_of_isRegistrant hreg1] at hv1
  have hle2 : g2 ≤ (recycleCount b τ' (n2 - 1) : ℤ) := le_of_genValue hv2.symm
  have hmono : recycleCount b τ' (n2 - 1) ≤ recycleCount b τ' (n1 - 1) :=
    recycleCount_mono b τ' (by omega)
  omega

/-- **First-instruction uses of an mbarrier refute well-synchronization**: from
the initial configuration every mbarrier is uninitialized and both step guards
hold, so the thread's `arrive_mb`/`wait_mb` errs at once — a two-configuration
complete trace ending in `err`, contradicting `completeTrace_ends_done`. (This
supersedes the paper's parity argument for first-instruction waits: the guarded
error productions make the refutation immediate.) -/
theorem firstInstr_use_not_wellSynchronized {T : CTA} {c : ProgPoint}
    {sb : SharedBarrier} (hidx : c.idx = 0)
    (huse : (T.cmdAt c).bind Cmd.usesMBarrier? = some sb) :
    ¬ T.WellSynchronized := by
  intro hws
  -- decode the use command and the thread's program shape
  obtain ⟨cmd, hcmd, husecmd⟩ : ∃ cmd, T.cmdAt c = some cmd ∧
      cmd.usesMBarrier? = some sb := by
    cases hc : T.cmdAt c with
    | none => rw [hc] at huse; exact absurd huse (by simp)
    | some cmd => rw [hc] at huse; exact ⟨cmd, rfl, huse⟩
  obtain ⟨rest, hprog⟩ : ∃ rest, T.prog c.thread = cmd :: rest := by
    have h0 : (T.prog c.thread)[0]? = some cmd := by
      have h := hcmd
      simp only [CTA.cmdAt] at h
      rwa [hidx] at h
    cases hp : T.prog c.thread with
    | nil => rw [hp] at h0; simp at h0
    | cons a tl =>
      rw [hp] at h0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      exact ⟨tl, by rw [h0]⟩
  -- the erring thread step from the initial state
  have herr : ∃ P', ThreadStep (.run State.initial c.thread (T.prog c.thread))
      (.err c.thread P') := by
    cases cmd with
    | arrive_mb sb' =>
      exact ⟨_, by rw [hprog]; exact ThreadStep.mb_arrive_err rfl rfl⟩
    | wait_mb sb' ph =>
      exact ⟨_, by rw [hprog]; exact ThreadStep.mb_wait_err rfl rfl⟩
    | read l => simp [Cmd.usesMBarrier?] at husecmd
    | write l => simp [Cmd.usesMBarrier?] at husecmd
    | arrive_nb nb n => simp [Cmd.usesMBarrier?] at husecmd
    | sync_nb nb n => simp [Cmd.usesMBarrier?] at husecmd
    | init_mb sb' n => simp [Cmd.usesMBarrier?] at husecmd
  obtain ⟨P', hth⟩ := herr
  have hbar : ∀ nb, State.initial.BN nb = NamedBarrierState.unconfigured ∨
      ∃ I A n, State.initial.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat) :=
    fun nb => Or.inl rfl
  have hmbar : ∀ sb', State.initial.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A n ph, State.initial.BM sb' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat) :=
    fun sb' => Or.inl rfl
  have hstep : CTAStep (Config.run State.initial T) (Config.err T) :=
    CTAStep.error hbar hmbar hth
  have htrace : IsCompleteTraceFrom (Config.run State.initial T)
      [Config.run State.initial T, Config.err T] := by
    refine ⟨⟨?_, Config.err T, by simp, Or.inr (Or.inl ⟨T, rfl⟩)⟩, by simp⟩
    change List.IsChain CTAStep [Config.run State.initial T, Config.err T]
    rw [List.isChain_cons]
    exact ⟨fun y hy => by rw [List.head?_cons, Option.mem_some_iff] at hy; exact hy ▸ hstep,
      List.isChain_singleton _⟩
  obtain ⟨sd, hd⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
  simp at hd


/-- Across one step, a thread's program either stays or drops exactly its
head. -/
theorem step_progOf_eq_or_tail {C C' : Config} (hstep : CTAStep C C') (t : ThreadId) :
    C'.progOf t = C.progOf t ∨ C'.progOf t = (C.progOf t).tail := by
  obtain ⟨d, hd⟩ := hstep.progOf_drop t
  have hlen := hstep.progOf_length_le_succ t
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · left
    rw [hd, List.drop_zero]
  · right
    rw [hd, ← List.drop_one]
    rw [hd, List.length_drop] at hlen
    rcases Nat.lt_or_ge ((C.progOf t).length) (d + 1) with hlt | hge
    · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    · have hd1 : d = 1 := by omega
      rw [hd1]

/-- **A first-instruction `sync_nb` registers into round one.** If thread `t`'s
program starts with `sync_nb nb m`, and at index `1` of the trace `t` is already
parked in `nb`'s synced list with its program intact, then `t`'s first
instruction executes with recycle count `0`: the parked thread persists until
`nb`'s *first* recycle, which is the wake that runs it. -/
theorem firstSync_recycleCount_zero {T : CTA} {τ : List Config} {t : ThreadId}
    {nb : NamedBarrier} {m : ℕ+} {tail : Prog} {m' : Nat} {s1 : State} {T1 : CTA}
    (hcomp : IsCompleteTraceFrom (Config.run State.initial T) τ)
    (hprogT : T.prog t = Cmd.sync_nb nb m :: tail)
    (hC1 : τ[1]? = some (Config.run s1 T1))
    (hsync1 : t ∈ (s1.BN nb).synced) (hprog1 : T1.prog t = T.prog t)
    (hm' : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ m') :
    recycleCount (.inl nb) τ (m' - 1) = 0 := by
  have hchain := hcomp.1.subtrace
  have hhead : τ[0]? = some (Config.run State.initial T) := by
    have h0 : τ[0]? = τ.head? := by cases τ <;> rfl
    rw [h0]
    exact hcomp.2
  have hBItr : ∀ C ∈ τ, ∀ s', C.state? = some s' → s'.BlockInv :=
    blockInv_chain hchain hcomp.2 (by
      intro s' hs'
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs'
      subst hs'
      exact State.BlockInv.initial)
  have hm'len : m' < τ.length := by
    obtain ⟨_, _, _, _, _C', hj, _, hCj1, _, _⟩ := hm'
    have := (List.getElem?_eq_some_iff.mp hCj1).1
    omega
  have hrun : ∀ j, j < m' → ∃ s T2, τ[j]? = some (Config.run s T2) := by
    intro j hj
    obtain ⟨Cj, hCj⟩ : ∃ C, τ[j]? = some C :=
      ⟨_, List.getElem?_eq_getElem (show j < τ.length by omega)⟩
    obtain ⟨Cj1, hCj1⟩ : ∃ C, τ[j + 1]? = some C :=
      ⟨_, List.getElem?_eq_getElem (show j + 1 < τ.length by omega)⟩
    obtain ⟨s, T2, heq⟩ := CTAStep.source_run (chain_step hchain hCj hCj1)
    exact ⟨s, T2, by rw [hCj, heq]⟩
  -- the parked thread persists with its program intact through `[1, m'-1]`
  have P : ∀ j, 1 ≤ j → j ≤ m' - 1 → ∃ sj Tj, τ[j]? = some (Config.run sj Tj) ∧
      t ∈ (sj.BN nb).synced ∧ Tj.prog t = T.prog t := by
    intro j
    induction j with
    | zero => intro h _; omega
    | succ kk ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos kk with hk0 | hkpos
      · subst hk0
        exact ⟨s1, T1, hC1, hsync1, hprog1⟩
      · obtain ⟨sk, Tk, hCk, hsk, hpk⟩ := ih hkpos (by omega)
        obtain ⟨sk1, Tk1, hCk1⟩ := hrun (kk + 1) (by omega)
        have hst : CTAStep (Config.run sk Tk) (Config.run sk1 Tk1) :=
          chain_step hchain hCk hCk1
        have hskb : t ∈ sk.blocked (.inl nb) := hsk
        have hnorec : stepRecyclesBarrier (.inl nb) (Config.run sk Tk)
            (Config.run sk1 Tk1) = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have hwake : (Config.run sk1 Tk1).progOf t
              = ((Config.run sk Tk).progOf t).tail :=
            recycle_advances_blocked hst rfl hskb hc
          have htime : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ (kk + 1) := by
            refine ⟨hcomp, ?_, kk, _, _, rfl, hCk, hCk1, ?_, ?_⟩
            · change 0 < (T.prog t).length
              rw [hprogT]
              simp
            · change Tk.prog t = (T.prog t).drop 0
              rw [List.drop_zero]
              exact hpk
            · change Tk1.prog t = (T.prog t).drop 1
              have heq : Tk1.prog t = (Tk.prog t).tail := hwake
              rw [heq, hpk, hprogT]
              rfl
          have := IsTimeOf.unique htime hm'
          omega
        refine ⟨sk1, Tk1, hCk1, blocked_persists hst rfl
          (hBItr _ (List.mem_of_getElem? hCk) sk rfl) hskb hnorec rfl, ?_⟩
        rcases step_progOf_eq_or_tail hst t with heq | htl
        · have h2 : Tk1.prog t = Tk.prog t := heq
          rw [h2, hpk]
        · exfalso
          have hrec := sync_drop_recycles hst
            (show (Config.run sk Tk).progOf t = Cmd.sync_nb nb m :: tail by
              change Tk.prog t = _
              rw [hpk, hprogT])
            (show (Config.run sk1 Tk1).progOf t = tail by
              change Tk1.prog t = _
              have h2 : Tk1.prog t = (Tk.prog t).tail := htl
              rw [h2, hpk, hprogT]
              rfl)
          rw [hrec] at hnorec
          exact absurd hnorec (by simp)
  -- hence no step in `[0, m'-1)` recycles `nb`
  rw [recycleCount, List.countP_eq_zero]
  intro j hjmem
  rw [List.mem_range] at hjmem
  rw [Bool.not_eq_true]
  obtain ⟨Cj, hCj⟩ : ∃ C, τ[j]? = some C :=
    ⟨_, List.getElem?_eq_getElem (show j < τ.length by omega)⟩
  obtain ⟨Cj1, hCj1⟩ : ∃ C, τ[j + 1]? = some C :=
    ⟨_, List.getElem?_eq_getElem (show j + 1 < τ.length by omega)⟩
  simp only [hCj, hCj1]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- the first step leaves the unconfigured `nb` un-full
    rw [hhead] at hCj
    obtain rfl := Option.some.inj hCj
    cases Cj1 <;> rfl
  · -- a recycle in `[1, m'-1)` would wake the parked `t` too early
    obtain ⟨sj, Tj, hCjr, hsj, hpj⟩ := P j hjpos (by omega)
    rw [hCjr] at hCj
    obtain rfl := Option.some.inj hCj
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hst : CTAStep (Config.run sj Tj) Cj1 := chain_step hchain hCjr hCj1
    have hwake : Cj1.progOf t = ((Config.run sj Tj).progOf t).tail :=
      recycle_advances_blocked hst rfl (show t ∈ sj.blocked (.inl nb) from hsj) hc
    -- `Cj1` is a `run` (there is a step out of it, since `j + 1 < m' < τ.length`)
    obtain ⟨sj1, Tj1, rfl⟩ : ∃ s T2, Cj1 = Config.run s T2 := by
      obtain ⟨s, T2, h⟩ := hrun (j + 1) (by omega)
      exact ⟨s, T2, Option.some.inj (hCj1.symm.trans h)⟩
    have htime : IsTimeOf (Config.run State.initial T) τ ⟨t, 0⟩ (j + 1) := by
      refine ⟨hcomp, ?_, j, _, _, rfl, hCjr, hCj1, ?_, ?_⟩
      · change 0 < (T.prog t).length
        rw [hprogT]
        simp
      · change Tj.prog t = (T.prog t).drop 0
        rw [List.drop_zero]
        exact hpj
      · change Tj1.prog t = (T.prog t).drop 1
        have heq : Tj1.prog t = (Tj.prog t).tail := hwake
        rw [heq, hpj, hprogT]
        rfl
    have := IsTimeOf.unique htime hm'
    omega

/-- **Generation read-back at recycle count 0.** A registrant `c2` of positive
generation cannot belong to a well-synchronized CTA if some complete trace
`τ''` runs it with no recyclings of its barrier before it. -/
theorem firstInstr_contradiction {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints) {cmd2 : Cmd}
    (hcmd2 : T.cmdAt c2 = some cmd2) (hreg2 : cmd2.isRegistrant = true)
    {b : NamedBarrier ⊕ SharedBarrier} (hbar2 : cmd2.barrier? = some b)
    {k : ℤ} (hgen2 : pointGen T τ c2 = some k) (hge1 : 1 ≤ k)
    {τ'' : List Config}
    (hcomp'' : IsCompleteTraceFrom (Config.run State.initial T) τ'')
    (hrc : ∀ m', IsTimeOf (Config.run State.initial T) τ'' c2 m' →
      recycleCount b τ'' (m' - 1) = 0) : False := by
  obtain ⟨sd, hdone⟩ := hτ.2
  obtain ⟨mτ, hmτ⟩ :=
    exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T c2).mp hc2).2
  obtain ⟨g, hgτ, hgτ''⟩ := hws.2 τ τ'' hτ.1 hcomp'' c2
    ⟨b, by change (T.cmdAt c2).bind Cmd.barrier? = some b; rw [hcmd2]; exact hbar2⟩
  have hgeq : g = k :=
    Option.some.inj ((IsGenOf.unique hgτ (isGenOf_pointGen hcmd2 hbar2 hmτ)).trans hgen2)
  obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp''
  obtain ⟨m'', hm''⟩ := exists_time_of_ends_done hcomp'' hdone''
    ((mem_progPoints_iff T c2).mp hc2).2
  have hval : g = cmd2.genValue (recycleCount b τ'' (m'' - 1)) :=
    isGenOf_genValue hgτ'' hcmd2 hbar2 hm''
  rw [genValue_of_isRegistrant hreg2, hrc m'' hm''] at hval
  omega

/-- **Completeness, the predecessor-less (`c2.idx = 0`) case** (mode 1b). A
registrant `c2` that is the first instruction of its thread yet is assigned
generation `k + 1` (for a same-barrier registrant `c1` of generation `k ≥ 0`)
cannot belong to a well-synchronized CTA: nothing anchors it after generation
`k`, so a schedule that steps `c2`'s thread first lands it in an earlier
generation. An `arrive_nb` has no in-edges at index `0`, so the reversing-trace
argument applies directly; a `sync_nb` is stepped first (`sync_configure`),
parking it into round one (`firstSync_recycleCount_zero`); an `arrive_mb` errs
at once (`firstInstr_use_not_wellSynchronized`). -/
theorem firstInstr_highGen_not_wellSynchronized {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 : ProgPoint} (hc1 : c1 ∈ T.progPoints) {b : NamedBarrier ⊕ SharedBarrier} {k : ℤ}
    (hreg1 : registrantGen T τ c1 = some (b, k))
    {c2 : ProgPoint} (hc2 : c2 ∈ T.progPoints)
    (hreg2 : registrantGen T τ c2 = some (b, k + 1))
    (hidx0 : c2.idx = 0) : False := by
  obtain ⟨cmd1, hcmd1, hisreg1, hbar1, hgen1⟩ := registrantGen_some hreg1
  obtain ⟨cmd2, hcmd2, hisreg2, hbar2, hgen2⟩ := registrantGen_some hreg2
  have hk0 : 0 ≤ k := pointGen_registrant_nonneg hcmd1 hisreg1 hgen1
  cases cmd2 with
  | read l => simp [Cmd.isRegistrant] at hisreg2
  | write l => simp [Cmd.isRegistrant] at hisreg2
  | init_mb sb n => simp [Cmd.isRegistrant] at hisreg2
  | wait_mb sb ph => simp [Cmd.isRegistrant] at hisreg2
  | arrive_mb sb =>
    exact firstInstr_use_not_wellSynchronized hidx0 (by rw [hcmd2]; rfl) hws
  | arrive_nb nb m =>
    have hnothb : ¬ happensBefore T τ c1 c2 := by
      intro h
      rcases Relation.ReflTransGen.cases_tail h with heq | ⟨d, _, hdc2⟩
      · rw [heq] at hgen2
        have := Option.some.inj (hgen1.symm.trans hgen2)
        omega
      · obtain ⟨_, _, hcase⟩ := initRelation_cases hdc2
        rcases hcase with hpo | ⟨nb', n', hsync, _, _⟩ | ⟨sb', ph', hwait, _, _⟩
        · have hii : c2.idx = d.idx + 1 := by rw [hpo]
          omega
        · rw [hcmd2] at hsync
          exact absurd hsync (by simp)
        · rw [hcmd2] at hwait
          exact absurd hwait (by simp)
    exact reverse_barrier_contradiction hτ hws hc1 hc2 hcmd1 hisreg1 hbar1 hcmd2 hbar2
      hgen1 hgen2 hnothb
  | sync_nb nb m =>
    have hbeq : b = .inl nb := by
      have h := hbar2
      simp only [Cmd.barrier?, Option.some.injEq] at h
      exact h.symm
    subst hbeq
    have hi : c2.thread ∈ T.ids := ((mem_progPoints_iff T c2).mp hc2).1
    have hc2eq : c2 = ⟨c2.thread, 0⟩ := by rw [← hidx0]
    have hhead0 : (T.prog c2.thread)[0]? = some (Cmd.sync_nb nb m) := by
      have h := hcmd2
      simp only [CTA.cmdAt, hidx0] at h
      exact h
    obtain ⟨tl, hprogT⟩ : ∃ tl, T.prog c2.thread = Cmd.sync_nb nb m :: tl := by
      have hne : T.prog c2.thread ≠ [] := by
        intro h
        rw [h] at hhead0
        simp at hhead0
      obtain ⟨hd, tl, hp⟩ := List.exists_cons_of_ne_nil hne
      rw [hp] at hhead0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead0
      exact ⟨tl, by rw [hp, hhead0]⟩
    -- first step: `sync_configure` of `c2`'s thread, then complete the trace
    set s1 : State := { State.initial with
      E := Function.update State.initial.E c2.thread false,
      BN := Function.update State.initial.BN nb ⟨[c2.thread], 0, some m⟩ } with hs1def
    set T1 : CTA := T.set c2.thread hi (T.prog c2.thread) with hT1def
    have hts : ThreadStep (.run State.initial c2.thread (T.prog c2.thread))
        (.run s1 c2.thread (T.prog c2.thread)) := by
      rw [hprogT]
      exact ThreadStep.sync_configure rfl rfl
    have hstep01 : CTAStep (Config.run State.initial T) (Config.run s1 T1) :=
      CTAStep.interleave hi (fun _ => Or.inl rfl) (fun _ => Or.inl rfl) hts
    have hinv1 : (Config.barriersWithin T.barrierSet (Config.run s1 T1)) :=
      barriersWithin_of_reaches (Relation.ReflTransGen.single hstep01)
    obtain ⟨τr, hτr⟩ := exists_completeTrace T.barrierSet (Config.run s1 T1) hinv1
    have hτrne : τr ≠ [] := by
      intro h
      rw [h] at hτr
      obtain ⟨_, hl, _⟩ := hτr.1.ends
      simp at hl
    have hcomp'' : IsCompleteTraceFrom (Config.run State.initial T)
        (Config.run State.initial T :: τr) := by
      refine ⟨⟨?_, ?_⟩, by simp⟩
      · change List.IsChain CTAStep (Config.run State.initial T :: τr)
        rw [List.isChain_cons]
        refine ⟨fun y hy => ?_, hτr.1.subtrace⟩
        rw [hτr.2, Option.mem_some_iff] at hy
        subst hy
        exact hstep01
      · obtain ⟨Cn, hlast, hterm⟩ := hτr.1.ends
        exact ⟨Cn, by rw [List.getLast?_cons_of_ne_nil hτrne]; exact hlast, hterm⟩
    have hC1'' : (Config.run State.initial T :: τr)[1]? = some (Config.run s1 T1) := by
      have h1 : (Config.run State.initial T :: τr)[1]? = τr[0]? := rfl
      have h0 : τr[0]? = τr.head? := by cases τr <;> rfl
      rw [h1, h0]
      exact hτr.2
    have hsync1 : c2.thread ∈ (s1.BN nb).synced := by
      rw [hs1def]
      simp [Function.update_self]
    have hprog1 : T1.prog c2.thread = T.prog c2.thread := by
      rw [hT1def]
      simp [WeftCommon.CTA.set]
    refine firstInstr_contradiction hτ hws hc2 hcmd2 hisreg2 hbar2 hgen2 (by omega)
      hcomp'' ?_
    intro m' hm'
    rw [hc2eq] at hm'
    exact firstSync_recycleCount_zero hcomp'' hprogT hC1'' hsync1 hprog1 hm'

/-- **Mode 4: duplicate initializations refute a successful trace** — no
well-synchronization needed. Two distinct `init_mb` points of the same mbarrier
both execute in `τ`; whichever runs second drops an `init_mb` head from an
*already initialized* barrier (`count_some_persists` from the first), which
only `mb_init` — requiring `uninitialized` — could do. -/
theorem unique_init_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    {ci cj : ProgPoint} {sb : SharedBarrier} {n n' : ℕ+}
    (hci : ci ∈ T.progPoints) (hcj : cj ∈ T.progPoints)
    (hcmdi : T.cmdAt ci = some (.init_mb sb n))
    (hcmdj : T.cmdAt cj = some (.init_mb sb n'))
    (hne : ci ≠ cj) : False := by
  obtain ⟨sd, hdone⟩ := hτ.2
  have hchain := hτ.1.1.subtrace
  obtain ⟨mi, hmi⟩ :=
    exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T ci).mp hci).2
  obtain ⟨mj, hmj⟩ :=
    exists_time_of_ends_done hτ.1 hdone ((mem_progPoints_iff T cj).mp hcj).2
  -- an earlier init makes the later one drop from an initialized barrier
  have key : ∀ {p q : ProgPoint} {np nq : ℕ+} {mp mq : Nat},
      T.cmdAt p = some (Cmd.init_mb sb np) → T.cmdAt q = some (Cmd.init_mb sb nq) →
      IsTimeOf (Config.run State.initial T) τ p mp →
      IsTimeOf (Config.run State.initial T) τ q mq → mp < mq → False := by
    intro p q np nq mp mq hp hq hmp hmq hlt
    have hmp1 : 1 ≤ mp := by
      obtain ⟨_, _, j, _, _, hj, _⟩ := hmp
      omega
    have hmq1 : 1 ≤ mq := by
      obtain ⟨_, _, j, _, _, hj, _⟩ := hmq
      omega
    obtain ⟨Cp, Cp', hCp, hCp', hshape_p⟩ := time_drop_evidence hmp hp
    obtain ⟨Cq, Cq', hCq, hCq', hshape_q⟩ := time_drop_evidence hmq hq
    have hmqlen : mq < τ.length := (List.getElem?_eq_some_iff.mp hCq').1
    have hstep_p : CTAStep Cp Cp' := by
      refine chain_step hchain hCp ?_
      rw [show mp - 1 + 1 = mp by omega]
      exact hCp'
    obtain ⟨sp', Tp', hCp'eq, hcount⟩ := init_drop_target_initialized hstep_p hshape_p rfl
    -- the count persists from `mp` through `mq - 1`
    have hpers : ∀ d, mp + d ≤ mq - 1 → ∃ sd Td, τ[mp + d]? = some (Config.run sd Td) ∧
        (sd.BM sb).count = some np := by
      intro d
      induction d with
      | zero =>
        intro _
        rw [hCp'eq] at hCp'
        exact ⟨sp', Tp', hCp', hcount⟩
      | succ e ih =>
        intro hle
        obtain ⟨sd, Td, hCd, hcnt⟩ := ih (by omega)
        obtain ⟨Cn, hCn⟩ : ∃ C, τ[mp + e + 1]? = some C :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hstep := chain_step hchain hCd hCn
        obtain ⟨sn, Tn, rfl⟩ : ∃ s2 T2, Cn = Config.run s2 T2 := by
          obtain ⟨Cnn, hCnn⟩ : ∃ C, τ[mp + e + 1 + 1]? = some C :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          cases chain_step hchain hCn hCnn <;> exact ⟨_, _, rfl⟩
        exact ⟨sn, Tn, hCn, count_some_persists hstep rfl rfl hcnt⟩
    -- `q`'s drop has an uninitialized source — contradiction
    have hstep_q : CTAStep Cq Cq' := by
      refine chain_step hchain hCq ?_
      rw [show mq - 1 + 1 = mq by omega]
      exact hCq'
    obtain ⟨sq, Tq, hCqeq, huninitq⟩ := init_drop_uninitialized hstep_q hshape_q rfl
    obtain ⟨sd, Td, hCd, hcnt⟩ := hpers (mq - 1 - mp) (by omega)
    rw [show mp + (mq - 1 - mp) = mq - 1 by omega] at hCd
    rw [hCqeq] at hCq
    have heq := Option.some.inj (hCd.symm.trans hCq)
    rw [WeftCommon.Config.run.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [huninitq] at hcnt
    simp [MBarrierState.uninitialized] at hcnt
  rcases Nat.lt_trichotomy mi mj with hlt | heq | hgt
  · exact key hcmdi hcmdj hmi hmj hlt
  · -- equal times: the same step drops both heads — same thread, same point
    subst heq
    obtain ⟨Ci, Ci', hCi, hCi', hshi⟩ := time_drop_evidence hmi hcmdi
    obtain ⟨Cj2, Cj2', hCj2, hCj2', hshj⟩ := time_drop_evidence hmj hcmdj
    obtain rfl : Ci = Cj2 := Option.some.inj (hCi.symm.trans hCj2)
    obtain rfl : Ci' = Cj2' := Option.some.inj (hCi'.symm.trans hCj2')
    have hmi1 : 1 ≤ mi := by
      obtain ⟨_, _, j, _, _, hj, _⟩ := hmi
      omega
    have hstep : CTAStep Ci Ci' := by
      refine chain_step hchain hCi ?_
      rw [show mi - 1 + 1 = mi by omega]
      exact hCi'
    have hteq : ci.thread = cj.thread :=
      init_head_drop_same_thread hstep hshi rfl hshj rfl
    -- same index, via the drop shapes of the two time witnesses
    obtain ⟨_, hidxLi, ji, Ci0, Ci0', hji, hCji, hCji', hCeqi, _⟩ := id hmi
    obtain ⟨_, hidxLj, jj, Cj0, Cj0', hjj, hCjj, hCjj', hCeqj, _⟩ := id hmj
    have hjieq : jj = ji := by omega
    rw [hjieq] at hCjj
    obtain rfl : Ci0 = Cj0 := Option.some.inj (hCji.symm.trans hCjj)
    rw [← hteq] at hCeqj hidxLj
    have e1 := congrArg List.length hCeqi
    have e2 := congrArg List.length hCeqj
    rw [List.length_drop] at e1 e2
    have hidx : ci.idx = cj.idx := by omega
    apply hne
    obtain ⟨cit, cii⟩ := ci
    obtain ⟨cjt, cji⟩ := cj
    simp only at hteq hidx
    rw [hteq, hidx]
  · exact key hcmdj hcmdi hmj hmi hgt

/-- **Mode 3, reachable-err flavor**: the use `u` is `hb`-forced after the
initialization (through a release edge) but its *predecessor* is not — so a
schedule reaches `u` before the initialization and errs. Run the ideal
`G = {η | ¬ happensBefore T τ ip η}` to its cut: `pred(u) ∈ G` executes,
`u ∉ G` (from `hbu`) leaves `u`'s thread control at `u`, enabled, with `sb`
uninitialized (`ip ∉ G` never ran; the initialization is unique) — after
draining any pending recycle (empty-wake: nothing is blocked at the cut), the
`mb_arrive_err`/`mb_wait_err` production fires, giving a complete trace ending
`err`, refuting `hws`. -/
theorem init_pred_unordered_err_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hws : T.WellSynchronized) (huniq : okUniqueInitCheck T τ = true)
    {ip u : ProgPoint} {sb : SharedBarrier} {n : ℕ+}
    (hip : ip ∈ T.progPoints) (hu : u ∈ T.progPoints)
    (hcmdip : T.cmdAt ip = some (.init_mb sb n))
    (huse : (T.cmdAt u).bind Cmd.usesMBarrier? = some sb)
    (hidx1 : 1 ≤ u.idx)
    (hnpred : ¬ happensBefore T τ ip ⟨u.thread, u.idx - 1⟩)
    (hbu : happensBefore T τ ip u) : False := by
  classical
  -- run the ideal `G = {η | ¬ hb(ip, η)}` to its clean cut
  obtain ⟨τ'', p, s_G, T_G, hcomp, hpcfg, hGprog, hbempty⟩ := run_ideal (η₁ := ip) hτ hws
  have hchain'' := hcomp.1.subtrace
  have h0idx'' : τ''[0]? = some (Config.run State.initial T) := by
    have hgen0 : ∀ l : List Config, l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen0]; exact hcomp.2
  have hreachG : Relation.ReflTransGen CTAStep (Config.run State.initial T)
      (Config.run s_G T_G) := reaches_of_chain_getElem hchain'' h0idx'' p _ hpcfg
  have hwfG := WF_of_reaches hreachG
  have hamof : s_G.AtMostOneFull := hwfG.2.2.2.2.1
  -- every thread is enabled at the cut: nothing is blocked anywhere
  have hEall : ∀ i, s_G.E i = true := by
    intro i
    cases hE : s_G.E i with
    | true => rfl
    | false =>
      exfalso
      have hei : s_G.EnabledInv := by
        refine enabledInv_chain hchain'' hcomp.2 ?_ _ (List.mem_of_getElem? hpcfg) s_G rfl
        intro s₀ hs₀
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hs₀
        subst hs₀
        exact State.EnabledInv.initial
      obtain ⟨b, hib⟩ := hei i hE
      exact hbempty b i hib
  -- `ip ∈ F` never runs in the ideal prefix, so `sb`'s count is still `⊥` at the cut
  have hipidx : ip.idx < (T.prog ip.thread).length := ((mem_progPoints_iff T ip).mp hip).2
  have hfip : fcut T τ ip ip.thread ≤ ip.idx := fcut_le_of_hb Relation.ReflTransGen.refl hip
  have hcntG : (s_G.BM sb).count = none := by
    cases hcnt : (s_G.BM sb).count with
    | none => rfl
    | some n₂ =>
      exfalso
      obtain ⟨q, i2, ninit, D, D', rest, hq1, hD, hD', hdrop, hdrop'⟩ :=
        exists_init_drop_of_count_some hchain'' h0idx'' p _ s_G hpcfg rfl hcnt
      have hsufq : D.progOf i2 <:+ (Config.run State.initial T).progOf i2 :=
        progOf_suffix_index_le hchain'' i2 h0idx'' (Nat.zero_le q) hD
      have hcmdq := cmd_at_last hsufq hdrop
      have hipq : (⟨i2, ((Config.run State.initial T).progOf i2).length -
          (D.progOf i2).length⟩ : ProgPoint) = ip :=
        unique_init_of_check huniq (mem_progPoints_of_cmdAt T hcmdq) hip hcmdq hcmdip
      have hth2 : i2 = ip.thread := congrArg ProgPoint.thread hipq
      have hidx2 : ((Config.run State.initial T).progOf i2).length -
          (D.progOf i2).length = ip.idx := congrArg ProgPoint.idx hipq
      have hlenD_le : (D.progOf i2).length ≤
          ((Config.run State.initial T).progOf i2).length := suffix_length_le hsufq
      have hlenD : (D.progOf i2).length = rest.length + 1 := by rw [hdrop]; simp
      -- past the drop, `i2`'s program is strictly shorter than the cut allows
      have hsufp : (Config.run s_G T_G).progOf i2 <:+ D'.progOf i2 :=
        progOf_suffix_index_le hchain'' i2 hD' hq1 hpcfg
      have hlenp : (T_G.prog i2).length ≤ rest.length := by
        have := suffix_length_le hsufp
        rw [hdrop'] at this
        exact this
      have hlenG : (T_G.prog i2).length = (T.prog i2).length - fcut T τ ip i2 := by
        rw [hGprog i2]
        simp
      have hTlen : ((Config.run State.initial T).progOf i2).length =
          (T.prog i2).length := rfl
      rw [← hth2] at hfip hipidx
      omega
  -- hence `sb` is fully pristine at the cut (WF's uninitialized clause)
  have hMG : s_G.BM sb = MBarrierState.uninitialized := by
    rcases hsh : s_G.BM sb with ⟨I₀, A₀, c₀, ph₀⟩
    have hc₀ : c₀ = none := by rw [hsh] at hcntG; exact hcntG
    subst hc₀
    obtain ⟨hI₀, hA₀, hph₀⟩ := hwfG.2.2.2.1 sb I₀ A₀ ph₀ hsh
    subst hI₀; subst hA₀; subst hph₀
    rfl
  -- the cut leaves `u`'s control exactly at `u`
  obtain ⟨huid, hulen⟩ := (mem_progPoints_iff T u).mp hu
  have hpredmem : (⟨u.thread, u.idx - 1⟩ : ProgPoint) ∈ T.progPoints :=
    (mem_progPoints_iff T _).mpr
      ⟨huid, by change u.idx - 1 < (T.prog u.thread).length; omega⟩
  have hfcutu : fcut T τ ip u.thread = u.idx := by
    have h1 := fcut_le_of_hb hbu hu
    have h2 : u.idx - 1 < fcut T τ ip u.thread := lt_fcut_of_not_hb hnpred hpredmem
    omega
  -- decode the use command and expose it at the head of `u`'s remaining program
  obtain ⟨cu, hcu, hcuse⟩ : ∃ cu, T.cmdAt u = some cu ∧
      cu.usesMBarrier? = some sb := by
    cases hc : T.cmdAt u with
    | none => rw [hc] at huse; exact absurd huse (by simp)
    | some c => rw [hc] at huse; exact ⟨c, rfl, by simpa using huse⟩
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp
    (show (T.prog u.thread)[u.idx]? = some cu from hcu)
  have hheadu : T_G.prog u.thread = cu :: (T.prog u.thread).drop (u.idx + 1) := by
    rw [hGprog u.thread, hfcutu, List.drop_eq_getElem_cons hlt0, hget0]
  -- under-fullness certificates at the cut, given a barrier is not full
  have hnguard : ∀ nb', ¬ s_G.FullBarrier (.inl nb') →
      s_G.BN nb' = NamedBarrierState.unconfigured ∨
      ∃ I A m, s_G.BN nb' = ⟨I, A, some m⟩ ∧ I.length + A < (m : Nat) := by
    intro nb' hnf
    rcases hb' : s_G.BN nb' with ⟨I', A', c'⟩
    cases c' with
    | none =>
      obtain ⟨hI, hA⟩ := hwfG.2.1 nb' I' A' hb'
      subst hI; subst hA
      exact Or.inl rfl
    | some m' =>
      refine Or.inr ⟨I', A', m', rfl, ?_⟩
      have hle := (hwfG.1 nb' I' A' m' hb').1
      rcases Nat.lt_or_ge (I'.length + A') (m' : Nat) with h | h
      · exact h
      · exfalso
        apply hnf
        change (s_G.BN nb').isFull = true
        rw [hb']
        simp only [NamedBarrierState.isFull, beq_iff_eq]
        omega
  have hmguard : ∀ sb', ¬ s_G.FullBarrier (.inr sb') →
      s_G.BM sb' = MBarrierState.uninitialized ∨
      ∃ I A m ph, s_G.BM sb' = ⟨I, A, some m, ph⟩ ∧ A < (m : Nat) := by
    intro sb' hnf
    rcases hb' : s_G.BM sb' with ⟨I', A', c', ph'⟩
    cases c' with
    | none =>
      obtain ⟨hI, hA, hph⟩ := hwfG.2.2.2.1 sb' I' A' ph' hb'
      subst hI; subst hA; subst hph
      exact Or.inl rfl
    | some m' =>
      refine Or.inr ⟨I', A', m', ph', rfl, ?_⟩
      have hle := (hwfG.2.2.1 sb' I' A' m' ph' hb').1
      rcases Nat.lt_or_ge A' (m' : Nat) with h | h
      · exact h
      · exfalso
        apply hnf
        change (s_G.BM sb').isFull = true
        rw [hb']
        simp only [MBarrierState.isFull, beq_iff_eq]
        omega
  -- drain the (at most one) full barrier: reach a config where the error guards
  -- hold, with `u`'s program, enabledness, and `sb`'s pristine state intact
  obtain ⟨s₂, T₂, hreach₂, hbar₂, hmbar₂, hprog₂, hE₂, hM₂⟩ :
      ∃ (s₂ : State) (T₂ : CTA),
        Relation.ReflTransGen CTAStep (Config.run State.initial T)
          (Config.run s₂ T₂) ∧
        (∀ nb', s₂.BN nb' = NamedBarrierState.unconfigured ∨
          ∃ I A m, s₂.BN nb' = ⟨I, A, some m⟩ ∧ I.length + A < (m : Nat)) ∧
        (∀ sb', s₂.BM sb' = MBarrierState.uninitialized ∨
          ∃ I A m ph, s₂.BM sb' = ⟨I, A, some m, ph⟩ ∧ A < (m : Nat)) ∧
        T₂.prog u.thread = T_G.prog u.thread ∧
        s₂.E u.thread = true ∧ s₂.BM sb = MBarrierState.uninitialized := by
    by_cases hfn : ∃ nb', s_G.FullBarrier (.inl nb')
    · -- a full named barrier: recycle it (empty wake — nothing is blocked)
      obtain ⟨nb, hfnb⟩ := hfn
      have hfnb' : (s_G.BN nb).isFull = true := hfnb
      rcases hbshape : s_G.BN nb with ⟨I, A, c⟩
      cases c with
      | none =>
        rw [hbshape] at hfnb'
        simp [NamedBarrierState.isFull] at hfnb'
      | some m =>
        have hfull : I.length + A = (m : Nat) := by
          rw [hbshape] at hfnb'
          simpa [NamedBarrierState.isFull] using hfnb'
        have hInil : I = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro i hi
          refine hbempty (.inl nb) i ?_
          change i ∈ (s_G.BN nb).synced
          rw [hbshape]
          exact hi
        subst hInil
        have hrec : CTAStep (Config.run s_G T_G)
            (Config.run
              { s_G with E := updateMapOn s_G.E [] true,
                         BN := Function.update s_G.BN nb
                           NamedBarrierState.unconfigured }
              (T_G.wake [])) :=
          CTAStep.recycle hbshape hfull (by simp)
        have hbar' : ∀ nb', Function.update s_G.BN nb NamedBarrierState.unconfigured nb' =
            NamedBarrierState.unconfigured ∨
            ∃ I' A' m', Function.update s_G.BN nb NamedBarrierState.unconfigured nb' =
              ⟨I', A', some m'⟩ ∧ I'.length + A' < (m' : Nat) := by
          intro nb'
          by_cases hbb : nb' = nb
          · subst hbb
            rw [Function.update_self]
            exact Or.inl rfl
          · rw [Function.update_of_ne hbb]
            refine hnguard nb' fun hf => hbb ?_
            have hmem : (Sum.inl nb' : NamedBarrier ⊕ SharedBarrier) ∈
                {b | s_G.FullBarrier b} := hf
            have hmem₀ : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈
                {b | s_G.FullBarrier b} := hfnb
            simpa using hamof hmem hmem₀
        have hmbar' : ∀ sb', s_G.BM sb' = MBarrierState.uninitialized ∨
            ∃ I' A' m' ph', s_G.BM sb' = ⟨I', A', some m', ph'⟩ ∧ A' < (m' : Nat) := by
          intro sb'
          refine hmguard sb' fun hf => ?_
          have hmem : (Sum.inr sb' : NamedBarrier ⊕ SharedBarrier) ∈
              {b | s_G.FullBarrier b} := hf
          have hmem₀ : (Sum.inl nb : NamedBarrier ⊕ SharedBarrier) ∈
              {b | s_G.FullBarrier b} := hfnb
          simpa using hamof hmem hmem₀
        have hEu : updateMapOn s_G.E [] true u.thread = true := by
          rw [updateMapOn_apply, if_neg (by simp)]
          exact hEall u.thread
        have hpu : (T_G.wake []).prog u.thread = T_G.prog u.thread := by
          simp [WeftCommon.CTA.wake]
        exact ⟨_, _, hreachG.tail hrec, hbar', hmbar', hpu, hEu, hMG⟩
    · by_cases hfm : ∃ sb', s_G.FullBarrier (.inr sb')
      · -- a full mbarrier: mb-recycle it (empty wake); it is not `sb` (initialized)
        obtain ⟨sb₀, hfsb⟩ := hfm
        have hfsb' : (s_G.BM sb₀).isFull = true := hfsb
        rcases hbshape : s_G.BM sb₀ with ⟨I, A, c, ph⟩
        cases c with
        | none =>
          rw [hbshape] at hfsb'
          simp [MBarrierState.isFull] at hfsb'
        | some m =>
          have hfull : A = (m : Nat) := by
            rw [hbshape] at hfsb'
            simpa [MBarrierState.isFull] using hfsb'
          have hInil : I = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro i hi
            refine hbempty (.inr sb₀) i ?_
            change i ∈ (s_G.BM sb₀).waiting
            rw [hbshape]
            exact hi
          subst hInil
          have hne : sb ≠ sb₀ := by
            intro h
            rw [← h, hMG] at hbshape
            simp [MBarrierState.uninitialized] at hbshape
          have hrec : CTAStep (Config.run s_G T_G)
              (Config.run
                { s_G with E := updateMapOn s_G.E [] true,
                           BM := Function.update s_G.BM sb₀
                             ⟨[], 0, some m, !ph⟩ }
                (T_G.wake [])) :=
            CTAStep.mb_recycle hbshape hfull (by simp)
          have hbar' : ∀ nb', s_G.BN nb' = NamedBarrierState.unconfigured ∨
              ∃ I' A' m', s_G.BN nb' = ⟨I', A', some m'⟩ ∧
                I'.length + A' < (m' : Nat) := by
            intro nb'
            refine hnguard nb' fun hf => ?_
            have hmem : (Sum.inl nb' : NamedBarrier ⊕ SharedBarrier) ∈
                {b | s_G.FullBarrier b} := hf
            have hmem₀ : (Sum.inr sb₀ : NamedBarrier ⊕ SharedBarrier) ∈
                {b | s_G.FullBarrier b} := hfsb
            simpa using hamof hmem hmem₀
          have hmbar' : ∀ sb', Function.update s_G.BM sb₀ ⟨[], 0, some m, !ph⟩ sb' =
              MBarrierState.uninitialized ∨
              ∃ I' A' m' ph', Function.update s_G.BM sb₀ ⟨[], 0, some m, !ph⟩ sb' =
                ⟨I', A', some m', ph'⟩ ∧ A' < (m' : Nat) := by
            intro sb'
            by_cases hbb : sb' = sb₀
            · subst hbb
              rw [Function.update_self]
              exact Or.inr ⟨[], 0, m, !ph, rfl, m.pos⟩
            · rw [Function.update_of_ne hbb]
              refine hmguard sb' fun hf => hbb ?_
              have hmem : (Sum.inr sb' : NamedBarrier ⊕ SharedBarrier) ∈
                  {b | s_G.FullBarrier b} := hf
              have hmem₀ : (Sum.inr sb₀ : NamedBarrier ⊕ SharedBarrier) ∈
                  {b | s_G.FullBarrier b} := hfsb
              simpa using hamof hmem hmem₀
          have hEu : updateMapOn s_G.E [] true u.thread = true := by
            rw [updateMapOn_apply, if_neg (by simp)]
            exact hEall u.thread
          have hpu : (T_G.wake []).prog u.thread = T_G.prog u.thread := by
            simp [WeftCommon.CTA.wake]
          have hMu : Function.update s_G.BM sb₀ ⟨[], 0, some m, !ph⟩ sb =
              MBarrierState.uninitialized := by
            rw [Function.update_of_ne hne]
            exact hMG
          exact ⟨_, _, hreachG.tail hrec, hbar', hmbar', hpu, hEu, hMu⟩
      · -- nothing is full: the guards already hold at the cut
        push Not at hfn hfm
        exact ⟨s_G, T_G, hreachG,
          fun nb' => hnguard nb' (hfn nb'), fun sb' => hmguard sb' (hfm sb'),
          rfl, hEall u.thread, hMG⟩
  -- fire the error production at `u` and close against well-synchronization
  have hstepu : ∃ P', ThreadStep (.run s₂ u.thread (T₂.prog u.thread))
      (.err u.thread P') := by
    rw [hprog₂, hheadu]
    cases cu with
    | arrive_mb sb' =>
      have hsb' : sb' = sb := by simpa [Cmd.usesMBarrier?] using hcuse
      subst hsb'
      exact ⟨_, ThreadStep.mb_arrive_err hE₂ hM₂⟩
    | wait_mb sb' ph' =>
      have hsb' : sb' = sb := by simpa [Cmd.usesMBarrier?] using hcuse
      subst hsb'
      exact ⟨_, ThreadStep.mb_wait_err hE₂ hM₂⟩
    | read l => simp [Cmd.usesMBarrier?] at hcuse
    | write l => simp [Cmd.usesMBarrier?] at hcuse
    | arrive_nb nb' n' => simp [Cmd.usesMBarrier?] at hcuse
    | sync_nb nb' n' => simp [Cmd.usesMBarrier?] at hcuse
    | init_mb sb' n' => simp [Cmd.usesMBarrier?] at hcuse
  obtain ⟨P', hth⟩ := hstepu
  have herrstep : CTAStep (Config.run s₂ T₂) (Config.err T₂) :=
    CTAStep.error hbar₂ hmbar₂ hth
  obtain ⟨l, hlch, hlhd, hllast⟩ := exists_chain_of_reaches (hreach₂.tail herrstep)
  have htrace : IsCompleteTraceFrom (Config.run State.initial T) l :=
    ⟨⟨hlch, Config.err T₂, hllast, Or.inr (Or.inl ⟨T₂, rfl⟩)⟩, hlhd⟩
  obtain ⟨sd, hd⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
  rw [hllast] at hd
  simp at hd

/-- **Mode 3: a use not forced after its (unique) initialization refutes
well-synchronization.** From `¬ happensBefore (ip, u)`, a reversing schedule
runs the use `u` before the initialization `ip`; but before `ip` — the *only*
`init_mb` of `sb`, by the unique-initialization check — the barrier is pristine
(`uninit_step` chain), and no rule drops an `arrive_mb`/`wait_mb` head from an
uninitialized barrier. -/
theorem init_ordering_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    (huniq : okUniqueInitCheck T τ = true)
    {ip u : ProgPoint} {sb : SharedBarrier} {n : ℕ+}
    (hip : ip ∈ T.progPoints) (hu : u ∈ T.progPoints)
    (hcmdip : T.cmdAt ip = some (.init_mb sb n))
    (huse : (T.cmdAt u).bind Cmd.usesMBarrier? = some sb)
    (hnotmem : (ip, u) ∉ (CheckWellSynchronized T τ).2) : False := by
  -- `ip ≠ u`: an `init_mb` is not a use
  have hne : ip ≠ u := by
    rintro rfl
    rw [hcmdip] at huse
    simp [Cmd.usesMBarrier?] at huse
  have hnothb : ¬ happensBefore T τ ip u := not_happensBefore_of_not_mem hne hnotmem
  obtain ⟨τ', hτ'c, n1, n2, ht1, ht2, hlt⟩ := exists_reversing_trace hτ hws hip hu hnothb
  have hchain' := hτ'c.1.subtrace
  have htr0' : τ'[0]? = some (Config.run State.initial T) := by
    rw [← List.head?_eq_getElem?]
    exact hτ'c.2
  -- before `n1` (the time of the unique init), `sb` is pristine
  have huninit : ∀ j, j < n1 → ∀ sj Tj, τ'[j]? = some (Config.run sj Tj) →
      sj.BM sb = MBarrierState.uninitialized := by
    intro j
    induction j with
    | zero =>
      intro _ sj Tj hj
      rw [htr0'] at hj
      have heq := Option.some.inj hj
      rw [WeftCommon.Config.run.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rfl
    | succ jj ih =>
      intro hjlt sj' Tj' hj'
      have hjj : jj < τ'.length := by
        have := (List.getElem?_eq_some_iff.mp hj').1
        omega
      obtain ⟨Cp, hCp⟩ : ∃ C, τ'[jj]? = some C := ⟨_, List.getElem?_eq_getElem hjj⟩
      have hstep := chain_step hchain' hCp hj'
      obtain ⟨sp, Tp, rfl⟩ := hstep.source_run
      have hup := ih (by omega) sp Tp hCp
      rcases uninit_step hstep rfl rfl hup with h | ⟨i, ninit, rest, hdrop, hdrop'⟩
      · exact h
      · -- the dropped point is the unique init `ip`, executing too early
        exfalso
        have hsuf : (Config.run sp Tp).progOf i <:+
            (Config.run State.initial T).progOf i :=
          progOf_suffix_index_le hchain' i htr0' (Nat.zero_le jj) hCp
        have heqd := List.IsSuffix.eq_drop hsuf
        have hcmdp : T.cmdAt ⟨i, ((Config.run State.initial T).progOf i).length
            - ((Config.run sp Tp).progOf i).length⟩ = some (Cmd.init_mb sb ninit) :=
          cmd_at_last hsuf hdrop
        have hppt := mem_progPoints_of_cmdAt T hcmdp
        have hpeq := unique_init_of_check huniq hppt hip hcmdp hcmdip
        have hproglen : 0 < ((Config.run sp Tp).progOf i).length := by
          rw [hdrop]
          simp
        have hsuflen : ((Config.run sp Tp).progOf i).length
            ≤ ((Config.run State.initial T).progOf i).length := suffix_length_le hsuf
        have htime : IsTimeOf (Config.run State.initial T) τ'
            ⟨i, ((Config.run State.initial T).progOf i).length
              - ((Config.run sp Tp).progOf i).length⟩ (jj + 1) := by
          refine ⟨hτ'c, by simp only; omega, jj, _, _, rfl, hCp, hj', heqd, ?_⟩
          have htl : (Config.run sj' Tj').progOf i = ((Config.run sp Tp).progOf i).tail := by
            rw [hdrop', hdrop]
            rfl
          rw [htl]
          conv_lhs => rw [heqd]
          rw [List.tail_drop]
        rw [hpeq] at htime
        have := IsTimeOf.unique htime ht1
        omega
  -- `u`'s drop step has an initialized source — contradiction
  obtain ⟨cmdu, hcmdu, husecmd⟩ : ∃ cmdu, T.cmdAt u = some cmdu ∧
      cmdu.usesMBarrier? = some sb := by
    cases hc : T.cmdAt u with
    | none => rw [hc] at huse; exact absurd huse (by simp)
    | some cmdu => rw [hc] at huse; exact ⟨cmdu, rfl, huse⟩
  have hn21 : 1 ≤ n2 := by
    obtain ⟨_, _, j, _, _, hj, _⟩ := ht2
    omega
  obtain ⟨Cq, Cq', hCq, hCq', hshape⟩ := time_drop_evidence ht2 hcmdu
  have hstep_q : CTAStep Cq Cq' := by
    refine chain_step hchain' hCq ?_
    rw [show n2 - 1 + 1 = n2 by omega]
    exact hCq'
  cases cmdu with
  | read l => simp [Cmd.usesMBarrier?] at husecmd
  | write l => simp [Cmd.usesMBarrier?] at husecmd
  | arrive_nb nb m => simp [Cmd.usesMBarrier?] at husecmd
  | sync_nb nb m => simp [Cmd.usesMBarrier?] at husecmd
  | init_mb sb' m => simp [Cmd.usesMBarrier?] at husecmd
  | arrive_mb sb' =>
    have hsbeq : sb' = sb := by simpa [Cmd.usesMBarrier?] using husecmd
    subst hsbeq
    obtain ⟨sq, Tq, I, A, nq, ph, hCqeq, hinit⟩ :=
      arrive_mb_drop_initialized hstep_q hshape rfl
    rw [hCqeq] at hCq
    have := huninit (n2 - 1) (by omega) sq Tq hCq
    rw [this] at hinit
    simp [MBarrierState.uninitialized] at hinit
  | wait_mb sb' ph =>
    have hsbeq : sb' = sb := by simpa [Cmd.usesMBarrier?] using husecmd
    subst hsbeq
    obtain ⟨sq, Tq, I, A, nq, ph', hCqeq, hinit⟩ :=
      wait_mb_drop_initialized hstep_q hshape rfl
    rw [hCqeq] at hCq
    have := huninit (n2 - 1) (by omega) sq Tq hCq
    rw [this] at hinit
    simp [MBarrierState.uninitialized] at hinit

/-- **Competing-sync reversal** (mode 1a, `sync_nb` source, `hb(c1, c2)` case).
Run the ideal `G = {η | ¬ hb(c1, η)}` to its cut, where both `c1` and `c2` head
their threads poised at `sync_nb nb`; fire `c2` into `c1`'s still-open round
(generation `≤ k`, or `err` on count mismatch), contradicting `hws`. -/
theorem competing_sync_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 c2 : ProgPoint} {nb : NamedBarrier} {nn mm : ℕ+}
    (hc1 : c1 ∈ T.progPoints) (hc2 : c2 ∈ T.progPoints)
    (hcmd1 : T.cmdAt c1 = some (.sync_nb nb nn)) (hcmd2 : T.cmdAt c2 = some (.sync_nb nb mm))
    {k : ℤ} (hgen1 : pointGen T τ c1 = some k) (hgen2 : pointGen T τ c2 = some (k + 1))
    (hidx : 1 ≤ c2.idx)
    (hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩)
    (hhb : happensBefore T τ c1 c2) : False := by
  -- `c3 = pred(c2)` is a valid program point
  have hc3mem : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T c2).mp hc2
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- the ideal cut splits `c2`'s thread *exactly* at `c2` (`c3 ∈ G`, `c2 ∈ F`)
  have hfcut : fcut T τ c1 c2.thread = c2.idx := by
    have h1 : fcut T τ c1 c2.thread ≤ c2.idx := fcut_le_of_hb hhb hc2
    have h2 := lt_fcut_of_not_hb hnothb3 hc3mem
    simp only at h2
    omega
  -- run `G` to the cut configuration; `c2` heads its thread there
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ :=
    run_ideal (τ := τ) (η₁ := c1) hτ hws
  have hc2head : T_G.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    rw [hcutprog c2.thread, hfcut]
  -- in `τ'`, `c1` executes (recycles `nb`) at some time `n1`
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hc1L : c1.idx < ((Config.run State.initial T).progOf c1.thread).length :=
    ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨n1, hn1⟩ := exists_time_of_ends_done hcomp hdone hc1L
  classical
  have hchain := hcomp.1.subtrace
  -- `c1` executes strictly after the cut (`c1 ∈ F`)
  have hfcutc1 : fcut T τ c1 c1.thread ≤ c1.idx := fcut_le_of_hb Relation.ReflTransGen.refl hc1
  have hpn1 : p < n1 := by
    refine lt_time_of_lt_progOf hn1 hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog c1.thread, List.length_drop]
    have : c1.idx < (T.prog c1.thread).length := hc1L
    omega
  -- `c1` is parked in `nb.synced` at the configuration just before its recycle
  obtain ⟨s1, T1, hC1, hc1synced⟩ :
      ∃ s1 T1, τ'[n1 - 1]? = some (Config.run s1 T1) ∧ c1.thread ∈ (s1.BN nb).synced := by
    have hn1' := hn1
    obtain ⟨_, _, jj, C, C', hjj, hCj, hCj1, _, _⟩ := hn1'
    obtain rfl : jj = n1 - 1 := by omega
    obtain ⟨s1, T1, rfl⟩ : ∃ s T2, C = Config.run s T2 := by
      cases chain_step hchain hCj hCj1 <;> exact ⟨_, _, rfl⟩
    exact ⟨s1, T1, hCj, synced_before_recycle hn1 rfl hcmd1 hCj⟩
  -- so there is a first configuration after the cut with a nonempty blocking list
  have hwit : ∃ s T2, τ'[p + (n1 - 1 - p)]? = some (Config.run s T2) ∧
      ∃ b' t', t' ∈ s.blocked b' :=
    ⟨s1, T1, by rw [show p + (n1 - 1 - p) = n1 - 1 from by omega]; exact hC1,
      .inl nb, c1.thread, hc1synced⟩
  have hPex : ∃ d, ∃ s T2, τ'[p + d]? = some (Config.run s T2) ∧
      ∃ b' t', t' ∈ s.blocked b' :=
    ⟨n1 - 1 - p, hwit⟩
  set d₀ := Nat.find hPex with hd₀
  have hd₀spec := Nat.find_spec hPex
  rw [← hd₀] at hd₀spec
  obtain ⟨sq', Tq', hCq', b', t', hjoin⟩ := hd₀spec
  -- `d₀ > 0` since blocking lists are empty at the cut
  have hd₀pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · exfalso
      rw [h, Nat.add_zero, hcut, Option.some.injEq, WeftCommon.Config.run.injEq] at hCq'
      obtain ⟨rfl, rfl⟩ := hCq'
      exact hsempty b' t' hjoin
    · exact h
  -- at the firing config `q-1 = p + (d₀-1)`, blocking lists are still empty
  have hq1 : ¬ (∃ s T2, τ'[p + (d₀ - 1)]? = some (Config.run s T2) ∧
      ∃ b' t', t' ∈ s.blocked b') :=
    Nat.find_min hPex (by omega)
  -- the firing happens within `c1`'s round: `q = p + d₀ ≤ n1 - 1 < n1`
  have hqn1 : p + d₀ ≤ n1 - 1 := by
    have hle : d₀ ≤ n1 - 1 - p := hd₀ ▸ Nat.find_le hwit
    omega
  have hqlen : p + d₀ < τ'.length := (List.getElem?_eq_some_iff.mp hCq').1
  have hget : ∀ j, j ≤ p + d₀ → ∃ C, τ'[j]? = some C :=
    fun j hj => ⟨_, List.getElem?_eq_getElem (show j < τ'.length by omega)⟩
  -- shared chain invariants
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have hwfAll : ∀ C ∈ τ', C.WF := WF_chain hchain hC₀head WF_initial
  have hei0 : ∀ s, (WeftCommon.Config.state? (Config.run State.initial T)) = some s →
      s.EnabledInv := by
    intro s hs
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    exact State.EnabledInv.initial
  have heiAll : ∀ C ∈ τ', ∀ s, C.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hC₀head hei0
  -- `c2`'s static facts
  have hc2L : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
  have hcmd2_get : (T.prog c2.thread)[c2.idx]'hc2L = Cmd.sync_nb nb mm := by
    have h := hcmd2
    simp only [CTA.cmdAt] at h
    rw [List.getElem?_eq_getElem hc2L, Option.some.injEq] at h
    exact h
  have hdrop2 : (T.prog c2.thread).drop c2.idx
      = Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [List.drop_eq_getElem_cons hc2L, hcmd2_get]
  -- **Program invariance**: while the blocking lists stay empty, `c2` cannot step
  have hinv : ∀ e, e ≤ d₀ - 1 → ∃ s' T', τ'[p + e]? = some (Config.run s' T') ∧
      T'.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    intro e
    induction e with
    | zero => intro _; exact ⟨s_G, T_G, by simpa using hcut, hc2head⟩
    | succ e ih =>
      intro he
      obtain ⟨s', T', hCe, hprog⟩ := ih (by omega)
      obtain ⟨C'', hCe1⟩ := hget (p + (e + 1)) (by omega)
      have hstep : CTAStep (Config.run s' T') C'' :=
        chain_step hchain (show τ'[p + e]? = some _ from hCe)
          (show τ'[(p + e) + 1]? = _ from hCe1)
      obtain ⟨Cnext, hCnext⟩ := hget (p + (e + 1) + 1) (by omega)
      obtain ⟨s'', T'', rfl⟩ : ∃ s2 T2, C'' = Config.run s2 T2 := by
        cases chain_step hchain (show τ'[p + (e + 1)]? = _ from hCe1)
          (show τ'[p + (e + 1) + 1]? = _ from hCnext) <;> exact ⟨_, _, rfl⟩
      refine ⟨s'', T'', hCe1, ?_⟩
      have hsemp_e1 : ∀ bb tt, tt ∉ s''.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e + 1 < d₀ by omega) ⟨s'', T'', hCe1, bb, tt, htt⟩
      have hsemp_e : ∀ bb tt, tt ∉ s'.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e < d₀ by omega) ⟨s', T', hCe, bb, tt, htt⟩
      cases hstep with
      | @interleave _ _ _ i P' hi hbar hmbar hth =>
        by_cases hic2 : i = c2.thread
        · exfalso
          subst hic2
          rw [hprog, hdrop2] at hth
          cases hth with
          | sync_configure he hb =>
            exact hsemp_e1 (.inl nb) c2.thread
              (by simp [State.blocked, Function.update_self])
          | sync_block he hb _ _ =>
            exact hsemp_e1 (.inl nb) c2.thread
              (by simp [State.blocked, Function.update_self])
        · simp only [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hic2)]
          exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inl bb) x
              (by change x ∈ (s'.BN bb).synced; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
      | @mb_recycle _ _ sbb I A n ph hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inr sbb) x
              (by change x ∈ (s'.BM sbb).waiting; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
  -- **Firing config** `q-1`: `c2` poised at head, enabled, with both guards holding
  have hmem : ∀ {j C}, τ'[j]? = some C → C ∈ τ' := fun hj => List.mem_of_getElem? hj
  obtain ⟨sm, Tm, hCq1, hprogm⟩ := hinv (d₀ - 1) (le_refl _)
  have hsemp_q1 : ∀ bb tt, tt ∉ sm.blocked bb := fun bb tt htt =>
    hq1 ⟨sm, Tm, hCq1, bb, tt, htt⟩
  have hheadm : Tm.prog c2.thread
      = Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [hprogm, hdrop2]
  have hc2ids : c2.thread ∈ Tm.ids := by
    by_contra hni
    rw [Tm.nil_outside_ids c2.thread hni] at hheadm
    exact (List.cons_ne_nil _ _) hheadm.symm
  have hc2en : sm.E c2.thread = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    obtain ⟨bb, hbb⟩ := heiAll _ (hmem hCq1) sm rfl c2.thread hne
    exact hsemp_q1 bb c2.thread hbb
  have hCq'' : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run sq' Tq') := by
    rw [show (p + (d₀ - 1)) + 1 = p + d₀ from by omega]
    exact hCq'
  have hstepq : CTAStep (Config.run sm Tm) (Config.run sq' Tq') :=
    chain_step hchain hCq1 hCq''
  obtain ⟨hbarq, hmbarq⟩ := guards_of_joins_blocked hstepq rfl rfl (hsemp_q1 b' t') hjoin
  have hwfq : (Config.WF (Config.run sm Tm)) := hwfAll _ (hmem hCq1)
  -- reachability of the firing config (for `barriersWithin`)
  have hreach : ∀ j, j ≤ p + d₀ → ∀ C, τ'[j]? = some C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C := by
    intro j
    induction j with
    | zero =>
      intro _ C hC
      rw [← List.head?_eq_getElem?, hC₀head, Option.some.injEq] at hC
      subst hC
      exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj C hC
      obtain ⟨Cj, hCj⟩ := hget j (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega) Cj hCj) (chain_step hchain hCj hC)
  have hreachq1 : Relation.ReflTransGen CTAStep (Config.run State.initial T)
      (Config.run sm Tm) :=
    hreach (p + (d₀ - 1)) (by omega) _ hCq1
  -- shared prefix facts: `pre = τ'.take (p+d₀)` ends at the firing config `q-1`
  have hprelen : (τ'.take (p + d₀)).length = p + d₀ := by
    rw [List.length_take]
    omega
  have hpne : τ'.take (p + d₀) ≠ [] := by
    intro h
    rw [h, List.length_nil] at hprelen
    omega
  have hprechain : List.IsChain CTAStep (τ'.take (p + d₀)) := hchain.take _
  have hpre_get : ∀ i, i < p + d₀ → (τ'.take (p + d₀))[i]? = τ'[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hprehead : (τ'.take (p + d₀)).head? = some (Config.run State.initial T) := by
    rw [List.head?_eq_getElem?, hpre_get 0 (by omega), ← List.head?_eq_getElem?]
    exact hC₀head
  have hprelast : (τ'.take (p + d₀)).getLast? = some (Config.run sm Tm) := by
    rw [List.getLast?_eq_getElem?, hprelen, hpre_get (p + d₀ - 1) (by omega),
      show p + d₀ - 1 = p + (d₀ - 1) from by omega]
    exact hCq1
  -- gluing: a complete trace from any successor of the firing config extends `pre`
  have glue : ∀ (σ : List Config) (Cstart : Config), IsCompleteTraceFrom Cstart σ →
      CTAStep (Config.run sm Tm) Cstart →
      IsCompleteTraceFrom (Config.run State.initial T) (τ'.take (p + d₀) ++ σ) := by
    intro σ Cstart hσ hcon
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.IsChain.append hprechain hσ.1.subtrace ?_
      intro x hx y hy
      rw [hprelast, Option.mem_some_iff] at hx
      subst hx
      rw [hσ.2, Option.mem_some_iff] at hy
      subst hy
      exact hcon
    · obtain ⟨Cn, hCnlast, hterm⟩ := hσ.1.ends
      exact ⟨Cn, List.mem_getLast?_append_of_mem_getLast? hCnlast, hterm⟩
    · rw [List.head?_append_of_ne_nil _ hpne]
      exact hprehead
  -- **Fire `c2` early.** It either joins `synced nb` or errors.
  have hc2step : (∃ sN, CTAStep (Config.run sm Tm)
        (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) ∧
        c2.thread ∈ (sN.BN nb).synced) ∨ CTAStep (Config.run sm Tm) (Config.err Tm) := by
    rcases hbarq nb with hbu | ⟨I, A, n', hbcfg, hltn⟩
    · have hcta := CTAStep.interleave hc2ids hbarq hmbarq
        (by rw [hheadm]; exact ThreadStep.sync_configure hc2en hbu)
      exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
    · have hI : I = [] := by
        rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
        · exact h
        · exact absurd (hsemp_q1 (.inl nb) x
            (by change x ∈ (sm.BN nb).synced; rw [hbcfg]; simp)) (by simp)
      subst hI
      have hApos : 0 < A := by simpa using (hwfq.1 nb [] A n' hbcfg).2.2
      by_cases hmmn : n' = mm
      · rw [hmmn] at hbcfg hltn
        have hcta := CTAStep.interleave hc2ids hbarq hmbarq
          (by rw [hheadm]
              exact ThreadStep.sync_block hc2en hbcfg (by simpa using hApos)
                (by simpa using hltn))
        exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
      · exact Or.inr (CTAStep.error hbarq hmbarq
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmmn))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced nb`: complete the trace, then read off a generation clash
    have hbne : sN.BN nb ≠ NamedBarrierState.unconfigured := by
      intro hcon
      rw [hcon] at hsync
      simp [NamedBarrierState.unconfigured] at hsync
    have hbwN : (Config.barriersWithin T.barrierSet (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1))))) :=
      inv_preserved T.barrierSet hcstep (barriersWithin_of_reaches hreachq1)
    obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
    set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
    have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' := glue σ _ hσ hcstep
    obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
    obtain ⟨m2, hm2⟩ := exists_time_of_ends_done htrace hdone'' (η := c2) hc2L
    -- `c2` is parked in `synced nb` at index `p+d₀` of `τ''`, poised at its `sync_nb`
    have hCpark : τ''[p + d₀]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
        ← List.head?_eq_getElem?]
      exact hσ.2
    have hprogpark : (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1))).prog c2.thread
        = ((Config.run State.initial T).progOf c2.thread).drop c2.idx := by
      change (Function.update Tm.prog c2.thread _) c2.thread = _
      rw [Function.update_self]
      exact hdrop2.symm
    have hBI'' : ∀ C ∈ τ'', ∀ s, C.state? = some s → s.BlockInv := by
      refine blockInv_chain htrace.1.subtrace htrace.2 ?_
      intro s hs
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
      subst hs
      exact State.BlockInv.initial
    have hpn : p + d₀ < m2 := by
      refine lt_time_of_lt_progOf hm2 hCpark ?_
      rw [show (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))).progOf c2.thread
          = ((Config.run State.initial T).progOf c2.thread).drop c2.idx from hprogpark,
        List.length_drop]
      have hX : c2.idx < ((Config.run State.initial T).progOf c2.thread).length := hc2L
      omega
    -- parked ⟹ `recycleCount` is unchanged between parking and recycle
    have heq3 : recycleCount (.inl nb) τ'' (m2 - 1) = recycleCount (.inl nb) τ'' (p + d₀) :=
      parked_blocked_recycleCount hBI'' rfl hm2 hCpark hsync hprogpark hpn
    -- `τ''` agrees with `τ'` on configs `0 … p+d₀-1`
    have hshare : ∀ j, j < p + d₀ → τ''[j]? = τ'[j]? := by
      intro j hj
      rw [hτ''def, List.getElem?_append_left (by rw [hprelen]; exact hj)]
      exact hpre_get j hj
    -- the firing step itself does not recycle `nb` (it joins `synced nb`)
    have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
      rw [hshare (p + (d₀ - 1)) (by omega)]
      exact hCq1
    have hCpark'' : τ''[p + (d₀ - 1) + 1]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]
      exact hCpark
    have hstepfalse : stepRecyclesBarrier (.inl nb) (Config.run sm Tm) (Config.run sN
        (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) = false := by
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hbne]
    have heq4 : recycleCount (.inl nb) τ'' (p + d₀)
        = recycleCount (.inl nb) τ' (p + (d₀ - 1)) := by
      have hsucc : recycleCount (.inl nb) τ'' (p + d₀)
          = recycleCount (.inl nb) τ'' (p + (d₀ - 1)) := by
        rw [show p + d₀ = (p + (d₀ - 1)) + 1 from by omega]
        exact recycleCount_succ_of_not_recycle _ hCq1'' hCpark'' hstepfalse
      rw [hsucc]
      exact recycleCount_prefix_eq _ (p + (d₀ - 1)) (fun j hj => hshare j (by omega))
    -- transfer generations across traces via well-synchronization
    obtain ⟨sτ, hdoneτ⟩ := hτ.2
    obtain ⟨m1τ, hm1τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c1) hc1L
    obtain ⟨m2τ, hm2τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c2) hc2L
    have gen_in : ∀ (σ' : List Config) (η : ProgPoint) (cmd : Cmd)
        (bb : NamedBarrier ⊕ SharedBarrier),
        IsCompleteTraceFrom (Config.run State.initial T) σ' →
        T.cmdAt η = some cmd → cmd.barrier? = some bb →
        (∃ mτ, IsTimeOf (Config.run State.initial T) τ η mτ) →
        IsGenOf (Config.run State.initial T) σ' η (pointGen T τ η) := by
      intro σ' η cmd bb hσ' hcmdh hbarh hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
        isGenOf_pointGen hcmdh hbarh hmτ
      obtain ⟨g, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η
        ⟨bb, by change (T.cmdAt η).bind Cmd.barrier? = some bb; rw [hcmdh]; exact hbarh⟩
      rwa [IsGenOf.unique hgτ hgenτ] at hgσ
    have hgτ'1 : IsGenOf (Config.run State.initial T) τ' c1 (some k) := by
      have h := gen_in τ' c1 _ (.inl nb) hcomp hcmd1 rfl ⟨m1τ, hm1τ⟩
      rwa [hgen1] at h
    have hgτ''2 : IsGenOf (Config.run State.initial T) τ'' c2 (some (k + 1)) := by
      have h := gen_in τ'' c2 _ (.inl nb) htrace hcmd2 rfl ⟨m2τ, hm2τ⟩
      rwa [hgen2] at h
    have hv1 : k = (recycleCount (.inl nb) τ' (n1 - 1) : ℤ) := by
      have h := isGenOf_genValue hgτ'1 hcmd1 rfl hn1
      rwa [genValue_of_isRegistrant rfl] at h
    have hv2 : k + 1 = (recycleCount (.inl nb) τ'' (m2 - 1) : ℤ) := by
      have h := isGenOf_genValue hgτ''2 hcmd2 rfl hm2
      rwa [genValue_of_isRegistrant rfl] at h
    have hmono : recycleCount (.inl nb) τ' (p + (d₀ - 1))
        ≤ recycleCount (.inl nb) τ' (n1 - 1) :=
      recycleCount_mono _ τ' (show p + (d₀ - 1) ≤ n1 - 1 from by omega)
    omega
  · -- count-mismatch: the spliced trace ends in `err`, impossible for a WS CTA
    have herrtrace : IsCompleteTraceFrom (Config.err Tm) [Config.err Tm] :=
      ⟨⟨List.isChain_singleton _, Config.err Tm, by simp, Or.inr (Or.inl ⟨Tm, rfl⟩)⟩, by simp⟩
    obtain ⟨sd2, hdone2⟩ :=
      CTA.WellSynchronized.completeTrace_ends_done hws (glue _ _ herrtrace herr)
    have hgl : (τ'.take (p + d₀) ++ [Config.err Tm]).getLast? = some (Config.err Tm) := by
      simp
    rw [hgl] at hdone2
    simp at hdone2

/-- **Competing arrive/sync reversal** (mode 1a, `arrive_nb` source, `hb(c1, c2)`
case) — the operational analog of `competing_sync_false` for an `arrive_nb`
source, which parks in `nb.arrived` rather than `nb.synced`. -/
theorem competing_arrive_sync_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c1 c2 : ProgPoint} {nb : NamedBarrier} {nn mm : ℕ+}
    (hc1 : c1 ∈ T.progPoints) (hc2 : c2 ∈ T.progPoints)
    (hcmd1 : T.cmdAt c1 = some (.arrive_nb nb nn)) (hcmd2 : T.cmdAt c2 = some (.sync_nb nb mm))
    {k : ℤ} (hgen1 : pointGen T τ c1 = some k) (hgen2 : pointGen T τ c2 = some (k + 1))
    (hidx : 1 ≤ c2.idx)
    (hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩)
    (hhb : happensBefore T τ c1 c2) : False := by
  -- `c3 = pred(c2)` is a valid program point
  have hc3mem : (⟨c2.thread, c2.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T c2).mp hc2
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- the ideal cut splits `c2`'s thread *exactly* at `c2` (`c3 ∈ G`, `c2 ∈ F`)
  have hfcut : fcut T τ c1 c2.thread = c2.idx := by
    have h1 : fcut T τ c1 c2.thread ≤ c2.idx := fcut_le_of_hb hhb hc2
    have h2 := lt_fcut_of_not_hb hnothb3 hc3mem
    simp only at h2
    omega
  -- run `G` to the cut configuration; `c2` heads its thread there
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ :=
    run_ideal (τ := τ) (η₁ := c1) hτ hws
  have hc2head : T_G.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    rw [hcutprog c2.thread, hfcut]
  -- in `τ'`, `c1` executes (an `interleave` arrive) at some time `n1`
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hc1L : c1.idx < ((Config.run State.initial T).progOf c1.thread).length :=
    ((mem_progPoints_iff T c1).mp hc1).2
  obtain ⟨n1, hn1⟩ := exists_time_of_ends_done hcomp hdone hc1L
  classical
  have hchain := hcomp.1.subtrace
  have hfcutc1 : fcut T τ c1 c1.thread ≤ c1.idx := fcut_le_of_hb Relation.ReflTransGen.refl hc1
  have hpn1 : p < n1 := by
    refine lt_time_of_lt_progOf hn1 hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog c1.thread, List.length_drop]
    have : c1.idx < (T.prog c1.thread).length := hc1L
    omega
  -- `c1`'s arrive step `n1-1 → n1` advances `c1`; the config at `n1` is a `run`.
  obtain ⟨hcomp', hidxL1, j1, C1a, C1a', hj1eq, hC1a, hC1a', hC1aprog, hC1a'prog⟩ := id hn1
  have hC1aget : τ'[n1]? = some C1a' := by
    rw [hj1eq]
    exact hC1a'
  have hC1astep : CTAStep C1a C1a' := chain_step hchain hC1a hC1a'
  obtain ⟨s1n, T1n, rfl⟩ : ∃ s2 T2, C1a' = Config.run s2 T2 := by
    have hc1ne : ((Config.run State.initial T).progOf c1.thread).drop c1.idx ≠ [] := by
      intro h
      have hl := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at hl
      simp only [WeftCommon.Config.progOf] at hc1L
      omega
    cases hC1astep with
    | @interleave _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @recycle _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @mb_recycle _ _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @done sa Ta hdone2 hnofull hmbnofull =>
      exfalso
      have hc1prog : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop c1.idx := hC1aprog
      have hc1ids : c1.thread ∈ Ta.ids := by
        by_contra hni
        rw [Ta.nil_outside_ids c1.thread hni] at hc1prog
        exact hc1ne hc1prog.symm
      exact hc1ne (hc1prog ▸ hdone2 c1.thread hc1ids)
    | @error sa Ta i P' _ _ hth =>
      exfalso
      have h1 : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop c1.idx := hC1aprog
      have h2 : Ta.prog c1.thread
          = ((Config.run State.initial T).progOf c1.thread).drop (c1.idx + 1) := hC1a'prog
      rw [h1] at h2
      have hl := congrArg List.length h2
      simp only [List.length_drop] at hl
      simp only [WeftCommon.Config.progOf] at hc1L
      omega
  -- **Search for the firing config**: the first config after the cut whose successor
  -- joins a blocking list, *or* is `c1`'s arrive at `n1` — `c1`'s arrive witnesses it.
  have hPex : ∃ d, ∃ s T2, τ'[p + d]? = some (Config.run s T2) ∧
      ((∃ b' t', t' ∈ s.blocked b') ∨ p + d = n1) :=
    ⟨n1 - p, s1n, T1n,
      by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget, Or.inr (by omega)⟩
  set d₀ := Nat.find hPex with hd₀
  have hd₀spec := Nat.find_spec hPex
  rw [← hd₀] at hd₀spec
  obtain ⟨sq', Tq', hCq', hdisj⟩ := hd₀spec
  -- `d₀ > 0` since blocking lists are empty at the cut and `p ≠ n1`
  have hd₀pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · exfalso
      rw [h, Nat.add_zero, hcut, Option.some.injEq, WeftCommon.Config.run.injEq] at hCq'
      obtain ⟨rfl, rfl⟩ := hCq'
      rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
      · exact hsempty b' t' hjoin
      · omega
    · exact h
  -- at the firing config `q-1 = p + (d₀-1)`, blocking lists are empty, `p+(d₀-1) ≠ n1`
  have hq1 : ¬ (∃ s T2, τ'[p + (d₀ - 1)]? = some (Config.run s T2) ∧
      ((∃ b' t', t' ∈ s.blocked b') ∨ p + (d₀ - 1) = n1)) := Nat.find_min hPex (by omega)
  -- the firing happens at or before `c1`'s arrive: `q = p + d₀ ≤ n1`
  have hqn1 : p + d₀ ≤ n1 := by
    have hle : d₀ ≤ n1 - p := hd₀ ▸ Nat.find_le
      ⟨s1n, T1n, by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget,
        Or.inr (by omega)⟩
    omega
  have hqlen : p + d₀ < τ'.length := (List.getElem?_eq_some_iff.mp hCq').1
  have hget : ∀ j, j ≤ p + d₀ → ∃ C, τ'[j]? = some C :=
    fun j hj => ⟨_, List.getElem?_eq_getElem (show j < τ'.length by omega)⟩
  -- shared chain invariants
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have hwfAll : ∀ C ∈ τ', C.WF := WF_chain hchain hC₀head WF_initial
  have hei0 : ∀ s, (WeftCommon.Config.state? (Config.run State.initial T)) = some s →
      s.EnabledInv := by
    intro s hs
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    exact State.EnabledInv.initial
  have heiAll : ∀ C ∈ τ', ∀ s, C.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hC₀head hei0
  -- `c2`'s static facts
  have hc2L : c2.idx < (T.prog c2.thread).length := ((mem_progPoints_iff T c2).mp hc2).2
  have hcmd2_get : (T.prog c2.thread)[c2.idx]'hc2L = Cmd.sync_nb nb mm := by
    have h := hcmd2
    simp only [CTA.cmdAt] at h
    rw [List.getElem?_eq_getElem hc2L, Option.some.injEq] at h
    exact h
  have hdrop2 : (T.prog c2.thread).drop c2.idx
      = Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [List.drop_eq_getElem_cons hc2L, hcmd2_get]
  -- **Program invariance** on `[p, q-1]`: `c2` stays poised at its head
  have hinv : ∀ e, e ≤ d₀ - 1 → ∃ s' T', τ'[p + e]? = some (Config.run s' T') ∧
      T'.prog c2.thread = (T.prog c2.thread).drop c2.idx := by
    intro e
    induction e with
    | zero => intro _; exact ⟨s_G, T_G, by simpa using hcut, hc2head⟩
    | succ e ih =>
      intro he
      obtain ⟨s', T', hCe, hprog⟩ := ih (by omega)
      obtain ⟨C'', hCe1⟩ := hget (p + (e + 1)) (by omega)
      have hstep : CTAStep (Config.run s' T') C'' :=
        chain_step hchain (show τ'[p + e]? = some _ from hCe)
          (show τ'[(p + e) + 1]? = _ from hCe1)
      obtain ⟨Cnext, hCnext⟩ := hget (p + (e + 1) + 1) (by omega)
      obtain ⟨s'', T'', rfl⟩ : ∃ s2 T2, C'' = Config.run s2 T2 := by
        cases chain_step hchain (show τ'[p + (e + 1)]? = _ from hCe1)
          (show τ'[p + (e + 1) + 1]? = _ from hCnext) <;> exact ⟨_, _, rfl⟩
      refine ⟨s'', T'', hCe1, ?_⟩
      have hsemp_e1 : ∀ bb tt, tt ∉ s''.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e + 1 < d₀ by omega)
          ⟨s'', T'', hCe1, Or.inl ⟨bb, tt, htt⟩⟩
      have hsemp_e : ∀ bb tt, tt ∉ s'.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e < d₀ by omega) ⟨s', T', hCe, Or.inl ⟨bb, tt, htt⟩⟩
      cases hstep with
      | @interleave _ _ _ i P' hi hbar hmbar hth =>
        by_cases hic2 : i = c2.thread
        · exfalso
          subst hic2
          rw [hprog, hdrop2] at hth
          cases hth with
          | sync_configure he hb =>
            exact hsemp_e1 (.inl nb) c2.thread
              (by simp [State.blocked, Function.update_self])
          | sync_block he hb _ _ =>
            exact hsemp_e1 (.inl nb) c2.thread
              (by simp [State.blocked, Function.update_self])
        · simp only [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hic2)]
          exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inl bb) x
              (by change x ∈ (s'.BN bb).synced; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
      | @mb_recycle _ _ sbb I A n ph hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inr sbb) x
              (by change x ∈ (s'.BM sbb).waiting; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
  -- **Firing config** `q-1`: `c2` poised at head, enabled, with both guards holding
  have hmem : ∀ {j C}, τ'[j]? = some C → C ∈ τ' := fun hj => List.mem_of_getElem? hj
  obtain ⟨sm, Tm, hCq1, hprogm⟩ := hinv (d₀ - 1) (le_refl _)
  have hsemp_q1 : ∀ bb tt, tt ∉ sm.blocked bb := fun bb tt htt =>
    hq1 ⟨sm, Tm, hCq1, Or.inl ⟨bb, tt, htt⟩⟩
  have hheadm : Tm.prog c2.thread
      = Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1) := by
    rw [hprogm, hdrop2]
  have hc2ids : c2.thread ∈ Tm.ids := by
    by_contra hni
    rw [Tm.nil_outside_ids c2.thread hni] at hheadm
    exact (List.cons_ne_nil _ _) hheadm.symm
  have hc2en : sm.E c2.thread = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    obtain ⟨bb, hbb⟩ := heiAll _ (hmem hCq1) sm rfl c2.thread hne
    exact hsemp_q1 bb c2.thread hbb
  have hCq'' : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run sq' Tq') := by
    rw [show (p + (d₀ - 1)) + 1 = p + d₀ from by omega]
    exact hCq'
  have hstepq : CTAStep (Config.run sm Tm) (Config.run sq' Tq') :=
    chain_step hchain hCq1 hCq''
  -- both guards hold at `q-1`: the step out of it is an `interleave` (a join, or
  -- `c1`'s own arrive); a recycle would wake nobody yet `c1`'s program advances
  have hguards : (∀ nb'', sm.BN nb'' = NamedBarrierState.unconfigured ∨
      ∃ I A n, sm.BN nb'' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat)) ∧
      (∀ sb'', sm.BM sb'' = MBarrierState.uninitialized ∨
      ∃ I A n ph, sm.BM sb'' = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat)) := by
    rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
    · exact guards_of_joins_blocked hstepq rfl rfl (hsemp_q1 b' t') hjoin
    · have hj1 : j1 = p + (d₀ - 1) := by omega
      have e1 : C1a = Config.run sm Tm := by
        rw [hj1, hCq1] at hC1a
        exact (Option.some.injEq _ _).mp hC1a.symm
      rw [e1] at hC1aprog
      simp only [WeftCommon.Config.progOf] at hC1aprog
      have hadv : ∀ (Twake : CTA), T1n = Twake → Twake.prog c1.thread = Tm.prog c1.thread →
          False := by
        intro Twake hTeq hsame
        have h2 := hC1a'prog
        simp only [WeftCommon.Config.progOf] at h2
        rw [hTeq, hsame, hC1aprog] at h2
        have hl := congrArg List.length h2
        simp only [List.length_drop] at hl
        simp only [WeftCommon.Config.progOf] at hc1L
        omega
      cases hstepq with
      | @interleave _ _ _ i P' hi hbar hmbar hth => exact ⟨hbar, hmbar⟩
      | @recycle _ _ bb I A n hb hfull hpark =>
        exfalso
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_q1 (.inl bb) x
              (by change x ∈ (sm.BN bb).synced; rw [hb]; simp)) (by simp)
        subst hI
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]
            rw [show j1 + 1 = n1 from by omega]
            exact hC1aget
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [WeftCommon.Config.run.injEq] at h
          exact h.2.symm
        exact hadv (Tm.wake []) hTeq (by simp [WeftCommon.CTA.wake])
      | @mb_recycle _ _ sbb I A n ph hb hfull hpark =>
        exfalso
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_q1 (.inr sbb) x
              (by change x ∈ (sm.BM sbb).waiting; rw [hb]; simp)) (by simp)
        subst hI
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]
            rw [show j1 + 1 = n1 from by omega]
            exact hC1aget
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [WeftCommon.Config.run.injEq] at h
          exact h.2.symm
        exact hadv (Tm.wake []) hTeq (by simp [WeftCommon.CTA.wake])
  obtain ⟨hbarq, hmbarq⟩ := hguards
  have hwfq : (Config.WF (Config.run sm Tm)) := hwfAll _ (hmem hCq1)
  -- reachability of the firing config (for `barriersWithin`)
  have hreach : ∀ j, j ≤ p + d₀ → ∀ C, τ'[j]? = some C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C := by
    intro j
    induction j with
    | zero =>
      intro _ C hC
      rw [← List.head?_eq_getElem?, hC₀head, Option.some.injEq] at hC
      subst hC
      exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj C hC
      obtain ⟨Cj, hCj⟩ := hget j (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega) Cj hCj) (chain_step hchain hCj hC)
  have hreachq1 : Relation.ReflTransGen CTAStep (Config.run State.initial T)
      (Config.run sm Tm) :=
    hreach (p + (d₀ - 1)) (by omega) _ hCq1
  -- shared prefix facts
  have hprelen : (τ'.take (p + d₀)).length = p + d₀ := by
    rw [List.length_take]
    omega
  have hpne : τ'.take (p + d₀) ≠ [] := by
    intro h
    rw [h, List.length_nil] at hprelen
    omega
  have hprechain : List.IsChain CTAStep (τ'.take (p + d₀)) := hchain.take _
  have hpre_get : ∀ i, i < p + d₀ → (τ'.take (p + d₀))[i]? = τ'[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hprehead : (τ'.take (p + d₀)).head? = some (Config.run State.initial T) := by
    rw [List.head?_eq_getElem?, hpre_get 0 (by omega), ← List.head?_eq_getElem?]
    exact hC₀head
  have hprelast : (τ'.take (p + d₀)).getLast? = some (Config.run sm Tm) := by
    rw [List.getLast?_eq_getElem?, hprelen, hpre_get (p + d₀ - 1) (by omega),
      show p + d₀ - 1 = p + (d₀ - 1) from by omega]
    exact hCq1
  have glue : ∀ (σ : List Config) (Cstart : Config), IsCompleteTraceFrom Cstart σ →
      CTAStep (Config.run sm Tm) Cstart →
      IsCompleteTraceFrom (Config.run State.initial T) (τ'.take (p + d₀) ++ σ) := by
    intro σ Cstart hσ hcon
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.IsChain.append hprechain hσ.1.subtrace ?_
      intro x hx y hy
      rw [hprelast, Option.mem_some_iff] at hx
      subst hx
      rw [hσ.2, Option.mem_some_iff] at hy
      subst hy
      exact hcon
    · obtain ⟨Cn, hCnlast, hterm⟩ := hσ.1.ends
      exact ⟨Cn, List.mem_getLast?_append_of_mem_getLast? hCnlast, hterm⟩
    · rw [List.head?_append_of_ne_nil _ hpne]
      exact hprehead
  -- **Fire `c2` early.** It either joins `synced nb` or errors.
  have hc2step : (∃ sN, CTAStep (Config.run sm Tm)
        (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) ∧
        c2.thread ∈ (sN.BN nb).synced) ∨ CTAStep (Config.run sm Tm) (Config.err Tm) := by
    rcases hbarq nb with hbu | ⟨I, A, n', hbcfg, hltn⟩
    · have hcta := CTAStep.interleave hc2ids hbarq hmbarq
        (by rw [hheadm]; exact ThreadStep.sync_configure hc2en hbu)
      exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
    · have hI : I = [] := by
        rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
        · exact h
        · exact absurd (hsemp_q1 (.inl nb) x
            (by change x ∈ (sm.BN nb).synced; rw [hbcfg]; simp)) (by simp)
      subst hI
      have hApos : 0 < A := by simpa using (hwfq.1 nb [] A n' hbcfg).2.2
      by_cases hmmn : n' = mm
      · rw [hmmn] at hbcfg hltn
        have hcta := CTAStep.interleave hc2ids hbarq hmbarq
          (by rw [hheadm]
              exact ThreadStep.sync_block hc2en hbcfg (by simpa using hApos)
                (by simpa using hltn))
        exact Or.inl ⟨_, hcta, by simp [Function.update_self]⟩
      · exact Or.inr (CTAStep.error hbarq hmbarq
          (by rw [hheadm]; exact ThreadStep.sync_err_count hc2en hbcfg hmmn))
  rcases hc2step with ⟨sN, hcstep, hsync⟩ | herr
  · -- `c2` joins `synced nb`: complete the trace, then read off a generation clash
    have hbne : sN.BN nb ≠ NamedBarrierState.unconfigured := by
      intro hcon
      rw [hcon] at hsync
      simp [NamedBarrierState.unconfigured] at hsync
    have hbwN : (Config.barriersWithin T.barrierSet (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1))))) :=
      inv_preserved T.barrierSet hcstep (barriersWithin_of_reaches hreachq1)
    obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
    set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
    have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' := glue σ _ hσ hcstep
    obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
    obtain ⟨m2, hm2⟩ := exists_time_of_ends_done htrace hdone'' (η := c2) hc2L
    have hCpark : τ''[p + d₀]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
        ← List.head?_eq_getElem?]
      exact hσ.2
    have hprogpark : (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1))).prog c2.thread
        = ((Config.run State.initial T).progOf c2.thread).drop c2.idx := by
      change (Function.update Tm.prog c2.thread _) c2.thread = _
      rw [Function.update_self]
      exact hdrop2.symm
    have hBI'' : ∀ C ∈ τ'', ∀ s, C.state? = some s → s.BlockInv := by
      refine blockInv_chain htrace.1.subtrace htrace.2 ?_
      intro s hs
      simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
      subst hs
      exact State.BlockInv.initial
    have hpn : p + d₀ < m2 := by
      refine lt_time_of_lt_progOf hm2 hCpark ?_
      rw [show (Config.run sN (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))).progOf c2.thread
          = ((Config.run State.initial T).progOf c2.thread).drop c2.idx from hprogpark,
        List.length_drop]
      have hX : c2.idx < ((Config.run State.initial T).progOf c2.thread).length := hc2L
      omega
    have heq3 : recycleCount (.inl nb) τ'' (m2 - 1) = recycleCount (.inl nb) τ'' (p + d₀) :=
      parked_blocked_recycleCount hBI'' rfl hm2 hCpark hsync hprogpark hpn
    have hshare : ∀ j, j < p + d₀ → τ''[j]? = τ'[j]? := by
      intro j hj
      rw [hτ''def, List.getElem?_append_left (by rw [hprelen]; exact hj)]
      exact hpre_get j hj
    have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
      rw [hshare (p + (d₀ - 1)) (by omega)]
      exact hCq1
    have hCpark'' : τ''[p + (d₀ - 1) + 1]? = some (Config.run sN (Tm.set c2.thread hc2ids
        (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) := by
      rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]
      exact hCpark
    have hstepfalse : stepRecyclesBarrier (.inl nb) (Config.run sm Tm) (Config.run sN
        (Tm.set c2.thread hc2ids
          (Cmd.sync_nb nb mm :: (T.prog c2.thread).drop (c2.idx + 1)))) = false := by
      simp [stepRecyclesBarrier, WeftCommon.Config.state?, hbne]
    have heq4 : recycleCount (.inl nb) τ'' (p + d₀)
        = recycleCount (.inl nb) τ' (p + (d₀ - 1)) := by
      have hsucc : recycleCount (.inl nb) τ'' (p + d₀)
          = recycleCount (.inl nb) τ'' (p + (d₀ - 1)) := by
        rw [show p + d₀ = (p + (d₀ - 1)) + 1 from by omega]
        exact recycleCount_succ_of_not_recycle _ hCq1'' hCpark'' hstepfalse
      rw [hsucc]
      exact recycleCount_prefix_eq _ (p + (d₀ - 1)) (fun j hj => hshare j (by omega))
    obtain ⟨sτ, hdoneτ⟩ := hτ.2
    obtain ⟨m1τ, hm1τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c1) hc1L
    obtain ⟨m2τ, hm2τ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c2) hc2L
    have gen_in : ∀ (σ' : List Config) (η : ProgPoint) (cmd : Cmd)
        (bb : NamedBarrier ⊕ SharedBarrier),
        IsCompleteTraceFrom (Config.run State.initial T) σ' →
        T.cmdAt η = some cmd → cmd.barrier? = some bb →
        (∃ mτ, IsTimeOf (Config.run State.initial T) τ η mτ) →
        IsGenOf (Config.run State.initial T) σ' η (pointGen T τ η) := by
      intro σ' η cmd bb hσ' hcmdh hbarh hex
      obtain ⟨mτ, hmτ⟩ := hex
      have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
        isGenOf_pointGen hcmdh hbarh hmτ
      obtain ⟨g, hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η
        ⟨bb, by change (T.cmdAt η).bind Cmd.barrier? = some bb; rw [hcmdh]; exact hbarh⟩
      rwa [IsGenOf.unique hgτ hgenτ] at hgσ
    have hgτ'1 : IsGenOf (Config.run State.initial T) τ' c1 (some k) := by
      have h := gen_in τ' c1 _ (.inl nb) hcomp hcmd1 rfl ⟨m1τ, hm1τ⟩
      rwa [hgen1] at h
    have hgτ''2 : IsGenOf (Config.run State.initial T) τ'' c2 (some (k + 1)) := by
      have h := gen_in τ'' c2 _ (.inl nb) htrace hcmd2 rfl ⟨m2τ, hm2τ⟩
      rwa [hgen2] at h
    have hv1 : k = (recycleCount (.inl nb) τ' (n1 - 1) : ℤ) := by
      have h := isGenOf_genValue hgτ'1 hcmd1 rfl hn1
      rwa [genValue_of_isRegistrant rfl] at h
    have hv2 : k + 1 = (recycleCount (.inl nb) τ'' (m2 - 1) : ℤ) := by
      have h := isGenOf_genValue hgτ''2 hcmd2 rfl hm2
      rwa [genValue_of_isRegistrant rfl] at h
    have hmono : recycleCount (.inl nb) τ' (p + (d₀ - 1))
        ≤ recycleCount (.inl nb) τ' (n1 - 1) :=
      recycleCount_mono _ τ' (show p + (d₀ - 1) ≤ n1 - 1 from by omega)
    omega
  · have herrtrace : IsCompleteTraceFrom (Config.err Tm) [Config.err Tm] :=
      ⟨⟨List.isChain_singleton _, Config.err Tm, by simp, Or.inr (Or.inl ⟨Tm, rfl⟩)⟩, by simp⟩
    obtain ⟨sd2, hdone2⟩ :=
      CTA.WellSynchronized.completeTrace_ends_done hws (glue _ _ herrtrace herr)
    have hgl : (τ'.take (p + d₀) ++ [Config.err Tm]).getLast? = some (Config.err Tm) := by
      simp
    rw [hgl] at hdone2
    simp at hdone2

/-- **Competing arrive/wait reversal** (mode 2b, `hb(c, w)` case). Run the ideal
`G = {η | ¬ hb(c, η)}` to its cut, where `w` heads its thread (`c3 ∈ G`,
`w ∈ F`) and the recycle count of `sb` is at most `g − 1` (`c ∈ F` is a missing
round-`(g−1)` arrival); fire `w`: it passes observing `≤ g − 2`, errs, or parks
and wakes at recycle `≤ g`, observing `≤ g − 1` — never `g`. -/
theorem competing_arrive_wait_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    {c w : ProgPoint} {sb : SharedBarrier} {ph : Phase} {g : ℤ}
    (hc : c ∈ T.progPoints) (hw : w ∈ T.progPoints)
    (hcmdc : T.cmdAt c = some (.arrive_mb sb)) (hcmdw : T.cmdAt w = some (.wait_mb sb ph))
    (hgenc : pointGen T τ c = some (g - 1)) (hgenw : pointGen T τ w = some g)
    (hidx : 1 ≤ w.idx)
    (hnothb3 : ¬ happensBefore T τ c ⟨w.thread, w.idx - 1⟩)
    (hhb : happensBefore T τ c w) : False := by
  -- `c3 = pred(w)` is a valid program point
  have hc3mem : (⟨w.thread, w.idx - 1⟩ : ProgPoint) ∈ T.progPoints := by
    obtain ⟨hth, hlt⟩ := (mem_progPoints_iff T w).mp hw
    exact (mem_progPoints_iff T _).mpr ⟨hth, by simp only; omega⟩
  -- the ideal cut splits `w`'s thread *exactly* at `w`
  have hfcut : fcut T τ c w.thread = w.idx := by
    have h1 : fcut T τ c w.thread ≤ w.idx := fcut_le_of_hb hhb hw
    have h2 := lt_fcut_of_not_hb hnothb3 hc3mem
    simp only at h2
    omega
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ :=
    run_ideal (τ := τ) (η₁ := c) hτ hws
  have hwhead : T_G.prog w.thread = (T.prog w.thread).drop w.idx := by
    rw [hcutprog w.thread, hfcut]
  -- in `τ'`, `c` executes (an `interleave` arrive) at some time `n1`
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hcL : c.idx < ((Config.run State.initial T).progOf c.thread).length :=
    ((mem_progPoints_iff T c).mp hc).2
  have hwL : w.idx < ((Config.run State.initial T).progOf w.thread).length :=
    ((mem_progPoints_iff T w).mp hw).2
  obtain ⟨n1, hn1⟩ := exists_time_of_ends_done hcomp hdone hcL
  classical
  have hchain := hcomp.1.subtrace
  have hfcutc : fcut T τ c c.thread ≤ c.idx := fcut_le_of_hb Relation.ReflTransGen.refl hc
  have hpn1 : p < n1 := by
    refine lt_time_of_lt_progOf hn1 hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog c.thread, List.length_drop]
    have : c.idx < (T.prog c.thread).length := hcL
    omega
  -- generation transfer and the recycle-count bound at `c`'s execution
  obtain ⟨sτ, hdoneτ⟩ := hτ.2
  obtain ⟨mcτ, hmcτ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := c) hcL
  obtain ⟨mwτ, hmwτ⟩ := exists_time_of_ends_done hτ.1 hdoneτ (η := w) hwL
  have gen_in : ∀ (σ' : List Config) (η : ProgPoint) (cmd : Cmd)
      (bb : NamedBarrier ⊕ SharedBarrier),
      IsCompleteTraceFrom (Config.run State.initial T) σ' →
      T.cmdAt η = some cmd → cmd.barrier? = some bb →
      (∃ mτ, IsTimeOf (Config.run State.initial T) τ η mτ) →
      IsGenOf (Config.run State.initial T) σ' η (pointGen T τ η) := by
    intro σ' η cmd bb hσ' hcmdh hbarh hex
    obtain ⟨mτ, hmτ⟩ := hex
    have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
      isGenOf_pointGen hcmdh hbarh hmτ
    obtain ⟨g', hgτ, hgσ⟩ := hws.2 τ σ' hτ.1 hσ' η
      ⟨bb, by change (T.cmdAt η).bind Cmd.barrier? = some bb; rw [hcmdh]; exact hbarh⟩
    rwa [IsGenOf.unique hgτ hgenτ] at hgσ
  have hgτ'c : IsGenOf (Config.run State.initial T) τ' c (some (g - 1)) := by
    have h := gen_in τ' c _ (.inr sb) hcomp hcmdc rfl ⟨mcτ, hmcτ⟩
    rwa [hgenc] at h
  have hv1 : g - 1 = (recycleCount (.inr sb) τ' (n1 - 1) : ℤ) := by
    have h := isGenOf_genValue hgτ'c hcmdc rfl hn1
    rwa [genValue_of_isRegistrant rfl] at h
  -- `c`'s arrive step: the config at `n1` is a `run`
  obtain ⟨hcomp', hidxL1, j1, C1a, C1a', hj1eq, hC1a, hC1a', hC1aprog, hC1a'prog⟩ := id hn1
  have hC1aget : τ'[n1]? = some C1a' := by
    rw [hj1eq]
    exact hC1a'
  have hC1astep : CTAStep C1a C1a' := chain_step hchain hC1a hC1a'
  obtain ⟨s1n, T1n, rfl⟩ : ∃ s2 T2, C1a' = Config.run s2 T2 := by
    have hcne : ((Config.run State.initial T).progOf c.thread).drop c.idx ≠ [] := by
      intro h
      have hl := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at hl
      simp only [WeftCommon.Config.progOf] at hcL
      omega
    cases hC1astep with
    | @interleave _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @recycle _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @mb_recycle _ _ _ _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩
    | @done sa Ta hdone2 hnofull hmbnofull =>
      exfalso
      have hcprog : Ta.prog c.thread
          = ((Config.run State.initial T).progOf c.thread).drop c.idx := hC1aprog
      have hcids : c.thread ∈ Ta.ids := by
        by_contra hni
        rw [Ta.nil_outside_ids c.thread hni] at hcprog
        exact hcne hcprog.symm
      exact hcne (hcprog ▸ hdone2 c.thread hcids)
    | @error sa Ta i P' _ _ hth =>
      exfalso
      have h1 : Ta.prog c.thread
          = ((Config.run State.initial T).progOf c.thread).drop c.idx := hC1aprog
      have h2 : Ta.prog c.thread
          = ((Config.run State.initial T).progOf c.thread).drop (c.idx + 1) := hC1a'prog
      rw [h1] at h2
      have hl := congrArg List.length h2
      simp only [List.length_drop] at hl
      simp only [WeftCommon.Config.progOf] at hcL
      omega
  -- search for the firing config
  have hPex : ∃ d, ∃ s T2, τ'[p + d]? = some (Config.run s T2) ∧
      ((∃ b' t', t' ∈ s.blocked b') ∨ p + d = n1) :=
    ⟨n1 - p, s1n, T1n,
      by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget, Or.inr (by omega)⟩
  set d₀ := Nat.find hPex with hd₀
  have hd₀spec := Nat.find_spec hPex
  rw [← hd₀] at hd₀spec
  obtain ⟨sq', Tq', hCq', hdisj⟩ := hd₀spec
  have hd₀pos : 0 < d₀ := by
    rcases Nat.eq_zero_or_pos d₀ with h | h
    · exfalso
      rw [h, Nat.add_zero, hcut, Option.some.injEq, WeftCommon.Config.run.injEq] at hCq'
      obtain ⟨rfl, rfl⟩ := hCq'
      rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
      · exact hsempty b' t' hjoin
      · omega
    · exact h
  have hq1 : ¬ (∃ s T2, τ'[p + (d₀ - 1)]? = some (Config.run s T2) ∧
      ((∃ b' t', t' ∈ s.blocked b') ∨ p + (d₀ - 1) = n1)) := Nat.find_min hPex (by omega)
  have hqn1 : p + d₀ ≤ n1 := by
    have hle : d₀ ≤ n1 - p := hd₀ ▸ Nat.find_le
      ⟨s1n, T1n, by rw [show p + (n1 - p) = n1 from by omega]; exact hC1aget,
        Or.inr (by omega)⟩
    omega
  have hqlen : p + d₀ < τ'.length := (List.getElem?_eq_some_iff.mp hCq').1
  have hget : ∀ j, j ≤ p + d₀ → ∃ C, τ'[j]? = some C :=
    fun j hj => ⟨_, List.getElem?_eq_getElem (show j < τ'.length by omega)⟩
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have hei0 : ∀ s, (WeftCommon.Config.state? (Config.run State.initial T)) = some s →
      s.EnabledInv := by
    intro s hs
    simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
    subst hs
    exact State.EnabledInv.initial
  have heiAll : ∀ C ∈ τ', ∀ s, C.state? = some s → s.EnabledInv :=
    enabledInv_chain hchain hC₀head hei0
  -- `w`'s static facts
  have hcmdw_get : (T.prog w.thread)[w.idx]'((mem_progPoints_iff T w).mp hw).2
      = Cmd.wait_mb sb ph := by
    have h := hcmdw
    simp only [CTA.cmdAt] at h
    rw [List.getElem?_eq_getElem ((mem_progPoints_iff T w).mp hw).2,
      Option.some.injEq] at h
    exact h
  have hdrop2 : (T.prog w.thread).drop w.idx
      = Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1) := by
    rw [List.drop_eq_getElem_cons ((mem_progPoints_iff T w).mp hw).2, hcmdw_get]
  -- program invariance: `w` stays poised until the firing config
  have hinv : ∀ e, e ≤ d₀ - 1 → ∃ s' T', τ'[p + e]? = some (Config.run s' T') ∧
      T'.prog w.thread = (T.prog w.thread).drop w.idx := by
    intro e
    induction e with
    | zero => intro _; exact ⟨s_G, T_G, by simpa using hcut, hwhead⟩
    | succ e ih =>
      intro he
      obtain ⟨s', T', hCe, hprog⟩ := ih (by omega)
      obtain ⟨C'', hCe1⟩ := hget (p + (e + 1)) (by omega)
      have hstep : CTAStep (Config.run s' T') C'' :=
        chain_step hchain (show τ'[p + e]? = some _ from hCe)
          (show τ'[(p + e) + 1]? = _ from hCe1)
      obtain ⟨Cnext, hCnext⟩ := hget (p + (e + 1) + 1) (by omega)
      obtain ⟨s'', T'', rfl⟩ : ∃ s2 T2, C'' = Config.run s2 T2 := by
        cases chain_step hchain (show τ'[p + (e + 1)]? = _ from hCe1)
          (show τ'[p + (e + 1) + 1]? = _ from hCnext) <;> exact ⟨_, _, rfl⟩
      refine ⟨s'', T'', hCe1, ?_⟩
      have hsemp_e1 : ∀ bb tt, tt ∉ s''.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e + 1 < d₀ by omega)
          ⟨s'', T'', hCe1, Or.inl ⟨bb, tt, htt⟩⟩
      have hsemp_e : ∀ bb tt, tt ∉ s'.blocked bb := fun bb tt htt =>
        Nat.find_min hPex (show e < d₀ by omega) ⟨s', T', hCe, Or.inl ⟨bb, tt, htt⟩⟩
      cases hstep with
      | @interleave _ _ _ i P' hi hbar hmbar hth =>
        by_cases hiw : i = w.thread
        · exfalso
          subst hiw
          rw [hprog, hdrop2] at hth
          cases hth with
          | mb_wait_block he2 hb2 =>
            exact hsemp_e1 (.inr sb) w.thread
              (by simp [State.blocked, Function.update_self])
          | mb_wait_pass he2 hb2 hnep =>
            -- `w` would execute at `p + e + 1 ≤ n1 - 1` with too few recycles
            have htw : IsTimeOf (Config.run State.initial T) τ' w (p + e + 1) := by
              refine ⟨hcomp, hwL, p + e, _, _, rfl, hCe, hCe1, hprog, ?_⟩
              change (T'.set w.thread hi
                ((T.prog w.thread).drop (w.idx + 1))).prog w.thread = _
              simp only [WeftCommon.CTA.set, Function.update_self]
              rfl
            have hgw : IsGenOf (Config.run State.initial T) τ' w (some g) := by
              have h := gen_in τ' w _ (.inr sb) hcomp hcmdw rfl ⟨mwτ, hmwτ⟩
              rwa [hgenw] at h
            have hval := isGenOf_genValue hgw hcmdw rfl htw
            have hle := le_of_genValue hval.symm
            have hmono2 : recycleCount (.inr sb) τ' (p + e + 1 - 1)
                ≤ recycleCount (.inr sb) τ' (n1 - 1) :=
              recycleCount_mono _ τ' (by omega)
            omega
        · simp only [WeftCommon.CTA.set, Function.update_of_ne (Ne.symm hiw)]
          exact hprog
      | @recycle _ _ bb I A n hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inl bb) x
              (by change x ∈ (s'.BN bb).synced; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
      | @mb_recycle _ _ sbb I A n ph2 hb hfull hpark =>
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_e (.inr sbb) x
              (by change x ∈ (s'.BM sbb).waiting; rw [hb]; simp)) (by simp)
        subst hI
        simpa [WeftCommon.CTA.wake] using hprog
  -- the firing config
  have hmem : ∀ {j C}, τ'[j]? = some C → C ∈ τ' := fun hj => List.mem_of_getElem? hj
  obtain ⟨sm, Tm, hCq1, hprogm⟩ := hinv (d₀ - 1) (le_refl _)
  have hsemp_q1 : ∀ bb tt, tt ∉ sm.blocked bb := fun bb tt htt =>
    hq1 ⟨sm, Tm, hCq1, Or.inl ⟨bb, tt, htt⟩⟩
  have hheadm : Tm.prog w.thread
      = Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1) := by
    rw [hprogm, hdrop2]
  have hwids : w.thread ∈ Tm.ids := by
    by_contra hni
    rw [Tm.nil_outside_ids w.thread hni] at hheadm
    exact (List.cons_ne_nil _ _) hheadm.symm
  have hwen : sm.E w.thread = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    obtain ⟨bb, hbb⟩ := heiAll _ (hmem hCq1) sm rfl w.thread hne
    exact hsemp_q1 bb w.thread hbb
  have hCq'' : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run sq' Tq') := by
    rw [show (p + (d₀ - 1)) + 1 = p + d₀ from by omega]
    exact hCq'
  have hstepq : CTAStep (Config.run sm Tm) (Config.run sq' Tq') :=
    chain_step hchain hCq1 hCq''
  have hguards : (∀ nb'', sm.BN nb'' = NamedBarrierState.unconfigured ∨
      ∃ I A n, sm.BN nb'' = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat)) ∧
      (∀ sb'', sm.BM sb'' = MBarrierState.uninitialized ∨
      ∃ I A n ph2, sm.BM sb'' = ⟨I, A, some n, ph2⟩ ∧ A < (n : Nat)) := by
    rcases hdisj with ⟨b', t', hjoin⟩ | hpeq
    · exact guards_of_joins_blocked hstepq rfl rfl (hsemp_q1 b' t') hjoin
    · have hj1 : j1 = p + (d₀ - 1) := by omega
      have e1 : C1a = Config.run sm Tm := by
        rw [hj1, hCq1] at hC1a
        exact (Option.some.injEq _ _).mp hC1a.symm
      rw [e1] at hC1aprog
      simp only [WeftCommon.Config.progOf] at hC1aprog
      have hadv : ∀ (Twake : CTA), T1n = Twake → Twake.prog c.thread = Tm.prog c.thread →
          False := by
        intro Twake hTeq hsame
        have h2 := hC1a'prog
        simp only [WeftCommon.Config.progOf] at h2
        rw [hTeq, hsame, hC1aprog] at h2
        have hl := congrArg List.length h2
        simp only [List.length_drop] at hl
        simp only [WeftCommon.Config.progOf] at hcL
        omega
      cases hstepq with
      | @interleave _ _ _ i P' hi hbar hmbar hth => exact ⟨hbar, hmbar⟩
      | @recycle _ _ bb I A n hb hfull hpark =>
        exfalso
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_q1 (.inl bb) x
              (by change x ∈ (sm.BN bb).synced; rw [hb]; simp)) (by simp)
        subst hI
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]
            rw [show j1 + 1 = n1 from by omega]
            exact hC1aget
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [WeftCommon.Config.run.injEq] at h
          exact h.2.symm
        exact hadv (Tm.wake []) hTeq (by simp [WeftCommon.CTA.wake])
      | @mb_recycle _ _ sbb I A n ph2 hb hfull hpark =>
        exfalso
        have hI : I = [] := by
          rcases List.eq_nil_or_concat I with h | ⟨I', x, rfl⟩
          · exact h
          · exact absurd (hsemp_q1 (.inr sbb) x
              (by change x ∈ (sm.BM sbb).waiting; rw [hb]; simp)) (by simp)
        subst hI
        have hTeq : T1n = Tm.wake [] := by
          have hat : τ'[(p + (d₀ - 1)) + 1]? = some (Config.run s1n T1n) := by
            rw [← hj1]
            rw [show j1 + 1 = n1 from by omega]
            exact hC1aget
          rw [hCq''] at hat
          have h := (Option.some.injEq _ _).mp hat
          rw [WeftCommon.Config.run.injEq] at h
          exact h.2.symm
        exact hadv (Tm.wake []) hTeq (by simp [WeftCommon.CTA.wake])
  obtain ⟨hbarq, hmbarq⟩ := hguards
  -- reachability + shared prefix + gluing
  have hreach : ∀ j, j ≤ p + d₀ → ∀ C, τ'[j]? = some C →
      Relation.ReflTransGen CTAStep (Config.run State.initial T) C := by
    intro j
    induction j with
    | zero =>
      intro _ C hC
      rw [← List.head?_eq_getElem?, hC₀head, Option.some.injEq] at hC
      subst hC
      exact Relation.ReflTransGen.refl
    | succ j ih =>
      intro hj C hC
      obtain ⟨Cj, hCj⟩ := hget j (by omega)
      exact Relation.ReflTransGen.tail (ih (by omega) Cj hCj) (chain_step hchain hCj hC)
  have hreachq1 : Relation.ReflTransGen CTAStep (Config.run State.initial T)
      (Config.run sm Tm) :=
    hreach (p + (d₀ - 1)) (by omega) _ hCq1
  have hprelen : (τ'.take (p + d₀)).length = p + d₀ := by
    rw [List.length_take]
    omega
  have hpne : τ'.take (p + d₀) ≠ [] := by
    intro h
    rw [h, List.length_nil] at hprelen
    omega
  have hprechain : List.IsChain CTAStep (τ'.take (p + d₀)) := hchain.take _
  have hpre_get : ∀ i, i < p + d₀ → (τ'.take (p + d₀))[i]? = τ'[i]? :=
    fun i hi => List.getElem?_take_of_lt hi
  have hprehead : (τ'.take (p + d₀)).head? = some (Config.run State.initial T) := by
    rw [List.head?_eq_getElem?, hpre_get 0 (by omega), ← List.head?_eq_getElem?]
    exact hC₀head
  have hprelast : (τ'.take (p + d₀)).getLast? = some (Config.run sm Tm) := by
    rw [List.getLast?_eq_getElem?, hprelen, hpre_get (p + d₀ - 1) (by omega),
      show p + d₀ - 1 = p + (d₀ - 1) from by omega]
    exact hCq1
  have glue : ∀ (σ : List Config) (Cstart : Config), IsCompleteTraceFrom Cstart σ →
      CTAStep (Config.run sm Tm) Cstart →
      IsCompleteTraceFrom (Config.run State.initial T) (τ'.take (p + d₀) ++ σ) := by
    intro σ Cstart hσ hcon
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.IsChain.append hprechain hσ.1.subtrace ?_
      intro x hx y hy
      rw [hprelast, Option.mem_some_iff] at hx
      subst hx
      rw [hσ.2, Option.mem_some_iff] at hy
      subst hy
      exact hcon
    · obtain ⟨Cn, hCnlast, hterm⟩ := hσ.1.ends
      exact ⟨Cn, List.mem_getLast?_append_of_mem_getLast? hCnlast, hterm⟩
    · rw [List.head?_append_of_ne_nil _ hpne]
      exact hprehead
  have hshareTake : ∀ j, j < p + d₀ → ∀ (σ : List Config),
      (τ'.take (p + d₀) ++ σ)[j]? = τ'[j]? := by
    intro j hj σ
    rw [List.getElem?_append_left (by rw [hprelen]; exact hj)]
    exact hpre_get j hj
  -- **Fire `w` early.**
  rcases hmbarq sb with hbu | ⟨I, A, n', ph', hbcfg, hltn⟩
  · -- uninitialized: `mb_wait_err` — the spliced trace ends in `err`
    have herr : CTAStep (Config.run sm Tm) (Config.err Tm) :=
      CTAStep.error hbarq hmbarq
        (by rw [hheadm]; exact ThreadStep.mb_wait_err hwen hbu)
    have herrtrace : IsCompleteTraceFrom (Config.err Tm) [Config.err Tm] :=
      ⟨⟨List.isChain_singleton _, Config.err Tm, by simp, Or.inr (Or.inl ⟨Tm, rfl⟩)⟩, by simp⟩
    obtain ⟨sd2, hdone2⟩ :=
      CTA.WellSynchronized.completeTrace_ends_done hws (glue _ _ herrtrace herr)
    have hgl : (τ'.take (p + d₀) ++ [Config.err Tm]).getLast? = some (Config.err Tm) := by
      simp
    rw [hgl] at hdone2
    simp at hdone2
  · by_cases hpheq : ph = ph'
    · -- matched phase: `mb_wait_block` parks `w`; it wakes at recycle `≤ g`
      subst hpheq
      have hwstep : CTAStep (Config.run sm Tm)
          (Config.run { sm with E := Function.update sm.E w.thread false,
                                BM := Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ }
            (Tm.set w.thread hwids
              (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1)))) :=
        CTAStep.interleave hwids hbarq hmbarq
          (by rw [hheadm]; exact ThreadStep.mb_wait_block hwen hbcfg)
      have hsNval : ({ sm with E := Function.update sm.E w.thread false,
                               BM := Function.update sm.BM sb
                                 ⟨w.thread :: I, A, some n', ph⟩ } : State).BM sb
          = ⟨w.thread :: I, A, some n', ph⟩ := by
        change Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ sb = _
        rw [Function.update_self]
      have hsync : w.thread ∈ ({ sm with E := Function.update sm.E w.thread false,
                                         BM := Function.update sm.BM sb
                                           ⟨w.thread :: I, A, some n', ph⟩ } : State).blocked
          (.inr sb) := by
        change w.thread ∈ (({ sm with E := Function.update sm.E w.thread false,
                                      BM := Function.update sm.BM sb
                                        ⟨w.thread :: I, A, some n', ph⟩ } : State).BM sb).waiting
        rw [hsNval]
        simp
      have hbwN := inv_preserved T.barrierSet hwstep (barriersWithin_of_reaches hreachq1)
      obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
      set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
      have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' :=
        glue σ _ hσ hwstep
      obtain ⟨sd'', hdone''⟩ := CTA.WellSynchronized.completeTrace_ends_done hws htrace
      obtain ⟨m2, hm2⟩ := exists_time_of_ends_done htrace hdone'' (η := w) hwL
      have hCpark : τ''[p + d₀]? = some (Config.run
          { sm with E := Function.update sm.E w.thread false,
                    BM := Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ }
          (Tm.set w.thread hwids
            (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1)))) := by
        rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
          ← List.head?_eq_getElem?]
        exact hσ.2
      have hprogpark : (Tm.set w.thread hwids
            (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1))).prog w.thread
          = ((Config.run State.initial T).progOf w.thread).drop w.idx := by
        change (Function.update Tm.prog w.thread _) w.thread = _
        rw [Function.update_self]
        exact hdrop2.symm
      have hBI'' : ∀ C ∈ τ'', ∀ s, C.state? = some s → s.BlockInv := by
        refine blockInv_chain htrace.1.subtrace htrace.2 ?_
        intro s hs
        simp only [WeftCommon.Config.state?, Option.some.injEq] at hs
        subst hs
        exact State.BlockInv.initial
      have hpn : p + d₀ < m2 := by
        refine lt_time_of_lt_progOf hm2 hCpark ?_
        have h1 : (Config.run
            { sm with E := Function.update sm.E w.thread false,
                      BM := Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ }
            (Tm.set w.thread hwids
              (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1)))).progOf w.thread
            = ((Config.run State.initial T).progOf w.thread).drop w.idx := hprogpark
        rw [h1, List.length_drop]
        have hX : w.idx < ((Config.run State.initial T).progOf w.thread).length := hwL
        omega
      have heq3 : recycleCount (.inr sb) τ'' (m2 - 1)
          = recycleCount (.inr sb) τ'' (p + d₀) :=
        parked_blocked_recycleCount hBI'' rfl hm2 hCpark hsync hprogpark hpn
      have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
        rw [hτ''def, hshareTake (p + (d₀ - 1)) (by omega)]
        exact hCq1
      have hCpark'' : τ''[p + (d₀ - 1) + 1]? = some (Config.run
          { sm with E := Function.update sm.E w.thread false,
                    BM := Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ }
          (Tm.set w.thread hwids
            (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1)))) := by
        rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]
        exact hCpark
      have hstepfalse : stepRecyclesBarrier (.inr sb) (Config.run sm Tm) (Config.run
          { sm with E := Function.update sm.E w.thread false,
                    BM := Function.update sm.BM sb ⟨w.thread :: I, A, some n', ph⟩ }
          (Tm.set w.thread hwids
            (Cmd.wait_mb sb ph :: (T.prog w.thread).drop (w.idx + 1)))) = false := by
        simp [stepRecyclesBarrier, WeftCommon.Config.state?]
      have heq4 : recycleCount (.inr sb) τ'' (p + d₀)
          = recycleCount (.inr sb) τ' (p + (d₀ - 1)) := by
        have hsucc : recycleCount (.inr sb) τ'' (p + d₀)
            = recycleCount (.inr sb) τ'' (p + (d₀ - 1)) := by
          rw [show p + d₀ = (p + (d₀ - 1)) + 1 from by omega]
          exact recycleCount_succ_of_not_recycle _ hCq1'' hCpark'' hstepfalse
        rw [hsucc]
        exact recycleCount_prefix_eq _ (p + (d₀ - 1))
          (fun j hj => hshareTake j (by omega) σ)
      have hgw : IsGenOf (Config.run State.initial T) τ'' w (some g) := by
        have h := gen_in τ'' w _ (.inr sb) htrace hcmdw rfl ⟨mwτ, hmwτ⟩
        rwa [hgenw] at h
      have hval := isGenOf_genValue hgw hcmdw rfl hm2
      have hle := le_of_genValue hval.symm
      have hmono : recycleCount (.inr sb) τ' (p + (d₀ - 1))
          ≤ recycleCount (.inr sb) τ' (n1 - 1) :=
        recycleCount_mono _ τ' (show p + (d₀ - 1) ≤ n1 - 1 from by omega)
      omega
    · -- mismatched phase: `mb_wait_pass` — `w` executes at once with too few recycles
      have hwstep : CTAStep (Config.run sm Tm)
          (Config.run sm (Tm.set w.thread hwids ((T.prog w.thread).drop (w.idx + 1)))) :=
        CTAStep.interleave hwids hbarq hmbarq
          (by rw [hheadm]; exact ThreadStep.mb_wait_pass hwen hbcfg
                (fun hcon => hpheq hcon))
      have hbwN := inv_preserved T.barrierSet hwstep (barriersWithin_of_reaches hreachq1)
      obtain ⟨σ, hσ⟩ := exists_completeTrace T.barrierSet _ hbwN
      set τ'' := τ'.take (p + d₀) ++ σ with hτ''def
      have htrace : IsCompleteTraceFrom (Config.run State.initial T) τ'' :=
        glue σ _ hσ hwstep
      have hCq1'' : τ''[p + (d₀ - 1)]? = some (Config.run sm Tm) := by
        rw [hτ''def, hshareTake (p + (d₀ - 1)) (by omega)]
        exact hCq1
      have hCpass : τ''[p + d₀]? = some (Config.run sm
          (Tm.set w.thread hwids ((T.prog w.thread).drop (w.idx + 1)))) := by
        rw [hτ''def, List.getElem?_append_right (le_of_eq hprelen), hprelen, Nat.sub_self,
          ← List.head?_eq_getElem?]
        exact hσ.2
      have htw : IsTimeOf (Config.run State.initial T) τ'' w (p + d₀) := by
        refine ⟨htrace, hwL, p + (d₀ - 1), _, _, by omega,
          hCq1'', by rw [show p + (d₀ - 1) + 1 = p + d₀ from by omega]; exact hCpass,
          hprogm, ?_⟩
        change (Tm.set w.thread hwids ((T.prog w.thread).drop (w.idx + 1))).prog w.thread
          = _
        simp only [WeftCommon.CTA.set, Function.update_self]
        rfl
      have hgw : IsGenOf (Config.run State.initial T) τ'' w (some g) := by
        have h := gen_in τ'' w _ (.inr sb) htrace hcmdw rfl ⟨mwτ, hmwτ⟩
        rwa [hgenw] at h
      have hval := isGenOf_genValue hgw hcmdw rfl htw
      have hle := le_of_genValue hval.symm
      have heq5 : recycleCount (.inr sb) τ'' (p + d₀ - 1)
          = recycleCount (.inr sb) τ' (p + d₀ - 1) := by
        refine recycleCount_prefix_eq _ (p + d₀ - 1)
          (fun j hj => hshareTake j (by omega) σ)
      have hmono : recycleCount (.inr sb) τ' (p + d₀ - 1)
          ≤ recycleCount (.inr sb) τ' (n1 - 1) :=
        recycleCount_mono _ τ' (by omega)
      omega

/-- **Wait upper bound** (mode 2c). If generation `g + 1` *fills* (`n`
registrants, `n` from the unique initialization) yet `w` precedes none of them,
run the ideal `G = {η | ¬ hb(w, η)}`: every arrival of generations `≤ g + 1`
lands before the cut, so the `(g + 2)`-th recycle fires before `w`, which then
observes `≥ g + 1` — never `g`. -/
theorem wait_upper_bound_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) (hws : T.WellSynchronized)
    (huniq : okUniqueInitCheck T τ = true)
    {w : ProgPoint} {sb : SharedBarrier} {ph : Phase} {g : ℤ} {n : ℕ+}
    (hw : w ∈ T.progPoints) (hcmdw : T.cmdAt w = some (.wait_mb sb ph))
    (hgenw : pointGen T τ w = some g)
    (hn : T.initCountOf sb = some n)
    (hlen : (T.progPoints.filter fun cp =>
      registrantGen T τ cp = some (.inr sb, g + 1)).length = (n : Nat))
    (hnone : ∀ cp ∈ T.progPoints.filter fun cp =>
        registrantGen T τ cp = some (.inr sb, g + 1),
      (w, cp) ∉ (CheckWellSynchronized T τ).2) : False := by
  classical
  set points := T.progPoints.filter fun cp =>
    registrantGen T τ cp = some (.inr sb, g + 1) with hpointsdef
  have hpnd : points.Nodup := (progPoints_nodup T).filter _
  -- decode: each point is an `arrive_mb sb` of reference generation `g + 1`
  have hdec : ∀ cp ∈ points, cp ∈ T.progPoints ∧ T.cmdAt cp = some (.arrive_mb sb) ∧
      pointGen T τ cp = some (g + 1) := by
    intro cp hcp
    rw [hpointsdef, List.mem_filter] at hcp
    obtain ⟨hcpm, hcpreg⟩ := hcp
    rw [decide_eq_true_eq] at hcpreg
    obtain ⟨cmd, hcmd, hisreg, hbar, hpg⟩ := registrantGen_some hcpreg
    refine ⟨hcpm, ?_, hpg⟩
    cases cmd with
    | read l => simp [Cmd.isRegistrant] at hisreg
    | write l => simp [Cmd.isRegistrant] at hisreg
    | init_mb sb' n' => simp [Cmd.isRegistrant] at hisreg
    | wait_mb sb' ph' => simp [Cmd.isRegistrant] at hisreg
    | arrive_nb nb1 m1 =>
      have h := hbar
      simp only [Cmd.barrier?, Option.some.injEq] at h
      exact absurd h (by simp)
    | sync_nb nb1 m1 =>
      have h := hbar
      simp only [Cmd.barrier?, Option.some.injEq] at h
      exact absurd h (by simp)
    | arrive_mb sb' =>
      have h : sb' = sb := by
        have hh := hbar
        simp only [Cmd.barrier?, Option.some.injEq, Sum.inr.injEq] at hh
        exact hh
      subst h
      exact hcmd
  have hnothb : ∀ cp ∈ points, ¬ happensBefore T τ w cp := by
    intro cp hcp
    obtain ⟨hcpm, hcpcmd, -⟩ := hdec cp hcp
    have hne : w ≠ cp := by
      intro h
      rw [h, hcpcmd] at hcmdw
      simp at hcmdw
    exact not_happensBefore_of_not_mem hne (hnone cp hcp)
  -- run the ideal `G = {η | ¬ hb(w, η)}` to its cut
  obtain ⟨τ', p, s_G, T_G, hcomp, hcut, hcutprog, hsempty⟩ :=
    run_ideal (τ := τ) (η₁ := w) hτ hws
  obtain ⟨sd, hdone⟩ := CTA.WellSynchronized.completeTrace_ends_done hws hcomp
  have hchain := hcomp.1.subtrace
  have hC₀head : τ'.head? = some (Config.run State.initial T) := hcomp.2
  have htr0 : τ'[0]? = some (Config.run State.initial T) := by
    rw [← List.head?_eq_getElem?]
    exact hC₀head
  have hwL : w.idx < ((Config.run State.initial T).progOf w.thread).length :=
    ((mem_progPoints_iff T w).mp hw).2
  obtain ⟨mw, hmw⟩ := exists_time_of_ends_done hcomp hdone hwL
  have hfcutw : fcut T τ w w.thread ≤ w.idx := fcut_le_of_hb Relation.ReflTransGen.refl hw
  have hpmw : p < mw := by
    refine lt_time_of_lt_progOf hmw hcut ?_
    simp only [WeftCommon.Config.progOf]
    rw [hcutprog w.thread, List.length_drop]
    have : w.idx < (T.prog w.thread).length := hwL
    omega
  -- each point executes by the cut
  have htimes : ∀ cp ∈ points, ∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧
      t ≤ p := by
    intro cp hcp
    obtain ⟨hcpm, hcpcmd, -⟩ := hdec cp hcp
    have hcpL : cp.idx < (T.prog cp.thread).length := ((mem_progPoints_iff T cp).mp hcpm).2
    obtain ⟨t, ht⟩ := exists_time_of_ends_done hcomp hdone
      (show cp.idx < ((Config.run State.initial T).progOf cp.thread).length from hcpL)
    refine ⟨t, ht, ?_⟩
    have hlt := lt_fcut_of_not_hb (hnothb cp hcp) hcpm
    refine time_le_of_progOf_le ht hcut ?_
    change (T_G.prog cp.thread).length ≤ _
    rw [hcutprog cp.thread, List.length_drop]
    change _ ≤ (T.prog cp.thread).length - cp.idx - 1
    omega
  -- generation transfer into τ'
  obtain ⟨sτ, hdoneτ⟩ := hτ.2
  have gen_in : ∀ (η : ProgPoint) (cmd : Cmd), T.cmdAt η = some cmd →
      cmd.barrier? = some (.inr sb) →
      η.idx < ((Config.run State.initial T).progOf η.thread).length →
      IsGenOf (Config.run State.initial T) τ' η (pointGen T τ η) := by
    intro η cmd hcmdh hbarh hL
    obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdoneτ hL
    have hgenτ : IsGenOf (Config.run State.initial T) τ η (pointGen T τ η) :=
      isGenOf_pointGen hcmdh hbarh hmτ
    have hbind : (T.cmdAt η).bind Cmd.barrier? = some (.inr sb) := by
      rw [hcmdh]
      exact hbarh
    obtain ⟨g', hgτ, hgσ⟩ := hws.2 τ τ' hτ.1 hcomp η ⟨.inr sb, hbind⟩
    rwa [IsGenOf.unique hgτ hgenτ] at hgσ
  -- each point's recycle count at its execution is (the cast of) `g + 1`
  have hrcpoint : ∀ cp ∈ points, ∀ t, IsTimeOf (Config.run State.initial T) τ' cp t →
      (recycleCount (.inr sb) τ' (t - 1) : ℤ) = g + 1 := by
    intro cp hcp t ht
    obtain ⟨hcpm, hcpcmd, hpg⟩ := hdec cp hcp
    have hgcp : IsGenOf (Config.run State.initial T) τ' cp (some (g + 1)) := by
      have h := gen_in cp _ hcpcmd rfl ((mem_progPoints_iff T cp).mp hcpm).2
      rwa [hpg] at h
    have h := isGenOf_genValue hgcp hcpcmd rfl ht
    rw [genValue_of_isRegistrant rfl] at h
    omega
  -- `w`'s recycle count at its execution is exactly `g + 1`, mismatched phase
  have hgw : IsGenOf (Config.run State.initial T) τ' w (some g) := by
    have h := gen_in w _ hcmdw rfl hwL
    rwa [hgenw] at h
  have hvalw := isGenOf_genValue hgw hcmdw rfl hmw
  have hpne : points ≠ [] := by
    intro h
    rw [h] at hlen
    simp only [List.length_nil] at hlen
    have := n.pos
    omega
  obtain ⟨cp₀, hcp₀⟩ := List.exists_mem_of_ne_nil points hpne
  obtain ⟨t₀, ht₀, ht₀p⟩ := htimes cp₀ hcp₀
  have hrc₀ := hrcpoint cp₀ hcp₀ t₀ ht₀
  have hmono₀ : recycleCount (.inr sb) τ' (t₀ - 1) ≤ recycleCount (.inr sb) τ' (mw - 1) :=
    recycleCount_mono _ τ' (by omega)
  have hge : g + 1 ≤ (recycleCount (.inr sb) τ' (mw - 1) : ℤ) := by omega
  have hrw1 : (recycleCount (.inr sb) τ' (mw - 1) : ℤ) = g + 1 ∧
      phaseAfter (recycleCount (.inr sb) τ' (mw - 1)) ≠ ph := by
    simp only [Cmd.genValue] at hvalw
    split at hvalw
    · exfalso
      omega
    · rename_i hph
      exact ⟨by omega, hph⟩
  obtain ⟨hrwval, hrwph⟩ := hrw1
  -- ===== counting: `arrived ≥ n` at `mw - 1` =====
  have hmwlen : mw < τ'.length := by
    obtain ⟨_, _, j, _, _, hj, _, hCj1, _, _⟩ := hmw
    have := (List.getElem?_eq_some_iff.mp hCj1).1
    omega
  have hrun : ∀ j, j ≤ mw - 1 → ∃ s2 T2, τ'[j]? = some (Config.run s2 T2) := by
    intro j hj
    obtain ⟨Cj, hCj⟩ : ∃ C, τ'[j]? = some C := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨Cj1, hCj1⟩ : ∃ C, τ'[j + 1]? = some C :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s2, T2, heq⟩ := CTAStep.source_run (chain_step hchain hCj hCj1)
    exact ⟨s2, T2, by rw [hCj, heq]⟩
  have key : ∀ j, j ≤ mw - 1 → ∀ sj Tj, τ'[j]? = some (Config.run sj Tj) →
      points.countP (fun cp =>
        decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ j))
        ≤ (sj.BM sb).arrived := by
    intro j
    induction j with
    | zero =>
      intro _ sj Tj hj
      have h0 : points.countP (fun cp =>
          decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ 0)) = 0 := by
        rw [List.countP_eq_zero]
        intro cp _
        simp only [decide_eq_true_eq, not_exists, not_and]
        rintro t ht
        obtain ⟨_, _, j2, _, _, hj2, _⟩ := ht
        omega
      rw [h0]
      exact Nat.zero_le _
    | succ jj ih =>
      intro hle sj' Tj' hj'
      obtain ⟨sj, Tj, hj⟩ := hrun jj (by omega)
      have hstep := chain_step hchain hj hj'
      have hihj := ih (by omega) sj Tj hj
      by_cases hrec : stepRecyclesBarrier (.inr sb) (Config.run sj Tj)
          (Config.run sj' Tj') = true
      · -- an `sb`-recycle strictly below `g + 1` empties the count
        have hrcsucc := recycleCount_succ_of_recycle _ τ' hj hj' hrec
        have hcnt0 : points.countP (fun cp =>
            decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ jj + 1))
            = 0 := by
          rw [List.countP_eq_zero]
          intro cp hcp
          simp only [decide_eq_true_eq, not_exists, not_and]
          rintro t ht htle
          have hr := hrcpoint cp hcp t ht
          have h1 : recycleCount (.inr sb) τ' (t - 1) ≤ recycleCount (.inr sb) τ' jj :=
            recycleCount_mono _ τ' (by omega)
          have h2 : recycleCount (.inr sb) τ' (jj + 1)
              ≤ recycleCount (.inr sb) τ' (mw - 1) :=
            recycleCount_mono _ τ' (by omega)
          omega
        rw [hcnt0]
        exact Nat.zero_le _
      · rw [Bool.not_eq_true] at hrec
        have hamono := arrived_mono_of_not_recycle hstep hrec rfl rfl
        by_cases hdrop : ∃ cp ∈ points,
            IsTimeOf (Config.run State.initial T) τ' cp (jj + 1)
        · obtain ⟨cp₁, hcp₁, ht₁⟩ := hdrop
          obtain ⟨hcp₁m, hcp₁cmd, -⟩ := hdec cp₁ hcp₁
          obtain ⟨Cy, Cy', hCy, hCy', hshy⟩ := time_drop_evidence ht₁ hcp₁cmd
          obtain rfl : Cy = Config.run sj Tj := by
            rw [show jj + 1 - 1 = jj from rfl] at hCy
            exact Option.some.inj (hCy.symm.trans hj)
          obtain rfl : Cy' = Config.run sj' Tj' := Option.some.inj (hCy'.symm.trans hj')
          have hinc := arrive_mb_drop_arrived hstep hshy rfl rfl rfl
          -- the count grows by exactly one (`cp₁` is the unique new element)
          have hcle : points.countP (fun cp =>
              decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ jj + 1))
              = points.countP (fun cp =>
              decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ jj))
              + 1 := by
            refine countP_succ_of_unique hpnd hcp₁ ?_ ?_ ?_
            · rw [decide_eq_true_eq]
              exact ⟨jj + 1, ht₁, le_refl _⟩
            · rw [decide_eq_false_iff_not]
              rintro ⟨t, ht', htle⟩
              have := IsTimeOf.unique ht' ht₁
              omega
            · intro x hx hxne
              have hiff : (∃ t, IsTimeOf (Config.run State.initial T) τ' x t ∧ t ≤ jj + 1)
                  ↔ (∃ t, IsTimeOf (Config.run State.initial T) τ' x t ∧ t ≤ jj) := by
                constructor
                · rintro ⟨t, ht, htle⟩
                  refine ⟨t, ht, ?_⟩
                  rcases Nat.lt_or_ge t (jj + 1) with h | h
                  · omega
                  · exfalso
                    have hteq : t = jj + 1 := by omega
                    subst hteq
                    -- two distinct points executing at the same step: impossible
                    obtain ⟨hxm, hxcmd, -⟩ := hdec x hx
                    obtain ⟨Cx, Cx', hCx, hCx', hshx⟩ := time_drop_evidence ht hxcmd
                    obtain rfl : Cx = Config.run sj Tj := by
                      rw [show jj + 1 - 1 = jj from rfl] at hCx
                      exact Option.some.inj (hCx.symm.trans hj)
                    obtain rfl : Cx' = Config.run sj' Tj' :=
                      Option.some.inj (hCx'.symm.trans hj')
                    have hteq2 : x.thread = cp₁.thread :=
                      arrive_mb_head_drop_same_thread hstep hshx rfl hshy rfl
                    obtain ⟨_, hidxLx, jx, Cx0, Cx0', hjx, hCjx, hCjx', hCeqx, -⟩ := id ht
                    obtain ⟨_, hidxLy, jy, Cy0, Cy0', hjy, hCjy, hCjy', hCeqy, -⟩ := id ht₁
                    have hjxy : jy = jx := by omega
                    rw [hjxy] at hCjy
                    obtain rfl : Cx0 = Cy0 := Option.some.inj (hCjx.symm.trans hCjy)
                    rw [← hteq2] at hCeqy hidxLy
                    have e1 := congrArg List.length hCeqx
                    have e2 := congrArg List.length hCeqy
                    rw [List.length_drop] at e1 e2
                    have hidx2 : x.idx = cp₁.idx := by omega
                    apply hxne
                    obtain ⟨xt, xi⟩ := x
                    obtain ⟨ct, ci⟩ := cp₁
                    simp only at hteq2 hidx2
                    rw [hteq2, hidx2]
                · rintro ⟨t, ht, htle⟩
                  exact ⟨t, ht, by omega⟩
              exact decide_eq_decide.mpr hiff
          omega
        · have hceq : points.countP (fun cp =>
              decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ jj + 1))
              = points.countP (fun cp =>
              decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ jj)) := by
            refine List.countP_congr fun x hx => ?_
            simp only [decide_eq_true_eq]
            constructor
            · rintro ⟨t, ht, htle⟩
              refine ⟨t, ht, ?_⟩
              rcases Nat.lt_or_ge t (jj + 1) with h | h
              · omega
              · exfalso
                have hteq : t = jj + 1 := by omega
                subst hteq
                exact hdrop ⟨x, hx, ht⟩
            · rintro ⟨t, ht, htle⟩
              exact ⟨t, ht, by omega⟩
          omega
  -- all points executed by `mw - 1`
  have hcall : points.countP (fun cp =>
      decide (∃ t, IsTimeOf (Config.run State.initial T) τ' cp t ∧ t ≤ mw - 1))
      = points.length := by
    rw [List.countP_eq_length]
    intro cp hcp
    rw [decide_eq_true_eq]
    obtain ⟨t, ht, htp⟩ := htimes cp hcp
    exact ⟨t, ht, by omega⟩
  -- the barrier's count, wherever initialized along `τ'`, is the unique init's `n`
  obtain ⟨ip, hipmem, hipcmd⟩ := initCountOf_some hn
  have hcount_n : ∀ (j : Nat) (sj2 : State) (Tj2 : CTA),
      τ'[j]? = some (Config.run sj2 Tj2) →
      ∀ n'', (sj2.BM sb).count = some n'' → n'' = n := by
    have hinvr : ∀ (j : Nat) (sj2 : State) (Tj2 : CTA),
        τ'[j]? = some (Config.run sj2 Tj2) →
        sj2.BM sb = MBarrierState.uninitialized ∨ (sj2.BM sb).count = some n := by
      intro j
      induction j with
      | zero =>
        intro sj2 Tj2 hj
        rw [htr0] at hj
        have heq := Option.some.inj hj
        rw [WeftCommon.Config.run.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Or.inl rfl
      | succ jj ih =>
        intro sj2 Tj2 hj
        have hjj : jj < τ'.length := by
          have := (List.getElem?_eq_some_iff.mp hj).1
          omega
        obtain ⟨Cp, hCp⟩ : ∃ C, τ'[jj]? = some C := ⟨_, List.getElem?_eq_getElem hjj⟩
        have hstep := chain_step hchain hCp hj
        obtain ⟨sp, Tp, rfl⟩ := hstep.source_run
        rcases ih sp Tp hCp with hun | hsome
        · rcases uninit_step hstep rfl rfl hun with h | ⟨i, ninit, rest, hdropI, hdropI'⟩
          · exact Or.inl h
          · refine Or.inr ?_
            have hsuf : (Config.run sp Tp).progOf i <:+
                (Config.run State.initial T).progOf i :=
              progOf_suffix_index_le hchain i htr0 (Nat.zero_le jj) hCp
            have hcmdp : T.cmdAt ⟨i, ((Config.run State.initial T).progOf i).length
                - ((Config.run sp Tp).progOf i).length⟩ = some (Cmd.init_mb sb ninit) :=
              cmd_at_last hsuf hdropI
            have hpeq := unique_init_of_check huniq (mem_progPoints_of_cmdAt T hcmdp)
              hipmem hcmdp hipcmd
            rw [hpeq, hipcmd] at hcmdp
            have hneq : ninit = n := by
              have := Option.some.inj hcmdp
              simp only [Cmd.init_mb.injEq] at this
              exact this.2.symm
            subst hneq
            obtain ⟨s2, T2, hC'eq, hcount⟩ :=
              init_drop_target_initialized hstep hdropI hdropI'
            have heq := hC'eq
            rw [WeftCommon.Config.run.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact hcount
        · exact Or.inr (count_some_persists hstep rfl rfl hsome)
    intro j sj2 Tj2 hj n'' hcnt
    rcases hinvr j sj2 Tj2 hj with hun | hsome
    · rw [hun] at hcnt
      simp [MBarrierState.uninitialized] at hcnt
    · rw [hsome] at hcnt
      exact (Option.some.inj hcnt).symm
  -- `arrived ≥ n` at the source of `w`'s execution step
  obtain ⟨sq, Tq, hCqrun⟩ := hrun (mw - 1) le_rfl
  have harrived : (n : Nat) ≤ (sq.BM sb).arrived := by
    have h := key (mw - 1) le_rfl sq Tq hCqrun
    rw [hcall, hlen] at h
    exact h
  -- analyse `w`'s execution step: pass needs under-full, wake needs a matching phase
  obtain ⟨Cq, Cq', hCq, hCq', hshape⟩ := time_drop_evidence hmw hcmdw
  have hmw1 : 1 ≤ mw := by
    obtain ⟨_, _, j, _, _, hj, _⟩ := hmw
    omega
  obtain rfl : Cq = Config.run sq Tq := Option.some.inj (hCq.symm.trans hCqrun)
  have hstepw : CTAStep (Config.run sq Tq) Cq' := by
    refine chain_step hchain hCq ?_
    rw [show mw - 1 + 1 = mw from by omega]
    exact hCq'
  -- the phase of `sb` at `mw - 1` is `phaseAfter (rc (mw - 1)) ≠ ph`
  have hphq : (sq.BM sb).phase = phaseAfter (recycleCount (.inr sb) τ' (mw - 1)) := by
    have h := phase_eq_phaseAfter hchain htr0 sb (mw - 1) (Config.run sq Tq) sq hCqrun rfl
    exact h
  cases hstepw with
  | @interleave _ s₁ _ i P' hi hbar hmbar hth =>
    simp only [WeftCommon.Config.progOf] at hshape
    by_cases hiw : w.thread = i
    · subst hiw
      simp only [WeftCommon.CTA.set, Function.update_self] at hshape
      rw [hshape] at hth
      cases hth with
      | @mb_wait_pass _ _ _ _ _ I' A' n'' ph'' he hb0 hnep =>
        -- the pass fires under `hmbar`: `sb` strictly under-full — contradiction
        rcases hmbar sb with hbu | ⟨I₂, A₂, n₂, ph₂, hbcfg, hlt₂⟩
        · rw [hbu] at hb0
          simp [MBarrierState.uninitialized] at hb0
        · have hn2 : n₂ = n := hcount_n (mw - 1) sq Tq hCqrun n₂ (by rw [hbcfg])
          have hn2' : (n₂ : Nat) = (n : Nat) := by rw [hn2]
          have hA2 : (sq.BM sb).arrived = A₂ := by rw [hbcfg]
          omega
    · exfalso
      simp only [WeftCommon.CTA.set, Function.update_of_ne hiw] at hshape
      have hl := congrArg List.length hshape
      simp only [List.length_cons] at hl
      omega
  | @recycle _ _ nb₀ I₃ A₃ n₃ hb hfull hpark =>
    exfalso
    simp only [WeftCommon.Config.progOf] at hshape
    by_cases h : w.thread ∈ I₃
    · have hpk := hpark w.thread h
      rw [hshape] at hpk
      simp at hpk
    · simp only [WeftCommon.CTA.wake, if_neg h] at hshape
      have hl := congrArg List.length hshape
      simp only [List.length_cons] at hl
      omega
  | @mb_recycle _ _ sb₀ I₃ A₃ n₃ ph₃ hb hfull hpark =>
    simp only [WeftCommon.Config.progOf] at hshape
    by_cases h : w.thread ∈ I₃
    · -- the wake: `w` was parked at the *matching* phase — contradiction
      have hpk := hpark w.thread h
      rw [hshape] at hpk
      simp only [List.head?_cons, Option.some.injEq, Cmd.wait_mb.injEq] at hpk
      obtain ⟨rfl, rfl⟩ := hpk
      have hph3 : (sq.BM sb).phase = ph := by rw [hb]
      rw [hphq] at hph3
      exact hrwph hph3
    · exfalso
      simp only [WeftCommon.CTA.wake, if_neg h] at hshape
      have hl := congrArg List.length hshape
      simp only [List.length_cons] at hl
      omega
  | @done _ _ hdone2 _ _ =>
    exfalso
    simp only [WeftCommon.Config.progOf] at hshape
    have hnil : Tq.prog w.thread = [] := by
      by_cases hti : w.thread ∈ Tq.ids
      · exact hdone2 w.thread hti
      · exact Tq.nil_outside_ids w.thread hti
    rw [hnil] at hshape
    simp at hshape
  | @error _ _ i P' _ _ hth =>
    exfalso
    simp only [WeftCommon.Config.progOf] at hshape
    have hl := congrArg List.length hshape
    simp only [List.length_cons] at hl
    omega

/-! ## Correctness of Algorithm 2 (`CheckWellSynchronized`)

The two directions and their assembly, mirroring the named-barrier development
(its Theorems 1 and 2):

* **soundness** (§5.2.6) — a successful run of the check witnesses
  well-synchronization: the checked orderings force every schedule to assign
  each synchronization command its reference generation;
* **completeness** (§5.2.7) — a failing run witnesses a violation: a failing
  registrant or wait check exposes a pair the happens-before relation does not
  order, and a reversing schedule then changes the generation map. -/

/-- **Soundness of Algorithm 2.** If `τ` is a complete trace from `(I, T)` ending
in `done` (`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ` returns
`true`, then `T` is well-synchronized.

Note (rohany): This is a top-level theorem.
-/
theorem wellSynchronized_of_check {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = true) :
    T.WellSynchronized := by
  refine ⟨⟨State.initial, T, rfl⟩, ?_⟩
  intro τ₁ τ₂ hτ₁ hτ₂ η hbar
  obtain ⟨b, hbarb⟩ := hbar
  have hbar' : (T.cmdAt η).bind Cmd.barrier? = some b := hbarb
  obtain ⟨c, hcm, hcbar⟩ : ∃ c, T.cmdAt η = some c ∧ c.barrier? = some b := by
    cases hc : T.cmdAt η with
    | none => rw [hc] at hbar'; exact absurd hbar' (by simp)
    | some c =>
      rw [hc] at hbar'
      exact ⟨c, rfl, by simpa using hbar'⟩
  have hmem : η ∈ T.progPoints := mem_progPoints_of_cmdAt T hcm
  have hidx : η.idx < (T.prog η.thread).length := ((mem_progPoints_iff T η).mp hmem).2
  -- both challenger traces conform (Theorem 6) and end `done` (Theorem 7)
  have hc₁ : Conforms T τ τ₁ := conforms_of_traceFrom hτ hcheck ⟨hτ₁.1.subtrace, hτ₁.2⟩
  have hc₂ : Conforms T τ τ₂ := conforms_of_traceFrom hτ hcheck ⟨hτ₂.1.subtrace, hτ₂.2⟩
  obtain ⟨s₁, hd₁⟩ := conforms_complete_done hτ hτ₁ hc₁
  obtain ⟨s₂, hd₂⟩ := conforms_complete_done hτ hτ₂ hc₂
  -- `η` executes in each, and clause 1 transports the reference generation
  obtain ⟨m₁, hm₁⟩ := exists_time_of_ends_done hτ₁ hd₁ hidx
  obtain ⟨m₂, hm₂⟩ := exists_time_of_ends_done hτ₂ hd₂ hidx
  have hg₁ : pointGen T τ₁ η = pointGen T τ η :=
    hc₁.gen_eq η hmem m₁ (pointTime_eq_of_isTimeOf hm₁)
  have hg₂ : pointGen T τ₂ η = pointGen T τ η :=
    hc₂.gen_eq η hmem m₂ (pointTime_eq_of_isTimeOf hm₂)
  -- the reference generation is a `some` (η executes in the successful τ)
  obtain ⟨sd, hdone⟩ := hτ.2
  obtain ⟨mτ, hmτ⟩ := exists_time_of_ends_done hτ.1 hdone hidx
  obtain ⟨gτ, hgτ⟩ : ∃ gτ : ℤ, pointGen T τ η = some gτ :=
    ⟨_, pointGen_eq_of_time hcm hcbar hmτ⟩
  refine ⟨gτ, ?_, ?_⟩
  · have h := isGenOf_pointGen hcm hcbar hm₁
    rwa [hg₁, hgτ] at h
  · have h := isGenOf_pointGen hcm hcbar hm₂
    rwa [hg₂, hgτ] at h

/-- **Completeness of Algorithm 2.** If `τ` is a complete trace from `(I, T)`
ending in `done` (`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ`
returns `false`, then `T` is *not* well-synchronized.

Note (rohany): This is a top-level theorem.
-/
theorem not_wellSynchronized_of_check_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    ¬ T.WellSynchronized := by
  intro hws
  by_cases huq : okUniqueInitCheck T τ = true
  · rcases check_false_cases hcheck with hf | hf | hf | hf
    · -- mode 1: the registrant check
      obtain ⟨c1, hc1, b, g, hreg1, c2, hc2, hreg2, hcase⟩ := exists_failing_reg_pair hf
      rcases hcase with ⟨hidx, hne3, hnotmem⟩ | hidx0
      · obtain ⟨cmd1, hcmd1, hisreg1, hbar1, hgen1⟩ := registrantGen_some hreg1
        obtain ⟨cmd2, hcmd2, hisreg2, hbar2, hgen2⟩ := registrantGen_some hreg2
        have hnothb3 : ¬ happensBefore T τ c1 ⟨c2.thread, c2.idx - 1⟩ :=
          not_happensBefore_of_not_mem hne3 hnotmem
        cases cmd2 with
        | read l => simp [Cmd.isRegistrant] at hisreg2
        | write l => simp [Cmd.isRegistrant] at hisreg2
        | init_mb sb' n' => simp [Cmd.isRegistrant] at hisreg2
        | wait_mb sb' ph' => simp [Cmd.isRegistrant] at hisreg2
        | arrive_nb nb m =>
          -- an `arrive_nb` target has only the program-order in-edge from `c3`
          have hnothb2 : ¬ happensBefore T τ c1 c2 := by
            intro h
            rcases happensBefore_arrive_nb hcmd2 hidx h with heq | h3
            · rw [heq] at hgen1
              have := Option.some.inj (hgen1.symm.trans hgen2)
              omega
            · exact hnothb3 h3
          exact reverse_barrier_contradiction hτ hws hc1 hc2 hcmd1 hisreg1 hbar1
            hcmd2 hbar2 hgen1 hgen2 hnothb2
        | arrive_mb sb' =>
          -- likewise for an `arrive_mb` target
          have hnothb2 : ¬ happensBefore T τ c1 c2 := by
            intro h
            rcases happensBefore_arrive_mb hcmd2 hidx h with heq | h3
            · rw [heq] at hgen1
              have := Option.some.inj (hgen1.symm.trans hgen2)
              omega
            · exact hnothb3 h3
          exact reverse_barrier_contradiction hτ hws hc1 hc2 hcmd1 hisreg1 hbar1
            hcmd2 hbar2 hgen1 hgen2 hnothb2
        | sync_nb nb m =>
          have hbeq : b = .inl nb := by
            have h := hbar2
            simp only [Cmd.barrier?, Option.some.injEq] at h
            exact h.symm
          subst hbeq
          by_cases hhb : happensBefore T τ c1 c2
          · -- forced after `c1`: the competing operational reversal, per `c1`'s kind
            cases cmd1 with
            | read l => simp [Cmd.isRegistrant] at hisreg1
            | write l => simp [Cmd.isRegistrant] at hisreg1
            | init_mb sb' n' => simp [Cmd.isRegistrant] at hisreg1
            | wait_mb sb' ph' => simp [Cmd.isRegistrant] at hisreg1
            | arrive_mb sb' =>
              have h := hbar1
              simp only [Cmd.barrier?, Option.some.injEq] at h
              exact absurd h (by simp)
            | arrive_nb nb1 m1 =>
              have hbeq1 : nb1 = nb := by
                have h := hbar1
                simp only [Cmd.barrier?, Option.some.injEq, Sum.inl.injEq] at h
                exact h
              subst hbeq1
              exact competing_arrive_sync_false hτ hws hc1 hc2 hcmd1 hcmd2 hgen1 hgen2
                hidx hnothb3 hhb
            | sync_nb nb1 m1 =>
              have hbeq1 : nb1 = nb := by
                have h := hbar1
                simp only [Cmd.barrier?, Option.some.injEq, Sum.inl.injEq] at h
                exact h
              subst hbeq1
              exact competing_sync_false hτ hws hc1 hc2 hcmd1 hcmd2 hgen1 hgen2
                hidx hnothb3 hhb
          · exact reverse_barrier_contradiction hτ hws hc1 hc2 hcmd1 hisreg1 hbar1
              hcmd2 hbar2 hgen1 hgen2 hhb
      · exact firstInstr_highGen_not_wellSynchronized hτ hws hc1 hreg1 hc2 hreg2 hidx0
    · -- mode 2: the wait checks
      obtain ⟨w, hw, sb, ph, g, hcmdw, hgenw, hcase⟩ := exists_failing_wait hf
      rcases hcase with ⟨hg1, hidx0⟩ |
        ⟨hg1, hidx, c, hcmem, hregc, hne3, hnotmem⟩ | ⟨n, hn, hlen, hnone⟩
      · -- 2a: a first-instruction wait errs at once
        exact firstInstr_use_not_wellSynchronized hidx0 (by rw [hcmdw]; rfl) hws
      · -- 2b: the lower bound, sync-shaped
        obtain ⟨cmdc, hcmdc, hisregc, hbarc, hgenc⟩ := registrantGen_some hregc
        have hnothb3 : ¬ happensBefore T τ c ⟨w.thread, w.idx - 1⟩ :=
          not_happensBefore_of_not_mem hne3 hnotmem
        -- the registrant on `.inr sb` is an `arrive_mb sb`
        cases cmdc with
        | read l => simp [Cmd.isRegistrant] at hisregc
        | write l => simp [Cmd.isRegistrant] at hisregc
        | init_mb sb' n' => simp [Cmd.isRegistrant] at hisregc
        | wait_mb sb' ph' => simp [Cmd.isRegistrant] at hisregc
        | arrive_nb nb1 m1 =>
          have h := hbarc
          simp only [Cmd.barrier?, Option.some.injEq] at h
          exact absurd h (by simp)
        | sync_nb nb1 m1 =>
          have h := hbarc
          simp only [Cmd.barrier?, Option.some.injEq] at h
          exact absurd h (by simp)
        | arrive_mb sb' =>
          have hsbeq : sb' = sb := by
            have h := hbarc
            simp only [Cmd.barrier?, Option.some.injEq, Sum.inr.injEq] at h
            exact h
          subst hsbeq
          by_cases hhb : happensBefore T τ c w
          · exact competing_arrive_wait_false hτ hws hcmem hw hcmdc hcmdw hgenc hgenw
              hidx hnothb3 hhb
          · have hgenw' : pointGen T τ w = some (g - 1 + 1) := by
              rw [show g - 1 + 1 = g from by omega]
              exact hgenw
            exact reverse_barrier_contradiction hτ hws hcmem hw hcmdc hisregc hbarc
              hcmdw rfl hgenc hgenw' hhb
      · -- 2c: the upper bound
        exact wait_upper_bound_false hτ hws huq hw hcmdw hgenw hn hlen hnone
    · -- mode 3: initialization ordering (uniqueness holds here)
      obtain ⟨ci, hci, sb, n, hcmdi, u, hu, huse, hcase⟩ := exists_failing_init_pair hf
      rcases hcase with ⟨hidx1, hnepred, hnotmem⟩ | hidx0
      · have hnpred : ¬ happensBefore T τ ci ⟨u.thread, u.idx - 1⟩ :=
          not_happensBefore_of_not_mem hnepred hnotmem
        by_cases hbu : happensBefore T τ ci u
        · exact init_pred_unordered_err_false hτ hws huq hci hu hcmdi huse
            hidx1 hnpred hbu
        · have hnotmemu : (ci, u) ∉ (CheckWellSynchronized T τ).2 := by
            intro hmem
            rw [snd_checkWellSynchronized] at hmem
            exact hbu (mem_transClosure_imp_transGen _ hmem).to_reflTransGen
          exact init_ordering_false hτ hws huq hci hu hcmdi huse hnotmemu
      · exact firstInstr_use_not_wellSynchronized hidx0 huse hws
    · rw [huq] at hf
      exact absurd hf (by simp)
  · -- mode 4: duplicate initializations
    rw [Bool.not_eq_true] at huq
    obtain ⟨ci, hci, sb, n, hcmdi, cj, hcj, n', hcmdj, hne⟩ := exists_failing_dup_init huq
    exact unique_init_false hτ hci hcj hcmdi hcmdj hne

/-- **Correctness of `CheckWellSynchronized`** (soundness and completeness
combined). For a CTA `T` with a successful trace `τ`, the checker accepts iff
`T` is well-synchronized. This aggregates soundness
(`wellSynchronized_of_check`, the `check = true → WS` direction) and
completeness (`not_wellSynchronized_of_check_false`, the `check = false → ¬WS`
direction).

Implementation of the top-level `WeftMBarriers.checkWellSynchronized_correct`
(in `WeftMBarriers.lean`). -/
theorem checkWellSynchronized_correct_impl {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ) :
    (CheckWellSynchronized T τ).1 = true ↔ T.WellSynchronized := by
  refine ⟨wellSynchronized_of_check hτ, fun hws => ?_⟩
  by_contra hne
  rw [Bool.not_eq_true] at hne
  exact not_wellSynchronized_of_check_false hτ hne hws

end WeftMBarriers

