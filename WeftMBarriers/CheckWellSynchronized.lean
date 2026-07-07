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
  and if the next generation has any registrants (`Reg(sb, g+1) ≠ ∅`), `w`
  must happen-before one of them (lines 29–30) — an upper bound pinning `w`
  before the completion of `g + 1`.
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

export WeftCommon (transClosureStep transClosure)

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
some next-generation registrant, when any exists). The
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
        -- lines 29–30: if the next generation has registrants, `w` must
        -- happen-before one of them (the upper bound; `w` is never a
        -- registrant, so no reflexivity accommodation is needed).
        (let regNext : List ProgPoint := T.progPoints.filter fun cp =>
            registrantGen T τ cp = some (.inr sb, g + 1)
         regNext.isEmpty || regNext.any fun cp => decide ((w, cp) ∈ hb))
    | _, _ => true
  -- Step 5 (beyond Algorithm 2): every use of an mbarrier happens-after its
  -- initialization. An uninitialized `arrive_mb`/`wait_mb` is an error, so a
  -- schedule in which a use is not forced after the `init_mb` can err while
  -- the witness trace `τ` succeeded. (An `init_mb` point is never itself a
  -- use — the commands differ — so no reflexivity accommodation is needed.)
  let okInit : Bool := T.progPoints.all fun ci =>
    match T.cmdAt ci with
    | some (.init_mb sb _) =>
        T.progPoints.all fun u =>
          if (T.cmdAt u).bind Cmd.usesMBarrier? = some sb then
            decide ((ci, u) ∈ hb)
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
  sorry

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
  sorry

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

end WeftMBarriers
