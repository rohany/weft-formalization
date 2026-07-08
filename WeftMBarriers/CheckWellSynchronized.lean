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
  sorry

/-- **Completeness of Algorithm 2.** If `τ` is a complete trace from `(I, T)`
ending in `done` (`τ ≡ (I, T) ⤳* (F, done)`) and `CheckWellSynchronized T τ`
returns `false`, then `T` is *not* well-synchronized.

Note (rohany): This is a top-level theorem.
-/
theorem not_wellSynchronized_of_check_false {T : CTA} {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial T) τ)
    (hcheck : (CheckWellSynchronized T τ).1 = false) :
    ¬ T.WellSynchronized := by
  sorry

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

