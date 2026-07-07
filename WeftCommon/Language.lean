/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Function.Basic

/-!
# The language-independent core of the Weft languages

The Weft language family (the named-barrier language of the PLDI 2015 paper,
and its mbarrier extension from §5.2 of the weft++ theorems document) shares
everything except the command set, the barrier state, and the step rules. This
file collects the shared *syntax-side* core, parameterized by the command type
`Cmd` where a command is mentioned at all:

* shared-memory locations `Loc` and thread identifiers `ThreadId`;
* program points `ProgPoint` — static instruction names `⟨thread, index⟩`;
* the CTA functor `CTA Cmd` — a finite thread domain with a total program map —
  together with its update operations `set`, `wake`, `empty` and the
  termination predicate `IsDone`, none of which inspect a command;
* the set-update helper `updateMapOn` realizing the papers' `f[x/Y]` notation.

Each language instantiates `CTA` at its own `Cmd` (and re-exports these names
into its namespace), so the two languages literally share these types — a
trace lemma proved over `CTA Cmd` applies to both.
-/

namespace WeftCommon

/-- Shared-memory variable locations, denoted `g` in the paper. For simplicity
the paper assumes all variables occupy 64 bits; the identity of a location is
all that matters for the syntax, so we use names. -/
abbrev Loc := String

/-- Thread identifiers, denoted `id` (and ranged over by `i`). Each thread
program has a separate thread identifier (equivalent to `threadIdx.x` for the
one-dimensional CTAs common in warp-specialized kernels). -/
abbrev ThreadId := Nat

/-- A program point (§3.1): a *static* position in a thread's pre-execution
program, identified by the thread and an index into that thread's initial command
list. The point `⟨i, k⟩` names instruction `k` of thread `i` — the command
`cη = (C₀.progOf i)[k]` of the program `C₀.progOf i` at the start `C₀` of the
trace — and the point just after it. Being an index into the initial program, it
is a stable, trace-independent name, so a happens-before fact relates two such
points directly. -/
structure ProgPoint where
  /-- The thread that the program point belongs to. -/
  thread : ThreadId
  /-- The index of the command, into the thread's program at the start of the
  trace; the point sits just after that command. -/
  idx : Nat
  deriving DecidableEq, Repr

/-- A CTA `T = P₁ ‖ P₂ ‖ … ‖ P_N`: the parallel composition of its threads,
parameterized by the language's command type `Cmd` (a thread program is a
`List Cmd`; the empty program `[]` is the paper's `return`).

It pairs a finite domain `ids` (the thread identifiers that exist — the `N`
threads of the CTA, so `N = ids.card`) with a *total* program map `prog`, so
lookups never fail (`prog i` always; a terminated thread maps to the empty
program `[]`). The field `nil_outside_ids` couples the two: outside `ids` the
program is empty, i.e. the support of `prog` is contained in `ids`. Hence there
are no "ghost" threads with work outside the domain, `ids` is the fixed set of
the CTA's threads (a terminated thread stays in `ids` with `prog i = []`), and we
can both read/update a thread by id and quantify over the real threads via
`ids`. A CTA has at least one thread (`ids_nonempty`), matching the paper's `N`
threads. -/
structure CTA (Cmd : Type) where
  /-- The thread identifiers present in this CTA — its (finite) domain. -/
  ids : Finset ThreadId
  /-- Each thread's remaining program; total, with terminated ids mapping to `[]`. -/
  prog : ThreadId → List Cmd
  /-- Coupling invariant: a thread outside the domain has no program left, so
  every thread with remaining work is in `ids`. -/
  nil_outside_ids : ∀ i ∉ ids, prog i = []
  /-- A CTA has at least one thread — its domain is nonempty (`N ≥ 1` in the
  paper). Preserved by every step, since `ids` never changes. -/
  ids_nonempty : ids.Nonempty

namespace CTA

variable {Cmd : Type}

/-- Update one in-domain thread's program, keeping the domain `ids`. The
membership hypothesis `hi` is what lets us re-establish the coupling invariant. -/
def set (T : CTA Cmd) (i : ThreadId) (hi : i ∈ T.ids) (P : List Cmd) : CTA Cmd where
  ids := T.ids
  prog := Function.update T.prog i P
  nil_outside_ids := by
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    rw [Function.update_of_ne hji]
    exact T.nil_outside_ids j hj
  ids_nonempty := T.ids_nonempty

/-- Wake the threads blocked at a recycling barrier: every thread in `I` drops its
leading (parked blocking) command, others are unchanged. The domain is preserved,
and the coupling holds because outside `ids` the program is already `[]` (and
`[].tail = []`). -/
def wake (T : CTA Cmd) (I : List ThreadId) : CTA Cmd where
  ids := T.ids
  prog := fun j => if j ∈ I then (T.prog j).tail else T.prog j
  ids_nonempty := T.ids_nonempty
  nil_outside_ids := by
    intro j hj
    have hnil : T.prog j = [] := T.nil_outside_ids j hj
    by_cases h : j ∈ I <;> simp [h, hnil]

/-- The **empty CTA** on a thread set `ids`: every thread's program is empty. It carries no
instructions, so it is the unit of sequential composition (`empty ⨾ T` and `T ⨾ empty` have `T`'s
program up to `[]`-append) and is trivially well-synchronized. -/
def empty (ids : Finset ThreadId) (hne : ids.Nonempty) : CTA Cmd where
  ids := ids
  prog := fun _ => []
  nil_outside_ids := fun _ _ => rfl
  ids_nonempty := hne

/-- `done`: a CTA with no more commands to execute, i.e. every thread in the
domain has reached `return` (the empty command list `[]`). -/
def IsDone (T : CTA Cmd) : Prop := ∀ i ∈ T.ids, T.prog i = []

end CTA

/-- Map update over a set of keys, realizing the paper's `f[x/Y]`: the map that
agrees with `f` on all inputs not in `Y`, and maps every `y ∈ Y` to `x`. Built as
an iterated `Function.update` so it inherits that primitive's lemmas. (The
single-key update `f[x/y]` is just `Function.update f y x` directly.) -/
def updateMapOn {α β : Type} [DecidableEq α]
    (f : α → β) (Y : List α) (x : β) : α → β :=
  Y.foldr (fun y g => Function.update g y x) f

end WeftCommon
