/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Logic.Function.Basic

/-!
# The Weft++ source language with shared-memory barriers (§5.2, Figure 3)

This file formalizes the *syntax* of the abstract thread-program language
extended with shared-memory barriers (mbarriers), from §5.2 (Figure 3) of the
weft++ theorems document. The base language is that of the Weft paper (PLDI
2015): <https://lightsighter.org/pdfs/weft.pdf>.

A GPU program consists of an arbitrary number of non-interfering CTAs. Each CTA
has `N` threads (typically 32–1024) that synchronize for access to shared
memory. We model abstract thread programs in which everything has been
abstracted away except the instructions needed to reason about synchronization
and shared-memory accesses.

The grammar (Figure 3) is:

```
  P  ::=  return | c; P
  c  ::=  read g | write g
       |  arrive_nb nb n | sync_nb nb n
       |  init_mb sb n | arrive_mb sb | wait_mb sb ph
```

Per the papers:
* A thread program `P` is a sequence of commands (straight-line code) ending in
  `return`.
* `read g` / `write g` read/write a shared-memory location `g`. These are
  treated as no-ops for the barrier semantics; they exist only so that
  data races can be detected.
* `sync_nb nb n` is a *blocking* synchronization on named barrier `nb` expecting
  `n` threads; `arrive_nb nb n` is the *non-blocking* variant.
* For the named synchronization commands, the first argument `nb` is the barrier
  name and the second argument `n` is the expected number of threads to register
  at this generation of the barrier.
* `init_mb sb n` configures the shared-memory barrier (mbarrier) `sb` with
  arrival count `n` and phase `0`; initializing an already-initialized mbarrier
  is an error.
* `arrive_mb sb` is a *non-blocking* arrival on mbarrier `sb`. Arrivers are
  recorded as a *list*, so a thread may arrive on the same mbarrier more than
  once within a generation.
* `wait_mb sb ph` waits on mbarrier `sb` at phase `ph`: it *blocks* (parking the
  thread among `sb`'s waiters) when `ph` matches the barrier's current phase —
  i.e. the phase-`ph` generation is still collecting arrivals — and is a no-op
  when the phase has already advanced (`MB-Wait-Pass`).
* A CTA `T = P₁ || P₂ || … || P_N` is the parallel composition of its thread
  programs, each carrying its own thread identifier `id`.
-/

namespace WeftMBarriers

/-- Shared-memory variable locations, denoted `g` in the paper. For simplicity
the paper assumes all variables occupy 64 bits; the identity of a location is
all that matters for the syntax, so we use names. -/
abbrev Loc := String

/-- Named-barrier identifiers, denoted `nb`. The hardware provides `NB`
(typically 16) named barriers; `nb` refers to a specific barrier name. -/
abbrev NamedBarrier := Nat

/-- Shared-memory-barrier (mbarrier) identifiers, denoted `sb`. An mbarrier
lives at a shared-memory location; `sb` refers to a specific one of the `SB`
shared barrier names. Named and shared barriers form *separate* namespaces
(the state carries two maps, `BN` and `BM`). -/
abbrev SharedBarrier := Nat

/-- An mbarrier phase bit, denoted `ph ∈ {0, 1}`: `false` is phase `0` and
`true` is phase `1`. Each mbarrier recycle flips the phase (`ph ⊕ 1 = !ph`), so
an mbarrier returns to its initial state only after *two* recycles — the phase
bit is what doubles the loop period, `fₘ(b) = 2 · f(b)` (§5.2.2). -/
abbrev Phase := Bool

/-- Thread identifiers, denoted `id` (and ranged over by `i`). Each thread
program has a separate thread identifier (equivalent to `threadIdx.x` for the
one-dimensional CTAs common in warp-specialized kernels). -/
abbrev ThreadId := Nat

/-- A single command `c`.

```
  c  ::=  read g | write g
       |  arrive_nb nb n | sync_nb nb n
       |  init_mb sb n | arrive_mb sb | wait_mb sb ph
```
-/
inductive Cmd where
  /-- `read g`: read shared-memory location `g` (a no-op for barrier semantics). -/
  | read (g : Loc)
  /-- `write g`: write shared-memory location `g` (a no-op for barrier semantics). -/
  | write (g : Loc)
  /-- `arrive_nb nb n`: non-blocking registration at named barrier `nb`, which
  expects `n` threads at this generation. The count `n : ℕ+` is positive by
  construction: the paper rejects `n = 0` in a preprocessing phase, and an
  `arrive_nb nb 0` would configure a barrier that can never recycle. (`n` may
  still exceed the number of threads — a thread can register at the same barrier
  multiple times.) -/
  | arrive_nb (nb : NamedBarrier) (n : ℕ+)
  /-- `sync_nb nb n`: blocking synchronization at named barrier `nb`, which
  expects `n : ℕ+` threads at this generation (positive by construction; see
  `arrive_nb`). -/
  | sync_nb (nb : NamedBarrier) (n : ℕ+)
  /-- `init_mb sb n`: configure mbarrier `sb` with arrival count `n` and phase
  `0`; initializing an already-initialized mbarrier is an error. The count
  `n : ℕ+` is positive by construction (see `arrive_nb`): an mbarrier expecting
  `0` arrivals would be perpetually ready to recycle. -/
  | init_mb (sb : SharedBarrier) (n : ℕ+)
  /-- `arrive_mb sb`: non-blocking arrival on mbarrier `sb`. Unlike `arrive_nb`
  it carries no expected count — that was fixed by `init_mb` — and arrivers form
  a *list*, so the same thread may arrive more than once within a generation. -/
  | arrive_mb (sb : SharedBarrier)
  /-- `wait_mb sb ph`: wait on mbarrier `sb` at phase `ph`. Blocks (parking the
  thread among `sb`'s waiters) when `ph` is the barrier's current phase, and
  passes through as a no-op when the phase has already advanced. -/
  | wait_mb (sb : SharedBarrier) (ph : Phase)
  deriving DecidableEq, Repr, Inhabited

/-- A thread program `P`: straight-line code, a sequence of commands separated by
`;` and terminated by `return`.

```
  P  ::=  return | c; P
```

This grammar is exactly a list of commands, so we *are* a `List Cmd`: the empty
program `[]` is the paper's `return` (a thread "terminates by executing a
return"), and `c :: P` is the paper's `c; P`. Reusing `List` gives us its full
API and lemmas (`length`, `++`, membership, indexing, induction) for free, which
the trace/timing arguments of §4 will need. -/
abbrev Prog := List Cmd

/-- A CTA `T = P₁ ‖ P₂ ‖ … ‖ P_N`: the parallel composition of its threads.

It pairs a finite domain `ids` (the thread identifiers that exist — the `N`
threads of the CTA, so `N = ids.card`) with a *total* program map `prog`, so
lookups never fail (`prog i : Prog` always; a terminated thread maps to the empty
program `[]`). The field `nil_outside_ids` couples the two: outside `ids` the
program is empty, i.e. the support of `prog` is contained in `ids`. Hence there
are no "ghost" threads with work outside the domain, `ids` is the fixed set of
the CTA's threads (a terminated thread stays in `ids` with `prog i = []`), and we
can both read/update a thread by id and quantify over the real threads via
`ids`. A CTA has at least one thread (`ids_nonempty`), matching the paper's `N`
threads. -/
structure CTA where
  /-- The thread identifiers present in this CTA — its (finite) domain. -/
  ids : Finset ThreadId
  /-- Each thread's remaining program; total, with terminated ids mapping to `[]`. -/
  prog : ThreadId → Prog
  /-- Coupling invariant: a thread outside the domain has no program left, so
  every thread with remaining work is in `ids`. -/
  nil_outside_ids : ∀ i ∉ ids, prog i = []
  /-- A CTA has at least one thread — its domain is nonempty (`N ≥ 1` in the
  paper). Preserved by every step, since `ids` never changes. -/
  ids_nonempty : ids.Nonempty

namespace CTA

/-- Update one in-domain thread's program, keeping the domain `ids`. The
membership hypothesis `hi` is what lets us re-establish the coupling invariant. -/
def set (T : CTA) (i : ThreadId) (hi : i ∈ T.ids) (P : Prog) : CTA where
  ids := T.ids
  prog := Function.update T.prog i P
  nil_outside_ids := by
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    rw [Function.update_of_ne hji]
    exact T.nil_outside_ids j hj
  ids_nonempty := T.ids_nonempty

/-- Wake the threads blocked at a recycling barrier: every thread in `I` drops its
leading (parked `sync_nb` or `wait_mb`) command, others are unchanged. The domain
is preserved, and the coupling holds because outside `ids` the program is already
`[]` (and `[].tail = []`). -/
def wake (T : CTA) (I : List ThreadId) : CTA where
  ids := T.ids
  prog := fun j => if j ∈ I then (T.prog j).tail else T.prog j
  ids_nonempty := T.ids_nonempty
  nil_outside_ids := by
    intro j hj
    have hnil : T.prog j = [] := T.nil_outside_ids j hj
    by_cases h : j ∈ I <;> simp [h, hnil]

end CTA

/-- The **empty CTA** on a thread set `ids`: every thread's program is empty. It carries no
instructions, so it is the unit of sequential composition (`empty ⨾ T` and `T ⨾ empty` have `T`'s
program up to `[]`-append) and is trivially well-synchronized. -/
def CTA.empty (ids : Finset ThreadId) (hne : ids.Nonempty) : CTA where
  ids := ids
  prog := fun _ => []
  nil_outside_ids := fun _ _ => rfl
  ids_nonempty := hne

namespace Cmd

/-- A command is a synchronization command (a named-barrier or mbarrier
operation) as opposed to a memory access (`read`/`write`). -/
def isSync : Cmd → Bool
  | .arrive_nb .. | .sync_nb .. | .init_mb .. | .arrive_mb .. | .wait_mb .. => true
  | .read .. | .write .. => false

end Cmd

/-- The standard CTA-wide barrier `__syncthreads()` is expressed as `sync_nb 0 N`:
a blocking sync on named barrier `0` across all `N` threads of the CTA, where
`N : ℕ+` is the (positive) expected thread count. -/
def syncthreads (N : ℕ+) : Cmd := .sync_nb 0 N

end WeftMBarriers
