/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Language

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

export WeftCommon (Loc ThreadId)

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

/-- The CTA type of the mbarrier-extended language: the shared functor
`WeftCommon.CTA` (finite thread domain + total program map; see its
documentation) instantiated at this language's commands. Its operations
`set`/`wake`/`empty` and the termination predicate `IsDone` are the shared
ones (`empty`/`IsDone` re-exported below; `set`/`wake` resolve by dot
notation through the abbreviation). -/
abbrev CTA := WeftCommon.CTA Cmd

namespace CTA
export WeftCommon.CTA (empty IsDone)
end CTA

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
