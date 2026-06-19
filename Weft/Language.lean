/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic

/-!
# The Weft source language (§3.1)

This file formalizes the *syntax* of the abstract thread-program language from
Section 3.1 ("Syntax") of the Weft paper (PLDI 2015):
<https://lightsighter.org/pdfs/weft.pdf>.

A GPU program consists of an arbitrary number of non-interfering CTAs. Each CTA
has `N` threads (typically 32–1024) that synchronize for access to shared
memory. We model abstract thread programs in which everything has been
abstracted away except the instructions needed to reason about synchronization
and shared-memory accesses.

The paper's grammar is:

```
  P  ::=  return | c; P
  c  ::=  read g | write g
       |  arrive b n | sync b n
```

Per the paper:
* A thread program `P` is a sequence of commands (straight-line code) ending in
  `return`.
* `read g` / `write g` read/write a shared-memory location `g`. These are
  treated as no-ops for the named-barrier semantics; they exist only so that
  data races can be detected.
* `sync b n` is a *blocking* synchronization on named barrier `b` expecting `n`
  threads; `arrive b n` is the *non-blocking* variant.
* For the synchronization commands, the first argument `b` is the barrier name
  and the second argument `n` is the expected number of threads to register at
  this generation of the barrier.
* A CTA `T = P₁ || P₂ || … || P_N` is the parallel composition of its thread
  programs, each carrying its own thread identifier `id`.
-/

namespace Weft

/-- Shared-memory variable locations, denoted `g` in the paper. For simplicity
the paper assumes all variables occupy 64 bits; the identity of a location is
all that matters for the syntax, so we use names. -/
abbrev Loc := String

/-- Named-barrier identifiers, denoted `b`. The hardware provides `B` (typically
16) named barriers; `b` refers to a specific barrier name. -/
abbrev Barrier := Nat

/-- Thread identifiers, denoted `id` (and ranged over by `i`). Each thread
program has a separate thread identifier (equivalent to `threadIdx.x` for the
one-dimensional CTAs common in warp-specialized kernels). -/
abbrev ThreadId := Nat

/-- A single command `c`.

```
  c  ::=  read g | write g | arrive b n | sync b n
```
-/
inductive Cmd where
  /-- `read g`: read shared-memory location `g` (a no-op for barrier semantics). -/
  | read (g : Loc)
  /-- `write g`: write shared-memory location `g` (a no-op for barrier semantics). -/
  | write (g : Loc)
  /-- `arrive b n`: non-blocking registration at barrier `b`, which expects `n`
  threads at this generation. -/
  | arrive (b : Barrier) (n : Nat)
  /-- `sync b n`: blocking synchronization at barrier `b`, which expects `n`
  threads at this generation. -/
  | sync (b : Barrier) (n : Nat)
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
program `[]`). The field `nil_of_not_mem` couples the two: outside `ids` the
program is empty, i.e. the support of `prog` is contained in `ids`. Hence there
are no "ghost" threads with work outside the domain, `ids` is the fixed set of
the CTA's threads (a terminated thread stays in `ids` with `prog i = []`), and we
can both read/update a thread by id and quantify over the real threads via
`ids`. -/
structure CTA where
  /-- The thread identifiers present in this CTA — its (finite) domain. -/
  ids : Finset ThreadId
  /-- Each thread's remaining program; total, with terminated ids mapping to `[]`. -/
  prog : ThreadId → Prog
  /-- Coupling invariant: a thread outside the domain has no program left, so
  every thread with remaining work is in `ids`. -/
  nil_of_not_mem : ∀ i ∉ ids, prog i = []

namespace CTA

/-- Update one in-domain thread's program, keeping the domain `ids`. The
membership hypothesis `hi` is what lets us re-establish the coupling invariant. -/
def set (T : CTA) (i : ThreadId) (hi : i ∈ T.ids) (P : Prog) : CTA where
  ids := T.ids
  prog := Function.update T.prog i P
  nil_of_not_mem := by
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    rw [Function.update_of_ne hji]
    exact T.nil_of_not_mem j hj

/-- Wake the threads blocked at a recycling barrier: every thread in `I` drops its
leading (parked `sync`) command, others are unchanged. The domain is preserved,
and the coupling holds because outside `ids` the program is already `[]` (and
`[].tail = []`). -/
def wake (T : CTA) (I : List ThreadId) : CTA where
  ids := T.ids
  prog := fun j => if j ∈ I then (T.prog j).tail else T.prog j
  nil_of_not_mem := by
    intro j hj
    have hnil : T.prog j = [] := T.nil_of_not_mem j hj
    by_cases h : j ∈ I <;> simp [h, hnil]

end CTA

namespace Cmd

/-- A command is a synchronization command (`sync`/`arrive`) as opposed to a
memory access (`read`/`write`). -/
def isSync : Cmd → Bool
  | .arrive .. | .sync .. => true
  | .read .. | .write .. => false

end Cmd

/-- The standard CTA-wide barrier `__syncthreads()` is expressed as `sync 0 N`:
a blocking sync across all `N` threads in the CTA on barrier `0`. -/
def syncthreads (N : Nat) : Cmd := .sync 0 N

end Weft
