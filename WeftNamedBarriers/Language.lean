/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Language

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

export WeftCommon (Loc ThreadId)

/-- Named-barrier identifiers, denoted `b`. The hardware provides `B` (typically
16) named barriers; `b` refers to a specific barrier name. -/
abbrev Barrier := Nat

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
  threads at this generation. The count `n : ℕ+` is positive by construction: the
  paper rejects `n = 0` in a preprocessing phase, and an `arrive b 0` would
  configure a barrier that can never recycle. (`n` may still exceed the number of
  threads — a thread can register at the same barrier multiple times.) -/
  | arrive (b : Barrier) (n : ℕ+)
  /-- `sync b n`: blocking synchronization at barrier `b`, which expects `n : ℕ+`
  threads at this generation (positive by construction; see `arrive`). -/
  | sync (b : Barrier) (n : ℕ+)
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

/-- The CTA type of the named-barrier language: the shared functor
`WeftCommon.CTA` (finite thread domain + total program map; see its
documentation) instantiated at this language's commands. Its operations
`set`/`wake`/`empty` and the termination predicate `IsDone` are re-exported
below under their usual names. -/
abbrev CTA := WeftCommon.CTA Cmd

namespace CTA
export WeftCommon.CTA (empty IsDone)
end CTA

namespace Cmd

/-- A command is a synchronization command (`sync`/`arrive`) as opposed to a
memory access (`read`/`write`). -/
def isSync : Cmd → Bool
  | .arrive .. | .sync .. => true
  | .read .. | .write .. => false

end Cmd

/-- The standard CTA-wide barrier `__syncthreads()` is expressed as `sync 0 N`:
a blocking sync on barrier `0` across all `N` threads of the CTA, where `N : ℕ+`
is the (positive) expected thread count. -/
def syncthreads (N : ℕ+) : Cmd := .sync 0 N

end Weft
