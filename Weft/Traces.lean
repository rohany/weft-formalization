/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.Semantics
import Mathlib.Data.List.Chain

/-!
# Execution traces (§4.1)

This file formalizes the trace definitions from Section 4.1 ("Preliminaries") of
the Weft paper: Definition 1 (partial traces / subtraces), Definition 2 (complete
traces), Definition 3 (time), and Definition 4 (sound-and-precise happens-before).

The paper abbreviates `E, B, T` as `(s, T)` and calls a state-and-CTA pair a
*configuration* `C`; the distinguished terminal configurations `done` and `err`
are configurations too. Our `Config` type (from `Weft.Semantics`) already captures
all of these — `Config.run s T`, `Config.done s`, `Config.err T` — and the
one-step relation `⤳` is `CTAStep`. So a trace is just a sequence of `Config`s in
which successive entries are related by `⤳`.

## Definition 1 — subtraces

A *partial trace* (or *subtrace*) is a sequence of configurations
`(s₀, T₀), …, (sₙ, Tₙ)` such that every two successive configurations satisfy
`(sⱼ, Tⱼ) ⤳ (sⱼ₊₁, Tⱼ₊₁)`. We model the sequence as a `List Config` and the
"successive configurations step" condition as `List.IsChain CTAStep`.

## Definition 2 — complete traces

A *complete trace* ends in `done`, `err`, or a *deadlock* (a non-`done`
configuration from which no rule applies). We state these three cases explicitly
in `IsCompleteTrace.ends`. They are, in fact, exactly the **stuck** configurations
— those with no `⤳`-successor — since no `CTAStep` rule has `done` or `err` on its
left, and a deadlock is a stuck `run` configuration; `Config.Stuck` alone would
therefore suffice, but listing the three is closer to the paper and lets a caller
read off which outcome occurred from the final `Config`'s constructor (`done` =
success, `err` = error, `run` = deadlock).

So a complete trace is a subtrace whose last configuration is terminal; its
starting configuration is just `τ.head?`.

## Program points

A *program point* (§3.1) sits just after a command. We name it **statically**, by
an index into the thread's program *at the start of the trace*: `⟨i, k⟩` is
instruction `k` of thread `i` — the command `cη = (C₀.progOf i)[k]` of the
pre-execution program `C₀.progOf i` — and the point just after it. Because a
thread runs its straight-line commands in order, after executing instructions
`0 … k-1` its remaining program is exactly `(C₀.progOf i).drop k`
(`= cη :: (C₀.progOf i).drop (k+1)`). Indexing into the initial program gives a
*stable, trace-independent* name for each instruction — exactly what a
happens-before fact relates — and `ProgPoint.cmd` recovers the command `cη`.

## Definition 3 — time

`t(τ, η) = n` is the step at which thread `η.thread` executes its instruction
`η.idx` in a trace `τ` *starting from `C₀`*: the `n`-th step takes that thread's
remaining program from `(C₀.progOf i).drop η.idx` to `(C₀.progOf i).drop (η.idx+1)`,
i.e. drops the head `cη`. For `read`/`write`/`arrive` this is the step that runs
the command; for `sync` the program only advances past the (parked) `sync` when
the barrier is recycled, so `t` is the recycle step — this falls out
automatically, since that head can only be dropped by `CTAStep.recycle`. We model
`t(τ, η) = n` as `IsTimeOf C₀ τ η n`, which carries `IsCompleteTraceFrom C₀ τ` as
a premise so it stands on its own (a partial function: undefined when instruction
`η` is never executed in `τ`).

## Definition 4 — sound and precise happens-before

Relative to a start configuration `C₀`, a relation `R` on (static) program points
is *sound and precise* when `R η₁ η₂` holds iff in every complete trace from `C₀`
the time of `η₁` is `≤` the time of `η₂`. Since program points are indices into
`C₀`'s programs, `R` relates two fixed pre-execution instructions, and the same
`R η₁ η₂` can be reused trace by trace. (We read "`t(τ,η₁) ≤ t(τ,η₂)`" as a
constraint only on traces where both times are defined; an unexecuted command
imposes no constraint.) The `≤` — rather than `<` — means simultaneously executed
commands (e.g. `sync`s that synchronize together, recycled at the same step) are
related in both directions (`SoundAndPrecise`).
-/

namespace Weft

/-- Definition 1 (§4.1). A *partial trace* or *subtrace* is a sequence of
configurations in which every two successive configurations are related by a
single CTA step `⤳`. The sequence is a `List Config`; "successive configurations
step" is `List.IsChain CTAStep`. -/
def IsSubtrace (τ : List Config) : Prop := List.IsChain CTAStep τ

/-- A configuration is *stuck* if no CTA step applies from it. By Definition 2,
the terminal configurations — `done`, `err`, and deadlocked `run` configs — are
exactly the stuck ones: no `CTAStep` rule fires from `done` or `err`, and a
deadlock is a stuck `run` configuration. -/
def Config.Stuck (C : Config) : Prop := ¬ ∃ C', CTAStep C C'

/-- Definition 2 (§4.1). A *complete trace* is a subtrace whose last configuration
is terminal: it is `done` (success), `err` (error), or a deadlock (`Config.Stuck`
— a configuration, in practice a `run`, from which no rule applies). The starting
configuration is simply `τ.head?`, and the endpoint condition forces `τ` to be
nonempty. -/
structure IsCompleteTrace (τ : List Config) : Prop where
  /-- The sequence is a subtrace: successive configurations step (Definition 1). -/
  subtrace : IsSubtrace τ
  /-- The trace ends in one of the three terminal configurations: `done`, `err`,
  or a stuck (deadlocked) configuration. -/
  ends : ∃ Cₙ, τ.getLast? = some Cₙ ∧
    ((∃ s, Cₙ = Config.done s) ∨ (∃ T, Cₙ = Config.err T) ∨ Config.Stuck Cₙ)

/-- A complete trace `τ` that *starts from* a given configuration `C₀` — the form
"a complete trace starting from a configuration `(s, T)`" used in Definition 2.
This is just `IsCompleteTrace τ` together with the constraint that `C₀` is the
trace's first configuration. -/
def IsCompleteTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  IsCompleteTrace τ ∧ τ.head? = some C₀

/-- A *partial* trace that starts from `C₀` (Definition 1, relativized to a starting
configuration): a subtrace whose first configuration is `C₀`, with no requirement on how
it ends. The nonempty prefixes of any (complete or partial) trace from `C₀` are exactly
the `IsTraceFrom C₀` lists; a forward induction over an execution — such as the
conformance invariant of Theorem 1's soundness proof — is an induction over these. -/
def IsTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  IsSubtrace τ ∧ τ.head? = some C₀

/-- Thread `i`'s remaining program in a configuration. For a running or errored
configuration it is `T.prog i`; the `done` configuration has every thread at
`return`, so its program is `[]`. -/
def Config.progOf : Config → ThreadId → Prog
  | .run _ T, i => T.prog i
  | .err T, i => T.prog i
  | .done _, _ => []

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

/-- The command `cη` at program point `η`, read from the initial program
`C₀.progOf η.thread`; `none` if the index is out of range. -/
def ProgPoint.cmd (C₀ : Config) (η : ProgPoint) : Option Cmd :=
  (C₀.progOf η.thread)[η.idx]?

/-- Definition 3 (§4.1). The time `t(τ, η) = n` of instruction `η` in a complete
trace `τ` from `C₀`: the `n`-th step of `τ` (the transition from configuration
index `j = n-1` to `j+1`) executes instruction `η.idx` of thread `η.thread`,
advancing its remaining program from `(C₀.progOf η.thread).drop η.idx` (which is
`cη :: …`) to `(C₀.progOf η.thread).drop (η.idx + 1)`.

The `IsCompleteTraceFrom` premise makes the definition self-contained — time is
only meaningful along an actual complete trace from `C₀` — so it can be used
independently of `SoundAndPrecise`. The index guard requires the instruction to
exist (without it an out-of-range index would spuriously match two `[]` programs).
On such a trace this is a partial function of `(C₀, τ, η)` — at most one `n`
satisfies it (the program only shrinks), and none does if `η` is never executed.
For a `sync` the qualifying step is the barrier recycle, since only
`CTAStep.recycle` can drop a parked `sync` head. -/
def IsTimeOf (C₀ : Config) (τ : List Config) (η : ProgPoint) (n : Nat) : Prop :=
  IsCompleteTraceFrom C₀ τ ∧
  η.idx < (C₀.progOf η.thread).length ∧
  ∃ j C C', n = j + 1 ∧
    τ[j]? = some C ∧ τ[j + 1]? = some C' ∧
    C.progOf η.thread = (C₀.progOf η.thread).drop η.idx ∧
    C'.progOf η.thread = (C₀.progOf η.thread).drop (η.idx + 1)

/-- Definition 4 (§4.1). Relative to a starting configuration `C₀`, a candidate
happens-before relation `R` on (static) program points is *sound and precise*
when, for every pair `η₁ η₂`, `R η₁ η₂` holds iff in every complete trace from
`C₀` the time of `η₁` is `≤` the time of `η₂` (whenever both are executed). The
`≤` includes commands that execute simultaneously. -/
def SoundAndPrecise (C₀ : Config) (R : ProgPoint → ProgPoint → Prop) : Prop :=
  ∀ η₁ η₂ : ProgPoint,
    R η₁ η₂ ↔
      ∀ τ, IsCompleteTraceFrom C₀ τ →
        ∀ n₁ n₂, IsTimeOf C₀ τ η₁ n₁ → IsTimeOf C₀ τ η₂ n₂ → n₁ ≤ n₂

end Weft
