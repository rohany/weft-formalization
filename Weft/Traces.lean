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
the Weft paper — specifically Definition 1 (partial traces / subtraces) and
Definition 2 (complete traces).

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

end Weft
