/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Traces
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union

/-!
# Well-synchronization (Definitions 6–7, §4.1), language-independently

The *well-synchronized* property is the same statement for every language of
the Weft family: any two complete executions assign every synchronization
command the same, nonzero generation. What varies between languages is

* the step relation `R` (through `IsCompleteTraceFrom`),
* which commands are synchronization commands and which barrier they operate
  on — the classifier `barrier? : Cmd → Option β`, where the barrier name type
  `β` is also the language's (for the mbarrier-extended language, the sum
  `NamedBarrier ⊕ SharedBarrier` of its two name spaces), and
* the *generation* relation `GenOf C₀ τ η g` — Definition 5 — whose counting
  is genuinely language-specific (named barriers count recycles-to-unconfigured;
  mbarriers count phase flips, with the phase-corrected observation of §5.2.3),
  as is the generation *value type* `γ` itself.

`WellSynchronized` here is Definition 7 parameterized by exactly those three;
each language instantiates it under its usual name with its own `CTAStep`,
`Cmd.barrier?`, and `IsGenOf` (Definition 6 — the CTA-level property at the
language's initial state — stays language-side, since the initial state does
too).

**`Option`-valued generations.** `GenOf C₀ τ η g` relates a command to
`g : Option γ`: `some n` when the command executes in `τ` with generation `n`,
and `none` when it never executes (deadlock). Well-synchronization then simply
demands a *shared `some`* — no sentinel value is reserved, so the generation
value type `γ` is completely abstract here: the named-barrier language
instantiates `γ := ℕ` (1-indexed, aligning with its computable `pointGen`),
while the mbarrier language is free to use `γ := ℤ`, where the phase-corrected
observation of §5.2.3 makes generations `−1` and `0` legitimately observable.
A deadlocked command still refutes well-synchronization: it relates only to
`none`, and `GenOf`'s functionality leaves no `some` witness.
-/

namespace WeftCommon

variable {State Cmd β : Type}

/-- Definition 7 (§4.1), parameterized by the language: a configuration `C₀` is
*well-synchronized* (with respect to a step relation `R`, a synchronization
classifier `barrier?`, and a generation relation `GenOf`) if it is a `run`
configuration and any two complete traces from it assign every synchronization
command the same generation `some g` — in particular the command executes in
both.

The first conjunct requires `C₀` to be a `run` configuration (Def 7's
`(s, T)`). Without it, a terminal `err` configuration with no synchronization
commands would satisfy the rest vacuously and be "well-synchronized" while not
even able to make progress. -/
def WellSynchronized {γ : Type} (R : Config State Cmd → Config State Cmd → Prop)
    (barrier? : Cmd → Option β)
    (GenOf : Config State Cmd → List (Config State Cmd) → ProgPoint → Option γ → Prop)
    (C₀ : Config State Cmd) : Prop :=
  (∃ s T, C₀ = Config.run s T) ∧
  ∀ τ₁ τ₂, IsCompleteTraceFrom R C₀ τ₁ → IsCompleteTraceFrom R C₀ τ₂ →
    ∀ η : ProgPoint, (∃ b, (η.cmd C₀).bind barrier? = some b) →
      ∃ g : γ, GenOf C₀ τ₁ η (some g) ∧ GenOf C₀ τ₂ η (some g)

/-! ## Transitive closure of a finite edge relation

The checking algorithms (Figure 4 line 17, Algorithm 2 line 17) close their
finite edge relation `R` under transitivity; the construction is generic. -/

/-- One saturation round: add a composed edge `(e.1, f.2)` whenever `e ∈ S` and
`f ∈ R` meet at `e.2 = f.1`. -/
def transClosureStep {α : Type*} [DecidableEq α] (R S : Finset (α × α)) : Finset (α × α) :=
  S ∪ S.biUnion fun e => (R.filter fun f => e.2 = f.1).image fun f => (e.1, f.2)

/-- The transitive closure of a relation given as a finite set of edges `R`:
repeatedly add a composed edge `(e.1, f.2)` whenever `e ∈ S` and `f ∈ R` meet at
`e.2 = f.1`. Saturating for `R.card` rounds suffices, since a simple path uses at
most `|R|` edges. -/
def transClosure {α : Type*} [DecidableEq α] (R : Finset (α × α)) : Finset (α × α) :=
  (transClosureStep R)^[R.card] R

end WeftCommon
