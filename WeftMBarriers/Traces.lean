/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.Semantics

/-!
# Execution traces (§4.1) for the mbarrier-extended language

The trace definitions of Section 4.1 — Definition 1 (partial traces /
subtraces), Definition 2 (complete traces), Definition 3 (time), and
Definition 4 (sound-and-precise happens-before) — live language-independently
in `WeftCommon.Traces`, parameterized by a step relation; see that file for the
full documentation. This file instantiates them at the mbarrier-extended
language's step relation `CTAStep` under their usual (unparameterized) names,
exactly as `WeftNamedBarriers.Traces` does for the named-barrier language.
`Config`, `Config.progOf`, and `ProgPoint` are likewise the shared ones
(`Config` is instantiated in `WeftMBarriers.Semantics`; `ProgPoint` is
re-exported here).

Note the timing subtlety specific to this language: a `wait_mb` that *blocks*
gets its time from the `MB-Recycle` step that wakes it (like a named `sync`),
whereas a `wait_mb` that *passes* (`MB-Wait-Pass`) is timed like an ordinary
non-blocking command — both fall out of Definition 3 automatically, since the
time is simply the step that drops the instruction from the thread's program.
-/

namespace WeftMBarriers

export WeftCommon (ProgPoint)

namespace ProgPoint
export WeftCommon.ProgPoint (mk cmd thread idx mk.injEq)
end ProgPoint

/-- Definition 1 (§4.1), instantiated: a *partial trace* (or *subtrace*) of the
mbarrier-extended step relation. See `WeftCommon.IsSubtrace`. -/
abbrev IsSubtrace (τ : List Config) : Prop := WeftCommon.IsSubtrace CTAStep τ

/-- A configuration with no `CTAStep`-successor. See `WeftCommon.Config.Stuck`. -/
abbrev Config.Stuck (C : Config) : Prop := WeftCommon.Config.Stuck CTAStep C

/-- Definition 2 (§4.1), instantiated: a *complete trace* of the
mbarrier-extended language. See `WeftCommon.IsCompleteTrace`. -/
abbrev IsCompleteTrace (τ : List Config) : Prop := WeftCommon.IsCompleteTrace CTAStep τ

/-- A complete trace starting from `C₀`. See `WeftCommon.IsCompleteTraceFrom`. -/
abbrev IsCompleteTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  WeftCommon.IsCompleteTraceFrom CTAStep C₀ τ

/-- A partial trace starting from `C₀`. See `WeftCommon.IsTraceFrom`. -/
abbrev IsTraceFrom (C₀ : Config) (τ : List Config) : Prop :=
  WeftCommon.IsTraceFrom CTAStep C₀ τ

/-- Definition 3 (§4.1), instantiated: the time `t(τ, η) = n` of instruction `η`
in a complete mbarrier-language trace `τ` from `C₀`. See `WeftCommon.IsTimeOf`. -/
abbrev IsTimeOf (C₀ : Config) (τ : List Config) (η : ProgPoint) (n : Nat) : Prop :=
  WeftCommon.IsTimeOf CTAStep C₀ τ η n

/-- Definition 4 (§4.1), instantiated: `R` is *sound and precise* for the
mbarrier-extended language relative to `C₀`. See `WeftCommon.SoundAndPrecise`. -/
abbrev SoundAndPrecise (C₀ : Config) (R : ProgPoint → ProgPoint → Prop) : Prop :=
  WeftCommon.SoundAndPrecise CTAStep C₀ R

end WeftMBarriers
