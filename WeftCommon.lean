/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Language
import WeftCommon.Traces

/-!
# WeftCommon — the shared core of the Weft language family

Language-independent definitions shared by the named-barrier language
(`WeftNamedBarriers`) and its mbarrier extension (`WeftMBarriers`): locations,
thread identifiers, program points, the CTA and configuration functors, and the
§4.1 trace definitions parameterized by a step relation. Each language
instantiates these at its own `State`/`Cmd`/`CTAStep` under its usual names.
-/
