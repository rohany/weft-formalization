/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftNamedBarriers.State
import WeftCommon.Traces

/-!
# The Weft operational semantics (§3.3)

This file formalizes the small-step operational semantics of Section 3.3
("Semantics") of the Weft paper. There are two judgment forms:

```
        E, B, T  ⤳  E', B', T'           -- a CTA T takes one step
     E, B, i, P  ⤳  E', B', i, P'         -- thread i with program P takes one step
```

A configuration pairs a state `s = (E, B)` with a CTA `T`. The two distinguished
terminal results are `done` (the state is kept, the CTA collapses to "no more
commands") and `err` (the state becomes the error state, the CTA is kept) — see
`Config`. The CTA-level `interleave` rule nondeterministically picks one thread,
runs it for a single thread-level step, and splices the result back in; this is
only allowed while every barrier is unconfigured or still under-registered. When
some barrier is exactly full it must instead be recycled — *recycling has
priority over every other rule*, including error propagation (see the deviation
note below).

## Thread-level rules (`ThreadStep`)

* `read_noop` / `write_noop` — `read g; c ⤳ c` and `write g; c ⤳ c`; `read`/
  `write` are no-ops for the barrier semantics, merely advancing the program.
* `arrive_configure` — first thread to register at an unconfigured barrier via
  `arrive`: `E(id) = true`, `B(b) = ([],0,⊥)`, set `B' = B[([], 1, n)/b]`,
  advance to `c`. (The `E(id) = true` premise is explicit here, beyond the paper.)
* `arrive_register` — subsequent non-blocking arrive: `E(id) = true`,
  `B(b) = (I,A,n)` with `0 < |I|+A < n`, set `B' = B[(I, A+1, n)/b]`, advance
  to `c`. (`A` is now a count, so an arrival just increments it.)
* `sync_configure` — first thread to register at an unconfigured barrier via
  `sync`: `E(id) = true`, `E' = E[false/id]`, `B(b) = ([],0,⊥)`,
  `B' = B[([id], 0, n)/b]`; control stays at `sync b n; c` (thread now blocked).
* `sync_block` — subsequent blocking sync: `E(id) = true`, `E' = E[false/id]`,
  `B(b) = (I,A,n)` with `0 < |I|+A < n`, `B' = B[(I::id, A, n)/b]`; control
  stays at `sync b n; c`.
* `sync_err_count` — thread-count mismatch: `E(id) = true`, `B(b) = (I,A,n)`,
  `n ≠ m` ⇒ `sync b m; c` steps to `err`.
* `arrive_err_count` — the error production for `arrive`, identical to the
  `sync` one.

## CTA-level rules (`CTAStep`)

* `interleave` — if every barrier is unconfigured or under-registered
  (`∀ b. B(b) = ([],0,⊥) ∨ (B(b) = (I,A,n) ∧ |I|+A < n)`), pick a thread and run
  it one (non-error) step, splicing `Pᵢ'` back into the CTA.
* `recycle` — if some barrier `B(b) = (I,A,n)` has `|I|+A = n`, wake every thread
  blocked on it: set `E' = E[true/I]`, advance each thread in `I` past its
  `sync b n`, and reset the barrier to `([],0,⊥)`.
* `done` — `E, B, return ‖ … ‖ return ⤳ E, B, done`.
* `error` — if any thread produces `err`, the whole CTA goes to `err`; guarded by
  the *same* all-barriers-under-full condition as `interleave`.

## Deviation from the paper: recycle has priority over the error productions

The paper's err productions carry no barrier condition, and it also has
"too many threads" productions (`sync`/`arrive` at a barrier with `|I|+|A| = n`
step to `err`). Together these make the paper's own Theorem 1 false: a full
barrier is a *transient* state that the semantics is about to recycle (the
`interleave` guard exists exactly so no thread can act on it), yet an unguarded
err production lets a thread observe it and abort instead. Counterexample: the
single thread `[arrive b 1, sync b 1]` passes `WELLSYNC` (generations 1 and 2,
and the sync's predecessor *is* the generation-1 arrive), but after the `arrive`
fills `b` the still-enabled thread could take the full-barrier err production in
a race with the pending recycle, deadlocking Definition 6. On hardware the race
does not exist — a completed named barrier "is immediately re-initialized"
(§2.2), so fullness is never observable.

We therefore (i) guard `CTAStep.error` with the `interleave` barrier condition —
recycling a full barrier fires before any thread may observe it, erroring
included — and (ii) drop the two "too many threads" productions
(`sync_err_full` / `arrive_err_full`), which the guard makes unreachable at the
CTA level (they require a full barrier; the guard forbids one). Genuine
over-subscription is still caught by well-synchronization: the surplus
registrant lands in a fresh generation and either deadlocks (generation `0`) or
shifts generations between schedules. The count-mismatch productions
(`sync_err_count` / `arrive_err_count`) remain, firing — under the guard — from
ordinarily-reachable states.

(Multi-step closure `⤳*`, traces, and timing are §4, out of scope here.)
-/

namespace Weft

/-- A thread-level configuration `E, B, i, P` (or the error result `err, i, P`).
A thread program `P` of thread `i` runs against a state `s = (E, B)`. -/
inductive ThreadConfig where
  /-- `E, B, i, P`: thread `i` running program `P` in state `s`. -/
  | run (s : State) (i : ThreadId) (P : Prog)
  /-- `err, i, P`: thread `i` has produced the error state. -/
  | err (i : ThreadId) (P : Prog)

/-- A CTA-level configuration: the shared functor `WeftCommon.Config`
instantiated at this language's states and commands. Following the paper,
`done` keeps the state and collapses the CTA, whereas `err` replaces the state
with the error state but keeps the CTA. The constructors (and `progOf`) are
re-exported below under their usual names. -/
abbrev Config := WeftCommon.Config State Cmd

namespace Config
export WeftCommon.Config (run done err noConfusion
  run.injEq done.injEq err.injEq run.inj done.inj err.inj)
end Config

/-- The thread-level small-step relation `E, B, i, P  ⤳  E', B', i, P'` of §3.3.

Each constructor is one inference rule; see the module doc for the correspondence
to the paper. `read`/`write` are no-ops; `arrive` is non-blocking; `sync` blocks
(disabling the thread and leaving its control parked at the `sync`) until the
barrier is recycled. -/
inductive ThreadStep : ThreadConfig → ThreadConfig → Prop where
  /-- `read g` is a no-op for the barrier semantics: just advance the program. -/
  | read_noop {s : State} {i : ThreadId} {g : Loc} {c : Prog} :
      ThreadStep (.run s i (Cmd.read g :: c)) (.run s i c)
  /-- `write g` is a no-op for the barrier semantics: just advance the program. -/
  | write_noop {s : State} {i : ThreadId} {g : Loc} {c : Prog} :
      ThreadStep (.run s i (Cmd.write g :: c)) (.run s i c)
  /-- First thread to register at an unconfigured barrier `b` via `arrive`:
  configure `b` with count `n`, set the arrived count to `1`, advance to `c`.
  The enabledness premise `E(id) = true` is stronger than the paper, which leaves
  it implicit (a thread reaching an `arrive` is necessarily enabled); we require
  it explicitly, matching the `sync` rules. -/
  | arrive_configure {s : State} {i : ThreadId} {b : Barrier} {n : ℕ+} {c : Prog}
      (he : s.E i = true)
      (hb : s.B b = BarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.arrive b n :: c))
        (.run { s with B := Function.update s.B b ⟨[], 1, some n⟩ } i c)
  /-- Subsequent non-blocking `arrive` at a configured, not-yet-full barrier:
  increment the arrived count, advance to `c`. As in `arrive_configure`, the
  enabledness premise `E(id) = true` is required explicitly, beyond the paper. -/
  | arrive_register {s : State} {i : ThreadId} {b : Barrier} {n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A) (hlt : I.length + A < (n : Nat)) :
      ThreadStep (.run s i (Cmd.arrive b n :: c))
        (.run { s with B := Function.update s.B b ⟨I, A + 1, some n⟩ } i c)
  /-- First thread to register at an unconfigured barrier `b` via `sync`:
  configure `b` with count `n`, disable the thread (`E[false/id]`), add `id` to
  the synced list; control stays parked at `sync b n; c`. -/
  | sync_configure {s : State} {i : ThreadId} {b : Barrier} {n : ℕ+} {c : Prog}
      (he : s.E i = true)
      (hb : s.B b = BarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.sync b n :: c))
        (.run { E := Function.update s.E i false,
                B := Function.update s.B b ⟨[i], 0, some n⟩ } i (Cmd.sync b n :: c))
  /-- Subsequent blocking `sync` at a configured, not-yet-full barrier: disable
  the thread, add `id` to the synced list; control stays parked at `sync b n; c`. -/
  | sync_block {s : State} {i : ThreadId} {b : Barrier} {n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A) (hlt : I.length + A < (n : Nat)) :
      ThreadStep (.run s i (Cmd.sync b n :: c))
        (.run { E := Function.update s.E i false,
                B := Function.update s.B b ⟨i :: I, A, some n⟩ } i (Cmd.sync b n :: c))
  /-- Thread-count mismatch on `b`: barrier expects `n` but `sync b m` has `n ≠ m`;
  step to `err`. (The paper's companion "too many threads" production
  `sync_err_full` is deliberately absent — see the module doc's deviation note.) -/
  | sync_err_count {s : State} {i : ThreadId} {b : Barrier} {m n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.sync b m :: c)) (.err i (Cmd.sync b m :: c))
  /-- The `arrive` analogue of `sync_err_count` (identical, per the paper). -/
  | arrive_err_count {s : State} {i : ThreadId} {b : Barrier} {m n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.arrive b m :: c)) (.err i (Cmd.arrive b m :: c))

/-- The CTA-level small-step relation `E, B, T  ⤳  E', B', T'` of §3.3. -/
inductive CTAStep : Config → Config → Prop where
  /-- Interleaving: while every barrier is unconfigured or still under-registered,
  nondeterministically choose a thread and run it for one (non-error) thread step,
  splicing the resulting program and state back into the CTA. -/
  | interleave {s s' : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hi : i ∈ T.ids)
      (hbar : ∀ b, s.B b = BarrierState.unconfigured ∨
                   ∃ I A n, s.B b = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
      (hstep : ThreadStep (.run s i (T.prog i)) (.run s' i P')) :
      CTAStep (.run s T) (.run s' (T.set i hi P'))
  /-- Recycle: when barrier `b` has registered exactly its expected count
  (`|I|+A = n`), wake every thread blocked on it (`E' = E[true/I]`), advance each
  such thread past its parked `sync b n`, and reset `b` to unconfigured. -/
  | recycle {s : State} {T : CTA} {b : Barrier} {I : List ThreadId} {A : ℕ} {n : ℕ+}
      (hb : s.B b = ⟨I, A, some n⟩)
      (hfull : I.length + A = (n : Nat))
      (hpark : ∀ i ∈ I, (T.prog i).head? = some (Cmd.sync b n)) :
      CTAStep (.run s T)
        (.run { E := updateMapOn s.E I true,
                B := Function.update s.B b BarrierState.unconfigured }
              (T.wake I))
  /-- Termination: when every thread has reached `return`, the CTA is `done` —
  *provided* no barrier is left completed-but-not-recycled. The premise `hnofull`
  requires every configured barrier to be strictly under-full (`|I|+A < n`): a
  barrier that has reached its expected count must be recycled (`CTAStep.recycle`,
  always available for a full barrier) before the CTA may terminate, so completed
  barriers always advance their generation and return to the unconfigured state
  rather than being torn down full. (Under-full barriers, whose generation never
  completes, may remain at termination.) -/
  | done {s : State} {T : CTA} (hdone : CTA.IsDone T)
      (hnofull : ∀ b I A n, s.B b = ⟨I, A, some n⟩ → I.length + A < (n : Nat)) :
      CTAStep (.run s T) (.done s)
  /-- Error propagation: if any thread produces `err`, so does the whole CTA. The
  rule carries the *same* barrier condition as `interleave` (`hbar`): when some
  barrier is exactly full, only `recycle` may fire — no thread may observe the
  transient full state, erroring included. See the module doc's deviation note
  (the paper's unguarded err productions make its Theorem 1 false). -/
  | error {s : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hbar : ∀ b, s.B b = BarrierState.unconfigured ∨
                   ∃ I A n, s.B b = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
      (hstep : ThreadStep (.run s i (T.prog i)) (.err i P')) :
      CTAStep (.run s T) (.err T)

@[inherit_doc ThreadStep] scoped infix:40 " ⤳ₜ " => ThreadStep
@[inherit_doc CTAStep] scoped infix:40 " ⤳ " => CTAStep

end Weft
