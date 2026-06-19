/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.State

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
some barrier is exactly full it must instead be recycled, and a thread that
produces an error propagates `err` to the whole CTA (independent of the barrier
condition).

## Thread-level rules (`ThreadStep`)

* `read_noop` / `write_noop` — `read g; c ⤳ c` and `write g; c ⤳ c`; `read`/
  `write` are no-ops for the barrier semantics, merely advancing the program.
* `arrive_configure` — first thread to register at an unconfigured barrier via
  `arrive`: `B(b) = ([],[],⊥)`, set `B' = B[([], [id], n)/b]`, advance to `c`.
* `arrive_register` — subsequent non-blocking arrive: `B(b) = (I,A,n)` with
  `0 < |I|+|A| < n`, set `B' = B[(I, A::id, n)/b]`, advance to `c`.
* `sync_configure` — first thread to register at an unconfigured barrier via
  `sync`: `E(id) = true`, `E' = E[false/id]`, `B(b) = ([],[],⊥)`,
  `B' = B[([id], [], n)/b]`; control stays at `sync b n; c` (thread now blocked).
* `sync_block` — subsequent blocking sync: `E(id) = true`, `E' = E[false/id]`,
  `B(b) = (I,A,n)` with `0 < |I|+|A| < n`, `B' = B[(I::id, A, n)/b]`; control
  stays at `sync b n; c`.
* `sync_err_full` — too many threads: `E(id) = true`, `B(b) = (I,A,n)`,
  `|I|+|A| = n` ⇒ step to `err`.
* `sync_err_count` — thread-count mismatch: `E(id) = true`, `B(b) = (I,A,n)`,
  `n ≠ m` ⇒ `sync b m; c` steps to `err`.
* `arrive_err_full` / `arrive_err_count` — the error productions for `arrive`,
  identical to the `sync` ones.

## CTA-level rules (`CTAStep`)

* `interleave` — if every barrier is unconfigured or under-registered
  (`∀ b. B(b) = ([],[],⊥) ∨ (B(b) = (I,A,n) ∧ |I|+|A| < n)`), pick a thread and run
  it one (non-error) step, splicing `Pᵢ'` back into the CTA.
* `recycle` — if some barrier `B(b) = (I,A,n)` has `|I|+|A| = n`, wake every thread
  blocked on it: set `E' = E[true/I]`, advance each thread in `I` past its
  `sync b n`, and reset the barrier to `([],[],⊥)`.
* `done` — `E, B, return ‖ … ‖ return ⤳ E, B, done`.
* `error` — if any thread produces `err`, the whole CTA goes to `err`.

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

/-- A CTA-level configuration. Following the paper, `done` keeps the state and
collapses the CTA, whereas `err` replaces the state with the error state but
keeps the CTA. -/
inductive Config where
  /-- `E, B, T`: CTA `T` running in state `s`. -/
  | run (s : State) (T : CTA)
  /-- `E, B, done`: the CTA has no more commands to execute. -/
  | done (s : State)
  /-- `err, T`: the error state, carrying the CTA `T`. -/
  | err (T : CTA)

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
  configure `b` with count `n`, add `id` to the arrived list, advance to `c`. -/
  | arrive_configure {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      (hb : s.B b = BarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.arrive b n :: c))
        (.run { s with B := Function.update s.B b ⟨[], [i], some n⟩ } i c)
  /-- Subsequent non-blocking `arrive` at a configured, not-yet-full barrier:
  add `id` to the arrived list, advance to `c`. -/
  | arrive_register {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      {I A : List ThreadId}
      (hb : s.B b = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A.length) (hlt : I.length + A.length < n) :
      ThreadStep (.run s i (Cmd.arrive b n :: c))
        (.run { s with B := Function.update s.B b ⟨I, i :: A, some n⟩ } i c)
  /-- First thread to register at an unconfigured barrier `b` via `sync`:
  configure `b` with count `n`, disable the thread (`E[false/id]`), add `id` to
  the synced list; control stays parked at `sync b n; c`. -/
  | sync_configure {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      (he : s.E i = true)
      (hb : s.B b = BarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.sync b n :: c))
        (.run { E := Function.update s.E i false,
                B := Function.update s.B b ⟨[i], [], some n⟩ } i (Cmd.sync b n :: c))
  /-- Subsequent blocking `sync` at a configured, not-yet-full barrier: disable
  the thread, add `id` to the synced list; control stays parked at `sync b n; c`. -/
  | sync_block {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      {I A : List ThreadId}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A.length) (hlt : I.length + A.length < n) :
      ThreadStep (.run s i (Cmd.sync b n :: c))
        (.run { E := Function.update s.E i false,
                B := Function.update s.B b ⟨i :: I, A, some n⟩ } i (Cmd.sync b n :: c))
  /-- Too many threads register at `b` via `sync` (`|I|+|A| = n`): step to `err`. -/
  | sync_err_full {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      {I A : List ThreadId}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hfull : I.length + A.length = n) :
      ThreadStep (.run s i (Cmd.sync b n :: c)) (.err i (Cmd.sync b n :: c))
  /-- Thread-count mismatch on `b`: barrier expects `n` but `sync b m` has `n ≠ m`;
  step to `err`. -/
  | sync_err_count {s : State} {i : ThreadId} {b : Barrier} {m n : Nat} {c : Prog}
      {I A : List ThreadId}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.sync b m :: c)) (.err i (Cmd.sync b m :: c))
  /-- The `arrive` analogue of `sync_err_full` (identical, per the paper). -/
  | arrive_err_full {s : State} {i : ThreadId} {b : Barrier} {n : Nat} {c : Prog}
      {I A : List ThreadId}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hfull : I.length + A.length = n) :
      ThreadStep (.run s i (Cmd.arrive b n :: c)) (.err i (Cmd.arrive b n :: c))
  /-- The `arrive` analogue of `sync_err_count` (identical, per the paper). -/
  | arrive_err_count {s : State} {i : ThreadId} {b : Barrier} {m n : Nat} {c : Prog}
      {I A : List ThreadId}
      (he : s.E i = true)
      (hb : s.B b = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.arrive b m :: c)) (.err i (Cmd.arrive b m :: c))

/-- The CTA-level small-step relation `E, B, T  ⤳  E', B', T'` of §3.3. -/
inductive CTAStep : Config → Config → Prop where
  /- CHECKED. -/
  /-- Interleaving: while every barrier is unconfigured or still under-registered,
  nondeterministically choose a thread and run it for one (non-error) thread step,
  splicing the resulting program and state back into the CTA. -/
  | interleave {s s' : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hi : i ∈ T.ids)
      (hbar : ∀ b, s.B b = BarrierState.unconfigured ∨
                   ∃ I A n, s.B b = ⟨I, A, some n⟩ ∧ I.length + A.length < n)
      (hstep : ThreadStep (.run s i (T.prog i)) (.run s' i P')) :
      CTAStep (.run s T) (.run s' (T.set i hi P'))
  /- CHECKED. -/
  /-- Recycle: when barrier `b` has registered exactly its expected count
  (`|I|+|A| = n`), wake every thread blocked on it (`E' = E[true/I]`), advance each
  such thread past its parked `sync b n`, and reset `b` to unconfigured. -/
  | recycle {s : State} {T : CTA} {b : Barrier} {I A : List ThreadId} {n : Nat}
      (hb : s.B b = ⟨I, A, some n⟩)
      (hfull : I.length + A.length = n)
      (hpark : ∀ i ∈ I, (T.prog i).head? = some (Cmd.sync b n)) :
      CTAStep (.run s T)
        (.run { E := updateMapOn s.E I true,
                B := Function.update s.B b BarrierState.unconfigured }
              (T.wake I))
  /- CHECKED. -/
  /-- Termination: when every thread has reached `return`, the CTA is `done`. -/
  | done {s : State} {T : CTA} (hdone : CTA.IsDone T) :
      CTAStep (.run s T) (.done s)
  /- CHECKED. -/
  /-- Error propagation: if any thread produces `err`, so does the whole CTA. This
  rule is independent of the barrier condition guarding `interleave`. -/
  | error {s : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hstep : ThreadStep (.run s i (T.prog i)) (.err i P')) :
      CTAStep (.run s T) (.err T)

@[inherit_doc ThreadStep] infix:40 " ⤳ₜ " => ThreadStep
@[inherit_doc CTAStep] infix:40 " ⤳ " => CTAStep

end Weft
