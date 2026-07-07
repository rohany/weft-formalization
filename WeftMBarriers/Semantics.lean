/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftMBarriers.State
import WeftCommon.Traces

/-!
# The Weft++ operational semantics (§5.2, Figures 4–5)

This file formalizes the small-step operational semantics of the
mbarrier-extended language (Figures 4 and 5 of the weft++ theorems document).
The named-barrier rules are lifted directly from the base language (§3.3 of the
Weft paper): they read and write only the named-barrier map `BN` and thread the
mbarrier map `BM` through unchanged. There are two judgment forms:

```
        E, BN, BM, T  ⤳  E', BN', BM', T'      -- a CTA T takes one step
     E, BN, BM, i, P  ⤳  E', BN', BM', i, P'   -- thread i with program P takes one step
```

A configuration pairs a state `s = (E, BN, BM)` with a CTA `T`. The two
distinguished terminal results are `done` (the state is kept, the CTA collapses
to "no more commands") and `err` (the state becomes the error state, the CTA is
kept) — see `Config`. The CTA-level `interleave` rule nondeterministically picks
one thread, runs it for a single thread-level step, and splices the result back
in; this is only allowed while every barrier is unconfigured or still
under-registered. When some barrier is exactly full it must instead be recycled
— *recycling has priority over every other rule*, including error propagation
(see the deviation note below).

## Thread-level rules (`ThreadStep`)

* `read_noop` / `write_noop` — `read g; c ⤳ c` and `write g; c ⤳ c`; `read`/
  `write` are no-ops for the barrier semantics, merely advancing the program.
* `arrive_configure` — first thread to register at an unconfigured barrier via
  `arrive_nb`: `E(id) = true`, `BN(nb) = ([],0,⊥)`, set `BN' = BN[([], 1, n)/nb]`,
  advance to `c`. (The `E(id) = true` premise is explicit here, beyond the paper.)
* `arrive_register` — subsequent non-blocking arrive: `E(id) = true`,
  `BN(nb) = (I,A,n)` with `0 < |I|+A < n`, set `BN' = BN[(I, A+1, n)/nb]`, advance
  to `c`. (`A` is now a count, so an arrival just increments it.)
* `sync_configure` — first thread to register at an unconfigured barrier via
  `sync_nb`: `E(id) = true`, `E' = E[false/id]`, `BN(nb) = ([],0,⊥)`,
  `BN' = BN[([id], 0, n)/nb]`; control stays at `sync_nb nb n; c` (thread now
  blocked).
* `sync_block` — subsequent blocking sync: `E(id) = true`, `E' = E[false/id]`,
  `BN(nb) = (I,A,n)` with `0 < |I|+A < n`, `BN' = BN[(I::id, A, n)/nb]`; control
  stays at `sync_nb nb n; c`.
* `sync_err_count` — thread-count mismatch: `E(id) = true`, `BN(nb) = (I,A,n)`,
  `n ≠ m` ⇒ `sync_nb nb m; c` steps to `err`.
* `arrive_err_count` — the error production for `arrive_nb`, identical to the
  `sync_nb` one.
* `mb_init` — configure a fresh mbarrier: `E(id) = true`, `sb ∉ dom(BM)`,
  `BM' = BM[([], 0, n, 0)/sb]`, advance to `c`.
* `mb_init_err` — initializing an already-initialized mbarrier
  (`sb ∈ dom(BM)`) steps to `err`.
* `mb_arrive` — non-blocking arrival on an initialized mbarrier:
  `E(id) = true`, `BM(sb) = (I,A,n,ph)`, set `BM' = BM[(I, A+1, n, ph)/sb]`,
  advance to `c`. (No under-full premise — the `interleave` guard supplies it.)
* `mb_arrive_err` — arriving on an uninitialized mbarrier (`sb ∉ dom(BM)`)
  steps to `err`.
* `mb_wait_block` — a phase-matching wait blocks: `E(id) = true`,
  `BM(sb) = (I,A,n,ph)`, set `E' = E[false/id]`, `BM' = BM[(I::id, A, n, ph)/sb]`;
  control stays at `wait_mb sb ph; c`.
* `mb_wait_pass` — a phase-mismatched wait (`BM(sb) = (I,A,n,ph')`, `ph ≠ ph'`)
  is a no-op: advance to `c`, state untouched.
* `mb_wait_err` — waiting on an uninitialized mbarrier (`sb ∉ dom(BM)`) steps
  to `err`.

## CTA-level rules (`CTAStep`)

* `interleave` — if every named barrier is unconfigured or under-registered
  (`∀ nb. BN(nb) = ([],0,⊥) ∨ (BN(nb) = (I,A,n) ∧ |I|+A < n)`) and every
  mbarrier is uninitialized or under-full
  (`∀ sb ∈ dom(BM). BM(sb) = (I,A,n,ph) ∧ |A| < n`), pick a thread and run it
  one (non-error) step, splicing `Pᵢ'` back into the CTA.
* `recycle` — if some barrier `BN(nb) = (I,A,n)` has `|I|+A = n`, wake every
  thread blocked on it: set `E' = E[true/I]`, advance each thread in `I` past its
  `sync_nb nb n`, and reset the barrier to `([],0,⊥)`.
* `mb_recycle` — if some mbarrier `BM(sb) = (I,A,n,ph)` has `|A| = n`, wake every
  waiter: set `E' = E[true/I]`, advance each thread in `I` past its
  `wait_mb sb ph`, and *flip the phase*: `BM' = BM[([], 0, n, ph ⊕ 1)/sb]` — the
  barrier keeps its count and stays initialized.
* `done` — `E, BN, BM, return ‖ … ‖ return ⤳ E, BN, BM, done`, provided no
  barrier of either kind is full.
* `error` — if any thread produces `err`, the whole CTA goes to `err`; guarded by
  the *same* all-barriers-under-full conditions as `interleave`.

## Deviation from the paper: recycle has priority over the error productions

The paper's err productions carry no barrier condition, and it also has
"too many threads" productions (`sync`/`arrive` at a barrier with `|I|+|A| = n`
step to `err`). Together these make the paper's own Theorem 1 false: a full
barrier is a *transient* state that the semantics is about to recycle (the
`interleave` guard exists exactly so no thread can act on it), yet an unguarded
err production lets a thread observe it and abort instead. Counterexample: the
single thread `[arrive_nb nb 1, sync_nb nb 1]` passes `WELLSYNC` (generations 1
and 2, and the sync's predecessor *is* the generation-1 arrive), but after the
`arrive_nb` fills `nb` the still-enabled thread could take the full-barrier err
production in a race with the pending recycle, deadlocking Definition 6. On
hardware the race does not exist — a completed named barrier "is immediately
re-initialized" (§2.2), so fullness is never observable.

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

namespace WeftMBarriers

/-- A thread-level configuration `E, BN, BM, i, P` (or the error result
`err, i, P`). A thread program `P` of thread `i` runs against a state
`s = (E, BN, BM)`. -/
inductive ThreadConfig where
  /-- `E, BN, BM, i, P`: thread `i` running program `P` in state `s`. -/
  | run (s : State) (i : ThreadId) (P : Prog)
  /-- `err, i, P`: thread `i` has produced the error state. -/
  | err (i : ThreadId) (P : Prog)

/-- A CTA-level configuration: the shared functor `WeftCommon.Config`
instantiated at this language's states and commands. Following the paper,
`done` keeps the state and collapses the CTA, whereas `err` replaces the state
with the error state but keeps the CTA. The constructors are re-exported below
under their usual names. -/
abbrev Config := WeftCommon.Config State Cmd

namespace Config
export WeftCommon.Config (run done err noConfusion
  run.injEq done.injEq err.injEq run.inj done.inj err.inj)
end Config

/-- The thread-level small-step relation
`E, BN, BM, i, P  ⤳  E', BN', BM', i, P'` (Figure 4, named-barrier fragment).

Each constructor is one inference rule; see the module doc for the correspondence
to the paper. `read`/`write` are no-ops; `arrive_nb` is non-blocking; `sync_nb`
blocks (disabling the thread and leaving its control parked at the `sync_nb`)
until the barrier is recycled. Every named-barrier rule threads the mbarrier map
`BM` through unchanged; the mbarrier rules (`mb_*`, from Figure 5) touch only
`BM`. -/
inductive ThreadStep : ThreadConfig → ThreadConfig → Prop where
  /-- `read g` is a no-op for the barrier semantics: just advance the program. -/
  | read_noop {s : State} {i : ThreadId} {g : Loc} {c : Prog} :
      ThreadStep (.run s i (Cmd.read g :: c)) (.run s i c)
  /-- `write g` is a no-op for the barrier semantics: just advance the program. -/
  | write_noop {s : State} {i : ThreadId} {g : Loc} {c : Prog} :
      ThreadStep (.run s i (Cmd.write g :: c)) (.run s i c)
  /-- First thread to register at an unconfigured barrier `nb` via `arrive_nb`:
  configure `nb` with count `n`, set the arrived count to `1`, advance to `c`.
  The enabledness premise `E(id) = true` is stronger than the paper, which leaves
  it implicit (a thread reaching an `arrive_nb` is necessarily enabled); we
  require it explicitly, matching the `sync_nb` rules. -/
  | arrive_configure {s : State} {i : ThreadId} {nb : NamedBarrier} {n : ℕ+} {c : Prog}
      (he : s.E i = true)
      (hb : s.BN nb = NamedBarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.arrive_nb nb n :: c))
        (.run { s with BN := Function.update s.BN nb ⟨[], 1, some n⟩ } i c)
  /-- Subsequent non-blocking `arrive_nb` at a configured, not-yet-full barrier:
  increment the arrived count, advance to `c`. As in `arrive_configure`, the
  enabledness premise `E(id) = true` is required explicitly, beyond the paper. -/
  | arrive_register {s : State} {i : ThreadId} {nb : NamedBarrier} {n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.BN nb = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A) (hlt : I.length + A < (n : Nat)) :
      ThreadStep (.run s i (Cmd.arrive_nb nb n :: c))
        (.run { s with BN := Function.update s.BN nb ⟨I, A + 1, some n⟩ } i c)
  /-- First thread to register at an unconfigured barrier `nb` via `sync_nb`:
  configure `nb` with count `n`, disable the thread (`E[false/id]`), add `id` to
  the synced list; control stays parked at `sync_nb nb n; c`. -/
  | sync_configure {s : State} {i : ThreadId} {nb : NamedBarrier} {n : ℕ+} {c : Prog}
      (he : s.E i = true)
      (hb : s.BN nb = NamedBarrierState.unconfigured) :
      ThreadStep (.run s i (Cmd.sync_nb nb n :: c))
        (.run { s with E := Function.update s.E i false,
                       BN := Function.update s.BN nb ⟨[i], 0, some n⟩ }
          i (Cmd.sync_nb nb n :: c))
  /-- Subsequent blocking `sync_nb` at a configured, not-yet-full barrier: disable
  the thread, add `id` to the synced list; control stays parked at
  `sync_nb nb n; c`. -/
  | sync_block {s : State} {i : ThreadId} {nb : NamedBarrier} {n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.BN nb = ⟨I, A, some n⟩)
      (hpos : 0 < I.length + A) (hlt : I.length + A < (n : Nat)) :
      ThreadStep (.run s i (Cmd.sync_nb nb n :: c))
        (.run { s with E := Function.update s.E i false,
                       BN := Function.update s.BN nb ⟨i :: I, A, some n⟩ }
          i (Cmd.sync_nb nb n :: c))
  /-- Thread-count mismatch on `nb`: barrier expects `n` but `sync_nb nb m` has
  `n ≠ m`; step to `err`. (The paper's companion "too many threads" production
  `sync_err_full` is deliberately absent — see the module doc's deviation note.) -/
  | sync_err_count {s : State} {i : ThreadId} {nb : NamedBarrier} {m n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.BN nb = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.sync_nb nb m :: c)) (.err i (Cmd.sync_nb nb m :: c))
  /-- The `arrive_nb` analogue of `sync_err_count` (identical, per the paper). -/
  | arrive_err_count {s : State} {i : ThreadId} {nb : NamedBarrier} {m n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ}
      (he : s.E i = true)
      (hb : s.BN nb = ⟨I, A, some n⟩)
      (hne : n ≠ m) :
      ThreadStep (.run s i (Cmd.arrive_nb nb m :: c)) (.err i (Cmd.arrive_nb nb m :: c))
  /-- `MB-Init` (Figure 5): configure a fresh mbarrier `sb` with arrival count
  `n` and phase `0`, advance to `c`. The premise `sb ∉ dom(BM)` is our
  `uninitialized` encoding; the enabledness premise `E(id) = true` is explicit
  beyond the paper, matching the named-barrier convention. -/
  | mb_init {s : State} {i : ThreadId} {sb : SharedBarrier} {n : ℕ+} {c : Prog}
      (he : s.E i = true)
      (hb : s.BM sb = MBarrierState.uninitialized) :
      ThreadStep (.run s i (Cmd.init_mb sb n :: c))
        (.run { s with BM := Function.update s.BM sb ⟨[], 0, some n, false⟩ } i c)
  /-- `MB-Init-Err` (Figure 5): initializing an already-initialized mbarrier
  (`sb ∈ dom(BM)`) is an error. -/
  | mb_init_err {s : State} {i : ThreadId} {sb : SharedBarrier} {n : ℕ+} {c : Prog}
      {I : List ThreadId} {A : ℕ} {n' : ℕ+} {ph : Phase}
      (he : s.E i = true)
      (hb : s.BM sb = ⟨I, A, some n', ph⟩) :
      ThreadStep (.run s i (Cmd.init_mb sb n :: c)) (.err i (Cmd.init_mb sb n :: c))
  /-- `MB-Arrive` (Figure 5): non-blocking arrival on an initialized mbarrier —
  increment the arrived count, advance to `c`. Unlike the named `arrive_register`
  the rule carries no under-full premise: the `interleave` guard (`hmbar`) is
  what keeps arrivals from overshooting `n` (no thread steps while an mbarrier is
  ready to recycle), and no `configure` variant exists since initialization is
  explicit (`mb_init`). -/
  | mb_arrive {s : State} {i : ThreadId} {sb : SharedBarrier} {c : Prog}
      {I : List ThreadId} {A : ℕ} {n : ℕ+} {ph : Phase}
      (he : s.E i = true)
      (hb : s.BM sb = ⟨I, A, some n, ph⟩) :
      ThreadStep (.run s i (Cmd.arrive_mb sb :: c))
        (.run { s with BM := Function.update s.BM sb ⟨I, A + 1, some n, ph⟩ } i c)
  /-- `MB-Arrive-Err` (Figure 5): arriving on an uninitialized mbarrier
  (`sb ∉ dom(BM)`) is an error. (Note the asymmetry with named barriers, where an
  `arrive_nb` on an unconfigured barrier *configures* it and the error production
  is a count mismatch: an mbarrier's count exists only by explicit `init_mb`.) -/
  | mb_arrive_err {s : State} {i : ThreadId} {sb : SharedBarrier} {c : Prog}
      (he : s.E i = true)
      (hb : s.BM sb = MBarrierState.uninitialized) :
      ThreadStep (.run s i (Cmd.arrive_mb sb :: c)) (.err i (Cmd.arrive_mb sb :: c))
  /-- `MB-Wait-Block` (Figure 5): a `wait_mb` whose phase `ph` *matches* the
  barrier's current phase — the phase-`ph` generation is still collecting
  arrivals — blocks: disable the thread (`E[false/id]`), add `id` to the waiter
  list; control stays parked at `wait_mb sb ph; c` until `MB-Recycle` flips the
  phase and wakes the waiters. As with `mb_arrive`, there is no under-full
  premise — the `interleave` guard supplies it. -/
  | mb_wait_block {s : State} {i : ThreadId} {sb : SharedBarrier} {ph : Phase} {c : Prog}
      {I : List ThreadId} {A : ℕ} {n : ℕ+}
      (he : s.E i = true)
      (hb : s.BM sb = ⟨I, A, some n, ph⟩) :
      ThreadStep (.run s i (Cmd.wait_mb sb ph :: c))
        (.run { s with E := Function.update s.E i false,
                       BM := Function.update s.BM sb ⟨i :: I, A, some n, ph⟩ }
          i (Cmd.wait_mb sb ph :: c))
  /-- `MB-Wait-Pass` (Figure 5): a `wait_mb` whose phase does *not* match the
  barrier's current phase — the phase-`ph` generation has already completed —
  passes through as a no-op, advancing to `c` with the state untouched. This is
  the one rule with no named-barrier analogue: a synchronization command that may
  not synchronize at all. -/
  | mb_wait_pass {s : State} {i : ThreadId} {sb : SharedBarrier} {ph : Phase} {c : Prog}
      {I : List ThreadId} {A : ℕ} {n : ℕ+} {ph' : Phase}
      (he : s.E i = true)
      (hb : s.BM sb = ⟨I, A, some n, ph'⟩)
      (hne : ph ≠ ph') :
      ThreadStep (.run s i (Cmd.wait_mb sb ph :: c)) (.run s i c)
  /-- `MB-Wait-Err` (Figure 5): waiting on an uninitialized mbarrier
  (`sb ∉ dom(BM)`) is an error. -/
  | mb_wait_err {s : State} {i : ThreadId} {sb : SharedBarrier} {ph : Phase} {c : Prog}
      (he : s.E i = true)
      (hb : s.BM sb = MBarrierState.uninitialized) :
      ThreadStep (.run s i (Cmd.wait_mb sb ph :: c)) (.err i (Cmd.wait_mb sb ph :: c))

/-- The CTA-level small-step relation `E, BN, BM, T  ⤳  E', BN', BM', T'`
(Figure 4, named-barrier fragment; the mbarrier conjuncts of the guards are
deferred — see the module doc). -/
inductive CTAStep : Config → Config → Prop where
  /-- Interleaving: while every named barrier is unconfigured or still
  under-registered and every mbarrier is uninitialized or strictly under-full
  (`|A| < n` — only *arrivals* fill an mbarrier; waiters do not count),
  nondeterministically choose a thread and run it for one (non-error) thread step,
  splicing the resulting program and state back into the CTA. -/
  | interleave {s s' : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hi : i ∈ T.ids)
      (hbar : ∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
                    ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
      (hmbar : ∀ sb, s.BM sb = MBarrierState.uninitialized ∨
                     ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
      (hstep : ThreadStep (.run s i (T.prog i)) (.run s' i P')) :
      CTAStep (.run s T) (.run s' (T.set i hi P'))
  /-- Recycle: when barrier `nb` has registered exactly its expected count
  (`|I|+A = n`), wake every thread blocked on it (`E' = E[true/I]`), advance each
  such thread past its parked `sync_nb nb n`, and reset `nb` to unconfigured. -/
  | recycle {s : State} {T : CTA} {nb : NamedBarrier} {I : List ThreadId} {A : ℕ} {n : ℕ+}
      (hb : s.BN nb = ⟨I, A, some n⟩)
      (hfull : I.length + A = (n : Nat))
      (hpark : ∀ i ∈ I, (T.prog i).head? = some (Cmd.sync_nb nb n)) :
      CTAStep (.run s T)
        (.run { s with E := updateMapOn s.E I true,
                       BN := Function.update s.BN nb NamedBarrierState.unconfigured }
              (T.wake I))
  /-- `MB-Recycle` (Figure 5): when mbarrier `sb` has collected exactly its
  expected number of *arrivals* (`|A| = n` — waiters do not count toward
  fullness), wake every waiter (`E' = E[true/I]`), advance each past its parked
  `wait_mb sb ph`, clear the waiters and arrivals, and *flip the phase*. Unlike
  the named `recycle` the barrier is not reset to unconfigured: it keeps its
  count and stays initialized forever, and only two recycles restore its full
  state — the phase bit is what doubles the loop period (`fₘ(b) = 2 · f(b)`).
  The paper's explicit premise `∀ i ∈ I, E(i) = false` is omitted, as in the
  named `recycle`: it is derivable from the blocking invariant (every waiter was
  disabled by the `mb_wait_block` that parked it). -/
  | mb_recycle {s : State} {T : CTA} {sb : SharedBarrier} {I : List ThreadId} {A : ℕ}
      {n : ℕ+} {ph : Phase}
      (hb : s.BM sb = ⟨I, A, some n, ph⟩)
      (hfull : A = (n : Nat))
      (hpark : ∀ i ∈ I, (T.prog i).head? = some (Cmd.wait_mb sb ph)) :
      CTAStep (.run s T)
        (.run { s with E := updateMapOn s.E I true,
                       BM := Function.update s.BM sb ⟨[], 0, some n, !ph⟩ }
              (T.wake I))
  /-- Termination: when every thread has reached `return`, the CTA is `done` —
  *provided* no barrier is left completed-but-not-recycled. The premise `hnofull`
  requires every configured named barrier to be strictly under-full
  (`|I|+A < n`), and `hmbnofull` requires every initialized mbarrier to be
  strictly under-full in *arrivals* (`|A| < n`): a barrier that has reached its
  expected count must be recycled (`CTAStep.recycle` / `CTAStep.mb_recycle`,
  always available for a full barrier) before the CTA may terminate, so completed
  barriers always advance their generation rather than being torn down full.
  (Under-full barriers, whose generation never completes, may remain at
  termination.) -/
  | done {s : State} {T : CTA} (hdone : CTA.IsDone T)
      (hnofull : ∀ nb I A n, s.BN nb = ⟨I, A, some n⟩ → I.length + A < (n : Nat))
      (hmbnofull : ∀ sb I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ → A < (n : Nat)) :
      CTAStep (.run s T) (.done s)
  /-- Error propagation: if any thread produces `err`, so does the whole CTA. The
  rule carries the *same* barrier conditions as `interleave` (`hbar`/`hmbar`):
  when some barrier — named or shared — is exactly full, only the matching
  recycle may fire; no thread may observe the transient full state, erroring
  included. See the module doc's deviation note (the paper's unguarded err
  productions make its Theorem 1 false). -/
  | error {s : State} {T : CTA} {i : ThreadId} {P' : Prog}
      (hbar : ∀ nb, s.BN nb = NamedBarrierState.unconfigured ∨
                    ∃ I A n, s.BN nb = ⟨I, A, some n⟩ ∧ I.length + A < (n : Nat))
      (hmbar : ∀ sb, s.BM sb = MBarrierState.uninitialized ∨
                     ∃ I A n ph, s.BM sb = ⟨I, A, some n, ph⟩ ∧ A < (n : Nat))
      (hstep : ThreadStep (.run s i (T.prog i)) (.err i P')) :
      CTAStep (.run s T) (.err T)

@[inherit_doc ThreadStep] scoped infix:40 " ⤳ₜ " => ThreadStep
@[inherit_doc CTAStep] scoped infix:40 " ⤳ " => CTAStep

end WeftMBarriers
