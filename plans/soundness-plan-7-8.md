# Plan: `wellSynchronized_of_check` for WeftMBarriers (§5.2.6, Theorems 6–8)

Goal: `check = true → T.WellSynchronized`, by the conformance route — **not** via
Lemma 1 (circular). Port the named development: a forward induction over an arbitrary
challenger trace `τ'` carrying `Conforms T τ τ'` (Theorem 6 / `conforms_snoc` +
`conforms_of_traceFrom`), then conforming complete traces end `done` (Theorem 7 /
`conforms_complete_done`), then assembly (Theorem 8 / `wellSynchronized_of_check`).

Source: named CheckWellSynchronized.lean lines ~2429–7194 (~4750 lines):
support ~2429–4160, `BarrierConforms`/`Conforms` 4162–4230, bridge lemmas
(`Conforms.happensBefore_sound`, `conforms_init`, `conforms_reg_round`,
`conforms_full_fiber`) 4230–4670, **`conforms_snoc` 4671–6585 (~1900)**,
`conforms_of_traceFrom` 6586, `conforms_complete_done` 6627–7114 (~490),
`wellSynchronized_of_check` 7115–7194. Estimated mb total: **~5500–6500 lines** —
the largest single campaign of the port.

## 0. The mb-extended `Conforms` (design)

Named clauses (port as-is, with the 4-family `initRelation`):
- **0 `no_err`**: `τ'` has not errored. Now also refutes the three mb error
  productions (see snoc case E4).
- **1 `gen_eq`**: executed points carry reference generations
  (`pointGen T τ' η = pointGen T τ η`; both `Option ℤ` now — same statement shape).
- **3 `edge_sound`**: generating edges with executed target have an executed source,
  no later.
- **4 `rounds_complete`**: extend over `b : NamedBarrier ⊕ SharedBarrier` — once `b`
  has recycled `g` times in `τ'`, the reference fiber of round `g − 1` has fully
  executed. For mbarriers the fiber contains only arrives (see fibers below).

Clause **2 `state`** splits per kind:
- `.inl nb` — `BarrierConforms` ports verbatim (count-conformance vs fiber commands,
  `arrived` = #executed fiber-arrives, `synced ↔` fiber-syncs parked at their pointer,
  `count = none → unconfigured`).
- `.inr sb` — new `MBarrierConforms`:
  * **count**: `(s.BM sb).count = some n → T.initCountOf sb = some n`, and
    `count = none → s.BM sb = MBarrierState.uninitialized` (pristine normalization —
    machinery exists: `uninit_step`, `count_some_persists`, `initCountOf_some`,
    `unique_init_of_check`).
  * **arrived**: `= #` executed arrives of the current-round mb fiber (paper: "we only
    make sure that the arrival counts conform").
  * **phase**: `= phaseAfter (recycleCount (.inr sb) τ' …)` — free from
    `phase_eq_phaseAfter`, but carrying it in the clause saves re-deriving it in every
    case.
  * **parked waiters** (FLAG 1, deviation from the paper's "we don't track the parked
    waiters"): the mechanization needs
    `∀ i ∈ (s.BM sb).waiting, ∃ η, η.thread = i ∧ pointerAt T η C ∧
      T.cmdAt η = some (.wait_mb sb ph…) ∧ pointGen T τ η = some (rc : ℤ)` —
    "every parked waiter is parked at its reference generation (= the current recycle
    count)". The paper concedes this fact is needed at MBarrier-Recycle ("we know from
    conformance (and should be able to prove separately …)"); carrying it as a clause
    *is* the mechanized form of "prove separately" — it is established exactly by the
    Wait-Block snoc case (which proves `k = g`) and consumed by the recycle case to
    give the woken waits their `gen_eq`. Waiters still do **not** count toward
    `arrived`, matching the paper.

## 1. Phase S-A — check-`true` reading lemmas (~250 lines)

Duals of the completeness extractors, consuming `fst_checkWellSynchronized` +
`Bool.and_eq_true` + `mem_transClosure_imp_transGen` (all in place):
1. `check_true_parts` : `check = true → okRegCheck ∧ okWaitCheck ∧ okInitCheck ∧
   okUniqueInitCheck` (all `= true`).
2. `happensBefore_of_check` (registrant pairs): `Reg(b,g) ∋ c1`, `Reg(b,g+1) ∋ c2`,
   `1 ≤ c2.idx` → `happensBefore T τ c1 ⟨c2.thread, c2.idx−1⟩` — port of named,
   `registrantGen`-based.
3. `idx_pos_of_check`: flagged registrant pairs never have `c2.idx = 0` — port.
4. **new** `wait_lower_of_check`: wait `w` gen `g`, `1 ≤ g` →
   `1 ≤ w.idx ∧ ∀ c ∈ Reg(.inr sb, g−1), happensBefore T τ c ⟨w.thread, w.idx−1⟩`.
5. **new** `wait_upper_of_check`: wait `w` gen `g`, `initCountOf sb = some n`,
   `|Reg(.inr sb, g+1)| = n` → `∃ c⁺ ∈ Reg(.inr sb, g+1), happensBefore T τ w c⁺`.
6. **new** `init_hb_of_check`: `init_mb` point `ip`, use `u` →
   `happensBefore T τ ip u`.
7. `unique_init_of_check` — already proven.

## 2. Phase S-B — pointTime/trace support (~800 lines, mostly verbatim)

Barrier-agnostic ports from named 2429–2800: `pointTime_append_cases` (how
`pointTime` behaves under `τ' ++ [C']` — the workhorse of every snoc case),
`isTimeOf_of_pointTime`, `pointGen_eq_of_pointTime`, `pointTime_spec`,
`exec_step_time`, `exists_pointTime_of_passed`, `pointTime_sync_recycles` (+ a
`pointTime_wait_…` variant reading `wait_time_recycles_or_pass`), `pointerAt` +
`pointTime_none_of_pointerAt`, `countP_eq_all`, `exists_step_increase`,
`arrive_drop_thread_unique` (have the `arrive_mb`/`init` analogs already).
Already in the tree from the completeness campaign: `progPoints_nodup`,
`countP_succ_of_unique`, `time_drop_evidence`, all drop-classification lemmas,
`arrive_mb_drop_arrived`, `arrived_mono_of_not_recycle`, `count_some_persists`,
`uninit_step`, `phase_eq_phaseAfter`, `interleaveGuard_*_absurd`.

## 3. Phase S-C — fibers (~900 lines)

- `genFiber` over the sum: `genFiber T τ (b : NamedBarrier ⊕ SharedBarrier) (g : ℤ)`
  — points whose command registers on `b` with reference generation `g`
  (`registrantGen`-based; ℤ-indexed since mb generations are ℤ; named call sites use
  `.inl nb` with cast). For `.inr sb` the fiber automatically contains only
  `arrive_mb`s (Flag 3 below: registrants of `.inr` are arrives — the sum keeps the
  named fiber lemmas' shapes).
- Port the named fiber lemmas (`genFiber_nodup` ✓ trivial, `_length`,
  `_sync_thread_inj`, `_partial_no_sync`, `_arrive_post_count`, `_round_data`,
  `_count_eq`, `_nonempty_of_succ`, `_partial_length_lt`, `arrived_census`,
  `isArriveCmd`/`isSyncCmd`/`arriveBy`) — the counting engine for "round `g` was
  full ⟹ the fiber is consumed" and "a partial round is missing a member".
- mb analogs: the arrive-census for `.inr` fibers (`|fiber| = n` for completed
  rounds — the completed-round counting already prototyped in
  `wait_upper_bound_false`'s `key` induction; refactor to share where cheap, else
  re-derive in fiber terms), `wait_thread_inj` for the parked-waiter clause.

## 4. Phase S-D — the invariant + bridges (~800 lines)

`MBarrierConforms` + extended `Conforms` (per §0) + ports of `conforms_init`
(initial: everything empty/pristine), `Conforms.happensBefore_sound` (path lift of
clause 3 — verbatim), `conforms_reg_round` (the k=g argument for registrants: "late"
via clause 4 + fiber counting, "early" via `happensBefore_of_check` + clause 3 at the
predecessor `c3` — this is the shared core of every register-type snoc case),
`conforms_full_fiber`. New bridges:
- `conforms_wait_gen` — the k=g argument for **waits**, both flavors:
  * block (phase matched, so `k ≡ p (mod 2)`): `k < g ⟹ k ≤ g−2` → early-case via
    `wait_lower_of_check` (the lower bound's `Reg(sb,g−1) → c3` edges + clause 3);
    `k > g ⟹ k ≥ g+2` → via `wait_upper_of_check` (edge `w → c⁺ ∈ Reg(sb,g+1)`),
    clause 4 (`k ≥ g+2` closes round `g+1`, so `c⁺` executed), clause 3 backward
    (executed `c⁺` forces executed `w`) — but `w` is executing *now* ⊥.
  * pass (phase mismatched, observes `k−1`): show `k = g+1`; `k < g+1 ⟹ k ≤ g−1`
    via the lower bound; `k > g+1 ⟹ k ≥ g+3` via the upper bound — same two
    engines. (FLAG 2: the pass upper-case needs the *amended* upper bound's fill
    condition satisfied to have the edge at all — when `Reg(sb, g+1)` under-fills the
    check passes vacuously; but then round `g+1` never completes in `τ'` either
    (clause-2 arrive census bounds the round by the fiber), so `k ≥ g+2` is itself
    impossible — the case splits on fill vs. partial, with the partial branch closed
    by the census, no edge needed.)

## 5. Phase S-E — `conforms_snoc` (~2500 lines, the monster)

Sub-phases, each a green checkpoint (clauses proven per case; case order follows the
step rules):
- **E1** named-rule cases port (arrive-configure/register, sync-configure/block,
  read/write, named recycle, named count-mismatch errs): the τ-side arguments are
  identical; each case additionally threads the mb clauses (BM untouched → no-ops,
  the pattern is mechanical).
- **E2** mb run-rules:
  * `mb_init`: gen `k = g = 0` (recycles of `sb` impossible while uninitialized —
    count-none persists backward; in `τ` likewise), state clause moves pristine →
    `⟨[],0,some n,false⟩` with `initCountOf = some n` (uniqueness pins the point),
    phase `false = phaseAfter 0` ✓, edges into an `init_mb` are program-order only.
  * `mb_arrive`: mirror of named arrive-register (paper: "pretty much identical") —
    `conforms_reg_round` gives `k = g`; arrived-census +1 = the fiber-filter +1
    (`countP_succ_of_unique`); edges into an `arrive_mb` are program-order only.
  * `mb_wait_block`: `conforms_wait_gen` (block flavor) gives `k = g`; parked-waiter
    clause extended with the new waiter (its `pointGen τ = some k` is exactly what
    was just proven); *not retired* → clauses 1/3 untouched for `w` itself.
  * `mb_wait_pass`: `conforms_wait_gen` (pass flavor) gives `k = g+1`, so the
    retired wait observes `k−1 = g` ✓ clause 1; clause 3 for the arriveWait in-edges
    (`arrive_mb` gen `g` → `w`): round `g` completed (`k ≥ g+1`, clause 4) so every
    such arrive executed ✓; program-order in-edge standard.
- **E3** `mb_recycle`: `arrived = n` (census) means round `k`'s fiber is consumed;
  the woken waiters are parked at generation `k` (the parked-waiter clause) so each
  retiree gets `gen_eq` at `k` = its reference generation; state resets to
  `⟨[],0,some n,!ph⟩` with the phase flip matching `phaseAfter (k+1)`; clause-3 for
  the retirees' in-edges: program-order + arriveWait (all gen-`k` arrives executed —
  they filled the round) ✓; clause 4 extended to the newly closed round by the
  census. No wait↔wait edges exist to discharge.
- **E4** the error rule (clause 0 preservation — the step cannot be an error):
  * named count-mismatch errs: port.
  * `mb_arrive_err`/`mb_wait_err` (uninitialized use): `init_hb_of_check` gives
    `hb(ip, use)`; the erring use's *predecessor* has executed (thread order), and
    `Conforms.happensBefore_sound`… careful: the use itself has NOT executed. The
    paper's argument: the hb-path from `ip` to the use must route through the use's
    program-order predecessor (uses have only po + arriveWait in-edges; for an
    `arrive_mb` only po) — the path's penultimate node has executed, so by clause 3
    `ip` executed → `sb` initialized (`init_drop_target_initialized` +
    `count_some_persists`) ⊥ the err rule's `uninitialized` premise. For `wait_mb`
    the in-edge may also be arriveWait from a gen-`g` arrive; then that arrive
    executed → `arrive_mb_drop_initialized` gives initialized at *its* step →
    persists ⊥ — either way initialized.
  * `mb_init_err` (double init): the barrier is initialized, so some init-drop
    already happened; its point is `ip` (uniqueness via `cmd_at_last` +
    `unique_init_of_check`); the erring instruction's point is also an `init_mb sb`
    point = `ip` — but `ip` already executed and the erring thread still *heads* at
    it (`pointerAt`-style program-length contradiction).

## 6. Phase S-F — Theorems 7 and 8 (~600 lines)

- `conforms_of_traceFrom`: induction over `τ'` via `conforms_snoc` — verbatim.
- `conforms_complete_done` (Theorem 7): the earliest-parked argument now ranges over
  parked **syncs and waits** (FLAG 4). A stuck conforming trace has a parked thread;
  take the parked op `c` with least reference time; a missing registrant `r` of `c`'s
  round has `t_τ(r) < t_τ(c)` (for waits: gen-`g` arrives precede the wake at recycle
  `g+1`); `r` is stuck behind its thread's parked head `e` with `t_τ(e) < t_τ(r)` —
  contradicting minimality. Port structure with the sum-typed blocked lists; the
  named proof's `hdescend` induction generalizes with a wait case.
- `wellSynchronized_of_check` (Theorem 8): both challenger traces conform (Thm 6)
  and end done (Thm 7), so every barrier op executes with its reference generation —
  the shared `some` witness. Port.

## 7. Flags / design decisions

1. **Parked-waiter clause** (§0): carried in `MBarrierConforms` despite the paper's
   "don't track waiters" — it is the mechanization of the paper's "prove separately"
   remark, needed at `mb_recycle` for the retirees' `gen_eq`. Waiters still excluded
   from the arrived census.
2. **Wait-pass upper case under partial fill**: when `Reg(sb, g+1)` under-fills, the
   amended check provides no `w → c⁺` edge — but the arrive census then bounds the
   round below `n`, making `k ≥ g+2` impossible directly. The case analysis in
   `conforms_wait_gen` splits on the fill condition.
3. **Kind purity**: registrant fibers never mix kinds (barrier is the sum), so all
   named fiber lemmas keep their shapes at `.inl` and the `.inr` fibers are
   arrive-only.
4. **Theorem 7 extension**: "sync or wait_mb" for parked ops, per the paper's note.
5. `mb_init`/`mb_init_err` cases are not discussed in the paper (§5.2.6 covers
   arrive/wait/recycle/errs) — arguments as in E2/E4 above; flag for review.

## 8. Build order / checkpoints

S-A → S-B → S-C → S-D (invariant compiles with `conforms_snoc` sorried) → E1 → E2 →
E3 → E4 → S-F. Each phase ends green/lint-clean; `conforms_snoc` is developed with
per-case sorries so progress is reviewable. Reuse from the completeness campaign is
substantial in S-B/S-C (listed above); the genuinely new mathematics is concentrated
in `conforms_wait_gen` (S-D) and E2/E3.
