# Plan: `not_wellSynchronized_of_check_false` for WeftMBarriers (§5.2.7)

**STATUS (2026-07-08): COMPLETE.** All six failure modes proven; the theorem is
axiom-clean. The only remaining sorry in the project is `wellSynchronized_of_check`
(soundness, a separate campaign). This file is retained as the design record.

Goal: `check = false → ¬ WellSynchronized`, proved as the contrapositive — assume
`hws : T.WellSynchronized`, derive `False` from the failing check. As in the named
development, `hws` is what unlocks the preciseness half of Lemma 1
(`happensBefore_precise` / `exists_reversing_trace` / `run_ideal`), which is the engine
of every reversal below. All of that machinery is already proven for mbarriers.

## 0. Failure-mode decomposition

`(CheckWellSynchronized T τ).1 = okReg && okWait && okInit && okUniqueInit`, so a
`false` result exhibits (at least) one failing conjunct, and `okWait` itself has three
failure modes. Six contradiction lemmas, one per mode:

| # | mode | data extracted | contradiction lemma |
|---|------|----------------|---------------------|
| 1a | `okReg`, `1 ≤ c2.idx` | registrants `c1 ∈ Reg(b,g)`, `c2 ∈ Reg(b,g+1)`, `c1 ≠ c3`, `(c1,c3) ∉ hb` | per-kind: named-port (`.inl`) / arrive-reduction (`.inr`) |
| 1b | `okReg`, `c2.idx = 0` | first-instruction registrant of gen `g+1` | `.inl`: named `firstInstr` port; `.inr`: **err shortcut** |
| 2a | `okWait` lines 25–26 | wait `w`, `G w = g ≥ 1`, `w.idx = 0` | **err shortcut** |
| 2b | `okWait` lines 27–28 | `w` (gen `g ≥ 1`, `1 ≤ w.idx`), `c ∈ Reg(sb,g−1)`, `c ≠ c3`, `(c,c3) ∉ hb` | sync-shaped: reversal / `competing_arrive_wait_false` |
| 2c | `okWait` lines 29–30 | `w` (gen `g`), `\|Reg(sb,g+1)\| = n`, no `(w,c⁺) ∈ hb` | ideal-run + arrival counting (Flag 1 fix agreed) |
| 3 | `okInit` | `init_mb` point `ip`, use `u`, `(ip,u) ∉ hb` | reversal + uninitialized-persistence |
| 4 | `okUniqueInit` | two distinct `init_mb` points for one `sb` | count-persistence (no reversal) |

## 1. Design flags — resolve before/while proving

### Flag 1 — RESOLVED (2026-07-07): amend the check with the fill condition

Lines 29–30 require `(w, c⁺) ∈ R` for some `c⁺ ∈ Reg(sb, g+1)` whenever that set is
nonempty. The paper's argument ("all arrives at g+1 complete before w ⇒ g+2 recyclings
⇒ `G(w) = g+2`") silently assumes **generation `g+1` fills** (`|Reg(sb,g+1)| = n`). If
the final generation is *partial* (allowed at termination — `hmbnofull` only forbids
*exactly full* barriers), the reversal produces `r_w = g+1`, phase mismatched, and `w`
still observes `g` — **no contradiction, and seemingly genuinely WS programs where the
`w`/`c⁺` order is free in both directions** (e.g. `n = 2` with a single gen-`g+1`
arrival: neither order changes any generation). The check would reject such programs.

Agreed fix (rohany, 2026-07-07): condition line 29 on `|Reg(sb, g+1)| = n`, reading
`n` from the barrier's unique `init_mb sb n` via a static `CTA.initCountOf`
(`okUniqueInit` already pins uniqueness; `initCountOf = none` passes vacuously — with
a successful `τ`, any generation-carrying `arrive_mb` implies the init exists anyway).
The upper bound's soundness role only pins `w` before a *completed* next generation,
so the weakening is harmless for Theorem 1.

### Flag 2 — RESOLVED (2026-07-07): idx-0 modes via the error guard

The paper's case 2 argues first-instruction waits by parity/generation. Our semantics
gives a two-line shortcut: **any thread whose *first* instruction is `arrive_mb`/`wait_mb`
admits an immediate error trace** — from the initial configuration all mbarriers are
uninitialized, both interleave/error guards hold, so `mb_wait_err`/`mb_arrive_err` fire
at once; `[init, err]` is a complete trace ending `err`, contradicting
`completeTrace_ends_done hws` (formally: the erring command never executes in that
trace, so it relates only to generation `none`). This covers modes 1b-`.inr` and 2a
without touching generations — the paper's parity argument is superseded by the guarded
error productions of our semantics. (Named-kind 1b still needs the ported
`firstInstr_highGen` argument, since named barriers self-configure and cannot err this
way.) Confirmed by rohany.

### Flag 3 (structural luck): registrant pairs never mix kinds

`Reg(b,g)` and `Reg(b,g+1)` share the barrier `b : NamedBarrier ⊕ SharedBarrier`, so in
mode 1 either both `c1, c2` are named ops (`arrive_nb`/`sync_nb` — the named argument
ports verbatim) or both are `arrive_mb` (no blocking, no competing case — the
arrive-reduction + reversal suffices, mirroring the named `arrive` sub-case).

## 2. Phase A — shared machinery (small, mechanical)

1. **Pillar A port/extraction**: the named `TransClosureConverse` section
   (WeftNamedBarriers/CheckWellSynchronized.lean 165–379) is `{α}`-generic — extract to
   `WeftCommon/WellSynchronized.lean` next to `transClosure` and re-export from both
   libs (keep named names working). Port `mem_transClosure_imp_transGen`,
   `mem_transClosure_of_transGen`, and `not_happensBefore_of_not_mem` (named 2235; the
   mb version needs `mem_initRelation_iff` in place of the named one — already have it).
2. **Extraction lemmas** (Boolean unfolding of the four conjuncts):
   `check_false_cases : check = false → okReg = false ∨ okWait = false ∨ …` (trivial
   from `Bool.and_eq_false`), then per conjunct, mirroring named
   `fst_checkWellSynchronized`/`exists_failing_pair` (named 2341):
   - `exists_failing_reg_pair` (mode 1 data; note `registrantGen`-based, so the
     extraction also decodes `c1`'s command kind);
   - `exists_failing_wait` (three-way disjunction for 2a/2b/2c);
   - `exists_failing_init_pair`; `exists_failing_dup_init`.
3. **In-edge reductions**: `happensBefore_arrive_nb` (port of named
   `happensBefore_arrive`, 2296) and `happensBefore_arrive_mb` — targets with only
   program-order in-edges (`initRelation_cases` shows all barrier edges target
   `sync_nb`/`wait_mb`).
4. **Guard absurdity**: `interleaveGuard_full_absurd` ports ×2 kinds (named 8675).
5. **Persistence lemmas** (chain inductions in the style of `blocked_persists`):
   - `uninitialized_until_init`: if no step of `τ'[0..t)` executes an `init_mb sb`,
     then `BM sb = uninitialized` at `t` (only `mb_init` moves `count` off `none`;
     arrives/waits/recycles on `sb` all *require* `some`);
   - `count_some_persists`: `(BM sb).count = some n` is forever (nothing
     de-initializes);
   - drop-classification: a step dropping an `arrive_mb sb` (resp. `init_mb sb`,
     `wait_mb`) head has source `BM sb` initialized (resp. uninitialized, initialized)
     — small case analyses like `sync_drop_recycles`.
6. **Arrival-count invariant** (used by 2b *and* 2c):
   `arrived_eq : (s_t.BM sb).arrived + n · recycleCount (.inr sb) τ' t = #(arrive_mb sb steps in τ'[0..t))`
   for initialized barriers with count `n` — chain induction; each rule's contribution
   is ±0/+1/−n. Corollary `never_full_of_missing_arrival`: if some `Reg(sb, k)`-arrival
   (`k ≤ r`) has not yet executed, `sb` cannot be full at recycle-count `r` — this is
   what keeps the recycle count frozen in the sprint/drain constructions.

## 3. Phase B — the reversal core

7. `reverse_barrier_contradiction` (port of named 2252, ℤ-valued and generalized):
   `c1` a *registrant* on `b` with `pointGen c1 = some k`; `ca` **any** barrier op on
   `b` with `pointGen ca = some (k+1)`; `¬ happensBefore c1 ca → False`. Key reading
   lemma `le_of_genValue : c.genValue r = g → g ≤ (r : ℤ)` (registrants: `= r`; waits:
   `r` or `r − 1`): the reversal gives `ca` before `c1`, so
   `k + 1 ≤ r_ca ≤ r_c1 = k` — `omega`. The generalization to wait-`ca` is what mode
   2b's first case consumes; mode 1a uses it with both registrants.
8. `firstInstr_highGen_not_wellSynchronized` — named port (8395–8594, ~200 lines),
   `.inl` only. Check its internal dependencies while porting (it sits late in the
   named file; if it leans on soundness-side helpers, inline what's needed).
9. `firstInstr_use_err` — Flag 2's shortcut: `T.prog t = (arrive_mb sb | wait_mb sb ph) :: rest → ¬ T.WellSynchronized`.
   Two-step trace + `completeTrace_ends_done`. ~40 lines.

## 4. Phase C — init modes (3, 4)

10. `init_ordering_false` (mode 3): `¬ hb(ip, u)` (points differ since commands differ)
    → `exists_reversing_trace` gives `τ'` with `time(u) < time(ip)`; `okUniqueInit`'s
    *data are not available here* — but uniqueness is not needed: `u` before *this* `ip`
    is not yet a contradiction if another init exists… so mode 3 must either (a) use
    mode 4 first: if `okUniqueInit` fails we're in mode 4; hence when proving mode 3 we
    may assume `okUniqueInit = true`, i.e. `ip` is the *only* init of `sb`; then before
    `ip` in `τ'` no init of `sb` has run (`uninitialized_until_init` + uniqueness), so
    `u`'s executing step (needs `count = some`) is impossible. Assembly must therefore
    dispatch mode 4 *before* mode 3 (or pass `okUniqueInit = true` into the mode-3
    lemma).
11. `unique_init_false` (mode 4): both inits execute in `τ` (WS gives `some`
    generations, hence times); order them; the later one drops an `init_mb` head from
    an initialized barrier (`count_some_persists` from the earlier init) —
    contradiction with the drop-classification. No reversal needed.

## 5. Phase D — mode 2b, the sync-shaped two-case argument

RESOLVED (2026-07-07): mirror the named **sync** sub-case structure (not the arrive
reduction — `wait_mb` targets have `arriveWait` in-edges, so "only program order enters"
fails for waits; rohany confirms the named `(c1, c3)` shape is the intended argument).
The sprint construction from the earlier draft is dropped.

Data: `c ∈ Reg(sb, g−1)` (an `arrive_mb`, gen `g−1`), `w` a wait with gen `g ≥ 1`,
`c3 = pred(w)`, `c ≠ c3`, `¬ hb(c, c3)`. Split on `hb(c, w)`:

- **`¬ hb(c, w)`** — direct reversal via the generalized
  `reverse_barrier_contradiction` (Phase B item 7) with `c1 := c`, `ca := w`.
- **`hb(c, w)`** — `competing_arrive_wait_false`, a sibling of `competing_sync_false`:
  run the ideal `G = {η | ¬ hb(c, η)}` to its cut (`run_ideal`/`reach_cut_aux`):
  - `w` heads its thread at the cut: `c3 ∈ G` (hypothesis) and `w ∈ F` (`hb(c,w)`),
    so `fcut(w.thread) = w.idx`;
  - `c ∈ F` is unexecuted at the cut, so round `g−1` of `sb` is incomplete and
    `recycleCount (.inr sb) ≤ g − 1` there (`never_full_of_missing_arrival` +
    the arrival invariant; the τ'-generation of `c` is `g−1` by WS transfer);
  - **drain** any pending full barrier at the cut: the cut has empty blocked lists
    (`run_ideal`'s conclusion), so recycles there advance no program — `Gdone` is
    preserved — and `sb` itself cannot fill past `g−1` (round incomplete);
  - **fire `w`**: pass (phase mismatch) observes `r − 1 ≤ g − 2 ≠ g`; block parks `w`,
    complete angelically (`exists_completeTrace` + the chain-glue patterns of
    `run_ideal`): `w` wakes at the next `sb`-recycle `≤ #g`, observing `≤ g − 1 ≠ g`,
    or never wakes and the trace cannot end `done` (nonempty program) —
    `completeTrace_ends_done` refutes;
  - read the contradiction through `hws.2 τ τ''` + `isGenOf_genValue`.

The cut-drain-fire-complete glue is shared with the Phase-F ports
(`competing_sync_false` has exactly this skeleton) — factor the common pieces
(drain-at-cut, fire-and-complete splicing, gen-reading in the spliced trace) into
helpers usable by all three.

## 6. Phase E — mode 2c, the upper bound (Flag 1 fix agreed)

With the amended check, the failing data include `T.initCountOf sb = some n` and
`|Reg(sb, g+1)| = n`. Argument:
- Every arrival `x` of generation `≤ g+1` satisfies `¬ hb(w, x)`: `x` precedes recycle
  `#(gen(x)+1) ≤ #(g+2)` and… directly: in `τ`, `time(x) < time(w)` would make
  `hb(w,x)`'s soundness give `time(w) ≤ time(x)` — contradiction. (For gen `≤ g`
  arrivals `time(x) <` recycle `#(g+1) ≤ r_w`-th recycle `< time(w)` in `τ`; for gen
  `g+1` arrivals use the *hypothesis* — no `(w, c⁺) ∈ hb` — plus Pillar A.)
- Run `run_ideal` with `η₁ := w`: all arrivals of generations `0..g+1` land in the
  `G`-prefix (they are `¬ hb(w,·)` points). Rounds `0..g` are complete
  (`gen(c⁺) = g+1` presupposes `g+1` recycles), so the prefix contains
  `n·(g+2)` `sb`-arrivals.
- The arrival invariant gives: at `w`'s step, `arrived = total − n·r < n` is required
  for `w` to step at all (the interleave guard `hmbar` — `interleaveGuard_full_absurd`),
  forcing `r ≥ g + 2`.
- `gen_{τ'}(w) ∈ {r, r−1} ≥ g+1 > g` — contradiction with WS-transfer. `omega` on ℤ.
- `wait_upper_bound_false`, ~250 lines.

## 7. Phase F — mode 1 (registrant check)

- `.inr` (both `arrive_mb`): `happensBefore_arrive_mb` reduces `hb(c1, c2)` to
  `c1 = c2` (kills via `gen c2 = gen c1 + 1`) or `hb(c1, c3)` (kills by hypothesis);
  then `reverse_barrier_contradiction`. idx-0 via `firstInstr_use_err`. Small.
- `.inl`: port the named dispatch plus its two operational lemmas:
  - `competing_sync_false` (named 7445–7770, ~330 lines) — run-ideal cut with
    `η₁ := c1`, fire `c2`'s `sync` into `c1`'s round;
  - `competing_arrive_sync_false` (named 7771–8394, ~620 lines) — same with `c1` an
    `arrive`.
  These use the (now-proven) mbarrier `run_ideal`/cut lemmas; the ports add mb rule
  cases to their internal case analyses but the barrier under attack is named, so the
  new cases are all "BM untouched" no-ops. This is the bulkiest but most mechanical
  phase.

## 8. Phase G — assembly

`not_wellSynchronized_of_check_false`: `Bool` decomposition → dispatch order
**4 → 3 → 1b → 1a → 2a → 2b → 2c** (mode 3 assumes mode 4 passed, per Phase C).
Then re-verify `checkWellSynchronized_correct_impl` picks it up, axioms clean modulo
the remaining `wellSynchronized_of_check` sorry.

## 9. Build order / checkpoints

A (extraction + Pillar A) → B (reversal core; mode 1b done) → C (modes 3, 4 done) →
F-`.inr` (cheap win) → D (mode 2b) → E (mode 2c, after Flag 1 decision) → F-`.inl`
(the big ports) → G. Each phase ends with a green, lint-clean build; sorries only on
not-yet-reached mode lemmas.

Estimated new code: ~2.5–3k lines (dominated by Phase F `.inl` ports and Phase D).
