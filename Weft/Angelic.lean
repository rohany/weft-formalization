/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import Weft.WellSynchronized
import Weft.CheckWellSynchronized

/-!
# Sequential composition and angelic completion

This file introduces the *sequential composition* `A ⨾ B` of two CTAs — each
thread runs `A`'s program and then `B`'s — and states (without proof) the
**angelic completion** property:

> If `A` is well-synchronized and `A ⨾ B` is well-synchronized, then every successful
> trace of `A` can be extended to a successful trace of `A ⨾ B`.

Intuitively, no matter how the scheduler resolves the nondeterminism while running
`A`, that partial execution is always a *prefix* of some successful run of the
whole `A ⨾ B`: running `A` first never paints `A ⨾ B` into a corner.

## Composition

`A ⨾ B` (`CTA.seq`) is only meaningful when `A` and `B` are two phases of the *same*
kernel — i.e. they have the **same set of threads** (`A.ids = B.ids`). This equality
is a required argument, so the composition is simply not constructible otherwise.
The thread set is then `A.ids`, and `(A ⨾ B).prog i = A.prog i ++ B.prog i`.

## Relating the two executions — `Config.seqLift`

A trace of `A` is a `List Config` whose configurations carry `A`-derivatives, while
a trace of `A ⨾ B` carries `A ⨾ B`-derivatives, so the two cannot be compared
directly. `Config.seqLift A B` maps a configuration of `A` to the corresponding
configuration of `A ⨾ B` by appending `B`'s program to every thread's *remaining*
program. The crucial point is that the **state** `(E, B)` is shared: while `A ⨾ B`
is still inside its `A`-phase it performs exactly the same synchronization steps as
`A` alone, so a configuration `run s C` of `A` lifts to `run s (C with B appended)`
with the same `s`. A finished `A`-configuration (`done s`) lifts to the `A ⨾ B`
configuration in which `A` is done and `B` is poised to start.

The lift appends programs with `CTA.appendTail`, a *total* program-concatenation
(over the union of thread sets) that coincides with `CTA.seq` exactly when the two
CTAs share their threads — which they do for every configuration of an actual
`A`-trace. "`t` is a prefix of `t'`" is then `t.map (Config.seqLift A B) <+: t'`.
-/

namespace Weft

/-- Sequential composition `A ⨾ B`: each thread runs `A`'s program and then `B`'s.
Valid **only when `A` and `B` have the same threads** (`hids : A.ids = B.ids`) — two
phases of one kernel — so the equality is a required argument. The thread set is
`A.ids` and `(A ⨾ B).prog i = A.prog i ++ B.prog i`. -/
def CTA.seq (A B : CTA) (hids : A.ids = B.ids) : CTA where
  ids := A.ids
  prog := fun i => A.prog i ++ B.prog i
  nil_outside_ids := by
    intro i hi
    show A.prog i ++ B.prog i = []
    rw [A.nil_outside_ids i hi, B.nil_outside_ids i (hids ▸ hi)]; rfl
  ids_nonempty := A.ids_nonempty

/-- `A` with every thread finished (all programs empty), keeping `A`'s threads.
Describes the `A`-half of an `A ⨾ B` configuration once `A` is done. -/
def CTA.emptied (A : CTA) : CTA where
  ids := A.ids
  prog := fun _ => []
  nil_outside_ids := fun _ _ => rfl
  ids_nonempty := A.ids_nonempty

/-- `B`'s programs appended to `C`'s remaining programs, over the *union* of their
threads — a total operation (no `ids` hypothesis) used to lift configurations of `A`
into `A ⨾ B`. When `C` and `B` share their threads it agrees with `CTA.seq`. -/
def CTA.appendTail (C B : CTA) : CTA where
  ids := C.ids ∪ B.ids
  prog := fun i => C.prog i ++ B.prog i
  nil_outside_ids := by
    intro i hi
    simp only [Finset.mem_union, not_or] at hi
    show C.prog i ++ B.prog i = []
    rw [C.nil_outside_ids i hi.1, B.nil_outside_ids i hi.2]; rfl
  ids_nonempty := by
    obtain ⟨i, hi⟩ := C.ids_nonempty
    exact ⟨i, Finset.mem_union_left _ hi⟩

/-- Lift a configuration of `A` to the corresponding configuration of `A ⨾ B`,
appending `B`'s program to each thread's remaining program (the state `s` is
unchanged, since `A ⨾ B` performs the same steps while in its `A`-phase). A finished
`A`-configuration (`done`) becomes the `A ⨾ B` configuration in which `A` is done and
`B` is about to start. -/
def Config.seqLift (A B : CTA) : Config → Config
  | .run s C => .run s (C.appendTail B)
  | .done s  => .run s (A.emptied.appendTail B)
  | .err T   => .err (T.appendTail B)

/- CLAUDE: Place helper methods for proving the angelic prefix lemma between here: -/

/-- Two CTAs are equal once their thread sets and program maps agree — the
well-formedness fields are propositions, hence irrelevant. -/
theorem CTA.ext {C₁ C₂ : CTA} (hids : C₁.ids = C₂.ids) (hprog : C₁.prog = C₂.prog) :
    C₁ = C₂ := by
  cases C₁; cases C₂; subst hids; subst hprog; rfl

/-- The source of any `CTAStep` is a `run` configuration. -/
theorem CTAStep.run_source {C C' : Config} (h : CTAStep C C') :
    ∃ s T, C = Config.run s T := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- A thread step is unaffected by program text appended *after* the part it
touches: it acts only on the head command, so appending `Q` carries through. (Only
the six non-error rules can occur, since the target is a `run` configuration.) -/
theorem ThreadStep.appendProg {s s' : State} {i : ThreadId} {P P' Q : Prog}
    (hstep : ThreadStep (.run s i P) (.run s' i P')) :
    ThreadStep (.run s i (P ++ Q)) (.run s' i (P' ++ Q)) := by
  cases hstep with
  | read_noop => exact .read_noop
  | write_noop => exact .write_noop
  | arrive_configure he hb => exact .arrive_configure he hb
  | arrive_register he hb hpos hlt => exact .arrive_register he hb hpos hlt
  | sync_configure he hb => exact .sync_configure he hb
  | sync_block he hb hpos hlt => exact .sync_block he hb hpos hlt

/-- **Simulation.** A `run → run` CTA step (`interleave` or `recycle`) of `C` lifts
to the same step of `C.appendTail B`: appending `B`'s not-yet-run programs changes
neither the state nor the head commands, so the rule still fires. This is the
engine behind angelic completion — running `A` inside `A ⨾ B` mirrors running `A`. -/
theorem CTAStep.appendTail {s s' : State} {C C' : CTA} (B : CTA)
    (hstep : CTAStep (Config.run s C) (Config.run s' C')) :
    CTAStep (Config.run s (C.appendTail B)) (Config.run s' (C'.appendTail B)) := by
  cases hstep with
  | @interleave _ _ _ i P' hi hbar hth =>
    have hi' : i ∈ (C.appendTail B).ids := Finset.mem_union_left _ hi
    have hth' : ThreadStep (.run s i ((C.appendTail B).prog i)) (.run s' i (P' ++ B.prog i)) :=
      hth.appendProg
    have hCTA : (C.appendTail B).set i hi' (P' ++ B.prog i) = (C.set i hi P').appendTail B := by
      apply CTA.ext
      · rfl
      · funext j
        simp only [CTA.set, CTA.appendTail, Function.update_apply]
        by_cases hj : j = i <;> simp [hj]
    rw [← hCTA]
    exact CTAStep.interleave hi' hbar hth'
  | @recycle _ _ b I A n hb hfull hpark =>
    have hpark' : ∀ j ∈ I, ((C.appendTail B).prog j).head? = some (Cmd.sync b n) := by
      intro j hj
      have hp := hpark j hj
      change ((C.prog j) ++ B.prog j).head? = some (Cmd.sync b n)
      cases hpj : C.prog j with
      | nil => rw [hpj] at hp; simp at hp
      | cons x xs => rw [hpj] at hp; simpa using hp
    have hCTA : (C.appendTail B).wake I = (C.wake I).appendTail B := by
      apply CTA.ext
      · rfl
      · funext j
        by_cases hj : j ∈ I
        · have hne : C.prog j ≠ [] := by
            have := hpark j hj; intro h; rw [h] at this; simp at this
          obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
          simp [CTA.wake, CTA.appendTail, hj, hxs]
        · simp [CTA.wake, CTA.appendTail, hj]
    rw [← hCTA]
    exact CTAStep.recycle hb hfull hpark'

/-- Every configuration of a chain except the last is a `run` configuration (it has
a successor, and `CTAStep` sources are `run`). In particular this holds for every
element of `l.dropLast`. -/
theorem mem_dropLast_isRun : ∀ {l : List Config}, List.IsChain CTAStep l →
    ∀ C ∈ l.dropLast, ∃ s T, C = Config.run s T := by
  intro l
  induction l with
  | nil => intro _ C hC; simp at hC
  | cons a rest ih =>
    cases rest with
    | nil => intro _ C hC; simp at hC
    | cons b rest' =>
      intro hl C hC
      rw [List.isChain_cons_cons] at hl
      rw [List.dropLast_cons_cons, List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact CTAStep.run_source hl.1
      · exact ih hl.2 C hC'

/-- Lifting a chain of `run` configurations through `Config.seqLift` (i.e. appending
`B`) is again a chain, by the simulation lemma `CTAStep.appendTail`. -/
theorem isChain_seqLift (A B : CTA) : ∀ {l : List Config},
    (∀ C ∈ l, ∃ s T, C = Config.run s T) → List.IsChain CTAStep l →
    List.IsChain CTAStep (l.map (Config.seqLift A B)) := by
  intro l
  induction l with
  | nil => intro _ _; exact List.IsChain.nil
  | cons a rest ih =>
    intro hrun hl
    cases rest with
    | nil => simp
    | cons b rest' =>
      rw [List.isChain_cons_cons] at hl
      obtain ⟨sa, Ca, rfl⟩ := hrun a (by simp)
      obtain ⟨sb, Cb, rfl⟩ := hrun b (by simp)
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      refine ⟨CTAStep.appendTail B hl.1, ?_⟩
      have := ih (fun C hC => hrun C (List.mem_cons_of_mem _ hC)) hl.2
      rwa [List.map_cons] at this

/-- The support invariant `barriersWithin S` propagates from the head of a chain to
every configuration along it (it holds initially and is preserved by every step). -/
theorem barriersWithin_chain (S : Finset Barrier) : ∀ {l : List Config} {C₀ : Config},
    List.IsChain CTAStep l → l.head? = some C₀ → C₀.barriersWithin S →
    ∀ C ∈ l, C.barriersWithin S := by
  intro l
  induction l with
  | nil => intro C₀ _ hhead _ C hC; simp at hC
  | cons a rest ih =>
    intro C₀ hchain hhead hinv C hC
    rw [List.head?_cons, Option.some.injEq] at hhead; subst hhead
    cases rest with
    | nil => rw [List.mem_singleton] at hC; subst hC; exact hinv
    | cons b rest' =>
      rw [List.isChain_cons_cons] at hchain
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact hinv
      · exact ih hchain.2 rfl (inv_preserved S hchain.1 hinv) C hC'

/-- Under matching thread sets, the total append `A.appendTail B` *is* the genuine
composition `A ⨾ B`. -/
theorem CTA.appendTail_eq_seq {A B : CTA} (hids : A.ids = B.ids) :
    A.appendTail B = A.seq B hids := by
  apply CTA.ext
  · change A.ids ∪ B.ids = A.ids
    rw [← hids, Finset.union_self]
  · rfl

/- and here. -/

/- ### This is the main theorem. -/

/-- **Angelic completion** (the extension half). If the composition `A ⨾ B` is
well-synchronized, then every *successful* trace `t` of `A` (`IsSuccessfulTraceFrom`
— a complete trace that runs `A` to `done`) is a prefix of some successful trace `t'`
of `A ⨾ B`: any execution that runs `A` to completion can always be continued to a
successful run of the whole composition. Here "`t` is a prefix of `t'`" means that
lifting each `A`-configuration into `A ⨾ B` (`Config.seqLift`) yields an initial
segment of `t'`.

This is a `∀`-statement over *given* successful traces of `A`, so it does **not**
require `A` itself to be well-synchronized — only `A ⨾ B`. The companion existence
fact, "a successful trace of `A` exists" (which is what needs `WS(A)`), is
`CTA.WellSynchronized.exists_successfulTrace`; `seq_angelic_completion` below bundles
the two.

Why `t.dropLast` and not `t`. A successful trace of `A` ends `… ⤳ run s C ⤳ done s`,
where the final step fires `CTAStep.done`, which requires `IsDone C` — every thread's
program already empty. So the *last two* configurations of `t` are the all-empty
`run s C` and the terminal marker `done s`. Both lift to the **same** `A ⨾ B`
configuration `run s (… ⨾ B)` (programs `[] ++ B.prog i = B.prog i`, state `s`
shared), so `t.map (Config.seqLift A B)` would end in a duplicated configuration —
impossible as a prefix of a `CTAStep`-chain, which has no self-loop `C ⤳ C`. The
mismatch is intrinsic: `done s` is `A`-specific bookkeeping ("the `A`-CTA finished"),
but in `A ⨾ B` the CTA has *not* finished there — `B` runs on from exactly that
all-empty-`A` configuration. Dropping `t`'s terminal `done` (`t.dropLast`) keeps
precisely the part of `A`'s execution literally shared with `A ⨾ B`. -/
theorem CTA.WellSynchronized.seq_angelic_prefix {A B : CTA} (hids : A.ids = B.ids)
    (hAB : (A.seq B hids).WellSynchronized) :
    ∀ t, IsSuccessfulTraceFrom (Config.run State.initial A) t →
      ∃ t', IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) t' ∧
        t.dropLast.map (Config.seqLift A B) <+: t' := by
  intro t ht
  -- Correspondence with the four-step pen-and-paper strategy:
  --   Step 1 ("∃ a successful trace of A, because WS(A)") — NOT done here: this lemma
  --     is `∀` over a *given* successful trace `t` of A, so it never produces one and
  --     never needs `WS(A)`. Existence is factored into the separate lemma
  --     `exists_successfulTrace`; `seq_angelic_completion` below composes the two.
  --   Step 3 ("run that A-trace inside A ⨾ B") — see "Step 3" below: lift `t.dropLast`
  --     by appending B (`Config.seqLift`); the simulation lemma `CTAStep.appendTail`
  --     makes the lifted list `P` a genuine execution prefix of `A ⨾ B`.
  --   Step 2 ("A ⨾ B also has completing traces") — see "Step 2" below: from the
  --     reached configuration `C_star` ("A done, B poised") strong normalization
  --     (`exists_completeTrace`) yields a complete continuation `τ` to glue onto `P`.
  --   Step 4 ("AFSOC B cannot be completed ⇒ deadlock ⇒ contradicts WS(A ⨾ B)") —
  --     DIVERGENCE (logically equivalent): instead of arguing by contradiction, we
  --     observe the glued trace `t'` is a complete trace of `A ⨾ B` and apply
  --     `completeTrace_ends_done` — the lemma that *every* complete trace of a WS
  --     configuration is successful, which is exactly the fact your contradiction
  --     appeals to. See "Step 4" below.
  obtain ⟨⟨htIC, hthead⟩, s_d, ht_done⟩ := ht
  -- `t` has length ≥ 2: it starts at `run init A` and ends at `done s_d`.
  obtain ⟨c1, trest, rfl⟩ :
      ∃ c1 trest, t = Config.run State.initial A :: c1 :: trest := by
    rcases t with _ | ⟨c, _ | ⟨c1, tr⟩⟩
    · simp at hthead
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      simp only [List.getLast?_singleton, Option.some.injEq] at ht_done
      rw [hthead] at ht_done; simp at ht_done
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      subst hthead; exact ⟨c1, tr, rfl⟩
  -- Step 3: "run the A-trace inside A ⨾ B". The lifted running prefix `P` is
  -- `t.dropLast` with B appended to every config; `isChain_seqLift` (driven by the
  -- simulation lemma `CTAStep.appendTail`) certifies it is a real A ⨾ B execution.
  set P := (Config.run State.initial A :: c1 :: trest).dropLast.map (Config.seqLift A B) with hPdef
  have hPchain : List.IsChain CTAStep P :=
    isChain_seqLift A B (mem_dropLast_isRun htIC.subtrace) htIC.subtrace.dropLast
  have hPne : P ≠ [] := by rw [hPdef]; simp
  have hPhead : P.head? = some (Config.run State.initial (A.seq B hids)) := by
    rw [hPdef, List.dropLast_cons_cons, List.map_cons, List.head?_cons,
      Config.seqLift, CTA.appendTail_eq_seq hids]
  -- `C_star` is the last configuration of `P` ("`A` done, `B` poised to start")
  obtain ⟨C_star, hC_star⟩ : ∃ C, P.getLast? = some C := by
    cases hPl : P.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hPl; exact absurd hPl hPne
    | some C => exact ⟨C, rfl⟩
  have hC_starmem : C_star ∈ P := List.mem_of_getLast? hC_star
  -- `C_star` satisfies the support invariant (it is reachable from `init (A ⨾ B)`)
  have hbw : C_star.barriersWithin (A.seq B hids).barrierSet :=
    barriersWithin_chain _ hPchain hPhead barriersWithin_initial C_star hC_starmem
  -- Step 2: "A ⨾ B also has completing traces". From `C_star` ("A done, B poised")
  -- strong normalization gives a complete continuation `τ` of the A ⨾ B run.
  obtain ⟨τ, hτIC, hτhead⟩ :=
    exists_completeTrace (A.seq B hids).barrierSet C_star hbw
  obtain ⟨τtail, rfl⟩ : ∃ l, τ = C_star :: l := by
    cases τ with
    | nil => simp at hτhead
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hτhead
      subst hτhead; exact ⟨l, rfl⟩
  have hτchain : List.IsChain CTAStep (C_star :: τtail) := hτIC.subtrace
  rw [List.isChain_cons] at hτchain
  -- glue: `t' = P ++ τtail`
  -- (1) the glued list is a chain
  have hchain' : List.IsChain CTAStep (P ++ τtail) := by
    refine hPchain.append hτchain.2 ?_
    intro x hx y hy
    rw [hC_star, Option.mem_some_iff] at hx; subst hx
    exact hτchain.1 y hy
  -- `P ++ τtail` ends exactly where `τ` ends, via `P = P.dropLast ++ [C_star]`
  have hsplit : P ++ τtail = P.dropLast ++ (C_star :: τtail) := by
    have hgl : P.getLast hPne = C_star := by
      have h := List.getLast?_eq_some_getLast hPne
      rw [hC_star] at h; exact (Option.some.injEq _ _).mp h.symm
    conv_lhs => rw [← List.dropLast_concat_getLast hPne, hgl]
    simp
  -- (2) the glued list ends in a terminal configuration (the same one `τ` does)
  have hends' : ∃ Cₙ, (P ++ τtail).getLast? = some Cₙ ∧
      ((∃ s, Cₙ = Config.done s) ∨ (∃ T, Cₙ = Config.err T) ∨ Config.Stuck Cₙ) := by
    obtain ⟨Cₙ, hτlast, hterm⟩ := hτIC.ends
    exact ⟨Cₙ, by rw [hsplit]; exact List.mem_getLast?_append_of_mem_getLast? hτlast, hterm⟩
  -- (3) it starts at `init (A ⨾ B)`
  have hhead' : (P ++ τtail).head? = some (Config.run State.initial (A.seq B hids)) := by
    rw [List.head?_append_of_ne_nil _ hPne, hPhead]
  have hICF : IsCompleteTraceFrom (Config.run State.initial (A.seq B hids)) (P ++ τtail) :=
    ⟨⟨hchain', hends'⟩, hhead'⟩
  -- Step 4: the glued trace `t' = P ++ τtail` is a complete trace of `A ⨾ B`. Rather
  -- than assume-for-contradiction that it deadlocks, `completeTrace_ends_done hAB`
  -- (every complete trace of the WS configuration `A ⨾ B` ends in `done`) gives
  -- directly that `t'` is successful; and `P` — i.e. `t.dropLast.map seqLift` — is a
  -- prefix of it by construction.
  exact ⟨P ++ τtail, ⟨hICF, completeTrace_ends_done hAB hICF⟩, List.prefix_append P τtail⟩

/-- **Angelic completion** (existence and extension). If `A` and `A ⨾ B` are both
well-synchronized, then there *is* a successful trace `t` of `A`, and it is a prefix
of a successful trace `t'` of `A ⨾ B`. This is the headline result: it composes
`exists_successfulTrace` (which uses `WS(A)` to produce `t`) with `seq_angelic_prefix`
(which uses `WS(A ⨾ B)` to extend it). -/
theorem CTA.WellSynchronized.seq_angelic_completion {A B : CTA} (hids : A.ids = B.ids)
    (hA : A.WellSynchronized) (hAB : (A.seq B hids).WellSynchronized) :
    ∃ t t', IsSuccessfulTraceFrom (Config.run State.initial A) t ∧
            IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) t' ∧
            t.dropLast.map (Config.seqLift A B) <+: t' := by
  obtain ⟨t, ht⟩ := hA.exists_successfulTrace
  obtain ⟨t', ht', hpre⟩ := seq_angelic_prefix hids hAB t ht
  exact ⟨t, t', ht, ht', hpre⟩

/-- Lifting a configuration into `A ⨾ B` appends `B`'s program to every thread's
remaining program — at the level of `progOf`: `(Config.seqLift A B X).progOf i =
X.progOf i ++ B.prog i`. (For a finished `A`-configuration `done`, `X.progOf i = []`,
so the lift's program is exactly `B.prog i`.) -/
theorem Config.seqLift_progOf (A B : CTA) (X : Config) (i : ThreadId) :
    (Config.seqLift A B X).progOf i = X.progOf i ++ B.prog i := by
  cases X <;> rfl

/-- The configuration just before a successful trace's terminal `done` has every
thread finished. The final step `X ⤳ done` can only be `CTAStep.done`, whose premise
`CTA.IsDone` makes every thread's program empty; so `X.progOf i = []` for every `i`. -/
theorem progOf_penultimate_done {t : List Config} (hchain : List.IsChain CTAStep t)
    {sd : State} (hlast : t.getLast? = some (Config.done sd))
    {X : Config} (hX : t.dropLast.getLast? = some X) (i : ThreadId) : X.progOf i = [] := by
  have hne : t ≠ [] := by intro h; rw [h] at hlast; simp at hlast
  have hdropne : t.dropLast ≠ [] := by intro h; rw [h] at hX; simp at hX
  -- name the two relevant configurations via `getLast`
  have hgl : t.getLast hne = Config.done sd := by
    have h := List.getLast?_eq_some_getLast hne; rw [hlast, Option.some.injEq] at h; exact h.symm
  have hgl' : t.dropLast.getLast hdropne = X := by
    have h := List.getLast?_eq_some_getLast hdropne; rw [hX, Option.some.injEq] at h; exact h.symm
  -- `t = t.dropLast.dropLast ++ X :: done sd :: []`
  have e1 : t.dropLast ++ [Config.done sd] = t := by
    have h := List.dropLast_concat_getLast hne; rwa [hgl] at h
  have e2 : t.dropLast.dropLast ++ [X] = t.dropLast := by
    have h := List.dropLast_concat_getLast hdropne; rwa [hgl'] at h
  have hdecomp : t.dropLast.dropLast ++ X :: Config.done sd :: [] = t := by
    rw [show X :: Config.done sd :: [] = [X] ++ [Config.done sd] from rfl, ← List.append_assoc,
      e2, e1]
  -- the last step is `CTAStep X (done sd)`; only `CTAStep.done` can produce a `done`
  have hstep : CTAStep X (Config.done sd) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain hdecomp.symm
  cases hstep with
  | @done s T hdone _ =>
    change T.prog i = []
    by_cases hi : i ∈ T.ids
    · exact hdone i hi
    · exact T.nil_outside_ids i hi

/-- **No happens-before edge runs from `B` back into `A`.** Take two straight-line
fragments `A` and `B` of one kernel (`hids : A.ids = B.ids`) with both `A` and the
composition `A ⨾ B` well-synchronized, and let `τ` be a successful trace of `A ⨾ B`,
off which Figure 4 builds the happens-before relation `happensBefore (A ⨾ B) τ`. Then
that relation never orders a `B`-instruction before an `A`-instruction: there is no
pair `(s, d)` in it with `s` in the `B`-phase and `d` in the `A`-phase.

A program point `η = ⟨i, k⟩` of `A ⨾ B` indexes into `(A ⨾ B).prog i = A.prog i ++
B.prog i`, so it is **in `A`** (`d` here) exactly when `k < |A.prog i|` — the command
comes from `A`'s fragment — and **in `B`** (`s` here) exactly when `|A.prog i| ≤ k <
|A.prog i| + |B.prog i|` — a genuine point of `A ⨾ B` whose command comes from the
appended `B`.

Proof idea (uses Lemma 1's soundness, `happensBefore_sound`, with the angelic trace
of `seq_angelic_completion`): if `s` were happens-before `d`, soundness would force
`t(s) ≤ t(d)` in *every* complete trace of `A ⨾ B`. But `WS(A)` produces — via
`seq_angelic_completion` — the angelic schedule that runs `A` entirely to completion
and only then runs `B`; in it every `A`-instruction (so `d`) executes strictly before
every `B`-instruction (so `s`), i.e. `t(d) < t(s)`. Contradiction.
NOTE: rohany (this is not a major theorem, but one that wouldn't be possible if the
angelic approach was not actually true. )
-/
theorem CTA.WellSynchronized.seq_no_happensBefore_B_to_A {A B : CTA} (hids : A.ids = B.ids)
    (hA : A.WellSynchronized) (hAB : (A.seq B hids).WellSynchronized)
    {τ : List Config}
    (hτ : IsSuccessfulTraceFrom (Config.run State.initial (A.seq B hids)) τ) :
    ¬ ∃ s d : ProgPoint,
        happensBefore (A.seq B hids) τ s d ∧
        -- `s ∈ B`: `s` is a program point of `A ⨾ B` lying in the appended `B`-part.
        ((A.prog s.thread).length ≤ s.idx ∧
          s.idx < (A.prog s.thread).length + (B.prog s.thread).length) ∧
        -- `d ∈ A`: `d`'s command comes from `A`'s fragment.
        d.idx < (A.prog d.thread).length := by
  rintro ⟨s, d, hR, ⟨hsB1, hsB2⟩, hdA⟩
  -- `progOf` of the start configuration splits as `A.prog i ++ B.prog i`.
  have hC0prog : ∀ i, (Config.run State.initial (A.seq B hids)).progOf i
      = A.prog i ++ B.prog i := fun _ => rfl
  -- Soundness of the happens-before relation (Lemma 1, `happensBefore_sound`): since
  -- `A ⨾ B` is well-synchronized and `τ` runs it to `done`, every happens-before pair
  -- is a genuine ordering — `s` runs no later than `d` in *every* complete trace.
  have hsound := happensBefore_sound hτ hAB hR
  -- The contradiction comes from one specific schedule: the *angelic* trace `t'` that
  -- runs `A` entirely to completion and only then runs `B` (from `WS(A)` and `WS(A ⨾ B)`
  -- via `seq_angelic_completion`). Its `A`-phase is the lifted `A`-execution `P`, a
  -- prefix of `t'`.
  obtain ⟨t, t', ht, ht', hpre⟩ := CTA.WellSynchronized.seq_angelic_completion hids hA hAB
  set P := t.dropLast.map (Config.seqLift A B) with hPdef
  obtain ⟨rest, hrest⟩ := hpre              -- `hrest : P ++ rest = t'`
  obtain ⟨sdone, htlast⟩ := ht'.2
  have ht'complete : IsCompleteTraceFrom (Config.run State.initial (A.seq B hids)) t' := ht'.1
  have ht'chain : List.IsChain CTAStep t' := ht'complete.1.subtrace
  -- `d` and `s` both execute in `t'` (it ends in `done`, so every command runs).
  obtain ⟨n₂, htd⟩ : ∃ n, IsTimeOf (Config.run State.initial (A.seq B hids)) t' d n :=
    exists_time_of_ends_done (η := d) ht'complete htlast
      (by rw [hC0prog, List.length_append]; omega)
  obtain ⟨n₁, hts⟩ : ∃ n, IsTimeOf (Config.run State.initial (A.seq B hids)) t' s n :=
    exists_time_of_ends_done (η := s) ht'complete htlast
      (by rw [hC0prog, List.length_append]; omega)
  -- `P` is nonempty: `t` has length ≥ 2 (it runs from `run init A` to `done`).
  obtain ⟨sA, htAlast⟩ := ht.2
  have hthead : t.head? = some (Config.run State.initial A) := ht.1.2
  have htlen2 : 2 ≤ t.length := by
    rcases t with _ | ⟨c0, _ | ⟨c1, tr⟩⟩
    · simp at hthead
    · simp only [List.head?_cons, Option.some.injEq] at hthead
      simp only [List.getLast?_singleton, Option.some.injEq] at htAlast
      rw [hthead] at htAlast; simp at htAlast
    · simp only [List.length_cons]; omega
  have hPlen : P.length = t.length - 1 := by rw [hPdef, List.length_map, List.length_dropLast]
  have hPpos : 0 < P.length := by rw [hPlen]; omega
  have hPne : P ≠ [] := List.ne_nil_of_length_pos hPpos
  have hdropne : t.dropLast ≠ [] := fun h => hPne (by rw [hPdef, h, List.map_nil])
  -- `Cstar`, the last config of `P` ("`A` done, `B` poised"): its remaining program is
  -- exactly `B.prog i`, since the penultimate config of `t` is all-empty.
  obtain ⟨Cstar, hCstar⟩ : ∃ C, P.getLast? = some C := by
    cases hPl : P.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hPl; exact absurd hPl hPne
    | some C => exact ⟨C, rfl⟩
  have hXempty : ∀ i, (t.dropLast.getLast hdropne).progOf i = [] := fun i =>
    progOf_penultimate_done ht.1.1.subtrace htAlast (List.getLast?_eq_some_getLast hdropne) i
  have hCstarprog : ∀ i, Cstar.progOf i = B.prog i := by
    intro i
    have hmap : P.getLast? = (t.dropLast.getLast?).map (Config.seqLift A B) := by
      rw [hPdef, List.getLast?_map]
    rw [List.getLast?_eq_some_getLast hdropne, Option.map_some, hCstar, Option.some.injEq] at hmap
    rw [hmap, Config.seqLift_progOf, hXempty i, List.nil_append]
  -- index of `Cstar` in `t'`.
  have hp : P.length - 1 < P.length := by omega
  have hCstaridx : t'[P.length - 1]? = some Cstar := by
    rw [← hrest, List.getElem?_append_left hp, ← List.getLast?_eq_getElem?]; exact hCstar
  -- **P-invariant**: in `P` every thread's program is `≥ |B.prog i|` long (B intact).
  have hPinv : ∀ q (C : Config), q < P.length → t'[q]? = some C →
      ∀ i, (B.prog i).length ≤ (C.progOf i).length := by
    intro q C hq hCq i
    rw [← hrest, List.getElem?_append_left hq, hPdef, List.getElem?_map] at hCq
    obtain ⟨X', _, hCeq⟩ := Option.map_eq_some_iff.mp hCq
    rw [← hCeq, Config.seqLift_progOf, List.length_append]; omega
  -- **tail-invariant**: from `Cstar` onward every thread's program is `≤ |B.prog i|`.
  have hTinv : ∀ q (C : Config), P.length - 1 ≤ q → t'[q]? = some C →
      ∀ i, (C.progOf i).length ≤ (B.prog i).length := by
    intro q C hq hCq i
    have hsuf := progOf_suffix_index_le ht'chain i hCstaridx hq hCq
    have hle := suffix_length_le hsuf
    rwa [hCstarprog i] at hle
  -- `d` (in the `A`-phase) executes before reaching `Cstar`: `n₂ ≤ P.length - 1`.
  obtain ⟨-, -, jd, Cd, _Cd', hn₂eq, hCdj, _, hCdeq, _⟩ := id htd
  have hCdlen : (Cd.progOf d.thread).length
      = (A.prog d.thread).length + (B.prog d.thread).length - d.idx := by
    rw [hCdeq, hC0prog, List.length_drop, List.length_append]
  have hjd : jd < P.length - 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h := hTinv jd Cd hcon hCdj d.thread
    rw [hCdlen] at h; omega
  -- `s` (in the `B`-phase) executes only after `Cstar`: `P.length ≤ n₁`.
  obtain ⟨-, -, js, _Cs, Cs', hn₁eq, _, hCsj1, _, hCs'eq⟩ := id hts
  have hCs'len : (Cs'.progOf s.thread).length
      = (A.prog s.thread).length + (B.prog s.thread).length - (s.idx + 1) := by
    rw [hCs'eq, hC0prog, List.length_drop, List.length_append]
  have hjs : P.length ≤ js + 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have h := hPinv (js + 1) Cs' hcon hCsj1 s.thread
    rw [hCs'len] at h; omega
  -- assemble: `n₂ = jd+1 ≤ P.length-1 < P.length ≤ js+1 = n₁`, contradicting soundness.
  have hlt : n₂ < n₁ := by omega
  have hle : n₁ ≤ n₂ := hsound t' ht'complete n₁ n₂ hts htd
  omega

end Weft
