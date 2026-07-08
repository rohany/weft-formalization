/-
Copyright (c) 2026 Stanford University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Yadav
-/
import WeftCommon.Traces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find

/-!
# Shared well-formedness and timing infrastructure

Trace-level machinery shared by the languages of the Weft family, layered by
what it needs from the language:

* **Nothing** (generic over the `Config`/`CTA` functors and an arbitrary step
  relation): `Config.state?`, `IsSuccessfulTraceFrom`, `CTA.numCmds`, the
  chain utilities `chain_step`/`step_into_getLast`, the suffix list lemmas,
  `updateMapOn_apply`, and `cmd_at_last`.

* **The step discipline** (the `StepDiscipline` section): everything else here
  is generic once the language supplies one or two facts about how programs
  evolve under its step relation `R`, each proved per-language by cases on its
  rules:

  - `hdrop` — a step leaves each thread's program a `drop` of what it was
    (programs advance in order, never grow or rewrite);
  - `hle1` — a step shortens each thread's program by at most one command.

  From `hdrop` alone: single-step and along-the-trace suffix facts
  (`progOf_suffix_of_step`, `progOf_suffix_last`, `progOf_suffix_index_le`),
  uniqueness of execution times (`IsTimeOf.unique`), and the
  never-executes-at-the-end lemma (`noTime_at_last`). Adding `hle1`: the
  intermediate-value argument `exists_time_of_ends_done` — in a successful
  trace, every valid program point executes.

Each language re-exposes these under its usual names: aliases (`export`) for
the fully generic items, and thin same-signature wrappers discharging the
discipline facts for the parameterized ones — so call sites in the language
libraries are unchanged.
-/

namespace WeftCommon

variable {State Cmd : Type}

/-- The state component of a configuration, if it has one. `run` and `done`
carry a state; the error configuration `err` does not. -/
def Config.state? : Config State Cmd → Option State
  | .run s _ => some s
  | .done s => some s
  | .err _ => none

/-- `τ` *successfully runs `C₀` to completion*: it is a complete trace from `C₀`
(Definition 2) whose final configuration is `done`. This bundles the two facts that
a successful execution needs: that `τ` is a genuine complete trace *starting at
`C₀`* (`IsCompleteTraceFrom`, so `τ.head? = some C₀`), and that it terminates in
`done` — reaching the goal without deadlocking (a stuck `run`) or erroring (`err`). -/
def IsSuccessfulTraceFrom (R : Config State Cmd → Config State Cmd → Prop)
    (C₀ : Config State Cmd) (τ : List (Config State Cmd)) : Prop :=
  IsCompleteTraceFrom R C₀ τ ∧ ∃ s, τ.getLast? = some (Config.done s)

/-- The total number of commands remaining across a CTA's threads. -/
def CTA.numCmds (T : CTA Cmd) : Nat := ∑ i ∈ T.ids, (T.prog i).length

/-- A suffix `s` of `l` is `l.drop (|l| - |s|)`. -/
theorem List.IsSuffix.eq_drop {α} {s l : List α} (h : s <:+ l) :
    s = l.drop (l.length - s.length) := by
  obtain ⟨p, rfl⟩ := h
  rw [List.length_append, Nat.add_sub_cancel, List.drop_left]

/-- A suffix is no longer than the list. -/
theorem suffix_length_le {α} {s l : List α} (h : s <:+ l) : s.length ≤ l.length := by
  obtain ⟨p, rfl⟩ := h
  simp [List.length_append]

/-- Map update over a set of keys, pointwise: `updateMapOn f Y x` sends `a` to
`x` when `a ∈ Y` and to `f a` otherwise. -/
theorem updateMapOn_apply {α β} [DecidableEq α] (f : α → β) (Y : List α) (x : β) (a : α) :
    updateMapOn f Y x a = if a ∈ Y then x else f a := by
  induction Y with
  | nil => simp [updateMapOn]
  | cons y ys ih =>
    change Function.update (updateMapOn f ys x) y x a = _
    rw [Function.update_apply, ih]
    by_cases h : a = y
    · subst h; simp
    · simp [h, List.mem_cons]

/-- Consecutive elements of a chain step: from `List.IsChain R` with
`τ[j]? = some C` and `τ[j+1]? = some C'`, the single step `R C C'`. -/
theorem chain_step {α} {R : α → α → Prop} {τ : List α} (hchain : List.IsChain R τ)
    {j : Nat} {C C' : α} (hC : τ[j]? = some C) (hC' : τ[j + 1]? = some C') : R C C' := by
  obtain ⟨_hj, rfl⟩ := List.getElem?_eq_some_iff.mp hC
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.mp hC'
  exact (List.isChain_iff_getElem.mp hchain) j hj1

/-- In a chain, the last element is either the head (singleton) or has a
predecessor that steps to it. -/
theorem step_into_getLast {α} {R : α → α → Prop} :
    ∀ {l : List α} {x : α}, List.IsChain R l →
      l.getLast? = some x → l.head? = some x ∨ ∃ y, R y x := by
  intro l
  induction l with
  | nil => intro x _ hlast; simp at hlast
  | cons a rest ih =>
    intro x h hlast
    cases rest with
    | nil => left; rw [List.getLast?_singleton] at hlast; simpa using hlast
    | cons b t' =>
      rw [List.isChain_cons_cons] at h
      obtain ⟨hab, hbt⟩ := h
      rw [List.getLast?_cons_cons] at hlast
      rcases ih hbt hlast with hhead | hstep
      · right
        rw [List.head?_cons, Option.some.injEq] at hhead
        exact ⟨a, hhead ▸ hab⟩
      · exact Or.inr hstep

/-- The program point at index `|C₀.progOf t| - |Cₙ.progOf t|` names the command at
the head of `Cₙ.progOf t`, when the latter is a suffix of `C₀.progOf t`. -/
theorem cmd_at_last {C₀ Cₙ : Config State Cmd} {t : ThreadId} {cmd : Cmd} {c : List Cmd}
    (hsuf : Cₙ.progOf t <:+ C₀.progOf t) (hCn : Cₙ.progOf t = cmd :: c) :
    (ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length)).cmd C₀ = some cmd := by
  have hk : (C₀.progOf t).drop ((C₀.progOf t).length - (Cₙ.progOf t).length) = cmd :: c := by
    rw [← List.IsSuffix.eq_drop hsuf]; exact hCn
  change (C₀.progOf t)[(C₀.progOf t).length - (Cₙ.progOf t).length]? = some cmd
  rw [← Nat.add_zero ((C₀.progOf t).length - (Cₙ.progOf t).length), ← List.getElem?_drop, hk]
  rfl

/-! ### The step discipline

The remaining lemmas are generic in the step relation `R` given the *step
discipline*: `hdrop` (each step leaves each thread's program a `drop` of what
it was) and, where needed, `hle1` (each step shortens a program by at most
one). Each language proves these once, by cases on its own rules, and wraps
the lemmas below under its usual names. -/

section StepDiscipline

variable {R : Config State Cmd → Config State Cmd → Prop}

/-- The `hdrop` discipline fact: one step of `R` changes each thread's program
only by dropping a prefix. -/
def StepDropsPrefix (R : Config State Cmd → Config State Cmd → Prop) : Prop :=
  ∀ ⦃C C' : Config State Cmd⦄, R C C' → ∀ t, ∃ d, C'.progOf t = (C.progOf t).drop d

/-- The `hle1` discipline fact: one step of `R` shortens each thread's program
by at most one command. -/
def StepShrinksByOne (R : Config State Cmd → Config State Cmd → Prop) : Prop :=
  ∀ ⦃C C' : Config State Cmd⦄, R C C' → ∀ t,
    (C.progOf t).length ≤ (C'.progOf t).length + 1

/-- One step makes each thread's program a suffix of its previous program. -/
theorem progOf_suffix_of_step (hdrop : StepDropsPrefix R) {C C' : Config State Cmd}
    (hstep : R C C') (t : ThreadId) : C'.progOf t <:+ C.progOf t := by
  obtain ⟨d, hd⟩ := hdrop hstep t
  rw [hd]
  exact ⟨(C.progOf t).take d, List.take_append_drop d (C.progOf t)⟩

/-- Along a (sub)trace, the *last* configuration's program for a thread is a suffix
of every configuration's program for that thread — programs only shrink. -/
theorem progOf_suffix_last (hdrop : StepDropsPrefix R) (t : ThreadId) :
    ∀ {l : List (Config State Cmd)} {Cₙ : Config State Cmd},
      List.IsChain R l → l.getLast? = some Cₙ →
      ∀ C ∈ l, Cₙ.progOf t <:+ C.progOf t := by
  intro l
  induction l with
  | nil => intro Cₙ _ hlast; simp at hlast
  | cons a rest ih =>
    intro Cₙ hchain hlast C hC
    cases rest with
    | nil =>
      simp only [List.mem_singleton] at hC
      subst hC
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact List.suffix_refl _
    | cons b t' =>
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hab, hbt⟩ := hchain
      rw [List.getLast?_cons_cons] at hlast
      rw [List.mem_cons] at hC
      rcases hC with rfl | hC'
      · exact (ih hbt hlast b (by simp)).trans (progOf_suffix_of_step hdrop hab t)
      · exact ih hbt hlast C hC'

/-- Programs only shrink: at a later trace index a thread's remaining program is a
suffix of its program at an earlier index. -/
theorem progOf_suffix_index_le (hdrop : StepDropsPrefix R)
    {τ : List (Config State Cmd)} (hchain : List.IsChain R τ)
    (t : ThreadId) {p : Nat} {Cp : Config State Cmd} (hp : τ[p]? = some Cp) :
    ∀ {q : Nat}, p ≤ q → ∀ {Cq : Config State Cmd}, τ[q]? = some Cq →
      Cq.progOf t <:+ Cp.progOf t := by
  intro q hpq
  induction q, hpq using Nat.le_induction with
  | base =>
      intro Cq hq
      rw [hp, Option.some.injEq] at hq
      subst hq; exact List.suffix_refl _
  | succ q _hpq ih =>
      intro Cq hq
      have hqlt : q < τ.length := by
        have h1 : q + 1 < τ.length := (List.getElem?_eq_some_iff.mp hq).1
        omega
      have hD : τ[q]? = some τ[q] := List.getElem?_eq_getElem hqlt
      exact (progOf_suffix_of_step hdrop (chain_step hchain hD hq) t).trans (ih hD)

/-- `IsTimeOf` is a partial function: an instruction executes at most once in a trace. -/
theorem IsTimeOf.unique (hdrop : StepDropsPrefix R)
    {C₀ : Config State Cmd} {τ : List (Config State Cmd)} {η : ProgPoint} {m m' : Nat}
    (h : IsTimeOf R C₀ τ η m) (h' : IsTimeOf R C₀ τ η m') : m = m' := by
  obtain ⟨hτ, hlt, j, C, C', hm, hCj, hCj1, hCeq, hC'eq⟩ := h
  obtain ⟨_, _, j', D, D', hm', hDj, hDj1, hDeq, hD'eq⟩ := h'
  subst hm; subst hm'
  have hchain := hτ.1.subtrace
  rcases Nat.lt_trichotomy j j' with hlt' | heq | hgt
  · exfalso
    have hsuf := progOf_suffix_index_le hdrop hchain η.thread hCj1
      (show j + 1 ≤ j' by omega) hDj
    have hle := suffix_length_le hsuf
    rw [hDeq, hC'eq, List.length_drop, List.length_drop] at hle
    omega
  · omega
  · exfalso
    have hsuf := progOf_suffix_index_le hdrop hchain η.thread hDj1
      (show j' + 1 ≤ j by omega) hCj
    have hle := suffix_length_le hsuf
    rw [hCeq, hD'eq, List.length_drop, List.length_drop] at hle
    omega

/-- The command at the head of the *last* configuration's program never executes:
the program never gets shorter than at the end, so it never advances past that
command. -/
theorem noTime_at_last (hdrop : StepDropsPrefix R)
    {C₀ Cₙ : Config State Cmd} {τ : List (Config State Cmd)} {t : ThreadId}
    (hτ : IsCompleteTraceFrom R C₀ τ) (hlast : τ.getLast? = some Cₙ)
    (hpos : 0 < (Cₙ.progOf t).length) (hle : (Cₙ.progOf t).length ≤ (C₀.progOf t).length) :
    ¬ ∃ m, IsTimeOf R C₀ τ (ProgPoint.mk t ((C₀.progOf t).length - (Cₙ.progOf t).length)) m := by
  rintro ⟨m, _, _, j, C, C', _, _, hCj1, _, hC'eq⟩
  have hC'mem : C' ∈ τ := List.mem_of_getElem? hCj1
  have hsuf : Cₙ.progOf t <:+ C'.progOf t :=
    progOf_suffix_last hdrop t hτ.1.subtrace hlast C' hC'mem
  have hlen := suffix_length_le hsuf
  simp only at hC'eq
  rw [hC'eq, List.length_drop] at hlen
  omega

/-- Every command runs in a successful execution: in a complete trace from `C₀` that
ends in `done`, every valid program point `η` (`η.idx <` its program length) has a
time. Found by an integer intermediate-value argument — the program length falls from
`|C₀.progOf i|` to `0` in steps of at most one (`hle1`), so it passes through the
transition `|drop η.idx| → |drop (η.idx+1)|`; lengths pin down the suffix
(`progOf_suffix_index_le`), giving the exact `drop`s. -/
theorem exists_time_of_ends_done (hdrop : StepDropsPrefix R) (hle1 : StepShrinksByOne R)
    {C₀ : Config State Cmd} {τ' : List (Config State Cmd)} {sd : State}
    (hτ : IsCompleteTraceFrom R C₀ τ') (hlast : τ'.getLast? = some (Config.done sd))
    {η : ProgPoint} (hk : η.idx < (C₀.progOf η.thread).length) :
    ∃ n, IsTimeOf R C₀ τ' η n := by
  have hchain : List.IsChain R τ' := hτ.1.subtrace
  set i := η.thread with hidef
  have h0 : τ'[0]? = some C₀ := by
    have hgen : ∀ l : List (Config State Cmd), l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hlastidx : τ'[τ'.length - 1]? = some (Config.done sd) := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hsuffix : ∀ {j} {C : Config State Cmd}, τ'[j]? = some C →
      C.progOf i <:+ C₀.progOf i :=
    fun {j C} hCj => progOf_suffix_index_le hdrop hchain i h0 (Nat.zero_le j) hCj
  have hQlast : ((τ'[τ'.length - 1]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [hlastidx]; change (0 : Nat) < (C₀.progOf i).length - η.idx; omega
  have hex : ∃ j, ((τ'[j]?).map (fun (C : Config State Cmd) => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := ⟨τ'.length - 1, hQlast⟩
  have hQj0 := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ τ'.length - 1 := Nat.find_le hQlast
  have hQ0 : ¬ ((τ'[0]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [h0]; change ¬ (C₀.progOf i).length < (C₀.progOf i).length - η.idx; omega
  have hj0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hQj0; exact absurd hQj0 hQ0
    · exact h
  have hminj := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have hj0lt : Nat.find hex < τ'.length := by omega
  obtain ⟨C, hC⟩ : ∃ C, τ'[Nat.find hex - 1]? = some C :=
    ⟨_, List.getElem?_eq_getElem (show Nat.find hex - 1 < τ'.length by omega)⟩
  obtain ⟨C', hC'⟩ : ∃ C', τ'[Nat.find hex]? = some C' :=
    ⟨_, List.getElem?_eq_getElem hj0lt⟩
  have hCC' : τ'[Nat.find hex - 1 + 1]? = some C' := by
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hC'
  have hub : (C.progOf i).length ≤ (C'.progOf i).length + 1 :=
    hle1 (chain_step hchain hC hCC') i
  have e1 : ((τ'[Nat.find hex - 1]?).map (fun C => (C.progOf i).length)).getD 0
      = (C.progOf i).length := by rw [hC]; rfl
  have e2 : ((τ'[Nat.find hex]?).map (fun C => (C.progOf i).length)).getD 0
      = (C'.progOf i).length := by rw [hC']; rfl
  rw [e1] at hminj
  rw [e2] at hQj0
  have hlenC : (C.progOf i).length = (C₀.progOf i).length - η.idx := by omega
  have hlenC' : (C'.progOf i).length = (C₀.progOf i).length - η.idx - 1 := by omega
  have hCdrop : C.progOf i = (C₀.progOf i).drop η.idx := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC)
    rw [hlenC] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx) = η.idx by omega] at heq
  have hC'drop : C'.progOf i = (C₀.progOf i).drop (η.idx + 1) := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC')
    rw [hlenC'] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx - 1) = η.idx + 1
      by omega] at heq
  exact ⟨Nat.find hex, hτ, hk, Nat.find hex - 1, C, C', by omega, hC, hCC', hCdrop, hC'drop⟩

/-- Generalization of `exists_time_of_ends_done` with an arbitrary evidence
index: if at *some* position `j` of the trace, thread `i`'s remaining program
has already shrunk strictly below `|C₀.progOf i| - η.idx`, then instruction `η`
has executed (its drop transition lies before `j`). The `ends_done` version is
the special case `j = τ'.length - 1` with the empty final program. -/
theorem exists_time_of_progOf_lt (hdrop : StepDropsPrefix R) (hle1 : StepShrinksByOne R)
    {C₀ : Config State Cmd} {τ' : List (Config State Cmd)}
    (hτ : IsCompleteTraceFrom R C₀ τ')
    {η : ProgPoint} (hk : η.idx < (C₀.progOf η.thread).length)
    {j : Nat} {Cj : Config State Cmd} (hj : τ'[j]? = some Cj)
    (hshort : (Cj.progOf η.thread).length < (C₀.progOf η.thread).length - η.idx) :
    ∃ n, IsTimeOf R C₀ τ' η n := by
  have hchain : List.IsChain R τ' := hτ.1.subtrace
  set i := η.thread with hidef
  have h0 : τ'[0]? = some C₀ := by
    have hgen : ∀ l : List (Config State Cmd), l[0]? = l.head? := fun l => by cases l <;> rfl
    rw [hgen]; exact hτ.2
  have hsuffix : ∀ {j'} {C : Config State Cmd}, τ'[j']? = some C →
      C.progOf i <:+ C₀.progOf i :=
    fun {j' C} hCj => progOf_suffix_index_le hdrop hchain i h0 (Nat.zero_le j') hCj
  have hQj : ((τ'[j]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [hj]; exact hshort
  have hex : ∃ j', ((τ'[j']?).map (fun (C : Config State Cmd) => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := ⟨j, hQj⟩
  have hQj0 := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ j := Nat.find_le hQj
  have hjlt : j < τ'.length := (List.getElem?_eq_some_iff.mp hj).1
  have hQ0 : ¬ ((τ'[0]?).map (fun C => (C.progOf i).length)).getD 0
      < (C₀.progOf i).length - η.idx := by
    rw [h0]; change ¬ (C₀.progOf i).length < (C₀.progOf i).length - η.idx; omega
  have hj0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hQj0; exact absurd hQj0 hQ0
    · exact h
  have hminj := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have hj0lt : Nat.find hex < τ'.length := by omega
  obtain ⟨C, hC⟩ : ∃ C, τ'[Nat.find hex - 1]? = some C :=
    ⟨_, List.getElem?_eq_getElem (show Nat.find hex - 1 < τ'.length by omega)⟩
  obtain ⟨C', hC'⟩ : ∃ C', τ'[Nat.find hex]? = some C' :=
    ⟨_, List.getElem?_eq_getElem hj0lt⟩
  have hCC' : τ'[Nat.find hex - 1 + 1]? = some C' := by
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hC'
  have hub : (C.progOf i).length ≤ (C'.progOf i).length + 1 :=
    hle1 (chain_step hchain hC hCC') i
  have e1 : ((τ'[Nat.find hex - 1]?).map (fun C => (C.progOf i).length)).getD 0
      = (C.progOf i).length := by rw [hC]; rfl
  have e2 : ((τ'[Nat.find hex]?).map (fun C => (C.progOf i).length)).getD 0
      = (C'.progOf i).length := by rw [hC']; rfl
  rw [e1] at hminj
  rw [e2] at hQj0
  have hlenC : (C.progOf i).length = (C₀.progOf i).length - η.idx := by omega
  have hlenC' : (C'.progOf i).length = (C₀.progOf i).length - η.idx - 1 := by omega
  have hCdrop : C.progOf i = (C₀.progOf i).drop η.idx := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC)
    rw [hlenC] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx) = η.idx by omega] at heq
  have hC'drop : C'.progOf i = (C₀.progOf i).drop (η.idx + 1) := by
    have heq := List.IsSuffix.eq_drop (hsuffix hC')
    rw [hlenC'] at heq
    rwa [show (C₀.progOf i).length - ((C₀.progOf i).length - η.idx - 1) = η.idx + 1
      by omega] at heq
  exact ⟨Nat.find hex, hτ, hk, Nat.find hex - 1, C, C', by omega, hC, hCC', hCdrop, hC'drop⟩

end StepDiscipline

end WeftCommon
