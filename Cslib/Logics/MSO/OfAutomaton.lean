/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.Effective.Basic
public import Cslib.Logics.MSO.Basic

/-! # From automata to monadic second-order logic

This file constructs the sentences that express the acceptance of a word by an automaton, as in the
proofs of Theorem 3.1 and Theorem 5.9 of [Thomas1997]. The sentences existentially quantify over a
set `X_q` for each state `q`, containing the positions where the state `q` is assumed, and state
that these sets are pairwise disjoint and describe a successful run:

`∃X₀ … ∃X_k (⋀_{q ≠ r} ∀x ¬(X_q(x) ∧ X_r(x))`
`    ∧ ∀x (first(x) → ⋁_{s ∈ Q₀} X_s(x))`
`    ∧ ∀x ∀y (S(x, y) → ⋁_{(q, a, r) ∈ Δ} (X_q(x) ∧ Q_a(x) ∧ X_r(y)))`
`    ∧ acceptance)`

## Main definitions and results

- `Automata.EffectiveNA.toSentence`: the sentence for finite words, whose acceptance part is
  `∀x (last(x) → ⋁_{(q, a, r) ∈ Δ, r ∈ F} (X_q(x) ∧ Q_a(x)))`, with an additional clause for the
  empty word. It is correct by `holds_toSentence`.
- `Automata.EffectiveNA.toωSentence`: the sentence for ω-words, whose acceptance part is
  `∀x ∃y (x < y ∧ ⋁_{q ∈ F} X_q(y))`. It is correct by `holds_toωSentence`.

## Implementation notes

In contrast to the reference, an automaton can have several initial states.

The structure `IsRunCode` captures what the first three clauses say about the sets `X_q`. It
connects the formulas to runs given as functions from positions to states, and it is shared by
finite words and ω-words, which only differ in the acceptance clause.

The clause `buchiClause` uses the order relation, as this is needed for the kernel of the sentence
to be first-order. Applying `Formula.elimLt` removes it at the price of leaving EMSO.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open Automata Formula WordModel

universe u

variable {B : Type u}

/-- A description of a run by the sets of positions where each state is assumed: the sets are
pairwise disjoint and contain a run from an initial state. -/
structure IsRunCode (c : EffectiveNA B) (M : WordModel B) (U : c.State → Set ℕ) : Prop where
  /-- The sets are pairwise disjoint. -/
  disjoint : ∀ q r, q ≠ r → ∀ p ∈ M.dom, p ∈ U q → p ∉ U r
  /-- The first position carries an initial state. -/
  first : 0 ∈ M.dom → ∃ s ∈ c.toNA.start, 0 ∈ U s
  /-- Successive positions carry states that are connected by a transition. -/
  step : ∀ p, p + 1 ∈ M.dom → ∃ q a r, c.toNA.Tr q a r ∧ p ∈ U q ∧ M.label p = some a ∧ p + 1 ∈ U r

namespace IsRunCode

variable {c : EffectiveNA B} {M : WordModel B} {U : c.State → Set ℕ}

/-- The positions of the domain where a function `ρ` assumes a state. -/
def codeOf (M : WordModel B) (ρ : ℕ → c.State) (q : c.State) : Set ℕ := {p ∈ M.dom | ρ p = q}

/-- A function from positions to states that follows the transition relation is a run code. -/
theorem of_run {ρ : ℕ → c.State} (h₀ : 0 ∈ M.dom → ρ 0 ∈ c.toNA.start)
    (hρ : ∀ p, p + 1 ∈ M.dom → ∃ a, M.label p = some a ∧ c.toNA.Tr (ρ p) a (ρ (p + 1))) :
    IsRunCode c M (codeOf M ρ) where
  -- A position cannot be in the sets of two different states, as `ρ` is a function.
  disjoint q r hqr p _ hq hr := hqr (hq.2.symm.trans hr.2)
  -- The state `ρ 0` is initial and assumed at position `0`.
  first h := ⟨ρ 0, h₀ h, h, rfl⟩
  -- Consecutive positions:
  step p hp := by
    -- Take the letter `a` and the transition of `ρ` at `p`.
    obtain ⟨a, ha, htr⟩ := hρ p hp
    -- The sets of `ρ p` and `ρ (p + 1)` contain `p` and `p + 1`, which are in the domain.
    exact ⟨_, a, _, htr, ⟨M.mem_dom_of_le (Nat.le_succ p) hp, rfl⟩, ha, hp, rfl⟩

/-- Every position of the domain belongs to one of the sets of a run code. -/
theorem exists_mem (h : IsRunCode c M U) {p : ℕ} (hp : p ∈ M.dom) : ∃ q, p ∈ U q := by
  -- Distinguish the first position from later ones.
  cases p with
  -- Position `0`:
  | zero =>
    -- The first clause gives a state at position `0`.
    obtain ⟨s, -, hs⟩ := h.first hp
    -- This state is the witness.
    exact ⟨s, hs⟩
  -- Position `p + 1`:
  | succ p =>
    -- The step clause for `p` gives a state at position `p + 1`.
    obtain ⟨-, -, r, -, -, -, hr⟩ := h.step p hp
    -- This state is the witness.
    exact ⟨r, hr⟩

/-- A run code determines a run on the domain. -/
theorem exists_run [Nonempty c.State] (h : IsRunCode c M U) :
    ∃ ρ : ℕ → c.State, (∀ p ∈ M.dom, p ∈ U (ρ p)) ∧ (0 ∈ M.dom → ρ 0 ∈ c.toNA.start) ∧
      ∀ p, p + 1 ∈ M.dom → ∃ a, M.label p = some a ∧ c.toNA.Tr (ρ p) a (ρ (p + 1)) := by
  -- Use classical logic to choose states.
  classical
  -- Choose a state for each position; the choice is only relevant on the domain.
  have hmem : ∀ p, ∃ q, p ∈ M.dom → p ∈ U q := fun p ↦ by
    -- Distinguish whether the position is in the domain.
    by_cases hp : p ∈ M.dom
    -- In the domain, some set contains the position.
    · obtain ⟨q, hq⟩ := h.exists_mem hp
      -- The state of this set is the choice.
      exact ⟨q, fun _ ↦ hq⟩
    -- Outside of the domain, any state is fine.
    · exact ⟨Classical.arbitrary _, fun hp' ↦ absurd hp' hp⟩
  -- Collect the choices into a function `ρ`.
  choose ρ hρ using hmem
  -- By disjointness, the state of a position of the domain is unique.
  have huniq : ∀ {p q}, p ∈ M.dom → p ∈ U q → q = ρ p := fun {p q} hp hq ↦ by
    -- Suppose that `q` differs from the chosen state.
    by_contra hne
    -- Then the position is in two different sets: a contradiction.
    exact h.disjoint q (ρ p) hne p hp hq (hρ p hp)
  -- It remains to check the first state and the transitions.
  refine ⟨ρ, hρ, fun h₀ ↦ ?_, fun p hp ↦ ?_⟩
  -- The first clause gives an initial state at position `0`.
  · obtain ⟨s, hs, hs₀⟩ := h.first h₀
    -- By uniqueness, this state is `ρ 0`.
    rwa [← huniq h₀ hs₀]
  -- The step clause gives a transition between the positions `p` and `p + 1`.
  · obtain ⟨q, a, r, htr, hq, ha, hr⟩ := h.step p hp
    -- The position `p` is in the domain as well.
    have hp' := M.mem_dom_of_le (Nat.le_succ p) hp
    -- By uniqueness, the states of the transition are `ρ p` and `ρ (p + 1)`.
    rw [← huniq hp' hq, ← huniq hp hr]
    -- So this is the required transition of `ρ`.
    exact ⟨a, ha, htr⟩

end IsRunCode

section Formulas

variable [FinEnum B] (c : EffectiveNA B)

/-- The variable `X_q` for the positions where the state `q` is assumed. -/
def stateVar (q : c.State) : Fin (FinEnum.card c.State) := FinEnum.equiv q

/-- The list of all transitions of an automaton. -/
def transitions : List (c.State × B × c.State) :=
  (FinEnum.toList (c.State × B × c.State)).filter fun t ↦ c.toNA.Tr t.1 t.2.1 t.2.2

/-- A triple is in the list of transitions iff it is a transition of the automaton. -/
theorem mem_transitions {t : c.State × B × c.State} :
    t ∈ transitions c ↔ c.toNA.Tr t.1 t.2.1 t.2.2 := by
  -- All triples are enumerated, and the filter keeps the transitions.
  simp [transitions]

/-- `⋀_{q ≠ r} ∀x ¬(X_q(x) ∧ X_r(x))` -/
def disjointClause : Formula B 0 (FinEnum.card c.State) :=
  ⋀(((FinEnum.toList (c.State × c.State)).filter fun p ↦ p.1 ≠ p.2).map fun p ↦
    all₁ (¬((.mem (Fin.last 0) (stateVar c p.1)) ∧ (.mem (Fin.last 0) (stateVar c p.2)) :
      Formula B 1 (FinEnum.card c.State))))

/-- `∀x (first(x) → ⋁_{s ∈ Q₀} X_s(x))` -/
def startClause : Formula B 0 (FinEnum.card c.State) :=
  all₁ ((first (Fin.last 0)) →
    (⋁(((FinEnum.toList c.State).filter (· ∈ c.toNA.start)).map fun s ↦
      .mem (Fin.last 0) (stateVar c s)) : Formula B 1 (FinEnum.card c.State)))

/-- `∀x ∀y (S(x, y) → ⋁_{(q, a, r) ∈ Δ} (X_q(x) ∧ Q_a(x) ∧ X_r(y)))` -/
def stepClause : Formula B 0 (FinEnum.card c.State) :=
  all₁ (all₁ ((.succ (Fin.last 0).castSucc (Fin.last 1)) →
    (⋁((transitions c).map fun t ↦
      (.mem (Fin.last 0).castSucc (stateVar c t.1)) ∧
        ((.label t.2.1 (Fin.last 0).castSucc) ∧ (.mem (Fin.last 1) (stateVar c t.2.2)))) :
      Formula B 2 (FinEnum.card c.State))))

/-- `∀x (last(x) → ⋁_{(q, a, r) ∈ Δ, r ∈ F} (X_q(x) ∧ Q_a(x)))` -/
def lastClause : Formula B 0 (FinEnum.card c.State) :=
  all₁ ((last (Fin.last 0)) →
    (⋁(((transitions c).filter (·.2.2 ∈ c.accept)).map fun t ↦
      (.mem (Fin.last 0) (stateVar c t.1)) ∧ (.label t.2.1 (Fin.last 0))) :
      Formula B 1 (FinEnum.card c.State)))

/-- The clause for the empty word: `∃x x = x`, unless the automaton accepts the empty word. -/
def emptyClause : Formula B 0 (FinEnum.card c.State) :=
  if ∃ s, s ∈ c.toNA.start ∧ s ∈ c.accept then ⊤ else .ex₁ (.eq (Fin.last 0) (Fin.last 0))

/-- `∀x ∃y (x < y ∧ ⋁_{q ∈ F} X_q(y))` -/
def buchiClause : Formula B 0 (FinEnum.card c.State) :=
  all₁ (.ex₁ ((.lt (Fin.last 0).castSucc (Fin.last 1)) ∧
    (⋁(((FinEnum.toList c.State).filter (· ∈ c.accept)).map fun q ↦
      .mem (Fin.last 1) (stateVar c q)) : Formula B 2 (FinEnum.card c.State))))

section Semantics

variable {c} {M : WordModel B} {v : Fin 0 → ℕ} {Y : Fin (FinEnum.card c.State) → Set ℕ}

omit [FinEnum B] in
/-- The semantics of the clause that the sets are pairwise disjoint. -/
theorem satisfies_disjointClause :
    Satisfies M v Y (disjointClause c) ↔
      ∀ q r, q ≠ r → ∀ p ∈ M.dom, p ∈ Y (stateVar c q) → p ∉ Y (stateVar c r) := by
  -- Evaluate the conjunction over all pairs of different states.
  simp only [disjointClause, satisfies_finiteAnd, List.forall_mem_map, List.mem_filter,
    -- Evaluate the membership in the filtered list and the connectives.
    FinEnum.mem_toList, true_and, decide_eq_true_eq, satisfies_all₁, satisfies_not, satisfies_and,
    -- Evaluate the variables and split the pairs of states.
    Satisfies, Fin.snoc_last, not_and, Prod.forall, ne_eq]

omit [FinEnum B] in
/-- The semantics of the clause that the first position carries an initial state. -/
theorem satisfies_startClause :
    Satisfies M v Y (startClause c) ↔
      0 ∈ M.dom → ∃ s ∈ c.toNA.start, 0 ∈ Y (stateVar c s) := by
  -- Evaluate the implication and the disjunction over the initial states.
  simp only [startClause, satisfies_all₁, satisfies_imp, satisfies_finiteOr, List.mem_map,
    -- Evaluate the membership in the filtered list.
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq, exists_exists_and_eq_and,
    -- Evaluate the variables.
    Satisfies, Fin.snoc_last]
  -- Show both directions.
  constructor
  -- Assume the clause, and that position `0` is in the domain.
  · intro h h₀
    -- Apply the clause to position `0`, which is the first position.
    refine h 0 h₀ ((satisfies_first ?_).mpr ?_) <;> simp only [Fin.snoc_last, h₀]
  -- Conversely, let `p` be a first position.
  · intro h p hp hfirst
    -- The position `p` is `0`.
    have hp₀ : p = 0 := by
      -- The value of the new variable is `p`.
      simpa only [Fin.snoc_last] using
        -- A position of the domain is first iff it is `0`.
        (satisfies_first (by simpa only [Fin.snoc_last] using hp)).mp hfirst
    -- So `p` is `0`.
    obtain rfl := hp₀
    -- The assumption gives an initial state at position `0`.
    exact h hp

/-- The semantics of the clause that successive positions are connected by transitions. -/
theorem satisfies_stepClause :
    Satisfies M v Y (stepClause c) ↔
      ∀ p, p + 1 ∈ M.dom → ∃ q a r, c.toNA.Tr q a r ∧ p ∈ Y (stateVar c q) ∧
        M.label p = some a ∧ p + 1 ∈ Y (stateVar c r) := by
  -- Evaluate the implication and the disjunction over the transitions.
  simp only [stepClause, satisfies_all₁, satisfies_imp, satisfies_finiteOr, List.mem_map,
    -- Evaluate the connectives and the variables.
    satisfies_and, Satisfies, Fin.snoc_castSucc, Fin.snoc_last, exists_exists_and_eq_and,
    -- Use the description of the list of transitions.
    mem_transitions]
  -- Show both directions.
  constructor
  -- Assume the clause, and that `p + 1` is in the domain.
  · intro h p hp
    -- Apply the clause to the positions `p` and `p + 1`.
    obtain ⟨⟨q, a, r⟩, htr, h⟩ := h p (M.mem_dom_of_le (Nat.le_succ p) hp) (p + 1) hp rfl
    -- The transition from the list has the required components.
    exact ⟨q, a, r, htr, h⟩
  -- Conversely, take the positions `p` and `p + 1` of the domain.
  · rintro h p - _ hp rfl
    -- The assumption gives a transition.
    obtain ⟨q, a, r, htr, h⟩ := h p hp
    -- This transition is in the list of transitions.
    exact ⟨⟨q, a, r⟩, htr, h⟩

/-- The semantics of the clause that the last position has a transition into an accepting state. -/
theorem satisfies_lastClause :
    Satisfies M v Y (lastClause c) ↔
      ∀ p ∈ M.dom, p + 1 ∉ M.dom → ∃ q a r, c.toNA.Tr q a r ∧ r ∈ c.accept ∧
        p ∈ Y (stateVar c q) ∧ M.label p = some a := by
  -- Evaluate the implication and the disjunction over the transitions into accepting states.
  simp only [lastClause, satisfies_all₁, satisfies_imp, satisfies_last, satisfies_finiteOr,
    -- Use the description of the filtered list of transitions and the connectives.
    List.mem_map, List.mem_filter, mem_transitions, decide_eq_true_eq, satisfies_and, Satisfies,
    -- Evaluate the variables.
    Fin.snoc_last, exists_exists_and_eq_and]
  -- Show both directions.
  constructor
  -- Assume the clause, and let `p` be the last position.
  · intro h p hp hp'
    -- The clause gives a transition into an accepting state.
    obtain ⟨⟨q, a, r⟩, ⟨htr, hr⟩, h⟩ := h p hp hp'
    -- It has the required components.
    exact ⟨q, a, r, htr, hr, h⟩
  -- Conversely, let `p` be the last position.
  · intro h p hp hp'
    -- The assumption gives a transition into an accepting state.
    obtain ⟨q, a, r, htr, hr, h⟩ := h p hp hp'
    -- This transition is in the filtered list of transitions.
    exact ⟨⟨q, a, r⟩, ⟨htr, hr⟩, h⟩

omit [FinEnum B] in
/-- The semantics of the clause for the empty word. -/
theorem satisfies_emptyClause :
    Satisfies M v Y (emptyClause c) ↔
      (∃ s, s ∈ c.toNA.start ∧ s ∈ c.accept) ∨ M.dom.Nonempty := by
  -- Unfold the clause.
  unfold emptyClause
  -- Distinguish whether the automaton accepts the empty word.
  split_ifs with h
  -- If it does, the clause is `⊤`.
  · simp only [satisfies_top, h, true_or]
  -- Otherwise, the clause states that there is a position.
  · simp only [Satisfies, h, false_or, Set.Nonempty, and_true]

omit [FinEnum B] in
/-- The semantics of the clause that accepting states are visited infinitely often. -/
theorem satisfies_buchiClause :
    Satisfies M v Y (buchiClause c) ↔
      ∀ p ∈ M.dom, ∃ p' ∈ M.dom, p < p' ∧ ∃ q ∈ c.accept, p' ∈ Y (stateVar c q) := by
  -- Evaluate the quantifiers, the order relation and the disjunction over accepting states.
  simp only [buchiClause, satisfies_all₁, Satisfies, satisfies_and, satisfies_finiteOr,
    -- Evaluate the membership in the filtered list.
    List.mem_map, List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq,
    -- Evaluate the variables.
    exists_exists_and_eq_and, Fin.snoc_castSucc, Fin.snoc_last]

/-- The first three clauses of the sentences express that the sets form a run code. -/
theorem isRunCode_iff :
    IsRunCode c M (fun q ↦ Y (stateVar c q)) ↔
      Satisfies M v Y (disjointClause c) ∧ Satisfies M v Y (startClause c) ∧
        Satisfies M v Y (stepClause c) := by
  -- Apply the semantics of the three clauses.
  rw [satisfies_disjointClause, satisfies_startClause, satisfies_stepClause]
  -- This is the definition of a run code.
  exact ⟨fun h ↦ ⟨h.disjoint, h.first, h.step⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

end Semantics

section Fragments

omit [FinEnum B] in
/-- The clause `disjointClause` is first-order. -/
theorem isFirstOrder_disjointClause : (disjointClause c).IsFirstOrder := by
  -- Each conjunct has to be first-order.
  refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
  -- It has the form `∀x ¬(X_q(x) ∧ X_r(x))`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- Its atomic formulas are first-order.
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
/-- The clause `startClause` is first-order. -/
theorem isFirstOrder_startClause : (startClause c).IsFirstOrder := by
  -- The implication consists of `first(x)` and a disjunction.
  refine isFirstOrder_imp.mpr ⟨isFirstOrder_first _, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_s(x)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- This formula is atomic.
  trivial

/-- The clause `stepClause` is first-order. -/
theorem isFirstOrder_stepClause : (stepClause c).IsFirstOrder := by
  -- The implication consists of `S(x, y)` and a disjunction.
  refine isFirstOrder_imp.mpr ⟨trivial, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_q(x) ∧ Q_a(x) ∧ X_r(y)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- Its atomic formulas are first-order.
  exact ⟨trivial, trivial, trivial⟩

/-- The clause `lastClause` is first-order. -/
theorem isFirstOrder_lastClause : (lastClause c).IsFirstOrder := by
  -- The implication consists of `last(x)` and a disjunction.
  refine isFirstOrder_imp.mpr ⟨isFirstOrder_last _, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_q(x) ∧ Q_a(x)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- Its atomic formulas are first-order.
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
/-- The clause `emptyClause` is first-order. -/
theorem isFirstOrder_emptyClause : (emptyClause c).IsFirstOrder := by
  -- Unfold the clause.
  unfold emptyClause
  -- Distinguish whether the automaton accepts the empty word.
  split_ifs
  -- If it does, the clause is `⊤`.
  · exact isFirstOrder_top
  -- Otherwise, the clause is `∃x x = x`.
  · trivial

omit [FinEnum B] in
/-- The clause `buchiClause` is first-order. -/
theorem isFirstOrder_buchiClause : (buchiClause c).IsFirstOrder := by
  -- The conjunction consists of `x < y` and a disjunction.
  refine isFirstOrder_and.mpr ⟨trivial, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_q(y)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- This formula is atomic.
  trivial

omit [FinEnum B] in
/-- The clause `disjointClause` does not use the order relation. -/
theorem ltFree_disjointClause : (disjointClause c).LtFree := by
  -- Each conjunct has to be in MSO[S].
  refine ltFree_finiteAnd fun φ hφ ↦ ?_
  -- It has the form `∀x ¬(X_q(x) ∧ X_r(x))`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- It does not use the order relation.
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
/-- The clause `startClause` does not use the order relation. -/
theorem ltFree_startClause : (startClause c).LtFree := by
  -- The implication consists of `first(x)` and a disjunction.
  refine ltFree_imp.mpr ⟨ltFree_first _, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_s(x)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- This formula does not use the order relation.
  trivial

/-- The clause `stepClause` does not use the order relation. -/
theorem ltFree_stepClause : (stepClause c).LtFree := by
  -- The implication consists of `S(x, y)` and a disjunction.
  refine ltFree_imp.mpr ⟨trivial, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_q(x) ∧ Q_a(x) ∧ X_r(y)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- It does not use the order relation.
  exact ⟨trivial, trivial, trivial⟩

/-- The clause `lastClause` does not use the order relation. -/
theorem ltFree_lastClause : (lastClause c).LtFree := by
  -- The implication consists of `last(x)` and a disjunction.
  refine ltFree_imp.mpr ⟨ltFree_last _, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  -- A disjunct has the form `X_q(x) ∧ Q_a(x)`.
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  -- It does not use the order relation.
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
/-- The clause `emptyClause` does not use the order relation. -/
theorem ltFree_emptyClause : (emptyClause c).LtFree := by
  -- Unfold the clause.
  unfold emptyClause
  -- Distinguish whether the automaton accepts the empty word.
  split_ifs
  -- If it does, the clause is `⊤`.
  · exact ltFree_top
  -- Otherwise, the clause is `∃x x = x`.
  · trivial

end Fragments

end Formulas

end Cslib.Logic.MSO

namespace Cslib.Automata.EffectiveNA

open Logic Logic.MSO Logic.MSO.Formula WordModel
open scoped Logic

universe u

variable {B : Type u} [FinEnum B] (c : EffectiveNA B)

/-- The sentence expressing that an automaton accepts a finite word. -/
def toSentence : Sentence B :=
  exAll₂ _ ((disjointClause c ∧ startClause c ∧ stepClause c ∧ lastClause c ∧ emptyClause c :
    Formula B 0 (FinEnum.card c.State)))

/-- The sentence expressing that an automaton accepts an ω-word as a Büchi automaton. -/
def toωSentence : Sentence B :=
  exAll₂ _ ((disjointClause c ∧ startClause c ∧ stepClause c ∧ buchiClause c :
    Formula B 0 (FinEnum.card c.State)))

/-- The sentence `toSentence` is first-order after its second-order prefix. -/
theorem isEMSO_toSentence : (toSentence c).IsEMSO :=
  -- The prefix comes from `exAll₂`, and `disjointClause` is first-order.
  isEMSO_exAll₂ <| .firstOrder <| isFirstOrder_and.mpr ⟨isFirstOrder_disjointClause c,
    -- `startClause` is first-order.
    isFirstOrder_and.mpr ⟨isFirstOrder_startClause c, isFirstOrder_and.mpr
      -- `stepClause` is first-order.
      ⟨isFirstOrder_stepClause c, isFirstOrder_and.mpr
        -- `lastClause` and `emptyClause` are first-order.
        ⟨isFirstOrder_lastClause c, isFirstOrder_emptyClause c⟩⟩⟩⟩

/-- The sentence `toSentence` is a sentence of MSO[S]. -/
theorem ltFree_toSentence : (toSentence c).LtFree :=
  -- The prefix does not matter, and `disjointClause` does not use the order relation.
  ltFree_exAll₂.mpr <| ltFree_and.mpr ⟨ltFree_disjointClause c,
    -- Neither does `startClause`.
    ltFree_and.mpr ⟨ltFree_startClause c, ltFree_and.mpr
      -- Nor do `stepClause`, `lastClause` and `emptyClause`.
      ⟨ltFree_stepClause c, ltFree_and.mpr ⟨ltFree_lastClause c, ltFree_emptyClause c⟩⟩⟩⟩

/-- The sentence `toωSentence` is first-order after its second-order prefix. -/
theorem isEMSO_toωSentence : (toωSentence c).IsEMSO :=
  -- The prefix comes from `exAll₂`, and `disjointClause` is first-order.
  isEMSO_exAll₂ <| .firstOrder <| isFirstOrder_and.mpr ⟨isFirstOrder_disjointClause c,
    -- `startClause` is first-order.
    isFirstOrder_and.mpr ⟨isFirstOrder_startClause c, isFirstOrder_and.mpr
      -- `stepClause` and `buchiClause` are first-order.
      ⟨isFirstOrder_stepClause c, isFirstOrder_buchiClause c⟩⟩⟩

omit [FinEnum B] in
/-- Interpret the variables of the sentences by the positions where a function assumes a state. -/
private theorem exists_vars (M : WordModel B) (ρ : ℕ → c.State) :
    ∃ Y : Fin (FinEnum.card c.State) → Set ℕ,
      (∀ j, Y j ⊆ M.dom) ∧ ∀ q, Y (stateVar c q) = IsRunCode.codeOf M ρ q :=
  -- Let `Y j` be the positions of the state with number `j`, which are in the domain.
  ⟨fun j ↦ IsRunCode.codeOf M ρ (FinEnum.equiv.symm j), fun _ _ hp ↦ hp.1,
    -- The number of a state `q` leads back to `q`.
    fun q ↦ by simp [stateVar]⟩

variable {c}

/-- The sentence `toSentence` expresses the acceptance of a finite word by the automaton (first part
of the proof of Theorem 3.1 of [Thomas1997]). -/
theorem holds_toSentence {w : List B} : (toSentence c).Holds (ofList w) ↔ w ∈ c.language := by
  -- Unfold: there are sets `Y` that satisfy the clauses, and `w` has an accepting run.
  rw [Sentence.Holds, toSentence, satisfies_exAll₂, mem_language_iff]
  -- Show both directions.
  constructor
  -- Take sets `Y` that satisfy all clauses.
  · rintro ⟨Y, -, h⟩
    -- Split the conjunction.
    simp only [satisfies_and] at h
    -- Name the five clauses.
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    -- The sets `Y` form a run code.
    have hrun : IsRunCode c (ofList w) (fun q ↦ Y (stateVar c q)) :=
      -- This is what the first three clauses state.
      isRunCode_iff.mpr ⟨h₁, h₂, h₃⟩
    -- Distinguish the empty word.
    by_cases hw : w = []
    -- The empty word:
    · subst hw
      -- By the clause for the empty word, a state is initial and accepting, or there is a position.
      obtain ⟨s, hs, ha⟩ | ⟨p, hp⟩ := satisfies_emptyClause.mp h₅
      -- The constant function on `s` is an accepting run without transitions.
      · exact ⟨fun _ ↦ s, hs, ha, fun i h ↦ absurd h (Nat.not_lt_zero i)⟩
      -- The empty word has no positions.
      · exact absurd (mem_dom_ofList.mp hp) (Nat.not_lt_zero p)
    -- A nonempty word has positive length.
    · have hlen : 0 < w.length := List.length_pos_iff.mpr hw
      -- So position `0` belongs to the domain.
      have h0 : 0 ∈ (ofList w).dom := mem_dom_ofList.mpr hlen
      -- There is an initial state at position `0`.
      obtain ⟨s₀, -, -⟩ := hrun.first h0
      -- So there are states at all.
      have : Nonempty c.State := ⟨s₀⟩
      -- The run code gives a run `ρ` on the domain.
      obtain ⟨ρ, hρ, hstart, hstep⟩ := hrun.exists_run
      -- The last position belongs to the domain.
      have hlast : w.length - 1 ∈ (ofList w).dom := mem_dom_ofList.mpr (by omega)
      -- The clause for the last position gives the last transition, into an accepting state `r`.
      obtain ⟨q, a, r, htr, hr, hq, ha⟩ :=
        -- The position after the last one is not in the domain.
        satisfies_lastClause.mp h₄ _ hlast (by simp only [mem_dom_ofList]; omega)
      -- The state `q` of the last position is the state of the run.
      have hqρ : q = ρ (w.length - 1) := by
        -- Suppose that they differ.
        by_contra hne
        -- Then the last position is in two different sets: a contradiction.
        exact hrun.disjoint q _ hne _ hlast hq (hρ _ hlast)
      -- Follow `ρ` on the positions of the word, and end in the accepting state `r`.
      refine ⟨fun i ↦ if i < w.length then ρ i else r, ?_, ?_, fun i hi ↦ ?_⟩
      -- The first state is `ρ 0`, which is initial.
      · simpa only [hlen, ↓reduceIte] using hstart h0
      -- The last state is `r`, which is accepting.
      · simpa only [lt_self_iff_false, ↓reduceIte] using hr
      -- Distinguish the last transition from the others.
      · by_cases hi' : i + 1 < w.length
        -- Not the last one: take the transition of the run `ρ`.
        · obtain ⟨a', ha', htr'⟩ := hstep i (mem_dom_ofList.mpr hi')
          -- The letter of this transition is the letter of the word.
          simp only [ofList_label, List.getElem?_eq_getElem hi, Option.some.injEq] at ha'
          -- So this is the required transition.
          simpa only [hi, hi', ↓reduceIte, ha'] using htr'
        -- The last one: the position is the last position.
        · obtain rfl : i = w.length - 1 := by omega
          -- The letter of the transition is the letter of the word.
          simp only [ofList_label, List.getElem?_eq_getElem hi, Option.some.injEq] at ha
          -- So this is the transition from the clause for the last position.
          simpa only [hi, hi', ↓reduceIte, ha, ← hqρ] using htr
  -- Conversely, take an accepting run `ρ` on `w`.
  · rintro ⟨ρ, hs, ha, hρ⟩
    -- Interpret the variables by the positions where `ρ` assumes a state.
    obtain ⟨Y, hYdom, hY⟩ := exists_vars (c := c) (ofList w) ρ
    -- These sets form a run code.
    have hrun : IsRunCode c (ofList w) (fun q ↦ Y (stateVar c q)) := by
      -- The sets are the ones of `ρ`.
      simp only [hY]
      -- The first state of `ρ` is initial; it remains to check the transitions.
      refine IsRunCode.of_run (fun _ ↦ hs) fun p hp ↦ ?_
      -- The position `p` has a successor in the word.
      have hp' : p + 1 < w.length := mem_dom_ofList.mp hp
      -- The transition of `ρ` at `p` reads the letter of the word.
      exact ⟨w[p], List.getElem?_eq_getElem _, hρ p _⟩
    -- So the first three clauses hold.
    obtain ⟨h₁, h₂, h₃⟩ := isRunCode_iff.mp hrun
    -- Use these sets.
    refine ⟨Y, hYdom, ?_⟩
    -- Split the conjunction.
    simp only [satisfies_and]
    -- It remains to show the last two clauses.
    refine ⟨h₁, h₂, h₃, satisfies_lastClause.mpr ?_, satisfies_emptyClause.mpr ?_⟩
    -- The clause for the last position: let `p` be the last position.
    · intro p hp hp'
      -- It is below the length of the word.
      have hlt : p < w.length := mem_dom_ofList.mp hp
      -- As `p + 1` is not in the domain, `p` is the position before the end.
      have hlen : p + 1 = w.length := by
        -- Suppose that it is not.
        by_contra hne
        -- Then `p + 1` is in the domain: a contradiction.
        exact hp' (mem_dom_ofList.mpr (by omega))
      -- The last transition of `ρ` leads to the state `ρ (p + 1)`, which is accepting.
      refine ⟨ρ p, w[p], ρ (p + 1), hρ p hlt, hlen ▸ ha, ?_, List.getElem?_eq_getElem _⟩
      -- It remains that `p` is in the set of `ρ p`.
      rw [hY]
      -- This holds by definition of the set.
      exact ⟨hp, rfl⟩
    -- The clause for the empty word: distinguish the empty word.
    · by_cases hw : w = []
      -- The empty word:
      · subst hw
        -- The first state of the run is both initial and accepting.
        exact Or.inl ⟨ρ 0, hs, ha⟩
      -- A nonempty word has the position `0`.
      · exact Or.inr ⟨0, mem_dom_ofList.mpr (List.length_pos_iff.mpr hw)⟩

/-- The sentence `toωSentence` expresses the acceptance of an ω-word by the automaton as a Büchi
automaton (first part of the proof of Theorem 5.9 of [Thomas1997]). -/
theorem holds_toωSentence {α : ωSequence B} :
    (toωSentence c).Holds (ofOmega α) ↔ α ∈ c.ωlanguage := by
  -- Unfold: there are sets `Y` that satisfy the clauses, and `α` has an accepting run.
  rw [Sentence.Holds, toωSentence, satisfies_exAll₂, mem_ωlanguage_iff]
  -- Show both directions.
  constructor
  -- Take sets `Y` that satisfy all clauses.
  · rintro ⟨Y, -, h⟩
    -- Split the conjunction.
    simp only [satisfies_and] at h
    -- Name the four clauses.
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    -- The sets `Y` form a run code.
    have hrun : IsRunCode c (ofOmega α) (fun q ↦ Y (stateVar c q)) :=
      -- This is what the first three clauses state.
      isRunCode_iff.mpr ⟨h₁, h₂, h₃⟩
    -- There is an initial state at position `0`.
    obtain ⟨s₀, -, -⟩ := hrun.first mem_dom_ofOmega
    -- So there are states at all.
    have : Nonempty c.State := ⟨s₀⟩
    -- The run code gives a run `ρ`.
    obtain ⟨ρ, hρ, hstart, hstep⟩ := hrun.exists_run
    -- It remains to check the first state, the transitions and the acceptance.
    refine ⟨ρ, hstart mem_dom_ofOmega, fun i ↦ ?_, ?_⟩
    -- The transition of `ρ` at `i` reads a letter `a`.
    · obtain ⟨a, ha, htr⟩ := hstep i mem_dom_ofOmega
      -- This letter is the letter of the ω-word.
      obtain rfl := Option.some.inj ha
      -- So this is the required transition.
      exact htr
    -- Infinitely often means after each position.
    · rw [Filter.frequently_atTop']
      -- Let `p` be a position.
      intro p
      -- The Büchi clause gives a later position `p'` in the set of an accepting state `q`.
      obtain ⟨p', hp', hlt, q, hq, hqp⟩ := satisfies_buchiClause.mp h₄ p mem_dom_ofOmega
      -- The state `q` is the state of the run at `p'`.
      have hqρ : q = ρ p' := by
        -- Suppose that they differ.
        by_contra hne
        -- Then `p'` is in two different sets: a contradiction.
        exact hrun.disjoint q _ hne _ hp' hqp (hρ _ hp')
      -- So the run visits an accepting state at `p'`.
      exact ⟨p', hlt, hqρ ▸ hq⟩
  -- Conversely, take an accepting run `ρ` on `α`.
  · rintro ⟨ρ, hs, htr, hacc⟩
    -- Interpret the variables by the positions where `ρ` assumes a state.
    obtain ⟨Y, hYdom, hY⟩ := exists_vars (c := c) (ofOmega α) ρ
    -- These sets form a run code.
    have hrun : IsRunCode c (ofOmega α) (fun q ↦ Y (stateVar c q)) := by
      -- The sets are the ones of `ρ`.
      simp only [hY]
      -- The first state is initial, and each transition reads the letter of the ω-word.
      exact IsRunCode.of_run (fun _ ↦ hs) fun p _ ↦ ⟨α p, rfl, htr p⟩
    -- So the first three clauses hold.
    obtain ⟨h₁, h₂, h₃⟩ := isRunCode_iff.mp hrun
    -- Use these sets.
    refine ⟨Y, hYdom, ?_⟩
    -- Split the conjunction.
    simp only [satisfies_and]
    -- It remains to show the Büchi clause for a position `p`.
    refine ⟨h₁, h₂, h₃, satisfies_buchiClause.mpr fun p _ ↦ ?_⟩
    -- The run visits an accepting state at a later position `p'`.
    obtain ⟨p', hlt, hp'⟩ := Filter.frequently_atTop'.mp hacc p
    -- This position and its state witness the clause.
    refine ⟨p', mem_dom_ofOmega, hlt, ρ p', hp', ?_⟩
    -- It remains that `p'` is in the set of `ρ p'`.
    rw [hY]
    -- This holds by definition of the set.
    exact ⟨mem_dom_ofOmega, rfl⟩

end Cslib.Automata.EffectiveNA
