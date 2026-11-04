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
  disjoint q r hqr p _ hq hr := hqr (hq.2.symm.trans hr.2)
  first h := ⟨ρ 0, h₀ h, h, rfl⟩
  step p hp := by
    obtain ⟨a, ha, htr⟩ := hρ p hp
    exact ⟨_, a, _, htr, ⟨M.mem_dom_of_le (Nat.le_succ p) hp, rfl⟩, ha, hp, rfl⟩

/-- Every position of the domain belongs to one of the sets of a run code. -/
theorem exists_mem (h : IsRunCode c M U) {p : ℕ} (hp : p ∈ M.dom) : ∃ q, p ∈ U q := by
  cases p with
  | zero =>
    obtain ⟨s, -, hs⟩ := h.first hp
    exact ⟨s, hs⟩
  | succ p =>
    obtain ⟨-, -, r, -, -, -, hr⟩ := h.step p hp
    exact ⟨r, hr⟩

/-- A run code determines a run on the domain. -/
theorem exists_run [Nonempty c.State] (h : IsRunCode c M U) :
    ∃ ρ : ℕ → c.State, (∀ p ∈ M.dom, p ∈ U (ρ p)) ∧ (0 ∈ M.dom → ρ 0 ∈ c.toNA.start) ∧
      ∀ p, p + 1 ∈ M.dom → ∃ a, M.label p = some a ∧ c.toNA.Tr (ρ p) a (ρ (p + 1)) := by
  classical
  have hmem : ∀ p, ∃ q, p ∈ M.dom → p ∈ U q := fun p ↦ by
    by_cases hp : p ∈ M.dom
    · obtain ⟨q, hq⟩ := h.exists_mem hp
      exact ⟨q, fun _ ↦ hq⟩
    · exact ⟨Classical.arbitrary _, fun hp' ↦ absurd hp' hp⟩
  choose ρ hρ using hmem
  have huniq : ∀ {p q}, p ∈ M.dom → p ∈ U q → q = ρ p := fun {p q} hp hq ↦ by
    by_contra hne
    exact h.disjoint q (ρ p) hne p hp hq (hρ p hp)
  refine ⟨ρ, hρ, fun h₀ ↦ ?_, fun p hp ↦ ?_⟩
  · obtain ⟨s, hs, hs₀⟩ := h.first h₀
    rwa [← huniq h₀ hs₀]
  · obtain ⟨q, a, r, htr, hq, ha, hr⟩ := h.step p hp
    have hp' := M.mem_dom_of_le (Nat.le_succ p) hp
    rw [← huniq hp' hq, ← huniq hp hr]
    exact ⟨a, ha, htr⟩

end IsRunCode

section Formulas

variable [FinEnum B] (c : EffectiveNA B)

/-- The variable `X_q` for the positions where the state `q` is assumed. -/
def stateVar (q : c.State) : Fin (FinEnum.card c.State) := FinEnum.equiv q

/-- The list of all transitions of an automaton. -/
def transitions : List (c.State × B × c.State) :=
  (FinEnum.toList (c.State × B × c.State)).filter fun t ↦ c.toNA.Tr t.1 t.2.1 t.2.2

theorem mem_transitions {t : c.State × B × c.State} :
    t ∈ transitions c ↔ c.toNA.Tr t.1 t.2.1 t.2.2 := by
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
theorem satisfies_disjointClause :
    Satisfies M v Y (disjointClause c) ↔
      ∀ q r, q ≠ r → ∀ p ∈ M.dom, p ∈ Y (stateVar c q) → p ∉ Y (stateVar c r) := by
  simp only [disjointClause, satisfies_finiteAnd, List.forall_mem_map, List.mem_filter,
    FinEnum.mem_toList, true_and, decide_eq_true_eq, satisfies_all₁, satisfies_not, satisfies_and,
    Satisfies, Fin.snoc_last, not_and, Prod.forall, ne_eq]

omit [FinEnum B] in
theorem satisfies_startClause :
    Satisfies M v Y (startClause c) ↔
      0 ∈ M.dom → ∃ s ∈ c.toNA.start, 0 ∈ Y (stateVar c s) := by
  simp only [startClause, satisfies_all₁, satisfies_imp, satisfies_finiteOr, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq, exists_exists_and_eq_and,
    Satisfies, Fin.snoc_last]
  constructor
  · intro h h₀
    refine h 0 h₀ ((satisfies_first ?_).mpr ?_) <;> simp only [Fin.snoc_last, h₀]
  · intro h p hp hfirst
    have hp₀ : p = 0 := by
      simpa only [Fin.snoc_last] using
        (satisfies_first (by simpa only [Fin.snoc_last] using hp)).mp hfirst
    obtain rfl := hp₀
    exact h hp

theorem satisfies_stepClause :
    Satisfies M v Y (stepClause c) ↔
      ∀ p, p + 1 ∈ M.dom → ∃ q a r, c.toNA.Tr q a r ∧ p ∈ Y (stateVar c q) ∧
        M.label p = some a ∧ p + 1 ∈ Y (stateVar c r) := by
  simp only [stepClause, satisfies_all₁, satisfies_imp, satisfies_finiteOr, List.mem_map,
    satisfies_and, Satisfies, Fin.snoc_castSucc, Fin.snoc_last, exists_exists_and_eq_and,
    mem_transitions]
  constructor
  · intro h p hp
    obtain ⟨⟨q, a, r⟩, htr, h⟩ := h p (M.mem_dom_of_le (Nat.le_succ p) hp) (p + 1) hp rfl
    exact ⟨q, a, r, htr, h⟩
  · rintro h p - _ hp rfl
    obtain ⟨q, a, r, htr, h⟩ := h p hp
    exact ⟨⟨q, a, r⟩, htr, h⟩

theorem satisfies_lastClause :
    Satisfies M v Y (lastClause c) ↔
      ∀ p ∈ M.dom, p + 1 ∉ M.dom → ∃ q a r, c.toNA.Tr q a r ∧ r ∈ c.accept ∧
        p ∈ Y (stateVar c q) ∧ M.label p = some a := by
  simp only [lastClause, satisfies_all₁, satisfies_imp, satisfies_last, satisfies_finiteOr,
    List.mem_map, List.mem_filter, mem_transitions, decide_eq_true_eq, satisfies_and, Satisfies,
    Fin.snoc_last, exists_exists_and_eq_and]
  constructor
  · intro h p hp hp'
    obtain ⟨⟨q, a, r⟩, ⟨htr, hr⟩, h⟩ := h p hp hp'
    exact ⟨q, a, r, htr, hr, h⟩
  · intro h p hp hp'
    obtain ⟨q, a, r, htr, hr, h⟩ := h p hp hp'
    exact ⟨⟨q, a, r⟩, ⟨htr, hr⟩, h⟩

omit [FinEnum B] in
theorem satisfies_emptyClause :
    Satisfies M v Y (emptyClause c) ↔
      (∃ s, s ∈ c.toNA.start ∧ s ∈ c.accept) ∨ M.dom.Nonempty := by
  unfold emptyClause
  split_ifs with h
  · simp only [satisfies_top, h, true_or]
  · simp only [Satisfies, h, false_or, Set.Nonempty, and_true]

omit [FinEnum B] in
theorem satisfies_buchiClause :
    Satisfies M v Y (buchiClause c) ↔
      ∀ p ∈ M.dom, ∃ p' ∈ M.dom, p < p' ∧ ∃ q ∈ c.accept, p' ∈ Y (stateVar c q) := by
  simp only [buchiClause, satisfies_all₁, Satisfies, satisfies_and, satisfies_finiteOr,
    List.mem_map, List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq,
    exists_exists_and_eq_and, Fin.snoc_castSucc, Fin.snoc_last]

/-- The first three clauses of the sentences express that the sets form a run code. -/
theorem isRunCode_iff :
    IsRunCode c M (fun q ↦ Y (stateVar c q)) ↔
      Satisfies M v Y (disjointClause c) ∧ Satisfies M v Y (startClause c) ∧
        Satisfies M v Y (stepClause c) := by
  rw [satisfies_disjointClause, satisfies_startClause, satisfies_stepClause]
  exact ⟨fun h ↦ ⟨h.disjoint, h.first, h.step⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

end Semantics

section Fragments

omit [FinEnum B] in
theorem isFirstOrder_disjointClause : (disjointClause c).IsFirstOrder := by
  refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
theorem isFirstOrder_startClause : (startClause c).IsFirstOrder := by
  refine isFirstOrder_imp.mpr ⟨isFirstOrder_first _, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  trivial

theorem isFirstOrder_stepClause : (stepClause c).IsFirstOrder := by
  refine isFirstOrder_imp.mpr ⟨trivial, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial, trivial⟩

theorem isFirstOrder_lastClause : (lastClause c).IsFirstOrder := by
  refine isFirstOrder_imp.mpr ⟨isFirstOrder_last _, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
theorem isFirstOrder_emptyClause : (emptyClause c).IsFirstOrder := by
  unfold emptyClause
  split_ifs
  · exact isFirstOrder_top
  · trivial

omit [FinEnum B] in
theorem isFirstOrder_buchiClause : (buchiClause c).IsFirstOrder := by
  refine isFirstOrder_and.mpr ⟨trivial, isFirstOrder_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  trivial

omit [FinEnum B] in
theorem ltFree_disjointClause : (disjointClause c).LtFree := by
  refine ltFree_finiteAnd fun φ hφ ↦ ?_
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
theorem ltFree_startClause : (startClause c).LtFree := by
  refine ltFree_imp.mpr ⟨ltFree_first _, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  trivial

theorem ltFree_stepClause : (stepClause c).LtFree := by
  refine ltFree_imp.mpr ⟨trivial, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial, trivial⟩

theorem ltFree_lastClause : (lastClause c).LtFree := by
  refine ltFree_imp.mpr ⟨ltFree_last _, ltFree_finiteOr fun φ hφ ↦ ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
  exact ⟨trivial, trivial⟩

omit [FinEnum B] in
theorem ltFree_emptyClause : (emptyClause c).LtFree := by
  unfold emptyClause
  split_ifs
  · exact ltFree_top
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
  isEMSO_exAll₂ <| .firstOrder <| isFirstOrder_and.mpr ⟨isFirstOrder_disjointClause c,
    isFirstOrder_and.mpr ⟨isFirstOrder_startClause c, isFirstOrder_and.mpr
      ⟨isFirstOrder_stepClause c, isFirstOrder_and.mpr
        ⟨isFirstOrder_lastClause c, isFirstOrder_emptyClause c⟩⟩⟩⟩

/-- The sentence `toSentence` is a sentence of MSO[S]. -/
theorem ltFree_toSentence : (toSentence c).LtFree :=
  ltFree_exAll₂.mpr <| ltFree_and.mpr ⟨ltFree_disjointClause c,
    ltFree_and.mpr ⟨ltFree_startClause c, ltFree_and.mpr
      ⟨ltFree_stepClause c, ltFree_and.mpr ⟨ltFree_lastClause c, ltFree_emptyClause c⟩⟩⟩⟩

/-- The sentence `toωSentence` is first-order after its second-order prefix. -/
theorem isEMSO_toωSentence : (toωSentence c).IsEMSO :=
  isEMSO_exAll₂ <| .firstOrder <| isFirstOrder_and.mpr ⟨isFirstOrder_disjointClause c,
    isFirstOrder_and.mpr ⟨isFirstOrder_startClause c, isFirstOrder_and.mpr
      ⟨isFirstOrder_stepClause c, isFirstOrder_buchiClause c⟩⟩⟩

omit [FinEnum B] in
/-- Interpret the variables of the sentences by the positions where a function assumes a state. -/
private theorem exists_vars (M : WordModel B) (ρ : ℕ → c.State) :
    ∃ Y : Fin (FinEnum.card c.State) → Set ℕ,
      (∀ j, Y j ⊆ M.dom) ∧ ∀ q, Y (stateVar c q) = IsRunCode.codeOf M ρ q :=
  ⟨fun j ↦ IsRunCode.codeOf M ρ (FinEnum.equiv.symm j), fun _ _ hp ↦ hp.1,
    fun q ↦ by simp [stateVar]⟩

variable {c}

/-- The sentence `toSentence` expresses the acceptance of a finite word by the automaton (first part
of the proof of Theorem 3.1 of [Thomas1997]). -/
theorem holds_toSentence {w : List B} : (toSentence c).Holds (ofList w) ↔ w ∈ c.language := by
  rw [Sentence.Holds, toSentence, satisfies_exAll₂, mem_language_iff]
  constructor
  · rintro ⟨Y, -, h⟩
    simp only [satisfies_and] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    have hrun : IsRunCode c (ofList w) (fun q ↦ Y (stateVar c q)) :=
      isRunCode_iff.mpr ⟨h₁, h₂, h₃⟩
    by_cases hw : w = []
    · subst hw
      obtain ⟨s, hs, ha⟩ | ⟨p, hp⟩ := satisfies_emptyClause.mp h₅
      · exact ⟨fun _ ↦ s, hs, ha, fun i h ↦ absurd h (Nat.not_lt_zero i)⟩
      · exact absurd (mem_dom_ofList.mp hp) (Nat.not_lt_zero p)
    · have hlen : 0 < w.length := List.length_pos_iff.mpr hw
      have h0 : 0 ∈ (ofList w).dom := mem_dom_ofList.mpr hlen
      obtain ⟨s₀, -, -⟩ := hrun.first h0
      have : Nonempty c.State := ⟨s₀⟩
      obtain ⟨ρ, hρ, hstart, hstep⟩ := hrun.exists_run
      have hlast : w.length - 1 ∈ (ofList w).dom := mem_dom_ofList.mpr (by omega)
      obtain ⟨q, a, r, htr, hr, hq, ha⟩ :=
        satisfies_lastClause.mp h₄ _ hlast (by simp only [mem_dom_ofList]; omega)
      have hqρ : q = ρ (w.length - 1) := by
        by_contra hne
        exact hrun.disjoint q _ hne _ hlast hq (hρ _ hlast)
      refine ⟨fun i ↦ if i < w.length then ρ i else r, ?_, ?_, fun i hi ↦ ?_⟩
      · simpa only [hlen, ↓reduceIte] using hstart h0
      · simpa only [lt_self_iff_false, ↓reduceIte] using hr
      · by_cases hi' : i + 1 < w.length
        · obtain ⟨a', ha', htr'⟩ := hstep i (mem_dom_ofList.mpr hi')
          simp only [ofList_label, List.getElem?_eq_getElem hi, Option.some.injEq] at ha'
          simpa only [hi, hi', ↓reduceIte, ha'] using htr'
        · obtain rfl : i = w.length - 1 := by omega
          simp only [ofList_label, List.getElem?_eq_getElem hi, Option.some.injEq] at ha
          simpa only [hi, hi', ↓reduceIte, ha, ← hqρ] using htr
  · rintro ⟨ρ, hs, ha, hρ⟩
    obtain ⟨Y, hYdom, hY⟩ := exists_vars (c := c) (ofList w) ρ
    have hrun : IsRunCode c (ofList w) (fun q ↦ Y (stateVar c q)) := by
      simp only [hY]
      refine IsRunCode.of_run (fun _ ↦ hs) fun p hp ↦ ?_
      have hp' : p + 1 < w.length := mem_dom_ofList.mp hp
      exact ⟨w[p], List.getElem?_eq_getElem _, hρ p _⟩
    obtain ⟨h₁, h₂, h₃⟩ := isRunCode_iff.mp hrun
    refine ⟨Y, hYdom, ?_⟩
    simp only [satisfies_and]
    refine ⟨h₁, h₂, h₃, satisfies_lastClause.mpr ?_, satisfies_emptyClause.mpr ?_⟩
    · intro p hp hp'
      have hlt : p < w.length := mem_dom_ofList.mp hp
      have hlen : p + 1 = w.length := by
        by_contra hne
        exact hp' (mem_dom_ofList.mpr (by omega))
      refine ⟨ρ p, w[p], ρ (p + 1), hρ p hlt, hlen ▸ ha, ?_, List.getElem?_eq_getElem _⟩
      rw [hY]
      exact ⟨hp, rfl⟩
    · by_cases hw : w = []
      · subst hw
        exact Or.inl ⟨ρ 0, hs, ha⟩
      · exact Or.inr ⟨0, mem_dom_ofList.mpr (List.length_pos_iff.mpr hw)⟩

/-- The sentence `toωSentence` expresses the acceptance of an ω-word by the automaton as a Büchi
automaton (first part of the proof of Theorem 5.9 of [Thomas1997]). -/
theorem holds_toωSentence {α : ωSequence B} :
    (toωSentence c).Holds (ofOmega α) ↔ α ∈ c.ωlanguage := by
  rw [Sentence.Holds, toωSentence, satisfies_exAll₂, mem_ωlanguage_iff]
  constructor
  · rintro ⟨Y, -, h⟩
    simp only [satisfies_and] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hrun : IsRunCode c (ofOmega α) (fun q ↦ Y (stateVar c q)) :=
      isRunCode_iff.mpr ⟨h₁, h₂, h₃⟩
    obtain ⟨s₀, -, -⟩ := hrun.first mem_dom_ofOmega
    have : Nonempty c.State := ⟨s₀⟩
    obtain ⟨ρ, hρ, hstart, hstep⟩ := hrun.exists_run
    refine ⟨ρ, hstart mem_dom_ofOmega, fun i ↦ ?_, ?_⟩
    · obtain ⟨a, ha, htr⟩ := hstep i mem_dom_ofOmega
      obtain rfl := Option.some.inj ha
      exact htr
    · rw [Filter.frequently_atTop']
      intro p
      obtain ⟨p', hp', hlt, q, hq, hqp⟩ := satisfies_buchiClause.mp h₄ p mem_dom_ofOmega
      have hqρ : q = ρ p' := by
        by_contra hne
        exact hrun.disjoint q _ hne _ hp' hqp (hρ _ hp')
      exact ⟨p', hlt, hqρ ▸ hq⟩
  · rintro ⟨ρ, hs, htr, hacc⟩
    obtain ⟨Y, hYdom, hY⟩ := exists_vars (c := c) (ofOmega α) ρ
    have hrun : IsRunCode c (ofOmega α) (fun q ↦ Y (stateVar c q)) := by
      simp only [hY]
      exact IsRunCode.of_run (fun _ ↦ hs) fun p _ ↦ ⟨α p, rfl, htr p⟩
    obtain ⟨h₁, h₂, h₃⟩ := isRunCode_iff.mp hrun
    refine ⟨Y, hYdom, ?_⟩
    simp only [satisfies_and]
    refine ⟨h₁, h₂, h₃, satisfies_buchiClause.mpr fun p _ ↦ ?_⟩
    obtain ⟨p', hlt, hp'⟩ := Filter.frequently_atTop'.mp hacc p
    refine ⟨p', mem_dom_ofOmega, hlt, ρ p', hp', ?_⟩
    rw [hY]
    exact ⟨mem_dom_ofOmega, rfl⟩

end Cslib.Automata.EffectiveNA
