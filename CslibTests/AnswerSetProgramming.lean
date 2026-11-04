/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

import Cslib.Languages.AnswerSetProgramming.Equilibrium

namespace CslibTests.AnswerSetProgramming

open Cslib ASP Logic HT
open scoped InferenceSystem

/-- The rule `a ← not b`. -/
private abbrev negRule (a b : Char) : Rule Char := ⟨a, [], [b]⟩

/-- The program `{a ← not b, b ← not a}`. -/
private abbrev choice : Program Char := {negRule 'a' 'b', negRule 'b' 'a'}

/-! ### The reduct -/

example : (negRule 'a' 'b').reduct = ⟨'a', [], []⟩ := rfl

example : (negRule 'a' 'b').reduct ∈ Program.reduct {negRule 'a' 'b'} {'a'} :=
  Program.mem_reduct.mpr ⟨_, rfl, by simp, rfl⟩

/-! ### Stable models -/

-- `{a}` is a stable model of `{a ← not b}`.
example : IsStableModel {'a'} ({negRule 'a' 'b'} : Program Char) := by
  rw [IsStableModel, isMinimalClassicalModel_iff]
  constructor
  · rw [isClassicalModel_reduct_iff]
    rintro _ rfl -
    simp [satisfiesRule_reduct_iff]
  · intro J hJ hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hJ
    rw [isClassicalModel_reduct_iff] at hmodel
    simpa [satisfiesRule_reduct_iff] using hmodel _ rfl (by simp)

-- `∅` is not a stable model of `{a ← not b}`.
example : ¬IsStableModel ∅ ({negRule 'a' 'b'} : Program Char) := fun h => by
  have hmodel := isClassicalModel_reduct_iff.mp h.1 _ rfl (by simp)
  simp [satisfiesRule_reduct_iff] at hmodel

-- `{a}` is a stable model of `{a ← not b, b ← not a}`.
example : IsStableModel {'a'} choice := by
  rw [IsStableModel, isMinimalClassicalModel_iff]
  constructor
  · rw [isClassicalModel_reduct_iff]
    rintro _ (rfl | rfl) hneg
    · simp [satisfiesRule_reduct_iff]
    · simp at hneg
  · intro J hJ hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hJ
    rw [isClassicalModel_reduct_iff] at hmodel
    simpa [satisfiesRule_reduct_iff] using hmodel (negRule 'a' 'b') (by simp) (by simp)

-- `{a, b}` is not a stable model of `{a ← not b, b ← not a}`, since both rules are removed from the
-- reduct and `∅` is a smaller model.
example : ¬IsStableModel {'a', 'b'} choice := fun h => by
  rw [IsStableModel, isMinimalClassicalModel_iff] at h
  refine h.2 ∅ (by simp [Set.empty_ssubset]) (isClassicalModel_reduct_iff.mpr ?_)
  rintro _ (rfl | rfl) hneg <;> simp at hneg

/-! ### The translation -/

example :
    (⟨'a', ['x'], ['y']⟩ : Rule Char).toProposition =
      (((.atom ↑'x' ∧ ⊤) ∧ (¬.atom ↑'y' ∧ ⊤)) → .atom ↑'a') :=
  rfl

example : (negRule 'a' 'b').toProposition ∈ Program.toTheory {negRule 'a' 'b'} :=
  ⟨_, rfl, rfl⟩

/-! ### The correspondence -/

-- `{a}` is an equilibrium model of the translation of `{a ← not b, b ← not a}`, shown directly.
example : IsEquilibriumModel {'a'} (Program.toTheory choice) := by
  rw [isEquilibriumModel_iff]
  constructor
  · rw [isModel_toTheory_iff]
    rintro _ (rfl | rfl) <;>
      simp [satisfies_toProposition_here_iff, SatisfiesRule, Interpretation.total]
  · intro H hH hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hH
    rw [isModel_toTheory_iff] at hmodel
    have h := satisfies_toProposition_here_iff.mp (hmodel (negRule 'a' 'b') (by simp))
    simp at h

-- The same fact, obtained from the stable model through the correspondence theorem.
example (h : IsStableModel {'a'} choice) : IsEquilibriumModel {'a'} (Program.toTheory choice) :=
  (isStableModel_iff_isEquilibriumModel _ _).mp h

end CslibTests.AnswerSetProgramming
