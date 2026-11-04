/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

import Cslib.Logics.HereAndThere.Equilibrium

namespace CslibTests.HereAndThere

open Cslib Logic HT
open scoped InferenceSystem

variable {Atom : Type*}

/-- The proposition `¬b → a`. -/
private abbrev negImp (a b : Atom) : Proposition Atom := ¬.atom ↑b → .atom ↑a

/-- The theory `{¬b → a, ¬a → b}`. -/
private abbrev choice (a b : Atom) : Theory Atom := {negImp a b, negImp b a}

private theorem negImp_here_iff {I : Interpretation Atom} {a b : Atom} :
    ⇓HT[I,.here ⊨ negImp a b] ↔ (b ∉ I.there → a ∈ I.here) ∧ (b ∉ I.there → a ∈ I.there) := by
  rw [Satisfies.imp_here_iff, Satisfies.not_here_iff, Satisfies.not_there_iff]
  simp [Interpretation.atoms]

private theorem isModel_choice_iff {I : Interpretation Atom} {a b : Atom} :
    I.IsModel (choice a b) ↔ ⇓HT[I,.here ⊨ negImp a b] ∧ ⇓HT[I,.here ⊨ negImp b a] := by
  simp [Interpretation.IsModel]

/-! ### Satisfaction -/

-- At `⟨∅, {a, b}⟩`, the implication `¬b → a` holds at `here` although `a` does not, since `¬b`
-- fails at every reachable world.
example (a b : Atom) :
    ⇓HT[⟨∅, {a, b}, Set.empty_subset _⟩,.here ⊨ negImp a b] := by
  simp [negImp_here_iff]

example (a b : Atom) : ¬⇓HT[⟨∅, {a, b}, Set.empty_subset _⟩,.here ⊨ .atom ↑a] := by
  simp [Interpretation.atoms]

example (a b : Atom) : ⇓HT[⟨∅, {a, b}, Set.empty_subset _⟩,.there ⊨ .atom ↑a] := by
  simp [Interpretation.atoms]

example (a b : Atom) (hab : a ≠ b) :
    ¬(Interpretation.mk ∅ {a} (Set.empty_subset _)).IsModel (choice a b) := by
  simp [isModel_choice_iff, negImp_here_iff, hab.symm]

-- The two worlds can disagree on an atom.
example : ¬(⇓HT[⟨∅, {'a'}, Set.empty_subset _⟩,.here ⊨ .atom ↑'a'] ↔
    ⇓HT[⟨∅, {'a'}, Set.empty_subset _⟩,.there ⊨ .atom ↑'a']) := by
  simp [Interpretation.atoms]

-- `⟨{a}, {a, b}⟩` is not total, so some proposition separates its worlds.
example : ∃ φ : Proposition Char,
    ¬(⇓HT[⟨{'a'}, {'a', 'b'}, by simp⟩,.here ⊨ φ] ↔ ⇓HT[⟨{'a'}, {'a', 'b'}, by simp⟩,.there ⊨ φ]) :=
  exists_not_here_iff_there ⟨by simp, by simp⟩

-- `⊥` and `⊤` are the ones of propositional logic.
example (I : Interpretation Atom) (w : World) : ⇓HT[I,w ⊨ (⊥ → ⊥)] := Satisfies.top

/-! ### Equilibrium models -/

example : IsEquilibriumModel {'a'} ({negImp 'a' 'b'} : Theory Char) := by
  rw [isEquilibriumModel_iff]
  constructor
  · rintro _ rfl
    simp [negImp_here_iff, Interpretation.total]
  · intro H hH hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hH
    have := negImp_here_iff.mp (hmodel _ rfl)
    simp at this

-- Consider the theory `Γ = {¬b → a, ¬a → b}` for the rest of this section.

-- `⟨{a}, {a}⟩` is an equilibrium model.
example : IsEquilibriumModel {'a'} (choice 'a' 'b') := by
  rw [isEquilibriumModel_iff]
  constructor
  · simp [isModel_choice_iff, negImp_here_iff, Interpretation.total]
  · intro H hH hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hH
    simp [isModel_choice_iff, negImp_here_iff] at hmodel

-- `⟨{b}, {b}⟩` is an equilibrium model.
example : IsEquilibriumModel {'b'} (choice 'a' 'b') := by
  rw [isEquilibriumModel_iff]
  constructor
  · simp [isModel_choice_iff, negImp_here_iff, Interpretation.total]
  · intro H hH hmodel
    obtain rfl := Set.ssubset_singleton_iff.mp hH
    simp [isModel_choice_iff, negImp_here_iff] at hmodel

private theorem isModel_empty_choice :
    (Interpretation.mk ∅ {'a', 'b'} (Set.empty_subset _)).IsModel (choice 'a' 'b') := by
  simp [isModel_choice_iff, negImp_here_iff]

-- `⟨∅, {a, b}⟩` is a minimal model.
example : (Interpretation.mk ∅ {'a', 'b'} (Set.empty_subset _)).IsMinimal (choice 'a' 'b') :=
  Interpretation.isMinimal_iff.mpr
    ⟨isModel_empty_choice, fun _ hH => absurd (Set.nonempty_of_ssubset' hH) Set.not_nonempty_empty⟩

-- `⟨{a, b}, {a, b}⟩` is a model.
example : (Interpretation.total {'a', 'b'}).IsModel (choice 'a' 'b') := by
  simp [isModel_choice_iff, negImp_here_iff, Interpretation.total]

-- `⟨{a, b}, {a, b}⟩` is not an equilibrium model, since it is not minimal.
example : ¬IsEquilibriumModel {'a', 'b'} (choice 'a' 'b') := fun h =>
  (isEquilibriumModel_iff.mp h).2 ∅ (by simp [Set.empty_ssubset]) isModel_empty_choice

end CslibTests.HereAndThere
