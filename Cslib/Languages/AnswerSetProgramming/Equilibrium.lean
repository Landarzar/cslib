/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

module

public import Cslib.Languages.AnswerSetProgramming.StableModel
public import Cslib.Logics.HereAndThere.Equilibrium

/-! # Stable models are equilibrium models

The translation of normal logic programs into theories of Here-and-There logic, and Pearce's
correspondence theorem [Pearce1997] for normal programs: a set of atoms is a stable model of a
program iff it is an equilibrium model of the translated program.

## Main definitions

- `ASP.Rule.toProposition`: the translation `τ(r) := (⋀ body⁺(r) ∧ ⋀ ¬body⁻(r)) → head(r)`.
- `ASP.Program.toTheory`: the image of a program under the translation.

## Main results

- `ASP.isStableModel_iff_isEquilibriumModel`: Pearce's correspondence theorem.

## References

* [D. Pearce, *A New Logical Characterisation of Stable Models and Answer Sets*][Pearce1997]
* [M. Gelfond, V. Lifschitz, *The Stable Model Semantics for Logic Programming*]
  [GelfondLifschitz1988]
-/

@[expose] public section

universe u

namespace Cslib.ASP

open Logic HT
open scoped InferenceSystem

variable {Atom : Type u}

/-- Translates a rule by folding its two bodies into conjunctions:
`τ(r) := (⋀ body⁺(r) ∧ ⋀ ¬body⁻(r)) → head(r)`. -/
def Rule.toProposition (r : Rule Atom) : HT.Proposition Atom :=
  (⋀(r.bodyPos.map fun a => .atom ↑a) ∧ ⋀(r.bodyNeg.map fun a => ¬.atom ↑a)) → .atom ↑r.head

/-- Translates a program by taking the image of `Rule.toProposition`. -/
def Program.toTheory (P : Program Atom) : HT.Theory Atom := Rule.toProposition '' P

/-- A folded positive body is read against the atoms of the current world. -/
theorem satisfies_finiteAnd_atom_iff {I : Interpretation Atom} {w : World} {l : List Atom} :
    ⇓HT[I,w ⊨ ⋀(l.map fun a => .atom ↑a)] ↔ ∀ a ∈ l, a ∈ I.atoms w := by
  simp [Satisfies.finiteAnd_iff_forall]

/-- A folded negative body is read against `there`, at either world. -/
theorem satisfies_finiteAnd_not_atom_iff {I : Interpretation Atom} {w : World} {l : List Atom} :
    ⇓HT[I,w ⊨ ⋀(l.map fun a => ¬.atom ↑a)] ↔ ∀ a ∈ l, a ∉ I.there := by
  cases w <;>
    simp [Satisfies.finiteAnd_iff_forall, Satisfies.not_here_iff, Satisfies.not_there_iff,
      Interpretation.atoms]

/-- Being a model of a translated program, re-indexed over the rules of the program. -/
theorem isModel_toTheory_iff {I : Interpretation Atom} {P : Program Atom} :
    I.IsModel P.toTheory ↔ ∀ r ∈ P, ⇓HT[I,.here ⊨ r.toProposition] := by
  simp only [Interpretation.IsModel, Program.toTheory, Set.forall_mem_image]

/-- At `there`, satisfaction of a translated rule is classical satisfaction by the `there`
component. -/
theorem satisfies_toProposition_there_iff {I : Interpretation Atom} {r : Rule Atom} :
    ⇓HT[I,.there ⊨ r.toProposition] ↔ SatisfiesRule I.there r := by
  rw [Rule.toProposition, Satisfies.imp_there_iff, Satisfies.and_iff_and,
    satisfies_finiteAnd_atom_iff, satisfies_finiteAnd_not_atom_iff, Satisfies.atom_iff, and_imp]
  rfl

/-- At `here`, satisfaction of a translated rule splits into a condition reading the positive body
at `here` and the negative body at `there`, together with classical satisfaction by the `there`
component. This is what makes it comparable with a model of the reduct. -/
theorem satisfies_toProposition_here_iff {I : Interpretation Atom} {r : Rule Atom} :
    ⇓HT[I,.here ⊨ r.toProposition] ↔
      (((∀ a ∈ r.bodyPos, a ∈ I.here) ∧ ∀ a ∈ r.bodyNeg, a ∉ I.there) → r.head ∈ I.here) ∧
        SatisfiesRule I.there r := by
  rw [← satisfies_toProposition_there_iff, Rule.toProposition, Satisfies.imp_here_iff,
    Satisfies.and_iff_and, satisfies_finiteAnd_atom_iff, satisfies_finiteAnd_not_atom_iff,
    Satisfies.atom_iff]
  rfl

/-- A set of atoms is a classical model of a program iff the total interpretation is a model of the
translated program. -/
theorem isClassicalModel_iff_isModel_total {I : Set Atom} {P : Program Atom} :
    IsClassicalModel I P ↔ (Interpretation.total I).IsModel P.toTheory := by
  rw [isModel_toTheory_iff]
  refine forall₂_congr fun r _ => ?_
  rw [Satisfies.total_here_iff_there, satisfies_toProposition_there_iff]
  rfl

/-- For a classical model `T` of a program, `H ⊆ T` is a classical model of the reduct with respect
to `T` iff `⟨H, T⟩` is a model of the translated program. -/
theorem isClassicalModel_reduct_iff_isModel {H T : Set Atom} (sub : H ⊆ T) {P : Program Atom}
    (hT : IsClassicalModel T P) :
    IsClassicalModel H (P.reduct T) ↔ (Interpretation.mk H T sub).IsModel P.toTheory := by
  rw [isClassicalModel_reduct_iff, isModel_toTheory_iff]
  constructor
  · intro h r hr
    rw [satisfies_toProposition_here_iff]
    exact ⟨fun ⟨hpos, hneg⟩ => satisfiesRule_reduct_iff.mp (h r hr hneg) hpos, hT r hr⟩
  · intro h r hr hneg
    rw [satisfiesRule_reduct_iff]
    exact fun hpos => (satisfies_toProposition_here_iff.mp (h r hr)).1 ⟨hpos, hneg⟩

/-- Pearce's correspondence theorem for normal programs: a set of atoms is a stable model of a
program iff it is an equilibrium model of the translated program [Pearce1997]. -/
theorem isStableModel_iff_isEquilibriumModel (I : Set Atom) (P : Program Atom) :
    IsStableModel I P ↔ IsEquilibriumModel I P.toTheory := by
  rw [IsStableModel, isMinimalClassicalModel_iff, isEquilibriumModel_iff]
  constructor
  · rintro ⟨hreduct, hmin⟩
    have hI := isClassicalModel_of_isClassicalModel_reduct hreduct
    refine ⟨isClassicalModel_iff_isModel_total.mp hI, fun J hJ hmodel => hmin J hJ ?_⟩
    exact (isClassicalModel_reduct_iff_isModel hJ.subset hI).mpr hmodel
  · rintro ⟨htotal, hmin⟩
    have hI := isClassicalModel_iff_isModel_total.mpr htotal
    refine ⟨(isClassicalModel_reduct_iff_isModel subset_rfl hI).mpr htotal, fun J hJ hmodel => ?_⟩
    exact hmin J hJ ((isClassicalModel_reduct_iff_isModel hJ.subset hI).mp hmodel)

end Cslib.ASP
