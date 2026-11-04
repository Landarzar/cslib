/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

module

public import Cslib.Languages.AnswerSetProgramming.Basic
public import Mathlib.Order.Minimal

/-! # Stable models

Stable models of normal logic programs, defined as the minimal classical models of their own
Gelfond-Lifschitz reduct [GelfondLifschitz1988].

## Main definitions

- `ASP.Rule.reduct`, `ASP.Program.reduct`: the Gelfond-Lifschitz reduct.
- `ASP.IsMinimalClassicalModel`: classical models with no classical model as a proper subset.
- `ASP.IsStableModel`: stable models.

## Main results

- `ASP.isMinimalClassicalModel_reduct_unique`: a reduct has at most one minimal classical model.
- `ASP.isMinimalClassicalModel_of_isStableModel`: stable models are minimal classical models of the
  program itself, which is Theorem 1 of [GelfondLifschitz1988].

## References

* [M. Gelfond, V. Lifschitz, *The Stable Model Semantics for Logic Programming*]
  [GelfondLifschitz1988]
-/

@[expose] public section

universe u

namespace Cslib.ASP

variable {Atom : Type u} {I J : Set Atom} {P : Program Atom} {r r' : Rule Atom}

/-- Removes the negative body of a rule. -/
def Rule.reduct (r : Rule Atom) : Rule Atom := { r with bodyNeg := [] }

/-- The Gelfond-Lifschitz reduct of a program with respect to `I`: drop every rule whose negative
body meets `I`, and remove the negative bodies of the others. -/
def Program.reduct (P : Program Atom) (I : Set Atom) : Program Atom :=
  Rule.reduct '' {r ∈ P | ∀ a ∈ r.bodyNeg, a ∉ I}

/-- A minimal classical model is a classical model with no classical model as a proper subset. -/
def IsMinimalClassicalModel (I : Set Atom) (P : Program Atom) : Prop :=
  Minimal (IsClassicalModel · P) I

/-- A stable model is a minimal classical model of its own Gelfond-Lifschitz reduct. -/
def IsStableModel (I : Set Atom) (P : Program Atom) : Prop :=
  IsMinimalClassicalModel I (P.reduct I)

/-- The explicit form of `IsMinimalClassicalModel`. -/
theorem isMinimalClassicalModel_iff :
    IsMinimalClassicalModel I P ↔
      IsClassicalModel I P ∧ ∀ J, J ⊂ I → ¬IsClassicalModel J P := by
  rw [IsMinimalClassicalModel, Set.minimal_iff_forall_ssubset]

theorem Program.mem_reduct :
    r' ∈ P.reduct I ↔ ∃ r ∈ P, (∀ a ∈ r.bodyNeg, a ∉ I) ∧ r' = r.reduct := by
  constructor
  · rintro ⟨r, ⟨hr, hneg⟩, rfl⟩
    exact ⟨r, hr, hneg, rfl⟩
  · rintro ⟨r, hr, hneg, rfl⟩
    exact ⟨r, ⟨hr, hneg⟩, rfl⟩

/-- Being a classical model of a reduct, re-indexed over the rules of the program. -/
theorem isClassicalModel_reduct_iff :
    IsClassicalModel J (P.reduct I) ↔
      ∀ r ∈ P, (∀ a ∈ r.bodyNeg, a ∉ I) → SatisfiesRule J r.reduct := by
  constructor
  · exact fun h r hr hneg => h _ (Program.mem_reduct.mpr ⟨r, hr, hneg, rfl⟩)
  · intro h r' hr'
    obtain ⟨r, hr, hneg, rfl⟩ := Program.mem_reduct.mp hr'
    exact h r hr hneg

/-- A reduced rule has an empty negative body, so its satisfaction is a single implication. -/
theorem satisfiesRule_reduct_iff :
    SatisfiesRule I r.reduct ↔ ((∀ a ∈ r.bodyPos, a ∈ I) → r.head ∈ I) := by
  simp [SatisfiesRule, Rule.reduct]

/-- A classical model of its own reduct is a classical model of the program. -/
theorem isClassicalModel_of_isClassicalModel_reduct
    (h : IsClassicalModel I (P.reduct I)) : IsClassicalModel I P :=
  fun r hr hpos hneg =>
    satisfiesRule_reduct_iff.mp (isClassicalModel_reduct_iff.mp h r hr hneg) hpos

/-- A stable model is a classical model of the program. -/
theorem isClassicalModel_of_isStableModel (h : IsStableModel I P) : IsClassicalModel I P :=
  isClassicalModel_of_isClassicalModel_reduct h.1

/-- Classical models of a reduct are closed under intersection. -/
theorem isClassicalModel_reduct_inter {T : Set Atom}
    (hI : IsClassicalModel I (P.reduct T)) (hJ : IsClassicalModel J (P.reduct T)) :
    IsClassicalModel (I ∩ J) (P.reduct T) := by
  rw [isClassicalModel_reduct_iff] at hI hJ ⊢
  intro r hr hneg
  rw [satisfiesRule_reduct_iff]
  intro hpos
  exact ⟨satisfiesRule_reduct_iff.mp (hI r hr hneg) fun a ha => (hpos a ha).1,
    satisfiesRule_reduct_iff.mp (hJ r hr hneg) fun a ha => (hpos a ha).2⟩

/-- A reduct has at most one minimal classical model. -/
theorem isMinimalClassicalModel_reduct_unique {T : Set Atom}
    (hI : IsMinimalClassicalModel I (P.reduct T)) (hJ : IsMinimalClassicalModel J (P.reduct T)) :
    I = J := by
  have hinter := isClassicalModel_reduct_inter hI.1 hJ.1
  exact Set.Subset.antisymm
    (fun _ ha => (hI.2 hinter Set.inter_subset_left ha).2)
    (fun _ ha => (hJ.2 hinter Set.inter_subset_right ha).1)

/-- A classical model of a program that is a subset of `I` is a classical model of the reduct with
respect to `I`. -/
theorem isClassicalModel_reduct_of_subset (hsub : J ⊆ I) (h : IsClassicalModel J P) :
    IsClassicalModel J (P.reduct I) := by
  rw [isClassicalModel_reduct_iff]
  intro r hr hneg
  rw [satisfiesRule_reduct_iff]
  exact fun hpos => h r hr hpos fun a ha haJ => hneg a ha (hsub haJ)

/-- A stable model is a minimal classical model of the program [GelfondLifschitz1988, Theorem 1]. -/
theorem isMinimalClassicalModel_of_isStableModel (h : IsStableModel I P) :
    IsMinimalClassicalModel I P := by
  rw [IsStableModel, isMinimalClassicalModel_iff] at h
  rw [isMinimalClassicalModel_iff]
  exact ⟨isClassicalModel_of_isClassicalModel_reduct h.1,
    fun J hJ hmodel => h.2 J hJ (isClassicalModel_reduct_of_subset hJ.subset hmodel)⟩

end Cslib.ASP
