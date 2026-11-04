/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

module

public import Cslib.Logics.HereAndThere.Basic
public import Mathlib.Order.Minimal

/-! # Equilibrium models

Equilibrium models are the total models of a theory in Here-and-There logic that are minimal with
respect to the atoms true at `here` [Pearce1997]. They give a purely logical account of the stable
models of logic programs, see `Cslib.ASP.isStableModel_iff_isEquilibriumModel`.

## Main definitions

- `HT.Interpretation.IsMinimal`: models of a theory whose `here` component cannot be shrunk.
- `HT.IsEquilibriumModel`: the set `T` is an equilibrium model if `⟨T, T⟩` is minimal.

## Main results

- `HT.isEquilibriumModel_iff`: the explicit form of the definition.
- `HT.not_isEquilibriumModel_mono`: equilibrium models are nonmonotonic.

## References

* [D. Pearce, *A New Logical Characterisation of Stable Models and Answer Sets*][Pearce1997]
-/

@[expose] public section

universe u

namespace Cslib.Logic.HT

open scoped InferenceSystem

variable {Atom : Type u}

/-- A model of a theory is minimal if no proper subset of its `here` component gives a model with
the same `there` component. -/
def Interpretation.IsMinimal (I : Interpretation Atom) (Γ : Theory Atom) : Prop :=
  Minimal (fun H => ∃ h : H ⊆ I.there, (Interpretation.mk H I.there h).IsModel Γ) I.here

/-- The explicit form of `Interpretation.IsMinimal`. -/
theorem Interpretation.isMinimal_iff {I : Interpretation Atom} {Γ : Theory Atom} :
    I.IsMinimal Γ ↔ I.IsModel Γ ∧ ∀ (H : Set Atom) (hH : H ⊂ I.here),
      ¬(Interpretation.mk H I.there (hH.subset.trans I.subset)).IsModel Γ := by
  rw [IsMinimal, Set.minimal_iff_forall_ssubset]
  constructor
  · rintro ⟨⟨_, hI⟩, hmin⟩
    exact ⟨hI, fun H hH hmodel => hmin hH ⟨_, hmodel⟩⟩
  · rintro ⟨hI, hmin⟩
    exact ⟨⟨I.subset, hI⟩, fun H hH ⟨_, hmodel⟩ => hmin H hH hmodel⟩

/-- A set of atoms `T` is an equilibrium model of a theory if `⟨T, T⟩` is a minimal model. -/
def IsEquilibriumModel (T : Set Atom) (Γ : Theory Atom) : Prop :=
  (Interpretation.total T).IsMinimal Γ

/-- The explicit form of `IsEquilibriumModel`. -/
theorem isEquilibriumModel_iff {T : Set Atom} {Γ : Theory Atom} :
    IsEquilibriumModel T Γ ↔ (Interpretation.total T).IsModel Γ ∧
      ∀ (H : Set Atom) (hH : H ⊂ T), ¬(Interpretation.mk H T hH.subset).IsModel Γ :=
  Interpretation.isMinimal_iff

/-- Equilibrium models are nonmonotonic: for distinct atoms `a` and `b`, the set `{a}` is an
equilibrium model of `{¬b → a}`, but not of the larger theory `{¬b → a, b}`. -/
theorem not_isEquilibriumModel_mono [Nontrivial Atom] :
    ¬∀ (Γ Δ : Theory Atom) (T : Set Atom),
      Γ ⊆ Δ → IsEquilibriumModel T Γ → IsEquilibriumModel T Δ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne Atom
  intro h
  let φ : Proposition Atom := ¬.atom ↑b → .atom ↑a
  have hequilibrium : IsEquilibriumModel {a} ({φ} : Theory Atom) := by
    rw [isEquilibriumModel_iff]
    constructor
    · rintro _ rfl
      simp [φ, Satisfies.imp_here_iff, Interpretation.atoms, Interpretation.total]
    · intro H hH hmodel
      obtain rfl := Set.ssubset_singleton_iff.mp hH
      have hφ : ⇓HT[⟨∅, {a}, hH.subset⟩,.here ⊨ ¬.atom ↑b → .atom ↑a] := hmodel φ rfl
      rw [Satisfies.imp_here_iff, Satisfies.not_here_iff] at hφ
      simpa [Interpretation.atoms, hab.symm] using hφ.1
  have hb := (isEquilibriumModel_iff.mp
    (h {φ} (insert (.atom ↑b) {φ}) {a} (Set.subset_insert _ _) hequilibrium)).1 (.atom ↑b)
    (Set.mem_insert _ _)
  simp [Interpretation.atoms, Interpretation.total, hab.symm] at hb

end Cslib.Logic.HT
