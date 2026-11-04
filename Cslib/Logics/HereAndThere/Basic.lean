/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Here-and-There logic

Here-and-There (HT) logic is the intermediate logic of the two-world Kripke frame `here ≤ there`,
and the logical foundation of equilibrium models [Pearce1997].

HT logic has no syntax of its own. Its propositions are those of CSLib's propositional logic
(`PL.Proposition`) over `WithBot Atom`, following `PL.Theory.intuitionisticCompletion`: the added
bottom element is falsum, negation is the defined connective `¬φ := φ → ⊥`, and an interpretation
only has to speak about the atoms in `Atom`.

## Main definitions

- `HT.Proposition`, `HT.Theory`: propositions and theories of HT logic.
- `HT.World`: the two worlds of the frame.
- `HT.Interpretation`: pairs `⟨H, T⟩` of sets of atoms with `H ⊆ T`.
- `HT.Satisfies`, with the notation `⇓HT[I,w ⊨ φ]`: satisfaction at a world.
- `HT.Interpretation.IsModel`: an interpretation satisfying a theory at `here`.
- `HT.Valid`, `HT.Entails`: validity and consequence.

## Main results

- `HT.Satisfies.there_of_here`: persistence, what holds at `here` also holds at `there`.
- `HT.Satisfies.not_here_iff`: negation at `here` is decided at `there`.
- `HT.valid_not_or_not_not`: the weak law of excluded middle is valid.
- `HT.not_valid_or_not`, `HT.not_valid_not_not_imp`: excluded middle and double negation
  elimination are not valid, although both hold at `there`.

## References

* [D. Pearce, *A New Logical Characterisation of Stable Models and Answer Sets*][Pearce1997]
* [V. Lifschitz, D. Pearce, A. Valverde, *Strongly Equivalent Logic Programs*][Lifschitz2001]
-/

@[expose] public section

universe u

namespace Cslib.Logic.HT

open scoped InferenceSystem

variable {Atom : Type u}

/-- Propositions of HT logic are propositional formulas over the atoms extended by falsum. -/
abbrev Proposition (Atom : Type u) := PL.Proposition (WithBot Atom)

/-- Theories of HT logic are arbitrary sets of propositions. -/
abbrev Theory (Atom : Type u) := PL.Theory (WithBot Atom)

/-- The two worlds of the frame, ordered by `here ≤ there`. -/
inductive World where
  /-- The world `here`, from which both worlds are reachable. -/
  | here
  /-- The world `there`, from which only `there` is reachable. -/
  | there
  deriving DecidableEq

/-- An HT interpretation is a pair `⟨H, T⟩` of sets of atoms with `H ⊆ T`. -/
structure Interpretation (Atom : Type u) where
  /-- The atoms true at `here`. -/
  here : Set Atom
  /-- The atoms true at `there`. -/
  there : Set Atom
  /-- Atoms true at `here` remain true at `there`. -/
  subset : here ⊆ there

/-- The atoms true at a world. -/
def Interpretation.atoms (I : Interpretation Atom) : World → Set Atom
  | .here => I.here
  | .there => I.there

/-- The total interpretation `⟨T, T⟩`. -/
def Interpretation.total (T : Set Atom) : Interpretation Atom := ⟨T, T, subset_rfl⟩

/-- Satisfaction of a proposition at a world. An implication has to hold at every world reachable
from the current one, and falsum holds nowhere since it is not an atom of `Atom`. -/
def Satisfies (I : Interpretation Atom) (w : World) : Proposition Atom → Prop
  | .atom a => ∃ x ∈ I.atoms w, a = ↑x
  | .and φ ψ => Satisfies I w φ ∧ Satisfies I w ψ
  | .or φ ψ => Satisfies I w φ ∨ Satisfies I w ψ
  | .imp φ ψ =>
    match w with
    | .here =>
      (Satisfies I .here φ → Satisfies I .here ψ) ∧ (Satisfies I .there φ → Satisfies I .there ψ)
    | .there => Satisfies I .there φ → Satisfies I .there ψ

/-- A judgement `HT[I,w ⊨ φ]`, stating that `φ` is satisfied at the world `w` of `I`. -/
structure Judgement (Atom : Type u) where
  /-- The interpretation. -/
  I : Interpretation Atom
  /-- The world. -/
  w : World
  /-- The proposition. -/
  φ : Proposition Atom

@[inherit_doc Judgement] scoped notation "HT[" I "," w " ⊨ " φ "]" => Judgement.mk I w φ

instance : HasInferenceSystem (Judgement Atom) := ⟨fun j => Satisfies j.I j.w j.φ⟩

variable {I : Interpretation Atom} {w : World} {φ ψ : Proposition Atom}

@[scoped grind =]
theorem derivation_def : Satisfies I w φ = ⇓HT[I,w ⊨ φ] := rfl

/-! ### Satisfaction of atoms and connectives -/

@[simp, scoped grind =]
theorem Satisfies.atom_iff {a : Atom} : ⇓HT[I,w ⊨ .atom ↑a] ↔ a ∈ I.atoms w := by
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [WithBot.coe_inj.mp h]
  · exact fun h => ⟨a, h, rfl⟩

@[simp, scoped grind =]
theorem Satisfies.bot_iff : ⇓HT[I,w ⊨ ⊥] ↔ False := by
  constructor
  · rintro ⟨x, -, h⟩
    exact WithBot.bot_ne_coe h
  · exact False.elim

@[scoped grind =]
theorem Satisfies.and_iff_and : ⇓HT[I,w ⊨ φ ∧ ψ] ↔ ⇓HT[I,w ⊨ φ] ∧ ⇓HT[I,w ⊨ ψ] := Iff.rfl

@[scoped grind =]
theorem Satisfies.or_iff_or : ⇓HT[I,w ⊨ φ ∨ ψ] ↔ ⇓HT[I,w ⊨ φ] ∨ ⇓HT[I,w ⊨ ψ] := Iff.rfl

@[scoped grind =]
theorem Satisfies.imp_here_iff :
    ⇓HT[I,.here ⊨ φ → ψ] ↔
      (⇓HT[I,.here ⊨ φ] → ⇓HT[I,.here ⊨ ψ]) ∧ (⇓HT[I,.there ⊨ φ] → ⇓HT[I,.there ⊨ ψ]) :=
  Iff.rfl

@[scoped grind =]
theorem Satisfies.imp_there_iff :
    ⇓HT[I,.there ⊨ φ → ψ] ↔ (⇓HT[I,.there ⊨ φ] → ⇓HT[I,.there ⊨ ψ]) :=
  Iff.rfl

/-- Persistence: a proposition satisfied at `here` is also satisfied at `there`. -/
theorem Satisfies.there_of_here (h : ⇓HT[I,.here ⊨ φ]) : ⇓HT[I,.there ⊨ φ] := by
  induction φ with
  | atom a =>
    obtain ⟨x, hx, h⟩ := h
    exact ⟨x, I.subset hx, h⟩
  | and φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact h.imp ihφ ihψ
  | imp φ ψ ihφ ihψ => exact h.2

/-- A negation at `here` is decided at `there`. -/
@[scoped grind =]
theorem Satisfies.not_here_iff : ⇓HT[I,.here ⊨ ¬φ] ↔ ¬⇓HT[I,.there ⊨ φ] := by
  rw [← PL.not_eq, imp_here_iff, bot_iff, bot_iff, imp_false, imp_false,
    and_iff_right_iff_imp]
  exact fun hThere hHere => hThere hHere.there_of_here

@[scoped grind =]
theorem Satisfies.not_there_iff : ⇓HT[I,.there ⊨ ¬φ] ↔ ¬⇓HT[I,.there ⊨ φ] := by
  rw [← PL.not_eq, imp_there_iff, bot_iff, imp_false]

@[simp, scoped grind .]
theorem Satisfies.top : ⇓HT[I,w ⊨ ⊤] := by
  cases w
  · exact ⟨id, id⟩
  · exact id

/-- A world satisfies a finite conjunction iff it satisfies all conjuncts. -/
@[scoped grind =]
theorem Satisfies.finiteAnd_iff_forall {φs : List (Proposition Atom)} :
    ⇓HT[I,w ⊨ ⋀φs] ↔ ∀ φ ∈ φs, ⇓HT[I,w ⊨ φ] := by
  induction φs with
  | nil => simp
  | cons φ φs ih => simp [and_iff_and, ih]

/-- Satisfaction at `there` does not depend on the atoms true at `here`. -/
theorem Satisfies.there_congr {H₁ H₂ T : Set Atom} {h₁ : H₁ ⊆ T} {h₂ : H₂ ⊆ T} :
    ⇓HT[⟨H₁, T, h₁⟩,.there ⊨ φ] ↔ ⇓HT[⟨H₂, T, h₂⟩,.there ⊨ φ] := by
  induction φ with
  | atom a => exact Iff.rfl
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ => exact or_congr ihφ ihψ
  | imp φ ψ ihφ ihψ => exact imp_congr ihφ ihψ

/-- For a total interpretation, the two worlds agree. This is the converse of persistence. -/
theorem Satisfies.total_here_iff_there {T : Set Atom} :
    ⇓HT[Interpretation.total T,.here ⊨ φ] ↔ ⇓HT[Interpretation.total T,.there ⊨ φ] := by
  refine ⟨there_of_here, fun h => ?_⟩
  induction φ with
  | atom a => exact h
  | and φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => exact h.imp ihφ ihψ
  | imp φ ψ ihφ ihψ =>
    exact ⟨fun hφ => ihψ (h (there_of_here (I := Interpretation.total T) (φ := φ) hφ)), h⟩

/-- Every interpretation that is not total distinguishes its two worlds by some proposition. -/
theorem exists_not_here_iff_there {I : Interpretation Atom} (h : I.here ⊂ I.there) :
    ∃ φ : Proposition Atom, ¬(⇓HT[I,.here ⊨ φ] ↔ ⇓HT[I,.there ⊨ φ]) := by
  obtain ⟨a, haT, haH⟩ := Set.exists_of_ssubset h
  refine ⟨.atom ↑a, fun hiff => haH ?_⟩
  simpa [Interpretation.atoms] using hiff.mpr (by simpa [Interpretation.atoms] using haT)

/-! ### Models, validity and consequence -/

/-- An interpretation is a model of a theory if it satisfies all of its propositions at `here`. -/
def Interpretation.IsModel (I : Interpretation Atom) (Γ : Theory Atom) : Prop :=
  ∀ φ ∈ Γ, ⇓HT[I,.here ⊨ φ]

/-- A proposition is valid if every interpretation satisfies it at `here`. -/
def Valid (φ : Proposition Atom) : Prop := ∀ I : Interpretation Atom, ⇓HT[I,.here ⊨ φ]

/-- A theory entails a proposition if every model of the theory satisfies it at `here`. -/
def Entails (Γ : Theory Atom) (φ : Proposition Atom) : Prop :=
  ∀ I : Interpretation Atom, I.IsModel Γ → ⇓HT[I,.here ⊨ φ]

/-- By persistence, a model satisfies its theory at both worlds. -/
theorem Interpretation.isModel_iff_forall_world {Γ : Theory Atom} :
    I.IsModel Γ ↔ ∀ w, ∀ φ ∈ Γ, ⇓HT[I,w ⊨ φ] := by
  refine ⟨fun h w φ hφ => ?_, fun h => h .here⟩
  cases w
  · exact h φ hφ
  · exact (h φ hφ).there_of_here

/-- Every interpretation is a model of the empty theory. -/
@[simp]
theorem Interpretation.isModel_empty : I.IsModel ∅ := fun _ h => h.elim

/-- Entailment in HT logic is monotonic, unlike equilibrium entailment. -/
theorem Entails.mono {Γ Δ : Theory Atom} (hΓ : Γ ⊆ Δ) (h : Entails Γ φ) : Entails Δ φ :=
  fun I hI => h I fun ψ hψ => hI ψ (hΓ hψ)

/-! ### HT logic is strictly between intuitionistic and classical logic -/

/-- The interpretation `⟨∅, {a}⟩`, which separates HT logic from classical logic
[Lifschitz2001]. -/
private def witness (a : Atom) : Interpretation Atom := ⟨∅, {a}, Set.empty_subset _⟩

private theorem not_here_witness (a : Atom) : ¬⇓HT[witness a,.here ⊨ .atom ↑a] := by
  simp [Interpretation.atoms, witness]

private theorem there_witness (a : Atom) : ⇓HT[witness a,.there ⊨ .atom ↑a] := by
  simp [Interpretation.atoms, witness]

/-- The weak law of excluded middle is valid. -/
theorem valid_not_or_not_not (φ : Proposition Atom) : Valid (¬φ ∨ ¬¬φ) := fun I => by
  rw [Satisfies.or_iff_or, Satisfies.not_here_iff, Satisfies.not_here_iff,
    Satisfies.not_there_iff]
  exact em _

/-- The law of excluded middle is not valid. -/
theorem not_valid_or_not (a : Atom) :
    ¬Valid (.atom ↑a ∨ ¬.atom ↑a : Proposition Atom) := fun h => by
  rcases h (witness a) with h | h
  · exact not_here_witness a h
  · exact Satisfies.not_here_iff.mp h (there_witness a)

/-- Double negation elimination is not valid. -/
theorem not_valid_not_not_imp (a : Atom) :
    ¬Valid (¬¬.atom ↑a → .atom ↑a : Proposition Atom) := fun h => by
  have hnn : ⇓HT[witness a,.here ⊨ ¬¬.atom ↑a] := by
    rw [Satisfies.not_here_iff, Satisfies.not_there_iff]
    exact not_not_intro (there_witness a)
  exact not_here_witness a ((h (witness a)).1 hnn)

/-- The law of excluded middle holds at `there`. -/
theorem Satisfies.or_not_there : ⇓HT[I,.there ⊨ φ ∨ ¬φ] := by
  rw [or_iff_or, not_there_iff]
  exact em _

/-- Double negation elimination holds at `there`. -/
theorem Satisfies.not_not_imp_there : ⇓HT[I,.there ⊨ ¬¬φ → φ] := by
  rw [imp_there_iff, not_there_iff, not_there_iff]
  exact not_not.mp

end Cslib.Logic.HT
