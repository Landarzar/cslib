/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.Effective.Complement
public import Cslib.Computability.Languages.OmegaRegularLanguage
public import Cslib.Logics.MSO.Atoms
public import Cslib.Logics.MSO.Expansion
public import Cslib.Logics.MSO.OfAutomaton

/-! # Büchi's theorem

An ω-language is recognizable by a Büchi automaton iff it is definable in monadic second-order
logic, and the transformations of Büchi automata into formulas and conversely are effective. This is
Theorem 5.9 of [Thomas1997]. As a consequence, the theory S1S of all sentences that are true in
`(ω, S, <)` is decidable, which is Corollary 5.10 of [Thomas1997].

## Main definitions and results

- `Formula₀.toNA`, `Sentence.toNA`: the effective translations of formulas into Büchi automata,
  correct by `Formula₀.ωlanguage_toNA` and `Sentence.ωlanguage_toNA`.
- `isRegular_iff_isωDefinable`: **Büchi's theorem**. The effective translation of Büchi automata
  into sentences is `Automata.EffectiveNA.toωSentence`, see `holds_toωSentence`.
- `Sentence.IsSatisfiable`: the satisfiability of a sentence over ω-words, which is decidable.
- `S1S.Holds`: the truth of a sentence of S1S in `(ω, S, <)`, which is decidable by the instance
  `S1S.decidablePredHolds`. This is **Corollary 5.10**.
- `Formula.toωEMSO`, `exists_isEMSO_ωequiv`: every formula is equivalent over ω-words to an EMSO
  formula that uses the successor and the order relation, as remarked after Corollary 5.10.

## Implementation notes

The proof of the reference uses McNaughton's theorem for the complementation step, while we use
Büchi's original complementation by `Automata.EffectiveNA.compl`, since McNaughton's theorem is not
available in CSLib.

Decidability is formulated as an instance of `DecidablePred` that is computable: it is compiled to
an executable decision procedure, and it does not depend on classical choice for its computational
content. The procedure has nonelementary complexity, so it can only be run on tiny sentences.

The theorem numbers refer to the technical report version of [Thomas1997], Bericht 9607, Institut
für Informatik und Praktische Mathematik, Christian-Albrechts-Universität zu Kiel, May 1996.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open Automata WordModel Automata.EffectiveNA

universe u

variable {A : Type u} {k l n : ℕ}

namespace Formula₀

variable [FinEnum A]

/-- The translation of formulas of MSO₀ into Büchi automata over the track alphabet (second part of
the proof of Theorem 5.9 of [Thomas1997]). -/
def toNA : {n : ℕ} → Formula₀ A n → EffectiveNA (Track A n)
  | _, .sub X Y => (subDFA X Y).toNA
  | _, .sing X => (singDFA X).toNA
  | _, .suc X Y => (sucDFA X Y).toNA
  | _, .subLabel X a => (subLabelDFA X a).toNA
  | _, .not φ => φ.toNA.compl
  | _, .or φ ψ => φ.toNA.sup ψ.toNA
  | _, .and φ ψ => φ.toNA.inf ψ.toNA
  | _, .ex φ => φ.toNA.proj trackInit

/-- The translation of formulas of MSO₀ into Büchi automata is correct. -/
theorem ωlanguage_toNA (φ : Formula₀ A n) : φ.toNA.ωlanguage = φ.ωlanguage := by
  induction φ with
  | sub X Y =>
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_subDFA,
      ωlanguage_eq_omegaLim_of_isAtom (.sub X Y)]
  | sing X =>
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_singDFA,
      ωlanguage_eq_omegaLim_of_isAtom (.sing X)]
  | suc X Y =>
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_sucDFA,
      ωlanguage_eq_omegaLim_of_isAtom (.suc X Y)]
  | subLabel X a =>
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_subLabelDFA,
      ωlanguage_eq_omegaLim_of_isAtom (.subLabel X a)]
  | not φ ih =>
    rw [toNA, ωlanguage_compl, ih]
    rfl
  | or φ ψ ihφ ihψ =>
    rw [toNA, ωlanguage_sup, ihφ, ihψ]
    rfl
  | and φ ψ ihφ ihψ =>
    rw [toNA, ωlanguage_inf, ihφ, ihψ]
    rfl
  | ex φ ih => rw [toNA, ωlanguage_proj, ih, ωlanguage_ex]

end Formula₀

section Theorem

variable [FinEnum A]

/-- The effective translation of sentences into Büchi automata. -/
def Sentence.toNA (φ : Sentence A) : EffectiveNA A :=
  (Formula.toFormula₀ φ).toNA.proj Prod.fst

/-- The effective translation of sentences into Büchi automata is correct. -/
theorem Sentence.ωlanguage_toNA (φ : Sentence A) : φ.toNA.ωlanguage = φ.ωlanguage := by
  rw [Sentence.toNA, ωlanguage_proj, Formula₀.ωlanguage_toNA, Sentence.ωlanguage_eq_map]

end Theorem

/-- **Büchi's theorem** (Theorem 5.9 of [Thomas1997]): an ω-language is recognizable by a Büchi
automaton iff it is MSO[S]-definable. -/
theorem isRegular_iff_isωDefinable [Finite A] {p : ωLanguage A} : p.IsRegular ↔ IsωDefinable p := by
  let _ := finEnumOfFinite A
  rw [isωDefinable_iff_exists_sentence]
  constructor
  · rintro ⟨State, _, na, rfl⟩
    let c := EffectiveNA.ofNA na.toNA na.accept
    refine ⟨toωSentence c, ωLanguage.mem_ext fun α ↦ ?_⟩
    exact holds_toωSentence
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.toNA.State, inferInstance, φ.toNA.buchi, φ.ωlanguage_toNA⟩

/-- An ω-language is recognizable by a Büchi automaton iff it is defined by a sentence of MSO that
can use the successor relation as well as the order relation. -/
theorem isRegular_iff_exists_ωlanguage_eq [Finite A] {p : ωLanguage A} :
    p.IsRegular ↔ ∃ φ : Sentence A, φ.ωlanguage = p :=
  isRegular_iff_isωDefinable.trans isωDefinable_iff_exists_sentence

/-- A sentence is satisfiable over ω-words if it holds in the model of some ω-word. -/
def Sentence.IsSatisfiable (φ : Sentence A) : Prop := ∃ α : ωSequence A, φ.Holds (ofOmega α)

/-- The satisfiability of a sentence over ω-words is decided by the emptiness test for its Büchi
automaton. -/
theorem Sentence.isNonempty_toNA_iff [FinEnum A] {φ : Sentence A} :
    φ.toNA.isNonempty = true ↔ φ.IsSatisfiable := by
  rw [isNonempty_iff, Sentence.ωlanguage_toNA]
  rfl

/-- The satisfiability of a sentence over ω-words is decidable. -/
instance Sentence.decidablePredIsSatisfiable [FinEnum A] :
    DecidablePred (Sentence.IsSatisfiable (A := A)) :=
  fun φ ↦ decidable_of_iff (φ.toNA.isNonempty = true) Sentence.isNonempty_toNA_iff

/-! ### The theory S1S

The sentences of monadic second-order logic without letter predicates are represented by the
sentences over a one-letter alphabet, whose letter predicate is trivially true in `(ω, S, <)`. -/

namespace S1S

/-- The ω-word that represents the structure `(ω, S, <)`. -/
def word : ωSequence Unit := ωSequence.const ()

/-- The truth of a sentence in the structure `(ω, S, <)`. -/
def Holds (φ : Sentence Unit) : Prop := φ.Holds (ofOmega word)

/-- A sentence is true in `(ω, S, <)` iff it is satisfiable, as there is only one ω-word over a
one-letter alphabet. -/
theorem holds_iff_isSatisfiable {φ : Sentence Unit} : Holds φ ↔ φ.IsSatisfiable := by
  constructor
  · exact fun h ↦ ⟨word, h⟩
  · rintro ⟨α, h⟩
    rwa [show α = word from DFunLike.coe_injective rfl] at h

/-- Decide whether a sentence is true in `(ω, S, <)`, using the automaton for the sentence. -/
def decide (φ : Sentence Unit) : Bool := φ.toNA.isNonempty

/-- The decision procedure for S1S is correct. -/
theorem decide_eq_true_iff {φ : Sentence Unit} : decide φ = true ↔ Holds φ :=
  Sentence.isNonempty_toNA_iff.trans holds_iff_isSatisfiable.symm

/-- **Corollary 5.10** of [Thomas1997]: the theory S1S of all sentences of monadic second-order
logic that are true in `(ω, S, <)` is decidable. -/
instance decidablePredHolds : DecidablePred Holds :=
  fun φ ↦ decidable_of_iff (decide φ = true) decide_eq_true_iff

end S1S

namespace Formula

variable [FinEnum A]

/-- The automata normal form of a formula over ω-words: an EMSO formula that expresses the existence
of a successful run of the Büchi automaton for the formula, as remarked after Corollary 5.10 of
[Thomas1997]. -/
def toωEMSO (φ : Formula A k l) : Formula A k l :=
  ofTrackSentence (toωSentence φ.toFormula₀.toNA)

/-- The automata normal form over ω-words is an EMSO formula. -/
theorem isEMSO_toωEMSO (φ : Formula A k l) : φ.toωEMSO.IsEMSO :=
  isEMSO_elimTrack (isEMSO_toωSentence _)

/-- A formula is equivalent over ω-words to its automata normal form. -/
theorem satisfies_toωEMSO (φ : Formula A k l) {α : ωSequence A} {v : Fin k → ℕ}
    {W : Fin l → Set ℕ} :
    Satisfies (ofOmega α) v W φ.toωEMSO ↔ Satisfies (ofOmega α) v W φ := by
  obtain ⟨α', hα'⟩ := ((ofOmega α).expand v W).exists_eq_ofOmega (by simp)
  rw [toωEMSO, satisfies_ofTrackSentence, hα', holds_toωSentence, Formula₀.ωlanguage_toNA,
    Formula₀.mem_ωlanguage, ← hα',
    models_toFormula₀_expand φ (fun _ ↦ mem_dom_ofOmega) (fun _ _ _ ↦ mem_dom_ofOmega)]

end Formula

/-- Any formula of MSO is equivalent over ω-words to an EMSO formula that uses the successor and
the order relation (as remarked after Corollary 5.10 of [Thomas1997]). -/
theorem exists_isEMSO_ωequiv [Finite A] (φ : Formula A k l) :
    ∃ ψ : Formula A k l, ψ.IsEMSO ∧ ∀ (α : ωSequence A) (v : Fin k → ℕ) (W : Fin l → Set ℕ),
      Satisfies (ofOmega α) v W ψ ↔ Satisfies (ofOmega α) v W φ := by
  let _ := finEnumOfFinite A
  exact ⟨φ.toωEMSO, φ.isEMSO_toωEMSO, fun _ _ _ ↦ φ.satisfies_toωEMSO⟩

end Cslib.Logic.MSO
