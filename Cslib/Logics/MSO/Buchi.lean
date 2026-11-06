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

## Overview of the proof

The proof follows the one of the Büchi-Elgot-Trakhtenbrot theorem in
`Cslib.Logics.MSO.BuchiElgotTrakhtenbrot`. From automata to formulas, only the acceptance clause of
the sentence changes (`Automata.EffectiveNA.toωSentence`). From formulas to automata, the same
translation into MSO₀ and the same induction apply, with three differences:

- The automata are Büchi automata, which cannot be determinized in general, so the projection is
  done by nondeterminism (`Automata.EffectiveNA.proj`).
- The atomic formulas keep their deterministic automata: as Büchi automata, they recognize the
  ω-limit of their languages (`ωlanguage_eq_omegaLim_of_isAtom`).
- The complement is the hard step (`Automata.EffectiveNA.compl`).

Corollary 5.10 follows, because a sentence of S1S holds iff its automaton accepts the only ω-word
over a one-letter alphabet, and the nonemptiness of a Büchi automaton is decidable by searching for
a lasso (`Automata.EffectiveNA.isNonempty`).

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
  -- The atomic formulas use the deterministic automata for finite words.
  | _, .sub X Y => (subDFA X Y).toNA
  | _, .sing X => (singDFA X).toNA
  | _, .suc X Y => (sucDFA X Y).toNA
  | _, .subLabel X a => (subLabelDFA X a).toNA
  -- Negation: Büchi complementation.
  | _, .not φ => φ.toNA.compl
  -- Disjunction: the sum of the automata.
  | _, .or φ ψ => φ.toNA.sup ψ.toNA
  -- Conjunction: the intersection automaton.
  | _, .and φ ψ => φ.toNA.inf ψ.toNA
  -- Existential set quantifier: the automaton guesses the last track.
  | _, .ex φ => φ.toNA.proj trackInit

/-- The translation of formulas of MSO₀ into Büchi automata is correct. -/
theorem ωlanguage_toNA (φ : Formula₀ A n) : φ.toNA.ωlanguage = φ.ωlanguage := by
  -- Induct on the formula.
  induction φ with
  -- `X ⊆ Y`:
  | sub X Y =>
    -- The automaton recognizes the ω-limit of its language, which is the language of the atom.
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_subDFA,
      -- This ω-limit is the ω-language of the atom.
      ωlanguage_eq_omegaLim_of_isAtom (.sub X Y)]
  -- `Sing(X)`:
  | sing X =>
    -- The automaton recognizes the ω-limit of its language, which is the language of the atom.
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_singDFA,
      -- This ω-limit is the ω-language of the atom.
      ωlanguage_eq_omegaLim_of_isAtom (.sing X)]
  -- `Suc(X, Y)`:
  | suc X Y =>
    -- The automaton recognizes the ω-limit of its language, which is the language of the atom.
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_sucDFA,
      -- This ω-limit is the ω-language of the atom.
      ωlanguage_eq_omegaLim_of_isAtom (.suc X Y)]
  -- `X ⊆ Q_a`:
  | subLabel X a =>
    -- The automaton recognizes the ω-limit of its language, which is the language of the atom.
    rw [toNA, EffectiveDFA.ωlanguage_toNA, language_subLabelDFA,
      -- This ω-limit is the ω-language of the atom.
      ωlanguage_eq_omegaLim_of_isAtom (.subLabel X a)]
  -- Negation:
  | not φ ih =>
    -- Apply the correctness of the complement and the induction hypothesis.
    rw [toNA, ωlanguage_compl, ih]
    -- The ω-language of `¬φ` is the complement of the ω-language of `φ`.
    rfl
  -- Disjunction:
  | or φ ψ ihφ ihψ =>
    -- Apply the correctness of the union and the induction hypotheses.
    rw [toNA, ωlanguage_sup, ihφ, ihψ]
    -- The ω-language of `φ ∨ ψ` is the union of the ω-languages.
    rfl
  -- Conjunction:
  | and φ ψ ihφ ihψ =>
    -- Apply the correctness of the intersection and the induction hypotheses.
    rw [toNA, ωlanguage_inf, ihφ, ihψ]
    -- The ω-language of `φ ∧ ψ` is the intersection of the ω-languages.
    rfl
  -- Existential set quantifier: the projection of automata is the projection of ω-languages.
  | ex φ ih => rw [toNA, ωlanguage_proj, ih, ωlanguage_ex]

end Formula₀

section Theorem

variable [FinEnum A]

/-- The effective translation of sentences into Büchi automata. -/
def Sentence.toNA (φ : Sentence A) : EffectiveNA A :=
  (Formula.toFormula₀ φ).toNA.proj Prod.fst

/-- The effective translation of sentences into Büchi automata is correct. -/
theorem Sentence.ωlanguage_toNA (φ : Sentence A) : φ.toNA.ωlanguage = φ.ωlanguage := by
  -- Forget the empty tracks; the sentence defines the projection of the language of its
  -- translation.
  rw [Sentence.toNA, ωlanguage_proj, Formula₀.ωlanguage_toNA, Sentence.ωlanguage_eq_map]

end Theorem

/-- **Büchi's theorem** (Theorem 5.9 of [Thomas1997]): an ω-language is recognizable by a Büchi
automaton iff it is MSO[S]-definable. -/
theorem isRegular_iff_isωDefinable [Finite A] {p : ωLanguage A} : p.IsRegular ↔ IsωDefinable p := by
  -- Choose an enumeration of the finite alphabet, which is only needed for this proof.
  let _ := finEnumOfFinite A
  -- The order relation may be used in the sentence, as it can be eliminated.
  rw [isωDefinable_iff_exists_sentence]
  -- Show both directions.
  constructor
  -- Let `p` be recognized by a finite Büchi automaton.
  · rintro ⟨State, _, na, rfl⟩
    -- Present this automaton effectively.
    let c := EffectiveNA.ofNA na.toNA na.accept
    -- Its sentence defines `p`; compare on an ω-word `α`.
    refine ⟨toωSentence c, ωLanguage.mem_ext fun α ↦ ?_⟩
    -- The sentence expresses the acceptance by the automaton.
    exact holds_toωSentence
  -- Conversely, let `p` be defined by a sentence `φ`.
  · rintro ⟨φ, rfl⟩
    -- The automaton for `φ` is a finite Büchi automaton with the ω-language `p`.
    exact ⟨φ.toNA.State, inferInstance, φ.toNA.buchi, φ.ωlanguage_toNA⟩

/-- An ω-language is recognizable by a Büchi automaton iff it is defined by a sentence of MSO that
can use the successor relation as well as the order relation. -/
theorem isRegular_iff_exists_ωlanguage_eq [Finite A] {p : ωLanguage A} :
    p.IsRegular ↔ ∃ φ : Sentence A, φ.ωlanguage = p :=
  -- Combine the theorem with the elimination of the order relation.
  isRegular_iff_isωDefinable.trans isωDefinable_iff_exists_sentence

/-- A sentence is satisfiable over ω-words if it holds in the model of some ω-word. -/
def Sentence.IsSatisfiable (φ : Sentence A) : Prop := ∃ α : ωSequence A, φ.Holds (ofOmega α)

/-- The satisfiability of a sentence over ω-words is decided by the emptiness test for its Büchi
automaton. -/
theorem Sentence.isNonempty_toNA_iff [FinEnum A] {φ : Sentence A} :
    φ.toNA.isNonempty = true ↔ φ.IsSatisfiable := by
  -- The test decides whether the automaton accepts an ω-word, and the automaton is correct.
  rw [isNonempty_iff, Sentence.ωlanguage_toNA]
  -- This is the definition of satisfiability.
  rfl

/-- The satisfiability of a sentence over ω-words is decidable. -/
instance Sentence.decidablePredIsSatisfiable [FinEnum A] :
    DecidablePred (Sentence.IsSatisfiable (A := A)) :=
  -- Run the emptiness test of the automaton for the sentence.
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
  -- Show both directions.
  constructor
  -- The ω-word `word` is a witness.
  · exact fun h ↦ ⟨word, h⟩
  -- Conversely, let the sentence hold for an ω-word `α`.
  · rintro ⟨α, h⟩
    -- There is only one ω-word over the alphabet `Unit`, so `α` is `word`.
    rwa [show α = word from DFunLike.coe_injective rfl] at h

/-- Decide whether a sentence is true in `(ω, S, <)`, using the automaton for the sentence. -/
def decide (φ : Sentence Unit) : Bool := φ.toNA.isNonempty

/-- The decision procedure for S1S is correct. -/
theorem decide_eq_true_iff {φ : Sentence Unit} : decide φ = true ↔ Holds φ :=
  -- The emptiness test decides satisfiability, which is the same as truth in `(ω, S, <)`.
  Sentence.isNonempty_toNA_iff.trans holds_iff_isSatisfiable.symm

/-- **Corollary 5.10** of [Thomas1997]: the theory S1S of all sentences of monadic second-order
logic that are true in `(ω, S, <)` is decidable. -/
instance decidablePredHolds : DecidablePred Holds :=
  -- Run the decision procedure, which is correct.
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
  -- The sentence is an EMSO sentence, and the elimination of the tracks preserves this.
  isEMSO_elimTrack (isEMSO_toωSentence _)

/-- A formula is equivalent over ω-words to its automata normal form. -/
theorem satisfies_toωEMSO (φ : Formula A k l) {α : ωSequence A} {v : Fin k → ℕ}
    {W : Fin l → Set ℕ} :
    Satisfies (ofOmega α) v W φ.toωEMSO ↔ Satisfies (ofOmega α) v W φ := by
  -- The expansion has full domain, so it is the model of an ω-word `α'`.
  obtain ⟨α', hα'⟩ := ((ofOmega α).expand v W).exists_eq_ofOmega (by simp)
  -- The normal form holds iff its sentence holds in the expansion, iff the automaton accepts `α'`.
  rw [toωEMSO, satisfies_ofTrackSentence, hα', holds_toωSentence, Formula₀.ωlanguage_toNA,
    -- The ω-word `α'` has the expansion as its model.
    Formula₀.mem_ωlanguage, ← hα',
    -- The translation into MSO₀ holds in the expansion iff the formula holds.
    models_toFormula₀_expand φ (fun _ ↦ mem_dom_ofOmega) (fun _ _ _ ↦ mem_dom_ofOmega)]

end Formula

/-- Any formula of MSO is equivalent over ω-words to an EMSO formula that uses the successor and
the order relation (as remarked after Corollary 5.10 of [Thomas1997]). -/
theorem exists_isEMSO_ωequiv [Finite A] (φ : Formula A k l) :
    ∃ ψ : Formula A k l, ψ.IsEMSO ∧ ∀ (α : ωSequence A) (v : Fin k → ℕ) (W : Fin l → Set ℕ),
      Satisfies (ofOmega α) v W ψ ↔ Satisfies (ofOmega α) v W φ := by
  -- Choose an enumeration of the finite alphabet, which is only needed for this proof.
  let _ := finEnumOfFinite A
  -- The automata normal form has all the required properties.
  exact ⟨φ.toωEMSO, φ.isEMSO_toωEMSO, fun _ _ _ ↦ φ.satisfies_toωEMSO⟩

end Cslib.Logic.MSO
