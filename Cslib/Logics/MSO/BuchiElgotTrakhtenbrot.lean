/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Logics.MSO.Atoms
public import Cslib.Logics.MSO.Expansion
public import Cslib.Logics.MSO.OfAutomaton

/-! # The Büchi-Elgot-Trakhtenbrot theorem

A language of finite words is recognizable by a finite automaton iff it is definable in monadic
second-order logic, and both conversions are effective. This is Theorem 3.1 of [Thomas1997],
whose proof is followed here. As a consequence, every formula of MSO[S] is equivalent over finite
words to a formula of EMSO[S], which is Corollary 3.2 of [Thomas1997].

## Main definitions and results

- `Formula₀.toDFA`, `Sentence.toDFA`: the effective translations of formulas into automata, correct
  by `Formula₀.language_toDFA` and `Sentence.language_toDFA`.
- `isRegular_iff_isDefinable`: the **Büchi-Elgot-Trakhtenbrot theorem**. The effective translation
  of automata into sentences is `Automata.EffectiveNA.toSentence`, see `holds_toSentence`.
- `Formula.toEMSO`, `exists_isEMSO_equiv`: Corollary 3.2.

## Overview of the proof

From automata to formulas, `Automata.EffectiveNA.toSentence` states the existence of a successful
run (`Cslib.Logics.MSO.OfAutomaton`). From formulas to automata, the proof proceeds in three steps:

1. A formula is translated into MSO₀, whose variables all range over sets
   (`Formula.toFormula₀`, `Cslib.Logics.MSO.MSO0`).
2. A formula of MSO₀ with `n` free variables defines a language over the alphabet `A × {0, 1}ⁿ`.
   By induction on the formula, this language is recognized by an automaton: the atomic formulas
   have explicit automata (`Cslib.Logics.MSO.Atoms`), the connectives correspond to complement,
   union and intersection, and the existential set quantifier to projection (`Formula₀.toDFA`).
3. For a sentence, `n` is `0`, so projecting away the empty tracks gives an automaton over `A`.

Corollary 3.2 composes both directions: the automaton for a formula is translated back into a
formula, which has the form of an EMSO formula. For formulas with free variables, the resulting
sentence over the track alphabet is turned into a formula over `A` by `Formula.ofTrackSentence`
(`Cslib.Logics.MSO.Expansion`).

## Implementation notes

The theorem numbers refer to the technical report version of [Thomas1997], Bericht 9607, Institut
für Informatik und Praktische Mathematik, Christian-Albrechts-Universität zu Kiel, May 1996.

In the proof that definable languages are recognizable, the translation produces deterministic
automata. It uses the subset construction for every existential set quantifier, which also yields
the closure under complement used in the reference.

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

/-- The translation of formulas of MSO₀ into automata over the track alphabet (second part of the
proof of Theorem 3.1 of [Thomas1997]). -/
def toDFA : {n : ℕ} → Formula₀ A n → EffectiveDFA (Track A n)
  -- The atomic formulas have their own automata.
  | _, .sub X Y => subDFA X Y
  | _, .sing X => singDFA X
  | _, .suc X Y => sucDFA X Y
  | _, .subLabel X a => subLabelDFA X a
  -- Negation: switch the accepting states.
  | _, .not φ => φ.toDFA.compl
  -- Disjunction: take the product with the union of the accepting conditions.
  | _, .or φ ψ => φ.toDFA.sup ψ.toDFA
  -- Conjunction: take the product with the intersection of the accepting conditions.
  | _, .and φ ψ => φ.toDFA.inf ψ.toDFA
  -- Existential set quantifier: guess the last track, and determinize by the subset construction.
  | _, .ex φ => φ.toDFA.proj trackInit

/-- The translation of formulas of MSO₀ into automata is correct. -/
theorem language_toDFA (φ : Formula₀ A n) : φ.toDFA.language = φ.language := by
  -- Induct on the formula.
  induction φ with
  -- The automaton for `X ⊆ Y` is correct.
  | sub X Y => exact language_subDFA X Y
  -- The automaton for `Sing(X)` is correct.
  | sing X => exact language_singDFA X
  -- The automaton for `Suc(X, Y)` is correct.
  | suc X Y => exact language_sucDFA X Y
  -- The automaton for `X ⊆ Q_a` is correct.
  | subLabel X a => exact language_subLabelDFA X a
  -- Negation:
  | not φ ih =>
    -- Apply the correctness of the complement and the induction hypothesis.
    rw [toDFA, EffectiveDFA.language_compl, ih]
    -- The language of `¬φ` is the complement of the language of `φ`.
    rfl
  -- Disjunction:
  | or φ ψ ihφ ihψ =>
    -- Compare on a word `w`.
    ext w
    -- Apply the correctness of the union and the induction hypotheses.
    rw [toDFA, EffectiveDFA.mem_language_sup, ihφ, ihψ]
    -- The language of `φ ∨ ψ` is the union of the languages.
    rfl
  -- Conjunction:
  | and φ ψ ihφ ihψ =>
    -- Compare on a word `w`.
    ext w
    -- Apply the correctness of the intersection and the induction hypotheses.
    rw [toDFA, EffectiveDFA.mem_language_inf, ihφ, ihψ]
    -- The language of `φ ∧ ψ` is the intersection of the languages.
    rfl
  -- Existential set quantifier: the projection of automata is the projection of languages.
  | ex φ ih => rw [toDFA, EffectiveDFA.language_proj, ih, language_ex]

end Formula₀

section Theorem

variable [FinEnum A]

/-- The effective translation of sentences into automata. -/
def Sentence.toDFA (φ : Sentence A) : EffectiveDFA A :=
  (Formula.toFormula₀ φ).toDFA.proj Prod.fst

/-- The effective translation of sentences into automata is correct. -/
theorem Sentence.language_toDFA (φ : Sentence A) : φ.toDFA.language = φ.language := by
  -- Forget the empty tracks; the sentence defines the projection of the language of its
  -- translation.
  rw [Sentence.toDFA, EffectiveDFA.language_proj, Formula₀.language_toDFA, Sentence.language_eq_map]

end Theorem

/-- **Büchi-Elgot-Trakhtenbrot theorem** (Theorem 3.1 of [Thomas1997]): a language of finite words
is recognizable by a finite automaton iff it is MSO[S]-definable. -/
theorem isRegular_iff_isDefinable [Finite A] {L : Language A} : L.IsRegular ↔ IsDefinable L := by
  -- Choose an enumeration of the finite alphabet, which is only needed for this proof.
  let _ := finEnumOfFinite A
  -- Show both directions.
  constructor
  -- Let `L` be regular.
  · intro h
    -- So `L` is recognized by a finite nondeterministic automaton.
    obtain ⟨State, _, na, rfl⟩ := Cslib.Language.IsRegular.iff_nfa.mp h
    -- Present this automaton effectively.
    let c := EffectiveNA.ofNA na.toNA na.accept
    -- Its sentence is a sentence of MSO[S]; it remains to show that it defines `L`.
    refine ⟨toSentence c, ltFree_toSentence c, ?_⟩
    -- Compare on a word `w`.
    ext w
    -- The sentence expresses the acceptance by the automaton.
    exact holds_toSentence
  -- Conversely, let `L` be defined by a sentence `φ`.
  · rintro ⟨φ, -, rfl⟩
    -- The automaton for `φ` shows that `L` is regular.
    exact Cslib.Language.IsRegular.iff_dfa.mpr
      -- Its state space is finite, and its language is the language of `φ`.
      ⟨_, inferInstance, φ.toDFA.da, φ.language_toDFA⟩

/-- The order relation does not add expressive power to the Büchi-Elgot-Trakhtenbrot theorem: a
language of finite words is recognizable by a finite automaton iff it is defined by a sentence
of MSO that can use the successor relation as well as the order relation. -/
theorem isRegular_iff_exists_language_eq [Finite A] {L : Language A} :
    L.IsRegular ↔ ∃ φ : Sentence A, φ.language = L :=
  -- Combine the theorem with the elimination of the order relation.
  isRegular_iff_isDefinable.trans isDefinable_iff_exists_sentence

namespace Formula

variable [FinEnum A]

/-- The automata normal form of a formula: an EMSO formula that expresses the existence of a
successful run of the automaton for the formula (Corollary 3.2 of [Thomas1997]). -/
def toEMSO (φ : Formula A k l) : Formula A k l :=
  ofTrackSentence (toSentence φ.toFormula₀.toDFA.toNA)

/-- The automata normal form is an EMSO formula. -/
theorem isEMSO_toEMSO (φ : Formula A k l) : φ.toEMSO.IsEMSO :=
  -- The sentence is an EMSO sentence, and the elimination of the tracks preserves this.
  isEMSO_elimTrack (isEMSO_toSentence _)

/-- The automata normal form is a formula of MSO[S]. -/
theorem ltFree_toEMSO (φ : Formula A k l) : φ.toEMSO.LtFree :=
  -- The sentence does not use the order relation, and the elimination of the tracks preserves this.
  ltFree_elimTrack (ltFree_toSentence _)

/-- A formula is equivalent over finite words to its automata normal form. -/
theorem satisfies_toEMSO (φ : Formula A k l) {w : List A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hv : ∀ x, v x ∈ (ofList w).dom) (hW : ∀ X, W X ⊆ (ofList w).dom) :
    Satisfies (ofList w) v W φ.toEMSO ↔ Satisfies (ofList w) v W φ := by
  -- The expansion of the model of `w` is the model of a word `w'` over the track alphabet.
  obtain ⟨w', -, hw'⟩ := ((ofList w).expand v W).exists_eq_ofList w.length (by simp)
  -- The normal form holds iff its sentence holds in the expansion, iff the automaton accepts `w'`.
  rw [toEMSO, satisfies_ofTrackSentence, hw', holds_toSentence, EffectiveDFA.language_toNA,
    -- This holds iff the translation into MSO₀ holds in the expansion, iff the formula holds.
    Formula₀.language_toDFA, Formula₀.mem_language, ← hw', models_toFormula₀_expand φ hv hW]

end Formula

/-- Corollary 3.2 of [Thomas1997] for sentences: any sentence of MSO is equivalent over finite words
to a sentence of EMSO[S]. -/
theorem exists_isEMSO_language_eq [Finite A] (φ : Sentence A) :
    ∃ ψ : Sentence A, ψ.IsEMSO ∧ ψ.LtFree ∧ ψ.language = φ.language := by
  -- Choose an enumeration of the finite alphabet, which is only needed for this proof.
  let _ := finEnumOfFinite A
  -- Use the automata normal form; it remains to compare the languages.
  refine ⟨φ.toEMSO, φ.isEMSO_toEMSO, φ.ltFree_toEMSO, ?_⟩
  -- Compare on a word `w`.
  ext w
  -- The normal form is equivalent on `w`, and there are no free variables to check.
  exact φ.satisfies_toEMSO (fun x ↦ x.elim0) (fun X ↦ X.elim0)

/-- Corollary 3.2 of [Thomas1997]: any formula of MSO[S] can be written as a formula of EMSO[S]. -/
theorem exists_isEMSO_equiv [Finite A] (φ : Formula A k l) :
    ∃ ψ : Formula A k l, ψ.IsEMSO ∧ ψ.LtFree ∧ ∀ (w : List A) (v : Fin k → ℕ) (W : Fin l → Set ℕ),
      (∀ x, v x ∈ (ofList w).dom) → (∀ X, W X ⊆ (ofList w).dom) →
        (Satisfies (ofList w) v W ψ ↔ Satisfies (ofList w) v W φ) := by
  -- Choose an enumeration of the finite alphabet, which is only needed for this proof.
  let _ := finEnumOfFinite A
  -- The automata normal form has all the required properties.
  exact ⟨φ.toEMSO, φ.isEMSO_toEMSO, φ.ltFree_toEMSO, fun _ _ _ hv hW ↦ φ.satisfies_toEMSO hv hW⟩

end Cslib.Logic.MSO
