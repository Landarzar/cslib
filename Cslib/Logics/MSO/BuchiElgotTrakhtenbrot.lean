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
  | _, .sub X Y => subDFA X Y
  | _, .sing X => singDFA X
  | _, .suc X Y => sucDFA X Y
  | _, .subLabel X a => subLabelDFA X a
  | _, .not φ => φ.toDFA.compl
  | _, .or φ ψ => φ.toDFA.sup ψ.toDFA
  | _, .and φ ψ => φ.toDFA.inf ψ.toDFA
  | _, .ex φ => φ.toDFA.proj trackInit

/-- The translation of formulas of MSO₀ into automata is correct. -/
theorem language_toDFA (φ : Formula₀ A n) : φ.toDFA.language = φ.language := by
  induction φ with
  | sub X Y => exact language_subDFA X Y
  | sing X => exact language_singDFA X
  | suc X Y => exact language_sucDFA X Y
  | subLabel X a => exact language_subLabelDFA X a
  | not φ ih =>
    rw [toDFA, EffectiveDFA.language_compl, ih]
    rfl
  | or φ ψ ihφ ihψ =>
    ext w
    rw [toDFA, EffectiveDFA.mem_language_sup, ihφ, ihψ]
    rfl
  | and φ ψ ihφ ihψ =>
    ext w
    rw [toDFA, EffectiveDFA.mem_language_inf, ihφ, ihψ]
    rfl
  | ex φ ih => rw [toDFA, EffectiveDFA.language_proj, ih, language_ex]

end Formula₀

section Theorem

variable [FinEnum A]

/-- The effective translation of sentences into automata. -/
def Sentence.toDFA (φ : Sentence A) : EffectiveDFA A :=
  (Formula.toFormula₀ φ).toDFA.proj Prod.fst

/-- The effective translation of sentences into automata is correct. -/
theorem Sentence.language_toDFA (φ : Sentence A) : φ.toDFA.language = φ.language := by
  rw [Sentence.toDFA, EffectiveDFA.language_proj, Formula₀.language_toDFA, Sentence.language_eq_map]

end Theorem

/-- **Büchi-Elgot-Trakhtenbrot theorem** (Theorem 3.1 of [Thomas1997]): a language of finite words
is recognizable by a finite automaton iff it is MSO[S]-definable. -/
theorem isRegular_iff_isDefinable [Finite A] {L : Language A} : L.IsRegular ↔ IsDefinable L := by
  let _ := finEnumOfFinite A
  constructor
  · intro h
    obtain ⟨State, _, na, rfl⟩ := Cslib.Language.IsRegular.iff_nfa.mp h
    let c := EffectiveNA.ofNA na.toNA na.accept
    refine ⟨toSentence c, ltFree_toSentence c, ?_⟩
    ext w
    exact holds_toSentence
  · rintro ⟨φ, -, rfl⟩
    exact Cslib.Language.IsRegular.iff_dfa.mpr
      ⟨_, inferInstance, φ.toDFA.da, φ.language_toDFA⟩

/-- The order relation does not add expressive power to the Büchi-Elgot-Trakhtenbrot theorem: a
language of finite words is recognizable by a finite automaton iff it is defined by a sentence
of MSO that can use the successor relation as well as the order relation. -/
theorem isRegular_iff_exists_language_eq [Finite A] {L : Language A} :
    L.IsRegular ↔ ∃ φ : Sentence A, φ.language = L :=
  isRegular_iff_isDefinable.trans isDefinable_iff_exists_sentence

namespace Formula

variable [FinEnum A]

/-- The automata normal form of a formula: an EMSO formula that expresses the existence of a
successful run of the automaton for the formula (Corollary 3.2 of [Thomas1997]). -/
def toEMSO (φ : Formula A k l) : Formula A k l :=
  ofTrackSentence (toSentence φ.toFormula₀.toDFA.toNA)

/-- The automata normal form is an EMSO formula. -/
theorem isEMSO_toEMSO (φ : Formula A k l) : φ.toEMSO.IsEMSO :=
  isEMSO_elimTrack (isEMSO_toSentence _)

/-- The automata normal form is a formula of MSO[S]. -/
theorem ltFree_toEMSO (φ : Formula A k l) : φ.toEMSO.LtFree :=
  ltFree_elimTrack (ltFree_toSentence _)

/-- A formula is equivalent over finite words to its automata normal form. -/
theorem satisfies_toEMSO (φ : Formula A k l) {w : List A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hv : ∀ x, v x ∈ (ofList w).dom) (hW : ∀ X, W X ⊆ (ofList w).dom) :
    Satisfies (ofList w) v W φ.toEMSO ↔ Satisfies (ofList w) v W φ := by
  obtain ⟨w', -, hw'⟩ := ((ofList w).expand v W).exists_eq_ofList w.length (by simp)
  rw [toEMSO, satisfies_ofTrackSentence, hw', holds_toSentence, EffectiveDFA.language_toNA,
    Formula₀.language_toDFA, Formula₀.mem_language, ← hw', models_toFormula₀_expand φ hv hW]

end Formula

/-- Corollary 3.2 of [Thomas1997] for sentences: any sentence of MSO is equivalent over finite words
to a sentence of EMSO[S]. -/
theorem exists_isEMSO_language_eq [Finite A] (φ : Sentence A) :
    ∃ ψ : Sentence A, ψ.IsEMSO ∧ ψ.LtFree ∧ ψ.language = φ.language := by
  let _ := finEnumOfFinite A
  refine ⟨φ.toEMSO, φ.isEMSO_toEMSO, φ.ltFree_toEMSO, ?_⟩
  ext w
  exact φ.satisfies_toEMSO (fun x ↦ x.elim0) (fun X ↦ X.elim0)

/-- Corollary 3.2 of [Thomas1997]: any formula of MSO[S] can be written as a formula of EMSO[S]. -/
theorem exists_isEMSO_equiv [Finite A] (φ : Formula A k l) :
    ∃ ψ : Formula A k l, ψ.IsEMSO ∧ ψ.LtFree ∧ ∀ (w : List A) (v : Fin k → ℕ) (W : Fin l → Set ℕ),
      (∀ x, v x ∈ (ofList w).dom) → (∀ X, W X ⊆ (ofList w).dom) →
        (Satisfies (ofList w) v W ψ ↔ Satisfies (ofList w) v W φ) := by
  let _ := finEnumOfFinite A
  exact ⟨φ.toEMSO, φ.isEMSO_toEMSO, φ.ltFree_toEMSO, fun _ _ _ hv hW ↦ φ.satisfies_toEMSO hv hW⟩

end Cslib.Logic.MSO
