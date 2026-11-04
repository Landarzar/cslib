/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

import Cslib.Logics.MSO.Buchi
import Cslib.Logics.MSO.BuchiElgotTrakhtenbrot

/-! # Tests for monadic second-order logic and its decision procedures

The tests run the executable translations between formulas and automata, which validates the
semantics and the translations on concrete formulas.
-/

set_option linter.hashCommand false

namespace CslibTests.MSO

open Cslib.Automata Cslib.Logic.MSO Cslib.Logic.MSO.Formula

/-! ## From sentences to automata on finite words -/

/-- `∃x Q_true(x)`: some letter is `true`. -/
def someTrue : Sentence Bool := .ex₁ (.label true 0)

#guard decide ([false, true] ∈ someTrue.toDFA.language)
#guard !decide ([false, false] ∈ someTrue.toDFA.language)
#guard !decide ([] ∈ someTrue.toDFA.language)

/-- `∀x Q_true(x)`: all letters are `true`. In particular, this holds for the empty word. -/
def allTrue : Sentence Bool := all₁ (.label true 0)

#guard decide ([true, true] ∈ allTrue.toDFA.language)
#guard !decide ([true, false] ∈ allTrue.toDFA.language)
#guard decide ([] ∈ allTrue.toDFA.language)

/-- `∃x ∃y (S(x, y) ∧ Q_true(x) ∧ Q_false(y))`: `true` is directly followed by `false`. -/
def trueThenFalse : Sentence Bool :=
  .ex₁ (.ex₁ (.not (.or (.not (.succ 0 1)) (.not (.not (.or (.not (.label true 0))
    (.not (.label false 1))))))))

#guard decide ([false, true, false] ∈ trueThenFalse.toDFA.language)
#guard !decide ([false, false, true] ∈ trueThenFalse.toDFA.language)
#guard !decide ([true, true, false, false].reverse ∈ trueThenFalse.toDFA.language)

/-- `∃x ∃y (x < y ∧ Q_true(x) ∧ Q_false(y))`, where the order is eliminated by a set quantifier. -/
def trueBeforeFalse : Sentence Bool :=
  .ex₁ (.ex₁ (.not (.or (.not (.lt 0 1)) (.not (.not (.or (.not (.label true 0))
    (.not (.label false 1))))))))

#guard decide ([true, false] ∈ trueBeforeFalse.toDFA.language)
#guard !decide ([false, true] ∈ trueBeforeFalse.toDFA.language)

/-! ## From automata to sentences on finite words -/

/-- A nondeterministic automaton accepting the words whose last letter is `true`. -/
def lastTrue : EffectiveNA Bool where
  State := Bool
  toNA := { Tr := fun s x t ↦ s = false ∧ (t = true → x = true), start := {false} }
  accept := {true}
  decTr s x t := inferInstanceAs (Decidable (s = false ∧ (t = true → x = true)))
  decStart s := inferInstanceAs (Decidable (s = false))
  decAccept s := inferInstanceAs (Decidable (s = true))

/-- Translating this automaton into a sentence and back preserves its behaviour. -/
def lastTrueRoundTrip : EffectiveDFA Bool := (EffectiveNA.toSentence lastTrue).toDFA

#guard decide ([false, true] ∈ lastTrueRoundTrip.language)
#guard !decide ([true, false] ∈ lastTrueRoundTrip.language)
#guard !decide ([] ∈ lastTrueRoundTrip.language)

/-! ## Büchi automata -/

/-- A Büchi automaton accepting exactly the ω-word that is constantly `true`. -/
def onlyTrue : EffectiveNA Bool where
  State := Unit
  toNA := { Tr := fun _ x _ ↦ x = true, start := Set.univ }
  accept := Set.univ
  decTr _ x _ := inferInstanceAs (Decidable (x = true))
  decStart _ := isTrue trivial
  decAccept _ := isTrue trivial

/-- A Büchi automaton accepting all ω-words. -/
def everything : EffectiveNA Bool where
  State := Unit
  toNA := { Tr := fun _ _ _ ↦ True, start := Set.univ }
  accept := Set.univ
  decTr _ _ _ := isTrue trivial
  decStart _ := isTrue trivial
  decAccept _ := isTrue trivial

#guard onlyTrue.isNonempty
#guard onlyTrue.compl.isNonempty
#guard everything.isNonempty
#guard !everything.compl.isNonempty

/-! ## The theory S1S -/

/-- A true sentence of S1S: `∃x x = x`. -/
def nonemptyDomain : Sentence Unit := .ex₁ (.eq 0 0)

/-- A false sentence of S1S: `∃x S(x, x)`. -/
def selfSuccessor : Sentence Unit := .ex₁ (.succ 0 0)

/-- A true sentence of S1S: `∃X ∃x X(x)`. -/
def nonemptySet : Sentence Unit := .ex₂ (.ex₁ (.mem 0 0))

/-- A true sentence of S1S: `∃x ∃y S(x, y)`. -/
def someSuccessor : Sentence Unit := .ex₁ (.ex₁ (.succ 0 1))

#guard S1S.decide nonemptyDomain
#guard !S1S.decide selfSuccessor
#guard S1S.decide nonemptySet
#guard S1S.decide someSuccessor

-- The instance of `DecidablePred S1S.Holds` is executable.
#guard decide (S1S.Holds nonemptyDomain)
#guard !decide (S1S.Holds selfSuccessor)

-- The satisfiability of a sentence with letter predicates is decidable as well.
#guard decide someTrue.IsSatisfiable

/-! ## The main theorems -/

example {A : Type} [Finite A] {L : Language A} : L.IsRegular ↔ IsDefinable L :=
  isRegular_iff_isDefinable

example {A : Type} [Finite A] {p : Cslib.ωLanguage A} : p.IsRegular ↔ IsωDefinable p :=
  isRegular_iff_isωDefinable

example {A : Type} [Finite A] (φ : Formula A 1 2) :
    ∃ ψ : Formula A 1 2, ψ.IsEMSO ∧ ψ.LtFree ∧ ∀ (w : List A) (v : Fin 1 → ℕ) (W : Fin 2 → Set ℕ),
      (∀ x, v x ∈ (WordModel.ofList w).dom) → (∀ X, W X ⊆ (WordModel.ofList w).dom) →
        (Satisfies (WordModel.ofList w) v W ψ ↔ Satisfies (WordModel.ofList w) v W φ) :=
  exists_isEMSO_equiv φ

example : DecidablePred S1S.Holds := inferInstance

end CslibTests.MSO
