/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Languages.OmegaLanguage
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Monadic second-order logic over words

This file introduces monadic second-order logic (MSO) over word models, following Sections 2.1-2.3
of [W. Thomas, *Languages, Automata, and Logic*][Thomas1997].

## Main definitions

- `WordModel`: the relational structure of a finite word or of an ω-word.
- `Formula`: MSO formulas, whose free first- and second-order variables are given by de Bruijn
  levels, so that a quantifier always binds the last variable of its context.
- `Satisfies`: the satisfaction relation, also available as the judgement `MSO[M, v, W ⊨ φ]`.
- `Formula.LtFree`, `Formula.IsFirstOrder`, `Formula.IsEMSO`: the fragments MSO[S], FO and EMSO.
- `Sentence.language`, `Sentence.ωlanguage`: the languages defined by a sentence.
- `IsDefinable`, `IsωDefinable`: MSO[S]-definability of languages and ω-languages.
- `Formula.elimLt`: elimination of the order relation in favour of the successor relation.

## Implementation notes

- Positions of word models are natural numbers. A word model labels exactly the positions of its
  domain, which is an initial segment of `ℕ`. This treats finite words and ω-words uniformly.
- Only `¬`, `∨` and the existential quantifiers are primitive. The other connectives and the
  universal quantifiers are derived, and `⊥` is defined as `∃x ¬(x = x)`.
- Since the empty word is admitted, the domain of a word model can be empty. As in the reference,
  universal sentences then hold and existential sentences do not.
- A formula in `Formula A k l` can refer to the first-order variables `0, …, k - 1` and to the
  second-order variables `0, …, l - 1`, and a quantifier binds the variable with the largest index.
  For example, `∃x ∃y S(x, y)` is `.ex₁ (.ex₁ (.succ 0 1))`, where `0` is bound by the outer and `1`
  by the inner quantifier. An interpretation of the free variables is extended with `Fin.snoc`.
- The semantics is defined for all interpretations of the free variables, but it only corresponds to
  the reference for positions and subsets of the domain. Statements about the equivalence of
  formulas are therefore restricted to such interpretations.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open scoped InferenceSystem

universe u

variable {A : Type u} {B : Type*} {k l : ℕ}

/-- The word model of a finite word or an ω-word: the positions of the domain carry a label, and
the domain is an initial segment of `ℕ`. The successor relation and the order are those of `ℕ`. -/
@[ext]
structure WordModel (A : Type u) where
  /-- The label of a position, or `none` if the position does not belong to the domain. -/
  label : ℕ → Option A
  /-- The domain of a word model is an initial segment of `ℕ`. -/
  isSome_of_le {i j : ℕ} (hij : i ≤ j) (hj : (label j).isSome) : (label i).isSome

namespace WordModel

/-- The domain of a word model. -/
def dom (M : WordModel A) : Set ℕ := {i | (M.label i).isSome}

/-- Membership in the domain means that the position carries a label. -/
@[scoped grind =]
theorem mem_dom {M : WordModel A} {i : ℕ} : i ∈ M.dom ↔ (M.label i).isSome :=
  -- Holds by unfolding the definition of `dom`.
  Iff.rfl

/-- The domain is downward closed: each position below a position of the domain belongs to it. -/
theorem mem_dom_of_le {M : WordModel A} {i j : ℕ} (hij : i ≤ j) (hj : j ∈ M.dom) : i ∈ M.dom :=
  -- This is the initial-segment property of word models.
  M.isSome_of_le hij hj

/-- The word model of a finite word. -/
def ofList (w : List A) : WordModel A where
  label i := w[i]?
  isSome_of_le {i j} hij hj := by
    -- A position of a list exists iff it is below the length of the list.
    simp only [isSome_getElem?] at hj ⊢
    -- So `j < length` and `i ≤ j` give `i < length`.
    exact lt_of_le_of_lt hij hj

/-- The word model of an ω-word. -/
def ofOmega (α : ωSequence A) : WordModel A where
  label i := some (α i)
  -- Every position of an ω-word carries a label, so there is nothing to show.
  isSome_of_le _ _ := rfl

/-- The labels of the model of a finite word are read off the list. -/
@[simp, scoped grind =]
theorem ofList_label (w : List A) (i : ℕ) : (ofList w).label i = w[i]? :=
  -- Holds by definition of `ofList`.
  rfl

/-- The labels of the model of an ω-word are read off the sequence. -/
@[simp, scoped grind =]
theorem ofOmega_label (α : ωSequence A) (i : ℕ) : (ofOmega α).label i = some (α i) :=
  -- Holds by definition of `ofOmega`.
  rfl

/-- The domain of the model of a finite word consists of the positions below its length. -/
@[simp, scoped grind =]
theorem mem_dom_ofList {w : List A} {i : ℕ} : i ∈ (ofList w).dom ↔ i < w.length := by
  -- Unfold `dom`; then `isSome` of a list lookup is the bound on the position.
  simp [dom]

/-- Every position belongs to the domain of the model of an ω-word. -/
@[scoped grind .]
theorem mem_dom_ofOmega {α : ωSequence A} {i : ℕ} : i ∈ (ofOmega α).dom :=
  -- The label of a position of an ω-word is `some _`, so `isSome` computes to `true`.
  rfl

/-- The domain of the model of an ω-word is all of `ℕ`. -/
@[simp]
theorem dom_ofOmega (α : ωSequence A) : (ofOmega α).dom = Set.univ :=
  -- Every position is a member by `mem_dom_ofOmega`.
  Set.eq_univ_of_forall fun _ ↦ mem_dom_ofOmega

/-- Relabel the positions of a word model. -/
def map (f : A → B) (M : WordModel A) : WordModel B where
  label i := (M.label i).map f
  isSome_of_le hij hj := by
    -- Relabelling does not change whether a position carries a label.
    simp only [Option.isSome_map] at hj ⊢
    -- So the initial-segment property is inherited from `M`.
    exact M.isSome_of_le hij hj

/-- The labels of a relabelled word model are the relabelled labels. -/
@[simp, scoped grind =]
theorem map_label (f : A → B) (M : WordModel A) (i : ℕ) :
    (M.map f).label i = (M.label i).map f :=
  -- Holds by definition of `map`.
  rfl

/-- Relabelling does not change the domain. -/
@[simp, scoped grind =]
theorem dom_map (f : A → B) (M : WordModel A) : (M.map f).dom = M.dom := by
  -- Compare both domains position by position.
  ext i
  -- `Option.map` preserves `isSome`.
  simp [dom]

/-- Relabelling the model of a finite word gives the model of the mapped word. -/
@[simp]
theorem map_ofList (f : A → B) (w : List A) : (ofList w).map f = ofList (w.map f) := by
  -- Word models are equal iff their label functions are equal.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- A lookup in a mapped list is the mapped lookup.
  simp

/-- Relabelling the model of an ω-word gives the model of the mapped sequence. -/
@[simp]
theorem map_ofOmega (f : A → B) (α : ωSequence A) : (ofOmega α).map f = ofOmega (α.map f) :=
  -- Both label functions unfold to `fun i ↦ some (f (α i))`.
  rfl

/-- Different finite words have different models. -/
theorem ofList_injective : Function.Injective (ofList (A := A)) := by
  -- Take two words with the same model.
  intro w w' h
  -- Lists are equal if all their optional lookups agree.
  apply List.ext_getElem?
  -- Fix a position `i`.
  intro i
  -- The lookups are the labels of the models, which agree by `h`.
  exact congrFun (congrArg label h) i

/-- Different ω-words have different models. -/
theorem ofOmega_injective : Function.Injective (ofOmega (A := A)) := by
  -- Take two ω-words with the same model.
  intro α β h
  -- Compare the sequences at an arbitrary position `i`.
  ext i
  -- The labels `some (α i)` and `some (β i)` agree by `h`, and `some` is injective.
  exact Option.some.inj (congrFun (congrArg label h) i)

/-- A word model with the domain of a finite word is the model of a finite word. -/
theorem exists_eq_ofList (M : WordModel A) (n : ℕ) (hM : ∀ i, i ∈ M.dom ↔ i < n) :
    ∃ w : List A, w.length = n ∧ M = ofList w := by
  -- Read the labels of `M`, which are defined below `n` by `hM`, into a list of length `n`.
  refine ⟨List.ofFn fun i : Fin n ↦ (M.label i).get ((hM i).mpr i.isLt), by simp, ?_⟩
  -- It remains to show that `M` is the model of this list: compare the label functions.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- Distinguish whether `i` belongs to the domain.
  by_cases hi : i < n
  -- Below `n`, the list contains the value of the label by construction.
  · simpa [hi] using (Option.some_get ((hM i).mpr hi)).symm
  -- Otherwise, `M` has no label at `i` by `hM`.
  · have : M.label i = none := Option.not_isSome_iff_eq_none.mp fun h ↦ hi ((hM i).mp h)
    -- The lookup in the list is out of bounds as well, so both sides are `none`.
    simp [hi, this]

/-- A word model with full domain is the model of an ω-word. -/
theorem exists_eq_ofOmega (M : WordModel A) (hM : ∀ i, i ∈ M.dom) :
    ∃ α : ωSequence A, M = ofOmega α := by
  -- Read the labels of `M`, which are all defined, into a sequence.
  refine ⟨fun i ↦ (M.label i).get (hM i), ?_⟩
  -- It remains to compare the label functions.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- Both sides are the defined value of the label.
  exact (Option.some_get (hM i)).symm

end WordModel

open WordModel

/-- Formulas of monadic second-order logic over the alphabet `A`, with `k` free first-order and
`l` free second-order variables. A quantifier binds the last variable of its context. -/
inductive Formula (A : Type u) : ℕ → ℕ → Type u where
  /-- `x = y` -/
  | eq {k l : ℕ} (x y : Fin k) : Formula A k l
  /-- `S(x, y)`: position `y` is the successor of position `x`. -/
  | succ {k l : ℕ} (x y : Fin k) : Formula A k l
  /-- `x < y` -/
  | lt {k l : ℕ} (x y : Fin k) : Formula A k l
  /-- `Q_a(x)`: position `x` carries the letter `a`. -/
  | label {k l : ℕ} (a : A) (x : Fin k) : Formula A k l
  /-- `X(x)`: position `x` belongs to the set `X`. -/
  | mem {k l : ℕ} (x : Fin k) (X : Fin l) : Formula A k l
  /-- Negation. -/
  | not {k l : ℕ} (φ : Formula A k l) : Formula A k l
  /-- Disjunction. -/
  | or {k l : ℕ} (φ ψ : Formula A k l) : Formula A k l
  /-- First-order existential quantification. -/
  | ex₁ {k l : ℕ} (φ : Formula A (k + 1) l) : Formula A k l
  /-- Second-order existential quantification. -/
  | ex₂ {k l : ℕ} (φ : Formula A k (l + 1)) : Formula A k l

/-- Satisfaction. `Satisfies M v W φ` means that `φ` holds in the word model `M` when its free
first-order variables are interpreted by `v` and its free second-order variables by `W`. -/
def Satisfies (M : WordModel A) : {k l : ℕ} → (Fin k → ℕ) → (Fin l → Set ℕ) → Formula A k l → Prop
  | _, _, v, _, .eq x y => v x = v y
  | _, _, v, _, .succ x y => v y = v x + 1
  | _, _, v, _, .lt x y => v x < v y
  | _, _, v, _, .label a x => M.label (v x) = some a
  | _, _, v, W, .mem x X => v x ∈ W X
  | _, _, v, W, .not φ => ¬Satisfies M v W φ
  | _, _, v, W, .or φ ψ => Satisfies M v W φ ∨ Satisfies M v W ψ
  -- A first-order quantifier ranges over the domain; the new variable comes last.
  | _, _, v, W, .ex₁ φ => ∃ p ∈ M.dom, Satisfies M (Fin.snoc (α := fun _ ↦ ℕ) v p) W φ
  -- A second-order quantifier ranges over the subsets of the domain; the new variable comes last.
  | _, _, v, W, .ex₂ φ => ∃ P ⊆ M.dom, Satisfies M v (Fin.snoc (α := fun _ ↦ Set ℕ) W P) φ

/-- A judgement of monadic second-order logic. -/
structure Judgement (A : Type u) where
  /-- Constructs a judgement. -/
  mk ::
  /-- The number of free first-order variables. -/
  {k : ℕ}
  /-- The number of free second-order variables. -/
  {l : ℕ}
  /-- The word model. -/
  M : WordModel A
  /-- The interpretation of the free first-order variables. -/
  v : Fin k → ℕ
  /-- The interpretation of the free second-order variables. -/
  W : Fin l → Set ℕ
  /-- The formula. -/
  φ : Formula A k l

@[inherit_doc] scoped notation "MSO[" M "," v "," W " ⊨ " φ "]" => Judgement.mk M v W φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement A) : Prop := Satisfies j.M j.v j.W j.φ

/-- The satisfaction of formulas as an inference system. -/
instance : HasInferenceSystem (Judgement A) := ⟨Satisfies.Bundled⟩

/-- A derivation of a judgement is a proof of the satisfaction relation. -/
theorem derivation_def {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    {φ : Formula A k l} : Satisfies M v W φ = ⇓MSO[M, v, W ⊨ φ] :=
  -- Holds by definition of the inference system.
  rfl

namespace Formula

/-- Negation is primitive. -/
instance : HasNot (Formula A k l) := ⟨.not⟩
/-- Disjunction is primitive. -/
instance : HasOr (Formula A k l) := ⟨.or⟩
/-- `φ ∧ ψ` is defined as `¬(¬φ ∨ ¬ψ)`. -/
instance : HasAnd (Formula A k l) := ⟨fun φ ψ ↦ .not (.or (.not φ) (.not ψ))⟩
/-- `φ → ψ` is defined as `¬φ ∨ ψ`. -/
instance : HasImp (Formula A k l) := ⟨fun φ ψ ↦ .or (.not φ) ψ⟩
/-- `⊥` is defined as `∃x ¬(x = x)`, which does not need any free variable. -/
instance : Bot (Formula A k l) := ⟨.ex₁ (.not (.eq (Fin.last k) (Fin.last k)))⟩
/-- `⊤` is defined as `¬⊥`. -/
instance : Top (Formula A k l) := ⟨.not ⊥⟩

/-- First-order universal quantification. -/
def all₁ (φ : Formula A (k + 1) l) : Formula A k l := .not (.ex₁ (.not φ))

/-- Second-order universal quantification. -/
def all₂ (φ : Formula A k (l + 1)) : Formula A k l := .not (.ex₂ (.not φ))

/-- `first(x) := ¬∃y S(y, x)`: position `x` is the first position. -/
def first (x : Fin k) : Formula A k l := .not (.ex₁ (.succ (Fin.last k) x.castSucc))

/-- `last(x) := ¬∃y S(x, y)`: position `x` is the last position. -/
def last (x : Fin k) : Formula A k l := .not (.ex₁ (.succ x.castSucc (Fin.last k)))

/-- Prefix the formula `φ` by existential quantifiers for all its second-order variables. -/
def exAll₂ : (n : ℕ) → Formula A k n → Formula A k 0
  | 0, φ => φ
  | n + 1, φ => exAll₂ n (.ex₂ φ)

/-- `φ` is a formula of MSO[S], that is, it does not use the order relation. -/
def LtFree : {k l : ℕ} → Formula A k l → Prop
  | _, _, .lt _ _ => False
  | _, _, .not φ => φ.LtFree
  | _, _, .or φ ψ => φ.LtFree ∧ ψ.LtFree
  | _, _, .ex₁ φ => φ.LtFree
  | _, _, .ex₂ φ => φ.LtFree
  | _, _, .eq _ _ | _, _, .succ _ _ | _, _, .label _ _ | _, _, .mem _ _ => True

/-- `φ` is a first-order formula, that is, it does not contain second-order quantifiers. It can
have free second-order variables. -/
def IsFirstOrder : {k l : ℕ} → Formula A k l → Prop
  | _, _, .not φ => φ.IsFirstOrder
  | _, _, .or φ ψ => φ.IsFirstOrder ∧ ψ.IsFirstOrder
  | _, _, .ex₁ φ => φ.IsFirstOrder
  | _, _, .ex₂ _ => False
  | _, _, .eq _ _ | _, _, .succ _ _ | _, _, .lt _ _ | _, _, .label _ _ | _, _, .mem _ _ => True

/-- `φ` is a formula of existential monadic second-order logic (EMSO): a prefix of existential
second-order quantifiers followed by a first-order formula. -/
inductive IsEMSO : {k l : ℕ} → Formula A k l → Prop where
  /-- A first-order formula is an EMSO formula. -/
  | firstOrder {k l : ℕ} {φ : Formula A k l} (h : φ.IsFirstOrder) : IsEMSO φ
  /-- The existential second-order quantification of an EMSO formula is an EMSO formula. -/
  | ex₂ {k l : ℕ} {φ : Formula A k (l + 1)} (h : IsEMSO φ) : IsEMSO (.ex₂ φ)

section Fragments

variable {φ ψ : Formula A k l}

/-- `¬φ` is a formula of MSO[S] iff `φ` is. -/
@[simp, scoped grind =]
theorem ltFree_not : (¬φ : Formula A k l).LtFree ↔ φ.LtFree :=
  -- Holds by definition of `LtFree`.
  Iff.rfl

/-- `φ ∨ ψ` is a formula of MSO[S] iff both disjuncts are. -/
@[simp, scoped grind =]
theorem ltFree_or : (φ ∨ ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree :=
  -- Holds by definition of `LtFree`.
  Iff.rfl

/-- `φ ∧ ψ` is a formula of MSO[S] iff both conjuncts are. -/
@[simp, scoped grind =]
theorem ltFree_and : (φ ∧ ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree :=
  -- `φ ∧ ψ` unfolds to `¬(¬φ ∨ ¬ψ)`, so this holds by definition of `LtFree`.
  Iff.rfl

/-- `φ → ψ` is a formula of MSO[S] iff both subformulas are. -/
@[simp, scoped grind =]
theorem ltFree_imp : (φ → ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree :=
  -- `φ → ψ` unfolds to `¬φ ∨ ψ`, so this holds by definition of `LtFree`.
  Iff.rfl

/-- `⊥` is a formula of MSO[S]. -/
@[simp, scoped grind .]
theorem ltFree_bot : (⊥ : Formula A k l).LtFree :=
  -- `⊥` only uses equality, so `LtFree` computes to `True`.
  trivial

/-- `⊤` is a formula of MSO[S]. -/
@[simp, scoped grind .]
theorem ltFree_top : (⊤ : Formula A k l).LtFree :=
  -- `⊤` only uses negation and equality, so `LtFree` computes to `True`.
  trivial

/-- `∀x φ` is a formula of MSO[S] iff `φ` is. -/
@[simp, scoped grind =]
theorem ltFree_all₁ {φ : Formula A (k + 1) l} : φ.all₁.LtFree ↔ φ.LtFree :=
  -- `all₁ φ` unfolds to `¬∃x ¬φ`, so this holds by definition of `LtFree`.
  Iff.rfl

/-- `∀X φ` is a formula of MSO[S] iff `φ` is. -/
@[simp, scoped grind =]
theorem ltFree_all₂ {φ : Formula A k (l + 1)} : φ.all₂.LtFree ↔ φ.LtFree :=
  -- `all₂ φ` unfolds to `¬∃X ¬φ`, so this holds by definition of `LtFree`.
  Iff.rfl

/-- `first(x)` is a formula of MSO[S]. -/
@[simp, scoped grind .]
theorem ltFree_first (x : Fin k) : (first x : Formula A k l).LtFree :=
  -- `first` only uses the successor relation, so `LtFree` computes to `True`.
  trivial

/-- `last(x)` is a formula of MSO[S]. -/
@[simp, scoped grind .]
theorem ltFree_last (x : Fin k) : (last x : Formula A k l).LtFree :=
  -- `last` only uses the successor relation, so `LtFree` computes to `True`.
  trivial

/-- `¬φ` is first-order iff `φ` is. -/
@[simp, scoped grind =]
theorem isFirstOrder_not : (¬φ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder :=
  -- Holds by definition of `IsFirstOrder`.
  Iff.rfl

/-- `φ ∨ ψ` is first-order iff both disjuncts are. -/
@[simp, scoped grind =]
theorem isFirstOrder_or :
    (φ ∨ ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder :=
  -- Holds by definition of `IsFirstOrder`.
  Iff.rfl

/-- `φ ∧ ψ` is first-order iff both conjuncts are. -/
@[simp, scoped grind =]
theorem isFirstOrder_and :
    (φ ∧ ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder :=
  -- `φ ∧ ψ` unfolds to `¬(¬φ ∨ ¬ψ)`, so this holds by definition of `IsFirstOrder`.
  Iff.rfl

/-- `φ → ψ` is first-order iff both subformulas are. -/
@[simp, scoped grind =]
theorem isFirstOrder_imp :
    (φ → ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder :=
  -- `φ → ψ` unfolds to `¬φ ∨ ψ`, so this holds by definition of `IsFirstOrder`.
  Iff.rfl

/-- `⊥` is first-order. -/
@[simp, scoped grind .]
theorem isFirstOrder_bot : (⊥ : Formula A k l).IsFirstOrder :=
  -- `⊥` only has a first-order quantifier, so `IsFirstOrder` computes to `True`.
  trivial

/-- `⊤` is first-order. -/
@[simp, scoped grind .]
theorem isFirstOrder_top : (⊤ : Formula A k l).IsFirstOrder :=
  -- `⊤` only has a first-order quantifier, so `IsFirstOrder` computes to `True`.
  trivial

/-- `∀x φ` is first-order iff `φ` is. -/
@[simp, scoped grind =]
theorem isFirstOrder_all₁ {φ : Formula A (k + 1) l} : φ.all₁.IsFirstOrder ↔ φ.IsFirstOrder :=
  -- `all₁ φ` unfolds to `¬∃x ¬φ`, so this holds by definition of `IsFirstOrder`.
  Iff.rfl

/-- `first(x)` is first-order. -/
@[simp, scoped grind .]
theorem isFirstOrder_first (x : Fin k) : (first x : Formula A k l).IsFirstOrder :=
  -- `first` only has a first-order quantifier, so `IsFirstOrder` computes to `True`.
  trivial

/-- `last(x)` is first-order. -/
@[simp, scoped grind .]
theorem isFirstOrder_last (x : Fin k) : (last x : Formula A k l).IsFirstOrder :=
  -- `last` only has a first-order quantifier, so `IsFirstOrder` computes to `True`.
  trivial

/-- A finite disjunction of formulas of MSO[S] is a formula of MSO[S]. -/
theorem ltFree_finiteOr {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.LtFree) :
    (⋁φs : Formula A k l).LtFree := by
  -- Induct on the list of disjuncts.
  induction φs with
  -- The empty disjunction is `⊥`.
  | nil => exact ltFree_bot
  -- A disjunction `φ ∨ ⋁φs`: use `h` for `φ` and the induction hypothesis for `⋁φs`.
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite conjunction of formulas of MSO[S] is a formula of MSO[S]. -/
theorem ltFree_finiteAnd {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.LtFree) :
    (⋀φs : Formula A k l).LtFree := by
  -- Induct on the list of conjuncts.
  induction φs with
  -- The empty conjunction is `⊤`.
  | nil => exact ltFree_top
  -- A conjunction `φ ∧ ⋀φs`: use `h` for `φ` and the induction hypothesis for `⋀φs`.
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite disjunction of first-order formulas is a first-order formula. -/
theorem isFirstOrder_finiteOr {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.IsFirstOrder) :
    (⋁φs : Formula A k l).IsFirstOrder := by
  -- Induct on the list of disjuncts.
  induction φs with
  -- The empty disjunction is `⊥`.
  | nil => exact isFirstOrder_bot
  -- A disjunction `φ ∨ ⋁φs`: use `h` for `φ` and the induction hypothesis for `⋁φs`.
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite conjunction of first-order formulas is a first-order formula. -/
theorem isFirstOrder_finiteAnd {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.IsFirstOrder) :
    (⋀φs : Formula A k l).IsFirstOrder := by
  -- Induct on the list of conjuncts.
  induction φs with
  -- The empty conjunction is `⊤`.
  | nil => exact isFirstOrder_top
  -- A conjunction `φ ∧ ⋀φs`: use `h` for `φ` and the induction hypothesis for `⋀φs`.
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- Prefixing existential second-order quantifiers does not affect the use of the order relation. -/
@[simp]
theorem ltFree_exAll₂ {n : ℕ} {φ : Formula A k n} : (exAll₂ n φ).LtFree ↔ φ.LtFree := by
  -- Induct on the number of quantifiers.
  induction n with
  -- Without quantifiers, the formula is unchanged.
  | zero => rfl
  -- `exAll₂ (n + 1) φ` is `exAll₂ n (∃X φ)`, and `∃X φ` is in MSO[S] iff `φ` is.
  | succ n ih => exact ih

/-- A first-order formula prefixed by existential second-order quantifiers is an EMSO formula. -/
theorem isEMSO_exAll₂ {n : ℕ} {φ : Formula A k n} (h : φ.IsEMSO) : (exAll₂ n φ).IsEMSO := by
  -- Induct on the number of quantifiers.
  induction n with
  -- Without quantifiers, the formula is unchanged.
  | zero => exact h
  -- `∃X φ` is an EMSO formula as well, so the induction hypothesis applies to it.
  | succ n ih => exact ih h.ex₂

end Fragments

end Formula

section Semantics

variable {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ} {φ ψ : Formula A k l}

/-- The semantics of negation. -/
@[simp, scoped grind =]
theorem satisfies_not : Satisfies M v W (¬φ) ↔ ¬Satisfies M v W φ :=
  -- Holds by definition of `Satisfies`.
  Iff.rfl

/-- The semantics of disjunction. -/
@[simp, scoped grind =]
theorem satisfies_or : Satisfies M v W (φ ∨ ψ) ↔ Satisfies M v W φ ∨ Satisfies M v W ψ :=
  -- Holds by definition of `Satisfies`.
  Iff.rfl

/-- The semantics of the derived conjunction. -/
@[simp, scoped grind =]
theorem satisfies_and : Satisfies M v W (φ ∧ ψ) ↔ Satisfies M v W φ ∧ Satisfies M v W ψ := by
  -- Unfold `φ ∧ ψ` to `¬(¬φ ∨ ¬ψ)`.
  change ¬(¬Satisfies M v W φ ∨ ¬Satisfies M v W ψ) ↔ _
  -- The rest is propositional logic (De Morgan).
  tauto

/-- The semantics of the derived implication. -/
@[simp, scoped grind =]
theorem satisfies_imp : Satisfies M v W (φ → ψ) ↔ (Satisfies M v W φ → Satisfies M v W ψ) := by
  -- Unfold `φ → ψ` to `¬φ ∨ ψ`.
  change (¬Satisfies M v W φ ∨ Satisfies M v W ψ) ↔ _
  -- The rest is propositional logic.
  tauto

/-- The formula `⊥` is never satisfied. -/
@[simp, scoped grind .]
theorem not_satisfies_bot : ¬Satisfies M v W (⊥ : Formula A k l) := by
  -- `⊥` is `∃x ¬(x = x)`: take the witness `p` with `p ≠ p`.
  rintro ⟨p, -, hp⟩
  -- This contradicts the reflexivity of equality.
  exact hp rfl

/-- The formula `⊤` is always satisfied. -/
@[simp, scoped grind .]
theorem satisfies_top : Satisfies M v W (⊤ : Formula A k l) :=
  -- `⊤` is `¬⊥`, and `⊥` is not satisfied.
  not_satisfies_bot

/-- The semantics of first-order universal quantification. -/
@[simp, scoped grind =]
theorem satisfies_all₁ {φ : Formula A (k + 1) l} :
    Satisfies M v W φ.all₁ ↔ ∀ p ∈ M.dom, Satisfies M (Fin.snoc (α := fun _ ↦ ℕ) v p) W φ := by
  -- Unfold `∀x φ` to `¬∃x ¬φ`.
  change (¬∃ p ∈ M.dom, ¬Satisfies M _ W φ) ↔ _
  -- Push the negation inward.
  push Not
  -- Both sides are now the same statement.
  rfl

/-- The semantics of second-order universal quantification. -/
@[simp, scoped grind =]
theorem satisfies_all₂ {φ : Formula A k (l + 1)} :
    Satisfies M v W φ.all₂ ↔
      ∀ P ⊆ M.dom, Satisfies M v (Fin.snoc (α := fun _ ↦ Set ℕ) W P) φ := by
  -- Unfold `∀X φ` to `¬∃X ¬φ`.
  change (¬∃ P ⊆ M.dom, ¬Satisfies M v _ φ) ↔ _
  -- Push the negation inward.
  push Not
  -- Both sides are now the same statement.
  rfl

/-- A finite disjunction is satisfied iff one of the disjuncts is. -/
@[simp]
theorem satisfies_finiteOr {φs : List (Formula A k l)} :
    Satisfies M v W (⋁φs) ↔ ∃ φ ∈ φs, Satisfies M v W φ := by
  -- Induct on the list of disjuncts.
  induction φs with
  -- The empty disjunction is `⊥`, which is not satisfied.
  | nil => simp
  -- `φ ∨ ⋁φs` holds iff `φ` or, by the induction hypothesis, a disjunct of `φs` holds.
  | cons φ φs ih => simp [ih]

/-- A finite conjunction is satisfied iff all of the conjuncts are. -/
@[simp]
theorem satisfies_finiteAnd {φs : List (Formula A k l)} :
    Satisfies M v W (⋀φs) ↔ ∀ φ ∈ φs, Satisfies M v W φ := by
  -- Induct on the list of conjuncts.
  induction φs with
  -- The empty conjunction is `⊤`, which is satisfied.
  | nil => simp
  -- `φ ∧ ⋀φs` holds iff `φ` and, by the induction hypothesis, all conjuncts of `φs` hold.
  | cons φ φs ih => simp [ih]

/-- A position of the domain is the first position iff it is `0`. -/
theorem satisfies_first {x : Fin k} (hx : v x ∈ M.dom) :
    Satisfies M v W (Formula.first x) ↔ v x = 0 := by
  -- Unfold `first(x)` to `¬∃y S(y, x)`.
  change (¬∃ p ∈ M.dom, Satisfies M _ W (.succ _ _)) ↔ _
  -- Evaluate the variables: the statement becomes `¬∃p ∈ dom, v x = p + 1`.
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  -- Show both directions.
  constructor
  -- Assume that `x` has no predecessor in the domain.
  · intro h
    -- Suppose that `v x` is not `0`.
    by_contra hne
    -- Then `v x` is the successor of some `p`.
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hne
    -- As `p < v x`, the position `p` belongs to the domain, which contradicts `h`.
    exact h ⟨p, M.mem_dom_of_le (by omega) hx, hp⟩
  -- Conversely, let `v x = 0` and suppose that `v x = p + 1`.
  · rintro h ⟨p, -, hp⟩
    -- This is impossible.
    omega

/-- A position is the last position iff its successor does not belong to the domain. -/
theorem satisfies_last {x : Fin k} : Satisfies M v W (Formula.last x) ↔ v x + 1 ∉ M.dom := by
  -- Unfold `last(x)` to `¬∃y S(x, y)`.
  change (¬∃ p ∈ M.dom, Satisfies M _ W (.succ _ _)) ↔ _
  -- Evaluate the variables: the statement becomes `¬∃p ∈ dom, p = v x + 1`.
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  -- Show both directions.
  constructor
  -- If `v x + 1` were in the domain, it would be a successor of `v x` in the domain.
  · exact fun h hx ↦ h ⟨_, hx, rfl⟩
  -- Conversely, a successor `p` in the domain is `v x + 1` itself.
  · rintro h ⟨p, hp, rfl⟩
    -- This contradicts the assumption.
    exact h hp

/-- Existential quantification of all second-order variables of a formula. -/
theorem satisfies_exAll₂ {n : ℕ} {φ : Formula A k n} {W₀ : Fin 0 → Set ℕ} :
    Satisfies M v W₀ (Formula.exAll₂ n φ) ↔
      ∃ Y : Fin n → Set ℕ, (∀ j, Y j ⊆ M.dom) ∧ Satisfies M v Y φ := by
  -- Induct on the number of quantifiers, for all interpretations of the empty context.
  induction n generalizing W₀ with
  -- No quantifiers: `exAll₂ 0 φ` is `φ`, and there is only one interpretation of no variables.
  | zero =>
    -- From left to right, use the interpretation `W₀`, which has no components to check.
    refine ⟨fun h ↦ ⟨W₀, fun j ↦ j.elim0, h⟩, ?_⟩
    -- From right to left, take the given interpretation `Y`.
    rintro ⟨Y, -, hY⟩
    -- There is only one function on `Fin 0`, so `Y` is `W₀`.
    rwa [Subsingleton.elim W₀ Y]
  -- Induction step: `exAll₂ (n + 1) φ` quantifies the last variable first.
  | succ n ih =>
    -- Unfold one quantifier and apply the induction hypothesis to `∃X φ`.
    rw [Formula.exAll₂, ih]
    -- Show both directions.
    constructor
    -- Assume sets `Y` for the first `n` variables and a set `P` for the last one.
    · rintro ⟨Y, hY, P, hP, h⟩
      -- Extend `Y` by `P`; the formula holds by `h`, and it remains to check the domain.
      refine ⟨Fin.snoc (α := fun _ ↦ Set ℕ) Y P, fun j ↦ ?_, h⟩
      -- Distinguish the last variable from the others.
      induction j using Fin.lastCases with
      -- The last variable is interpreted by `P`.
      | last => simpa using hP
      -- The others are interpreted by `Y`.
      | cast j => simpa using hY j
    -- Conversely, assume sets `Y` for all `n + 1` variables.
    · rintro ⟨Y, hY, h⟩
      -- Split them into the first `n` sets and the last set, which are in the domain by `hY`.
      refine ⟨Fin.init (α := fun _ ↦ Set ℕ) Y, fun j ↦ hY _, Y (Fin.last n), hY _, ?_⟩
      -- Joining these parts again gives `Y`, so the formula holds by `h`.
      rwa [Fin.snoc_init_self]

end Semantics

namespace Formula

/-- The MSO[S]-definition of the order relation (Section 2.3 of [Thomas1997]):
`¬x = y ∧ ∀Z (Z(x) ∧ ∀u ∀u' (Z(u) ∧ S(u, u') → Z(u')) → Z(y))`. -/
def ltDef (x y : Fin k) : Formula A k l :=
  (¬(.eq x y) ∧ all₂ (
    ((.mem x (Fin.last l)) ∧
      all₁ (all₁ (((.mem (Fin.last k).castSucc (Fin.last l)) ∧
          (.succ (Fin.last k).castSucc (Fin.last (k + 1)))) →
        (.mem (Fin.last (k + 1)) (Fin.last l))))) →
    (.mem y (Fin.last l))) : Formula A k l)

/-- The definition of the order relation is a formula of MSO[S]. -/
@[simp]
theorem ltFree_ltDef (x y : Fin k) : (ltDef x y : Formula A k l).LtFree := by
  -- `ltDef` only uses equality, membership and the successor relation.
  simp [ltDef, LtFree]

/-- The definition of the order relation in terms of the successor relation is correct. -/
theorem satisfies_ltDef {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ} {x y : Fin k}
    (hx : v x ∈ M.dom) (hy : v y ∈ M.dom) : Satisfies M v W (ltDef x y) ↔ v x < v y := by
  -- Unfold the derived connectives of `ltDef`.
  simp only [ltDef, satisfies_and, satisfies_not, satisfies_all₂, satisfies_imp, satisfies_all₁]
  -- Evaluate the atomic formulas.
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  -- Show both directions.
  constructor
  -- Assume `x ≠ y`, and that `y` is in each set that contains `x` and is closed under successor.
  · rintro ⟨hne, h⟩
    -- The positions of the domain from `x` on are closed under successor.
    have hclosed : ∀ p ∈ M.dom, ∀ p' ∈ M.dom, p ∈ {p ∈ M.dom | v x ≤ p} ∧ p' = p + 1 →
        -- A successor of a position of this set belongs to the set as well.
        p' ∈ {p ∈ M.dom | v x ≤ p} := by
      -- Let `p` be such a position and `p' = p + 1` a position of the domain.
      rintro p - p' hp' ⟨⟨-, hp⟩, rfl⟩
      -- Then `x ≤ p'` follows from `x ≤ p`.
      exact ⟨hp', by omega⟩
    -- Hence `y` belongs to this set, as it contains `x` and is closed under successor.
    have hy' := h {p ∈ M.dom | v x ≤ p} (fun p hp ↦ hp.1) ⟨⟨hx, le_rfl⟩, hclosed⟩
    -- So `x ≤ y`, and together with `x ≠ y` this gives `x < y`.
    exact lt_of_le_of_ne hy'.2 hne
  -- Conversely, assume `x < y`.
  · intro hlt
    -- Then `x ≠ y`; let `Z` be a set that contains `x` and is closed under successor.
    refine ⟨hlt.ne, fun Z _ ⟨hx, hZ⟩ ↦ ?_⟩
    -- All positions `x + d` up to `y` belong to `Z`.
    have key : ∀ d, v x + d ≤ v y → v x + d ∈ Z := by
      -- Introduce the distance `d`.
      intro d
      -- Induct on `d`.
      induction d with
      -- For `d = 0`, this is the assumption that `x ∈ Z`.
      | zero => exact fun _ ↦ hx
      -- For `d + 1`, use the closure of `Z` under successor.
      | succ d ih =>
        -- Assume that `x + d + 1 ≤ y`.
        intro hd
        -- Close `Z` under the successor of `x + d`, which is in the domain as it is below `y`.
        exact hZ (v x + d) (M.mem_dom_of_le (by omega) hy) (v x + (d + 1))
          -- The position `x + d + 1` is in the domain, and `x + d ∈ Z` by the induction hypothesis.
          (M.mem_dom_of_le hd hy) ⟨ih (by omega), rfl⟩
    -- Apply this to the distance `y - x`.
    have := key (v y - v x) (by omega)
    -- This distance leads exactly to `y`.
    rwa [Nat.add_sub_cancel' hlt.le] at this

/-- Replace all occurrences of the order relation by their MSO[S]-definition `ltDef`. -/
def elimLt : {k l : ℕ} → Formula A k l → Formula A k l
  | _, _, .eq x y => .eq x y
  | _, _, .succ x y => .succ x y
  | _, _, .lt x y => ltDef x y
  | _, _, .label a x => .label a x
  | _, _, .mem x X => .mem x X
  | _, _, .not φ => .not φ.elimLt
  | _, _, .or φ ψ => .or φ.elimLt ψ.elimLt
  | _, _, .ex₁ φ => .ex₁ φ.elimLt
  | _, _, .ex₂ φ => .ex₂ φ.elimLt

/-- The elimination of the order relation yields a formula of MSO[S]. -/
@[simp]
theorem ltFree_elimLt (φ : Formula A k l) : φ.elimLt.LtFree := by
  -- Induct on the formula.
  induction φ with
  -- `x < y` is replaced by `ltDef`, which is in MSO[S].
  | lt x y => exact ltFree_ltDef x y
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact ih
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  -- First-order quantifier: apply the induction hypothesis.
  | ex₁ φ ih => exact ih
  -- Second-order quantifier: apply the induction hypothesis.
  | ex₂ φ ih => exact ih
  -- The other atomic formulas are unchanged and do not use the order relation.
  | _ => trivial

/-- Over word models, every formula is equivalent to a formula of MSO[S]. -/
theorem satisfies_elimLt {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (φ : Formula A k l) (hv : ∀ x, v x ∈ M.dom) :
    Satisfies M v W φ.elimLt ↔ Satisfies M v W φ := by
  -- Induct on the formula.
  induction φ with
  -- `ltDef` defines the order on the positions of the domain.
  | lt x y => exact satisfies_ltDef (hv x) (hv y)
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact not_congr (ih hv)
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hv) (ihψ hv)
  -- First-order quantifier: the new variable is a position `p` of the domain.
  | ex₁ φ ih =>
    -- By the induction hypothesis, it suffices that the extended interpretation stays in the
    -- domain.
    refine exists_congr fun p ↦ and_congr_right fun hp ↦ ih fun x ↦ ?_
    -- Distinguish the new variable from the old ones.
    induction x using Fin.lastCases with
    -- The new variable is interpreted by `p`.
    | last => simpa using hp
    -- The old ones are interpreted by `v`.
    | cast x => simpa using hv x
  -- Second-order quantifier: the first-order interpretation is unchanged.
  | ex₂ φ ih => exact exists_congr fun P ↦ and_congr_right fun _ ↦ ih hv
  -- The other atomic formulas are unchanged.
  | _ => rfl

end Formula

/-- A sentence is a formula without free variables. -/
abbrev Sentence (A : Type u) := Formula A 0 0

/-- The truth of a sentence in a word model. -/
def Sentence.Holds (φ : Sentence A) (M : WordModel A) : Prop := Satisfies M Fin.elim0 Fin.elim0 φ

/-- The language defined by a sentence (`L(φ)` in [Thomas1997]). -/
def Sentence.language (φ : Sentence A) : Language A := {w | φ.Holds (ofList w)}

/-- The ω-language defined by a sentence (`L_ω(φ)` in [Thomas1997]). -/
def Sentence.ωlanguage (φ : Sentence A) : ωLanguage A := ⟨{α | φ.Holds (ofOmega α)}⟩

/-- A word belongs to the language of a sentence iff the sentence holds in its model. -/
@[simp, scoped grind =]
theorem Sentence.mem_language {φ : Sentence A} {w : List A} :
    w ∈ φ.language ↔ φ.Holds (ofList w) :=
  -- Holds by definition of `language`.
  Iff.rfl

/-- An ω-word belongs to the ω-language of a sentence iff the sentence holds in its model. -/
@[simp, scoped grind =]
theorem Sentence.mem_ωlanguage {φ : Sentence A} {α : ωSequence A} :
    α ∈ φ.ωlanguage ↔ φ.Holds (ofOmega α) :=
  -- Holds by definition of `ωlanguage`.
  Iff.rfl

/-- Eliminating the order relation preserves the truth of a sentence in a word model. -/
@[simp]
theorem Sentence.holds_elimLt {φ : Sentence A} {M : WordModel A} :
    Holds (Formula.elimLt φ) M ↔ φ.Holds M :=
  -- The sentence has no free variables, so the interpretation is trivially in the domain.
  Formula.satisfies_elimLt φ fun x ↦ x.elim0

/-- A language is MSO[S]-definable if it is defined by a sentence that does not use the order
relation. -/
def IsDefinable (L : Language A) : Prop := ∃ φ : Sentence A, φ.LtFree ∧ φ.language = L

/-- An ω-language is MSO[S]-definable if it is defined by a sentence that does not use the order
relation. -/
def IsωDefinable (p : ωLanguage A) : Prop := ∃ φ : Sentence A, φ.LtFree ∧ φ.ωlanguage = p

/-- The order relation does not add expressive power: a language is MSO[S]-definable iff it is
defined by a sentence that can also use the order relation. -/
theorem isDefinable_iff_exists_sentence {L : Language A} :
    IsDefinable L ↔ ∃ φ : Sentence A, φ.language = L := by
  -- Show both directions.
  constructor
  -- A sentence of MSO[S] is in particular a sentence.
  · rintro ⟨φ, -, h⟩
    -- It defines `L` by assumption.
    exact ⟨φ, h⟩
  -- Conversely, take a sentence `φ` that may use the order relation.
  · rintro ⟨φ, rfl⟩
    -- Eliminating the order relation gives a sentence of MSO[S].
    refine ⟨Formula.elimLt φ, Formula.ltFree_elimLt φ, ?_⟩
    -- Compare both languages on a word `w`.
    ext w
    -- The elimination preserves the truth in the model of `w`.
    exact Sentence.holds_elimLt

/-- The order relation does not add expressive power: an ω-language is MSO[S]-definable iff it is
defined by a sentence that can also use the order relation. -/
theorem isωDefinable_iff_exists_sentence {p : ωLanguage A} :
    IsωDefinable p ↔ ∃ φ : Sentence A, φ.ωlanguage = p := by
  -- Show both directions.
  constructor
  -- A sentence of MSO[S] is in particular a sentence.
  · rintro ⟨φ, -, h⟩
    -- It defines `p` by assumption.
    exact ⟨φ, h⟩
  -- Conversely, take a sentence `φ` that may use the order relation.
  · rintro ⟨φ, rfl⟩
    -- Eliminating the order relation gives a sentence of MSO[S].
    refine ⟨Formula.elimLt φ, Formula.ltFree_elimLt φ, ?_⟩
    -- Compare both ω-languages on an ω-word `α`.
    ext α
    -- The elimination preserves the truth in the model of `α`.
    exact Sentence.holds_elimLt

end Cslib.Logic.MSO
