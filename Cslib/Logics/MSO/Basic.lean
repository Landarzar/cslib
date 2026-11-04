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

@[scoped grind =]
theorem mem_dom {M : WordModel A} {i : ℕ} : i ∈ M.dom ↔ (M.label i).isSome := Iff.rfl

theorem mem_dom_of_le {M : WordModel A} {i j : ℕ} (hij : i ≤ j) (hj : j ∈ M.dom) : i ∈ M.dom :=
  M.isSome_of_le hij hj

/-- The word model of a finite word. -/
def ofList (w : List A) : WordModel A where
  label i := w[i]?
  isSome_of_le {i j} hij hj := by
    simp only [isSome_getElem?] at hj ⊢
    exact lt_of_le_of_lt hij hj

/-- The word model of an ω-word. -/
def ofOmega (α : ωSequence A) : WordModel A where
  label i := some (α i)
  isSome_of_le _ _ := rfl

@[simp, scoped grind =]
theorem ofList_label (w : List A) (i : ℕ) : (ofList w).label i = w[i]? := rfl

@[simp, scoped grind =]
theorem ofOmega_label (α : ωSequence A) (i : ℕ) : (ofOmega α).label i = some (α i) := rfl

@[simp, scoped grind =]
theorem mem_dom_ofList {w : List A} {i : ℕ} : i ∈ (ofList w).dom ↔ i < w.length := by
  simp [dom]

@[scoped grind .]
theorem mem_dom_ofOmega {α : ωSequence A} {i : ℕ} : i ∈ (ofOmega α).dom := rfl

@[simp]
theorem dom_ofOmega (α : ωSequence A) : (ofOmega α).dom = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_dom_ofOmega

/-- Relabel the positions of a word model. -/
def map (f : A → B) (M : WordModel A) : WordModel B where
  label i := (M.label i).map f
  isSome_of_le hij hj := by
    simp only [Option.isSome_map] at hj ⊢
    exact M.isSome_of_le hij hj

@[simp, scoped grind =]
theorem map_label (f : A → B) (M : WordModel A) (i : ℕ) :
    (M.map f).label i = (M.label i).map f := rfl

@[simp, scoped grind =]
theorem dom_map (f : A → B) (M : WordModel A) : (M.map f).dom = M.dom := by
  ext i
  simp [dom]

@[simp]
theorem map_ofList (f : A → B) (w : List A) : (ofList w).map f = ofList (w.map f) := by
  ext1
  funext i
  simp

@[simp]
theorem map_ofOmega (f : A → B) (α : ωSequence A) : (ofOmega α).map f = ofOmega (α.map f) := rfl

theorem ofList_injective : Function.Injective (ofList (A := A)) := by
  intro w w' h
  apply List.ext_getElem?
  intro i
  exact congrFun (congrArg label h) i

theorem ofOmega_injective : Function.Injective (ofOmega (A := A)) := by
  intro α β h
  ext i
  exact Option.some.inj (congrFun (congrArg label h) i)

/-- A word model with the domain of a finite word is the model of a finite word. -/
theorem exists_eq_ofList (M : WordModel A) (n : ℕ) (hM : ∀ i, i ∈ M.dom ↔ i < n) :
    ∃ w : List A, w.length = n ∧ M = ofList w := by
  refine ⟨List.ofFn fun i : Fin n ↦ (M.label i).get ((hM i).mpr i.isLt), by simp, ?_⟩
  ext1
  funext i
  by_cases hi : i < n
  · simpa [hi] using (Option.some_get ((hM i).mpr hi)).symm
  · have : M.label i = none := Option.not_isSome_iff_eq_none.mp fun h ↦ hi ((hM i).mp h)
    simp [hi, this]

/-- A word model with full domain is the model of an ω-word. -/
theorem exists_eq_ofOmega (M : WordModel A) (hM : ∀ i, i ∈ M.dom) :
    ∃ α : ωSequence A, M = ofOmega α := by
  refine ⟨fun i ↦ (M.label i).get (hM i), ?_⟩
  ext1
  funext i
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
  | _, _, v, W, .ex₁ φ => ∃ p ∈ M.dom, Satisfies M (Fin.snoc (α := fun _ ↦ ℕ) v p) W φ
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

instance : HasInferenceSystem (Judgement A) := ⟨Satisfies.Bundled⟩

theorem derivation_def {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    {φ : Formula A k l} : Satisfies M v W φ = ⇓MSO[M, v, W ⊨ φ] := rfl

namespace Formula

instance : HasNot (Formula A k l) := ⟨.not⟩
instance : HasOr (Formula A k l) := ⟨.or⟩
instance : HasAnd (Formula A k l) := ⟨fun φ ψ ↦ .not (.or (.not φ) (.not ψ))⟩
instance : HasImp (Formula A k l) := ⟨fun φ ψ ↦ .or (.not φ) ψ⟩
instance : Bot (Formula A k l) := ⟨.ex₁ (.not (.eq (Fin.last k) (Fin.last k)))⟩
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

@[simp, scoped grind =]
theorem ltFree_not : (¬φ : Formula A k l).LtFree ↔ φ.LtFree := Iff.rfl

@[simp, scoped grind =]
theorem ltFree_or : (φ ∨ ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree := Iff.rfl

@[simp, scoped grind =]
theorem ltFree_and : (φ ∧ ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree := Iff.rfl

@[simp, scoped grind =]
theorem ltFree_imp : (φ → ψ : Formula A k l).LtFree ↔ φ.LtFree ∧ ψ.LtFree := Iff.rfl

@[simp, scoped grind .]
theorem ltFree_bot : (⊥ : Formula A k l).LtFree := trivial

@[simp, scoped grind .]
theorem ltFree_top : (⊤ : Formula A k l).LtFree := trivial

@[simp, scoped grind =]
theorem ltFree_all₁ {φ : Formula A (k + 1) l} : φ.all₁.LtFree ↔ φ.LtFree := Iff.rfl

@[simp, scoped grind =]
theorem ltFree_all₂ {φ : Formula A k (l + 1)} : φ.all₂.LtFree ↔ φ.LtFree := Iff.rfl

@[simp, scoped grind .]
theorem ltFree_first (x : Fin k) : (first x : Formula A k l).LtFree := trivial

@[simp, scoped grind .]
theorem ltFree_last (x : Fin k) : (last x : Formula A k l).LtFree := trivial

@[simp, scoped grind =]
theorem isFirstOrder_not : (¬φ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder := Iff.rfl

@[simp, scoped grind =]
theorem isFirstOrder_or :
    (φ ∨ ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder := Iff.rfl

@[simp, scoped grind =]
theorem isFirstOrder_and :
    (φ ∧ ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder := Iff.rfl

@[simp, scoped grind =]
theorem isFirstOrder_imp :
    (φ → ψ : Formula A k l).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder := Iff.rfl

@[simp, scoped grind .]
theorem isFirstOrder_bot : (⊥ : Formula A k l).IsFirstOrder := trivial

@[simp, scoped grind .]
theorem isFirstOrder_top : (⊤ : Formula A k l).IsFirstOrder := trivial

@[simp, scoped grind =]
theorem isFirstOrder_all₁ {φ : Formula A (k + 1) l} : φ.all₁.IsFirstOrder ↔ φ.IsFirstOrder :=
  Iff.rfl

@[simp, scoped grind .]
theorem isFirstOrder_first (x : Fin k) : (first x : Formula A k l).IsFirstOrder := trivial

@[simp, scoped grind .]
theorem isFirstOrder_last (x : Fin k) : (last x : Formula A k l).IsFirstOrder := trivial

/-- A finite disjunction of formulas of MSO[S] is a formula of MSO[S]. -/
theorem ltFree_finiteOr {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.LtFree) :
    (⋁φs : Formula A k l).LtFree := by
  induction φs with
  | nil => exact ltFree_bot
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite conjunction of formulas of MSO[S] is a formula of MSO[S]. -/
theorem ltFree_finiteAnd {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.LtFree) :
    (⋀φs : Formula A k l).LtFree := by
  induction φs with
  | nil => exact ltFree_top
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite disjunction of first-order formulas is a first-order formula. -/
theorem isFirstOrder_finiteOr {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.IsFirstOrder) :
    (⋁φs : Formula A k l).IsFirstOrder := by
  induction φs with
  | nil => exact isFirstOrder_bot
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

/-- A finite conjunction of first-order formulas is a first-order formula. -/
theorem isFirstOrder_finiteAnd {φs : List (Formula A k l)} (h : ∀ φ ∈ φs, φ.IsFirstOrder) :
    (⋀φs : Formula A k l).IsFirstOrder := by
  induction φs with
  | nil => exact isFirstOrder_top
  | cons φ φs ih => exact ⟨h φ (by simp), ih fun ψ hψ ↦ h ψ (by simp [hψ])⟩

@[simp]
theorem ltFree_exAll₂ {n : ℕ} {φ : Formula A k n} : (exAll₂ n φ).LtFree ↔ φ.LtFree := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A first-order formula prefixed by existential second-order quantifiers is an EMSO formula. -/
theorem isEMSO_exAll₂ {n : ℕ} {φ : Formula A k n} (h : φ.IsEMSO) : (exAll₂ n φ).IsEMSO := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.ex₂

end Fragments

end Formula

section Semantics

variable {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ} {φ ψ : Formula A k l}

@[simp, scoped grind =]
theorem satisfies_not : Satisfies M v W (¬φ) ↔ ¬Satisfies M v W φ := Iff.rfl

@[simp, scoped grind =]
theorem satisfies_or : Satisfies M v W (φ ∨ ψ) ↔ Satisfies M v W φ ∨ Satisfies M v W ψ := Iff.rfl

@[simp, scoped grind =]
theorem satisfies_and : Satisfies M v W (φ ∧ ψ) ↔ Satisfies M v W φ ∧ Satisfies M v W ψ := by
  change ¬(¬Satisfies M v W φ ∨ ¬Satisfies M v W ψ) ↔ _
  tauto

@[simp, scoped grind =]
theorem satisfies_imp : Satisfies M v W (φ → ψ) ↔ (Satisfies M v W φ → Satisfies M v W ψ) := by
  change (¬Satisfies M v W φ ∨ Satisfies M v W ψ) ↔ _
  tauto

@[simp, scoped grind .]
theorem not_satisfies_bot : ¬Satisfies M v W (⊥ : Formula A k l) := by
  rintro ⟨p, -, hp⟩
  exact hp rfl

@[simp, scoped grind .]
theorem satisfies_top : Satisfies M v W (⊤ : Formula A k l) := not_satisfies_bot

@[simp, scoped grind =]
theorem satisfies_all₁ {φ : Formula A (k + 1) l} :
    Satisfies M v W φ.all₁ ↔ ∀ p ∈ M.dom, Satisfies M (Fin.snoc (α := fun _ ↦ ℕ) v p) W φ := by
  change (¬∃ p ∈ M.dom, ¬Satisfies M _ W φ) ↔ _
  push Not
  rfl

@[simp, scoped grind =]
theorem satisfies_all₂ {φ : Formula A k (l + 1)} :
    Satisfies M v W φ.all₂ ↔
      ∀ P ⊆ M.dom, Satisfies M v (Fin.snoc (α := fun _ ↦ Set ℕ) W P) φ := by
  change (¬∃ P ⊆ M.dom, ¬Satisfies M v _ φ) ↔ _
  push Not
  rfl

@[simp]
theorem satisfies_finiteOr {φs : List (Formula A k l)} :
    Satisfies M v W (⋁φs) ↔ ∃ φ ∈ φs, Satisfies M v W φ := by
  induction φs with
  | nil => simp
  | cons φ φs ih => simp [ih]

@[simp]
theorem satisfies_finiteAnd {φs : List (Formula A k l)} :
    Satisfies M v W (⋀φs) ↔ ∀ φ ∈ φs, Satisfies M v W φ := by
  induction φs with
  | nil => simp
  | cons φ φs ih => simp [ih]

/-- A position of the domain is the first position iff it is `0`. -/
theorem satisfies_first {x : Fin k} (hx : v x ∈ M.dom) :
    Satisfies M v W (Formula.first x) ↔ v x = 0 := by
  change (¬∃ p ∈ M.dom, Satisfies M _ W (.succ _ _)) ↔ _
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h
    by_contra hne
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hne
    exact h ⟨p, M.mem_dom_of_le (by omega) hx, hp⟩
  · rintro h ⟨p, -, hp⟩
    omega

/-- A position is the last position iff its successor does not belong to the domain. -/
theorem satisfies_last {x : Fin k} : Satisfies M v W (Formula.last x) ↔ v x + 1 ∉ M.dom := by
  change (¬∃ p ∈ M.dom, Satisfies M _ W (.succ _ _)) ↔ _
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · exact fun h hx ↦ h ⟨_, hx, rfl⟩
  · rintro h ⟨p, hp, rfl⟩
    exact h hp

/-- Existential quantification of all second-order variables of a formula. -/
theorem satisfies_exAll₂ {n : ℕ} {φ : Formula A k n} {W₀ : Fin 0 → Set ℕ} :
    Satisfies M v W₀ (Formula.exAll₂ n φ) ↔
      ∃ Y : Fin n → Set ℕ, (∀ j, Y j ⊆ M.dom) ∧ Satisfies M v Y φ := by
  induction n generalizing W₀ with
  | zero =>
    refine ⟨fun h ↦ ⟨W₀, fun j ↦ j.elim0, h⟩, ?_⟩
    rintro ⟨Y, -, hY⟩
    rwa [Subsingleton.elim W₀ Y]
  | succ n ih =>
    rw [Formula.exAll₂, ih]
    constructor
    · rintro ⟨Y, hY, P, hP, h⟩
      refine ⟨Fin.snoc (α := fun _ ↦ Set ℕ) Y P, fun j ↦ ?_, h⟩
      induction j using Fin.lastCases with
      | last => simpa using hP
      | cast j => simpa using hY j
    · rintro ⟨Y, hY, h⟩
      refine ⟨Fin.init (α := fun _ ↦ Set ℕ) Y, fun j ↦ hY _, Y (Fin.last n), hY _, ?_⟩
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

@[simp]
theorem ltFree_ltDef (x y : Fin k) : (ltDef x y : Formula A k l).LtFree := by
  simp [ltDef, LtFree]

/-- The definition of the order relation in terms of the successor relation is correct. -/
theorem satisfies_ltDef {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ} {x y : Fin k}
    (hx : v x ∈ M.dom) (hy : v y ∈ M.dom) : Satisfies M v W (ltDef x y) ↔ v x < v y := by
  simp only [ltDef, satisfies_and, satisfies_not, satisfies_all₂, satisfies_imp, satisfies_all₁]
  simp only [Satisfies, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨hne, h⟩
    have hclosed : ∀ p ∈ M.dom, ∀ p' ∈ M.dom, p ∈ {p ∈ M.dom | v x ≤ p} ∧ p' = p + 1 →
        p' ∈ {p ∈ M.dom | v x ≤ p} := by
      rintro p - p' hp' ⟨⟨-, hp⟩, rfl⟩
      exact ⟨hp', by omega⟩
    have hy' := h {p ∈ M.dom | v x ≤ p} (fun p hp ↦ hp.1) ⟨⟨hx, le_rfl⟩, hclosed⟩
    exact lt_of_le_of_ne hy'.2 hne
  · intro hlt
    refine ⟨hlt.ne, fun Z _ ⟨hx, hZ⟩ ↦ ?_⟩
    have key : ∀ d, v x + d ≤ v y → v x + d ∈ Z := by
      intro d
      induction d with
      | zero => exact fun _ ↦ hx
      | succ d ih =>
        intro hd
        exact hZ (v x + d) (M.mem_dom_of_le (by omega) hy) (v x + (d + 1))
          (M.mem_dom_of_le hd hy) ⟨ih (by omega), rfl⟩
    have := key (v y - v x) (by omega)
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

@[simp]
theorem ltFree_elimLt (φ : Formula A k l) : φ.elimLt.LtFree := by
  induction φ with
  | lt x y => exact ltFree_ltDef x y
  | not φ ih => exact ih
  | or φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩
  | ex₁ φ ih => exact ih
  | ex₂ φ ih => exact ih
  | _ => trivial

/-- Over word models, every formula is equivalent to a formula of MSO[S]. -/
theorem satisfies_elimLt {M : WordModel A} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (φ : Formula A k l) (hv : ∀ x, v x ∈ M.dom) :
    Satisfies M v W φ.elimLt ↔ Satisfies M v W φ := by
  induction φ with
  | lt x y => exact satisfies_ltDef (hv x) (hv y)
  | not φ ih => exact not_congr (ih hv)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hv) (ihψ hv)
  | ex₁ φ ih =>
    refine exists_congr fun p ↦ and_congr_right fun hp ↦ ih fun x ↦ ?_
    induction x using Fin.lastCases with
    | last => simpa using hp
    | cast x => simpa using hv x
  | ex₂ φ ih => exact exists_congr fun P ↦ and_congr_right fun _ ↦ ih hv
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

@[simp, scoped grind =]
theorem Sentence.mem_language {φ : Sentence A} {w : List A} :
    w ∈ φ.language ↔ φ.Holds (ofList w) := Iff.rfl

@[simp, scoped grind =]
theorem Sentence.mem_ωlanguage {φ : Sentence A} {α : ωSequence A} :
    α ∈ φ.ωlanguage ↔ φ.Holds (ofOmega α) := Iff.rfl

/-- Eliminating the order relation preserves the truth of a sentence in a word model. -/
@[simp]
theorem Sentence.holds_elimLt {φ : Sentence A} {M : WordModel A} :
    Holds (Formula.elimLt φ) M ↔ φ.Holds M :=
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
  constructor
  · rintro ⟨φ, -, h⟩
    exact ⟨φ, h⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨Formula.elimLt φ, Formula.ltFree_elimLt φ, ?_⟩
    ext w
    exact Sentence.holds_elimLt

/-- The order relation does not add expressive power: an ω-language is MSO[S]-definable iff it is
defined by a sentence that can also use the order relation. -/
theorem isωDefinable_iff_exists_sentence {p : ωLanguage A} :
    IsωDefinable p ↔ ∃ φ : Sentence A, φ.ωlanguage = p := by
  constructor
  · rintro ⟨φ, -, h⟩
    exact ⟨φ, h⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨Formula.elimLt φ, Formula.ltFree_elimLt φ, ?_⟩
    ext α
    exact Sentence.holds_elimLt

end Cslib.Logic.MSO
