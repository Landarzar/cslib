/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Logics.MSO.MSO0

/-! # Free variables as letters of the track alphabet

A formula `φ(x₁, …, x_k, X₁, …, X_l)` interpreted in a word model corresponds to a sentence
interpreted in the expanded word model over the alphabet `A × {0, 1}^(k + l)` (Section 2.3 of
[Thomas1997]). This file provides the way back: `Formula.elimTrack` translates a formula over the
track alphabet into a formula over `A` with the free variables `x₁, …, x_k, X₁, …, X_l`, by
replacing each letter predicate by a test of the variables.

This is needed to state the normal forms of Corollary 3.2 of [Thomas1997] for formulas with free
variables.

## Main definitions and results

- `WordModel.expand`: the expansion of a word model by an interpretation of free variables.
- `Formula.elimTrack`: the elimination of letter predicates over the track alphabet, which is
  correct by `Formula.satisfies_elimTrack` and preserves the fragments of MSO.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open WordModel
open scoped Classical in
/-- The bits of a position in the expansion of a word model by an interpretation of free
variables. -/
noncomputable def trackBits {k₀ l₀ : ℕ} (v₀ : Fin k₀ → ℕ) (W₀ : Fin l₀ → Set ℕ) (i : ℕ) :
    Fin (k₀ + l₀) → Bool :=
  Fin.addCases (fun x ↦ decide (i = v₀ x)) (fun X ↦ decide (i ∈ W₀ X))

universe u

variable {A : Type u} {k₀ l₀ k l : ℕ} {v₀ : Fin k₀ → ℕ} {W₀ : Fin l₀ → Set ℕ}

/-- The bits of the first-order variables mark the positions of their values. -/
@[simp]
theorem trackBits_castAdd {i : ℕ} {x : Fin k₀} :
    trackBits v₀ W₀ i (Fin.castAdd l₀ x) = true ↔ i = v₀ x := by
  -- The bit of a first-order variable is the decision of `i = v₀ x`.
  simp [trackBits]

/-- The bits of the second-order variables mark the members of their sets. -/
@[simp]
theorem trackBits_natAdd {i : ℕ} {X : Fin l₀} :
    trackBits v₀ W₀ i (Fin.natAdd k₀ X) = true ↔ i ∈ W₀ X := by
  -- The bit of a second-order variable is the decision of `i ∈ W₀ X`.
  simp [trackBits]

namespace WordModel

/-- The expansion of a word model by an interpretation of `k₀` first-order variables and `l₀`
second-order variables to a word model over the track alphabet. -/
noncomputable def expand (M : WordModel A) (v₀ : Fin k₀ → ℕ) (W₀ : Fin l₀ → Set ℕ) :
    WordModel (Track A (k₀ + l₀)) where
  label i := (M.label i).map fun a ↦ (a, trackBits v₀ W₀ i)
  isSome_of_le hij hj := by
    -- Adding bits does not change whether a position carries a label.
    simp only [Option.isSome_map] at hj ⊢
    -- So the initial-segment property is inherited from `M`.
    exact M.isSome_of_le hij hj

/-- The expansion has the same domain. -/
@[simp]
theorem dom_expand (M : WordModel A) : (M.expand v₀ W₀).dom = M.dom := by
  -- Compare both domains position by position.
  ext i
  -- Mapping a label does not change whether it is defined.
  simp [dom, expand]

/-- The expansion has the original word model as its underlying model. -/
@[simp]
theorem base_expand (M : WordModel A) : (M.expand v₀ W₀).base = M := by
  -- Word models are equal iff their label functions are equal.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- Combine the two relabellings, which add and then forget the bits.
  simp only [base_label, expand, Option.map_map]
  -- Both labels are `none`, or both are the same letter.
  cases M.label i <;> rfl

/-- The designated sets of the expansion are the interpretations of the variables. -/
theorem tracks_expand {M : WordModel A} (hv : ∀ x, v₀ x ∈ M.dom) (hW : ∀ X, W₀ X ⊆ M.dom) :
    (M.expand v₀ W₀).tracks = Fin.append (α := Set ℕ) (fun x ↦ {v₀ x}) W₀ := by
  -- Compare the sets for an arbitrary variable `j`.
  funext j
  -- Compare both sets position by position.
  ext i
  -- Unfold the labels of the expansion.
  simp only [mem_tracks, expand, Option.map_eq_some_iff]
  -- Distinguish first-order from second-order variables.
  induction j using Fin.addCases with
  -- A first-order variable gives the singleton of its value.
  | left x =>
    -- The right-hand side is `{v₀ x}`.
    simp only [Fin.append_left, Set.mem_singleton_iff]
    -- Show both directions.
    constructor
    -- Take a position whose bit for `x` is set.
    · rintro ⟨_, ⟨a, -, rfl⟩, h⟩
      -- It is the value of `x`.
      exact trackBits_castAdd.mp h
    -- Conversely, take the position `v₀ x`.
    · rintro rfl
      -- It belongs to the domain by `hv`, so it carries a letter `a`.
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hv x)
      -- The bit of this position for `x` is set.
      exact ⟨_, ⟨a, ha, rfl⟩, trackBits_castAdd.mpr rfl⟩
  -- A second-order variable gives its interpretation.
  | right X =>
    -- The right-hand side is `W₀ X`.
    simp only [Fin.append_right]
    -- Show both directions.
    constructor
    -- Take a position whose bit for `X` is set.
    · rintro ⟨_, ⟨a, -, rfl⟩, h⟩
      -- It belongs to `W₀ X`.
      exact trackBits_natAdd.mp h
    -- Conversely, take a position of `W₀ X`.
    · intro h
      -- It belongs to the domain by `hW`, so it carries a letter `a`.
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hW X h)
      -- The bit of this position for `X` is set.
      exact ⟨_, ⟨a, ha, rfl⟩, trackBits_natAdd.mpr h⟩

/-- The label of a position in the expansion. -/
theorem expand_label_eq_some {M : WordModel A} {i : ℕ} {b : Track A (k₀ + l₀)} :
    (M.expand v₀ W₀).label i = some b ↔ M.label i = some b.1 ∧
      (∀ x, (b.2 (Fin.castAdd l₀ x) = true ↔ i = v₀ x)) ∧
        ∀ X, (b.2 (Fin.natAdd k₀ X) = true ↔ i ∈ W₀ X) := by
  -- Unfold the labels of the expansion.
  simp only [expand, Option.map_eq_some_iff]
  -- Show both directions.
  constructor
  -- A label of the expansion consists of a label `a` and the bits of the position.
  · rintro ⟨a, ha, rfl⟩
    -- These bits have the claimed properties.
    exact ⟨ha, fun _ ↦ trackBits_castAdd, fun _ ↦ trackBits_natAdd⟩
  -- Conversely, assume that the components of `b` have these properties.
  · rintro ⟨ha, hx, hX⟩
    -- It suffices to compare the bits of `b` with the bits of the position.
    refine ⟨b.1, ha, Prod.ext rfl (funext fun j ↦ ?_)⟩
    -- Distinguish first-order from second-order variables.
    induction j using Fin.addCases with
    -- The bit for `x` is set on both sides iff the position is the value of `x`.
    | left x => exact Bool.eq_iff_iff.mpr (trackBits_castAdd.trans (hx x).symm)
    -- The bit for `X` is set on both sides iff the position belongs to `W₀ X`.
    | right X => exact Bool.eq_iff_iff.mpr (trackBits_natAdd.trans (hX X).symm)

end WordModel

namespace Formula

open scoped Logic

/-- `(b ↔ φ)` for a Boolean `b`, as a formula that is `φ` or `¬φ`. -/
def ifBit {K L : ℕ} (b : Bool) (φ : Formula A K L) : Formula A K L := if b then φ else .not φ

/-- The test of whether a position `z` of a word model carries a letter of the track alphabet in
the expanded word model. -/
def letterTest {K L : ℕ} (ι₁ : Fin k₀ → Fin K) (ι₂ : Fin l₀ → Fin L) (b : Track A (k₀ + l₀))
    (z : Fin K) : Formula A K L :=
  (.label b.1 z) ∧
    ((⋀((List.finRange k₀).map fun x ↦ ifBit (b.2 (Fin.castAdd l₀ x)) (.eq z (ι₁ x)))) ∧
      (⋀((List.finRange l₀).map fun X ↦ ifBit (b.2 (Fin.natAdd k₀ X)) (.mem z (ι₂ X)))))

/-- Translate a formula over the track alphabet into a formula over `A`, where `ι₁` and `ι₂` give
the variables for the tracks and `ρ` and `τ` the variables of the formula. -/
def elimTrack : {k l : ℕ} → Formula (Track A (k₀ + l₀)) k l → {K L : ℕ} → (Fin k₀ → Fin K) →
    (Fin l₀ → Fin L) → (Fin k → Fin K) → (Fin l → Fin L) → Formula A K L
  -- Equality is translated along `ρ`.
  | _, _, .eq x y, _, _, _, _, ρ, _ => .eq (ρ x) (ρ y)
  | _, _, .succ x y, _, _, _, _, ρ, _ => .succ (ρ x) (ρ y)
  | _, _, .lt x y, _, _, _, _, ρ, _ => .lt (ρ x) (ρ y)
  -- A letter predicate over the track alphabet becomes a test of the variables.
  | _, _, .label b x, _, _, ι₁, ι₂, ρ, _ => letterTest ι₁ ι₂ b (ρ x)
  | _, _, .mem x X, _, _, _, _, ρ, τ => .mem (ρ x) (τ X)
  | _, _, .not φ, _, _, ι₁, ι₂, ρ, τ => .not (φ.elimTrack ι₁ ι₂ ρ τ)
  | _, _, .or φ ψ, _, _, ι₁, ι₂, ρ, τ => .or (φ.elimTrack ι₁ ι₂ ρ τ) (ψ.elimTrack ι₁ ι₂ ρ τ)
  -- The quantified variable is new and the last one of the context.
  | _, _, .ex₁ φ, K, _, ι₁, ι₂, ρ, τ =>
    .ex₁ (φ.elimTrack (fun x ↦ (ι₁ x).castSucc) ι₂
      (Fin.snoc (α := fun _ ↦ Fin (K + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last K)) τ)
  -- The quantified variable is new and the last one of the context.
  | _, _, .ex₂ φ, _, L, ι₁, ι₂, ρ, τ =>
    .ex₂ (φ.elimTrack ι₁ (fun X ↦ (ι₂ X).castSucc) ρ
      (Fin.snoc (α := fun _ ↦ Fin (L + 1)) (fun X ↦ (τ X).castSucc) (Fin.last L)))

section Fragments

variable {K L : ℕ} {ι₁ : Fin k₀ → Fin K} {ι₂ : Fin l₀ → Fin L} {ρ : Fin k → Fin K}
  {τ : Fin l → Fin L}

/-- `ifBit` preserves first-order formulas. -/
theorem isFirstOrder_ifBit {K L : ℕ} {b : Bool} {φ : Formula A K L} (h : φ.IsFirstOrder) :
    (ifBit b φ).IsFirstOrder := by
  -- Unfold `ifBit`.
  unfold ifBit
  -- Distinguish the value of the bit.
  split_ifs
  -- `φ` is first-order by assumption.
  · exact h
  -- `¬φ` is first-order if `φ` is.
  · exact h

/-- `ifBit` preserves formulas of MSO[S]. -/
theorem ltFree_ifBit {K L : ℕ} {b : Bool} {φ : Formula A K L} (h : φ.LtFree) :
    (ifBit b φ).LtFree := by
  -- Unfold `ifBit`.
  unfold ifBit
  -- Distinguish the value of the bit.
  split_ifs
  -- `φ` is in MSO[S] by assumption.
  · exact h
  -- `¬φ` is in MSO[S] if `φ` is.
  · exact h

/-- The letter test is a first-order formula. -/
theorem isFirstOrder_letterTest {b : Track A (k₀ + l₀)} {z : Fin K} :
    (letterTest ι₁ ι₂ b z).IsFirstOrder := by
  -- The test is a conjunction of a label test and two finite conjunctions.
  refine isFirstOrder_and.mpr ⟨trivial, isFirstOrder_and.mpr ⟨?_, ?_⟩⟩
  -- Consider a conjunct for a first-order variable.
  · refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
    -- It has the form `ifBit b (z = x)`.
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    -- This is first-order, as equality is atomic.
    exact isFirstOrder_ifBit trivial
  -- Consider a conjunct for a second-order variable.
  · refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
    -- It has the form `ifBit b (X(z))`.
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    -- This is first-order, as membership is atomic.
    exact isFirstOrder_ifBit trivial

/-- The letter test does not use the order relation. -/
theorem ltFree_letterTest {b : Track A (k₀ + l₀)} {z : Fin K} :
    (letterTest ι₁ ι₂ b z).LtFree := by
  -- The test is a conjunction of a label test and two finite conjunctions.
  refine ltFree_and.mpr ⟨trivial, ltFree_and.mpr ⟨?_, ?_⟩⟩
  -- Consider a conjunct for a first-order variable.
  · refine ltFree_finiteAnd fun φ hφ ↦ ?_
    -- It has the form `ifBit b (z = x)`.
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    -- Equality is not the order relation.
    exact ltFree_ifBit trivial
  -- Consider a conjunct for a second-order variable.
  · refine ltFree_finiteAnd fun φ hφ ↦ ?_
    -- It has the form `ifBit b (X(z))`.
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    -- Membership is not the order relation.
    exact ltFree_ifBit trivial

/-- The elimination of letter predicates preserves first-order formulas. -/
theorem isFirstOrder_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.IsFirstOrder) :
    (φ.elimTrack ι₁ ι₂ ρ τ).IsFirstOrder := by
  -- Induct on the formula, for all contexts of the translation.
  induction φ generalizing K L with
  -- A letter predicate becomes a first-order letter test.
  | label b x => exact isFirstOrder_letterTest
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact ih h
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  -- First-order quantifier: apply the induction hypothesis.
  | ex₁ φ ih => exact ih h
  -- A first-order formula has no second-order quantifier.
  | ex₂ φ ih => exact h.elim
  -- The other atomic formulas stay atomic.
  | _ => trivial

/-- The elimination of letter predicates preserves formulas of MSO[S]. -/
theorem ltFree_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.LtFree) :
    (φ.elimTrack ι₁ ι₂ ρ τ).LtFree := by
  -- Induct on the formula, for all contexts of the translation.
  induction φ generalizing K L with
  -- A formula of MSO[S] does not contain `x < y`.
  | lt x y => exact h.elim
  -- A letter predicate becomes a letter test, which does not use the order relation.
  | label b x => exact ltFree_letterTest
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact ih h
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  -- First-order quantifier: apply the induction hypothesis.
  | ex₁ φ ih => exact ih h
  -- Second-order quantifier: apply the induction hypothesis.
  | ex₂ φ ih => exact ih h
  -- The other atomic formulas stay atomic.
  | _ => trivial

/-- The elimination of letter predicates preserves EMSO formulas. -/
theorem isEMSO_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.IsEMSO) :
    (φ.elimTrack ι₁ ι₂ ρ τ).IsEMSO := by
  -- Induct on the definition of EMSO formulas.
  induction h generalizing K L with
  -- The first-order kernel stays first-order.
  | firstOrder h => exact .firstOrder (isFirstOrder_elimTrack h)
  -- The second-order prefix stays the same.
  | ex₂ _ ih => exact .ex₂ ih

end Fragments

section Semantics

variable {M : WordModel A} {K L : ℕ} {ι₁ : Fin k₀ → Fin K} {ι₂ : Fin l₀ → Fin L}
  {V : Fin K → ℕ} {U : Fin L → Set ℕ}

/-- `ifBit b φ` expresses that the bit `b` agrees with the truth of `φ`. -/
theorem satisfies_ifBit {b : Bool} {φ : Formula A K L} :
    Satisfies M V U (ifBit b φ) ↔ (b = true ↔ Satisfies M V U φ) := by
  -- If `b` is `true`, the formula is `φ`; otherwise, it is `¬φ`.
  cases b <;> simp [ifBit, Satisfies]

/-- The test `letterTest` decides the letters of the expanded word model. -/
theorem satisfies_letterTest (hι₁ : ∀ x, V (ι₁ x) = v₀ x) (hι₂ : ∀ X, U (ι₂ X) = W₀ X)
    {b : Track A (k₀ + l₀)} {z : Fin K} :
    Satisfies M V U (letterTest ι₁ ι₂ b z) ↔ (M.expand v₀ W₀).label (V z) = some b := by
  -- Describe the letters of the expansion by their components.
  rw [expand_label_eq_some]
  -- Evaluate the conjunctions and the bits.
  simp only [letterTest, satisfies_and, satisfies_finiteAnd, List.forall_mem_map, satisfies_ifBit,
    -- The conjunctions range over all variables, whose values are given by `hι₁` and `hι₂`.
    List.mem_finRange, forall_const, Satisfies, hι₁, hι₂]

/-- The elimination of letter predicates is correct: the translated formula holds in a word model
iff the formula holds in the expanded word model. -/
theorem satisfies_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} {ρ : Fin k → Fin K}
    {τ : Fin l → Fin L} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hι₁ : ∀ x, V (ι₁ x) = v₀ x) (hι₂ : ∀ X, U (ι₂ X) = W₀ X)
    (hρ : ∀ x, V (ρ x) = v x) (hτ : ∀ X, U (τ X) = W X) :
    Satisfies M V U (φ.elimTrack ι₁ ι₂ ρ τ) ↔ Satisfies (M.expand v₀ W₀) v W φ := by
  -- Induct on the formula, for all contexts of the translation.
  induction φ generalizing K L with
  -- Equality is translated along `ρ`.
  | eq x y => simp only [elimTrack, Satisfies, hρ]
  -- The successor relation is translated along `ρ`.
  | succ x y => simp only [elimTrack, Satisfies, hρ]
  -- The order relation is translated along `ρ`.
  | lt x y => simp only [elimTrack, Satisfies, hρ]
  -- A letter predicate becomes the test that decides the letters of the expansion.
  | label b x => simp only [elimTrack, Satisfies, satisfies_letterTest hι₁ hι₂, hρ]
  -- Membership is translated along `ρ` and `τ`.
  | mem x X => simp only [elimTrack, Satisfies, hρ, hτ]
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact not_congr (ih hι₁ hι₂ hρ hτ)
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hι₁ hι₂ hρ hτ) (ihψ hι₁ hι₂ hρ hτ)
  -- First-order quantifier: both sides range over the same domain.
  | @ex₁ k l φ ih =>
    -- Unfold the semantics; the domains of `M` and of its expansion agree.
    simp only [elimTrack, Satisfies, dom_expand]
    -- Apply the induction hypothesis to the interpretations extended by the same `p`.
    refine exists_congr fun p ↦ and_congr_right fun _ ↦ ih (fun x ↦ ?_) hι₂ (fun x ↦ ?_) hτ
    -- The variables of the tracks keep their interpretation.
    · simpa using hι₁ x
    -- Distinguish the new variable of the formula from the old ones.
    · induction x using Fin.lastCases with
      -- The new variable is interpreted by `p` on both sides.
      | last => simp
      -- The old variables are interpreted as before by `hρ`.
      | cast x => simpa using hρ x
  -- Second-order quantifier: both sides range over the same subsets of the domain.
  | @ex₂ k l φ ih =>
    -- Unfold the semantics; the domains of `M` and of its expansion agree.
    simp only [elimTrack, Satisfies, dom_expand]
    -- Apply the induction hypothesis to the interpretations extended by the same `P`.
    refine exists_congr fun P ↦ and_congr_right fun _ ↦ ih hι₁ (fun X ↦ ?_) hρ (fun X ↦ ?_)
    -- The variables of the tracks keep their interpretation.
    · simpa using hι₂ X
    -- Distinguish the new variable of the formula from the old ones.
    · induction X using Fin.lastCases with
      -- The new variable is interpreted by `P` on both sides.
      | last => simp
      -- The old variables are interpreted as before by `hτ`.
      | cast X => simpa using hτ X

/-- Translate a sentence over the track alphabet into a formula with free variables. -/
def ofTrackSentence (φ : Sentence (Track A (k₀ + l₀))) : Formula A k₀ l₀ :=
  φ.elimTrack id id Fin.elim0 Fin.elim0

/-- A formula obtained from a sentence over the track alphabet holds under an interpretation of its
free variables iff the sentence holds in the corresponding expanded word model. -/
theorem satisfies_ofTrackSentence {φ : Sentence (Track A (k₀ + l₀))} :
    Satisfies M v₀ W₀ (ofTrackSentence φ) ↔ φ.Holds (M.expand v₀ W₀) :=
  -- The tracks are the free variables themselves, and the sentence has no further variables.
  satisfies_elimTrack (fun _ ↦ rfl) (fun _ ↦ rfl) (fun x ↦ x.elim0) (fun X ↦ X.elim0)

end Semantics

end Formula

/-- A formula holds under an interpretation of its free variables by positions and subsets of the
domain iff its translation into MSO₀ holds in the expanded word model. -/
theorem Formula.models_toFormula₀_expand {M : WordModel A} (φ : Formula A k₀ l₀)
    (hv : ∀ x, v₀ x ∈ M.dom) (hW : ∀ X, W₀ X ⊆ M.dom) :
    φ.toFormula₀.Models (M.expand v₀ W₀) ↔ Satisfies M v₀ W₀ φ := by
  -- The expansion has `M` as underlying model and the interpretations as tracks.
  rw [Formula₀.Models, base_expand, tracks_expand hv hW, satisfies_toFormula₀ φ hv]

end Cslib.Logic.MSO
