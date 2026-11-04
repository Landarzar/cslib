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

@[simp]
theorem trackBits_castAdd {i : ℕ} {x : Fin k₀} :
    trackBits v₀ W₀ i (Fin.castAdd l₀ x) = true ↔ i = v₀ x := by
  simp [trackBits]

@[simp]
theorem trackBits_natAdd {i : ℕ} {X : Fin l₀} :
    trackBits v₀ W₀ i (Fin.natAdd k₀ X) = true ↔ i ∈ W₀ X := by
  simp [trackBits]

namespace WordModel

/-- The expansion of a word model by an interpretation of `k₀` first-order variables and `l₀`
second-order variables to a word model over the track alphabet. -/
noncomputable def expand (M : WordModel A) (v₀ : Fin k₀ → ℕ) (W₀ : Fin l₀ → Set ℕ) :
    WordModel (Track A (k₀ + l₀)) where
  label i := (M.label i).map fun a ↦ (a, trackBits v₀ W₀ i)
  isSome_of_le hij hj := by
    simp only [Option.isSome_map] at hj ⊢
    exact M.isSome_of_le hij hj

@[simp]
theorem dom_expand (M : WordModel A) : (M.expand v₀ W₀).dom = M.dom := by
  ext i
  simp [dom, expand]

@[simp]
theorem base_expand (M : WordModel A) : (M.expand v₀ W₀).base = M := by
  ext1
  funext i
  simp only [base_label, expand, Option.map_map]
  cases M.label i <;> rfl

/-- The designated sets of the expansion are the interpretations of the variables. -/
theorem tracks_expand {M : WordModel A} (hv : ∀ x, v₀ x ∈ M.dom) (hW : ∀ X, W₀ X ⊆ M.dom) :
    (M.expand v₀ W₀).tracks = Fin.append (α := Set ℕ) (fun x ↦ {v₀ x}) W₀ := by
  funext j
  ext i
  simp only [mem_tracks, expand, Option.map_eq_some_iff]
  induction j using Fin.addCases with
  | left x =>
    simp only [Fin.append_left, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨a, -, rfl⟩, h⟩
      exact trackBits_castAdd.mp h
    · rintro rfl
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hv x)
      exact ⟨_, ⟨a, ha, rfl⟩, trackBits_castAdd.mpr rfl⟩
  | right X =>
    simp only [Fin.append_right]
    constructor
    · rintro ⟨_, ⟨a, -, rfl⟩, h⟩
      exact trackBits_natAdd.mp h
    · intro h
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hW X h)
      exact ⟨_, ⟨a, ha, rfl⟩, trackBits_natAdd.mpr h⟩

/-- The label of a position in the expansion. -/
theorem expand_label_eq_some {M : WordModel A} {i : ℕ} {b : Track A (k₀ + l₀)} :
    (M.expand v₀ W₀).label i = some b ↔ M.label i = some b.1 ∧
      (∀ x, (b.2 (Fin.castAdd l₀ x) = true ↔ i = v₀ x)) ∧
        ∀ X, (b.2 (Fin.natAdd k₀ X) = true ↔ i ∈ W₀ X) := by
  simp only [expand, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, fun _ ↦ trackBits_castAdd, fun _ ↦ trackBits_natAdd⟩
  · rintro ⟨ha, hx, hX⟩
    refine ⟨b.1, ha, Prod.ext rfl (funext fun j ↦ ?_)⟩
    induction j using Fin.addCases with
    | left x => exact Bool.eq_iff_iff.mpr (trackBits_castAdd.trans (hx x).symm)
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
  | _, _, .eq x y, _, _, _, _, ρ, _ => .eq (ρ x) (ρ y)
  | _, _, .succ x y, _, _, _, _, ρ, _ => .succ (ρ x) (ρ y)
  | _, _, .lt x y, _, _, _, _, ρ, _ => .lt (ρ x) (ρ y)
  | _, _, .label b x, _, _, ι₁, ι₂, ρ, _ => letterTest ι₁ ι₂ b (ρ x)
  | _, _, .mem x X, _, _, _, _, ρ, τ => .mem (ρ x) (τ X)
  | _, _, .not φ, _, _, ι₁, ι₂, ρ, τ => .not (φ.elimTrack ι₁ ι₂ ρ τ)
  | _, _, .or φ ψ, _, _, ι₁, ι₂, ρ, τ => .or (φ.elimTrack ι₁ ι₂ ρ τ) (ψ.elimTrack ι₁ ι₂ ρ τ)
  | _, _, .ex₁ φ, K, _, ι₁, ι₂, ρ, τ =>
    .ex₁ (φ.elimTrack (fun x ↦ (ι₁ x).castSucc) ι₂
      (Fin.snoc (α := fun _ ↦ Fin (K + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last K)) τ)
  | _, _, .ex₂ φ, _, L, ι₁, ι₂, ρ, τ =>
    .ex₂ (φ.elimTrack ι₁ (fun X ↦ (ι₂ X).castSucc) ρ
      (Fin.snoc (α := fun _ ↦ Fin (L + 1)) (fun X ↦ (τ X).castSucc) (Fin.last L)))

section Fragments

variable {K L : ℕ} {ι₁ : Fin k₀ → Fin K} {ι₂ : Fin l₀ → Fin L} {ρ : Fin k → Fin K}
  {τ : Fin l → Fin L}

theorem isFirstOrder_ifBit {K L : ℕ} {b : Bool} {φ : Formula A K L} (h : φ.IsFirstOrder) :
    (ifBit b φ).IsFirstOrder := by
  unfold ifBit
  split_ifs
  · exact h
  · exact h

theorem ltFree_ifBit {K L : ℕ} {b : Bool} {φ : Formula A K L} (h : φ.LtFree) :
    (ifBit b φ).LtFree := by
  unfold ifBit
  split_ifs
  · exact h
  · exact h

theorem isFirstOrder_letterTest {b : Track A (k₀ + l₀)} {z : Fin K} :
    (letterTest ι₁ ι₂ b z).IsFirstOrder := by
  refine isFirstOrder_and.mpr ⟨trivial, isFirstOrder_and.mpr ⟨?_, ?_⟩⟩
  · refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    exact isFirstOrder_ifBit trivial
  · refine isFirstOrder_finiteAnd fun φ hφ ↦ ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    exact isFirstOrder_ifBit trivial

theorem ltFree_letterTest {b : Track A (k₀ + l₀)} {z : Fin K} :
    (letterTest ι₁ ι₂ b z).LtFree := by
  refine ltFree_and.mpr ⟨trivial, ltFree_and.mpr ⟨?_, ?_⟩⟩
  · refine ltFree_finiteAnd fun φ hφ ↦ ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    exact ltFree_ifBit trivial
  · refine ltFree_finiteAnd fun φ hφ ↦ ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hφ
    exact ltFree_ifBit trivial

theorem isFirstOrder_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.IsFirstOrder) :
    (φ.elimTrack ι₁ ι₂ ρ τ).IsFirstOrder := by
  induction φ generalizing K L with
  | label b x => exact isFirstOrder_letterTest
  | not φ ih => exact ih h
  | or φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | ex₁ φ ih => exact ih h
  | ex₂ φ ih => exact h.elim
  | _ => trivial

theorem ltFree_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.LtFree) :
    (φ.elimTrack ι₁ ι₂ ρ τ).LtFree := by
  induction φ generalizing K L with
  | lt x y => exact h.elim
  | label b x => exact ltFree_letterTest
  | not φ ih => exact ih h
  | or φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | ex₁ φ ih => exact ih h
  | ex₂ φ ih => exact ih h
  | _ => trivial

theorem isEMSO_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} (h : φ.IsEMSO) :
    (φ.elimTrack ι₁ ι₂ ρ τ).IsEMSO := by
  induction h generalizing K L with
  | firstOrder h => exact .firstOrder (isFirstOrder_elimTrack h)
  | ex₂ _ ih => exact .ex₂ ih

end Fragments

section Semantics

variable {M : WordModel A} {K L : ℕ} {ι₁ : Fin k₀ → Fin K} {ι₂ : Fin l₀ → Fin L}
  {V : Fin K → ℕ} {U : Fin L → Set ℕ}

theorem satisfies_ifBit {b : Bool} {φ : Formula A K L} :
    Satisfies M V U (ifBit b φ) ↔ (b = true ↔ Satisfies M V U φ) := by
  cases b <;> simp [ifBit, Satisfies]

/-- The test `letterTest` decides the letters of the expanded word model. -/
theorem satisfies_letterTest (hι₁ : ∀ x, V (ι₁ x) = v₀ x) (hι₂ : ∀ X, U (ι₂ X) = W₀ X)
    {b : Track A (k₀ + l₀)} {z : Fin K} :
    Satisfies M V U (letterTest ι₁ ι₂ b z) ↔ (M.expand v₀ W₀).label (V z) = some b := by
  rw [expand_label_eq_some]
  simp only [letterTest, satisfies_and, satisfies_finiteAnd, List.forall_mem_map, satisfies_ifBit,
    List.mem_finRange, forall_const, Satisfies, hι₁, hι₂]

/-- The elimination of letter predicates is correct: the translated formula holds in a word model
iff the formula holds in the expanded word model. -/
theorem satisfies_elimTrack {φ : Formula (Track A (k₀ + l₀)) k l} {ρ : Fin k → Fin K}
    {τ : Fin l → Fin L} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hι₁ : ∀ x, V (ι₁ x) = v₀ x) (hι₂ : ∀ X, U (ι₂ X) = W₀ X)
    (hρ : ∀ x, V (ρ x) = v x) (hτ : ∀ X, U (τ X) = W X) :
    Satisfies M V U (φ.elimTrack ι₁ ι₂ ρ τ) ↔ Satisfies (M.expand v₀ W₀) v W φ := by
  induction φ generalizing K L with
  | eq x y => simp only [elimTrack, Satisfies, hρ]
  | succ x y => simp only [elimTrack, Satisfies, hρ]
  | lt x y => simp only [elimTrack, Satisfies, hρ]
  | label b x => simp only [elimTrack, Satisfies, satisfies_letterTest hι₁ hι₂, hρ]
  | mem x X => simp only [elimTrack, Satisfies, hρ, hτ]
  | not φ ih => exact not_congr (ih hι₁ hι₂ hρ hτ)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hι₁ hι₂ hρ hτ) (ihψ hι₁ hι₂ hρ hτ)
  | @ex₁ k l φ ih =>
    simp only [elimTrack, Satisfies, dom_expand]
    refine exists_congr fun p ↦ and_congr_right fun _ ↦ ih (fun x ↦ ?_) hι₂ (fun x ↦ ?_) hτ
    · simpa using hι₁ x
    · induction x using Fin.lastCases with
      | last => simp
      | cast x => simpa using hρ x
  | @ex₂ k l φ ih =>
    simp only [elimTrack, Satisfies, dom_expand]
    refine exists_congr fun P ↦ and_congr_right fun _ ↦ ih hι₁ (fun X ↦ ?_) hρ (fun X ↦ ?_)
    · simpa using hι₂ X
    · induction X using Fin.lastCases with
      | last => simp
      | cast X => simpa using hτ X

/-- Translate a sentence over the track alphabet into a formula with free variables. -/
def ofTrackSentence (φ : Sentence (Track A (k₀ + l₀))) : Formula A k₀ l₀ :=
  φ.elimTrack id id Fin.elim0 Fin.elim0

/-- A formula obtained from a sentence over the track alphabet holds under an interpretation of its
free variables iff the sentence holds in the corresponding expanded word model. -/
theorem satisfies_ofTrackSentence {φ : Sentence (Track A (k₀ + l₀))} :
    Satisfies M v₀ W₀ (ofTrackSentence φ) ↔ φ.Holds (M.expand v₀ W₀) :=
  satisfies_elimTrack (fun _ ↦ rfl) (fun _ ↦ rfl) (fun x ↦ x.elim0) (fun X ↦ X.elim0)

end Semantics

end Formula

/-- A formula holds under an interpretation of its free variables by positions and subsets of the
domain iff its translation into MSO₀ holds in the expanded word model. -/
theorem Formula.models_toFormula₀_expand {M : WordModel A} (φ : Formula A k₀ l₀)
    (hv : ∀ x, v₀ x ∈ M.dom) (hW : ∀ X, W₀ X ⊆ M.dom) :
    φ.toFormula₀.Models (M.expand v₀ W₀) ↔ Satisfies M v₀ W₀ φ := by
  rw [Formula₀.Models, base_expand, tracks_expand hv hW, satisfies_toFormula₀ φ hv]

end Cslib.Logic.MSO
