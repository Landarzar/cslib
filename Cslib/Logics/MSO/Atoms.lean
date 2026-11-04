/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.Effective.Basic
public import Cslib.Logics.MSO.MSO0

/-! # Automata for the atomic formulas of MSO₀

This file presents the finite automata for the atomic formulas `X ⊆ Y`, `Sing(X)`, `Suc(X, Y)` and
`X ⊆ Q_a` of MSO₀, as used in the proof of Theorem 3.1 of [Thomas1997].

The automata are deterministic and their correctness is shown on finite words. As a Büchi
automaton, a deterministic automaton recognizes the ω-limit of its language. Since an ω-word
satisfies an atomic formula iff infinitely many of its prefixes do
(`ωlanguage_eq_omegaLim_of_isAtom`), the same automata also work for ω-words, as used in the proof
of Theorem 5.9 of [Thomas1997].

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open Automata WordModel Filter
open scoped ωSequence

universe u

variable {A : Type u} {n : ℕ}

section Tracks

variable {x : Track A n} {w : List (Track A n)} {j j' : Fin n}

/-- The membership in a track of `x :: w` splits into the first position and the track of `w`. -/
theorem forall_mem_tracks_cons_iff {Q : ℕ → Prop} :
    (∀ i, i ∈ (ofList (x :: w)).tracks j ↔ Q i) ↔
      (x.2 j = true ↔ Q 0) ∧ ∀ i, i ∈ (ofList w).tracks j ↔ Q (i + 1) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun i ↦ by simpa using h (i + 1)⟩
  · rintro ⟨h₀, h⟩ (_ | i)
    · simpa using h₀
    · simpa using h i

theorem tracks_subset_tracks_cons_iff :
    (ofList (x :: w)).tracks j ⊆ (ofList (x :: w)).tracks j' ↔
      (x.2 j = true → x.2 j' = true) ∧ (ofList w).tracks j ⊆ (ofList w).tracks j' := by
  constructor
  · intro h
    refine ⟨fun hj ↦ ?_, fun i hi ↦ ?_⟩
    · simpa using h (a := 0) (by simpa using hj)
    · simpa using h (a := i + 1) (by simpa using hi)
  · rintro ⟨h₀, h⟩ (_ | i) hi
    · simpa using h₀ (by simpa using hi)
    · simpa using h (by simpa using hi)

theorem forall_label_tracks_cons_iff {a : A} :
    (∀ p ∈ (ofList (x :: w)).tracks j, (ofList (x :: w)).base.label p = some a) ↔
      (x.2 j = true → x.1 = a) ∧
        ∀ p ∈ (ofList w).tracks j, (ofList w).base.label p = some a := by
  constructor
  · intro h
    refine ⟨fun hj ↦ ?_, fun i hi ↦ ?_⟩
    · simpa using h 0 (by simpa using hj)
    · simpa using h (i + 1) (by simpa using hi)
  · rintro ⟨h₀, h⟩ (_ | i) hi
    · simpa using h₀ (by simpa using hi)
    · simpa using h i (by simpa using hi)

/-- A set is the singleton `{p}` iff exactly `p` is a member. -/
theorem eq_singleton_iff_forall {T : Set ℕ} {p : ℕ} : T = {p} ↔ ∀ i, i ∈ T ↔ i = p := by
  simp only [Set.ext_iff, Set.mem_singleton_iff]

end Tracks

/-- The automaton for `X ⊆ Y`. -/
def subDFA (X Y : Fin n) : EffectiveDFA (Track A n) where
  State := Bool
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ s && (!x.2 X || x.2 Y)⟩, true⟩, {true}⟩
  decAccept s := inferInstanceAs (Decidable (s = true))

theorem language_subDFA (X Y : Fin n) :
    (subDFA X Y : EffectiveDFA (Track A n)).language = (Formula₀.sub X Y).language := by
  ext w
  refine ((subDFA X Y).mem_language_iff_of_residual
    (fun (s : Bool) w ↦ s = true ∧ (ofList w).tracks X ⊆ (ofList w).tracks Y) ?_ ?_ w).trans ?_
  · intro (s : Bool)
    change (s = true ∧ _) ↔ s = true
    simp [Set.subset_def, mem_tracks]
  · intro (s : Bool) x w
    rw [tracks_subset_tracks_cons_iff]
    change _ ↔ (s && (!x.2 X || x.2 Y)) = true ∧ _
    cases s <;> cases x.2 X <;> cases x.2 Y <;> simp
  · exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩

/-- The automaton for `X ⊆ Q_a`. -/
def subLabelDFA [DecidableEq A] (X : Fin n) (a : A) : EffectiveDFA (Track A n) where
  State := Bool
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ s && (!x.2 X || decide (x.1 = a))⟩, true⟩, {true}⟩
  decAccept s := inferInstanceAs (Decidable (s = true))

theorem language_subLabelDFA [DecidableEq A] (X : Fin n) (a : A) :
    (subLabelDFA X a).language = (Formula₀.subLabel X a).language := by
  ext w
  refine ((subLabelDFA X a).mem_language_iff_of_residual
    (fun (s : Bool) w ↦ s = true ∧ ∀ p ∈ (ofList w).tracks X, (ofList w).base.label p = some a)
    ?_ ?_ w).trans ?_
  · intro (s : Bool)
    change (s = true ∧ _) ↔ s = true
    simp [mem_tracks]
  · intro (s : Bool) x w
    rw [forall_label_tracks_cons_iff]
    change _ ↔ (s && (!x.2 X || decide (x.1 = a))) = true ∧ _
    cases s <;> cases x.2 X <;> simp
  · exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩

/-- The transition function of the automaton for `Sing(X)`. State `0` means that no position of `X`
has been seen, state `1` that exactly one has been seen, and `2` that there have been more. -/
def singStep : Fin 3 → Bool → Fin 3
  | 0, false => 0
  | 0, true => 1
  | 1, false => 1
  | 1, true => 2
  | 2, _ => 2

/-- The automaton for `Sing(X)`. -/
def singDFA (X : Fin n) : EffectiveDFA (Track A n) where
  State := Fin 3
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ singStep s (x.2 X)⟩, 0⟩, {1}⟩
  decAccept s := inferInstanceAs (Decidable (s = 1))

/-- The words accepted from a state of the automaton for `Sing(X)`. -/
def singResidual (X : Fin n) : Fin 3 → List (Track A n) → Prop
  | 0, w => ∃ p, ∀ i, i ∈ (ofList w).tracks X ↔ i = p
  | 1, w => ∀ i, i ∈ (ofList w).tracks X ↔ False
  | 2, _ => False

theorem singResidual_nil (X : Fin n) :
    (s : Fin 3) → singResidual (A := A) X s [] ↔ s = 1
  | 0 => by simp [singResidual, mem_tracks]
  | 1 => by simp [singResidual, mem_tracks]
  | 2 => by simp [singResidual]

theorem singResidual_cons (X : Fin n) (x : Track A n) (w : List (Track A n)) :
    (s : Fin 3) → singResidual X s (x :: w) ↔ singResidual X (singStep s (x.2 X)) w
  | 0 => by
    change (∃ p, ∀ i, i ∈ (ofList (x :: w)).tracks X ↔ i = p) ↔ _
    simp only [forall_mem_tracks_cons_iff]
    cases hb : x.2 X
    · change _ ↔ ∃ p, ∀ i, i ∈ (ofList w).tracks X ↔ i = p
      constructor
      · rintro ⟨_ | p, h₀, h⟩
        · simp at h₀
        · exact ⟨p, by simpa using h⟩
      · rintro ⟨p, h⟩
        exact ⟨p + 1, by simp, by simpa using h⟩
    · change _ ↔ ∀ i, i ∈ (ofList w).tracks X ↔ False
      constructor
      · rintro ⟨p, h₀, h⟩
        obtain rfl : 0 = p := h₀.mp rfl
        simpa using h
      · exact fun h ↦ ⟨0, by simp, by simpa using h⟩
  | 1 => by
    change (∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ↔ _
    rw [forall_mem_tracks_cons_iff]
    cases hb : x.2 X
    · change _ ↔ ∀ i, i ∈ (ofList w).tracks X ↔ False
      simp
    · change _ ↔ False
      simp
  | 2 => Iff.rfl

theorem language_singDFA (X : Fin n) :
    (singDFA X : EffectiveDFA (Track A n)).language = (Formula₀.sing X).language := by
  ext w
  refine ((singDFA X).mem_language_iff_of_residual (singResidual X) (singResidual_nil X)
    (fun s x w ↦ singResidual_cons X x w s) w).trans ?_
  simp only [Formula₀.mem_language, Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
  rfl

/-- The transition function of the automaton for `Suc(X, Y)`. State `0` means that neither position
has been seen, state `1` that the position of `X` was the last one, and state `2` that both have
been seen. State `3` is a sink for all words that violate `Suc(X, Y)`. -/
def sucStep : Fin 4 → Bool → Bool → Fin 4
  | 0, false, false => 0
  | 0, true, false => 1
  | 1, false, true => 2
  | 2, false, false => 2
  | _, _, _ => 3

/-- The automaton for `Suc(X, Y)`. -/
def sucDFA (X Y : Fin n) : EffectiveDFA (Track A n) where
  State := Fin 4
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ sucStep s (x.2 X) (x.2 Y)⟩, 0⟩, {2}⟩
  decAccept s := inferInstanceAs (Decidable (s = 2))

/-- The words accepted from a state of the automaton for `Suc(X, Y)`. -/
def sucResidual (X Y : Fin n) : Fin 4 → List (Track A n) → Prop
  | 0, w => ∃ p, (∀ i, i ∈ (ofList w).tracks X ↔ i = p) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ i = p + 1
  | 1, w => (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ i = 0
  | 2, w => (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ False
  | 3, _ => False

theorem sucResidual_nil (X Y : Fin n) :
    (s : Fin 4) → sucResidual (A := A) X Y s [] ↔ s = 2
  | 0 => by simp [sucResidual, mem_tracks]
  | 1 => by simp [sucResidual, mem_tracks]
  | 2 => by simp [sucResidual, mem_tracks]
  | 3 => by simp [sucResidual]

theorem sucResidual_cons (X Y : Fin n) (x : Track A n) (w : List (Track A n)) :
    (s : Fin 4) → sucResidual X Y s (x :: w) ↔ sucResidual X Y (sucStep s (x.2 X) (x.2 Y)) w
  | 0 => by
    change (∃ p, (∀ i, i ∈ (ofList (x :: w)).tracks X ↔ i = p) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ i = p + 1) ↔ _
    simp only [forall_mem_tracks_cons_iff]
    cases hX : x.2 X <;> cases hY : x.2 Y
    · change _ ↔ ∃ p, (∀ i, i ∈ (ofList w).tracks X ↔ i = p) ∧
        ∀ i, i ∈ (ofList w).tracks Y ↔ i = p + 1
      constructor
      · rintro ⟨_ | p, ⟨h₀, hX'⟩, -, hY'⟩
        · simp at h₀
        · exact ⟨p, by simpa using hX', by simpa using hY'⟩
      · rintro ⟨p, hX', hY'⟩
        exact ⟨p + 1, ⟨by simp, by simpa using hX'⟩, by simp, by simpa using hY'⟩
    · change _ ↔ False
      simp
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ i = 0
      constructor
      · rintro ⟨p, ⟨h₀, hX'⟩, -, hY'⟩
        obtain rfl : 0 = p := h₀.mp rfl
        exact ⟨by simpa using hX', by simpa using hY'⟩
      · rintro ⟨hX', hY'⟩
        exact ⟨0, ⟨by simp, by simpa using hX'⟩, by simp, by simpa using hY'⟩
    · change _ ↔ False
      simp
  | 1 => by
    change ((∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ i = 0) ↔ _
    simp only [forall_mem_tracks_cons_iff]
    cases hX : x.2 X <;> cases hY : x.2 Y
    · change _ ↔ False
      simp
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ False
      simp
    · change _ ↔ False
      simp
    · change _ ↔ False
      simp
  | 2 => by
    change ((∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ False) ↔ _
    simp only [forall_mem_tracks_cons_iff]
    cases hX : x.2 X <;> cases hY : x.2 Y
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ False
      simp
    · change _ ↔ False
      simp
    · change _ ↔ False
      simp
    · change _ ↔ False
      simp
  | 3 => Iff.rfl

theorem language_sucDFA (X Y : Fin n) :
    (sucDFA X Y : EffectiveDFA (Track A n)).language = (Formula₀.suc X Y).language := by
  ext w
  refine ((sucDFA X Y).mem_language_iff_of_residual (sucResidual X Y) (sucResidual_nil X Y)
    (fun s x w ↦ sucResidual_cons X Y x w s) w).trans ?_
  simp only [Formula₀.mem_language, Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
  rfl

section OmegaWords

variable {α : ωSequence (Track A n)} {j : Fin n} {i m : ℕ}

theorem getElem?_extract_zero : (α.extract 0 m)[i]? = if i < m then some (α i) else none := by
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa [ωSequence.length_extract] using h),
      ωSequence.get_extract (by simpa using h)]
    simp
  · exact List.getElem?_eq_none (by simpa [ωSequence.length_extract] using h)

theorem mem_tracks_extract :
    i ∈ (ofList (α.extract 0 m)).tracks j ↔ i < m ∧ i ∈ (ofOmega α).tracks j := by
  simp only [mem_tracks, ofList_label, ofOmega_label, getElem?_extract_zero]
  split_ifs with h <;> simp [h]

theorem base_label_extract (h : i < m) :
    (ofList (α.extract 0 m)).base.label i = (ofOmega α).base.label i := by
  simp only [base_label, ofList_label, ofOmega_label, getElem?_extract_zero, h, ↓reduceIte]

end OmegaWords

/-- The atomic formulas of MSO₀. -/
inductive Formula₀.IsAtom : {n : ℕ} → Formula₀ A n → Prop where
  | sub {n : ℕ} (X Y : Fin n) : IsAtom (.sub X Y)
  | sing {n : ℕ} (X : Fin n) : IsAtom (.sing X)
  | suc {n : ℕ} (X Y : Fin n) : IsAtom (.suc X Y)
  | subLabel {n : ℕ} (X : Fin n) (a : A) : IsAtom (.subLabel X a)

/-- An ω-word satisfies an atomic formula iff infinitely many of its prefixes do. -/
theorem ωlanguage_eq_omegaLim_of_isAtom {φ : Formula₀ A n} (hφ : φ.IsAtom) :
    φ.ωlanguage = φ.language↗ω := by
  ext α
  change φ.Models (ofOmega α) ↔ ∃ᶠ m in atTop, φ.Models (ofList (α.extract 0 m))
  cases hφ with
  | sub X Y =>
    simp only [Formula₀.Models, Formula₀.Satisfies]
    constructor
    · intro h
      refine Frequently.of_forall fun m i hi ↦ ?_
      rw [mem_tracks_extract] at hi ⊢
      exact ⟨hi.1, h hi.2⟩
    · intro h i hi
      obtain ⟨m, hm, hsub⟩ := frequently_atTop.mp h (i + 1)
      exact (mem_tracks_extract.mp (hsub (mem_tracks_extract.mpr ⟨hm, hi⟩))).2
  | subLabel X a =>
    simp only [Formula₀.Models, Formula₀.Satisfies]
    constructor
    · intro h
      refine Frequently.of_forall fun m i hi ↦ ?_
      obtain ⟨him, hi⟩ := mem_tracks_extract.mp hi
      rw [base_label_extract him]
      exact h i hi
    · intro h i hi
      obtain ⟨m, hm, hsub⟩ := frequently_atTop.mp h (i + 1)
      have := hsub i (mem_tracks_extract.mpr ⟨hm, hi⟩)
      rwa [base_label_extract hm] at this
  | sing X =>
    simp only [Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
    constructor
    · rintro ⟨p, hp⟩
      refine Eventually.frequently ((eventually_gt_atTop p).mono fun m hm ↦ ⟨p, fun i ↦ ?_⟩)
      rw [mem_tracks_extract, hp]
      omega
    · intro h
      obtain ⟨m₀, -, p, hp⟩ := frequently_atTop.mp h 0
      refine ⟨p, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩⟩
      · obtain ⟨m, hm, p', hp'⟩ := frequently_atTop.mp h (max p q + 1)
        have hpm : p ∈ (ofList (α.extract 0 m)).tracks X :=
          mem_tracks_extract.mpr ⟨by omega, (mem_tracks_extract.mp ((hp p).mpr rfl)).2⟩
        have hqm : q ∈ (ofList (α.extract 0 m)).tracks X :=
          mem_tracks_extract.mpr ⟨by omega, hq⟩
        rw [(hp' q).mp hqm, (hp' p).mp hpm]
      · rintro rfl
        exact (mem_tracks_extract.mp ((hp q).mpr rfl)).2
  | suc X Y =>
    simp only [Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
    constructor
    · rintro ⟨p, hX, hY⟩
      refine Eventually.frequently
        ((eventually_gt_atTop (p + 1)).mono fun m hm ↦ ⟨p, fun i ↦ ?_, fun i ↦ ?_⟩)
      · rw [mem_tracks_extract, hX]
        omega
      · rw [mem_tracks_extract, hY]
        omega
    · intro h
      obtain ⟨m₀, -, p, hpX, hpY⟩ := frequently_atTop.mp h 0
      have hpX' := (mem_tracks_extract.mp ((hpX p).mpr rfl)).2
      have hpY' := (mem_tracks_extract.mp ((hpY (p + 1)).mpr rfl)).2
      refine ⟨p, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩⟩
      · obtain ⟨m, hm, p', hp', -⟩ := frequently_atTop.mp h (max p q + 1)
        rw [(hp' q).mp (mem_tracks_extract.mpr ⟨by omega, hq⟩),
          (hp' p).mp (mem_tracks_extract.mpr ⟨by omega, hpX'⟩)]
      · rintro rfl
        exact hpX'
      · obtain ⟨m, hm, p', -, hp'⟩ := frequently_atTop.mp h (max (p + 1) q + 1)
        rw [(hp' q).mp (mem_tracks_extract.mpr ⟨by omega, hq⟩)]
        have := (hp' (p + 1)).mp (mem_tracks_extract.mpr ⟨by omega, hpY'⟩)
        omega
      · rintro rfl
        exact hpY'

end Cslib.Logic.MSO
