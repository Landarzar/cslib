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

## Proof technique

To prove that a deterministic automaton is correct, each state `s` is assigned a *residual
property*, which describes the words accepted from `s` (for example `singResidual`). By
`EffectiveDFA.mem_language_iff_of_residual`, it then suffices to check that the empty word satisfies
the property exactly for the accepting states, and that the property of `s` for `x :: w` is the
property of the successor state for `w`. Since words are consumed from the left, a position of
`x :: w` is either the first letter or a shifted position of `w`, which is described by
`forall_mem_tracks_cons_iff`.

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
  -- Show both directions.
  constructor
  -- Assume the statement for all positions of `x :: w`.
  · intro h
    -- Position `0` concerns `x`, and position `i + 1` concerns the position `i` of `w`.
    exact ⟨by simpa using h 0, fun i ↦ by simpa using h (i + 1)⟩
  -- Conversely, distinguish position `0` from positions `i + 1`.
  · rintro ⟨h₀, h⟩ (_ | i)
    -- Position `0` is the first letter.
    · simpa using h₀
    -- Position `i + 1` is the position `i` of `w`.
    · simpa using h i

/-- An inclusion of tracks of `x :: w` splits into the first position and the tracks of `w`. -/
theorem tracks_subset_tracks_cons_iff :
    (ofList (x :: w)).tracks j ⊆ (ofList (x :: w)).tracks j' ↔
      (x.2 j = true → x.2 j' = true) ∧ (ofList w).tracks j ⊆ (ofList w).tracks j' := by
  -- Show both directions.
  constructor
  -- Assume the inclusion for `x :: w`.
  · intro h
    -- Consider the first letter and the positions of `w`.
    refine ⟨fun hj ↦ ?_, fun i hi ↦ ?_⟩
    -- Position `0` gives the implication for the bits of `x`.
    · simpa using h (a := 0) (by simpa using hj)
    -- Position `i + 1` gives the inclusion for `w`.
    · simpa using h (a := i + 1) (by simpa using hi)
  -- Conversely, distinguish position `0` from positions `i + 1`.
  · rintro ⟨h₀, h⟩ (_ | i) hi
    -- Position `0` is covered by the implication for the bits of `x`.
    · simpa using h₀ (by simpa using hi)
    -- Position `i + 1` is covered by the inclusion for `w`.
    · simpa using h (by simpa using hi)

/-- A statement about the labels on a track of `x :: w` splits into the first position and the track
of `w`. -/
theorem forall_label_tracks_cons_iff {a : A} :
    (∀ p ∈ (ofList (x :: w)).tracks j, (ofList (x :: w)).base.label p = some a) ↔
      (x.2 j = true → x.1 = a) ∧
        ∀ p ∈ (ofList w).tracks j, (ofList w).base.label p = some a := by
  -- Show both directions.
  constructor
  -- Assume the statement for `x :: w`.
  · intro h
    -- Consider the first letter and the positions of `w`.
    refine ⟨fun hj ↦ ?_, fun i hi ↦ ?_⟩
    -- Position `0` gives the statement for the letter `x`.
    · simpa using h 0 (by simpa using hj)
    -- Position `i + 1` gives the statement for `w`.
    · simpa using h (i + 1) (by simpa using hi)
  -- Conversely, distinguish position `0` from positions `i + 1`.
  · rintro ⟨h₀, h⟩ (_ | i) hi
    -- Position `0` is covered by the statement for the letter `x`.
    · simpa using h₀ (by simpa using hi)
    -- Position `i + 1` is covered by the statement for `w`.
    · simpa using h i (by simpa using hi)

/-- A set is the singleton `{p}` iff exactly `p` is a member. -/
theorem eq_singleton_iff_forall {T : Set ℕ} {p : ℕ} : T = {p} ↔ ∀ i, i ∈ T ↔ i = p := by
  -- A set equality is extensional, and being in `{p}` means being equal to `p`.
  simp only [Set.ext_iff, Set.mem_singleton_iff]

end Tracks

/-- The automaton for `X ⊆ Y`. The state `true` means that the inclusion has not been violated, and
the state `false` is a sink. -/
def subDFA (X Y : Fin n) : EffectiveDFA (Track A n) where
  State := Bool
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ s && (!x.2 X || x.2 Y)⟩, true⟩, {true}⟩
  decAccept s := inferInstanceAs (Decidable (s = true))

/-- The automaton for `X ⊆ Y` is correct. -/
theorem language_subDFA (X Y : Fin n) :
    (subDFA X Y : EffectiveDFA (Track A n)).language = (Formula₀.sub X Y).language := by
  -- Compare on a word `w`.
  ext w
  -- Apply the method of residual properties.
  refine ((subDFA X Y).mem_language_iff_of_residual
    -- The property states that `s` is `true` and that the inclusion holds for the remaining word.
    (fun (s : Bool) w ↦ s = true ∧ (ofList w).tracks X ⊆ (ofList w).tracks Y) ?_ ?_ w).trans ?_
  -- The empty word:
  · intro (s : Bool)
    -- Being accepting means being `true`.
    change (s = true ∧ _) ↔ s = true
    -- The tracks of the empty word are empty, so the inclusion holds.
    simp [Set.subset_def, mem_tracks]
  -- A word `x :: w`:
  · intro (s : Bool) x w
    -- Split the inclusion into the first position and the tracks of `w`.
    rw [tracks_subset_tracks_cons_iff]
    -- Unfold the transition function on the right-hand side.
    change _ ↔ (s && (!x.2 X || x.2 Y)) = true ∧ _
    -- Check all values of the state and of the two bits.
    cases s <;> cases x.2 X <;> cases x.2 Y <;> simp
  -- From the start state `true`, the property is the inclusion itself.
  · exact ⟨fun h ↦ h.2, fun h ↦ ⟨rfl, h⟩⟩

/-- The automaton for `X ⊆ Q_a`. The state `true` means that the inclusion has not been violated,
and the state `false` is a sink. -/
def subLabelDFA [DecidableEq A] (X : Fin n) (a : A) : EffectiveDFA (Track A n) where
  State := Bool
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨⟨⟨fun s x ↦ s && (!x.2 X || decide (x.1 = a))⟩, true⟩, {true}⟩
  decAccept s := inferInstanceAs (Decidable (s = true))

/-- The automaton for `X ⊆ Q_a` is correct. -/
theorem language_subLabelDFA [DecidableEq A] (X : Fin n) (a : A) :
    (subLabelDFA X a).language = (Formula₀.subLabel X a).language := by
  -- Compare on a word `w`.
  ext w
  -- Apply the method of residual properties.
  refine ((subLabelDFA X a).mem_language_iff_of_residual
    -- The property states that `s` is `true` and that the labels are right on the remaining word.
    (fun (s : Bool) w ↦ s = true ∧ ∀ p ∈ (ofList w).tracks X, (ofList w).base.label p = some a)
    -- The goals are the empty word, a nonempty word, and the start state.
    ?_ ?_ w).trans ?_
  -- The empty word:
  · intro (s : Bool)
    -- Being accepting means being `true`.
    change (s = true ∧ _) ↔ s = true
    -- The track of the empty word is empty, so there is no label to check.
    simp [mem_tracks]
  -- A word `x :: w`:
  · intro (s : Bool) x w
    -- Split the statement into the first position and the track of `w`.
    rw [forall_label_tracks_cons_iff]
    -- Unfold the transition function on the right-hand side.
    change _ ↔ (s && (!x.2 X || decide (x.1 = a))) = true ∧ _
    -- Check all values of the state and of the bit.
    cases s <;> cases x.2 X <;> simp
  -- From the start state `true`, the property is the statement about the labels itself.
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

/-- The empty word is accepted from a state of the automaton for `Sing(X)` iff the state is `1`. -/
theorem singResidual_nil (X : Fin n) :
    (s : Fin 3) → singResidual (A := A) X s [] ↔ s = 1
  -- In state `0`, the empty word has no position of `X`, so `X` is no singleton.
  | 0 => by simp [singResidual, mem_tracks]
  -- In state `1`, no further position of `X` is needed.
  | 1 => by simp [singResidual, mem_tracks]
  -- State `2` is a sink.
  | 2 => by simp [singResidual]

/-- The residual properties for `Sing(X)` follow the transitions of the automaton. -/
theorem singResidual_cons (X : Fin n) (x : Track A n) (w : List (Track A n)) :
    (s : Fin 3) → singResidual X s (x :: w) ↔ singResidual X (singStep s (x.2 X)) w
  -- State `0`: `X` has to be a singleton in the remaining word.
  | 0 => by
    -- Unfold the residual property.
    change (∃ p, ∀ i, i ∈ (ofList (x :: w)).tracks X ↔ i = p) ↔ _
    -- Split the statement into the first position and the rest of the word.
    simp only [forall_mem_tracks_cons_iff]
    -- Distinguish the bit of the first letter.
    cases hb : x.2 X
    -- The bit is unset, so the automaton stays in state `0`.
    · change _ ↔ ∃ p, ∀ i, i ∈ (ofList w).tracks X ↔ i = p
      -- Show both directions.
      constructor
      -- Distinguish whether the position of `X` is `0`.
      · rintro ⟨_ | p, h₀, h⟩
        -- This is impossible, as the bit is unset.
        · simp at h₀
        -- For `p + 1`, the position `p` works for `w`.
        · exact ⟨p, by simpa using h⟩
      -- Conversely, take the position `p` for `w`.
      · rintro ⟨p, h⟩
        -- Then `p + 1` works for `x :: w`.
        exact ⟨p + 1, by simp, by simpa using h⟩
    -- The bit is set, so the automaton moves to state `1`.
    · change _ ↔ ∀ i, i ∈ (ofList w).tracks X ↔ False
      -- Show both directions.
      constructor
      -- Take the position `p` of `X` in `x :: w`.
      · rintro ⟨p, h₀, h⟩
        -- As the bit is set, this position is `0`.
        obtain rfl : 0 = p := h₀.mp rfl
        -- So no position of `w` belongs to `X`.
        simpa using h
      -- Conversely, position `0` is the only position of `X`.
      · exact fun h ↦ ⟨0, by simp, by simpa using h⟩
  -- State `1`: `X` has no further position.
  | 1 => by
    -- Unfold the residual property.
    change (∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ↔ _
    -- Split the statement into the first position and the rest of the word.
    rw [forall_mem_tracks_cons_iff]
    -- Distinguish the bit of the first letter.
    cases hb : x.2 X
    -- The bit is unset, so the automaton stays in state `1`.
    · change _ ↔ ∀ i, i ∈ (ofList w).tracks X ↔ False
      -- What remains is the statement for `w`.
      simp
    -- The bit is set, so the automaton moves to the sink `2`.
    · change _ ↔ False
      -- A further position contradicts the residual property.
      simp
  -- State `2` is a sink, whose residual property is `False`.
  | 2 => Iff.rfl

/-- The automaton for `Sing(X)` is correct. -/
theorem language_singDFA (X : Fin n) :
    (singDFA X : EffectiveDFA (Track A n)).language = (Formula₀.sing X).language := by
  -- Compare on a word `w`.
  ext w
  -- Use the residual properties, which hold for the empty word exactly in state `1`.
  refine ((singDFA X).mem_language_iff_of_residual (singResidual X) (singResidual_nil X)
    -- The residual properties follow the transitions by `singResidual_cons`.
    (fun s x w ↦ singResidual_cons X x w s) w).trans ?_
  -- Express the singleton pointwise as `i ∈ X ↔ i = p`.
  simp only [Formula₀.mem_language, Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
  -- This is the residual property of state `0`.
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

/-- The empty word is accepted from a state of the automaton for `Suc(X, Y)` iff the state is `2`.
-/
theorem sucResidual_nil (X Y : Fin n) :
    (s : Fin 4) → sucResidual (A := A) X Y s [] ↔ s = 2
  -- State `0`: the empty word has no position in `X`.
  | 0 => by simp [sucResidual, mem_tracks]
  -- State `1`: the empty word has no position in `Y`.
  | 1 => by simp [sucResidual, mem_tracks]
  -- State `2`: both tracks are empty, as required.
  | 2 => by simp [sucResidual, mem_tracks]
  -- State `3` is a sink.
  | 3 => by simp [sucResidual]

/-- The residual properties for `Suc(X, Y)` follow the transitions of the automaton. -/
theorem sucResidual_cons (X Y : Fin n) (x : Track A n) (w : List (Track A n)) :
    (s : Fin 4) → sucResidual X Y s (x :: w) ↔ sucResidual X Y (sucStep s (x.2 X) (x.2 Y)) w
  -- State `0`: neither position has been seen.
  | 0 => by
    -- Unfold the residual property.
    change (∃ p, (∀ i, i ∈ (ofList (x :: w)).tracks X ↔ i = p) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ i = p + 1) ↔ _
    -- Split the statement into the first position and the rest of the word.
    simp only [forall_mem_tracks_cons_iff]
    -- Distinguish the bits of the first letter for `X` and `Y`.
    cases hX : x.2 X <;> cases hY : x.2 Y
    -- Both bits are unset, so the automaton stays in state `0`.
    · change _ ↔ ∃ p, (∀ i, i ∈ (ofList w).tracks X ↔ i = p) ∧
        ∀ i, i ∈ (ofList w).tracks Y ↔ i = p + 1
      -- Show both directions.
      constructor
      -- Distinguish whether the position of `X` is `0`.
      · rintro ⟨_ | p, ⟨h₀, hX'⟩, -, hY'⟩
        -- This is impossible, as the bit of `X` is unset.
        · simp at h₀
        -- For `p + 1`, the position `p` works for `w`.
        · exact ⟨p, by simpa using hX', by simpa using hY'⟩
      -- Conversely, take the position `p` for `w`.
      · rintro ⟨p, hX', hY'⟩
        -- Then `p + 1` works for `x :: w`.
        exact ⟨p + 1, ⟨by simp, by simpa using hX'⟩, by simp, by simpa using hY'⟩
    -- Only the bit of `Y` is set: `Y` comes before `X`, so the automaton moves to the sink.
    · change _ ↔ False
      -- Position `0` cannot be the successor `p + 1`.
      simp
    -- Only the bit of `X` is set, so the automaton moves to state `1`.
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ i = 0
      -- Show both directions.
      constructor
      -- Take the position `p` of `X` in `x :: w`.
      · rintro ⟨p, ⟨h₀, hX'⟩, -, hY'⟩
        -- As the bit of `X` is set, this position is `0`.
        obtain rfl : 0 = p := h₀.mp rfl
        -- So `X` has no position in `w`, and `Y` has the position `0` in `w`.
        exact ⟨by simpa using hX', by simpa using hY'⟩
      -- Conversely, assume this statement about `w`.
      · rintro ⟨hX', hY'⟩
        -- Then position `0` works for `x :: w`.
        exact ⟨0, ⟨by simp, by simpa using hX'⟩, by simp, by simpa using hY'⟩
    -- Both bits are set: `X` and `Y` cannot share a position, so the automaton moves to the sink.
    · change _ ↔ False
      -- Position `0` cannot be both `p` and `p + 1`.
      simp
  -- State `1`: the position of `Y` has to come now.
  | 1 => by
    -- Unfold the residual property.
    change ((∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ i = 0) ↔ _
    -- Split the statement into the first position and the rest of the word.
    simp only [forall_mem_tracks_cons_iff]
    -- Distinguish the bits of the first letter for `X` and `Y`.
    cases hX : x.2 X <;> cases hY : x.2 Y
    -- Both bits are unset: the position of `Y` is missing, so the automaton moves to the sink.
    · change _ ↔ False
      -- Position `0` has to belong to `Y`.
      simp
    -- Only the bit of `Y` is set, so the automaton moves to state `2`.
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ False
      -- What remains is the statement for `w`.
      simp
    -- Only the bit of `X` is set: a further position of `X`, so the automaton moves to the sink.
    · change _ ↔ False
      -- `X` has no further position.
      simp
    -- Both bits are set: a further position of `X`, so the automaton moves to the sink.
    · change _ ↔ False
      -- `X` has no further position.
      simp
  -- State `2`: no further positions are allowed.
  | 2 => by
    -- Unfold the residual property.
    change ((∀ i, i ∈ (ofList (x :: w)).tracks X ↔ False) ∧
      ∀ i, i ∈ (ofList (x :: w)).tracks Y ↔ False) ↔ _
    -- Split the statement into the first position and the rest of the word.
    simp only [forall_mem_tracks_cons_iff]
    -- Distinguish the bits of the first letter for `X` and `Y`.
    cases hX : x.2 X <;> cases hY : x.2 Y
    -- Both bits are unset, so the automaton stays in state `2`.
    · change _ ↔ (∀ i, i ∈ (ofList w).tracks X ↔ False) ∧ ∀ i, i ∈ (ofList w).tracks Y ↔ False
      -- What remains is the statement for `w`.
      simp
    -- Only the bit of `Y` is set: a further position, so the automaton moves to the sink.
    · change _ ↔ False
      -- `Y` has no further position.
      simp
    -- Only the bit of `X` is set: a further position, so the automaton moves to the sink.
    · change _ ↔ False
      -- `X` has no further position.
      simp
    -- Both bits are set: further positions, so the automaton moves to the sink.
    · change _ ↔ False
      -- `X` has no further position.
      simp
  -- State `3` is a sink, whose residual property is `False`.
  | 3 => Iff.rfl

/-- The automaton for `Suc(X, Y)` is correct. -/
theorem language_sucDFA (X Y : Fin n) :
    (sucDFA X Y : EffectiveDFA (Track A n)).language = (Formula₀.suc X Y).language := by
  -- Compare on a word `w`.
  ext w
  -- Use the residual properties, which hold for the empty word exactly in state `2`.
  refine ((sucDFA X Y).mem_language_iff_of_residual (sucResidual X Y) (sucResidual_nil X Y)
    -- The residual properties follow the transitions by `sucResidual_cons`.
    (fun s x w ↦ sucResidual_cons X Y x w s) w).trans ?_
  -- Express the singletons pointwise as `i ∈ X ↔ i = p`.
  simp only [Formula₀.mem_language, Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
  -- This is the residual property of state `0`.
  rfl

section OmegaWords

variable {α : ωSequence (Track A n)} {j : Fin n} {i m : ℕ}

/-- The lookups in a prefix of an ω-word. -/
theorem getElem?_extract_zero : (α.extract 0 m)[i]? = if i < m then some (α i) else none := by
  -- Distinguish whether the position is in the prefix.
  split_ifs with h
  -- In the prefix, rewrite the optional lookup to the lookup with a bound.
  · rw [List.getElem?_eq_getElem (by simpa [ωSequence.length_extract] using h),
      -- The letter of the ω-word is at this position of the prefix.
      ωSequence.get_extract (by simpa using h)]
    -- The index `0 + i` is `i`.
    simp
  -- Beyond the prefix, the lookup fails.
  · exact List.getElem?_eq_none (by simpa [ωSequence.length_extract] using h)

/-- A position belongs to a track of a prefix iff it is in the prefix and in the track of the
ω-word. -/
theorem mem_tracks_extract :
    i ∈ (ofList (α.extract 0 m)).tracks j ↔ i < m ∧ i ∈ (ofOmega α).tracks j := by
  -- Unfold the tracks and the lookups in the prefix.
  simp only [mem_tracks, ofList_label, ofOmega_label, getElem?_extract_zero]
  -- Distinguish whether the position is in the prefix.
  split_ifs with h <;> simp [h]

/-- The labels of a prefix agree with the ones of the ω-word on the positions of the prefix. -/
theorem base_label_extract (h : i < m) :
    (ofList (α.extract 0 m)).base.label i = (ofOmega α).base.label i := by
  -- The lookup in the prefix gives the letter of the ω-word.
  simp only [base_label, ofList_label, ofOmega_label, getElem?_extract_zero, h, ↓reduceIte]

end OmegaWords

/-- The atomic formulas of MSO₀. -/
inductive Formula₀.IsAtom : {n : ℕ} → Formula₀ A n → Prop where
  /-- `X ⊆ Y` is atomic. -/
  | sub {n : ℕ} (X Y : Fin n) : IsAtom (.sub X Y)
  /-- `Sing(X)` is atomic. -/
  | sing {n : ℕ} (X : Fin n) : IsAtom (.sing X)
  /-- `Suc(X, Y)` is atomic. -/
  | suc {n : ℕ} (X Y : Fin n) : IsAtom (.suc X Y)
  /-- `X ⊆ Q_a` is atomic. -/
  | subLabel {n : ℕ} (X : Fin n) (a : A) : IsAtom (.subLabel X a)

/-- An ω-word satisfies an atomic formula iff infinitely many of its prefixes do. -/
theorem ωlanguage_eq_omegaLim_of_isAtom {φ : Formula₀ A n} (hφ : φ.IsAtom) :
    φ.ωlanguage = φ.language↗ω := by
  -- Compare on an ω-word `α`.
  ext α
  -- An ω-word is in the ω-limit iff infinitely many of its prefixes are in the language.
  change φ.Models (ofOmega α) ↔ ∃ᶠ m in atTop, φ.Models (ofList (α.extract 0 m))
  -- Consider the atoms one by one.
  cases hφ with
  -- `X ⊆ Y`:
  | sub X Y =>
    -- Unfold the semantics of the atom.
    simp only [Formula₀.Models, Formula₀.Satisfies]
    -- Show both directions.
    constructor
    -- Assume `X ⊆ Y` for the ω-word.
    · intro h
      -- We show the inclusion for all prefixes.
      refine Frequently.of_forall fun m i hi ↦ ?_
      -- A position in a prefix is below the prefix length and in the track of the ω-word.
      rw [mem_tracks_extract] at hi ⊢
      -- The inclusion for the ω-word transfers this to `Y`.
      exact ⟨hi.1, h hi.2⟩
    -- Conversely, let `i` be in `X` for the ω-word.
    · intro h i hi
      -- Take a good prefix that contains the position `i`.
      obtain ⟨m, hm, hsub⟩ := frequently_atTop.mp h (i + 1)
      -- The inclusion for this prefix gives that `i` is in `Y`.
      exact (mem_tracks_extract.mp (hsub (mem_tracks_extract.mpr ⟨hm, hi⟩))).2
  -- `X ⊆ Q_a`:
  | subLabel X a =>
    -- Unfold the semantics of the atom.
    simp only [Formula₀.Models, Formula₀.Satisfies]
    -- Show both directions.
    constructor
    -- Assume `X ⊆ Q_a` for the ω-word.
    · intro h
      -- We show this statement for all prefixes.
      refine Frequently.of_forall fun m i hi ↦ ?_
      -- A position in `X` for a prefix is below the prefix length and in `X` for the ω-word.
      obtain ⟨him, hi⟩ := mem_tracks_extract.mp hi
      -- Its label in the prefix is its label in the ω-word.
      rw [base_label_extract him]
      -- This label is `a` by assumption.
      exact h i hi
    -- Conversely, let `i` be in `X` for the ω-word.
    · intro h i hi
      -- Take a good prefix that contains the position `i`.
      obtain ⟨m, hm, hsub⟩ := frequently_atTop.mp h (i + 1)
      -- The position `i` has the label `a` in this prefix.
      have := hsub i (mem_tracks_extract.mpr ⟨hm, hi⟩)
      -- So it has the label `a` in the ω-word.
      rwa [base_label_extract hm] at this
  -- `Sing(X)`:
  | sing X =>
    -- Unfold the semantics of the atom, and describe singletons pointwise.
    simp only [Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
    -- Show both directions.
    constructor
    -- Let `p` be the unique position of `X` in the ω-word.
    · rintro ⟨p, hp⟩
      -- All prefixes that contain `p` are good.
      refine Eventually.frequently ((eventually_gt_atTop p).mono fun m hm ↦ ⟨p, fun i ↦ ?_⟩)
      -- A position of `X` in the prefix is below the prefix length and equal to `p`.
      rw [mem_tracks_extract, hp]
      -- As `p` is below the prefix length, this is the claim.
      omega
    -- Conversely, assume infinitely many good prefixes.
    · intro h
      -- Take a good prefix, with the unique position `p`.
      obtain ⟨m₀, -, p, hp⟩ := frequently_atTop.mp h 0
      -- We show that `p` is the only position of `X` in the ω-word.
      refine ⟨p, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩⟩
      -- Let `q` be in `X`; take a good prefix that contains `p` and `q`, with the position `p'`.
      · obtain ⟨m, hm, p', hp'⟩ := frequently_atTop.mp h (max p q + 1)
        -- The position `p` is in `X` for this prefix.
        have hpm : p ∈ (ofList (α.extract 0 m)).tracks X :=
          -- It is below the prefix length and in the track of the ω-word by the first good prefix.
          mem_tracks_extract.mpr ⟨by omega, (mem_tracks_extract.mp ((hp p).mpr rfl)).2⟩
        -- The position `q` is in `X` for this prefix.
        have hqm : q ∈ (ofList (α.extract 0 m)).tracks X :=
          -- It is below the prefix length and in the track of the ω-word by assumption.
          mem_tracks_extract.mpr ⟨by omega, hq⟩
        -- Both are its unique position `p'`, so they are equal.
        rw [(hp' q).mp hqm, (hp' p).mp hpm]
      -- Conversely, `p` itself is in `X`,
      · rintro rfl
        -- as it is in the track of the first good prefix.
        exact (mem_tracks_extract.mp ((hp q).mpr rfl)).2
  -- `Suc(X, Y)`:
  | suc X Y =>
    -- Unfold the semantics of the atom, and describe singletons pointwise.
    simp only [Formula₀.Models, Formula₀.Satisfies, eq_singleton_iff_forall]
    -- Show both directions.
    constructor
    -- Let `{p}` and `{p + 1}` be the tracks of the ω-word.
    · rintro ⟨p, hX, hY⟩
      -- It suffices that all prefixes that contain `p + 1` are good.
      refine Eventually.frequently
        -- The witness is the same `p` for all these prefixes.
        ((eventually_gt_atTop (p + 1)).mono fun m hm ↦ ⟨p, fun i ↦ ?_, fun i ↦ ?_⟩)
      -- The track of `X` in the prefix is `{p}`.
      · rw [mem_tracks_extract, hX]
        -- As `p` is below the prefix length, this is the claim.
        omega
      -- The track of `Y` in the prefix is `{p + 1}`.
      · rw [mem_tracks_extract, hY]
        -- As `p + 1` is below the prefix length, this is the claim.
        omega
    -- Conversely, assume infinitely many good prefixes.
    · intro h
      -- Take a good prefix, with the positions `p` and `p + 1`.
      obtain ⟨m₀, -, p, hpX, hpY⟩ := frequently_atTop.mp h 0
      -- So `p` is in `X` for the ω-word.
      have hpX' := (mem_tracks_extract.mp ((hpX p).mpr rfl)).2
      -- And `p + 1` is in `Y` for the ω-word.
      have hpY' := (mem_tracks_extract.mp ((hpY (p + 1)).mpr rfl)).2
      -- We show that these are the only positions of `X` and `Y`.
      refine ⟨p, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩, fun q ↦ ⟨fun hq ↦ ?_, ?_⟩⟩
      -- Let `q` be in `X`; take a good prefix that contains `p` and `q`.
      · obtain ⟨m, hm, p', hp', -⟩ := frequently_atTop.mp h (max p q + 1)
        -- The position `q` is the unique position of `X` in this prefix.
        rw [(hp' q).mp (mem_tracks_extract.mpr ⟨by omega, hq⟩),
          -- The same holds for `p`, so `q` and `p` are equal.
          (hp' p).mp (mem_tracks_extract.mpr ⟨by omega, hpX'⟩)]
      -- Conversely, `p` itself is in `X`.
      · rintro rfl
        -- This was shown above.
        exact hpX'
      -- Let `q` be in `Y`; take a good prefix that contains `p + 1` and `q`.
      · obtain ⟨m, hm, p', -, hp'⟩ := frequently_atTop.mp h (max (p + 1) q + 1)
        -- The position `q` is the unique position of `Y` in this prefix.
        rw [(hp' q).mp (mem_tracks_extract.mpr ⟨by omega, hq⟩)]
        -- The same holds for `p + 1`.
        have := (hp' (p + 1)).mp (mem_tracks_extract.mpr ⟨by omega, hpY'⟩)
        -- So `q` is `p + 1`.
        omega
      -- Conversely, `p + 1` itself is in `Y`.
      · rintro rfl
        -- This was shown above.
        exact hpY'

end Cslib.Logic.MSO
