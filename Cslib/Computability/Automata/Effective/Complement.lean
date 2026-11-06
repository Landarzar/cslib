/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.Effective.Buchi
public import Cslib.Computability.Languages.Congruences.BuchiCongruence

/-! # Effective complementation of Büchi automata

This file gives an effective version of Büchi's complementation of Büchi automata, whose
correctness is inherited from the theory of the Büchi congruence in
`Cslib.Computability.Languages.Congruences.BuchiCongruence`.

The *profile* of a finite word records, for each pair of states `s` and `t`, whether the word can
move the automaton from `s` to `t` and whether it can do so via an accepting state. Two words are
Büchi-congruent iff they have the same profile. Profiles can be computed by a deterministic
automaton, so all the languages `[a] * [b]^ω` for profiles `a` and `b` are effectively recognizable.
These languages cover all ω-words and each of them is either contained in or disjoint from the
ω-language of the automaton, which is decidable by the emptiness test. The complement is the union
of the ones disjoint from the ω-language.

## Main definitions and results

- `EffectiveNA.profile`: the profile of a finite word.
- `EffectiveNA.compl`: the complement automaton, which is correct by
  `EffectiveNA.mem_ωlanguage_compl`.

## Implementation notes

[Thomas1997] derives the closure under complement from McNaughton's theorem. Since a proof of
McNaughton's theorem is not available in CSLib, we follow Büchi's original approach instead, which
is the one taken in `Cslib.Computability.Languages.OmegaRegularLanguage`.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Automata.EffectiveNA

open _root_.Language RightCongruence NA.Buchi Acceptor
open scoped Computability

variable {Symbol : Type*} (c : EffectiveNA Symbol)

/-- A profile records, for each pair of states `s` and `t`, whether a finite word can move the
automaton from `s` to `t`, and whether it can do so via an accepting state. -/
abbrev Profile := c.State → c.State → Bool × Bool

/-- The profile of the empty word. -/
def profileStart : c.Profile := fun s t ↦ (decide (s = t), decide (s = t ∧ s ∈ c.accept))

/-- The profile of `u ++ [x]` in terms of the profile of `u`. -/
def profileStep (p : c.Profile) (x : Symbol) : c.Profile := fun s t ↦
  (decide (∃ r, (p s r).1 = true ∧ c.toNA.Tr r x t),
    decide ((∃ r, (p s r).2 = true ∧ c.toNA.Tr r x t) ∨
      (t ∈ c.accept ∧ ∃ r, (p s r).1 = true ∧ c.toNA.Tr r x t)))

/-- The deterministic automaton that computes the profiles of finite words. -/
def profileDA : DA c.Profile Symbol := ⟨⟨c.profileStep⟩, c.profileStart⟩

/-- The profile of a finite word. -/
def profile (u : List Symbol) : c.Profile := c.profileDA.mtr c.profileStart u

/-- The profile of the empty word is the start of the profile automaton. -/
@[simp]
theorem profile_nil : c.profile [] = c.profileStart :=
  -- Holds by definition of the extended transition function.
  rfl

/-- The profile of `u ++ [x]` is computed from the profile of `u`. -/
@[simp]
theorem profile_concat (u : List Symbol) (x : Symbol) :
    c.profile (u ++ [x]) = c.profileStep (c.profile u) x :=
  -- The extended transition function reads the last letter last.
  FLTS.mtr_concat_eq

variable {c}

/-- The first component of a profile tells whether the word moves the automaton between states. -/
theorem profile_fst_iff {u : List Symbol} {s t : c.State} :
    (c.profile u s t).1 = true ↔ c.toNA.MTr s u t := by
  -- Induct on the word from its end, for all target states.
  induction u using List.reverseRecOn generalizing t with
  -- The empty word only moves between equal states.
  | nil =>
    -- The first component of the start profile is the decision of `s = t`.
    simp only [profile_nil, profileStart, decide_eq_true_eq]
    -- A multistep transition over `[]` also means `s = t`.
    exact (LTS.MTr.nil_iff _ s t).symm
  -- The word `u ++ [x]`: a move on `u` followed by a transition on `x`.
  | append_singleton u x ih =>
    -- Both sides state the existence of a state `r` reached by `u` with a transition on `x` to `t`.
    simp only [profile_concat, profileStep, decide_eq_true_eq, ih, LTS.MTr.append_iff,
      -- A multistep transition over a one-letter word is a transition.
      LTS.MTr.singleton_iff]

/-- The second component of a profile tells whether the word moves the automaton between states via
an accepting state. -/
theorem profile_snd_iff {u : List Symbol} {s t : c.State} :
    (c.profile u s t).2 = true ↔ u ∈ c.toNA.pairViaLang c.accept s t := by
  -- Unfold the words that move via an accepting state into a split at this state.
  rw [LTS.mem_pairViaLang]
  -- Induct on the word from its end, for all target states.
  induction u using List.reverseRecOn generalizing t with
  -- The empty word:
  | nil =>
    -- The second component of the start profile is the decision of `s = t ∧ s ∈ F`.
    simp only [profile_nil, profileStart, decide_eq_true_eq]
    -- Show both directions.
    constructor
    -- For `s = t` with `s` accepting,
    · rintro ⟨rfl, hs⟩
      -- the empty word moves via `s`.
      exact ⟨s, hs, [], [], .refl, .refl, rfl⟩
    -- Conversely, take a split of the empty word at an accepting state `r`.
    · rintro ⟨r, hr, xs₁, xs₂, h₁, h₂, h⟩
      -- Both parts are empty.
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h
      -- So `s` is `r`.
      obtain rfl := LTS.MTr.nil_eq _ h₁
      -- And `r` is `t`, which is accepting.
      exact ⟨LTS.MTr.nil_eq _ h₂, hr⟩
  -- The word `u ++ [x]`:
  | append_singleton u x ih =>
    -- Unfold the step of the profile and apply the induction hypothesis.
    simp only [profile_concat, profileStep, decide_eq_true_eq, ih, profile_fst_iff]
    -- Show both directions.
    constructor
    -- Either `u` already passed an accepting state `f`, or `t` itself is accepting.
    · rintro (⟨r, ⟨f, hf, xs₁, xs₂, h₁, h₂, rfl⟩, hx⟩ | ⟨ht, r, hr, hx⟩)
      -- In the first case, extend the second part of the split by `x`.
      · exact ⟨f, hf, xs₁, xs₂ ++ [x], h₁, LTS.MTr.stepR _ h₂ hx, by simp⟩
      -- In the second case, split at the end of the word.
      · exact ⟨t, ht, u ++ [x], [], LTS.MTr.stepR _ hr hx, .refl, by simp⟩
    -- Conversely, take a split of `u ++ [x]` at an accepting state `f`.
    · rintro ⟨f, hf, xs₁, xs₂, h₁, h₂, h⟩
      -- Distinguish whether the second part is empty.
      rcases List.eq_nil_or_concat' xs₂ with rfl | ⟨ys, y, rfl⟩
      -- If it is empty, then `f` is `t`,
      · obtain rfl := LTS.MTr.nil_eq _ h₂
        -- and the first part is the whole word.
        rw [List.append_nil] at h
        -- Replace the first part by the whole word.
        subst h
        -- Split off the last transition on `x`.
        obtain ⟨r, hr, hx⟩ := (LTS.MTr.append_iff _).mp h₁
        -- So `t` is accepting and reached as required.
        exact Or.inr ⟨hf, r, hr, (LTS.MTr.singleton_iff _ _ _ _).mp hx⟩
      -- If the second part is `ys ++ [y]`, regroup the word.
      · rw [← List.append_assoc] at h
        -- Then `xs₁ ++ ys` is `u`, and the last letters agree.
        obtain ⟨rfl, hxy⟩ := List.append_inj' h rfl
        -- The last letters are `y` and `x`, so they are equal.
        obtain rfl : y = x := by simpa using hxy
        -- Split off the last transition on `x` from the second part.
        obtain ⟨r, hr, hx⟩ := (LTS.MTr.append_iff _).mp h₂
        -- So `u` moves via `f` to the state `r`, which has the last transition to `t`.
        exact Or.inl ⟨r, ⟨f, hf, xs₁, ys, h₁, hr, rfl⟩, (LTS.MTr.singleton_iff _ _ _ _).mp hx⟩

/-- Two words have the same profile iff they are Büchi-congruent. -/
theorem profile_eq_iff {u v : List Symbol} :
    c.profile u = c.profile v ↔ c.buchi.BuchiCongruence.eq.r u v := by
  -- Show both directions.
  constructor
  -- Assume equal profiles, and let `s` and `t` be states.
  · intro h s t
    -- The first components tell the same about moves from `s` to `t`.
    have h₁ : c.toNA.MTr s u t ↔ c.toNA.MTr s v t := by
      -- Rewrite both moves into the profiles, which agree.
      rw [← profile_fst_iff, ← profile_fst_iff, h]
    -- The second components tell the same about moves via accepting states.
    have h₂ : u ∈ c.toNA.pairViaLang c.accept s t ↔ v ∈ c.toNA.pairViaLang c.accept s t := by
      -- Rewrite both moves into the profiles, which agree.
      rw [← profile_snd_iff, ← profile_snd_iff, h]
    -- This is the definition of the Büchi congruence.
    exact ⟨h₁, h₂⟩
  -- Conversely, assume that the words are congruent.
  · intro h
    -- Compare the profiles at states `s` and `t`.
    funext s t
    -- Compare both components, which are Booleans.
    refine Prod.ext (Bool.eq_iff_iff.mpr ?_) (Bool.eq_iff_iff.mpr ?_)
    -- The first components describe moves.
    · rw [profile_fst_iff, profile_fst_iff]
      -- They agree by the congruence.
      exact (h s t).1
    -- The second components describe moves via accepting states.
    · rw [profile_snd_iff, profile_snd_iff]
      -- They agree by the congruence.
      exact (h s t).2

variable (c)

/-- The automaton recognizing the words with a given profile. -/
def classDFA (a : c.Profile) : EffectiveDFA Symbol where
  State := c.Profile
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨c.profileDA, {a}⟩
  decAccept s := inferInstanceAs (Decidable (s = a))

/-- A word is recognized iff it has the given profile. -/
theorem mem_language_classDFA {a : c.Profile} {u : List Symbol} :
    u ∈ (c.classDFA a).language ↔ c.profile u = a :=
  -- Holds by definition of the acceptance of the profile automaton.
  Iff.rfl

/-- The automaton recognizing the ω-language `[a] * [b]^ω` for profiles `a` and `b`. -/
def family (a b : c.Profile) : EffectiveNA Symbol :=
  (c.classDFA a).toNA.concat (c.classDFA b).toNA.loop

variable {c}

/-- The ω-language of `family a b` is `[a] * [b]^ω`. -/
theorem ωlanguage_family [Inhabited Symbol] (a b : c.Profile) :
    (c.family a b).ωlanguage = (c.classDFA a).language * (c.classDFA b).language^ω := by
  -- Apply the correctness of concatenation and ω-power to the automata for the profiles.
  rw [family, ωlanguage_concat, ωlanguage_loop, EffectiveDFA.language_toNA,
    -- The automata for profiles have the same language as nondeterministic automata.
    EffectiveDFA.language_toNA]

/-- The words whose profile is the one of a representative of a Büchi congruence class are exactly
the words of this class. -/
theorem language_classDFA_profile_out (q : Quotient c.buchi.BuchiCongruence.eq) :
    (c.classDFA (c.profile q.out)).language = c.buchi.BuchiCongruence.eqvCls q := by
  -- Compare both languages on a word `u`.
  ext u
  -- A word has the profile of `q.out` iff it is congruent to `q.out`.
  rw [mem_language_classDFA, profile_eq_iff]
  -- Show both directions.
  constructor
  -- Let `u` be congruent to `q.out`.
  · intro h
    -- So the classes of `u` and `q.out` agree.
    have := Quotient.sound (s := c.buchi.BuchiCongruence.eq) h
    -- The class of `q.out` is `q`.
    rwa [Quotient.out_eq] at this
  -- Conversely, let `u` have the class `q`.
  · intro h
    -- It suffices to show that the classes of `u` and `q.out` agree.
    apply Quotient.exact (s := c.buchi.BuchiCongruence.eq)
    -- The class of `q.out` is `q`.
    rw [Quotient.out_eq]
    -- The class of `u` is `q` by assumption.
    exact h

/-- The languages `[a] * [b]^ω` for representatives of Büchi congruence classes are the languages
of `NA.Buchi.buchiFamily`. -/
theorem ωlanguage_family_profile_out [Inhabited Symbol]
    (q q' : Quotient c.buchi.BuchiCongruence.eq) :
    (c.family (c.profile q.out) (c.profile q'.out)).ωlanguage = c.buchi.buchiFamily (q, q') := by
  -- Replace the words with a given profile by the congruence classes.
  rw [ωlanguage_family, language_classDFA_profile_out, language_classDFA_profile_out]
  -- This is the definition of `buchiFamily`.
  rfl

variable (c) [FinEnum Symbol]

/-- The pairs of profiles `a` and `b` such that `[a] * [b]^ω` is disjoint from the ω-language of the
automaton. -/
def disjointPairs : List (c.Profile × c.Profile) :=
  (FinEnum.toList (c.Profile × c.Profile)).filter fun ab ↦
    !((c.family ab.1 ab.2).inf c).isNonempty

/-- The complement of a Büchi automaton: the union of all automata for the languages `[a] * [b]^ω`
that are disjoint from the ω-language of the automaton. -/
def compl : EffectiveNA Symbol :=
  iSup fun ab : {ab // ab ∈ c.disjointPairs} ↦ c.family ab.1.1 ab.1.2

variable {c}

/-- A pair of profiles is disjoint iff its language has no common ω-word with the automaton. -/
theorem mem_disjointPairs {a b : c.Profile} :
    (a, b) ∈ c.disjointPairs ↔ ¬∃ α, α ∈ (c.family a b).ωlanguage ∧ α ∈ c.ωlanguage := by
  -- Unfold the filter, the emptiness test and the intersection automaton.
  simp only [disjointPairs, List.mem_filter, FinEnum.mem_toList, true_and, Bool.not_eq_true',
    -- Also apply the emptiness test and the correctness of the intersection.
    ← Bool.not_eq_true, isNonempty_iff, ωlanguage_inf]
  -- An ω-word of the intersection is an ω-word in both languages.
  exact not_congr (exists_congr fun α ↦ ωLanguage.mem_inf _ _ _)

/-- The complement of a Büchi automaton recognizes the complement of its ω-language. -/
theorem mem_ωlanguage_compl {α : ωSequence Symbol} : α ∈ c.compl.ωlanguage ↔ α ∉ c.ωlanguage := by
  -- An ω-word gives a letter, so the alphabet is inhabited, as needed for the ω-power.
  have : Inhabited Symbol := ⟨α 0⟩
  -- The complement is the union of the disjoint families.
  rw [compl, ωlanguage_iSup, ωLanguage.mem_iSup]
  -- Show both directions.
  constructor
  -- Let `α` be in a disjoint family and, for a contradiction, in the ω-language.
  · rintro ⟨⟨⟨a, b⟩, hab⟩, h⟩ hα
    -- This contradicts that the family is disjoint from the ω-language.
    exact mem_disjointPairs.mp hab ⟨α, h, hα⟩
  -- Conversely, let `α` not be in the ω-language.
  · intro hα
    -- The families for the congruence classes cover all ω-words, which uses Ramsey's theorem.
    have hcover : α ∈ ⨆ i, c.buchi.buchiFamily i := by
      -- This is the cover by the Büchi family of CSLib.
      rw [buchiFamily_cover]
      -- Every ω-word is in `⊤`.
      exact ωLanguage.mem_top α
    -- So `α` belongs to the family of some classes `q` and `q'`.
    obtain ⟨⟨q, q'⟩, hq⟩ := ωLanguage.mem_iSup.mp hcover
    -- Take the profiles of representatives; we show that the family is disjoint and contains `α`.
    refine ⟨⟨(c.profile q.out, c.profile q'.out), mem_disjointPairs.mpr ?_⟩, ?_⟩
    -- Suppose that `β` is in the family and in the ω-language.
    · rintro ⟨β, hβ₁, hβ₂⟩
      -- This family is the Büchi family of `q` and `q'`.
      rw [ωlanguage_family_profile_out] at hβ₁
      -- By saturation, the whole family is in the ω-language, including `α`: a contradiction.
      exact hα (buchiFamily_saturation (na := c.buchi) (q, q') ⟨β, hβ₁, hβ₂⟩ hq)
    -- `α` belongs to the family, as it is the Büchi family of `q` and `q'`.
    · rwa [ωlanguage_family_profile_out]

/-- The complement of a Büchi automaton recognizes the complement of its ω-language. -/
theorem ωlanguage_compl : c.compl.ωlanguage = c.ωlanguageᶜ :=
  -- Compare on each ω-word.
  ωLanguage.mem_ext fun _ ↦ mem_ωlanguage_compl

end Cslib.Automata.EffectiveNA
