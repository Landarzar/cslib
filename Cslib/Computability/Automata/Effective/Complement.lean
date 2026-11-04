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

@[simp]
theorem profile_nil : c.profile [] = c.profileStart := rfl

@[simp]
theorem profile_concat (u : List Symbol) (x : Symbol) :
    c.profile (u ++ [x]) = c.profileStep (c.profile u) x :=
  FLTS.mtr_concat_eq

variable {c}

/-- The first component of a profile tells whether the word moves the automaton between states. -/
theorem profile_fst_iff {u : List Symbol} {s t : c.State} :
    (c.profile u s t).1 = true ↔ c.toNA.MTr s u t := by
  induction u using List.reverseRecOn generalizing t with
  | nil =>
    simp only [profile_nil, profileStart, decide_eq_true_eq]
    exact (LTS.MTr.nil_iff _ s t).symm
  | append_singleton u x ih =>
    simp only [profile_concat, profileStep, decide_eq_true_eq, ih, LTS.MTr.append_iff,
      LTS.MTr.singleton_iff]

/-- The second component of a profile tells whether the word moves the automaton between states via
an accepting state. -/
theorem profile_snd_iff {u : List Symbol} {s t : c.State} :
    (c.profile u s t).2 = true ↔ u ∈ c.toNA.pairViaLang c.accept s t := by
  rw [LTS.mem_pairViaLang]
  induction u using List.reverseRecOn generalizing t with
  | nil =>
    simp only [profile_nil, profileStart, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, hs⟩
      exact ⟨s, hs, [], [], .refl, .refl, rfl⟩
    · rintro ⟨r, hr, xs₁, xs₂, h₁, h₂, h⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h
      obtain rfl := LTS.MTr.nil_eq _ h₁
      exact ⟨LTS.MTr.nil_eq _ h₂, hr⟩
  | append_singleton u x ih =>
    simp only [profile_concat, profileStep, decide_eq_true_eq, ih, profile_fst_iff]
    constructor
    · rintro (⟨r, ⟨f, hf, xs₁, xs₂, h₁, h₂, rfl⟩, hx⟩ | ⟨ht, r, hr, hx⟩)
      · exact ⟨f, hf, xs₁, xs₂ ++ [x], h₁, LTS.MTr.stepR _ h₂ hx, by simp⟩
      · exact ⟨t, ht, u ++ [x], [], LTS.MTr.stepR _ hr hx, .refl, by simp⟩
    · rintro ⟨f, hf, xs₁, xs₂, h₁, h₂, h⟩
      rcases List.eq_nil_or_concat' xs₂ with rfl | ⟨ys, y, rfl⟩
      · obtain rfl := LTS.MTr.nil_eq _ h₂
        rw [List.append_nil] at h
        subst h
        obtain ⟨r, hr, hx⟩ := (LTS.MTr.append_iff _).mp h₁
        exact Or.inr ⟨hf, r, hr, (LTS.MTr.singleton_iff _ _ _ _).mp hx⟩
      · rw [← List.append_assoc] at h
        obtain ⟨rfl, hxy⟩ := List.append_inj' h rfl
        obtain rfl : y = x := by simpa using hxy
        obtain ⟨r, hr, hx⟩ := (LTS.MTr.append_iff _).mp h₂
        exact Or.inl ⟨r, ⟨f, hf, xs₁, ys, h₁, hr, rfl⟩, (LTS.MTr.singleton_iff _ _ _ _).mp hx⟩

/-- Two words have the same profile iff they are Büchi-congruent. -/
theorem profile_eq_iff {u v : List Symbol} :
    c.profile u = c.profile v ↔ c.buchi.BuchiCongruence.eq.r u v := by
  constructor
  · intro h s t
    have h₁ : c.toNA.MTr s u t ↔ c.toNA.MTr s v t := by
      rw [← profile_fst_iff, ← profile_fst_iff, h]
    have h₂ : u ∈ c.toNA.pairViaLang c.accept s t ↔ v ∈ c.toNA.pairViaLang c.accept s t := by
      rw [← profile_snd_iff, ← profile_snd_iff, h]
    exact ⟨h₁, h₂⟩
  · intro h
    funext s t
    refine Prod.ext (Bool.eq_iff_iff.mpr ?_) (Bool.eq_iff_iff.mpr ?_)
    · rw [profile_fst_iff, profile_fst_iff]
      exact (h s t).1
    · rw [profile_snd_iff, profile_snd_iff]
      exact (h s t).2

variable (c)

/-- The automaton recognizing the words with a given profile. -/
def classDFA (a : c.Profile) : EffectiveDFA Symbol where
  State := c.Profile
  lazyEnum := ⟨fun _ ↦ inferInstance⟩
  da := ⟨c.profileDA, {a}⟩
  decAccept s := inferInstanceAs (Decidable (s = a))

theorem mem_language_classDFA {a : c.Profile} {u : List Symbol} :
    u ∈ (c.classDFA a).language ↔ c.profile u = a := Iff.rfl

/-- The automaton recognizing the ω-language `[a] * [b]^ω` for profiles `a` and `b`. -/
def family (a b : c.Profile) : EffectiveNA Symbol :=
  (c.classDFA a).toNA.concat (c.classDFA b).toNA.loop

variable {c}

theorem ωlanguage_family [Inhabited Symbol] (a b : c.Profile) :
    (c.family a b).ωlanguage = (c.classDFA a).language * (c.classDFA b).language^ω := by
  rw [family, ωlanguage_concat, ωlanguage_loop, EffectiveDFA.language_toNA,
    EffectiveDFA.language_toNA]

/-- The words whose profile is the one of a representative of a Büchi congruence class are exactly
the words of this class. -/
theorem language_classDFA_profile_out (q : Quotient c.buchi.BuchiCongruence.eq) :
    (c.classDFA (c.profile q.out)).language = c.buchi.BuchiCongruence.eqvCls q := by
  ext u
  rw [mem_language_classDFA, profile_eq_iff]
  constructor
  · intro h
    have := Quotient.sound (s := c.buchi.BuchiCongruence.eq) h
    rwa [Quotient.out_eq] at this
  · intro h
    apply Quotient.exact (s := c.buchi.BuchiCongruence.eq)
    rw [Quotient.out_eq]
    exact h

/-- The languages `[a] * [b]^ω` for representatives of Büchi congruence classes are the languages
of `NA.Buchi.buchiFamily`. -/
theorem ωlanguage_family_profile_out [Inhabited Symbol]
    (q q' : Quotient c.buchi.BuchiCongruence.eq) :
    (c.family (c.profile q.out) (c.profile q'.out)).ωlanguage = c.buchi.buchiFamily (q, q') := by
  rw [ωlanguage_family, language_classDFA_profile_out, language_classDFA_profile_out]
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

theorem mem_disjointPairs {a b : c.Profile} :
    (a, b) ∈ c.disjointPairs ↔ ¬∃ α, α ∈ (c.family a b).ωlanguage ∧ α ∈ c.ωlanguage := by
  simp only [disjointPairs, List.mem_filter, FinEnum.mem_toList, true_and, Bool.not_eq_true',
    ← Bool.not_eq_true, isNonempty_iff, ωlanguage_inf]
  exact not_congr (exists_congr fun α ↦ ωLanguage.mem_inf _ _ _)

/-- The complement of a Büchi automaton recognizes the complement of its ω-language. -/
theorem mem_ωlanguage_compl {α : ωSequence Symbol} : α ∈ c.compl.ωlanguage ↔ α ∉ c.ωlanguage := by
  have : Inhabited Symbol := ⟨α 0⟩
  rw [compl, ωlanguage_iSup, ωLanguage.mem_iSup]
  constructor
  · rintro ⟨⟨⟨a, b⟩, hab⟩, h⟩ hα
    exact mem_disjointPairs.mp hab ⟨α, h, hα⟩
  · intro hα
    have hcover : α ∈ ⨆ i, c.buchi.buchiFamily i := by
      rw [buchiFamily_cover]
      exact ωLanguage.mem_top α
    obtain ⟨⟨q, q'⟩, hq⟩ := ωLanguage.mem_iSup.mp hcover
    refine ⟨⟨(c.profile q.out, c.profile q'.out), mem_disjointPairs.mpr ?_⟩, ?_⟩
    · rintro ⟨β, hβ₁, hβ₂⟩
      rw [ωlanguage_family_profile_out] at hβ₁
      exact hα (buchiFamily_saturation (na := c.buchi) (q, q') ⟨β, hβ₁, hβ₂⟩ hq)
    · rwa [ωlanguage_family_profile_out]

/-- The complement of a Büchi automaton recognizes the complement of its ω-language. -/
theorem ωlanguage_compl : c.compl.ωlanguage = c.ωlanguageᶜ :=
  ωLanguage.mem_ext fun _ ↦ mem_ωlanguage_compl

end Cslib.Automata.EffectiveNA
