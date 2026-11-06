/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.DA.Buchi
public import Cslib.Computability.Automata.DA.Prod
public import Cslib.Computability.Automata.DA.ToNA
public import Mathlib.Computability.Language
public import Mathlib.Data.FinEnum
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Effectively presented automata

The automata of `Cslib.Automata` are given by propositions and sets, so nothing can be computed from
them. This file introduces effective presentations of automata: the states are enumerated and the
conditions of the automaton are decidable. Constructions on such presentations are ordinary
executable functions, which makes the transformations between logics and automata effective.

## Main definitions and results

- `EffectiveDFA`: an effectively presented deterministic automaton on finite words, together with
  the complement `EffectiveDFA.compl`, the operations `EffectiveDFA.sup` and `EffectiveDFA.inf` for
  union and intersection, and the projection `EffectiveDFA.proj` based on the subset construction.
- `EffectiveNA`: an effectively presented nondeterministic automaton `(Q, A, Q₀, Δ, F)`, which can
  be run on finite words (`EffectiveNA.language`) and as a Büchi automaton on ω-words
  (`EffectiveNA.ωlanguage`).
- `LTS.mTr_iff_exists_run`: multistep transitions in terms of functions from positions to states.

## Implementation notes

The structure `EffectiveDFA` stores the enumeration of its states in a `Thunk`, as a nested subset
construction would otherwise enumerate exponentially many states even if the automaton only has to
be run on a word. The enumerations are computed by the separate functions `EffectiveDFA.prodEnum`
and `EffectiveDFA.finsetEnum` marked `noinline`. Written directly as `⟨fun _ ↦ inferInstance⟩`, the
compiler moves the computation of the instance out of the closure, which makes the thunk eager.

The decidability instances of the structures are data of the automaton, not classical choices, so
all constructions in this file and in `Cslib.Computability.Automata.Effective.Buchi` run. The only
exceptions are `finEnumOfFinite` and `EffectiveNA.ofNA`, which are used to prove the statements for
arbitrary finite automata and are marked `noncomputable`.
-/

@[expose] public section

namespace Cslib

/-- A multistep transition is witnessed by a function from positions to states. -/
theorem LTS.mTr_iff_exists_run {State Label : Type*} {lts : LTS State Label} {s t : State}
    {w : List Label} :
    lts.MTr s w t ↔ ∃ ρ : ℕ → State, ρ 0 = s ∧ ρ w.length = t ∧
      ∀ i (h : i < w.length), lts.Tr (ρ i) w[i] (ρ (i + 1)) := by
  -- Induct on the word, for all start states.
  induction w generalizing s with
  -- The empty word does not move the automaton.
  | nil =>
    -- A multistep transition over `[]` is the equality of the states.
    rw [LTS.MTr.nil_iff]
    -- Show both directions.
    constructor
    -- If the states are equal,
    · rintro rfl
      -- the constant function is a run, and there are no transitions to check.
      exact ⟨fun _ ↦ s, rfl, rfl, fun i h ↦ absurd h (Nat.not_lt_zero i)⟩
    -- Conversely, a run on the empty word has `ρ 0` as its first and as its last state.
    · rintro ⟨ρ, rfl, rfl, -⟩
      -- So the states are equal.
      rfl
  -- A word `x :: w`: split off the first transition.
  | cons x w ih =>
    -- Unfold the multistep transition into a first step and a multistep transition on `w`.
    rw [LTS.MTr.cons_iff]
    -- Show both directions.
    constructor
    -- Let `s'` be the state after the first step.
    · rintro ⟨s', hs', hw⟩
      -- The induction hypothesis gives a run `ρ` on `w` from `s'`.
      obtain ⟨ρ, rfl, rfl, hρ⟩ := ih.mp hw
      -- Prepend `s` to the run; it remains to check the transitions.
      refine ⟨fun | 0 => s | i + 1 => ρ i, rfl, rfl, fun i h ↦ ?_⟩
      -- Distinguish the first transition from the others.
      cases i with
      -- The first transition is the given first step.
      | zero => exact hs'
      -- The other transitions come from the run `ρ`.
      | succ i => exact hρ i (by simpa using h)
    -- Conversely, take a run on `x :: w`.
    · rintro ⟨ρ, rfl, rfl, hρ⟩
      -- Its first transition leads to `ρ 1`, and its tail is a run on `w`.
      refine ⟨ρ 1, hρ 0 (by simp), ih.mpr ⟨fun i ↦ ρ (i + 1), rfl, rfl, fun i h ↦ ?_⟩⟩
      -- The transitions of the tail are transitions of the run, shifted by one position.
      exact hρ (i + 1) (by simpa using h)

end Cslib

namespace Cslib.Automata

open Acceptor ωAcceptor
open scoped DA.FinAcc DA.Buchi NA.FinAcc NA.Buchi

/-- The Booleans can be enumerated. -/
instance finEnumBool : FinEnum Bool :=
  -- The list `[false, true]` contains all Booleans, which `simp` checks.
  FinEnum.ofList [false, true] (by simp)

/-- Every finite type can be enumerated, although not computably. -/
@[instance_reducible]
noncomputable def finEnumOfFinite (α : Type*) [Finite α] : FinEnum α where
  card := Nat.card α
  equiv := Finite.equivFin α
  decEq := Classical.decEq α

variable {Symbol Symbol' : Type*}

/-- An effectively presented deterministic automaton on finite words: its states are enumerated and
its set of accepting states is decidable.

Running the automaton does not need the enumeration of the states, which grows exponentially with
each subset construction. It is therefore only computed on demand. -/
structure EffectiveDFA (Symbol : Type*) where
  /-- The type of states. -/
  State : Type
  /-- Equality of states is decidable. -/
  [decEq : DecidableEq State]
  /-- An enumeration of the states, computed on demand. -/
  lazyEnum : Thunk (FinEnum State)
  /-- The underlying deterministic automaton. -/
  da : DA.FinAcc State Symbol
  /-- Acceptance is decidable. -/
  [decAccept : DecidablePred (· ∈ da.accept)]

namespace EffectiveDFA

attribute [instance] decEq decAccept

/-- The states of an effectively presented deterministic automaton can be enumerated. -/
instance (c : EffectiveDFA Symbol) : FinEnum c.State := c.lazyEnum.get

/-- The language recognized by an effectively presented deterministic automaton. -/
def language (c : EffectiveDFA Symbol) : Language Symbol := Acceptor.language c.da

/-- A word belongs to the language iff the automaton reaches an accepting state. -/
theorem mem_language {c : EffectiveDFA Symbol} {w : List Symbol} :
    w ∈ c.language ↔ c.da.mtr c.da.start w ∈ c.da.accept :=
  -- Holds by definition of the acceptance of a deterministic automaton.
  Iff.rfl

/-- The membership in the language of an effectively presented automaton is decidable. -/
instance (c : EffectiveDFA Symbol) : DecidablePred (· ∈ c.language) :=
  -- Membership in the language is the acceptance of the state reached after the word.
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ c.da.accept))

/-- To determine the language of a deterministic automaton, it suffices to find a property `P s` for
each state `s` that describes the words accepted from `s`. -/
theorem mem_language_iff_of_residual (c : EffectiveDFA Symbol) (P : c.State → List Symbol → Prop)
    (nil : ∀ s, P s [] ↔ s ∈ c.da.accept)
    (cons : ∀ s x w, P s (x :: w) ↔ P (c.da.tr s x) w) (w : List Symbol) :
    w ∈ c.language ↔ P c.da.start w := by
  -- Membership in the language is the acceptance of the state reached after `w`.
  rw [mem_language]
  -- Generalize the start state, so that the induction hypothesis applies to all states.
  generalize c.da.start = s
  -- Induct on the word.
  induction w generalizing s with
  -- The empty word is accepted from `s` iff `s` is accepting.
  | nil => exact (nil s).symm
  -- Reading `x` moves the automaton from `s` to `tr s x`, and `P` follows this step.
  | cons x w ih => rw [cons, ← ih]; rfl

/-- The enumeration of the states of a product automaton, computed on demand. The separate function
keeps the compiler from moving the computation of the instance out of the thunk. -/
@[noinline, nolint unusedArguments, instance_reducible]
def prodEnum (c d : EffectiveDFA Symbol) (_ : Unit) : FinEnum (c.State × d.State) := inferInstance

/-- The enumeration of the states of a subset automaton, computed on demand. The separate function
keeps the compiler from moving the computation of the instance out of the thunk. -/
@[noinline, nolint unusedArguments, instance_reducible]
def finsetEnum (c : EffectiveDFA Symbol) (_ : Unit) : FinEnum (Finset c.State) := inferInstance

/-- The automaton recognizing the complement of a language. -/
def compl (c : EffectiveDFA Symbol) : EffectiveDFA Symbol where
  State := c.State
  lazyEnum := c.lazyEnum
  da := ⟨c.da.toDA, c.da.acceptᶜ⟩
  decAccept s := inferInstanceAs (Decidable (s ∉ c.da.accept))

/-- The complement automaton recognizes the complement of the language. -/
theorem language_compl (c : EffectiveDFA Symbol) : c.compl.language = c.languageᶜ :=
  -- Both sides are the words whose reached state is not accepting.
  rfl

/-- The automaton recognizing the union of two languages. -/
def sup (c d : EffectiveDFA Symbol) : EffectiveDFA Symbol where
  State := c.State × d.State
  lazyEnum := ⟨prodEnum c d⟩
  da := ⟨c.da.toDA.prod d.da.toDA, Prod.fst ⁻¹' c.da.accept ∪ Prod.snd ⁻¹' d.da.accept⟩
  decAccept s := inferInstanceAs (Decidable (s.1 ∈ c.da.accept ∨ s.2 ∈ d.da.accept))

/-- A word is accepted by the union automaton iff one of the automata accepts it. -/
theorem mem_language_sup {c d : EffectiveDFA Symbol} {w : List Symbol} :
    w ∈ (c.sup d).language ↔ w ∈ c.language ∨ w ∈ d.language := by
  -- Both sides are statements about the reached states.
  simp only [mem_language, sup]
  -- The state reached by the product is the pair of the states reached by the components.
  rw [DA.prod_mtr_eq]
  -- So the two statements agree.
  rfl

/-- The automaton recognizing the intersection of two languages. -/
def inf (c d : EffectiveDFA Symbol) : EffectiveDFA Symbol where
  State := c.State × d.State
  lazyEnum := ⟨prodEnum c d⟩
  da := ⟨c.da.toDA.prod d.da.toDA, Prod.fst ⁻¹' c.da.accept ∩ Prod.snd ⁻¹' d.da.accept⟩
  decAccept s := inferInstanceAs (Decidable (s.1 ∈ c.da.accept ∧ s.2 ∈ d.da.accept))

/-- A word is accepted by the intersection automaton iff both automata accept it. -/
theorem mem_language_inf {c d : EffectiveDFA Symbol} {w : List Symbol} :
    w ∈ (c.inf d).language ↔ w ∈ c.language ∧ w ∈ d.language := by
  -- Both sides are statements about the reached states.
  simp only [mem_language, inf]
  -- The state reached by the product is the pair of the states reached by the components.
  rw [DA.prod_mtr_eq]
  -- So the two statements agree.
  rfl

section Projection

variable [FinEnum Symbol] [DecidableEq Symbol'] (f : Symbol → Symbol') (c : EffectiveDFA Symbol)

/-- The transition function of the projection: the subset construction applied to the automaton
that guesses a preimage of each letter. -/
def projStep (T : Finset c.State) (y : Symbol') : Finset c.State :=
  (Finset.univ.filter (f · = y)).biUnion fun x ↦ T.image (c.da.tr · x)

/-- The deterministic automaton underlying the projection, see `proj`. -/
def projDA : DA.FinAcc (Finset c.State) Symbol' :=
  ⟨⟨⟨projStep f c⟩, {c.da.start}⟩, {T | ∃ s ∈ T, s ∈ c.da.accept}⟩

/-- The automaton recognizing the image of a language under a letter-to-letter map. This is the
construction for existential set quantification in the proof of Theorem 3.1 of [Thomas1997],
followed by the subset construction. -/
def proj : EffectiveDFA Symbol' where
  State := Finset c.State
  lazyEnum := ⟨finsetEnum c⟩
  da := projDA f c
  decAccept T := inferInstanceAs (Decidable (∃ s ∈ T, s ∈ c.da.accept))

/-- The states reached by the projection from a set `T` are the ones reached by the original
automaton from `T` along preimages of the word. -/
theorem mem_mtr_projDA {T : Finset c.State} {ys : List Symbol'} {t : c.State} :
    t ∈ (projDA f c).mtr T ys ↔ ∃ s ∈ T, ∃ xs : List Symbol, xs.map f = ys ∧ c.da.mtr s xs = t := by
  -- Induct on the word, for all sets `T` of states.
  induction ys generalizing T with
  -- The empty word stays in `T`.
  | nil =>
    -- Show both directions.
    constructor
    -- A state of `T` is reached from itself along the empty word.
    · exact fun h ↦ ⟨t, h, [], rfl, rfl⟩
    -- Conversely, take a preimage of the empty word.
    · rintro ⟨s, hs, xs, hxs, rfl⟩
      -- It is the empty word itself,
      obtain rfl := List.map_eq_nil_iff.mp hxs
      -- so the reached state is the state of `T`.
      exact hs
  -- The word `y :: ys`: first read `y`, then `ys`.
  | cons y ys ih =>
    -- Reading `y` leads from `T` to `projStep f c T y`.
    change t ∈ (projDA f c).mtr (projStep f c T y) ys ↔ _
    -- Apply the induction hypothesis to the remaining word `ys`.
    rw [ih]
    -- Unfold `projStep`.
    simp only [projStep, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      -- Also evaluate the filter and the image.
      Finset.mem_image]
    -- Show both directions.
    constructor
    -- A state reached via `s ∈ T`, a preimage `x` of `y` and a preimage `xs` of `ys`
    · rintro ⟨_, ⟨x, rfl, s, hs, rfl⟩, xs, rfl, rfl⟩
      -- is reached along the preimage `x :: xs` of `y :: ys`.
      exact ⟨s, hs, x :: xs, rfl, rfl⟩
    -- Conversely, take a preimage of `y :: ys`.
    · rintro ⟨s, hs, _ | ⟨x, xs⟩, hxs, rfl⟩
      -- It cannot be empty.
      · simp at hxs
      -- So it is `x :: xs` with preimages `x` of `y` and `xs` of `ys`.
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hxs
        -- The state `tr s x` leads to the reached state along `xs`.
        exact ⟨_, ⟨x, rfl, s, hs, rfl⟩, xs, rfl, rfl⟩

/-- The projection automaton recognizes the image of the language. -/
theorem language_proj : (proj f c).language = c.language.map f := by
  -- Compare the languages on a word `ys`.
  ext ys
  -- Show both directions.
  constructor
  -- The projection reaches a set with an accepting state `t`.
  · rintro ⟨t, ht, ha⟩
    -- So `t` is reached along a preimage `xs` of the word.
    obtain ⟨s, hs, xs, rfl, rfl⟩ := (mem_mtr_projDA f c).mp ht
    -- The start set is the singleton of the start state.
    obtain rfl := Finset.mem_singleton.mp hs
    -- Hence the preimage `xs` is accepted by the original automaton.
    exact ⟨xs, ha, rfl⟩
  -- Conversely, take an accepted preimage `xs` of the word.
  · rintro ⟨xs, hxs, rfl⟩
    -- Its accepting state is reached in the projection from the start set.
    exact ⟨_, (mem_mtr_projDA f c).mpr ⟨_, Finset.mem_singleton_self _, xs, rfl, rfl⟩, hxs⟩

end Projection

end EffectiveDFA

/-- An effectively presented nondeterministic automaton `(Q, A, Q₀, Δ, F)`: its states are
enumerated and the conditions of the automaton are decidable. It can be run on finite words and, as
a Büchi automaton, on ω-words. -/
structure EffectiveNA (Symbol : Type*) where
  /-- The type of states. -/
  State : Type
  /-- An enumeration of the states. -/
  [enum : FinEnum State]
  /-- The underlying transition system with its initial states. -/
  toNA : NA State Symbol
  /-- The set of accepting states. -/
  accept : Set State
  /-- The transition relation is decidable. -/
  [decTr : ∀ s x t, Decidable (toNA.Tr s x t)]
  /-- Being an initial state is decidable. -/
  [decStart : DecidablePred (· ∈ toNA.start)]
  /-- Being an accepting state is decidable. -/
  [decAccept : DecidablePred (· ∈ accept)]

namespace EffectiveNA

attribute [instance] enum decTr decStart decAccept

/-- The automaton running on finite words. -/
def finAcc (c : EffectiveNA Symbol) : NA.FinAcc c.State Symbol := ⟨c.toNA, c.accept⟩

/-- The automaton running as a Büchi automaton on ω-words. -/
def buchi (c : EffectiveNA Symbol) : NA.Buchi c.State Symbol := ⟨c.toNA, c.accept⟩

/-- The language recognized by the automaton on finite words. -/
def language (c : EffectiveNA Symbol) : Language Symbol := Acceptor.language c.finAcc

/-- The ω-language recognized by the automaton as a Büchi automaton. -/
def ωlanguage (c : EffectiveNA Symbol) : ωLanguage Symbol := ωAcceptor.language c.buchi

/-- A word is accepted iff there is an accepting run, given as a function from positions to
states. -/
theorem mem_language_iff {c : EffectiveNA Symbol} {w : List Symbol} :
    w ∈ c.language ↔ ∃ ρ : ℕ → c.State, ρ 0 ∈ c.toNA.start ∧ ρ w.length ∈ c.accept ∧
      ∀ i (h : i < w.length), c.toNA.Tr (ρ i) w[i] (ρ (i + 1)) := by
  -- Show both directions.
  constructor
  -- An accepted word has a multistep transition from an initial to an accepting state.
  · rintro ⟨s, hs, t, ht, h⟩
    -- This gives a run as a function.
    obtain ⟨ρ, rfl, rfl, hρ⟩ := LTS.mTr_iff_exists_run.mp h
    -- The function is an accepting run.
    exact ⟨ρ, hs, ht, hρ⟩
  -- Conversely, take an accepting run.
  · rintro ⟨ρ, hs, ht, hρ⟩
    -- It gives a multistep transition from an initial to an accepting state.
    exact ⟨_, hs, _, ht, LTS.mTr_iff_exists_run.mpr ⟨ρ, rfl, rfl, hρ⟩⟩

/-- An ω-word is accepted iff there is a run that visits accepting states infinitely often. -/
theorem mem_ωlanguage_iff {c : EffectiveNA Symbol} {α : ωSequence Symbol} :
    α ∈ c.ωlanguage ↔ ∃ ρ : ℕ → c.State, ρ 0 ∈ c.toNA.start ∧
      (∀ i, c.toNA.Tr (ρ i) (α i) (ρ (i + 1))) ∧ ∃ᶠ i in Filter.atTop, ρ i ∈ c.accept := by
  -- Show both directions.
  constructor
  -- An accepted ω-word has a run, which visits accepting states infinitely often.
  · rintro ⟨ρ, hρ, hacc⟩
    -- A run consists of its first state and its transitions.
    exact ⟨ρ, hρ.start, hρ.trans, hacc⟩
  -- Conversely, take such a function.
  · rintro ⟨ρ, hs, hρ, hacc⟩
    -- It forms a run as an ω-sequence of states.
    exact ⟨⟨ρ⟩, ⟨hs, hρ⟩, hacc⟩

open scoped Classical in
/-- Every automaton with finitely many states has an effective presentation, although it can not be
computed in general. -/
noncomputable def ofNA {State : Type} [Finite State] (na : NA State Symbol) (accept : Set State) :
    EffectiveNA Symbol :=
  -- Enumerate the states classically.
  letI := finEnumOfFinite State
  -- All decidability instances are found classically.
  { State, toNA := na, accept }

end EffectiveNA

namespace EffectiveDFA

/-- A deterministic automaton as a nondeterministic automaton. -/
def toNA (c : EffectiveDFA Symbol) : EffectiveNA Symbol where
  State := c.State
  toNA := c.da.toDA.toNA
  accept := c.da.accept
  decTr s x t := inferInstanceAs (Decidable (c.da.tr s x = t))
  decStart s := inferInstanceAs (Decidable (s = c.da.start))

/-- Viewing a deterministic automaton as a nondeterministic one preserves its language. -/
@[simp]
theorem language_toNA (c : EffectiveDFA Symbol) : c.toNA.language = c.language :=
  -- This is the translation of deterministic into nondeterministic automata of CSLib.
  DA.FinAcc.toNAFinAcc_language_eq (a := c.da)

/-- As a Büchi automaton, a deterministic automaton recognizes the ω-limit of its language. -/
theorem ωlanguage_toNA (c : EffectiveDFA Symbol) : c.toNA.ωlanguage = c.language↗ω := by
  -- The nondeterministic Büchi automaton has the language of the deterministic one.
  have h := DA.Buchi.toNABuchi_language_eq (a := DA.Buchi.mk c.da.toDA c.da.accept)
  -- A deterministic Büchi automaton recognizes the ω-limit of its language.
  exact h.trans DA.buchi_eq_finAcc_omegaLim

end EffectiveDFA

end Cslib.Automata
