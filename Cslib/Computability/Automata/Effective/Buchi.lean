/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Computability.Automata.Effective.Basic
public import Cslib.Computability.Automata.NA.BuchiInter
public import Cslib.Computability.Automata.NA.Concat
public import Cslib.Computability.Automata.NA.Loop
public import Cslib.Computability.Automata.NA.Sum

/-! # Effectively presented Büchi automata

This file provides the closure properties of effectively presented Büchi automata under union,
intersection, concatenation, ω-power and letter-to-letter maps, as well as the decision of their
nonemptiness. The automata are the ones of `Cslib.Automata.NA`, so their correctness is inherited.

## Main definitions and results

- `EffectiveNA.bot`, `EffectiveNA.iSup`, `EffectiveNA.sup`, `EffectiveNA.inf`,
  `EffectiveNA.concat`, `EffectiveNA.loop`, `EffectiveNA.proj`: closure operations.
- `EffectiveNA.isNonempty`: the decision of the nonemptiness of a Büchi automaton, which is correct
  by `EffectiveNA.isNonempty_iff`. As in the proof of Corollary 5.10 of [Thomas1997], a successful
  run exists iff some accepting state is reachable from an initial state and from itself by a
  nonempty path. The reachable states are computed by `EffectiveNA.reachable`, which adds successors
  until no new state appears (`EffectiveNA.mem_reachable`).

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Automata.EffectiveNA

open Filter ωSequence NA.Buchi
open scoped Computability

variable {Symbol Symbol' : Type*}

/-- The automaton recognizing no word. -/
def bot : EffectiveNA Symbol where
  State := Empty
  toNA := { Tr := fun _ _ _ ↦ False, start := ∅ }
  accept := ∅
  decTr s := s.elim
  decStart s := s.elim
  decAccept s := s.elim

/-- The empty automaton recognizes no ω-word. -/
@[simp]
theorem ωlanguage_bot : (bot : EffectiveNA Symbol).ωlanguage = ⊥ := by
  -- Compare on an ω-word `α`.
  ext α
  -- Show both directions.
  constructor
  -- A run would start in a state of the empty state type.
  · rintro ⟨ρ, -, -⟩
    -- There is no such state.
    exact (ρ 0).elim
  -- The other direction is trivial, as `⊥` contains no ω-word.
  · exact fun h ↦ h.elim

section Union

variable {I : Type} [FinEnum I]

omit [FinEnum I] in
/-- A state `⟨i, a⟩` of a sum belongs to the union of the injected sets iff `a` belongs to the
`i`-th set. -/
theorem mem_iUnion_sigma_image {β : I → Type} {S : (i : I) → Set (β i)} {i : I} {a : β i} :
    (⟨i, a⟩ : Σ i, β i) ∈ ⋃ j, Sigma.mk j '' S j ↔ a ∈ S i := by
  -- Unfold the union and the images; the equality of pairs is componentwise.
  simp only [Set.mem_iUnion, Set.mem_image, Sigma.mk.injEq]
  -- Show both directions.
  constructor
  -- Take `⟨j, b⟩ = ⟨i, a⟩` with `b` in the `j`-th set; then `j = i`.
  · rintro ⟨j, b, hb, rfl, h⟩
    -- So `b` and `a` are equal as well.
    obtain rfl := eq_of_heq h
    -- Hence `a` is in the set.
    exact hb
  -- Conversely, `a` itself is the witness.
  · exact fun h ↦ ⟨i, a, h, rfl, HEq.rfl⟩

omit [FinEnum I] in
/-- There is a transition in a sum of automata iff the states lie in the same component and are
connected by a transition of this component. -/
theorem iSum_tr_iff {β : I → Type} {na : (i : I) → NA (β i) Symbol} {i j : I} {s : β i} {t : β j}
    {x : Symbol} :
    (NA.iSum na).Tr ⟨i, s⟩ x ⟨j, t⟩ ↔ ∃ h : i = j, (na j).Tr (h ▸ s) x t := by
  -- Show both directions.
  constructor
  -- A transition of the sum is a transition in a component `k`.
  · rintro ⟨k, s', t', hTr, h₁, h₂⟩
    -- So the source lies in the component `k`.
    cases h₁
    -- And so does the target.
    cases h₂
    -- The components are equal, and the transition is one of the component.
    exact ⟨rfl, hTr⟩
  -- Conversely, take a transition in the common component.
  · rintro ⟨rfl, h⟩
    -- It is a transition of the sum.
    exact ⟨i, s, t, h, rfl, rfl⟩

/-- The automaton recognizing the union of finitely many ω-languages. -/
def iSup (c : I → EffectiveNA Symbol) : EffectiveNA Symbol where
  State := Σ i, (c i).State
  toNA := NA.iSum fun i ↦ (c i).toNA
  accept := ⋃ i, Sigma.mk i '' (c i).accept
  -- Transitions only connect states of the same component.
  decTr
    | ⟨i, s⟩, x, ⟨j, t⟩ => decidable_of_iff (∃ h : i = j, (c j).toNA.Tr (h ▸ s) x t)
      -- This is the characterization of the transitions of a sum.
      (iSum_tr_iff (β := fun i ↦ (c i).State) (na := fun i ↦ (c i).toNA)).symm
  -- A state `⟨i, a⟩` is initial iff `a` is initial in the `i`-th automaton.
  decStart
    | ⟨i, a⟩ => decidable_of_iff (a ∈ (c i).toNA.start)
      -- This is the characterization of the initial states of a sum.
      (mem_iUnion_sigma_image (S := fun i ↦ (c i).toNA.start)).symm
  -- A state `⟨i, a⟩` is accepting iff `a` is accepting in the `i`-th automaton.
  decAccept
    | ⟨i, a⟩ => decidable_of_iff (a ∈ (c i).accept)
      -- This is the characterization of the accepting states of a sum.
      (mem_iUnion_sigma_image (S := fun i ↦ (c i).accept)).symm

/-- The sum automaton recognizes the union of the ω-languages. -/
theorem ωlanguage_iSup (c : I → EffectiveNA Symbol) : (iSup c).ωlanguage = ⨆ i, (c i).ωlanguage :=
  -- This is the correctness of the sum of Büchi automata of CSLib.
  iSum_language_eq (na := fun i ↦ (c i).toNA) (acc := fun i ↦ (c i).accept)

end Union

/-- The automaton recognizing the union of two ω-languages. -/
def sup (c d : EffectiveNA Symbol) : EffectiveNA Symbol := iSup fun b : Bool ↦ cond b c d

/-- The automaton `sup` recognizes the union of two ω-languages. -/
theorem ωlanguage_sup (c d : EffectiveNA Symbol) :
    (c.sup d).ωlanguage = c.ωlanguage ⊔ d.ωlanguage := by
  -- `sup` is a union indexed by the Booleans.
  change (iSup _).ωlanguage = _
  -- Apply the correctness of the union and evaluate the supremum over `Bool`.
  rw [ωlanguage_iSup, iSup_bool_eq]
  -- The components are `c` and `d`.
  rfl

section Intersection

variable (e : Bool → EffectiveNA Symbol)

/-- The transition function of the history state of the intersection automaton. -/
def histStep (s : (Π i, (e i).State) × Bool) : Bool :=
  if s.1 false ∈ (e false).accept ∧ s.2 = false then true
  else if s.1 true ∈ (e true).accept ∧ s.2 = true then false else s.2

/-- The computable counterpart of the intersection automaton `NA.Buchi.interNA`. -/
def iInfBoolNA : NA ((Π i, (e i).State) × Bool) Symbol where
  Tr s x t := (∀ i, (e i).toNA.Tr (s.1 i) x (t.1 i)) ∧ histStep e s = t.2
  start := {s | (∀ i, s.1 i ∈ (e i).toNA.start) ∧ false = s.2}

/-- The computable automaton agrees with the intersection automaton of CSLib. -/
theorem iInfBoolNA_eq : iInfBoolNA e = interNA (fun i ↦ (e i).toNA) fun i ↦ (e i).accept := by
  -- The history state is updated in the same way,
  have hist : ∀ (s : (Π i, (e i).State) × Bool) (x : Symbol) (t : Π i, (e i).State),
      -- which means that the classical `histTrans` agrees with the computable `histStep`.
      histTrans (fun i ↦ (e i).accept) s x t = histStep e s := by
    -- The classical definition has the same case distinction as `histStep`.
    grind [histTrans, histStep, interAcc]
  -- Unfold both automata and use this fact for the transitions.
  simp only [iInfBoolNA, interNA, NA.addHist, NA.iProd, hist, histStart]
  -- It remains to compare the sets of initial states.
  congr
  -- Compare both sets on a state `s`.
  ext s
  -- Membership in an intersection of preimages is the statement for each component.
  simp only [Set.mem_iInter, Set.mem_preimage]

/-- The intersection automaton of two effectively presented Büchi automata. -/
def iInfBool : EffectiveNA Symbol where
  State := (Π i, (e i).State) × Bool
  toNA := iInfBoolNA e
  accept := interAccept fun i ↦ (e i).accept
  decTr s x t := inferInstanceAs
    (Decidable ((∀ i, (e i).toNA.Tr (s.1 i) x (t.1 i)) ∧ histStep e s = t.2))
  decStart s := inferInstanceAs (Decidable ((∀ i, s.1 i ∈ (e i).toNA.start) ∧ false = s.2))
  decAccept s := decidable_of_iff
    ((s.1 false ∈ (e false).accept ∧ s.2 = false) ∨ (s.1 true ∈ (e true).accept ∧ s.2 = true))
    Iff.rfl

/-- The intersection automaton recognizes the intersection of the ω-languages. -/
theorem ωlanguage_iInfBool : (iInfBool e).ωlanguage = ⨅ i, (e i).ωlanguage := by
  -- CSLib shows this for its intersection automaton.
  have h := inter_language_eq (na := fun i ↦ (e i).toNA) (acc := fun i ↦ (e i).accept)
  -- This automaton agrees with the computable one.
  rw [← iInfBoolNA_eq] at h
  -- So this is the claim.
  exact h

end Intersection

/-- The automaton recognizing the intersection of two ω-languages. -/
def inf (c d : EffectiveNA Symbol) : EffectiveNA Symbol := iInfBool fun b : Bool ↦ cond b c d

/-- The automaton `inf` recognizes the intersection of two ω-languages. -/
theorem ωlanguage_inf (c d : EffectiveNA Symbol) :
    (c.inf d).ωlanguage = c.ωlanguage ⊓ d.ωlanguage := by
  -- `inf` is an intersection indexed by the Booleans.
  change (iInfBool _).ωlanguage = _
  -- Apply the correctness of the intersection and evaluate the infimum over `Bool`.
  rw [ωlanguage_iInfBool, iInf_bool_eq]
  -- The components are `c` and `d`.
  rfl

/-- `[]` is accepted iff an initial state is an accepting state. -/
theorem nil_mem_language_iff {c : EffectiveNA Symbol} :
    [] ∈ c.language ↔ ∃ s, s ∈ c.toNA.start ∧ s ∈ c.accept := by
  -- Show both directions.
  constructor
  -- An accepted empty word gives a multistep transition from `s` to `t`.
  · rintro ⟨s, hs, t, ht, h⟩
    -- A multistep transition over `[]` does not change the state.
    obtain rfl := LTS.MTr.nil_eq _ h
    -- So `s` is initial and accepting.
    exact ⟨s, hs, ht⟩
  -- Conversely, take a state `s` that is initial and accepting.
  · rintro ⟨s, hs, ha⟩
    -- It accepts `[]` by the empty multistep transition.
    exact ⟨s, hs, s, ha, .refl⟩

section Concatenation

variable {c d : EffectiveNA Symbol}

/-- A left state is initial in the concatenation iff it is initial in `c`. -/
theorem inl_mem_concat_start {s : c.State} :
    .inl s ∈ (NA.concat c.finAcc d.toNA).start ↔ s ∈ c.toNA.start := by
  -- Unfold the initial states; the right part of the union contains no left states.
  simp only [NA.concat, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
    -- Evaluate the membership in the union and in the image.
    Set.mem_ofPred_eq, reduceCtorEq, and_false, exists_false, or_false]
  -- The initial states of `finAcc` are the ones of `c`.
  rfl

/-- A right state is initial in the concatenation iff `c` accepts the empty word and the state is
initial in `d`. -/
theorem inr_mem_concat_start {s : d.State} :
    .inr s ∈ (NA.concat c.finAcc d.toNA).start ↔
      (∃ r, r ∈ c.toNA.start ∧ r ∈ c.accept) ∧ s ∈ d.toNA.start := by
  -- Unfold the initial states; the left part of the union contains no right states.
  simp only [NA.concat, Set.mem_union, Set.mem_image, reduceCtorEq, and_false, exists_false,
    -- Evaluate the membership in the union and in the image.
    false_or, Set.mem_ofPred_eq, Sum.inr.injEq, exists_eq_right]
  -- `c` accepts the empty word iff an initial state is accepting.
  exact and_congr_left fun _ ↦ nil_mem_language_iff

end Concatenation

/-- The automaton recognizing the concatenation of a language and an ω-language. -/
def concat (c d : EffectiveNA Symbol) : EffectiveNA Symbol where
  State := c.State ⊕ d.State
  toNA := NA.concat c.finAcc d.toNA
  accept := Sum.inr '' d.accept
  decTr
    -- Both states are in `c`: a transition of `c`.
    | .inl s, x, .inl t => inferInstanceAs (Decidable (c.toNA.Tr s x t))
    -- From `c` to `d`: a transition into an accepting state of `c` and an initial state of `d`.
    | .inl s, x, .inr t => inferInstanceAs
      (Decidable (∃ r, c.toNA.Tr s x r ∧ r ∈ c.accept ∧ t ∈ d.toNA.start))
    -- Both states are in `d`: a transition of `d`.
    | .inr s, x, .inr t => inferInstanceAs (Decidable (d.toNA.Tr s x t))
    -- There is no way back from `d` to `c`.
    | .inr _, _, .inl _ => inferInstanceAs (Decidable False)
  decStart
    -- A state of `c` is initial iff it is initial in `c`.
    | .inl _ => decidable_of_iff _ inl_mem_concat_start.symm
    -- A state of `d` is initial iff `c` accepts the empty word and it is initial in `d`.
    | .inr _ => decidable_of_iff _ inr_mem_concat_start.symm
  decAccept
    -- States of `c` are not accepting.
    | .inl _ => isFalse (by simp)
    -- A state of `d` is accepting iff it is accepting in `d`.
    | .inr s => decidable_of_iff (s ∈ d.accept) (by simp)

/-- The concatenation automaton recognizes the concatenation of a language and an ω-language. -/
theorem ωlanguage_concat (c d : EffectiveNA Symbol) :
    (c.concat d).ωlanguage = c.language * d.ωlanguage :=
  -- This is the correctness of the concatenation of automata of CSLib.
  concat_language_eq

/-- The automaton recognizing the ω-power of a language. -/
def loop (c : EffectiveNA Symbol) : EffectiveNA Symbol where
  State := Unit ⊕ c.State
  toNA := c.finAcc.loop
  accept := {.inl ()}
  decTr
    -- From the dummy state to itself: a one-letter word of the language.
    | .inl (), x, .inl () => inferInstanceAs
      (Decidable (∃ s t, c.toNA.Tr s x t ∧ s ∈ c.toNA.start ∧ t ∈ c.accept))
    -- From the dummy state into `c`: a transition from an initial state.
    | .inl (), x, .inr t => inferInstanceAs (Decidable (∃ s, c.toNA.Tr s x t ∧ s ∈ c.toNA.start))
    -- From `c` to the dummy state: a transition into an accepting state.
    | .inr s, x, .inl () => inferInstanceAs (Decidable (∃ t, c.toNA.Tr s x t ∧ t ∈ c.accept))
    -- Within `c`: a transition of `c`.
    | .inr s, x, .inr t => inferInstanceAs (Decidable (c.toNA.Tr s x t))
  decStart s := inferInstanceAs (Decidable (s = .inl ()))
  decAccept s := inferInstanceAs (Decidable (s = .inl ()))

/-- The loop automaton recognizes the ω-power of the language. -/
theorem ωlanguage_loop [Inhabited Symbol] (c : EffectiveNA Symbol) :
    c.loop.ωlanguage = c.language^ω :=
  -- This is the correctness of the loop construction of CSLib.
  loop_language_eq

section Projection

variable [FinEnum Symbol] [DecidableEq Symbol']

/-- The automaton recognizing the image of an ω-language under a letter-to-letter map. It guesses
the preimage of each letter by nondeterminism, as in the proof of Theorem 3.1 of [Thomas1997]. -/
def proj (f : Symbol → Symbol') (c : EffectiveNA Symbol) : EffectiveNA Symbol' where
  State := c.State
  toNA :=
    { Tr := fun s y t ↦ ∃ x, f x = y ∧ c.toNA.Tr s x t
      start := c.toNA.start }
  accept := c.accept
  decTr s y t := inferInstanceAs (Decidable (∃ x, f x = y ∧ c.toNA.Tr s x t))
  decStart s := inferInstanceAs (Decidable (s ∈ c.toNA.start))
  decAccept s := inferInstanceAs (Decidable (s ∈ c.accept))

omit [FinEnum Symbol] [DecidableEq Symbol'] in
/-- A run whose transitions read preimages of the letters of `α` can be turned into a run on an
ω-word that maps to `α`. -/
theorem ωlanguage_proj_aux {f : Symbol → Symbol'} {c : EffectiveNA Symbol} {α : ωSequence Symbol'}
    {ρ : ℕ → c.State} (h : ∀ i, ∃ x, f x = α i ∧ c.toNA.Tr (ρ i) x (ρ (i + 1))) :
    ∃ β : ωSequence Symbol, β.map f = α ∧ ∀ i, c.toNA.Tr (ρ i) (β i) (ρ (i + 1)) := by
  -- Choose a preimage `xs i` of each letter `α i`.
  choose xs hxs using h
  -- They form the ω-word `β`, which maps to `α` and follows the run.
  exact ⟨⟨xs⟩, DFunLike.coe_injective (funext fun i ↦ (hxs i).1), fun i ↦ (hxs i).2⟩

/-- The projection automaton recognizes the image of the ω-language. -/
theorem ωlanguage_proj (f : Symbol → Symbol') (c : EffectiveNA Symbol) :
    (proj f c).ωlanguage = c.ωlanguage.map f := by
  -- Compare on an ω-word `α`.
  refine ωLanguage.mem_ext fun α ↦ ?_
  -- Describe the acceptance by the projection by a run.
  rw [mem_ωlanguage_iff]
  -- Show both directions.
  constructor
  -- Take an accepting run of the projection.
  · rintro ⟨ρ, hs, hρ, hacc⟩
    -- Choose the letters of a preimage `β` of `α` along this run.
    obtain ⟨β, rfl, hβ⟩ := ωlanguage_proj_aux hρ
    -- The same run accepts `β` in `c`.
    exact ⟨β, mem_ωlanguage_iff.mpr ⟨ρ, hs, hβ, hacc⟩, rfl⟩
  -- Conversely, take an ω-word `β` accepted by `c` that maps to `α`.
  · rintro ⟨β, hβ, rfl⟩
    -- Take an accepting run of `c` on `β`.
    obtain ⟨ρ, hs, hρ, hacc⟩ := mem_ωlanguage_iff.mp hβ
    -- It is an accepting run of the projection on the image of `β`.
    exact ⟨ρ, hs, fun i ↦ ⟨β i, rfl, hρ i⟩, hacc⟩

end Projection

section Emptiness

variable [FinEnum Symbol] (c : EffectiveNA Symbol)

/-- There is a transition between two states. -/
def Step (s t : c.State) : Prop := ∃ x, c.toNA.Tr s x t

/-- The existence of a transition between two states is decidable. -/
instance : DecidableRel c.Step := fun s t ↦ inferInstanceAs (Decidable (∃ x, c.toNA.Tr s x t))

/-- One round of the computation of the reachable states. -/
def reachStep (R : Finset c.State) : Finset c.State :=
  R ∪ Finset.univ.filter fun t ↦ ∃ s ∈ R, c.Step s t

/-- At most `n` rounds of the computation of the reachable states, which stops when no state is
added anymore. -/
def reachRounds : ℕ → Finset c.State → Finset c.State
  | 0, R => R
  | n + 1, R =>
    let R' := c.reachStep R
    if R' = R then R else reachRounds n R'

/-- The states reachable from a set of states. -/
def reachable (R : Finset c.State) : Finset c.State := c.reachRounds (FinEnum.card c.State) R

/-- The initial states. -/
def startStates : Finset c.State := Finset.univ.filter (· ∈ c.toNA.start)

/-- The states reachable by one step from a state. -/
def successors (q : c.State) : Finset c.State := Finset.univ.filter (c.Step q)

/-- Decide whether a Büchi automaton accepts some ω-word: there is an accepting state that is
reachable from an initial state and from itself by a nonempty path. -/
def isNonempty : Bool :=
  decide (∃ q ∈ c.reachable c.startStates, q ∈ c.accept ∧ q ∈ c.reachable (c.successors q))

variable {c}

/-- A round of the computation only adds states. -/
theorem subset_reachStep (R : Finset c.State) : R ⊆ c.reachStep R :=
  -- `reachStep R` is a union with `R`.
  Finset.subset_union_left

/-- The rounds that stop early compute the same set as the iteration of all rounds. -/
theorem reachRounds_eq_iterate (n : ℕ) (R : Finset c.State) :
    c.reachRounds n R = (c.reachStep)^[n] R := by
  -- Induct on the number of rounds.
  induction n generalizing R with
  -- No rounds: nothing happens on both sides.
  | zero => rfl
  -- `n + 1` rounds:
  | succ n ih =>
    -- Unfold the first round on both sides.
    rw [reachRounds, Function.iterate_succ_apply]
    -- Distinguish whether the first round adds a state.
    split_ifs with h
    -- If it adds none, `R` is a fixed point, so further rounds do not change it.
    · rw [h, Function.iterate_fixed h]
    -- Otherwise, apply the induction hypothesis to the new set.
    · exact ih _

/-- The sets computed in the rounds either are stable or contain at least as many states as rounds
have passed. -/
theorem reachStep_iterate_stable (R : Finset c.State) (n : ℕ) :
    c.reachStep ((c.reachStep)^[n] R) = (c.reachStep)^[n] R ∨ n ≤ ((c.reachStep)^[n] R).card := by
  -- Induct on the number of rounds.
  induction n with
  -- Every set has at least `0` elements.
  | zero => exact Or.inr (Nat.zero_le _)
  -- `n + 1` rounds:
  | succ n ih =>
    -- Write the result of `n + 1` rounds as one round applied after `n` rounds.
    rw [Function.iterate_succ_apply']
    -- Distinguish whether the round after `n` rounds adds a state.
    by_cases h : c.reachStep ((c.reachStep)^[n] R) = (c.reachStep)^[n] R
    -- If it adds none, the result after `n + 1` rounds is stable as well.
    · exact Or.inl (by rw [h, h])
    -- Otherwise, we show that the result has at least `n + 1` states.
    · refine Or.inr ?_
      -- As the round adds a state, the number of states grows.
      have hlt := Finset.card_lt_card
        -- It is a strict superset, so `reachStep` adds a state.
        (Finset.ssubset_iff_subset_ne.mpr ⟨subset_reachStep _, fun h' ↦ h h'.symm⟩)
      -- Apply the induction hypothesis to the result after `n` rounds.
      rcases ih with ih | ih
      -- This result is not stable by assumption.
      · exact absurd ih h
      -- So it has at least `n` states, and the next one at least `n + 1`.
      · omega

/-- The set of reachable states is closed under transitions. -/
theorem reachStep_reachable (R : Finset c.State) : c.reachStep (c.reachable R) = c.reachable R := by
  -- Replace the computation with early stopping by the plain iteration.
  rw [reachable, reachRounds_eq_iterate]
  -- The result of `card` rounds is stable or has at least `card` states.
  rcases reachStep_iterate_stable R (FinEnum.card c.State) with h | h
  -- In the first case, we are done.
  · exact h
  -- In the second case, the result contains all states.
  · have huniv : (c.reachStep)^[FinEnum.card c.State] R = Finset.univ := by
      -- A subset of the states with at least `card` elements is everything.
      refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
      -- The two ways to count the states agree.
      rwa [← FinEnum.card_eq_fintypeCard]
    -- So the result is the set of all states.
    rw [huniv]
    -- Another round cannot add anything to the set of all states.
    exact Finset.eq_univ_of_forall fun _ ↦ subset_reachStep _ (Finset.mem_univ _)

/-- A state is computed as reachable iff there is a path from a state of the given set. -/
theorem mem_reachable {R : Finset c.State} {t : c.State} :
    t ∈ c.reachable R ↔ ∃ s ∈ R, Relation.ReflTransGen c.Step s t := by
  -- Show both directions.
  constructor
  -- Replace the computation with early stopping by the plain iteration.
  · rw [reachable, reachRounds_eq_iterate]
    -- Induct on the number of rounds.
    induction FinEnum.card c.State generalizing t with
    -- No rounds: `t` is in `R`, and the empty path leads to `t`.
    | zero => exact fun h ↦ ⟨t, h, .refl⟩
    -- `n + 1` rounds:
    | succ n ih =>
      -- Write the result as one round applied after `n` rounds.
      rw [Function.iterate_succ_apply']
      -- Let `t` be in the result.
      intro h
      -- It was either in the previous set or it was added.
      rcases Finset.mem_union.mp h with h | h
      -- In the first case, apply the induction hypothesis.
      · exact ih h
      -- In the second case, `t` has a predecessor `u` in the previous set.
      · obtain ⟨u, hu, hstep⟩ := (Finset.mem_filter.mp h).2
        -- By the induction hypothesis, there is a path from `R` to `u`.
        obtain ⟨s, hs, hsu⟩ := ih hu
        -- Extend this path by the step to `t`.
        exact ⟨s, hs, hsu.tail hstep⟩
  -- Conversely, take a path from a state of `R` to `t`.
  · rintro ⟨s, hs, hst⟩
    -- `R` is contained in the computed set.
    have hR : R ⊆ c.reachable R := by
      -- Replace the computation with early stopping by the plain iteration.
      rw [reachable, reachRounds_eq_iterate]
      -- Induct on the number of rounds.
      induction FinEnum.card c.State with
      -- No rounds: this is `R` itself.
      | zero => exact Finset.Subset.refl R
      -- `n + 1` rounds:
      | succ n ih =>
        -- Write the result as one round applied after `n` rounds.
        rw [Function.iterate_succ_apply']
        -- Rounds only add states.
        exact ih.trans (subset_reachStep _)
    -- Induct on the path.
    induction hst with
    -- The empty path ends in `R`.
    | refl => exact hR hs
    -- A longer path ends with a step from a computed state.
    | tail _ hstep ih =>
      -- The computed set is a fixed point of the round.
      rw [← reachStep_reachable]
      -- So the target of the step is in the computed set, as a round adds it.
      exact Finset.mem_union_right _
        -- The state is added as a successor of a state in the computed set.
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, ih, hstep⟩)

omit [FinEnum Symbol] in
/-- A path gives a word that moves the automaton along the path. -/
theorem exists_mTr_of_reflTransGen {s t : c.State} (h : Relation.ReflTransGen c.Step s t) :
    ∃ u, c.toNA.MTr s u t := by
  -- Induct on the path.
  induction h with
  -- The empty path corresponds to the empty word.
  | refl => exact ⟨[], .refl⟩
  -- A longer path ends with a step.
  | tail _ hstep ih =>
    -- Take the word `u` for the path without its last step.
    obtain ⟨u, hu⟩ := ih
    -- Take a letter `x` for the last step.
    obtain ⟨x, hx⟩ := hstep
    -- Then `u ++ [x]` moves the automaton along the whole path.
    exact ⟨u ++ [x], LTS.MTr.stepR _ hu hx⟩

/-- `isNonempty` decides the nonemptiness of a Büchi automaton. -/
theorem isNonempty_iff : c.isNonempty = true ↔ ∃ α, α ∈ c.ωlanguage := by
  -- Unfold the test and the computed reachable states.
  simp only [isNonempty, decide_eq_true_eq, mem_reachable]
  -- Show both directions.
  constructor
  -- A lasso: `s` reaches the accepting state `q`, which has a step to `r` that leads back to `q`.
  · rintro ⟨q, ⟨s, hs, hsq⟩, hq, r, hr, hrq⟩
    -- Take a word `u` for the path from `s` to `q`.
    obtain ⟨u, hu⟩ := exists_mTr_of_reflTransGen hsq
    -- Take a letter `x` for the step from `q` to `r`.
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hr).2
    -- Take a word `v` for the path from `r` to `q`.
    obtain ⟨v, hv⟩ := exists_mTr_of_reflTransGen hrq
    -- So the nonempty word `x :: v` leads from `q` back to `q`.
    have hloop : c.toNA.MTr q (x :: v) q := .stepL hx hv
    -- The alphabet is inhabited, as required for flattening ω-sequences of lists.
    have : Inhabited Symbol := ⟨x⟩
    -- Repeating `x :: v` gives an execution `ss` with the state `q` at all word boundaries.
    obtain ⟨ss, hss, hcum⟩ := LTS.OmegaExecution.flatten_mTr
      -- The states at the word boundaries are `q`, and all the words are `x :: v`.
      (ts := ωSequence.const q) (μls := ωSequence.const (x :: v)) (fun _ ↦ hloop)
      -- All these words are nonempty.
      (fun _ ↦ Nat.succ_pos _)
    -- In particular, `ss` starts in `q`.
    have hss0 : ss 0 = q := hcum 0
    -- Prepending the path for `u` gives an execution `ss'` from `s`.
    obtain ⟨ss', hss', h0, -, hdrop⟩ := LTS.OmegaExecution.append hu hss hss0
    -- This is a run on `u` followed by the repetition; it remains to show the acceptance.
    refine ⟨_, mem_ωlanguage_iff.mpr ⟨ss', h0 ▸ (Finset.mem_filter.mp hs).2, hss', ?_⟩⟩
    -- Infinitely often means after each position.
    rw [frequently_atTop]
    -- Let `a` be a position.
    intro a
    -- The word boundaries grow strictly, as `x :: v` is nonempty.
    have hmono := cumLen_strictMono (ls := ωSequence.const (x :: v)) (fun _ ↦ Nat.succ_pos _)
    -- The word boundary number `a`, shifted by the length of `u`, is a position after `a`.
    refine ⟨(ωSequence.const (x :: v)).cumLen a + u.length,
      -- The position is at least `a`, as the word boundaries grow strictly.
      (hmono.le_apply).trans (Nat.le_add_right _ _), ?_⟩
    -- At this position, the state of `ss'`
    have : ss' ((ωSequence.const (x :: v)).cumLen a + u.length) =
        -- is the state of `ss` at the word boundary.
        ss ((ωSequence.const (x :: v)).cumLen a) := by
      -- `ss` is `ss'` after dropping the prefix of the length of `u`.
      rw [← hdrop]
      -- So the states are the same by definition of `drop`.
      rfl
    -- Hence the state at this position is `q`.
    rw [this, hcum]
    -- And `q` is accepting.
    exact hq
  -- Conversely, take an accepted ω-word `α`.
  · rintro ⟨α, hα⟩
    -- Take an accepting run `ρ` on `α`.
    obtain ⟨ρ, hs, hρ, hacc⟩ := mem_ωlanguage_iff.mp hα
    -- There are only finitely many states.
    have : Finite c.State := inferInstance
    -- So some accepting state `q` occurs infinitely often in the run.
    obtain ⟨q, hq, hfreq⟩ := (frequently_in_finite_type (xs := ⟨ρ⟩)).mp hacc
    -- Later states of the run are reachable from earlier ones.
    have hsteps : ∀ {i j}, i ≤ j → Relation.ReflTransGen c.Step (ρ i) (ρ j) := by
      -- Let `i ≤ j`.
      intro i j hij
      -- Induct on `j`, starting from `i`.
      induction j, hij using Nat.le_induction with
      -- The empty path for `j = i`.
      | base => exact .refl
      -- A further transition of the run extends the path.
      | succ j _ ih => exact ih.tail ⟨_, hρ j⟩
    -- Take an occurrence `k₀` of `q`.
    obtain ⟨k₀, -, hk₀⟩ := frequently_atTop.mp hfreq 0
    -- Take a later occurrence `k₁` of `q`.
    obtain ⟨k₁, hk₁, hk₁q⟩ := frequently_atTop.mp hfreq (k₀ + 1)
    -- The lasso: the first state reaches `q`, and `q` has a step to `ρ (k₀ + 1)` that leads back.
    refine ⟨q, ⟨ρ 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq, ρ (k₀ + 1), ?_, ?_⟩
    -- `q` is the state at `k₀`.
    · rw [← show ρ k₀ = q from hk₀]
      -- It is reachable from the first state of the run.
      exact hsteps (Nat.zero_le _)
    -- The state `ρ (k₀ + 1)` is a successor of `q`.
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      -- `q` is the state at `k₀`.
      rw [← show ρ k₀ = q from hk₀]
      -- The transition of the run at `k₀` is the step.
      exact ⟨_, hρ k₀⟩
    -- `q` is the state at `k₁`.
    · rw [← show ρ k₁ = q from hk₁q]
      -- It is reachable from `ρ (k₀ + 1)`, as `k₀ + 1 ≤ k₁`.
      exact hsteps hk₁

end Emptiness

end Cslib.Automata.EffectiveNA
