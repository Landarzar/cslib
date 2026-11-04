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
  nonempty path.

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

@[simp]
theorem ωlanguage_bot : (bot : EffectiveNA Symbol).ωlanguage = ⊥ := by
  ext α
  constructor
  · rintro ⟨ρ, -, -⟩
    exact (ρ 0).elim
  · exact fun h ↦ h.elim

section Union

variable {I : Type} [FinEnum I]

omit [FinEnum I] in
theorem mem_iUnion_sigma_image {β : I → Type} {S : (i : I) → Set (β i)} {i : I} {a : β i} :
    (⟨i, a⟩ : Σ i, β i) ∈ ⋃ j, Sigma.mk j '' S j ↔ a ∈ S i := by
  simp only [Set.mem_iUnion, Set.mem_image, Sigma.mk.injEq]
  constructor
  · rintro ⟨j, b, hb, rfl, h⟩
    obtain rfl := eq_of_heq h
    exact hb
  · exact fun h ↦ ⟨i, a, h, rfl, HEq.rfl⟩

omit [FinEnum I] in
theorem iSum_tr_iff {β : I → Type} {na : (i : I) → NA (β i) Symbol} {i j : I} {s : β i} {t : β j}
    {x : Symbol} :
    (NA.iSum na).Tr ⟨i, s⟩ x ⟨j, t⟩ ↔ ∃ h : i = j, (na j).Tr (h ▸ s) x t := by
  constructor
  · rintro ⟨k, s', t', hTr, h₁, h₂⟩
    cases h₁
    cases h₂
    exact ⟨rfl, hTr⟩
  · rintro ⟨rfl, h⟩
    exact ⟨i, s, t, h, rfl, rfl⟩

/-- The automaton recognizing the union of finitely many ω-languages. -/
def iSup (c : I → EffectiveNA Symbol) : EffectiveNA Symbol where
  State := Σ i, (c i).State
  toNA := NA.iSum fun i ↦ (c i).toNA
  accept := ⋃ i, Sigma.mk i '' (c i).accept
  decTr
    | ⟨i, s⟩, x, ⟨j, t⟩ => decidable_of_iff (∃ h : i = j, (c j).toNA.Tr (h ▸ s) x t)
      (iSum_tr_iff (β := fun i ↦ (c i).State) (na := fun i ↦ (c i).toNA)).symm
  decStart
    | ⟨i, a⟩ => decidable_of_iff (a ∈ (c i).toNA.start)
      (mem_iUnion_sigma_image (S := fun i ↦ (c i).toNA.start)).symm
  decAccept
    | ⟨i, a⟩ => decidable_of_iff (a ∈ (c i).accept)
      (mem_iUnion_sigma_image (S := fun i ↦ (c i).accept)).symm

theorem ωlanguage_iSup (c : I → EffectiveNA Symbol) : (iSup c).ωlanguage = ⨆ i, (c i).ωlanguage :=
  iSum_language_eq (na := fun i ↦ (c i).toNA) (acc := fun i ↦ (c i).accept)

end Union

/-- The automaton recognizing the union of two ω-languages. -/
def sup (c d : EffectiveNA Symbol) : EffectiveNA Symbol := iSup fun b : Bool ↦ cond b c d

theorem ωlanguage_sup (c d : EffectiveNA Symbol) :
    (c.sup d).ωlanguage = c.ωlanguage ⊔ d.ωlanguage := by
  change (iSup _).ωlanguage = _
  rw [ωlanguage_iSup, iSup_bool_eq]
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

theorem iInfBoolNA_eq : iInfBoolNA e = interNA (fun i ↦ (e i).toNA) fun i ↦ (e i).accept := by
  have hist : ∀ (s : (Π i, (e i).State) × Bool) (x : Symbol) (t : Π i, (e i).State),
      histTrans (fun i ↦ (e i).accept) s x t = histStep e s := by
    grind [histTrans, histStep, interAcc]
  simp only [iInfBoolNA, interNA, NA.addHist, NA.iProd, hist, histStart]
  congr
  ext s
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

theorem ωlanguage_iInfBool : (iInfBool e).ωlanguage = ⨅ i, (e i).ωlanguage := by
  have h := inter_language_eq (na := fun i ↦ (e i).toNA) (acc := fun i ↦ (e i).accept)
  rw [← iInfBoolNA_eq] at h
  exact h

end Intersection

/-- The automaton recognizing the intersection of two ω-languages. -/
def inf (c d : EffectiveNA Symbol) : EffectiveNA Symbol := iInfBool fun b : Bool ↦ cond b c d

theorem ωlanguage_inf (c d : EffectiveNA Symbol) :
    (c.inf d).ωlanguage = c.ωlanguage ⊓ d.ωlanguage := by
  change (iInfBool _).ωlanguage = _
  rw [ωlanguage_iInfBool, iInf_bool_eq]
  rfl

/-- `[]` is accepted iff an initial state is an accepting state. -/
theorem nil_mem_language_iff {c : EffectiveNA Symbol} :
    [] ∈ c.language ↔ ∃ s, s ∈ c.toNA.start ∧ s ∈ c.accept := by
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    obtain rfl := LTS.MTr.nil_eq _ h
    exact ⟨s, hs, ht⟩
  · rintro ⟨s, hs, ha⟩
    exact ⟨s, hs, s, ha, .refl⟩

section Concatenation

variable {c d : EffectiveNA Symbol}

theorem inl_mem_concat_start {s : c.State} :
    .inl s ∈ (NA.concat c.finAcc d.toNA).start ↔ s ∈ c.toNA.start := by
  simp only [NA.concat, Set.mem_union, Set.mem_image, Sum.inl.injEq, exists_eq_right,
    Set.mem_ofPred_eq, reduceCtorEq, and_false, exists_false, or_false]
  rfl

theorem inr_mem_concat_start {s : d.State} :
    .inr s ∈ (NA.concat c.finAcc d.toNA).start ↔
      (∃ r, r ∈ c.toNA.start ∧ r ∈ c.accept) ∧ s ∈ d.toNA.start := by
  simp only [NA.concat, Set.mem_union, Set.mem_image, reduceCtorEq, and_false, exists_false,
    false_or, Set.mem_ofPred_eq, Sum.inr.injEq, exists_eq_right]
  exact and_congr_left fun _ ↦ nil_mem_language_iff

end Concatenation

/-- The automaton recognizing the concatenation of a language and an ω-language. -/
def concat (c d : EffectiveNA Symbol) : EffectiveNA Symbol where
  State := c.State ⊕ d.State
  toNA := NA.concat c.finAcc d.toNA
  accept := Sum.inr '' d.accept
  decTr
    | .inl s, x, .inl t => inferInstanceAs (Decidable (c.toNA.Tr s x t))
    | .inl s, x, .inr t => inferInstanceAs
      (Decidable (∃ r, c.toNA.Tr s x r ∧ r ∈ c.accept ∧ t ∈ d.toNA.start))
    | .inr s, x, .inr t => inferInstanceAs (Decidable (d.toNA.Tr s x t))
    | .inr _, _, .inl _ => inferInstanceAs (Decidable False)
  decStart
    | .inl _ => decidable_of_iff _ inl_mem_concat_start.symm
    | .inr _ => decidable_of_iff _ inr_mem_concat_start.symm
  decAccept
    | .inl _ => isFalse (by simp)
    | .inr s => decidable_of_iff (s ∈ d.accept) (by simp)

theorem ωlanguage_concat (c d : EffectiveNA Symbol) :
    (c.concat d).ωlanguage = c.language * d.ωlanguage :=
  concat_language_eq

/-- The automaton recognizing the ω-power of a language. -/
def loop (c : EffectiveNA Symbol) : EffectiveNA Symbol where
  State := Unit ⊕ c.State
  toNA := c.finAcc.loop
  accept := {.inl ()}
  decTr
    | .inl (), x, .inl () => inferInstanceAs
      (Decidable (∃ s t, c.toNA.Tr s x t ∧ s ∈ c.toNA.start ∧ t ∈ c.accept))
    | .inl (), x, .inr t => inferInstanceAs (Decidable (∃ s, c.toNA.Tr s x t ∧ s ∈ c.toNA.start))
    | .inr s, x, .inl () => inferInstanceAs (Decidable (∃ t, c.toNA.Tr s x t ∧ t ∈ c.accept))
    | .inr s, x, .inr t => inferInstanceAs (Decidable (c.toNA.Tr s x t))
  decStart s := inferInstanceAs (Decidable (s = .inl ()))
  decAccept s := inferInstanceAs (Decidable (s = .inl ()))

theorem ωlanguage_loop [Inhabited Symbol] (c : EffectiveNA Symbol) :
    c.loop.ωlanguage = c.language^ω :=
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
theorem ωlanguage_proj_aux {f : Symbol → Symbol'} {c : EffectiveNA Symbol} {α : ωSequence Symbol'}
    {ρ : ℕ → c.State} (h : ∀ i, ∃ x, f x = α i ∧ c.toNA.Tr (ρ i) x (ρ (i + 1))) :
    ∃ β : ωSequence Symbol, β.map f = α ∧ ∀ i, c.toNA.Tr (ρ i) (β i) (ρ (i + 1)) := by
  choose xs hxs using h
  exact ⟨⟨xs⟩, DFunLike.coe_injective (funext fun i ↦ (hxs i).1), fun i ↦ (hxs i).2⟩

theorem ωlanguage_proj (f : Symbol → Symbol') (c : EffectiveNA Symbol) :
    (proj f c).ωlanguage = c.ωlanguage.map f := by
  refine ωLanguage.mem_ext fun α ↦ ?_
  rw [mem_ωlanguage_iff]
  constructor
  · rintro ⟨ρ, hs, hρ, hacc⟩
    obtain ⟨β, rfl, hβ⟩ := ωlanguage_proj_aux hρ
    exact ⟨β, mem_ωlanguage_iff.mpr ⟨ρ, hs, hβ, hacc⟩, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨ρ, hs, hρ, hacc⟩ := mem_ωlanguage_iff.mp hβ
    exact ⟨ρ, hs, fun i ↦ ⟨β i, rfl, hρ i⟩, hacc⟩

end Projection

section Emptiness

variable [FinEnum Symbol] (c : EffectiveNA Symbol)

/-- There is a transition between two states. -/
def Step (s t : c.State) : Prop := ∃ x, c.toNA.Tr s x t

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

theorem subset_reachStep (R : Finset c.State) : R ⊆ c.reachStep R := Finset.subset_union_left

/-- The rounds that stop early compute the same set as the iteration of all rounds. -/
theorem reachRounds_eq_iterate (n : ℕ) (R : Finset c.State) :
    c.reachRounds n R = (c.reachStep)^[n] R := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [reachRounds, Function.iterate_succ_apply]
    split_ifs with h
    · rw [h, Function.iterate_fixed h]
    · exact ih _

/-- The sets computed in the rounds either are stable or contain at least as many states as rounds
have passed. -/
theorem reachStep_iterate_stable (R : Finset c.State) (n : ℕ) :
    c.reachStep ((c.reachStep)^[n] R) = (c.reachStep)^[n] R ∨ n ≤ ((c.reachStep)^[n] R).card := by
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : c.reachStep ((c.reachStep)^[n] R) = (c.reachStep)^[n] R
    · exact Or.inl (by rw [h, h])
    · refine Or.inr ?_
      have hlt := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨subset_reachStep _, fun h' ↦ h h'.symm⟩)
      rcases ih with ih | ih
      · exact absurd ih h
      · omega

/-- The set of reachable states is closed under transitions. -/
theorem reachStep_reachable (R : Finset c.State) : c.reachStep (c.reachable R) = c.reachable R := by
  rw [reachable, reachRounds_eq_iterate]
  rcases reachStep_iterate_stable R (FinEnum.card c.State) with h | h
  · exact h
  · have huniv : (c.reachStep)^[FinEnum.card c.State] R = Finset.univ := by
      refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
      rwa [← FinEnum.card_eq_fintypeCard]
    rw [huniv]
    exact Finset.eq_univ_of_forall fun _ ↦ subset_reachStep _ (Finset.mem_univ _)

/-- A state is computed as reachable iff there is a path from a state of the given set. -/
theorem mem_reachable {R : Finset c.State} {t : c.State} :
    t ∈ c.reachable R ↔ ∃ s ∈ R, Relation.ReflTransGen c.Step s t := by
  constructor
  · rw [reachable, reachRounds_eq_iterate]
    induction FinEnum.card c.State generalizing t with
    | zero => exact fun h ↦ ⟨t, h, .refl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact ih h
      · obtain ⟨u, hu, hstep⟩ := (Finset.mem_filter.mp h).2
        obtain ⟨s, hs, hsu⟩ := ih hu
        exact ⟨s, hs, hsu.tail hstep⟩
  · rintro ⟨s, hs, hst⟩
    have hR : R ⊆ c.reachable R := by
      rw [reachable, reachRounds_eq_iterate]
      induction FinEnum.card c.State with
      | zero => exact Finset.Subset.refl R
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (subset_reachStep _)
    induction hst with
    | refl => exact hR hs
    | tail _ hstep ih =>
      rw [← reachStep_reachable]
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, ih, hstep⟩)

omit [FinEnum Symbol] in
/-- A path gives a word that moves the automaton along the path. -/
theorem exists_mTr_of_reflTransGen {s t : c.State} (h : Relation.ReflTransGen c.Step s t) :
    ∃ u, c.toNA.MTr s u t := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | tail _ hstep ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨x, hx⟩ := hstep
    exact ⟨u ++ [x], LTS.MTr.stepR _ hu hx⟩

/-- `isNonempty` decides the nonemptiness of a Büchi automaton. -/
theorem isNonempty_iff : c.isNonempty = true ↔ ∃ α, α ∈ c.ωlanguage := by
  simp only [isNonempty, decide_eq_true_eq, mem_reachable]
  constructor
  · rintro ⟨q, ⟨s, hs, hsq⟩, hq, r, hr, hrq⟩
    obtain ⟨u, hu⟩ := exists_mTr_of_reflTransGen hsq
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hr).2
    obtain ⟨v, hv⟩ := exists_mTr_of_reflTransGen hrq
    have hloop : c.toNA.MTr q (x :: v) q := .stepL hx hv
    have : Inhabited Symbol := ⟨x⟩
    obtain ⟨ss, hss, hcum⟩ := LTS.OmegaExecution.flatten_mTr
      (ts := ωSequence.const q) (μls := ωSequence.const (x :: v)) (fun _ ↦ hloop)
      (fun _ ↦ Nat.succ_pos _)
    have hss0 : ss 0 = q := hcum 0
    obtain ⟨ss', hss', h0, -, hdrop⟩ := LTS.OmegaExecution.append hu hss hss0
    refine ⟨_, mem_ωlanguage_iff.mpr ⟨ss', h0 ▸ (Finset.mem_filter.mp hs).2, hss', ?_⟩⟩
    rw [frequently_atTop]
    intro a
    have hmono := cumLen_strictMono (ls := ωSequence.const (x :: v)) (fun _ ↦ Nat.succ_pos _)
    refine ⟨(ωSequence.const (x :: v)).cumLen a + u.length,
      (hmono.le_apply).trans (Nat.le_add_right _ _), ?_⟩
    have : ss' ((ωSequence.const (x :: v)).cumLen a + u.length) =
        ss ((ωSequence.const (x :: v)).cumLen a) := by
      rw [← hdrop]
      rfl
    rw [this, hcum]
    exact hq
  · rintro ⟨α, hα⟩
    obtain ⟨ρ, hs, hρ, hacc⟩ := mem_ωlanguage_iff.mp hα
    have : Finite c.State := inferInstance
    obtain ⟨q, hq, hfreq⟩ := (frequently_in_finite_type (xs := ⟨ρ⟩)).mp hacc
    have hsteps : ∀ {i j}, i ≤ j → Relation.ReflTransGen c.Step (ρ i) (ρ j) := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact .refl
      | succ j _ ih => exact ih.tail ⟨_, hρ j⟩
    obtain ⟨k₀, -, hk₀⟩ := frequently_atTop.mp hfreq 0
    obtain ⟨k₁, hk₁, hk₁q⟩ := frequently_atTop.mp hfreq (k₀ + 1)
    refine ⟨q, ⟨ρ 0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩, hq, ρ (k₀ + 1), ?_, ?_⟩
    · rw [← show ρ k₀ = q from hk₀]
      exact hsteps (Nat.zero_le _)
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← show ρ k₀ = q from hk₀]
      exact ⟨_, hρ k₀⟩
    · rw [← show ρ k₁ = q from hk₁q]
      exact hsteps hk₁

end Emptiness

end Cslib.Automata.EffectiveNA
