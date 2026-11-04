/-
Copyright (c) 2026 Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Sauerwald
-/

module

public import Cslib.Logics.MSO.Basic

/-! # The logic MSO₀ and the track models

MSO₀ is the variant of monadic second-order logic without first-order variables which is used in
the proof that MSO-definable languages are regular (Section 2.3 of [Thomas1997]). First-order
variables are simulated by singletons, and the atomic formulas are `X ⊆ Y`, `Sing(X)`, `Suc(X, Y)`
and `X ⊆ Q_a`.

A word model with `n` designated subsets is represented by a word model over the extended alphabet
`A × {0, 1}ⁿ`, the *track alphabet* `Track A n`.

## Main definitions and results

- `Formula₀`, `Formula₀.Satisfies`: the formulas of MSO₀ and their semantics.
- `Formula.toFormula₀`: the translation of MSO into MSO₀, correct by `satisfies_toFormula₀`.
- `Track`, `WordModel.base`, `WordModel.tracks`: the track alphabet and the components of a word
  model over it.
- `Formula₀.language`, `Formula₀.ωlanguage`: the languages over the track alphabet defined by a
  formula of MSO₀.
- `Formula₀.language_ex`, `Formula₀.ωlanguage_ex`: existential set quantification corresponds to
  the projection of languages.

## Implementation notes

In contrast to the reference, the conjunction is primitive in MSO₀. This way, the translation of
first-order quantifiers does not need complementation when compiling formulas into automata.

## References

* [W. Thomas, *Languages, Automata, and Logic*][Thomas1997]
-/

@[expose] public section

namespace Cslib.Logic.MSO

open WordModel

universe u

variable {A : Type u} {k l n : ℕ}

/-- Formulas of MSO₀ over the alphabet `A` with `n` free variables, which range over sets. -/
inductive Formula₀ (A : Type u) : ℕ → Type u where
  /-- `X ⊆ Y` -/
  | sub {n : ℕ} (X Y : Fin n) : Formula₀ A n
  /-- `Sing(X)`: `X` is a singleton. -/
  | sing {n : ℕ} (X : Fin n) : Formula₀ A n
  /-- `Suc(X, Y)`: `X` and `Y` are singletons `{x}` and `{y}` such that `y` is the successor of
  `x`. -/
  | suc {n : ℕ} (X Y : Fin n) : Formula₀ A n
  /-- `X ⊆ Q_a`: all positions of `X` carry the letter `a`. -/
  | subLabel {n : ℕ} (X : Fin n) (a : A) : Formula₀ A n
  /-- Negation. -/
  | not {n : ℕ} (φ : Formula₀ A n) : Formula₀ A n
  /-- Disjunction. -/
  | or {n : ℕ} (φ ψ : Formula₀ A n) : Formula₀ A n
  /-- Conjunction. -/
  | and {n : ℕ} (φ ψ : Formula₀ A n) : Formula₀ A n
  /-- Existential quantification over sets. -/
  | ex {n : ℕ} (φ : Formula₀ A (n + 1)) : Formula₀ A n

namespace Formula₀

/-- Satisfaction of a formula of MSO₀ in a word model with an interpretation of its variables. -/
def Satisfies (M : WordModel A) : {n : ℕ} → (Fin n → Set ℕ) → Formula₀ A n → Prop
  | _, V, .sub X Y => V X ⊆ V Y
  | _, V, .sing X => ∃ p, V X = {p}
  | _, V, .suc X Y => ∃ p, V X = {p} ∧ V Y = {p + 1}
  | _, V, .subLabel X a => ∀ p ∈ V X, M.label p = some a
  | _, V, .not φ => ¬Satisfies M V φ
  | _, V, .or φ ψ => Satisfies M V φ ∨ Satisfies M V ψ
  | _, V, .and φ ψ => Satisfies M V φ ∧ Satisfies M V ψ
  | _, V, .ex φ => ∃ P ⊆ M.dom, Satisfies M (Fin.snoc (α := fun _ ↦ Set ℕ) V P) φ

end Formula₀

namespace Formula

/-- The translation of MSO into MSO₀ (Section 2.3 of [Thomas1997]) along an assignment of the
first-order variables `ρ` and second-order variables `τ` to the variables of MSO₀. This translation
requires a formula of MSO[S]: the order relation has to be eliminated first with `elimLt`, and the
case of `x < y` is a placeholder that does not occur for such formulas. -/
def toMSO₀ : {k l : ℕ} → Formula A k l → {n : ℕ} → (Fin k → Fin n) → (Fin l → Fin n) → Formula₀ A n
  | _, _, .eq x y, _, ρ, _ => .sub (ρ x) (ρ y)
  | _, _, .succ x y, _, ρ, _ => .suc (ρ x) (ρ y)
  | _, _, .lt x _, _, ρ, _ => .not (.sub (ρ x) (ρ x))
  | _, _, .label a x, _, ρ, _ => .subLabel (ρ x) a
  | _, _, .mem x X, _, ρ, τ => .sub (ρ x) (τ X)
  | _, _, .not φ, _, ρ, τ => .not (φ.toMSO₀ ρ τ)
  | _, _, .or φ ψ, _, ρ, τ => .or (φ.toMSO₀ ρ τ) (ψ.toMSO₀ ρ τ)
  | _, _, .ex₁ φ, n, ρ, τ =>
    .ex (.and (.sing (Fin.last n)) (φ.toMSO₀
      (Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last n))
      (fun X ↦ (τ X).castSucc)))
  | _, _, .ex₂ φ, n, ρ, τ =>
    .ex (φ.toMSO₀ (fun x ↦ (ρ x).castSucc)
      (Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun X ↦ (τ X).castSucc) (Fin.last n)))

/-- The translation into MSO₀ is correct for formulas of MSO[S], when the variables of MSO₀
interpret first-order variables by singletons. -/
theorem satisfies_toMSO₀ {M : WordModel A} {φ : Formula A k l} (hφ : φ.LtFree)
    {ρ : Fin k → Fin n} {τ : Fin l → Fin n} {V : Fin n → Set ℕ} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hρ : ∀ x, V (ρ x) = {v x}) (hτ : ∀ X, V (τ X) = W X) :
    Formula₀.Satisfies M V (φ.toMSO₀ ρ τ) ↔ Satisfies M v W φ := by
  induction φ generalizing n with
  | eq x y =>
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.singleton_subset_iff,
      Set.mem_singleton_iff]
  | succ x y =>
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.singleton_eq_singleton_iff]
    constructor
    · rintro ⟨p, rfl, h⟩
      exact h
    · exact fun h ↦ ⟨v x, rfl, h⟩
  | lt x y => exact hφ.elim
  | label a x =>
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.mem_singleton_iff, forall_eq]
  | mem x X =>
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, hτ, Set.singleton_subset_iff]
  | not φ ih => exact not_congr (ih hφ hρ hτ)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hφ.1 hρ hτ) (ihψ hφ.2 hρ hτ)
  | @ex₁ k l φ ih =>
    have key {p : ℕ} := ih (n := n + 1) hφ
      (ρ := Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last n))
      (τ := fun X ↦ (τ X).castSucc)
      (V := Fin.snoc (α := fun _ ↦ Set ℕ) V {p})
      (v := Fin.snoc (α := fun _ ↦ ℕ) v p) (W := W)
      (fun x ↦ by
        induction x using Fin.lastCases with
        | last => simp
        | cast x => simpa using hρ x)
      (fun X ↦ by simpa using hτ X)
    simp only [toMSO₀, Formula₀.Satisfies, Fin.snoc_last, Satisfies]
    constructor
    · rintro ⟨P, hP, ⟨p, rfl⟩, h⟩
      exact ⟨p, hP rfl, key.mp h⟩
    · rintro ⟨p, hp, h⟩
      exact ⟨{p}, Set.singleton_subset_iff.mpr hp, ⟨p, rfl⟩, key.mpr h⟩
  | @ex₂ k l φ ih =>
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies]
    refine exists_congr fun P ↦ and_congr_right fun _ ↦ ih hφ (fun x ↦ ?_) (fun X ↦ ?_)
    · simpa using hρ x
    · induction X using Fin.lastCases with
      | last => simp
      | cast X => simpa using hτ X

/-- The translation of an arbitrary formula of MSO into MSO₀, where the variables of MSO₀ are the
first-order variables followed by the second-order variables. -/
def toFormula₀ (φ : Formula A k l) : Formula₀ A (k + l) :=
  φ.elimLt.toMSO₀ (Fin.castAdd l) (Fin.natAdd k)

/-- The translation into MSO₀ is correct. -/
theorem satisfies_toFormula₀ {M : WordModel A} (φ : Formula A k l) {v : Fin k → ℕ}
    (hv : ∀ x, v x ∈ M.dom) {W : Fin l → Set ℕ} :
    Formula₀.Satisfies M (Fin.append (α := Set ℕ) (fun x ↦ {v x}) W) φ.toFormula₀ ↔
      Satisfies M v W φ := by
  rw [toFormula₀, satisfies_toMSO₀ (ltFree_elimLt φ) (v := v) (W := W), satisfies_elimLt φ hv]
  · exact fun x ↦ Fin.append_left _ _ x
  · exact fun X ↦ Fin.append_right _ _ X

end Formula

/-- The track alphabet `A × {0, 1}ⁿ`. The `j`-th bit of a letter at a position tells whether the
position belongs to the `j`-th designated set. -/
abbrev Track (A : Type u) (n : ℕ) := A × (Fin n → Bool)

/-- Forget the last component of a letter of the track alphabet. -/
def trackInit (x : Track A (n + 1)) : Track A n := (x.1, fun j ↦ x.2 j.castSucc)

namespace WordModel

/-- The word model underlying a word model over the track alphabet. -/
def base (M : WordModel (Track A n)) : WordModel A := M.map Prod.fst

/-- The designated sets of a word model over the track alphabet. -/
def tracks (M : WordModel (Track A n)) (j : Fin n) : Set ℕ :=
  {i | ∃ x, M.label i = some x ∧ x.2 j = true}

@[simp]
theorem base_label (M : WordModel (Track A n)) (i : ℕ) :
    M.base.label i = (M.label i).map Prod.fst := rfl

@[simp]
theorem dom_base (M : WordModel (Track A n)) : M.base.dom = M.dom := dom_map _ _

theorem mem_tracks {M : WordModel (Track A n)} {j : Fin n} {i : ℕ} :
    i ∈ M.tracks j ↔ ∃ x, M.label i = some x ∧ x.2 j = true := Iff.rfl

theorem tracks_subset_dom (M : WordModel (Track A n)) (j : Fin n) : M.tracks j ⊆ M.dom := by
  rintro i ⟨x, hx, -⟩
  simp [mem_dom, hx]

@[simp]
theorem base_map_trackInit (M : WordModel (Track A (n + 1))) : (M.map trackInit).base = M.base := by
  ext1
  funext i
  simp only [base_label, map_label, Option.map_map]
  rfl

/-- The designated sets of a model over the track alphabet are the ones of its projection together
with the last one. -/
theorem tracks_eq_snoc (M : WordModel (Track A (n + 1))) :
    M.tracks = Fin.snoc (α := fun _ ↦ Set ℕ) (M.map trackInit).tracks (M.tracks (Fin.last n)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast j =>
    ext i
    simp [mem_tracks, trackInit]

open Classical in
/-- Add the set `P` as a further designated set to a model over the track alphabet. -/
noncomputable def extend (M : WordModel (Track A n)) (P : Set ℕ) : WordModel (Track A (n + 1)) where
  label i := (M.label i).map fun x ↦ (x.1, Fin.snoc (α := fun _ ↦ Bool) x.2 (decide (i ∈ P)))
  isSome_of_le hij hj := by
    simp only [Option.isSome_map] at hj ⊢
    exact M.isSome_of_le hij hj

@[simp]
theorem map_trackInit_extend (M : WordModel (Track A n)) (P : Set ℕ) :
    (M.extend P).map trackInit = M := by
  ext1
  funext i
  cases h : M.label i <;> simp [extend, trackInit, h]

@[simp]
theorem tracks_extend {M : WordModel (Track A n)} {P : Set ℕ} (hP : P ⊆ M.dom) :
    (M.extend P).tracks = Fin.snoc (α := fun _ ↦ Set ℕ) M.tracks P := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    ext i
    simp only [mem_tracks, extend, Option.map_eq_some_iff, Fin.snoc_last]
    constructor
    · rintro ⟨_, ⟨x, -, rfl⟩, h⟩
      simpa using h
    · intro hi
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hP hi)
      exact ⟨_, ⟨x, hx, rfl⟩, by simpa using hi⟩
  | cast j =>
    ext i
    simp only [mem_tracks, extend, Option.map_eq_some_iff, Fin.snoc_castSucc]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
      exact ⟨x, hx, by simpa using h⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨_, ⟨x, hx, rfl⟩, by simpa using h⟩

@[simp]
theorem base_extend (M : WordModel (Track A n)) (P : Set ℕ) : (M.extend P).base = M.base := by
  rw [← base_map_trackInit (M.extend P), map_trackInit_extend]

@[simp]
theorem notMem_tracks_ofList_nil {j : Fin n} {i : ℕ} :
    i ∉ (ofList ([] : List (Track A n))).tracks j := by
  simp [mem_tracks]

@[simp]
theorem zero_mem_tracks_ofList_cons {x : Track A n} {w : List (Track A n)} {j : Fin n} :
    0 ∈ (ofList (x :: w)).tracks j ↔ x.2 j = true := by
  simp [mem_tracks]

@[simp]
theorem succ_mem_tracks_ofList_cons {x : Track A n} {w : List (Track A n)} {j : Fin n} {i : ℕ} :
    i + 1 ∈ (ofList (x :: w)).tracks j ↔ i ∈ (ofList w).tracks j := by
  simp [mem_tracks]

end WordModel

namespace Formula₀

/-- A word model over the track alphabet is a model of a formula of MSO₀ if the formula holds in the
underlying word model when its variables are interpreted by the designated sets. -/
def Models (φ : Formula₀ A n) (M : WordModel (Track A n)) : Prop := φ.Satisfies M.base M.tracks

/-- The language over the track alphabet defined by a formula of MSO₀. -/
def language (φ : Formula₀ A n) : Language (Track A n) := {w | φ.Models (ofList w)}

/-- The ω-language over the track alphabet defined by a formula of MSO₀. -/
def ωlanguage (φ : Formula₀ A n) : ωLanguage (Track A n) := ⟨{α | φ.Models (ofOmega α)}⟩

@[simp]
theorem mem_language {φ : Formula₀ A n} {w : List (Track A n)} :
    w ∈ φ.language ↔ φ.Models (ofList w) := Iff.rfl

@[simp]
theorem mem_ωlanguage {φ : Formula₀ A n} {α : ωSequence (Track A n)} :
    α ∈ φ.ωlanguage ↔ φ.Models (ofOmega α) := Iff.rfl

/-- Existential set quantification: `∃X φ` holds in a model iff `φ` holds in some extension of the
model by a further designated set. -/
theorem models_ex_iff {φ : Formula₀ A (n + 1)} {M : WordModel (Track A n)} :
    (ex φ).Models M ↔ ∃ M' : WordModel (Track A (n + 1)), M'.map trackInit = M ∧ φ.Models M' := by
  constructor
  · rintro ⟨P, hP, h⟩
    rw [dom_base] at hP
    refine ⟨M.extend P, map_trackInit_extend M P, ?_⟩
    rwa [Models, base_extend, tracks_extend hP]
  · rintro ⟨M', rfl, h⟩
    refine ⟨M'.tracks (Fin.last n), ?_, ?_⟩
    · rw [dom_base, dom_map]
      exact tracks_subset_dom M' _
    · rwa [base_map_trackInit, ← tracks_eq_snoc]

/-- Existential set quantification corresponds to the projection of the language. -/
theorem language_ex {φ : Formula₀ A (n + 1)} : (ex φ).language = φ.language.map trackInit := by
  ext w
  rw [mem_language, models_ex_iff]
  constructor
  · rintro ⟨M', hM', h⟩
    obtain ⟨w', -, rfl⟩ :=
      M'.exists_eq_ofList w.length fun i ↦ by simp [← dom_map trackInit M', hM']
    rw [map_ofList] at hM'
    exact ⟨w', h, ofList_injective hM'⟩
  · rintro ⟨w', h, rfl⟩
    exact ⟨ofList w', map_ofList _ _, h⟩

/-- Existential set quantification corresponds to the projection of the ω-language. -/
theorem ωlanguage_ex {φ : Formula₀ A (n + 1)} : (ex φ).ωlanguage = φ.ωlanguage.map trackInit := by
  ext α
  change (ex φ).Models (ofOmega α) ↔ _
  rw [models_ex_iff]
  constructor
  · rintro ⟨M', hM', h⟩
    obtain ⟨α', rfl⟩ := M'.exists_eq_ofOmega fun i ↦ by simp [← dom_map trackInit M', hM']
    rw [map_ofOmega] at hM'
    exact ⟨α', h, ofOmega_injective hM'⟩
  · rintro ⟨α', h, rfl⟩
    exact ⟨ofOmega α', map_ofOmega _ _, h⟩

end Formula₀

/-- A sentence holds in the word model underlying a model over the track alphabet iff its
translation into MSO₀ holds in the model. -/
theorem Sentence.models_toFormula₀ {φ : Sentence A} {M : WordModel (Track A 0)} :
    Formula₀.Models (Formula.toFormula₀ φ) M ↔ φ.Holds M.base := by
  rw [Sentence.Holds, ← Formula.satisfies_toFormula₀ φ (fun x ↦ x.elim0), Formula₀.Models]
  rw [Subsingleton.elim M.tracks (Fin.append (α := Set ℕ) (fun x ↦ {Fin.elim0 x}) Fin.elim0)]

/-- A sentence defines the projection of the language defined by its translation into MSO₀. -/
theorem Sentence.language_eq_map {φ : Sentence A} :
    φ.language = (Formula.toFormula₀ φ).language.map Prod.fst := by
  ext w
  constructor
  · intro h
    refine ⟨w.map fun a ↦ (a, Fin.elim0), ?_, by simp [Function.comp_def]⟩
    refine Sentence.models_toFormula₀.mpr ?_
    simpa [base, Function.comp_def] using h
  · rintro ⟨w', h, rfl⟩
    have := Sentence.models_toFormula₀.mp h
    simpa [base] using this

/-- A sentence defines the projection of the ω-language defined by its translation into MSO₀. -/
theorem Sentence.ωlanguage_eq_map {φ : Sentence A} :
    φ.ωlanguage = (Formula.toFormula₀ φ).ωlanguage.map Prod.fst := by
  ext α
  constructor
  · intro h
    refine ⟨α.map fun a ↦ (a, Fin.elim0), ?_, rfl⟩
    exact Sentence.models_toFormula₀.mpr h
  · rintro ⟨α', h, rfl⟩
    exact Sentence.models_toFormula₀.mp h

end Cslib.Logic.MSO
