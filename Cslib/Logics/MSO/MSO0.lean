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
`A × {0, 1}ⁿ`, the *track alphabet* `Track A n`. The `j`-th bit of the letter at a position tells
whether the position belongs to the `j`-th subset, so a formula of MSO₀ with `n` free variables
defines a language over `Track A n`. Under this view, existential set quantification is the
projection that forgets the last track, which is the key to the translation into automata.

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
  -- `x = y` becomes `{x} ⊆ {y}`.
  | _, _, .eq x y, _, ρ, _ => .sub (ρ x) (ρ y)
  -- `S(x, y)` becomes `Suc({x}, {y})`.
  | _, _, .succ x y, _, ρ, _ => .suc (ρ x) (ρ y)
  -- Placeholder: this case does not occur for formulas of MSO[S].
  | _, _, .lt x _, _, ρ, _ => .not (.sub (ρ x) (ρ x))
  -- `Q_a(x)` becomes `{x} ⊆ Q_a`.
  | _, _, .label a x, _, ρ, _ => .subLabel (ρ x) a
  -- `X(x)` becomes `{x} ⊆ X`.
  | _, _, .mem x X, _, ρ, τ => .sub (ρ x) (τ X)
  | _, _, .not φ, _, ρ, τ => .not (φ.toMSO₀ ρ τ)
  | _, _, .or φ ψ, _, ρ, τ => .or (φ.toMSO₀ ρ τ) (ψ.toMSO₀ ρ τ)
  -- `∃x φ` becomes `∃X (Sing(X) ∧ φ')`, where the singleton `X` takes the place of `x`.
  | _, _, .ex₁ φ, n, ρ, τ =>
    .ex (.and (.sing (Fin.last n)) (φ.toMSO₀
      (Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last n))
      (fun X ↦ (τ X).castSucc)))
  -- `∃X φ` stays a set quantifier; its variable is the last one of MSO₀.
  | _, _, .ex₂ φ, n, ρ, τ =>
    .ex (φ.toMSO₀ (fun x ↦ (ρ x).castSucc)
      (Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun X ↦ (τ X).castSucc) (Fin.last n)))

/-- The translation into MSO₀ is correct for formulas of MSO[S], when the variables of MSO₀
interpret first-order variables by singletons. -/
theorem satisfies_toMSO₀ {M : WordModel A} {φ : Formula A k l} (hφ : φ.LtFree)
    {ρ : Fin k → Fin n} {τ : Fin l → Fin n} {V : Fin n → Set ℕ} {v : Fin k → ℕ} {W : Fin l → Set ℕ}
    (hρ : ∀ x, V (ρ x) = {v x}) (hτ : ∀ X, V (τ X) = W X) :
    Formula₀.Satisfies M V (φ.toMSO₀ ρ τ) ↔ Satisfies M v W φ := by
  -- Induct on the formula, for all interpretations of the variables of MSO₀.
  induction φ generalizing n with
  -- `{x} ⊆ {y}` holds iff `x = y`.
  | eq x y =>
    -- Interpret the singletons and evaluate the subset relation.
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.singleton_subset_iff,
      -- A singleton is contained in another one iff their elements are equal.
      Set.mem_singleton_iff]
  -- `Suc({x}, {y})` holds iff `y` is the successor of `x`.
  | succ x y =>
    -- Interpret the singletons: `{x} = {p}` holds iff `x = p`.
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.singleton_eq_singleton_iff]
    -- Show both directions.
    constructor
    -- The witness `p` is `v x` itself.
    · rintro ⟨p, rfl, h⟩
      -- What remains is the claim.
      exact h
    -- Conversely, take `v x` as the witness.
    · exact fun h ↦ ⟨v x, rfl, h⟩
  -- `x < y` does not occur in a formula of MSO[S].
  | lt x y => exact hφ.elim
  -- `{x} ⊆ Q_a` holds iff `x` carries the letter `a`.
  | label a x =>
    -- The only position of `{x}` is `x`.
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, Set.mem_singleton_iff, forall_eq]
  -- `{x} ⊆ X` holds iff `x ∈ X`.
  | mem x X =>
    -- Interpret the variables and evaluate the subset relation.
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies, hρ, hτ, Set.singleton_subset_iff]
  -- Negation: apply the induction hypothesis.
  | not φ ih => exact not_congr (ih hφ hρ hτ)
  -- Disjunction: apply the induction hypotheses.
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hφ.1 hρ hτ) (ihψ hφ.2 hρ hτ)
  -- First-order quantifier: the new set variable of MSO₀ has to be a singleton.
  | @ex₁ k l φ ih =>
    -- For each position `p`, the induction hypothesis relates the extended interpretations.
    have key {p : ℕ} := ih (n := n + 1) hφ
      -- The new first-order variable is the new variable of MSO₀.
      (ρ := Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun x ↦ (ρ x).castSucc) (Fin.last n))
      -- The second-order variables keep their variables of MSO₀.
      (τ := fun X ↦ (τ X).castSucc)
      -- The new variable of MSO₀ is interpreted by `{p}`.
      (V := Fin.snoc (α := fun _ ↦ Set ℕ) V {p})
      -- The new first-order variable is interpreted by `p`.
      (v := Fin.snoc (α := fun _ ↦ ℕ) v p) (W := W)
      -- The new variable is interpreted by `{p}`, the old ones as before.
      (fun x ↦ by
        -- Distinguish the new first-order variable from the old ones.
        induction x using Fin.lastCases with
        -- The new variable is interpreted by `{p}` on both sides.
        | last => simp
        -- The old variables are interpreted as before by `hρ`.
        | cast x => simpa using hρ x)
      -- The second-order variables are interpreted as before by `hτ`.
      (fun X ↦ by simpa using hτ X)
    -- Unfold the translation and the semantics of both quantifiers.
    simp only [toMSO₀, Formula₀.Satisfies, Fin.snoc_last, Satisfies]
    -- Show both directions.
    constructor
    -- A singleton `{p}` in the domain gives the position `p`,
    · rintro ⟨P, hP, ⟨p, rfl⟩, h⟩
      -- which satisfies the formula by the induction hypothesis.
      exact ⟨p, hP rfl, key.mp h⟩
    -- Conversely, a position `p` of the domain gives the singleton `{p}`,
    · rintro ⟨p, hp, h⟩
      -- which satisfies the translated formula by the induction hypothesis.
      exact ⟨{p}, Set.singleton_subset_iff.mpr hp, ⟨p, rfl⟩, key.mpr h⟩
  -- Second-order quantifier: the same set interprets the new variable on both sides.
  | @ex₂ k l φ ih =>
    -- Unfold the translation and the semantics of both quantifiers.
    simp only [toMSO₀, Formula₀.Satisfies, Satisfies]
    -- Both sides quantify over the same sets `P`; apply the induction hypothesis to each of them.
    refine exists_congr fun P ↦ and_congr_right fun _ ↦ ih hφ (fun x ↦ ?_) (fun X ↦ ?_)
    -- The first-order variables are interpreted as before by `hρ`.
    · simpa using hρ x
    -- Distinguish the new second-order variable from the old ones.
    · induction X using Fin.lastCases with
      -- The new variable is interpreted by `P` on both sides.
      | last => simp
      -- The old variables are interpreted as before by `hτ`.
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
  -- Compose the correctness of the translation and of the elimination of the order relation.
  rw [toFormula₀, satisfies_toMSO₀ (ltFree_elimLt φ) (v := v) (W := W), satisfies_elimLt φ hv]
  -- The first-order variables are the left part of the appended interpretation.
  · exact fun x ↦ Fin.append_left _ _ x
  -- The second-order variables are the right part of the appended interpretation.
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

/-- The labels of the underlying word model are the first components of the letters. -/
@[simp]
theorem base_label (M : WordModel (Track A n)) (i : ℕ) :
    M.base.label i = (M.label i).map Prod.fst :=
  -- Holds by definition of `base`.
  rfl

/-- The underlying word model has the same domain. -/
@[simp]
theorem dom_base (M : WordModel (Track A n)) : M.base.dom = M.dom :=
  -- `base` is a relabelling, which preserves the domain.
  dom_map _ _

/-- A position belongs to a track iff its letter has the corresponding bit set. -/
theorem mem_tracks {M : WordModel (Track A n)} {j : Fin n} {i : ℕ} :
    i ∈ M.tracks j ↔ ∃ x, M.label i = some x ∧ x.2 j = true :=
  -- Holds by definition of `tracks`.
  Iff.rfl

/-- The designated sets are subsets of the domain. -/
theorem tracks_subset_dom (M : WordModel (Track A n)) (j : Fin n) : M.tracks j ⊆ M.dom := by
  -- A position of a track carries a letter `x`.
  rintro i ⟨x, hx, -⟩
  -- So it has a label and belongs to the domain.
  simp [mem_dom, hx]

/-- Forgetting the last track does not change the underlying word model. -/
@[simp]
theorem base_map_trackInit (M : WordModel (Track A (n + 1))) : (M.map trackInit).base = M.base := by
  -- Word models are equal iff their label functions are equal.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- Combine the two relabellings.
  simp only [base_label, map_label, Option.map_map]
  -- `trackInit` keeps the first component of a letter.
  rfl

/-- The designated sets of a model over the track alphabet are the ones of its projection together
with the last one. -/
theorem tracks_eq_snoc (M : WordModel (Track A (n + 1))) :
    M.tracks = Fin.snoc (α := fun _ ↦ Set ℕ) (M.map trackInit).tracks (M.tracks (Fin.last n)) := by
  -- Compare the sets for an arbitrary variable `j`.
  funext j
  -- Distinguish the last variable from the others.
  induction j using Fin.lastCases with
  -- The last track is the new component of the right-hand side.
  | last => simp
  -- Another track is kept by `trackInit`.
  | cast j =>
    -- Compare both sets position by position.
    ext i
    -- `trackInit` does not change the bits of the remaining tracks.
    simp [mem_tracks, trackInit]

open Classical in
/-- Add the set `P` as a further designated set to a model over the track alphabet. -/
noncomputable def extend (M : WordModel (Track A n)) (P : Set ℕ) : WordModel (Track A (n + 1)) where
  label i := (M.label i).map fun x ↦ (x.1, Fin.snoc (α := fun _ ↦ Bool) x.2 (decide (i ∈ P)))
  isSome_of_le hij hj := by
    -- Adding a bit does not change whether a position carries a label.
    simp only [Option.isSome_map] at hj ⊢
    -- So the initial-segment property is inherited from `M`.
    exact M.isSome_of_le hij hj

/-- Forgetting the added track gives the original model back. -/
@[simp]
theorem map_trackInit_extend (M : WordModel (Track A n)) (P : Set ℕ) :
    (M.extend P).map trackInit = M := by
  -- Word models are equal iff their label functions are equal.
  ext1
  -- Compare the labels at an arbitrary position `i`.
  funext i
  -- With a label, only the added bit is forgotten; without a label, both sides are `none`.
  cases h : M.label i <;> simp [extend, trackInit, h]

/-- The designated sets of the extension are the original ones together with `P`. -/
@[simp]
theorem tracks_extend {M : WordModel (Track A n)} {P : Set ℕ} (hP : P ⊆ M.dom) :
    (M.extend P).tracks = Fin.snoc (α := fun _ ↦ Set ℕ) M.tracks P := by
  -- Compare the sets for an arbitrary variable `j`.
  funext j
  -- Distinguish the new track from the others.
  induction j using Fin.lastCases with
  -- The new track is `P`.
  | last =>
    -- Compare both sets position by position.
    ext i
    -- Unfold the tracks of the extension.
    simp only [mem_tracks, extend, Option.map_eq_some_iff, Fin.snoc_last]
    -- Show both directions.
    constructor
    -- Assume that the added bit of a letter is set at `i`.
    · rintro ⟨_, ⟨x, -, rfl⟩, h⟩
      -- Then `i ∈ P`, as this bit is `decide (i ∈ P)`.
      simpa using h
    -- Conversely, let `i ∈ P`.
    · intro hi
      -- As `P` is a subset of the domain, `M` has a label at `i`.
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hP hi)
      -- So the extension has a label at `i` with the added bit set.
      exact ⟨_, ⟨x, hx, rfl⟩, by simpa using hi⟩
  -- Another track is kept by the extension.
  | cast j =>
    -- Compare both sets position by position.
    ext i
    -- Unfold the tracks of the extension.
    simp only [mem_tracks, extend, Option.map_eq_some_iff, Fin.snoc_castSucc]
    -- Show both directions.
    constructor
    -- A letter of the extension comes from a letter `x` of `M`,
    · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
      -- whose bit for `j` is unchanged.
      exact ⟨x, hx, by simpa using h⟩
    -- Conversely, take the letter `x` of `M` with its bit for `j` set.
    · rintro ⟨x, hx, h⟩
      -- Extending this letter does not change the bit.
      exact ⟨_, ⟨x, hx, rfl⟩, by simpa using h⟩

/-- Adding a track does not change the underlying word model. -/
@[simp]
theorem base_extend (M : WordModel (Track A n)) (P : Set ℕ) : (M.extend P).base = M.base := by
  -- Forgetting the added track preserves the underlying model and gives `M` back.
  rw [← base_map_trackInit (M.extend P), map_trackInit_extend]

/-- The empty word has empty tracks. -/
@[simp]
theorem notMem_tracks_ofList_nil {j : Fin n} {i : ℕ} :
    i ∉ (ofList ([] : List (Track A n))).tracks j := by
  -- The empty list has no letters.
  simp [mem_tracks]

/-- The first position of `x :: w` belongs to a track iff the bit of `x` is set. -/
@[simp]
theorem zero_mem_tracks_ofList_cons {x : Track A n} {w : List (Track A n)} {j : Fin n} :
    0 ∈ (ofList (x :: w)).tracks j ↔ x.2 j = true := by
  -- The letter at position `0` is `x`.
  simp [mem_tracks]

/-- A later position of `x :: w` belongs to a track iff the shifted position belongs to the track of
`w`. -/
@[simp]
theorem succ_mem_tracks_ofList_cons {x : Track A n} {w : List (Track A n)} {j : Fin n} {i : ℕ} :
    i + 1 ∈ (ofList (x :: w)).tracks j ↔ i ∈ (ofList w).tracks j := by
  -- The letter at position `i + 1` of `x :: w` is the letter at position `i` of `w`.
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

/-- A word belongs to the language of a formula iff the formula holds in its model. -/
@[simp]
theorem mem_language {φ : Formula₀ A n} {w : List (Track A n)} :
    w ∈ φ.language ↔ φ.Models (ofList w) :=
  -- Holds by definition of `language`.
  Iff.rfl

/-- An ω-word belongs to the ω-language of a formula iff the formula holds in its model. -/
@[simp]
theorem mem_ωlanguage {φ : Formula₀ A n} {α : ωSequence (Track A n)} :
    α ∈ φ.ωlanguage ↔ φ.Models (ofOmega α) :=
  -- Holds by definition of `ωlanguage`.
  Iff.rfl

/-- Existential set quantification: `∃X φ` holds in a model iff `φ` holds in some extension of the
model by a further designated set. -/
theorem models_ex_iff {φ : Formula₀ A (n + 1)} {M : WordModel (Track A n)} :
    (ex φ).Models M ↔ ∃ M' : WordModel (Track A (n + 1)), M'.map trackInit = M ∧ φ.Models M' := by
  -- Show both directions.
  constructor
  -- Take a set `P` that witnesses the quantifier.
  · rintro ⟨P, hP, h⟩
    -- The domain of the underlying model is the domain of `M`.
    rw [dom_base] at hP
    -- Extend `M` by `P`; this extension projects to `M`.
    refine ⟨M.extend P, map_trackInit_extend M P, ?_⟩
    -- The extension has the same underlying model and the additional track `P`.
    rwa [Models, base_extend, tracks_extend hP]
  -- Conversely, take a model `M'` that projects to `M`.
  · rintro ⟨M', rfl, h⟩
    -- The last track of `M'` witnesses the quantifier.
    refine ⟨M'.tracks (Fin.last n), ?_, ?_⟩
    -- The domain of `M` is the domain of `M'`.
    · rw [dom_base, dom_map]
      -- Tracks are subsets of the domain.
      exact tracks_subset_dom M' _
    -- The tracks of `M'` are the ones of `M` with the last track added.
    · rwa [base_map_trackInit, ← tracks_eq_snoc]

/-- Existential set quantification corresponds to the projection of the language. -/
theorem language_ex {φ : Formula₀ A (n + 1)} : (ex φ).language = φ.language.map trackInit := by
  -- Compare the languages on a word `w`.
  ext w
  -- Apply the characterization of the quantifier in terms of models.
  rw [mem_language, models_ex_iff]
  -- Show both directions.
  constructor
  -- Take a model `M'` that projects to the model of `w`.
  · rintro ⟨M', hM', h⟩
    -- `M'` is the model of a word `w'` of the same length as `w`,
    obtain ⟨w', -, rfl⟩ :=
      -- as its domain is the domain of the model of `w`.
      M'.exists_eq_ofList w.length fun i ↦ by simp [← dom_map trackInit M', hM']
    -- Relabelling the model of `w'` gives the model of the mapped word.
    rw [map_ofList] at hM'
    -- So `w'` projects to `w` by the injectivity of `ofList`.
    exact ⟨w', h, ofList_injective hM'⟩
  -- Conversely, take a word `w'` in the language that projects to `w`.
  · rintro ⟨w', h, rfl⟩
    -- Its model is the required extension.
    exact ⟨ofList w', map_ofList _ _, h⟩

/-- Existential set quantification corresponds to the projection of the ω-language. -/
theorem ωlanguage_ex {φ : Formula₀ A (n + 1)} : (ex φ).ωlanguage = φ.ωlanguage.map trackInit := by
  -- Compare the ω-languages on an ω-word `α`.
  ext α
  -- Unfold the membership in the ω-language.
  change (ex φ).Models (ofOmega α) ↔ _
  -- Apply the characterization of the quantifier in terms of models.
  rw [models_ex_iff]
  -- Show both directions.
  constructor
  -- Take a model `M'` that projects to the model of `α`.
  · rintro ⟨M', hM', h⟩
    -- `M'` has full domain, so it is the model of an ω-word `α'`.
    obtain ⟨α', rfl⟩ := M'.exists_eq_ofOmega fun i ↦ by simp [← dom_map trackInit M', hM']
    -- Relabelling the model of `α'` gives the model of the mapped ω-word.
    rw [map_ofOmega] at hM'
    -- So `α'` projects to `α` by the injectivity of `ofOmega`.
    exact ⟨α', h, ofOmega_injective hM'⟩
  -- Conversely, take an ω-word `α'` in the ω-language that projects to `α`.
  · rintro ⟨α', h, rfl⟩
    -- Its model is the required extension.
    exact ⟨ofOmega α', map_ofOmega _ _, h⟩

end Formula₀

/-- A sentence holds in the word model underlying a model over the track alphabet iff its
translation into MSO₀ holds in the model. -/
theorem Sentence.models_toFormula₀ {φ : Sentence A} {M : WordModel (Track A 0)} :
    Formula₀.Models (Formula.toFormula₀ φ) M ↔ φ.Holds M.base := by
  -- Translate the truth of the sentence into MSO₀; no free variables need to be in the domain.
  rw [Sentence.Holds, ← Formula.satisfies_toFormula₀ φ (fun x ↦ x.elim0), Formula₀.Models]
  -- There are no variables, so all interpretations of them are equal.
  rw [Subsingleton.elim M.tracks (Fin.append (α := Set ℕ) (fun x ↦ {Fin.elim0 x}) Fin.elim0)]

/-- A sentence defines the projection of the language defined by its translation into MSO₀. -/
theorem Sentence.language_eq_map {φ : Sentence A} :
    φ.language = (Formula.toFormula₀ φ).language.map Prod.fst := by
  -- Compare the languages on a word `w`.
  ext w
  -- Show both directions.
  constructor
  -- Let `w` be in the language of the sentence.
  · intro h
    -- Take `w` with empty tracks, which projects to `w`.
    refine ⟨w.map fun a ↦ (a, Fin.elim0), ?_, by simp [Function.comp_def]⟩
    -- By the correctness of the translation, it suffices to consider the underlying word.
    refine Sentence.models_toFormula₀.mpr ?_
    -- The underlying word of `w` with empty tracks is `w`.
    simpa [base, Function.comp_def] using h
  -- Conversely, take a word `w'` over the track alphabet that satisfies the translation.
  · rintro ⟨w', h, rfl⟩
    -- So the sentence holds in the underlying model of `w'`.
    have := Sentence.models_toFormula₀.mp h
    -- The underlying model is the model of the projected word.
    simpa [base] using this

/-- A sentence defines the projection of the ω-language defined by its translation into MSO₀. -/
theorem Sentence.ωlanguage_eq_map {φ : Sentence A} :
    φ.ωlanguage = (Formula.toFormula₀ φ).ωlanguage.map Prod.fst := by
  -- Compare the ω-languages on an ω-word `α`.
  ext α
  -- Show both directions.
  constructor
  -- Let `α` be in the ω-language of the sentence.
  · intro h
    -- Take `α` with empty tracks, which projects to `α`.
    refine ⟨α.map fun a ↦ (a, Fin.elim0), ?_, rfl⟩
    -- By the correctness of the translation, it suffices to consider the underlying ω-word.
    exact Sentence.models_toFormula₀.mpr h
  -- Conversely, take an ω-word `α'` over the track alphabet that satisfies the translation.
  · rintro ⟨α', h, rfl⟩
    -- So the sentence holds in the underlying model of `α'`, which is the projected ω-word.
    exact Sentence.models_toFormula₀.mp h

end Cslib.Logic.MSO
