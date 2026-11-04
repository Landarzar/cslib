/-
Copyright (c) 2026 Robin Proeckl, Kai Sauerwald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Proeckl, Kai Sauerwald
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Defs

/-! # Answer Set Programming

Syntax and classical semantics of propositional normal logic programs over an arbitrary type of
atoms, the fragment of Answer Set Programming (ASP) studied in [GelfondLifschitz1988].

## Main definitions

- `ASP.Rule`: normal rules `head ← body⁺, not body⁻`.
- `ASP.Program`: sets of rules, not required to be finite.
- `ASP.SatisfiesRule`, `ASP.IsClassicalModel`: classical satisfaction of rules and programs.

## Implementation notes

Rule bodies are lists rather than sets. A rule is a piece of syntax, its semantics only depends on
membership in the bodies, and lists make the translation into propositional logic computable (see
`ASP.Rule.toProposition`).

## References

* [M. Gelfond, V. Lifschitz, *The Stable Model Semantics for Logic Programming*]
  [GelfondLifschitz1988]
-/

@[expose] public section

universe u

namespace Cslib.ASP

variable {Atom : Type u}

/-- A normal rule `head ← body⁺, not body⁻`, without disjunction or strong negation. -/
structure Rule (Atom : Type u) where
  /-- The atom derived by the rule. -/
  head : Atom
  /-- The atoms that have to hold. -/
  bodyPos : List Atom
  /-- The atoms that must not hold. -/
  bodyNeg : List Atom
  deriving DecidableEq

/-- A program is a set of rules, not required to be finite. -/
abbrev Program (Atom : Type u) := Set (Rule Atom)

/-- A set of atoms satisfies a rule if the head holds whenever both bodies do. -/
def SatisfiesRule (I : Set Atom) (r : Rule Atom) : Prop :=
  (∀ a ∈ r.bodyPos, a ∈ I) → (∀ a ∈ r.bodyNeg, a ∉ I) → r.head ∈ I

/-- A set of atoms is a classical model of a program if it satisfies every rule. -/
def IsClassicalModel (I : Set Atom) (P : Program Atom) : Prop := ∀ r ∈ P, SatisfiesRule I r

end Cslib.ASP
