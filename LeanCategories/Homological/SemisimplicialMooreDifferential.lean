/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Moore differential of a semisimplicial object

Definition-level realization of Kerodon FC17-KER-U00827 (tag 00QA).

For a semisimplicial object in a preadditive category, Kerodon's Moore
differential is the alternating sum of the face maps.  This file records the
semisimplicial carrier, its face operators, the degree objects, and that
differential.

The identity `d ≫ d = 0` is a theorem obtained by cancelling pairs of face
maps.  Consequently the `ChainComplex` packaging depends on result/proof work
and is deliberately left to Sweep IV.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological.SemisimplicialMoore

open CategoryTheory Opposite Simplicial

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A semisimplicial object in `C`, using Mathlib's semi-simplex category. -/
abbrev SemisimplicialObject (C : Type u) [Category.{v} C] :=
  SemiSimplexCategoryᵒᵖ ⥤ C

variable (X : SemisimplicialObject C)

/-- The `i`th face map of a semisimplicial object. -/
def face {n : ℕ} (i : Fin (n + 2)) :
    X.obj (op ⦋n + 1⦌ₛ) ⟶ X.obj (op ⦋n⦌ₛ) :=
  X.map (SemiSimplexCategory.homEquiv.symm (Fin.succAboveOrderEmb i)).op

/-- The object in degree `n` of Kerodon's Moore construction. -/
abbrev degree (n : ℕ) : C := X.obj (op ⦋n⦌ₛ)

/-- The Moore differential, the alternating sum of the face maps. -/
def differential (n : ℕ) : degree X (n + 1) ⟶ degree X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • face X i

end LeanCategories.Homological.SemisimplicialMoore
