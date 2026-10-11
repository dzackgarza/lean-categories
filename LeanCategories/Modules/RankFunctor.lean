/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

@[expose] public section

/-!
# Rank as a functor

The rank of a module (Mathlib's `Module.rank`, the supremum of the cardinalities of linearly
independent subsets) is an isomorphism invariant (`LinearEquiv.rank_eq`), hence a functor
`rank : Core(Mod_R) ⥤ Disc(Card)`.
This cardinal invariant is defined over any ring. Interpreting it as the cardinality
of an arbitrary basis requires appropriate ring hypotheses, such as the strong rank
condition; no basis or free-module hypothesis is assumed by this functor.
-/

open CategoryTheory

namespace LeanCategories.Modules

universe u v

/-- The rank of `R`-modules, as a functor on the core of `Mod_R`. -/
noncomputable def rankFunctor (R : Type u) [Ring R] : Core (ModuleCat.{v} R) ⥤ Discrete Cardinal.{v} where
  obj M := ⟨Module.rank R M.of⟩
  map f := eqToHom (congrArg Discrete.mk (LinearEquiv.rank_eq f.iso.toLinearEquiv))

end LeanCategories.Modules
