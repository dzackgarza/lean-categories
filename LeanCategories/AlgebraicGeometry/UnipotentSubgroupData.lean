/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Unipotent subgroup data

Definition-level realization of Humphreys FC16-C07-U011.

Humphreys defines an algebraic subgroup to be unipotent when every one of
its elements is unipotent in the intrinsic Jordan-decomposition sense of
FC16-C06-U008.  Sweep III does not construct that theorem-level intrinsic
Jordan decomposition; instead the already named element predicate is kept
as an explicit input.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u

variable {G : Type u} [Group G]

/-- A subgroup is unipotent when every one of its elements satisfies the
ambient unipotent-element predicate.

For FC16-C07-U011, `isUnipotentElement` is the intrinsic predicate supplied
by the Jordan-decomposition layer FC16-C06-U008. -/
def IsUnipotentSubgroup
    (isUnipotentElement : G → Prop) (U : Subgroup G) : Prop :=
  ∀ u : U, isUnipotentElement u.1

end LeanCategories.AlgebraicGeometry
