/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.UnipotentSubgroupData
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.Basic

/-! # E-group data

Definition-level realization of Humphreys FC16-C07-U034.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u v

variable {K : Type u} [Field K]
variable {G : Type v} [Group G]

/-- In characteristic `p > 0`, an e-group is commutative, unipotent, and
has exponent `p`.  The intrinsic unipotent-element predicate is supplied by
the preceding Jordan-decomposition layer. -/
def IsEGroup (p : ℕ) [CharP K p]
    (isUnipotentElement : G → Prop) : Prop :=
  0 < p ∧
    (∀ x y : G, x * y = y * x) ∧
    IsUnipotentSubgroup isUnipotentElement (⊤ : Subgroup G) ∧
    ∀ x : G, x ^ p = 1

end LeanCategories.AlgebraicGeometry
