/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Sl2

/-!
# Weight-space data for sl₂ modules

Humphreys FC14-C02-U044. This file records the eigenspace carrier `V_lambda`
and the source predicate that `lambda` is a weight exactly when this space is
nonzero. Raising/lowering statements are result content.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

variable (R : Type u) (L : Type v) (V : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
variable {h e f : L}

/-- The `lambda`-weight space for the distinguished `h` in an `sl₂` triple. -/
def sl2WeightSpace (_t : IsSl2Triple h e f) (lambda : R) : Submodule R V :=
  (LieModule.toEnd R L V h).eigenspace lambda

/-- Humphreys' weight predicate: `lambda` is a weight exactly when its
`h`-eigenspace is nonzero. -/
def IsSl2Weight (t : IsSl2Triple h e f) (lambda : R) : Prop :=
  sl2WeightSpace R L V t lambda ≠ ⊥

end LeanCategories.Algebra
