/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Submodule

/-!
# Completely reducible Lie-module data

Humphreys FC14-C02-U030.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v w

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable (M : Type w) [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

/-- Humphreys' completely-reducible-module predicate (FC14-C02-U030),
using the source-equivalent formulation that every Lie submodule has a
Lie-stable complement. -/
def IsCompletelyReducibleLieModuleData : Prop :=
  ∀ N : LieSubmodule R L M, ∃ P : LieSubmodule R L M, IsCompl N P

end LeanCategories.Algebra
