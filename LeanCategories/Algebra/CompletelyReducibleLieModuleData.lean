/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs

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

/-- Humphreys' definition of a completely reducible Lie module (FC14-C02-U030):
the module is an internal direct sum of irreducible Lie submodules. -/
def IsCompletelyReducibleLieModuleData : Prop :=
  ∃ (ι : Type) (N : ι → LieSubmodule R L M),
    (∀ i, LieModule.IsIrreducible R L (N i)) ∧ DirectSum.IsInternal N

end LeanCategories.Algebra
