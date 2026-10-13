/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Profinite-integer data

Definition-level realization of Serre FC10-C11-U033.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Serre's profinite completion `Z-hat` (FC10-C11-U033), represented by the
native profinite completion of the additive group `ℤ` through its standard
multiplicative wrapper.

The identification with the product of the `p`-adic integer groups is a
comparison theorem and is not bundled into this Sweep-III declaration. -/
def serreProfiniteIntegerData : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

end LeanCategories.Algebra
