/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Humphreys' integral weight group ring `Z[Lambda]` (FC14-C06-U032). -/
abbrev integralWeightGroupRing (Lambda : Type*) [AddCommGroup Lambda] :=
  AddMonoidAlgebra ℤ Lambda

/-- The basis element `e(lambda)` of the integral weight group ring. -/
def weightBasisElement {Lambda : Type*} [AddCommGroup Lambda] (lambda : Lambda) :
    integralWeightGroupRing Lambda :=
  AddMonoidAlgebra.single lambda 1

/-- Relabel weight exponents along an additive lattice equivalence.
This is the source Weyl-action formula before any invariance theorem. -/
def weightGroupRingAction {Lambda : Type*} [AddCommGroup Lambda]
    (w : Lambda ≃+ Lambda) (x : integralWeightGroupRing Lambda) :
    integralWeightGroupRing Lambda :=
  AddMonoidAlgebra.mapDomain w x

end LeanCategories.Algebra
