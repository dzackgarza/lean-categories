/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildComplex

/-!
# The cyclic operator on Hochschild chains

Weibel, *An Introduction to Homological Algebra* (1994), §9.6, pp. 330--337
(FC05-C09-U081).

For `ZR_n = R^{⊗(n+1)}`, the cyclic operator rotates the last tensor factor to
the front.  This file records the operator formula on pure tensors.  Its order
and compatibility with the simplicial operators are theorem-layer assertions.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial
open scoped TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]

/-- Pure-tensor rotation data for the cyclic Hochschild operator. -/
def hochschildCyclicData {n : ℕ} (r₀ : R) (a : Fin n → R) :
    R × (Fin n → R) := by
  cases n with
  | zero => exact (r₀, a)
  | succ n =>
      exact (a (Fin.last n), Fin.cons r₀ (fun j : Fin n => a j.castSucc))

/-- A cyclic-operator realization on the standard Hochschild simplicial module `ZR`. -/
structure HochschildCyclicOperator
    (S : HochschildSimplicialRealization k R R) where
  /-- The degreewise automorphism `t_n`. -/
  operator : ∀ n : ℕ, S.obj.obj (op ⦋n⦌) ≅ S.obj.obj (op ⦋n⦌)
  /-- On pure tensors, `t(r₀⊗⋯⊗rₙ)=rₙ⊗r₀⊗⋯⊗rₙ₋₁`. -/
  operator_pure : ∀ (n : ℕ) (r₀ : R) (a : Fin n → R),
    (S.degreeIso n).hom
        ((operator n).hom ((S.degreeIso n).inv
          (hochschildChainPure (k := k) (R := R) (M := R) r₀ a))) =
      hochschildChainPure (k := k) (R := R) (M := R)
        (hochschildCyclicData R r₀ a).1 (hochschildCyclicData R r₀ a).2

end LeanCategories.Homological
