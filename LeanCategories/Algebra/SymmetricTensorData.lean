/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Homogeneous symmetric tensor data

Humphreys FC14-C05-U004. We record the permutation-fixed tensor submodule
and the characteristic-zero averaging operator. The canonical comparison with
`SymmetricPower` and the graded copy of `SymmetricAlgebra` are result content.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) (V : Type v)
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- The order-`m` tensors fixed by every permutation of tensor factors. -/
def homogeneousSymmetricTensors (m : ℕ) :
    Submodule R (⨂[R] (_ : Fin m), V) :=
  ⨅ sigma : Equiv.Perm (Fin m),
    LinearMap.ker <|
      (PiTensorProduct.reindex R (fun _ : Fin m => V) sigma).toLinearMap - LinearMap.id

/-- The symmetrization operator obtained by averaging all factor permutations. -/
def tensorSymmetrizer (K : Type u) (W : Type v)
    [Field K] [CharZero K] [AddCommGroup W] [Module K W] (m : ℕ) :
    Module.End K (⨂[K] (_ : Fin m), W) :=
  ((Nat.factorial m : K)⁻¹) •
    ∑ sigma : Equiv.Perm (Fin m),
      (PiTensorProduct.reindex K (fun _ : Fin m => W) sigma).toLinearMap

end LeanCategories.Algebra
