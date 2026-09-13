/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.EulerianIdempotents
public import LeanCategories.Homological.HochschildComplex
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Hodge summands of the Hochschild complex

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.4.15,
§9.4, pp. 319--325 (FC05-C09-U072).

For a commutative `ℚ`-algebra `R`, the `i`th degree-`n` Hodge summand is the
image of the Eulerian idempotent `e_n^(i)` on the standard Hochschild chain
module `R ⊗_ℚ R^{⊗ n}`.  Corollary 9.4.14 proves that the Hochschild
differential preserves these images.  That preservation result is theorem
work, so this file records the degreewise source definition and packages a
chain-complex realization when the compatibility has been supplied.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]

/-- The action of Weibel's Eulerian idempotent `e_n^(i)` on the tensor-power
factor `R^{⊗ n}`. -/
noncomputable def eulerianTensorPowerEndomorphism (n i : ℕ) :
    TensorPower ℚ n R →ₗ[ℚ] TensorPower ℚ n R :=
  (MonoidAlgebra.coeff (eulerianIdempotent n i)).sum fun σ a =>
    a • (PiTensorProduct.reindex ℚ (fun _ : Fin n => R) σ).toLinearMap

/-- The Eulerian projector on Hochschild chains, acting trivially on the
leading coefficient factor and by `e_n^(i)` on `R^{⊗ n}`. -/
noncomputable def hochschildHodgeProjector (n i : ℕ) :
    HochschildChainDegree (k := ℚ) (R := R) (M := R) n →ₗ[ℚ]
      HochschildChainDegree (k := ℚ) (R := R) (M := R) n :=
  TensorProduct.map LinearMap.id (eulerianTensorPowerEndomorphism R n i)

/-- Weibel's degree-`n`, `i`th Hodge piece
`C_n^h(R)^(i) = e_n^(i)(R ⊗ R^{⊗ n})`. -/
noncomputable def hochschildHodgeDegree (n i : ℕ) :
    Submodule ℚ (HochschildChainDegree (k := ℚ) (R := R) (M := R) n) :=
  LinearMap.range (hochschildHodgeProjector R n i)

/-- A chain-complex realization of the degreewise Hodge pieces.  Existence is
the content of the differential-compatibility result preceding Definition
9.4.15; it is not asserted in the Definitions sweep. -/
structure HochschildHodgeSubcomplexRealization (i : ℕ) where
  /-- The realized `i`th Hodge subcomplex. -/
  complex : ChainComplex (ModuleCat ℚ) ℕ
  /-- Its degree-`n` object is the image of `e_n^(i)`. -/
  degreeIso : ∀ n : ℕ,
    complex.X n ≅ ModuleCat.of ℚ ↥(hochschildHodgeDegree R n i)

/-- The homology of a realized Hodge subcomplex. -/
noncomputable def hochschildHodgeHomology
    {i : ℕ} (H : HochschildHodgeSubcomplexRealization R i) (n : ℕ) : ModuleCat ℚ :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).obj H.complex

end LeanCategories.Homological
