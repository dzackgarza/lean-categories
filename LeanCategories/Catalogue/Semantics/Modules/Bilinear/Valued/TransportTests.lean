/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Transport
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ConstructionTests

@[expose] public section

open CategoryTheory TensorProduct
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.Constructions
open CasCatalogue.Modules.Bilinear.Valued.ConstructionTests

namespace CasCatalogue.Modules.Bilinear.Valued.TransportTests

/-- The prescribed value map is nonidentity and retains both coordinates. -/
def doubleValues : ConstructionTests.values ⟶ pairedValues :=
  ModuleCat.ofHom (LinearMap.prod LinearMap.id (2 • LinearMap.id))

def changed : BilWFormCat integers :=
  Transport.changeValues integers (formed integers vectors ConstructionTests.values hyperbolic)
    pairedValues doubleValues

example : pairing integers changed (![2, -1], ![3, 4]) = ((5, 10) : ℤ × ℤ) := by
  change ((2 * 4 + (-1) * 3, 2 * (2 * 4 + (-1) * 3)) : ℤ × ℤ) = (5, 10)
  norm_num

example : (BilWFormCat.valueMap
    (Transport.toChangedValues integers
      (formed integers vectors ConstructionTests.values hyperbolic)
      pairedValues doubleValues)).hom (7 : ℤ) = ((7, 14) : ℤ × ℤ) := by
  change ((7, 2 * 7) : ℤ × ℤ) = (7, 14)
  norm_num

abbrev rationals : CommRingCat := CommRingCat.of ℚ
def integerToRational : integers ⟶ rationals := CommRingCat.ofHom (Int.castRingHom ℚ)

noncomputable def rationalForm : BilWFormCat rationals :=
  Transport.extendScalars integers rationals integerToRational
    (formed integers vectors ConstructionTests.values hyperbolic)

/-- Scalar extension retains the tensor-valued pairing and both prescribed scalars. -/
example : pairing rationals rationalForm
    ((2 : ℚ) ⊗ₜ[ℤ] (![2, -1] : Fin 2 → ℤ),
     (3 : ℚ) ⊗ₜ[ℤ] (![3, 4] : Fin 2 → ℤ)) = (6 : ℚ) ⊗ₜ[ℤ] (5 : ℤ) := by
  change ((2 * 3 : ℚ) ⊗ₜ[ℤ] (2 * 4 + (-1) * 3 : ℤ)) =
    (6 : ℚ) ⊗ₜ[ℤ] (5 : ℤ)
  norm_num

end CasCatalogue.Modules.Bilinear.Valued.TransportTests
