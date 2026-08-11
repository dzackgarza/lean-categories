/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Standard
public import SpherePacking.Basic.E8
public meta import Mathlib.Data.Matrix.Basic
public meta import SpherePacking.Basic.E8

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The positive `E₈` lattice on the carrier from Sphere-Packing-Lean. -/
noncomputable def spherePackingE8Lattice : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap
    (Matrix.toBilin E8_ℤBasis E8.inn), ?_, ?_⟩
  · exact Module.Projective.of_basis E8_ℤBasis
  · exact ((Matrix.isSymm_toBilin_iff_isSymm
      (b := E8_ℤBasis)).mpr (by decide)).eq

/-- The external basis has the external positive `E₈` Gram matrix. -/
theorem spherePackingE8Lattice_gramMatrix :
    gramMatrix spherePackingE8Lattice E8_ℤBasis = E8.inn := by
  exact LinearMap.BilinForm.toMatrix_toBilin E8_ℤBasis E8.inn

/-- The change from the external basis to the selected simple-root basis. -/
def e8SphereBasisChange : Matrix (Fin 8) (Fin 8) ℤ := ![
  ![-3, -6, -5, -4, -3, -2, -1, 1],
  ![ 1,  1,  0,  0,  0,  0,  0, 0],
  ![ 0,  1,  0,  0,  0,  0,  0, 0],
  ![ 0,  0,  1,  0,  0,  0,  0, 0],
  ![ 0,  0,  0,  1,  0,  0,  0, 0],
  ![ 0,  0,  0,  0,  1,  0,  0, 0],
  ![ 0,  0,  0,  0,  0,  1,  0, 0],
  ![ 0,  0,  0,  0,  0,  0,  1, 0]]

/-- The inverse change from the selected basis to the external basis. -/
def e8SphereBasisChangeInverse : Matrix (Fin 8) (Fin 8) ℤ := ![
  ![0, 1, -1, 0, 0, 0, 0, 0],
  ![0, 0,  1, 0, 0, 0, 0, 0],
  ![0, 0,  0, 1, 0, 0, 0, 0],
  ![0, 0,  0, 0, 1, 0, 0, 0],
  ![0, 0,  0, 0, 0, 1, 0, 0],
  ![0, 0,  0, 0, 0, 0, 1, 0],
  ![0, 0,  0, 0, 0, 0, 0, 1],
  ![1, 3,  3, 5, 4, 3, 2, 1]]

theorem e8SphereBasisChange_mul_inverse :
    e8SphereBasisChange * e8SphereBasisChangeInverse = 1 := by
  decide +kernel

theorem e8SphereBasisChange_inverse_mul :
    e8SphereBasisChangeInverse * e8SphereBasisChange = 1 := by
  decide +kernel

/-- The basis change carries the external positive form to the project form. -/
theorem e8SphereBasisChange_gram :
    e8SphereBasisChange * E8.inn * e8SphereBasisChange.transpose =
      -e8GramMatrix := by
  rw [e8GramMatrix_eq]
  decide +kernel

/-- The integral coordinate equivalence between both `E₈` presentations. -/
noncomputable def e8SphereCarrierEquiv :
    (Fin 8 → ℤ) ≃ₗ[ℤ] E8Lattice :=
  Matrix.toLinOfInv (Pi.basisFun ℤ (Fin 8)) E8_ℤBasis
    (show e8SphereBasisChange.transpose *
        e8SphereBasisChangeInverse.transpose = 1 by
      rw [← Matrix.transpose_mul, e8SphereBasisChange_inverse_mul]
      simp)
    (show e8SphereBasisChangeInverse.transpose *
        e8SphereBasisChange.transpose = 1 by
      rw [← Matrix.transpose_mul, e8SphereBasisChange_mul_inverse]
      simp)

/-- The coordinate equivalence preserves the sign-corrected pairing. -/
theorem e8SphereCarrierEquiv_pairing
    (x y : Fin 8 → ℤ) :
    spherePackingE8Lattice.obj.pairing
        (e8SphereCarrierEquiv x) (e8SphereCarrierEquiv y) =
      (oppositeLattice e8Lattice).obj.pairing x y := by
  rw [oppositeLattice_pairing]
  change Matrix.toBilin E8_ℤBasis E8.inn
      (Matrix.toLin (Pi.basisFun ℤ (Fin 8)) E8_ℤBasis
        e8SphereBasisChange.transpose x)
      (Matrix.toLin (Pi.basisFun ℤ (Fin 8)) E8_ℤBasis
        e8SphereBasisChange.transpose y) =
    -Matrix.toBilin' e8GramMatrix x y
  rw [← LinearMap.BilinForm.comp_apply,
    Matrix.toBilin_comp, Matrix.transpose_transpose,
    e8SphereBasisChange_gram]
  simp [Matrix.toBilin_basisFun]

/-- The same coordinate equivalence on the carriers of the lattice objects. -/
noncomputable def e8SphereLatticeCarrierEquiv :
    (oppositeLattice e8Lattice).obj.carrier ≃ₗ[ℤ]
      spherePackingE8Lattice.obj.carrier :=
  e8SphereCarrierEquiv

theorem e8SphereLatticeCarrierEquiv_pairing
    (x y : (oppositeLattice e8Lattice).obj.carrier) :
    spherePackingE8Lattice.obj.pairing
        (e8SphereLatticeCarrierEquiv x)
        (e8SphereLatticeCarrierEquiv y) =
      (oppositeLattice e8Lattice).obj.pairing x y :=
  e8SphereCarrierEquiv_pairing x y

/-- Sphere-Packing-Lean's positive `E₈` equals the opposite project lattice. -/
noncomputable def e8LatticeSpherePackingIso :
    oppositeLattice e8Lattice ≅ spherePackingE8Lattice := by
  let eBilin :
      (oppositeLattice e8Lattice).obj ≅ spherePackingE8Lattice.obj := {
    hom := BilinModuleCat.homMk e8SphereLatticeCarrierEquiv.toLinearMap
      e8SphereLatticeCarrierEquiv_pairing
    inv := BilinModuleCat.homMk e8SphereLatticeCarrierEquiv.symm.toLinearMap
      (fun x y ↦ by
        rw [← e8SphereLatticeCarrierEquiv_pairing]
        simp)
    hom_inv_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact e8SphereLatticeCarrierEquiv.symm_apply_apply x
    inv_hom_id := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact e8SphereLatticeCarrierEquiv.apply_symm_apply x
  }
  exact ObjectProperty.isoMk (P := isLattice ℤ ℤ) eBilin

/-- The comparison makes the sign change explicit on every pair. -/
theorem e8LatticeSpherePackingIso_pairing
    (x y : (oppositeLattice e8Lattice).obj.carrier) :
    spherePackingE8Lattice.obj.pairing
        (BilinModuleCat.underlyingMap e8LatticeSpherePackingIso.hom.hom x)
        (BilinModuleCat.underlyingMap e8LatticeSpherePackingIso.hom.hom y) =
      -e8Lattice.obj.pairing x y := by
  rw [BilinModuleCat.map_pairing e8LatticeSpherePackingIso.hom.hom]
  exact oppositeLattice_pairing e8Lattice x y

end LeanCategories.Lattices.Valued
