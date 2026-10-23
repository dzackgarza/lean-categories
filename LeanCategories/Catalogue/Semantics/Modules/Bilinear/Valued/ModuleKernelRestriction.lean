/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# Restrict a chosen form to the kernel of an ordinary module map

An ordinary linear map out of the carrier of a formed module need not preserve
any target form. Its module kernel is nevertheless a selected submodule, and the
existing restriction construction applies to it. The source form and ordinary
map are independent inputs. Parameter order: scalar ring, value module, formed
source, target module, ordinary module arrow.

The fixed example is precisely `π : ℚ² → ℚ`, `π(a,b)=a`, with source form
`2ac+3bd`. Its kernel is parametrized by `t ↦ (0,t)` and has form `3st`.
The final theorem rules out treating this projection as a fixed-value formed arrow.

Source: Mathlib `LinearMap.ker` and the existing `Kernels.restricted`.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction

universe u

/-- Compose an ordinary module kernel with restriction of the independently selected form. -/
noncomputable def ordinaryKernelRestriction (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (Y : ModuleCat.{u} R) (f : X.carrierObj ⟶ Y) :
    BilinModuleCat R W :=
  Kernels.restricted R W X f.hom.ker

/-- The actual defining formed inclusion of that restriction. -/
noncomputable def ordinaryKernelInclusion (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (Y : ModuleCat.{u} R) (f : X.carrierObj ⟶ Y) :
    ordinaryKernelRestriction R W X Y f ⟶ X :=
  Kernels.restrictedInclusion R W X f.hom.ker

/-- The defining inclusion is annihilated by the original ordinary module map. -/
theorem ordinaryKernelInclusion_condition (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (Y : ModuleCat.{u} R) (f : X.carrierObj ⟶ Y) :
    (forget R W).map (ordinaryKernelInclusion R W X Y f) ≫ f = 0 := by
  ext x
  exact x.property

namespace RationalProjection

open CasCatalogue.Algebra

/-- The original source form, with the ordered diagonal entries two and three. -/
def diagonalSource : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (Matrix.toBilin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ))

/-- The exact ordinary projection into `ℚ`, obtained from its `1 × 2` matrix. -/
def projection : diagonalSource.carrierObj ⟶ ModuleCat.of ℚ ℚ :=
  RectangularLinearAlgebra.rowLinearMap 2 (CommRingCat.of ℚ) !![1, 0]

/-- The ordinary map has its prescribed, nonsquare action. -/
theorem projection_apply (x : Fin 2 → ℚ) : projection.hom x = x 0 := by
  simp [projection, RectangularLinearAlgebra.rowLinearMap_apply, Fin.sum_univ_two]

/-- The complete selected pairing, in the original coordinate order. -/
theorem diagonalSource_pairing (x y : Fin 2 → ℚ) :
    diagonalSource.pairing x y = 2 * x 0 * y 0 + 3 * x 1 * y 1 := by
  simp [diagonalSource, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

/-- Membership in the ordinary module kernel is exactly vanishing of the first coordinate. -/
theorem mem_kernel (x : Fin 2 → ℚ) : x ∈ projection.hom.ker ↔ x 0 = 0 := by
  simp [LinearMap.mem_ker, projection_apply]

/-- The fixed kernel coordinates include a scalar as the second coordinate. -/
def kernelCoordinates : ℚ ≃ₗ[ℚ] projection.hom.ker where
  toFun t := ⟨![0, t], (mem_kernel _).2 rfl⟩
  invFun x := x.val 1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · exact ((mem_kernel x.val).1 x.property).symm
    · rfl
  map_add' _ _ := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  map_smul' _ _ := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

/-- The kernel has dimension one with the specified coordinate equivalence. -/
theorem kernel_dimension : Module.finrank ℚ projection.hom.ker = 1 := by
  rw [← kernelCoordinates.finrank_eq]
  simp

/-- The restriction is formed from the actual nonsquare ordinary map. -/
noncomputable def restricted : BilinModuleCat ℚ ℚ :=
  ordinaryKernelRestriction (CommRingCat.of ℚ) (ModuleCat.of ℚ ℚ)
    diagonalSource (ModuleCat.of ℚ ℚ) projection

/-- Its actual defining inclusion into the original selected source. -/
noncomputable def inclusion : restricted ⟶ diagonalSource :=
  ordinaryKernelInclusion (CommRingCat.of ℚ) (ModuleCat.of ℚ ℚ)
    diagonalSource (ModuleCat.of ℚ ℚ) projection

/-- In the specified kernel coordinate the defining inclusion is exactly `t ↦ (0,t)`. -/
theorem inclusion_coordinates (t : ℚ) :
    BilinModuleCat.underlyingMap inclusion (kernelCoordinates t) = ![0, t] := rfl

/-- The restricted Gram matrix is `[3]`, with a universal scalar pairing formula. -/
theorem restricted_pairing (s t : ℚ) :
    restricted.pairing (kernelCoordinates s) (kernelCoordinates t) = 3 * s * t := by
  change diagonalSource.pairing ![0, s] ![0, t] = _
  rw [diagonalSource_pairing]
  simp

/-- The positive selected observation retains the nonzero restricted form. -/
theorem restricted_pairing_one :
    restricted.pairing (kernelCoordinates 1) (kernelCoordinates 1) = 3 := by
  rw [restricted_pairing]
  norm_num

/-- The actual inclusion, followed by the original projection, is zero. -/
theorem projection_inclusion (t : ℚ) :
    projection.hom (BilinModuleCat.underlyingMap inclusion (kernelCoordinates t)) = 0 := by
  rw [inclusion_coordinates, projection_apply]
  rfl

/-- No bilinear form on the actual scalar target makes this projection form preserving. -/
theorem projection_not_formed (B : LinearMap.BilinMap ℚ ℚ ℚ) :
    ¬ ∃ f : diagonalSource ⟶ BilinModuleCat.ofBilinMap B,
      BilinModuleCat.underlyingMap f = projection.hom := by
  rintro ⟨f, hf⟩
  have h := BilinModuleCat.map_pairing f ![0, 1] ![0, 1]
  rw [hf, projection_apply, projection_apply, diagonalSource_pairing] at h
  norm_num at h

end RationalProjection
end CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.bilin_module.ordinary_kernel_restriction"⟩, category := CategoryId.bilinModule
    name := "RestrictToModuleKernel"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.ordinaryKernelRestriction }
normalized_registry .morphism
  { id := ⟨"mor.bilin_module.ordinary_kernel_inclusion"⟩, category := CategoryId.bilinModule
    name := "ordinary_kernel_inclusion"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.ordinaryKernelInclusion }
normalized_registry .object
  { id := ⟨"obj.bilin_module.rational_diagonal_2_3"⟩, category := CategoryId.bilinModule
    name := "RationalDiagonal23"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.ModuleKernelRestriction.RationalProjection.diagonalSource }

end CasCatalogue
