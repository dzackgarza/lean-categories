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

set_option backward.isDefEq.respectTransparency false

/-- Given a selected commutative ring `R`, value module `W`, formed module
`X : BilinModuleCat R W`, target module `Y`, and ordinary module map
`f : X.carrierObj ⟶ Y`, form the `W`-valued module on the actual submodule
`f.hom.ker = {x | f.hom x = 0}`. Its pairing on kernel elements `x`, `y`
is `X.pairing x.val y.val`, as in `Kernels.restrictedPairing_apply`.
Parameters occur in the order `R`, `W`, `X`, `Y`, `f`. There is no form
on `Y` and no form-preservation condition on `f`. The associated formed
inclusion is `ordinaryKernelInclusion R W X Y f`. -/
noncomputable def ordinaryKernelRestriction (R : CommRingCat.{u}) (W : ModuleCat.{u} R)
    (X : BilinModuleCat R W) (Y : ModuleCat.{u} R) (f : X.carrierObj ⟶ Y) :
    BilinModuleCat R W :=
  Kernels.restricted R W X f.hom.ker

/-- At the selected parameters `R`, `W`, `X`, `Y`, `f`, the formed map
from `ordinaryKernelRestriction R W X Y f` to `X` sending each kernel
element `⟨x, hx⟩` to its original vector `x`. The domain has carrier
`{x : X.carrier | f.hom x = 0}` and the restriction of `X`'s actual
`W`-valued pairing. `ordinaryKernelInclusion_condition` states that its
underlying module inclusion followed by the original map `f` is zero. -/
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

/-- The fixed `ℚ`-valued formed `ℚ`-module with carrier `Fin 2 → ℚ` and
ordered Gram matrix `[[2,0],[0,3]]`. Its pairing is
`B((a,b),(c,d)) = 2*a*c + 3*b*d`, as stated by `diagonalSource_pairing`.
Both the scalar ring and value module are `ℚ`; there are no object parameters.
The ordinary map `projection` out of this object sends `(a,b)` to `a`. -/
abbrev diagonalSource : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (Matrix.toBilin' (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ))

/-- The exact ordinary projection into `ℚ`, obtained from its `1 × 2` matrix. -/
def projection : diagonalSource.carrierObj ⟶ ModuleCat.of ℚ ℚ :=
  RectangularLinearAlgebra.rowLinearMap 2 (CommRingCat.of ℚ) !![1, 0]

/-- The ordinary map has its prescribed, nonsquare action. -/
theorem projection_apply (x : Fin 2 → ℚ) : projection.hom x = x 0 := by
  change (!![1, 0] : Matrix (Fin 1) (Fin 2) ℚ).mulVec x 0 = x 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The complete selected pairing, in the original coordinate order. -/
theorem diagonalSource_pairing (x y : Fin 2 → ℚ) :
    diagonalSource.pairing x y = 2 * x 0 * y 0 + 3 * x 1 * y 1 := by
  simp [diagonalSource, Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

/-- Membership in the ordinary module kernel is exactly vanishing of the first coordinate. -/
theorem mem_kernel (x : Fin 2 → ℚ) : x ∈ projection.hom.ker ↔ x 0 = 0 := by
  change projection.hom x = 0 ↔ x 0 = 0
  rw [projection_apply]

/-- The fixed kernel coordinates include a scalar as the second coordinate. -/
def kernelCoordinates : ℚ ≃ₗ[ℚ] projection.hom.ker where
  toFun t := ⟨![0, t], (mem_kernel _).2 rfl⟩
  invFun x := x.val 1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    change (![0, x.val 1] : Fin 2 → ℚ) = x.val
    funext i
    fin_cases i
    · exact ((mem_kernel x.val).1 x.property).symm
    · rfl
  map_add' s t := by
    apply Subtype.ext
    change (![0, s + t] : Fin 2 → ℚ) = ![0, s] + ![0, t]
    funext i
    fin_cases i <;> simp
  map_smul' r t := by
    apply Subtype.ext
    change (![0, r * t] : Fin 2 → ℚ) = r • ![0, t]
    funext i
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
  have hz : BilinModuleCat.underlyingMap f ![0, 1] = 0 := by
    rw [hf]
    change projection.hom ![0, 1] = (0 : ℚ)
    exact projection_apply ![0, 1]
  have hp : (BilinModuleCat.ofBilinMap B).pairing
      (BilinModuleCat.underlyingMap f ![0, 1])
      (BilinModuleCat.underlyingMap f ![0, 1]) = 0 := by
    rw [hz]
    exact BilinModuleCat.pairing_zero_left _ _
  have hd : diagonalSource.pairing ![0, 1] ![0, 1] = 3 := by
    rw [diagonalSource_pairing]
    norm_num
  have impossible : (0 : ℚ) = 3 := hp.symm.trans (h.trans hd)
  norm_num at impossible

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
