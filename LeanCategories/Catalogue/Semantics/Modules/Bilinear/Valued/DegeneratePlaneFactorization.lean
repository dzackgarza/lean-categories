/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# Nonzero factorization through the two returned restrictions

The cone is independently fixed by `h(s,t)=(3s-2t,-3s+2t)`. Its first source
form is zero, and its base mediator is `(3s-2t)/2`. The returned first and final
defining maps are reused in the factorization equations. Both comparisons are
retained, including the nonidentity first comparison.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization

open CasCatalogue.Algebra
open DegeneratePlaneLifts

set_option backward.isDefEq.respectTransparency false

abbrev zeroSource : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (0 : LinearMap.BilinMap ℚ (Fin 2 → ℚ) ℚ)

/-- The cone is fixed by its own matrix, before choosing its factorization. -/
def coneUnderlying : zeroSource.carrierObj ⟶ source.carrierObj :=
  LinearAlgebra.matrixLinearMap 2 (CommRingCat.of ℚ) !![3, -2; -3, 2]

theorem coneUnderlying_apply (x : Fin 2 → ℚ) :
    coneUnderlying.hom x = ![3 * x 0 - 2 * x 1, -3 * x 0 + 2 * x 1] := by
  change (!![3, -2; -3, 2] : Matrix (Fin 2) (Fin 2) ℚ).mulVec x = _
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- This nonzero cone is a genuine fixed-value formed arrow. -/
def cone : zeroSource ⟶ source :=
  BilinModuleCat.homMk coneUnderlying.hom (by
    intro x y
    rw [coneUnderlying_apply, coneUnderlying_apply, source_pairing]
    change 2 * ((3 * x 0 - 2 * x 1) + (-3 * x 0 + 2 * x 1)) *
      ((3 * y 0 - 2 * y 1) + (-3 * y 0 + 2 * y 1)) = 0
    ring)

/-- The proposed base mediator is independently specified by the row `[3/2,-1]`. -/
def baseMediator : zeroSource.carrierObj ⟶ ModuleCat.of ℚ ℚ :=
  RectangularLinearAlgebra.rowLinearMap 2 (CommRingCat.of ℚ) !![3 / 2, -1]

theorem baseMediator_apply (x : Fin 2 → ℚ) :
    baseMediator.hom x = (3 * x 0 - 2 * x 1) / 2 := by
  change (!![3 / 2, -1] : Matrix (Fin 1) (Fin 2) ℚ).mulVec x 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Compatibility is proved from the independently fixed two matrices. -/
theorem cone_base_factorization :
    (forget ℚ ℚ).map cone = baseMediator ≫ kernelInclusion := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change coneUnderlying.hom x = kernelInclusion.hom (baseMediator.hom x)
  rw [coneUnderlying_apply, kernelInclusion_apply, baseMediator_apply]
  funext j
  fin_cases j <;> simp <;> ring

/-- The first formed mediator uses the full cone values in the actual range submodule. -/
noncomputable def formedMediator : zeroSource ⟶ firstObject :=
  BilinModuleCat.homMk
    (coneUnderlying.hom.codRestrict (LinearMap.range kernelInclusion.hom) (fun x =>
      ⟨baseMediator.hom x,
        (congrArg (fun k : zeroSource.carrierObj ⟶ source.carrierObj => k.hom x)
          cone_base_factorization).symm⟩))
    (fun x y => BilinModuleCat.map_pairing cone x y)

/-- The returned first defining map factors the original cone. -/
theorem formedMediator_factorization : formedMediator ≫ firstInclusion = cone := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl

/-- The retained first comparison recovers the specified half-coordinate mediator. -/
theorem formedMediator_comparison :
    (forget ℚ ℚ).map formedMediator ≫ alpha = baseMediator := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change alpha.hom (BilinModuleCat.underlyingMap formedMediator x) = baseMediator.hom x
  rw [alpha_value]
  change coneUnderlying.hom x 0 / 2 = baseMediator.hom x
  rw [coneUnderlying_apply, baseMediator_apply]
  rfl

/-- The formed factorization is unique, as required by the full cartesian law. -/
theorem formedMediator_unique (k : zeroSource ⟶ firstObject)
    (hk : (forget ℚ ℚ).map k ≫ alpha = baseMediator ∧ k ≫ firstInclusion = cone) :
    k = formedMediator :=
  (cancel_mono firstInclusion).mp (hk.2.trans formedMediator_factorization.symm)

/-- The source of the second cone carries the pulled-back additional dot product. -/
noncomputable abbrev pairedConeSource : BilinModuleCat ℚ (ℚ × ℚ) :=
  ChangeValueLifts.pulledBack ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ) pairedSource cone

noncomputable def pairedCone : pairedConeSource ⟶ pairedSource :=
  ChangeValueLifts.pulledBackHom ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ) pairedSource cone

/-- The same full cone values factor through the second stage's actual output. -/
noncomputable def finalMediator : pairedConeSource ⟶ finalObject :=
  let g : zeroSource.carrier →ₗ[ℚ] firstObject.carrier :=
    BilinModuleCat.underlyingMap (W := ℚ) formedMediator
  BilinModuleCat.homMk g (fun _ _ => rfl)

/-- The final defining map is reused, not replaced by the earlier inclusion. -/
theorem finalMediator_factorization : finalMediator ≫ finalInclusion = pairedCone := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl

/-- The composed forward comparison still recovers the selected base mediator. -/
theorem finalMediator_comparison :
    ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)) ⋙ forget ℚ ℚ).map finalMediator ≫
      finalAlpha = baseMediator := formedMediator_comparison

/-- The composed cartesian factorization is unique. -/
theorem finalMediator_unique (k : pairedConeSource ⟶ finalObject)
    (hk : ((changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)) ⋙ forget ℚ ℚ).map k ≫
        finalAlpha = baseMediator ∧ k ≫ finalInclusion = pairedCone) :
    k = finalMediator :=
  (cancel_mono finalInclusion).mp (hk.2.trans finalMediator_factorization.symm)

theorem first_observation :
    coneUnderlying.hom ![2, 1] = ![4, -4] ∧ baseMediator.hom ![2, 1] = 2 ∧
      (BilinModuleCat.underlyingMap finalMediator ![2, 1]).val = ![4, -4] := by
  change coneUnderlying.hom ![2, 1] = ![4, -4] ∧ baseMediator.hom ![2, 1] = 2 ∧
    coneUnderlying.hom ![2, 1] = ![4, -4]
  rw [coneUnderlying_apply, baseMediator_apply]
  norm_num

theorem second_observation :
    coneUnderlying.hom ![1, 3] = ![-3, 3] ∧ baseMediator.hom ![1, 3] = -3 / 2 ∧
      (BilinModuleCat.underlyingMap finalMediator ![1, 3]).val = ![-3, 3] := by
  change coneUnderlying.hom ![1, 3] = ![-3, 3] ∧ baseMediator.hom ![1, 3] = -3 / 2 ∧
    coneUnderlying.hom ![1, 3] = ![-3, 3]
  rw [coneUnderlying_apply, baseMediator_apply]
  norm_num

end CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.bilin_module.degenerate_plane_cone"⟩, category := CategoryId.bilinModule
    name := "degenerate_plane_cone"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone }
normalized_registry .morphism
  { id := ⟨"mor.bilin_module.degenerate_plane_paired_cone"⟩, category := CategoryId.bilinModule
    name := "degenerate_plane_paired_cone"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone }

end CasCatalogue
