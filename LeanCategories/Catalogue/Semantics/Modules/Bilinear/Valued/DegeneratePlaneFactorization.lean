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

/-- The fixed formed `ℚ`-module on `Fin 2 → ℚ` with values in `ℚ` and
zero pairing on every pair of vectors. It is the source of `cone`. -/
abbrev zeroSource : BilinModuleCat ℚ ℚ :=
  BilinModuleCat.ofBilinMap (0 : LinearMap.BilinMap ℚ (Fin 2 → ℚ) ℚ)

/-- The ordinary `ℚ`-linear map `ℚ² → ℚ²` with matrix
`[[3,-2],[-3,2]]`, sending `(s,t)` to `(3*s-2*t,-3*s+2*t)`.
Its actual endpoints are the underlying modules of `zeroSource` and
`DegeneratePlaneLifts.source`; `coneUnderlying_apply` states its action. -/
def coneUnderlying : zeroSource.carrierObj ⟶ source.carrierObj :=
  LinearAlgebra.matrixLinearMap 2 (CommRingCat.of ℚ) !![3, -2; -3, 2]

theorem coneUnderlying_apply (x : Fin 2 → ℚ) :
    coneUnderlying.hom x = ![3 * x 0 - 2 * x 1, -3 * x 0 + 2 * x 1] := by
  change (!![3, -2; -3, 2] : Matrix (Fin 2) (Fin 2) ℚ).mulVec x = _
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The formed map from `ℚ²` with zero `ℚ`-valued pairing to `ℚ²` with
pairing `B((a,b),(c,d)) = 2*(a+b)*(c+d)`, sending
`(s,t) ↦ (3*s-2*t,-3*s+2*t)`. These are the selected objects `zeroSource`
and `DegeneratePlaneLifts.source`. The target pairing vanishes on all
images, giving form preservation. `coneUnderlying_apply` gives the full
linear action; `cone_base_factorization` relates its underlying module map
to `baseMediator` followed by the selected inclusion `u ↦ (2*u,-2*u)`.
The declaration has no parameters. -/
def cone : zeroSource ⟶ source :=
  BilinModuleCat.homMk coneUnderlying.hom (by
    intro x y
    rw [coneUnderlying_apply, coneUnderlying_apply, source_pairing]
    change 2 * ((3 * x 0 - 2 * x 1) + (-3 * x 0 + 2 * x 1)) *
      ((3 * y 0 - 2 * y 1) + (-3 * y 0 + 2 * y 1)) = 0
    ring)

/-- The `ℚ`-linear map from `zeroSource.carrierObj = ℚ²` to the scalar
module `ℚ` with row matrix `[3/2,-1]`, sending `(s,t)` to
`(3*s-2*t)/2`. `baseMediator_apply` gives this formula and
`cone_base_factorization` gives its composition with `kernelInclusion`. -/
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

/-- The formed map `zeroSource → firstObject` sending `(s,t)` to the
actual range-subtype vector `(3*s-2*t,-3*s+2*t)`. Both source and target
have zero `ℚ`-valued pairing. `formedMediator_factorization` states that
following it by `firstInclusion` recovers `cone`;
`formedMediator_comparison` states that following its module map by `alpha`
recovers the scalar `baseMediator`. `formedMediator_unique` gives uniqueness. -/
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

/-- The formed `ℚ`-module on `Fin 2 → ℚ` with values in `ℚ × ℚ` and
pairing `B((s,t),(u,v)) = (0,2*(3*s-2*t)*(3*u-2*v))`.
It pulls the ordered pair of forms on `pairedSource` back along the
underlying map of `cone`, by `ChangeValueLifts.pulledBack`.
`ChangeValueLifts.pulledBack_pairing`, `pairedSource_pairing` and `coneUnderlying_apply`
describe this complete pairing and its selected coordinate order. -/
noncomputable abbrev pairedConeSource : BilinModuleCat ℚ (ℚ × ℚ) :=
  ChangeValueLifts.pulledBack ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ) pairedSource cone

/-- The formed map with scalar ring `ℚ` and value module `ℚ × ℚ` from
the plane with pairing `(0,2*(3*s-2*t)*(3*u-2*v))` to the plane with
pairing `(2*(a+b)*(c+d),a*c+b*d)`. Its vector action is
`(s,t) ↦ (3*s-2*t,-3*s+2*t)`, the same matrix `[[3,-2],[-3,2]]` as
`coneUnderlying`. The source is `pairedConeSource`, the exact pullback of
both target forms. `finalMediator_factorization` and
`finalMediator_comparison` give its factorization through the final lifted
object and the retained scalar comparison. There are no parameters. -/
noncomputable def pairedCone : pairedConeSource ⟶ pairedSource :=
  ChangeValueLifts.pulledBackHom ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ) pairedSource cone

/-- The formed map `pairedConeSource → finalObject` sending `(s,t)` to
the actual range-subtype vector `(3*s-2*t,-3*s+2*t)`, retaining both
`ℚ × ℚ`-valued forms. `finalMediator_factorization` gives its composite
with `finalInclusion`, `finalMediator_comparison` recovers `baseMediator`
through `finalAlpha`, and `finalMediator_unique` gives uniqueness. -/
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
