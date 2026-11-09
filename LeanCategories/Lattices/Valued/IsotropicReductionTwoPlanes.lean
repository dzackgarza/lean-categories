/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.EvenReduction
public import LeanCategories.Lattices.Valued.IsotropicDiscriminantAction
public import LeanCategories.Lattices.Valued.IsotropicReductionDiscriminant
public import LeanCategories.Lattices.Valued.IsotropicReductionLevel

@[expose] public section

namespace LeanCategories.Lattices.Valued

open LeanCategories.Modules.Bilinear.Valued

/-- The second standard basis vector is a unimodular dual of the standard isotropic vector. -/
theorem twoHyperbolicPlanes_standard_pairing_dual :
    twoHyperbolicPlanes.obj.pairing standardVector ![0, 1, 0, 0] = 1 := by
  rw [twoHyperbolicPlanes_pairing]
  simp [standardVector]

/-- The standard line is totally isotropic in `U ⊕ U`. -/
theorem twoHyperbolicPlanes_standardLine_isotropic :
    twoHyperbolicPlanes.obj.IsTotallyIsotropic (Submodule.span ℤ {standardVector}) := by
  intro x hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_singleton.mp hx)
  rw [twoHyperbolicPlanes.obj.mem_orthogonalSubmodule_iff]
  intro y hy
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_singleton.mp hy)
  change twoHyperbolicPlanes.obj.pairing
    (b • twoHyperbolicPlanesVector.toVector) (a • twoHyperbolicPlanesVector.toVector) = 0
  change twoHyperbolicPlanes.obj.bilinMap (b • twoHyperbolicPlanesVector.toVector)
    (a • twoHyperbolicPlanesVector.toVector) = 0
  rw [map_smul, map_smul]
  change a * (b * twoHyperbolicPlanes.obj.pairing twoHyperbolicPlanesVector.toVector
    twoHyperbolicPlanesVector.toVector) = 0
  rw [twoHyperbolicPlanesVector.isotropic]
  simp

/-- `U ⊕ U` has nondegenerate integral pairing. -/
theorem twoHyperbolicPlanes_isNondegenerate : twoHyperbolicPlanes.obj.IsNondegenerate := by
  rw [twoHyperbolicPlanes.obj.isNondegenerate_iff_adjoint_injective_of_isSymmetric
    twoHyperbolicPlanes.property.2]
  exact adjoint_injective_of_fractionFieldPerfect ℤ twoHyperbolicPlanes
    twoHyperbolicPlanes_isFractionFieldPerfect

/-- Primitive isotropic reduction data for the standard line in `U ⊕ U`. -/
noncomputable def twoHyperbolicPlanesReductionData :
    IsotropicReductionData twoHyperbolicPlanes where
  submodule := Submodule.span ℤ {standardVector}
  isotropic := twoHyperbolicPlanes_standardLine_isotropic
  primitive := standardVector_primitiveSpan
  nondegenerate := twoHyperbolicPlanes_isNondegenerate
  finite := inferInstanceAs (Module.Finite ℤ (Fin 4 → ℤ))

/-- The discriminant subgroup of the standard line vanishes because the line has an integral
unimodular dual. -/
theorem twoHyperbolicPlanes_standard_isotropicDiscriminant_eq_bot :
    isotropicDiscriminant twoHyperbolicPlanes twoHyperbolicPlanes_isFractionFieldPerfect
      (Submodule.span ℤ {standardVector}) = ⊥ := by
  exact isotropicDiscriminant_span_singleton_eq_bot twoHyperbolicPlanes
    twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_standard_pairing_dual

/-- The discriminant subquotient of the standard line is trivial, because the whole ambient
discriminant of `U ⊕ U` is trivial. -/
theorem twoHyperbolicPlanes_isotropicDiscriminantSubquotient_subsingleton :
    Subsingleton (↥(isotropicDiscriminantOrthogonal twoHyperbolicPlanes
        twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanesReductionData.submodule) ⧸
      isotropicDiscriminantInOrthogonal twoHyperbolicPlanes
        twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanesReductionData.submodule) := by
  let _ := twoHyperbolicPlanes_defect_subsingleton
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      exact congrArg Submodule.Quotient.mk (Subsingleton.elim a b)

/-- The canonical comparison on `U ⊕ U` identifies two subsingleton discriminant groups. -/
theorem twoHyperbolicPlanes_extendDualSubquotientHom_bijective
    {C : Submodule ℤ twoHyperbolicPlanes.obj.carrier}
    (hsup : twoHyperbolicPlanesReductionData.perp ⊔ C = ⊤)
    (hinf : twoHyperbolicPlanesReductionData.perp ⊓ C = ⊥) :
    Function.Bijective (extendDualSubquotientHom twoHyperbolicPlanesReductionData
      twoHyperbolicPlanes.property.2 twoHyperbolicPlanes_isFractionFieldPerfect hsup hinf) := by
  let _ := twoHyperbolicPlanes_isotropicDiscriminantSubquotient_subsingleton
  refine ⟨extendDualSubquotientHom_injective twoHyperbolicPlanesReductionData
    twoHyperbolicPlanes.property.2 twoHyperbolicPlanes_isFractionFieldPerfect hsup hinf, ?_⟩
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The reduced discriminant is a subsingleton, using the actual canonical comparison. -/
theorem twoHyperbolicPlanes_reduction_discriminant_subsingleton
    {C : Submodule ℤ twoHyperbolicPlanes.obj.carrier}
    (hsup : twoHyperbolicPlanesReductionData.perp ⊔ C = ⊤)
    (hinf : twoHyperbolicPlanesReductionData.perp ⊓ C = ⊥) :
    Subsingleton (twoHyperbolicPlanesReductionData.reductionLattice
      twoHyperbolicPlanes.property.2).obj.defect := by
  let _ := twoHyperbolicPlanes_isotropicDiscriminantSubquotient_subsingleton
  constructor
  intro x y
  apply extendDualSubquotientHom_injective twoHyperbolicPlanesReductionData
    twoHyperbolicPlanes.property.2 twoHyperbolicPlanes_isFractionFieldPerfect hsup hinf
  exact Subsingleton.elim _ _

/-- The `U ⊕ U` worked equivalence, given by the canonical extension map. On this model the
isotropic line has an integral dual, so `D = 0` and the comparison needs no count: it is the
unconditional discriminant isometry of the isotropic reduction. -/
noncomputable def twoHyperbolicPlanesExtendDualDiscriminantEquiv
    {C : Submodule ℤ twoHyperbolicPlanes.obj.carrier}
    (hsup : twoHyperbolicPlanesReductionData.perp ⊔ C = ⊤)
    (hinf : twoHyperbolicPlanesReductionData.perp ⊓ C = ⊥) :
    (twoHyperbolicPlanesReductionData.reductionLattice twoHyperbolicPlanes.property.2).obj.defect
      ≃ₗ[ℤ]
      (↥(isotropicDiscriminantOrthogonal twoHyperbolicPlanes
          twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanesReductionData.submodule) ⧸
        isotropicDiscriminantInOrthogonal twoHyperbolicPlanes
          twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanesReductionData.submodule) :=
  extendDualDiscriminantEquiv twoHyperbolicPlanes twoHyperbolicPlanesReductionData
    twoHyperbolicPlanes.property.2 twoHyperbolicPlanes_isFractionFieldPerfect hsup hinf

end LeanCategories.Lattices.Valued

