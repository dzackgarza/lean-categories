/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Modules.Bilinear.Valued.Witt

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A submodule of the rational span is integral when all pairings lie in `R`. -/
def IsIntegralSubmodule (R : Type u) [CommRing R] [IsDomain R]
    (L : IntegralLatticeCat R)
    (P : Submodule R (RationalSpan R L)) : Prop :=
  P ≤ (rationalizedForm R L).dualSubmodule P

/-- An integral overlattice lies between a lattice and its metric dual. -/
noncomputable def Overlattice (R : Type u) [CommRing R] [IsDomain R]
    (L : IntegralLatticeCat R) :=
  {P : Submodule R (RationalSpan R L) //
    integralImage R L ≤ P ∧ IsIntegralSubmodule R L P}

namespace Overlattice

variable {L : IntegralLatticeCat R}

/-- The underlying submodule of an overlattice. -/
noncomputable abbrev carrier (M : Overlattice R L) :
    Submodule R (RationalSpan R L) :=
  M.1

/-- The original lattice lies in each overlattice. -/
theorem integralImage_le (M : Overlattice R L) :
    integralImage R L ≤ M.carrier :=
  M.property.1

/-- Each overlattice lies in the metric dual. -/
theorem le_metricDual (M : Overlattice R L) :
    M.carrier ≤ metricDual R L := by
  intro x hx
  have hxDual := M.property.2 hx
  change ∀ y ∈ M.carrier,
      rationalizedForm R L x y ∈
        (1 : Submodule R (FractionRing R)) at hxDual
  intro y hy
  exact hxDual y (M.integralImage_le hy)

/-- The restricted pairing of an overlattice is integral. -/
theorem isIntegral (M : Overlattice R L) :
    IsIntegralSubmodule R L M.carrier :=
  M.property.2

/-- Include the original lattice in an overlattice. -/
noncomputable def inclusion (M : Overlattice R L) :
    L.obj.carrier →ₗ[R] M.carrier :=
  LinearMap.codRestrict M.carrier (toRationalSpan R L) (by
    intro x
    apply M.integralImage_le
    exact LinearMap.mem_range_self (toRationalSpan R L) x)

end Overlattice

variable {L : IntegralLatticeCat R}
variable (hL : IsFractionFieldPerfect R L)

/-- An isotropic subgroup of the bilinear discriminant form. -/
noncomputable abbrev DiscriminantIsotropicSubgroup
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L) :=
  {H : Submodule R L.obj.defect //
    (discriminantBilinObject R L hL).IsTotallyIsotropic H}

/-- A metabolizer is a Lagrangian subgroup of the discriminant form. -/
noncomputable abbrev DiscriminantMetabolizer
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L) :=
  {H : Submodule R L.obj.defect //
    (discriminantBilinObject R L hL).IsLagrangian H}

/-- The inverse image of an isotropic subgroup inside the metric dual. -/
noncomputable def metricDualPreimage
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L)
    (H : DiscriminantIsotropicSubgroup R hL) :
    Submodule R (metricDual R L) :=
  H.1.comap (metricDualToDiscriminant R L)

/-- The rational-span submodule associated to an isotropic subgroup. -/
noncomputable def overlatticeSubmodule
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L)
    (H : DiscriminantIsotropicSubgroup R hL) :
    Submodule R (RationalSpan R L) :=
  (metricDualPreimage R hL H).map (metricDualInclusion R L)

theorem integralImage_le_overlatticeSubmodule
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L)
    (H : DiscriminantIsotropicSubgroup R hL) :
    integralImage R L ≤ overlatticeSubmodule R hL H := by
  rintro _ ⟨x, rfl⟩
  refine ⟨toMetricDual R L x, ?_, rfl⟩
  change metricDualToDiscriminant R L (toMetricDual R L x) ∈ H.1
  have hz : L.obj.defectProjection (L.obj.adjoint x) = 0 := by
    change Submodule.Quotient.mk (L.obj.adjoint x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self L.obj.adjoint x
  rw [metricDualToDiscriminant, LinearMap.comp_apply,
    metricDualToValueDual_toMetricDual R hL, hz]
  exact H.1.zero_mem

theorem overlatticeSubmodule_isIntegral
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L)
    (H : DiscriminantIsotropicSubgroup R hL) :
    IsIntegralSubmodule R L (overlatticeSubmodule R hL H) := by
  intro z hz
  rcases hz with ⟨x, hx, hxz⟩
  subst z
  intro w hw
  rcases hw with ⟨y, hy, hyw⟩
  subst w
  rw [Submodule.mem_one]
  have hyOrthogonal := H.property hy
  have hzero :=
    ((discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff
      H.1 (metricDualToDiscriminant R L y)).mp hyOrthogonal
      (metricDualToDiscriminant R L x) hx
  rw [discriminant_pairing_metricDualToDiscriminant R hL] at hzero
  rw [fractionValueProjection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hzero
  exact hzero

/-- An isotropic subgroup constructs an integral overlattice. -/
noncomputable def overlatticeFromIsotropicSubgroup
    (R : Type u) [CommRing R] [IsDomain R]
    {L : IntegralLatticeCat R} (hL : IsFractionFieldPerfect R L)
    (H : DiscriminantIsotropicSubgroup R hL) : Overlattice R L :=
  ⟨overlatticeSubmodule R hL H,
    integralImage_le_overlatticeSubmodule R hL H,
    overlatticeSubmodule_isIntegral R hL H⟩

namespace Overlattice

/-- Include an overlattice into the metric dual. -/
noncomputable def toMetricDual (M : Overlattice R L) :
    M.carrier →ₗ[R] metricDual R L :=
  LinearMap.codRestrict (metricDual R L) M.carrier.subtype
    (fun x ↦ M.le_metricDual x.property)

/-- The image of an overlattice in the discriminant module. -/
noncomputable def glueSubgroup (M : Overlattice R L) :
    Submodule R L.obj.defect :=
  LinearMap.range ((metricDualToDiscriminant R L).comp M.toMetricDual)

theorem glueSubgroup_isTotallyIsotropic (M : Overlattice R L) :
    (discriminantBilinObject R L hL).IsTotallyIsotropic
      M.glueSubgroup := by
  intro a ha
  rw [(discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff]
  intro b hb
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  change (discriminantBilinObject R L hL).pairing
      (metricDualToDiscriminant R L (M.toMetricDual y))
      (metricDualToDiscriminant R L (M.toMetricDual x)) = 0
  rw [discriminant_pairing_metricDualToDiscriminant R hL]
  change fractionValueProjection R
      (rationalizedForm R L (y : RationalSpan R L) (x : RationalSpan R L)) = 0
  have hyDual := M.isIntegral y.property
  change ∀ z ∈ M.carrier,
      rationalizedForm R L (y : RationalSpan R L) z ∈
        (1 : Submodule R (FractionRing R)) at hyDual
  have hPair := hyDual x x.property
  rw [Submodule.mem_one] at hPair
  rcases hPair with ⟨r, hr⟩
  rw [← hr]
  change fractionValueProjection R
      (algebraMap R (FractionRing R) r) = 0
  exact fractionValueProjection_algebraMap R r

/-- Recover the isotropic gluing subgroup from an overlattice. -/
noncomputable def glue (M : Overlattice R L) :
    DiscriminantIsotropicSubgroup R hL :=
  ⟨M.glueSubgroup, M.glueSubgroup_isTotallyIsotropic hL⟩

end Overlattice

end LeanCategories.Lattices.Valued
