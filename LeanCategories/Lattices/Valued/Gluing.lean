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

set_option backward.isDefEq.respectTransparency.types false in
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

/-! ## The inverse laws

`overlatticeFromIsotropicSubgroup` and `Overlattice.glue` are inverse on the nose: gluing the
overlattice of an isotropic subgroup returns the subgroup, and the overlattice of the gluing of an
integral overlattice returns the overlattice. This is the exact identification of overlattices the
correspondence uses: an overlattice *is* a submodule of the rational span between the lattice and
its metric dual, so equality of overlattices is equality of carriers. -/

/-- **Inverse law, subgroup side** (#25): the gluing subgroup of the overlattice built from an
isotropic subgroup is the subgroup itself. Surjectivity of the discriminant projection
`L^∨ → A_L` places every class of `H` in the image of the preimage. -/
theorem glue_overlatticeFromIsotropicSubgroup
    (H : DiscriminantIsotropicSubgroup R hL) :
    (overlatticeFromIsotropicSubgroup R hL H).glueSubgroup = H.1 := by
  apply le_antisymm
  · rintro a ⟨x, rfl⟩
    simp only [LinearMap.comp_apply]
    have hx : (x : RationalSpan R L) ∈
        (metricDualPreimage R hL H).map (metricDualInclusion R L) := x.2
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
    have hval : Overlattice.toMetricDual (overlatticeFromIsotropicSubgroup R hL H) x = y :=
      Subtype.ext hxy.symm
    rw [hval]
    exact hy
  · intro a ha
    obtain ⟨y, rfl⟩ := metricDualToDiscriminant_surjective R L hL a
    refine ⟨⟨(y : RationalSpan R L),
      Submodule.mem_map_of_mem (f := metricDualInclusion R L) ha⟩, ?_⟩
    rfl

/-- **Inverse law, overlattice side** (#25): the overlattice built from the gluing subgroup of an
integral overlattice is the overlattice itself. An element of the preimage of the image differs
from an element of the overlattice by an element of the kernel — which is the image of the lattice
(`ker_metricDualToDiscriminant`) — and the lattice lies in every overlattice. -/
theorem overlatticeFromIsotropicSubgroup_glue (M : Overlattice R L) :
    overlatticeFromIsotropicSubgroup R hL (M.glue hL) = M := by
  apply Subtype.ext
  apply le_antisymm
  · intro z hz
    have hx : (z : RationalSpan R L) ∈
        (metricDualPreimage R hL (M.glue hL)).map (metricDualInclusion R L) := hz
    obtain ⟨y, hy, hzy⟩ := Submodule.mem_map.mp hx
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hy
    simp only [LinearMap.comp_apply] at hm
    have hker : y - Overlattice.toMetricDual M m ∈
        LinearMap.ker (metricDualToDiscriminant R L) := by
      rw [LinearMap.mem_ker]
      rw [show metricDualToDiscriminant R L (y - Overlattice.toMetricDual M m) =
          metricDualToDiscriminant R L y -
            metricDualToDiscriminant R L (Overlattice.toMetricDual M m) from
        map_sub (metricDualToDiscriminant R L) y (Overlattice.toMetricDual M m)]
      rw [← hm, sub_self]
    rw [ker_metricDualToDiscriminant R L hL] at hker
    obtain ⟨l, hl⟩ := LinearMap.mem_range.mp hker
    have hsum : y = Overlattice.toMetricDual M m + toMetricDual R L l := by
      rw [hl]
      module
    have hsplit : (y : RationalSpan R L) =
        (Overlattice.toMetricDual M m : RationalSpan R L) +
        (toMetricDual R L l : RationalSpan R L) := by
      simpa using congrArg
        (Subtype.val : ↥(metricDual R L) → RationalSpan R L) hsum
    rw [← hzy]
    show (y : RationalSpan R L) ∈ M.carrier
    rw [hsplit]
    have hm' : (Overlattice.toMetricDual M m : RationalSpan R L) ∈ M.carrier := m.2
    have hl' : (toMetricDual R L l : RationalSpan R L) ∈ M.carrier := by
      change toRationalSpan R L l ∈ M.carrier
      exact M.integralImage_le (LinearMap.mem_range_self _ l)
    exact M.carrier.add_mem hm' hl'
  · intro z hz
    have hzmem : (z : RationalSpan R L) ∈ metricDual R L := M.le_metricDual hz
    refine Submodule.mem_map.mpr ⟨⟨(z : RationalSpan R L), hzmem⟩, ?_, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

/-- **Monotonicity, subgroup side** (#25): a larger isotropic subgroup gives a larger
overlattice. -/
theorem overlatticeSubmodule_mono
    {H K : DiscriminantIsotropicSubgroup R hL} (hHK : H.1 ≤ K.1) :
    overlatticeSubmodule R hL H ≤ overlatticeSubmodule R hL K := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_map.mpr ⟨y, hHK hy, rfl⟩

/-- **Monotonicity, overlattice side** (#25): a larger overlattice has a larger gluing subgroup. -/
theorem glueSubgroup_mono {M N : Overlattice R L} (hMN : M.carrier ≤ N.carrier) :
    M.glueSubgroup ≤ N.glueSubgroup := by
  rintro a ⟨x, rfl⟩
  simp only [LinearMap.comp_apply]
  refine ⟨⟨(x : RationalSpan R L), hMN x.2⟩, ?_⟩
  rfl

end LeanCategories.Lattices.Valued
