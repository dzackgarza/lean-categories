/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PrimitiveReduction
public import LeanCategories.Lattices.Valued.DiscriminantIsotropic

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The orthogonal complement inside `A_L` of the intrinsic isotropic subgroup. -/
noncomputable def isotropicDiscriminantPerp (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    Submodule R L.obj.defect :=
  (discriminantBilinObject R L hL).orthogonalSubmodule (isotropicDiscriminant L hL P)

/-- The integral dual representatives used by the intrinsic subgroup. -/
theorem toMetricDual_mem_isotropicDiscriminant (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) {P : Submodule R L.obj.carrier}
    {x : L.obj.carrier} (hx : x ∈ P) :
    metricDualToDiscriminant R L (toMetricDual R L x) ∈ isotropicDiscriminant L hL P := by
  refine ⟨toMetricDual R L x, ?_, rfl⟩
  show (toMetricDual R L x : RationalSpan R L) ∈ rationalSpanSubmodule L P
  have hxx : (x : L.obj.carrier) = x := rfl
  rw [show (toMetricDual R L x : RationalSpan R L) = toRationalSpan R L x from rfl]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

/-- Evaluation of a discriminant pairing on the dual representative of an integral vector gives
the integral evaluation, not an abstract pairing. -/
theorem discriminantBilinMap_valueDual_adjoint (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (f : L.obj.valueDual) (x : L.obj.carrier) :
    discriminantBilinMap R L hL (Submodule.Quotient.mk f)
        (L.obj.defectProjection (L.obj.adjoint x)) =
      fractionValueProjection R (algebraMap R (FractionRing R) (f x)) := by
  change (discriminantBilinMap R L hL) (Submodule.Quotient.mk f)
      (Submodule.Quotient.mk (L.obj.adjoint x)) = _
  rw [discriminantBilinMap_mk, rieszDualBilinMap_adjoint_right R L hL f x]

/-- Image of the lattice orthogonal in the orthogonal complement of the isotropic subgroup. -/
theorem toMetricDual_mem_isotropicDiscriminantPerp (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) {P : Submodule R L.obj.carrier}
    {x : L.obj.carrier}
    (hx : x ∈ L.obj.orthogonalSubmodule P) :
    metricDualToDiscriminant R L (toMetricDual R L x) ∈
      isotropicDiscriminantPerp L hL P := by
  let W : Submodule (FractionRing R) (RationalSpan R L) :=
    { carrier := {y | rationalizedForm R L y (toRationalSpan R L x) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change (rationalizedForm R L) (a + b) (toRationalSpan R L x) = 0
        rw [LinearMap.BilinForm.add_left, ha, hb, add_zero]
      smul_mem' := by
        intro r a ha
        change (rationalizedForm R L) (r • a) (toRationalSpan R L x) = 0
        rw [LinearMap.BilinForm.smul_left_of_tower, ha, smul_zero] }
  have hle : rationalSpanSubmodule L P ≤ W := by
    apply Submodule.span_le.mpr
    rintro y ⟨p, hp, rfl⟩
    change (rationalizedForm R L) (toRationalSpan R L p) (toRationalSpan R L x) = 0
    rw [rational_pairing_eq L p x]
    rw [(L.obj.mem_orthogonalSubmodule_iff P x).mp hx p hp, map_zero]
  rw [isotropicDiscriminantPerp]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [discriminant_pairing_metricDualToDiscriminant R hL]
  have hW := hle hy
  change (rationalizedForm R L) (metricDualInclusion R L y)
    (toRationalSpan R L x) = 0 at hW
  change fractionValueProjection R
    (rationalizedForm R L (metricDualInclusion R L y) (toRationalSpan R L x)) = 0
  rw [hW, map_zero]

end LeanCategories.Lattices.Valued

