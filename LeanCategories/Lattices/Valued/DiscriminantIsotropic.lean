/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PrimitiveReduction
public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Lattices.Valued.DiscriminantQuadratic

/-!
# The intrinsic discriminant subgroup of an isotropic submodule

For an isotropic submodule `P`, let `span P` denote the span of the image of `P` in
`RationalSpan R L`, and let `D` be the image in `A_L` of the submodule of `L♯` lying in that
span: this is exactly the image of `(K ⊗ P) ∩ L♯` under the projection to the discriminant form.

Quadratic isotropy of `D` is genuine content: it comes from the stronger assertion that the
rationalized form vanishes on every pair of elements of the span, proved here by induction on the
span generation. Hence there is no hidden assumption that the discriminant subgroup has
nonzero `q`; every discriminant class in `D` has zero norm.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The `Frac(R)`-span of an integral submodule inside its rational span. -/
noncomputable def rationalSpanSubmodule (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :
    Submodule (FractionRing R) (RationalSpan R L) :=
  Submodule.span (FractionRing R) (toRationalSpan R L '' P)

/-- An isotropic integral submodule is isotropic after rationalization. -/
theorem rationalizedForm_isTotallyIsotropic_span (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    {u v : TensorProduct R (FractionRing R) L.obj.carrier}
    (hu : u ∈ rationalSpanSubmodule L P) (hv : v ∈ rationalSpanSubmodule L P) :
    rationalizedForm R L u v = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      induction hv using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨p, hp, rfl⟩ := hy
          rw [rational_pairing_eq L q p]
          have hz : L.obj.pairing q p = 0 :=
            (L.obj.mem_orthogonalSubmodule_iff P p).mp (hP hp) q hq
          rw [hz, map_zero]
      | zero => exact LinearMap.BilinForm.zero_right _
      | add y z hy hz hy' hz' =>
          rw [LinearMap.BilinForm.add_right, hy', hz', add_zero]
      | smul a y hy hy' =>
          rw [LinearMap.BilinForm.smul_right_of_tower, hy', smul_zero]
  | zero => exact LinearMap.BilinForm.zero_left _
  | add x y hx hy hx' hy' =>
      rw [LinearMap.BilinForm.add_left, hx', hy', add_zero]
  | smul a x hx hx' =>
      rw [LinearMap.BilinForm.smul_left_of_tower, hx', smul_zero]

/-- The discriminant-image of the isotropic subgroup inside the discriminant module. -/
noncomputable def isotropicDiscriminant (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    Submodule R L.obj.defect :=
  ((Submodule.restrictScalars R (rationalSpanSubmodule L P)).comap
      (metricDualInclusion R L)).map (metricDualToDiscriminant R L)

/-- The intrinsic discriminant subgroup is isotropic in the discriminant form. -/
theorem isotropicDiscriminant_isTotallyIsotropic
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    (discriminantBilinObject R L hL).IsTotallyIsotropic (isotropicDiscriminant L hL P) := by
  rintro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [(discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff
    (isotropicDiscriminant L hL P) (metricDualToDiscriminant R L x)]
  intro w hw
  obtain ⟨y, hy, rfl⟩ := hw
  change (discriminantBilinObject R L hL).pairing
      (metricDualToDiscriminant R L y) (metricDualToDiscriminant R L x) = 0
  rw [discriminant_pairing_metricDualToDiscriminant R hL]
  have hx' : (x : RationalSpan R L) ∈ rationalSpanSubmodule L P := hx
  have hy' : (y : RationalSpan R L) ∈ rationalSpanSubmodule L P := hy
  rw [rationalizedForm_isTotallyIsotropic_span L P hP hy' hx']
  simp

end LeanCategories.Lattices.Valued
