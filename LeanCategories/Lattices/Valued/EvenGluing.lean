/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.Gluing
public import LeanCategories.Modules.Quadratic.Valued.Witt

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}

/-- The discriminant anti-isometry data used to glue two even lattices. -/
structure EvenDiscriminantGluingData
    (L M : IntegralLatticeCat R) where
  left_fractionFieldPerfect : IsFractionFieldPerfect R L
  right_fractionFieldPerfect : IsFractionFieldPerfect R M
  left_isEven : IsEven L
  right_isEven : IsEven M
  antiIsometry : EvenDiscriminantAntiIsometry L M
    left_fractionFieldPerfect right_fractionFieldPerfect
    left_isEven right_isEven

/-- Two even lattices have discriminant data which can support anti-isometric gluing. -/
def HasEvenDiscriminantGluingData
    (L M : IntegralLatticeCat R) : Prop :=
  Nonempty (EvenDiscriminantGluingData L M)

/-- An isotropic subgroup of the quadratic discriminant form of an even lattice. -/
noncomputable abbrev EvenDiscriminantIsotropicSubgroup
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :=
  {H : Submodule R L.obj.defect //
    (evenDiscriminantQuadraticObject L hL hEven).IsTotallyIsotropic H}

/-- A quadratic metabolizer is both quadratic-isotropic and bilinear-Lagrangian. -/
noncomputable abbrev EvenDiscriminantMetabolizer
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :=
  {H : Submodule R L.obj.defect //
    (evenDiscriminantQuadraticObject L hL hEven).IsTotallyIsotropic H ∧
      (discriminantBilinObject R L hL).IsLagrangian H}

set_option backward.isDefEq.respectTransparency.types false in
/-- A quadratic-isotropic subgroup is isotropic for the discriminant pairing. -/
noncomputable def EvenDiscriminantIsotropicSubgroup.toBilinear
    [NeZero (2 : R)]
    {hL : IsFractionFieldPerfect R L} {hEven : IsEven L}
    (H : EvenDiscriminantIsotropicSubgroup hL hEven) :
    DiscriminantIsotropicSubgroup R hL := by
  refine ⟨H.1, ?_⟩
  intro x hx
  rw [(discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff]
  intro y hy
  change discriminantBilinMap R L hL y x = 0
  have hpolar := H.property.polar_eq_zero hy hx
  change QuadraticMap.polar (evenDiscriminantQuadraticMap L hL hEven)
      y x = 0 at hpolar
  rw [evenDiscriminantQuadraticMap_polar] at hpolar
  apply (doubleValueEquiv R).injective
  rw [map_zero]
  simpa [doubleValueMap_eq_doubleValueEquiv] using hpolar

/-- A quadratic-isotropic subgroup constructs an integral overlattice. -/
noncomputable def evenOverlatticeFromIsotropicSubgroup
    [NeZero (2 : R)]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (H : EvenDiscriminantIsotropicSubgroup hL hEven) : Overlattice R L :=
  overlatticeFromIsotropicSubgroup R hL H.toBilinear

/-! ## Evenness transfer and the correspondence

An overlattice is **even** when every element of its carrier has even self-pairing — the
overlattice-level form of `IsEven`, stated on the rational-span submodule that an `Overlattice R L`
is. The transfer lemmas connect quadratic isotropy of the discriminant subgroup with evenness of
the overlattice in both directions, and the inverse laws of `Gluing.lean` then make the
correspondence a bijection: **quadratic-isotropic subgroups of the even discriminant form are in
one-to-one correspondence with even overlattices**, the classical Nikulin correspondence at the
set level (π₀) of the truncation ruling. The overlattices are identified exactly as submodules of
the rational span between the lattice and its metric dual, so equality of overlattices is equality
of carriers. -/

/-- An overlattice is even when every element of its carrier has even self-pairing: `x · x ∈ 2R`.
This is the overlattice-level form of `IsEven` (`isIEven_iff_value_mem`): the overlattice, as a
lattice with the restricted rationalized form, is even exactly when this holds. -/
def Overlattice.IsEven (M : Overlattice R L) : Prop :=
  ∀ x ∈ M.carrier, ∃ r : R,
    rationalizedForm R L (x : RationalSpan R L) (x : RationalSpan R L) =
      2 * algebraMap R (FractionRing R) r

/-- **Evenness transfer, forward** (#25): the overlattice of a quadratic-isotropic subgroup of the
even discriminant form is even. The class of every element of the overlattice lies in the subgroup
(`H.1`), where the quadratic discriminant form vanishes; by
`evenDiscriminantQuadraticMap_metricDualToDiscriminant` that says the rationalized self-pairing is
`2R`-integral. -/
theorem evenOverlatticeFromIsotropicSubgroup_isEven [NeZero (2 : R)]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (H : EvenDiscriminantIsotropicSubgroup hL hEven) :
    (evenOverlatticeFromIsotropicSubgroup hL hEven H).IsEven := by
  intro x hx
  have hx' : (x : RationalSpan R L) ∈
      (metricDualPreimage R hL H.toBilinear).map (metricDualInclusion R L) := hx
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx'
  have hy' : metricDualToDiscriminant R L y ∈ H.1 := hy
  have hq : evenDiscriminantQuadraticMap L hL hEven
      (metricDualToDiscriminant R L y) = 0 :=
    H.2 (metricDualToDiscriminant R L y) hy'
  rw [evenDiscriminantQuadraticMap_metricDualToDiscriminant,
    doubleFractionValueProjection_eq_zero_iff] at hq
  obtain ⟨r, hr⟩ := LinearMap.mem_range.mp hq
  refine ⟨r, ?_⟩
  rw [← hxy]
  show rationalizedForm R L (y : RationalSpan R L) (y : RationalSpan R L) = _
  rw [← hr]
  change algebraMap R (FractionRing R) (2 * r) = 2 * algebraMap R (FractionRing R) r
  rw [map_mul, show algebraMap R (FractionRing R) (2 : R) = 2 from by
      rw [show (2 : R) = 1 + 1 from by ring, map_add, map_one]
      ring]

/-- **Evenness transfer, backward** (#25): the gluing subgroup of an even overlattice is
quadratic-isotropic for the even discriminant form. Every class of the gluing subgroup is the
class of an overlattice element, whose self-pairing is `2R`-integral by evenness, so the quadratic
discriminant form vanishes on it. -/
theorem glueSubgroup_isTotallyIsotropic_quadratic
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) (M : Overlattice R L)
    (hM : M.IsEven) :
    (evenDiscriminantQuadraticObject L hL hEven).IsTotallyIsotropic M.glueSubgroup := by
  intro a ha
  obtain ⟨x, rfl⟩ := ha
  simp only [LinearMap.comp_apply]
  change evenDiscriminantQuadraticMap L hL hEven
      (metricDualToDiscriminant R L (Overlattice.toMetricDual M x)) = 0
  rw [evenDiscriminantQuadraticMap_metricDualToDiscriminant]
  change doubleFractionValueProjection R
      (rationalizedForm R L (x : RationalSpan R L) (x : RationalSpan R L)) = 0
  obtain ⟨r, hr⟩ := hM x x.2
  have h2 : (2 : FractionRing R) = algebraMap R (FractionRing R) (2 : R) := by
    rw [Algebra.algebraMap_eq_smul_one, two_smul, one_add_one_eq_two]
  rw [hr, h2]
  exact doubleFractionValueProjection_double R r

/-- **The classical correspondence** (#25): for an even lattice, quadratic-isotropic subgroups of
the discriminant form are in bijection with even overlattices. `toFun` is the overlattice
construction, `invFun` the gluing subgroup; the inverse laws of `Gluing.lean` give both
roundtrips, and the transfer lemmas above place each side in the other's subtype. This is the
set-level (π₀) identification of the truncation ruling: overlattices are submodules of the
rational span between `L` and `L^∨`, compared by carrier equality. -/
noncomputable def evenDiscriminantIsotropicSubgroupEquivEvenOverlattice [NeZero (2 : R)]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :
    EvenDiscriminantIsotropicSubgroup hL hEven ≃
      {M : Overlattice R L // M.IsEven} where
  toFun H := ⟨evenOverlatticeFromIsotropicSubgroup hL hEven H,
    evenOverlatticeFromIsotropicSubgroup_isEven hL hEven H⟩
  invFun M := ⟨M.1.glueSubgroup,
    glueSubgroup_isTotallyIsotropic_quadratic hL hEven M.1 M.2⟩
  left_inv H := by
    apply Subtype.ext
    exact glue_overlatticeFromIsotropicSubgroup hL H.toBilinear
  right_inv M := by
    apply Subtype.ext
    exact overlatticeFromIsotropicSubgroup_glue hL M.1

end LeanCategories.Lattices.Valued
