/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PrimitiveReduction
public import LeanCategories.Lattices.Valued.QuadraticSubquotient
public import LeanCategories.Lattices.Valued.DiscriminantQuotient
public import LeanCategories.Lattices.Valued.DiscriminantAction
public import LeanCategories.Lattices.Valued.CuspWorkedInstance

/-!
# The isotropic discriminant `D` is natural, and the stabilizer acts on `D^⊥/D`

For a primitive isotropic submodule `P` of an integral lattice `L` with perfect generic fiber, the
intrinsic discriminant subgroup `D = isotropicDiscriminant L hL P` is the image in `A_L` of
`(K ⊗ P) ∩ L♯`. The reduction `Q = P^⊥/P` has discriminant `A_Q`; the interface between the two
is the subquotient `D^⊥/D` of the discriminant form of `L`, which by the reduction theorem is
naturally isometric to `A_Q`.

This file proves the *naturality* half of that interface, in a form that does not depend on the
reduction theorem:

* an isometry `g` of `L` carries `D(P)` to `D(g P)` — `isotropicDiscriminant_actOnDefect`;
* hence an isometry stabilizing `P` exactly carries `D` to itself, its orthogonal `D^⊥` to itself,
  and acts on the subquotient `D^⊥/D` (`discriminantSubquotientEquiv`);
* the quotient form on `D^⊥/D` — the restriction of the discriminant form, which descends because
  `D` is totally isotropic — is preserved by that action (`discriminantSubquotientBilinMap_...`);
* if the isotropic line `P` has an integral dual, `D` vanishes and `D^⊥/D = A_L`
  (`isotropicDiscriminant_eq_bot_of_pairing_eq_one`), which is the shape the `U ⊕ U` and
  `U(2) ⊕ U` worked instances take.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

open OrthogonalGroup

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}

/-! ## The rational span transforms naturally -/

/-- The rational action sends a lattice vector to the rationalization of its image. -/
theorem actOnRationalSpan_toRationalSpan (g : OrthogonalGroup L) (x : L.obj.carrier) :
    actOnRationalSpan g (toRationalSpan R L x) = toRationalSpan R L (g.1 x) := by
  have h : actOnRationalSpan g =
      (g.1).baseChange R (FractionRing R) L.obj.carrier L.obj.carrier := rfl
  rw [h, show toRationalSpan R L x = (1 : FractionRing R) ⊗ₜ[R] x from rfl,
    LinearEquiv.baseChange_tmul]
  rfl

/-- The rational span of `P` is carried onto the rational span of the image submodule. -/
theorem rationalSpanSubmodule_map_actOnRationalSpan (g : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) :
    (rationalSpanSubmodule L P).map (actOnRationalSpan g).toLinearMap =
      rationalSpanSubmodule L (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) := by
  rw [rationalSpanSubmodule, rationalSpanSubmodule, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨g.1 p, Submodule.mem_map_of_mem hp,
      (actOnRationalSpan_toRationalSpan g p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hp
    exact ⟨toRationalSpan R L q, ⟨q, hq, rfl⟩, actOnRationalSpan_toRationalSpan g q⟩

/-- Membership in the rational span, transported along an isometry. -/
theorem actOnRationalSpan_mem_rationalSpanSubmodule_iff (g : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) (y : RationalSpan R L) :
    actOnRationalSpan g y ∈
        rationalSpanSubmodule L (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) ↔
      y ∈ rationalSpanSubmodule L P := by
  constructor
  · intro hy
    rw [← rationalSpanSubmodule_map_actOnRationalSpan g P] at hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
    rw [← (actOnRationalSpan g).injective hzy]
    exact hz
  · intro hy
    rw [← rationalSpanSubmodule_map_actOnRationalSpan g P]
    exact Submodule.mem_map_of_mem hy



section Naturality

variable (L : IntegralLatticeCat R)

/-- The preimage in the metric dual of the rational span of `P`: this is `(K ⊗ P) ∩ L♯`. -/
noncomputable def isotropicDiscriminantPreimage (P : Submodule R L.obj.carrier) :
    Submodule R (metricDual R L) :=
  (Submodule.restrictScalars R (rationalSpanSubmodule L P)).comap (metricDualInclusion R L)

theorem mem_isotropicDiscriminantPreimage (P : Submodule R L.obj.carrier)
    (x : metricDual R L) :
    x ∈ isotropicDiscriminantPreimage L P ↔ (x : RationalSpan R L) ∈ rationalSpanSubmodule L P :=
  Iff.rfl

theorem isotropicDiscriminant_eq_map_preimage (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) :
    isotropicDiscriminant L hL P =
      (isotropicDiscriminantPreimage L P).map (metricDualToDiscriminant R L) :=
  rfl

/-- The preimage of the rational span is carried along by the metric-dual action. -/
theorem isotropicDiscriminantPreimage_map (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (g : OrthogonalGroup L) :
    (isotropicDiscriminantPreimage L P).map (actOnMetricDual g hL).toLinearMap =
      isotropicDiscriminantPreimage L (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    change (actOnMetricDual g hL y : RationalSpan R L) ∈
      rationalSpanSubmodule L (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier))
    rw [actOnMetricDual_coe, ← rationalSpanSubmodule_map_actOnRationalSpan g P]
    exact Submodule.mem_map_of_mem hy
  · intro z hz
    have hzV : (z : RationalSpan R L) ∈
        rationalSpanSubmodule L (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) := hz
    rw [← rationalSpanSubmodule_map_actOnRationalSpan g P] at hzV
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hzV
    have hww : actOnRationalSpan g⁻¹ (actOnRationalSpan g w) = w :=
      (actOnRationalSpan g).injective
        (actOnRationalSpan_inv_apply g (actOnRationalSpan g w))
    have hmul : actOnMetricDual g hL (actOnMetricDual g⁻¹ hL z) = z := by
      have h2 := actOnMetricDual_mul_apply g g⁻¹ hL z
      rw [mul_inv_cancel, actOnMetricDual_one_apply] at h2
      exact h2.symm
    refine Submodule.mem_map.mpr ⟨actOnMetricDual g⁻¹ hL z, ?_, hmul⟩
    have hcoe : (actOnMetricDual g⁻¹ hL z : RationalSpan R L) = w := by
      rw [actOnMetricDual_coe]
      rw [show (z : RationalSpan R L) = actOnRationalSpan g w from hwz.symm]
      exact hww
    have hgoal : (actOnMetricDual g⁻¹ hL z : RationalSpan R L) ∈ rationalSpanSubmodule L P := by
      rw [hcoe]
      exact hw
    exact hgoal

/-- An isometry of `L` carries the intrinsic isotropic discriminant of `P` to the intrinsic
isotropic discriminant of the image isotropic submodule: the discriminant subgroup is natural. -/
theorem isotropicDiscriminant_actOnDefect (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (g : OrthogonalGroup L) :
    (isotropicDiscriminant L hL P).map (actOnDefect g).toLinearMap =
      isotropicDiscriminant L hL (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)) := by
  have hcomp : ((actOnDefect g).toLinearMap).comp (metricDualToDiscriminant R L) =
      (metricDualToDiscriminant R L).comp (actOnMetricDual g hL).toLinearMap := by
    ext x
    exact (metricDualToDiscriminant_actOnMetricDual g hL x).symm
  rw [isotropicDiscriminant_eq_map_preimage L hL P,
    isotropicDiscriminant_eq_map_preimage L hL
      (P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)),
    ← Submodule.map_comp (metricDualToDiscriminant R L) (actOnDefect g).toLinearMap
      (isotropicDiscriminantPreimage L P),
    hcomp, Submodule.map_comp (actOnMetricDual g hL).toLinearMap
      (metricDualToDiscriminant R L) (isotropicDiscriminantPreimage L P),
    isotropicDiscriminantPreimage_map L hL P g]

/-- The isotropic discriminant of a submodule is carried to itself by an isometry stabilizing the
submodule exactly. -/
theorem isotropicDiscriminant_map_of_map_eq (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (g : OrthogonalGroup L)
    (hg : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P) :
    (isotropicDiscriminant L hL P).map (actOnDefect g).toLinearMap =
      isotropicDiscriminant L hL P := by
  rw [isotropicDiscriminant_actOnDefect L hL P g, hg]

end Naturality



section OrthogonalComplement

/-- An isometry of `L` carries the orthogonal complement of a discriminant subgroup onto the
orthogonal complement of the image subgroup. -/
theorem orthogonalSubmodule_map_actOnDefect (hL : IsFractionFieldPerfect R L)
    (D : Submodule R L.obj.defect) (g : OrthogonalGroup L) :
    ((discriminantBilinObject R L hL).orthogonalSubmodule D).map
        (actOnDefect g).toLinearMap =
      (discriminantBilinObject R L hL).orthogonalSubmodule
        (D.map (actOnDefect g).toLinearMap) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    change ∀ w ∈ D.map (actOnDefect g).toLinearMap,
      discriminantBilinMap R L hL w (actOnDefect g y) = 0
    rintro _ ⟨d, hd, rfl⟩
    change discriminantBilinMap R L hL (actOnDefect g d) (actOnDefect g y) = 0
    rw [discriminantBilinMap_actOnDefect g hL]
    exact hy d hd
  · intro z hz
    have hmul : actOnDefect g (actOnDefect g⁻¹ z) = z := by
      have h2 := actOnDefect_mul_apply g g⁻¹ z
      rw [mul_inv_cancel, actOnDefect_one_apply] at h2
      exact h2.symm
    refine Submodule.mem_map.mpr ⟨actOnDefect g⁻¹ z, ?_, hmul⟩
    change ∀ d ∈ D, discriminantBilinMap R L hL d (actOnDefect g⁻¹ z) = 0
    intro d hd
    have hgd : actOnDefect g d ∈ D.map (actOnDefect g).toLinearMap :=
      Submodule.mem_map_of_mem hd
    have hz' : discriminantBilinMap R L hL (actOnDefect g d) z = 0 := hz _ hgd
    rw [← hmul] at hz'
    change discriminantBilinMap R L hL (actOnDefect g d)
      (actOnDefect g (actOnDefect g⁻¹ z)) = 0 at hz'
    rw [discriminantBilinMap_actOnDefect g hL] at hz'
    exact hz'

end OrthogonalComplement



section Subquotient

variable (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L)
variable (P : Submodule R L.obj.carrier)

/-- `D` itself, regarded as a submodule of its orthogonal complement, using the existing
owner `isotropicDiscriminantInOrthogonal`. -/
noncomputable abbrev isotropicDiscriminantInPerp :
    Submodule R ↥(isotropicDiscriminantPerp L hL P) :=
  isotropicDiscriminantInOrthogonal L hL P

theorem mem_isotropicDiscriminantInPerp_iff (x : ↥(isotropicDiscriminantPerp L hL P)) :
    x ∈ isotropicDiscriminantInPerp L hL P ↔
      (x : L.obj.defect) ∈ isotropicDiscriminant L hL P :=
  Iff.rfl

/-- The restricted discriminant form, using the existing `RestrictedBilinMap` owner. -/
noncomputable abbrev isotropicDiscriminantRestrictionBilinMap :
    LinearMap.BilinMap R ↥(isotropicDiscriminantPerp L hL P) (FractionValueQuotient R) :=
  isotropicDiscriminantRestrictedBilinMap L hL P

@[simp]
theorem isotropicDiscriminantRestrictionBilinMap_apply
    (x y : ↥(isotropicDiscriminantPerp L hL P)) :
    isotropicDiscriminantRestrictionBilinMap L hL P x y =
      discriminantBilinMap R L hL (x : L.obj.defect) (y : L.obj.defect) :=
  rfl

theorem isotropicDiscriminantInPerp_le_leftRadical :
    isotropicDiscriminantInPerp L hL P ≤
      (isotropicDiscriminantRestrictionBilinMap L hL P).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  rw [isotropicDiscriminantRestrictionBilinMap_apply]
  exact y.2 (x : L.obj.defect) hx

theorem isotropicDiscriminantInPerp_le_rightRadical :
    isotropicDiscriminantInPerp L hL P ≤
      (isotropicDiscriminantRestrictionBilinMap L hL P).flip.ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change isotropicDiscriminantRestrictionBilinMap L hL P y x = 0
  rw [isotropicDiscriminantRestrictionBilinMap_apply,
    discriminantBilinMap_isSymmetric R L hL]
  exact y.2 (x : L.obj.defect) hx

/-- The descended bilinear form, using the shared `QuadraticSubquotient` owner. -/
noncomputable abbrev isotropicDiscriminantSubquotientBilinMap :
    LinearMap.BilinMap R
      (↥(isotropicDiscriminantPerp L hL P) ⧸ isotropicDiscriminantInPerp L hL P)
      (FractionValueQuotient R) :=
  isotropicSubquotientBilinMap L hL P

@[simp]
theorem isotropicDiscriminantSubquotientBilinMap_mk
    (x y : ↥(isotropicDiscriminantPerp L hL P)) :
    isotropicDiscriminantSubquotientBilinMap L hL P
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      discriminantBilinMap R L hL (x : L.obj.defect) (y : L.obj.defect) :=
  rfl

/-- The subquotient `D^⊥/D` as the established formed object. -/
noncomputable abbrev isotropicDiscriminantSubquotient :
    BilinModuleCat R (FractionValueQuotient R) :=
  isotropicSubquotientBilinObject L hL P

omit [IsDomain R] in
theorem map_inv_eq_of_map_eq {P : Submodule R L.obj.carrier} {g : OrthogonalGroup L}
    (h : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P) :
    P.map ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P := by
  have h2 := Submodule.map_comp (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier)
    ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) P
  have hcomp : ((g⁻¹).1 : L.obj.carrier →ₗ[R] L.obj.carrier) ∘ₗ
      (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = LinearMap.id := by
    ext x
    exact (g.1).symm_apply_apply x
  rw [hcomp, Submodule.map_id, h] at h2
  exact h2.symm

/-- Membership in the orthogonal complement of the isotropic discriminant, in terms of the
discriminant bilinear map. -/
theorem isotropicDiscriminantPerp_apply_eq_zero (x : ↥(isotropicDiscriminantPerp L hL P))
    {d : L.obj.defect} (hd : d ∈ isotropicDiscriminant L hL P) :
    discriminantBilinMap R L hL d (x : L.obj.defect) = 0 :=
  x.2 d hd

/-- The action of an isometry stabilizing `P` on the orthogonal complement `D^⊥`. -/
noncomputable def actOnPerp (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P) :
    ↥(isotropicDiscriminantPerp L hL P) ≃ₗ[R] ↥(isotropicDiscriminantPerp L hL P) where
  toFun x := ⟨actOnDefect g x, by
    intro d hd
    have hd' : actOnDefect g⁻¹ (d : L.obj.defect) ∈ isotropicDiscriminant L hL P := by
      have hmem : actOnDefect g⁻¹ (d : L.obj.defect) ∈
          (isotropicDiscriminant L hL P).map (actOnDefect g⁻¹).toLinearMap :=
        Submodule.mem_map_of_mem hd
      rwa [isotropicDiscriminant_map_of_map_eq L hL P g⁻¹
        (map_inv_eq_of_map_eq (L := L) hstab)] at hmem
    have hd2 : (d : L.obj.defect) = actOnDefect g (actOnDefect g⁻¹ (d : L.obj.defect)) := by
      have h2 := actOnDefect_mul_apply g g⁻¹ (d : L.obj.defect)
      have h3 : actOnDefect (1 : OrthogonalGroup L) (d : L.obj.defect) = (d : L.obj.defect) :=
        actOnDefect_one_apply _
      rw [mul_inv_cancel, h3] at h2
      exact h2
    change discriminantBilinMap R L hL (d : L.obj.defect)
      (actOnDefect g (x : L.obj.defect)) = 0
    rw [hd2, discriminantBilinMap_actOnDefect]
    exact isotropicDiscriminantPerp_apply_eq_zero L hL P x hd'⟩
  invFun x := ⟨actOnDefect g⁻¹ x, by
    intro d hd
    have hd' : actOnDefect g (d : L.obj.defect) ∈ isotropicDiscriminant L hL P := by
      have hmem : actOnDefect g (d : L.obj.defect) ∈
          (isotropicDiscriminant L hL P).map (actOnDefect g).toLinearMap :=
        Submodule.mem_map_of_mem hd
      rwa [isotropicDiscriminant_map_of_map_eq L hL P g hstab] at hmem
    have hd2 : (d : L.obj.defect) =
        actOnDefect g⁻¹ (actOnDefect g (d : L.obj.defect)) := by
      have h2 := actOnDefect_mul_apply g⁻¹ g (d : L.obj.defect)
      have h3 : actOnDefect (1 : OrthogonalGroup L) (d : L.obj.defect) = (d : L.obj.defect) :=
        actOnDefect_one_apply _
      rw [inv_mul_cancel, h3] at h2
      exact h2
    change discriminantBilinMap R L hL (d : L.obj.defect)
      (actOnDefect g⁻¹ (x : L.obj.defect)) = 0
    rw [hd2, discriminantBilinMap_actOnDefect]
    exact isotropicDiscriminantPerp_apply_eq_zero L hL P x hd'⟩
  left_inv x := by
    apply Subtype.ext
    change actOnDefect g⁻¹ (actOnDefect g (x : L.obj.defect)) = (x : L.obj.defect)
    have h2 := actOnDefect_mul_apply g⁻¹ g (x : L.obj.defect)
    have h3 : actOnDefect (1 : OrthogonalGroup L) (x : L.obj.defect) = (x : L.obj.defect) :=
      actOnDefect_one_apply _
    rw [inv_mul_cancel, h3] at h2
    exact h2.symm
  right_inv x := by
    apply Subtype.ext
    change actOnDefect g (actOnDefect g⁻¹ (x : L.obj.defect)) = (x : L.obj.defect)
    have h2 := actOnDefect_mul_apply g g⁻¹ (x : L.obj.defect)
    have h3 : actOnDefect (1 : OrthogonalGroup L) (x : L.obj.defect) = (x : L.obj.defect) :=
      actOnDefect_one_apply _
    rw [mul_inv_cancel, h3] at h2
    exact h2.symm
  map_add' x y := by
    apply Subtype.ext
    exact (actOnDefect g).map_add (x : L.obj.defect) (y : L.obj.defect)
  map_smul' a x := by
    apply Subtype.ext
    exact (actOnDefect g).map_smul a (x : L.obj.defect)

theorem actOnPerp_mem (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P)
    {x : ↥(isotropicDiscriminantPerp L hL P)}
    (hx : x ∈ isotropicDiscriminantInPerp L hL P) :
    actOnPerp L hL P g hstab x ∈ isotropicDiscriminantInPerp L hL P := by
  have hxD : (x : L.obj.defect) ∈ isotropicDiscriminant L hL P := hx
  have hmem : actOnDefect g (x : L.obj.defect) ∈
      (isotropicDiscriminant L hL P).map (actOnDefect g).toLinearMap :=
    Submodule.mem_map_of_mem hxD
  rw [isotropicDiscriminant_map_of_map_eq L hL P g hstab] at hmem
  exact hmem

/-- The action of the stabilizer of the isotropic submodule on the subquotient `D^⊥/D` of the
discriminant form. -/
noncomputable def isotropicDiscriminantSubquotientEquiv (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P) :
    (↥(isotropicDiscriminantPerp L hL P) ⧸ isotropicDiscriminantInPerp L hL P) ≃ₗ[R]
      (↥(isotropicDiscriminantPerp L hL P) ⧸ isotropicDiscriminantInPerp L hL P) where
  toLinearMap := Submodule.mapQ (isotropicDiscriminantInPerp L hL P)
    (isotropicDiscriminantInPerp L hL P) (actOnPerp L hL P g hstab).toLinearMap
    (fun _ hx => actOnPerp_mem L hL P g hstab hx)
  invFun := Submodule.mapQ (isotropicDiscriminantInPerp L hL P)
    (isotropicDiscriminantInPerp L hL P)
    (actOnPerp L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab)).toLinearMap
    (fun _ hx => actOnPerp_mem L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab) hx)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (actOnPerp L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab)
        (actOnPerp L hL P g hstab y)) = Submodule.Quotient.mk y
      rw [show actOnPerp L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab)
          (actOnPerp L hL P g hstab y) = y from
        (actOnPerp L hL P g hstab).symm_apply_apply y]
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (actOnPerp L hL P g hstab
        (actOnPerp L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab) y)) = Submodule.Quotient.mk y
      rw [show actOnPerp L hL P g hstab
          (actOnPerp L hL P g⁻¹ (map_inv_eq_of_map_eq (L := L) hstab) y) = y from
        (actOnPerp L hL P g hstab).right_inv y]

@[simp]
theorem isotropicDiscriminantSubquotientEquiv_mk (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P)
    (x : ↥(isotropicDiscriminantPerp L hL P)) :
    isotropicDiscriminantSubquotientEquiv L hL P g hstab
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (actOnPerp L hL P g hstab x) :=
  rfl

/-- **Equivariance.** The stabilizer action on the subquotient `D^⊥/D` preserves the induced
discriminant form: the induced map on the correction subquotient is an isometry. -/
theorem isotropicDiscriminantSubquotientEquiv_pairing (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P)
    (x y : ↥(isotropicDiscriminantPerp L hL P) ⧸ isotropicDiscriminantInPerp L hL P) :
    isotropicDiscriminantSubquotientBilinMap L hL P
        (isotropicDiscriminantSubquotientEquiv L hL P g hstab x)
        (isotropicDiscriminantSubquotientEquiv L hL P g hstab y) =
      isotropicDiscriminantSubquotientBilinMap L hL P x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      rw [isotropicDiscriminantSubquotientEquiv_mk,
        isotropicDiscriminantSubquotientEquiv_mk,
        isotropicDiscriminantSubquotientBilinMap_mk,
        isotropicDiscriminantSubquotientBilinMap_mk]
      change discriminantBilinMap R L hL (actOnDefect g (a : L.obj.defect))
        (actOnDefect g (b : L.obj.defect)) =
        discriminantBilinMap R L hL (a : L.obj.defect) (b : L.obj.defect)
      rw [discriminantBilinMap_actOnDefect]

/-- The subquotient `D^⊥/D` with its induced action of the exact stabilizer of `P`. -/
noncomputable def isotropicDiscriminantSubquotientAction (g : OrthogonalGroup L)
    (hstab : P.map (g.1 : L.obj.carrier →ₗ[R] L.obj.carrier) = P) :
    BilinModuleCat.OrthogonalGroup (isotropicDiscriminantSubquotient L hL P) :=
  ⟨isotropicDiscriminantSubquotientEquiv L hL P g hstab,
    fun x y => isotropicDiscriminantSubquotientEquiv_pairing L hL P g hstab x y⟩

end Subquotient



section Vanishing

variable (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L)

/-- A rational multiple of a lattice vector that lies in the metric dual has integral multiplier,
provided the vector has an integral dual: the pairing with that dual computes the multiplier. -/
theorem algebraMap_of_smul_toRationalSpan_mem_metricDual
    {p l : L.obj.carrier} (hpl : L.obj.pairing p l = 1) {c : FractionRing R}
    (hc : c • toRationalSpan R L p ∈ metricDual R L) :
    ∃ r : R, c = algebraMap R (FractionRing R) r := by
  have h := hc
  change c • toRationalSpan R L p ∈
    (rationalizedForm R L).dualSubmodule (integralImage R L) at h
  rw [LinearMap.BilinForm.mem_dualSubmodule] at h
  have h2 := h (toRationalSpan R L l) ⟨l, rfl⟩
  rw [Submodule.mem_one] at h2
  obtain ⟨r, hr⟩ := h2
  refine ⟨r, ?_⟩
  have hval : rationalizedForm R L (c • toRationalSpan R L p) (toRationalSpan R L l) = c := by
    rw [LinearMap.BilinForm.smul_left, rational_pairing_eq L p l, hpl, map_one, mul_one]
  rw [← hval, hr]

omit [IsDomain R] in
/-- The rational span of a cyclic submodule is the `Frac(R)`-span of the rationalized generator. -/
theorem rationalSpanSubmodule_span_singleton_le (p : L.obj.carrier) :
    rationalSpanSubmodule L (Submodule.span R {p}) ≤
      Submodule.span (FractionRing R) {toRationalSpan R L p} := by
  have himg : ((toRationalSpan R L) '' (Submodule.span R {p}) :
      Set (RationalSpan R L)) =
      (Submodule.span R {toRationalSpan R L p} : Set (RationalSpan R L)) := by
    rw [← Submodule.map_coe, Submodule.map_span, Set.image_singleton]
  rw [rationalSpanSubmodule, himg, Submodule.span_span_of_tower]

/-- **The isotropic discriminant of a line with an integral dual vanishes.** If the isotropic line
`P = ⟨p⟩` has a dual lattice vector `l` with `b(p,l) = 1`, then `K p ∩ L♯ = P`, so `D = 0` and
`D^⊥/D = A_L`: the discriminant of the reduction `P^⊥/P` is the discriminant of `L` itself. This is
the shape taken by the `U ⊕ U` and `U(2) ⊕ U` worked instances. -/
theorem isotropicDiscriminant_span_singleton_eq_bot
    {p l : L.obj.carrier} (hpl : L.obj.pairing p l = 1) :
    isotropicDiscriminant L hL (Submodule.span R {p}) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  have hx' : (x : RationalSpan R L) ∈ rationalSpanSubmodule L (Submodule.span R {p}) := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (rationalSpanSubmodule_span_singleton_le L p hx')
  have hc' : c • toRationalSpan R L p ∈ metricDual R L := by
    rw [hc]; exact x.2
  obtain ⟨r, hr⟩ := algebraMap_of_smul_toRationalSpan_mem_metricDual L hpl hc'
  rw [metricDualToDiscriminant_eq_zero_iff (R := R) (L := L) hL]
  refine ⟨r • p, ?_⟩
  apply Subtype.ext
  change toRationalSpan R L (r • p) = (x : RationalSpan R L)
  rw [map_smul, ← hc, hr, IsScalarTower.algebraMap_smul (A := FractionRing R) r]

end Vanishing

/-! ## The worked instances `U ⊕ U` and `U(2) ⊕ U`

Both lattices carry the isotropic line generated by `p = e₁ + e₂`, for which the dual lattice
vector `f₂` computes the multiplier: `b(p, f₂) = 1`. By
`isotropicDiscriminant_span_singleton_eq_bot` the intrinsic isotropic discriminant of that line
therefore vanishes, so the interface `D^⊥/D` between the discriminant form of `L` and the
discriminant form of the reduction is all of `A_L` in exactly these two instances. -/

/-- The bilinear map of `U(2) ⊕ U` on `Fin 4 → ℤ`: a hyperbolic plane scaled by `2` and a
hyperbolic plane. -/
def u2PlusUBilinMap : LinearMap.BilinMap ℤ (Fin 4 → ℤ) ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y => 2 * (x 0 * y 1 + x 1 * y 0) + (x 2 * y 3 + x 3 * y 2))
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- `U(2) ⊕ U` presented on `Fin 4 → ℤ`. -/
def u2PlusU : IntegralLatticeCat ℤ :=
  ⟨BilinModuleCat.ofBilinMap u2PlusUBilinMap, by
    change Module.Projective ℤ (Fin 4 → ℤ)
    infer_instance, by
    intro x y
    change 2 * (x 0 * y 1 + x 1 * y 0) + (x 2 * y 3 + x 3 * y 2) =
      2 * (y 0 * x 1 + y 1 * x 0) + (y 2 * x 3 + y 3 * x 2)
    ring⟩

theorem u2PlusU_pairing (x y : Fin 4 → ℤ) :
    u2PlusU.obj.pairing x y =
      2 * (x 0 * y 1 + x 1 * y 0) + (x 2 * y 3 + x 3 * y 2) := rfl

/-- The isotropic generator `e₁ + e₂` of `U(2) ⊕ U`. -/
def u2PlusUIsotropicVector : Fin 4 → ℤ := ![1, 0, 1, 0]

/-- The dual vector `f₂`: it pairs to `1` with the isotropic generator. -/
def u2PlusUDualVector : Fin 4 → ℤ := ![0, 0, 0, 1]

theorem u2PlusU_pairing_isotropic_dual :
    u2PlusU.obj.pairing u2PlusUIsotropicVector u2PlusUDualVector = 1 := by
  rw [u2PlusU_pairing]
  simp [u2PlusUIsotropicVector, u2PlusUDualVector]

theorem u2PlusU_isotropic :
    u2PlusU.obj.pairing u2PlusUIsotropicVector u2PlusUIsotropicVector = 0 := by
  rw [u2PlusU_pairing]
  simp [u2PlusUIsotropicVector]

/-- **`U(2) ⊕ U` instance**: the isotropic discriminant of the line `⟨e₁ + e₂⟩` vanishes, so
`D^⊥/D = A_L` there. -/
theorem u2PlusU_isotropicDiscriminant_eq_bot
    (hL : IsFractionFieldPerfect ℤ u2PlusU) :
    isotropicDiscriminant u2PlusU hL
      (Submodule.span ℤ {u2PlusUIsotropicVector}) = ⊥ :=
  isotropicDiscriminant_span_singleton_eq_bot u2PlusU hL
    u2PlusU_pairing_isotropic_dual

/-- The isotropic vector `e₁ + e₂` of `U ⊕ U`. -/
def twoHyperbolicPlanesIsotropicVector : Fin 4 → ℤ := ![1, 0, 1, 0]

theorem twoHyperbolicPlanes_pairing_isotropic_dual :
    twoHyperbolicPlanes.obj.pairing twoHyperbolicPlanesIsotropicVector ![0, 0, 0, 1] = 1 := by
  rw [twoHyperbolicPlanes_pairing]
  simp [twoHyperbolicPlanesIsotropicVector]

theorem twoHyperbolicPlanes_isotropic_isotropic :
    twoHyperbolicPlanes.obj.pairing twoHyperbolicPlanesIsotropicVector
      twoHyperbolicPlanesIsotropicVector = 0 := by
  rw [twoHyperbolicPlanes_pairing]
  simp [twoHyperbolicPlanesIsotropicVector]

/-- **`U ⊕ U` instance**: the isotropic discriminant of the line `⟨e₁ + e₂⟩` vanishes, so
`D^⊥/D = A_L` there. -/
theorem twoHyperbolicPlanes_isotropicDiscriminant_eq_bot
    (hL : IsFractionFieldPerfect ℤ twoHyperbolicPlanes) :
    isotropicDiscriminant twoHyperbolicPlanes hL
      (Submodule.span ℤ {twoHyperbolicPlanesIsotropicVector}) = ⊥ :=
  isotropicDiscriminant_span_singleton_eq_bot twoHyperbolicPlanes hL
    twoHyperbolicPlanes_pairing_isotropic_dual

end LeanCategories.Lattices.Valued
