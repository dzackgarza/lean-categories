/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantIsotropic
public import LeanCategories.Lattices.Valued.DiscriminantQuotient
public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.EvenGluing
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# The quadratic refinement of the discriminant on `D^⊥/D`

`isotropicDiscriminant L hL P` is the subgroup `D ⊆ A_L` cut out by the rational span of an
isotropic submodule `P`, and `DiscriminantIsotropic` proves that it is isotropic for the
discriminant *bilinear* form.  For an even lattice the discriminant carries the finer quadratic
refinement `evenDiscriminantQuadraticMap : A_L → Frac(R)/2R`, and the bilinear isotropy alone does
not say that `q` descends to a subquotient: one needs `q` to vanish on the subgroup one divides by,
not merely that its polarization does.

The main results here are

* `evenDiscriminantQuadraticMap_eq_zero_of_mem_isotropicDiscriminant`: the refinement vanishes on
  `D` itself, computed on the metric-dual representative as `⟨x,x⟩ = 0` for `x` in the rational
  span of `P` (this is where isotropy of `P` over `Frac R` is used, not just `ℤ`-integrality);
* `isotropicDiscriminant_le_radical`: consequently the restriction of `q_A` to the orthogonal
  `D^⊥` lies in the radical of the restricted quadratic map modulo `D`, so it descends to a genuine
  quadratic form on the subquotient `D^⊥/D`;
* `isotropicSubquotientQuadraticMap` and `isotropicSubquotientQuadModule`: the descended quadratic
  form and quadratic module of this subquotient. Identifying it with the discriminant of
  `Q = P^⊥/P` is the separate theorem still to be proved, not the construction itself;
* `isotropicSubquotientQuadraticMap_polar`: the polarization of the descended form is the
  discriminant bilinear form of `L` restricted to `D^⊥/D`, transported along `doubleValueMap`;
* `isotropicSubquotientQuadraticMap_mk_metricDualToDiscriminant`: the value on the class of a
  metric-dual element is the rationalized self-pairing, reduced mod `2R`;
* `isotropicSubquotientBilinObject` and `polar_isotropicSubquotientQuadraticMap`: the same for the
  discriminant bilinear form — it descends to `D^⊥/D`, is symmetric, and is the polarization of
  the descended refinement after `doubleValueMap`;
* `isotropicSubquotientQuadraticMap_unique` and `isotropicDiscriminant_congr`: the descended form
  is the unique one inducing `q_A`, and `D` depends only on the rational span of `P`;
* `evenDiscriminantIsotropicSubgroupOfIsotropic` with
  `evenOverlatticeFromIsotropicSubgroup_glueSubgroup`/`_glue_isEven`: the existing `EvenGluing`
  construction accepts `D`, giving an even overlattice whose glue subgroup is `D` itself.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The pairing of the discriminant bilinear object is the discriminant bilinear map. -/
@[simp]
theorem discriminantBilinObject_pairing (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (x y : L.obj.defect) :
    (discriminantBilinObject R L hL).pairing x y = discriminantBilinMap R L hL x y :=
  rfl

/-- The orthogonal complement in `A_L` of the intrinsic discriminant subgroup `D`, through the
shared owner `isotropicDiscriminantPerp` already in `DiscriminantQuotient`. -/
noncomputable abbrev isotropicDiscriminantOrthogonal (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    Submodule R L.obj.defect :=
  isotropicDiscriminantPerp L hL P

/-- `D` viewed as a submodule of its own orthogonal complement. -/
noncomputable def isotropicDiscriminantInOrthogonal (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    Submodule R ↥(isotropicDiscriminantOrthogonal L hL P) :=
  Submodule.comap (isotropicDiscriminantOrthogonal L hL P).subtype
    (isotropicDiscriminant L hL P)

/-- The intrinsic discriminant subgroup sits inside its orthogonal complement. -/
theorem isotropicDiscriminant_le_orthogonal (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier)
    (hP : L.obj.IsTotallyIsotropic P) :
    isotropicDiscriminant L hL P ≤ isotropicDiscriminantOrthogonal L hL P :=
  isotropicDiscriminant_isTotallyIsotropic L hL P hP

/-- A vector of `D` is invisible to the descended form: the quadratic refinement vanishes on the
intrinsic discriminant subgroup, not only its polarization. -/
theorem evenDiscriminantQuadraticMap_eq_zero_of_mem_isotropicDiscriminant
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    {z : L.obj.defect} (hz : z ∈ isotropicDiscriminant L hL P) :
    evenDiscriminantQuadraticMap L hL hEven z = 0 := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [evenDiscriminantQuadraticMap_metricDualToDiscriminant]
  have hx' : (x : RationalSpan R L) ∈ rationalSpanSubmodule L P := hx
  rw [rationalizedForm_isTotallyIsotropic_span L P hP hx' hx']
  simp

omit [IsDomain R] in
/-- A member of the radical of a quadratic map: the form and its polarization vanish. -/
theorem mem_quadraticRadical_iff_polar {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N) {m : M} :
    m ∈ Q.radical ↔ Q m = 0 ∧ ∀ n, QuadraticMap.polar Q m n = 0 := by
  rw [QuadraticMap.radical]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun n => ?_⟩
    have := LinearMap.congr_fun h2 n
    rwa [QuadraticMap.polarBilin_apply_apply] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext n
    rw [QuadraticMap.polarBilin_apply_apply]
    exact h2 n

omit [IsDomain R] in
/-- The polarization of a restricted quadratic map is the polarization of the ambient one. -/
theorem polar_restrict {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N] (Q : QuadraticMap R M N)
    (W : Submodule R M) (x y : ↥W) :
    QuadraticMap.polar (Q.restrict W) x y = QuadraticMap.polar Q (x : M) (y : M) := by
  simp only [QuadraticMap.polar, QuadraticMap.restrict_apply, Submodule.coe_add]

/-- The restriction of the discriminant refinement to `D^⊥` has radical containing `D`. -/
theorem isotropicDiscriminant_le_radical (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    isotropicDiscriminantInOrthogonal L hL P ≤
      ((evenDiscriminantQuadraticMap L hL hEven).restrict
        (isotropicDiscriminantOrthogonal L hL P)).radical := by
  intro m hm
  rw [mem_quadraticRadical_iff_polar]
  constructor
  · exact evenDiscriminantQuadraticMap_eq_zero_of_mem_isotropicDiscriminant L hL hEven P hP
      hm
  · intro n
    rw [polar_restrict, evenDiscriminantQuadraticMap_polar,
      ← discriminantBilinObject_pairing]
    have hzero : (discriminantBilinObject R L hL).pairing (m : L.obj.defect)
        (n : L.obj.defect) = 0 :=
      ((discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff
        (isotropicDiscriminant L hL P) (n : L.obj.defect)).mp n.2
        (m : L.obj.defect) hm
    rw [hzero, map_zero]


/-- The descended quadratic refinement on `D^⊥/D`: the quadratic form of a subquotient inside
`A_L`; identifying it with the discriminant of `Q = P^⊥/P` is a separate theorem. -/
noncomputable def isotropicSubquotientQuadraticMap (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    QuadraticMap R
      (↥(isotropicDiscriminantOrthogonal L hL P) ⧸
        isotropicDiscriminantInOrthogonal L hL P)
      (DoubleFractionValueQuotient R) :=
  ((evenDiscriminantQuadraticMap L hL hEven).restrict
      (isotropicDiscriminantOrthogonal L hL P)).lift
    (isotropicDiscriminantInOrthogonal L hL P)
    (isotropicDiscriminant_le_radical L hL hEven P hP)

/-- The descended form on the class of a representative. -/
@[simp]
theorem isotropicSubquotientQuadraticMap_mk (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x : ↥(isotropicDiscriminantOrthogonal L hL P)) :
    isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk x) =
      evenDiscriminantQuadraticMap L hL hEven (x : L.obj.defect) :=
  rfl

/-- The descended form vanishes on the class of a metric-dual vector in `D^⊥` exactly when the
rationalized self-pairing does. -/
theorem isotropicSubquotientQuadraticMap_mk_metricDualToDiscriminant
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x : metricDual R L)
    (hx : metricDualToDiscriminant R L x ∈ isotropicDiscriminantOrthogonal L hL P) :
    isotropicSubquotientQuadraticMap L hL hEven P hP
        (Submodule.Quotient.mk ⟨metricDualToDiscriminant R L x, hx⟩) =
      doubleFractionValueProjection R
        (rationalizedForm R L (x : RationalSpan R L) (x : RationalSpan R L)) := by
  rw [isotropicSubquotientQuadraticMap_mk,
    evenDiscriminantQuadraticMap_metricDualToDiscriminant]

/-- The polarization of the descended form is the discriminant form of `L` restricted to `D^⊥`,
transported along `doubleValueMap` (the factor two of a quadratic refinement). -/
theorem isotropicSubquotientQuadraticMap_polar (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x y : ↥(isotropicDiscriminantOrthogonal L hL P)) :
    QuadraticMap.polar (isotropicSubquotientQuadraticMap L hL hEven P hP)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      doubleValueMap R
        ((discriminantBilinObject R L hL).pairing (x : L.obj.defect) (y : L.obj.defect)) := by
  rw [QuadraticMap.polar, ← Submodule.Quotient.mk_add,
    isotropicSubquotientQuadraticMap_mk, isotropicSubquotientQuadraticMap_mk,
    isotropicSubquotientQuadraticMap_mk, Submodule.coe_add, ← QuadraticMap.polar,
    evenDiscriminantQuadraticMap_polar, discriminantBilinObject_pairing]

/-- The parabolic addition formula: the descended form is quadratic with the restricted
discriminant form as its polarization, not linear. -/
theorem isotropicSubquotientQuadraticMap_add (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x y : ↥(isotropicDiscriminantOrthogonal L hL P)) :
    isotropicSubquotientQuadraticMap L hL hEven P hP
        (Submodule.Quotient.mk x + Submodule.Quotient.mk y) =
      isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk x) +
        isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk y) +
        doubleValueMap R
          ((discriminantBilinObject R L hL).pairing (x : L.obj.defect) (y : L.obj.defect)) := by
  rw [show isotropicSubquotientQuadraticMap L hL hEven P hP
        (Submodule.Quotient.mk x + Submodule.Quotient.mk y) =
      isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk x) +
        isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk y) +
        QuadraticMap.polar (isotropicSubquotientQuadraticMap L hL hEven P hP)
          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
      from QuadraticMap.map_add _ _ _,
    isotropicSubquotientQuadraticMap_polar]

/-- The quadratic module of the discriminant subquotient `D^⊥/D`. -/
noncomputable def isotropicSubquotientQuadModule (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    QuadModuleCat R (DoubleFractionValueQuotient R) :=
  QuadModuleCat.ofQuadraticMap (isotropicSubquotientQuadraticMap L hL hEven P hP)


/-- The descended form is the unique quadratic map on `D^⊥/D` inducing `q_A` on representatives:
well-definedness read as a universal property. -/
theorem isotropicSubquotientQuadraticMap_unique (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (Q' : QuadraticMap R
      (↥(isotropicDiscriminantOrthogonal L hL P) ⧸
        isotropicDiscriminantInOrthogonal L hL P)
      (DoubleFractionValueQuotient R))
    (h : ∀ x : ↥(isotropicDiscriminantOrthogonal L hL P),
      Q' (Submodule.Quotient.mk x) =
        evenDiscriminantQuadraticMap L hL hEven (x : L.obj.defect)) :
    Q' = isotropicSubquotientQuadraticMap L hL hEven P hP := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ x => rw [h x, isotropicSubquotientQuadraticMap_mk]

/-- The intrinsic discriminant subgroup of an isotropic submodule, as a quadratic-isotropic
subgroup of the even discriminant form. This is the input the overlattice/gluing constructions of
`EvenGluing` ask for; its isotropy is the vanishing of the *quadratic* refinement proved above,
not the bilinear isotropy of `DiscriminantIsotropic`. -/
noncomputable def evenDiscriminantIsotropicSubgroupOfIsotropic (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    EvenDiscriminantIsotropicSubgroup (L := L) hL hEven :=
  ⟨isotropicDiscriminant L hL P, fun _x hx =>
    evenDiscriminantQuadraticMap_eq_zero_of_mem_isotropicDiscriminant L hL hEven P hP hx⟩

/-- The bilinear shadow of the quadratic-isotropic subgroup attached to `P`: it is exactly the
intrinsic discriminant subgroup with its bilinear isotropy. -/
theorem evenDiscriminantIsotropicSubgroupOfIsotropic_toBilinear [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    (evenDiscriminantIsotropicSubgroupOfIsotropic L hL hEven P hP).toBilinear =
      ⟨isotropicDiscriminant L hL P,
        isotropicDiscriminant_isTotallyIsotropic L hL P hP⟩ :=
  Subtype.ext rfl

/-- The overlattice glued along the intrinsic discriminant subgroup: the gluing subgroup of the
overlattice obtained from `D` is `D` itself, so `D` is realised as the discriminant subgroup of a
genuine overlattice of `L` inside `L^♯`. -/
theorem evenOverlatticeFromIsotropicSubgroup_glueSubgroup [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    (evenOverlatticeFromIsotropicSubgroup hL hEven
      (evenDiscriminantIsotropicSubgroupOfIsotropic L hL hEven P hP)).glueSubgroup =
        isotropicDiscriminant L hL P :=
  glue_overlatticeFromIsotropicSubgroup hL _

/-- That overlattice is even: the quadratic vanishing on `D` is exactly what evenness of the glued
lattice requires. -/
theorem evenOverlatticeFromIsotropicSubgroup_glue_isEven [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P) :
    (evenOverlatticeFromIsotropicSubgroup hL hEven
      (evenDiscriminantIsotropicSubgroupOfIsotropic L hL hEven P hP)).IsEven :=
  evenOverlatticeFromIsotropicSubgroup_isEven hL hEven _


/-- The descended form vanishes on every class of `D`: the representative-level content of
well-definedness, read on the quotient. -/
theorem isotropicSubquotientQuadraticMap_eq_zero_of_mem (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x : ↥(isotropicDiscriminantOrthogonal L hL P))
    (hx : (x : L.obj.defect) ∈ isotropicDiscriminant L hL P) :
    isotropicSubquotientQuadraticMap L hL hEven P hP (Submodule.Quotient.mk x) = 0 := by
  rw [isotropicSubquotientQuadraticMap_mk]
  exact evenDiscriminantQuadraticMap_eq_zero_of_mem_isotropicDiscriminant L hL hEven P hP hx

/-- `D` depends only on the rational span of `P`: the intrinsic discriminant subgroup is attached
to the subspace of the rational span, not to a chosen integral generating set. -/
theorem isotropicDiscriminant_congr (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) {P P' : Submodule R L.obj.carrier}
    (h : rationalSpanSubmodule L P = rationalSpanSubmodule L P') :
    isotropicDiscriminant L hL P = isotropicDiscriminant L hL P' := by
  simp only [isotropicDiscriminant, h]

/-- Consequently the quadratic-isotropic subgroup attached to `P` is an invariant of the rational
span. -/
theorem evenDiscriminantIsotropicSubgroupOfIsotropic_congr (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    {P P' : Submodule R L.obj.carrier}
    (hP : L.obj.IsTotallyIsotropic P) (hP' : L.obj.IsTotallyIsotropic P')
    (h : rationalSpanSubmodule L P = rationalSpanSubmodule L P') :
    evenDiscriminantIsotropicSubgroupOfIsotropic L hL hEven P hP =
      evenDiscriminantIsotropicSubgroupOfIsotropic L hL hEven P' hP' :=
  Subtype.ext (isotropicDiscriminant_congr L hL h)


/-! ## The descended bilinear form and its relation to the refinement -/

/-- The discriminant bilinear form of `L` restricted to the orthogonal `D^⊥`. -/
noncomputable def isotropicDiscriminantRestrictedBilinMap (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    LinearMap.BilinMap R ↥(isotropicDiscriminantOrthogonal L hL P)
      (FractionValueQuotient R) :=
  (discriminantBilinMap R L hL).domRestrict₁₂ _ _

/-- The restricted form vanishes on a member of `D` against all of `D^⊥`. -/
theorem isotropicDiscriminantRestrictedBilinMap_left_vanishing
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (m : ↥(isotropicDiscriminantOrthogonal L hL P))
    (hm : m ∈ isotropicDiscriminantInOrthogonal L hL P) :
    isotropicDiscriminantRestrictedBilinMap L hL P m = 0 := by
  ext n
  rw [LinearMap.zero_apply]
  change discriminantBilinMap R L hL (m : L.obj.defect) (n : L.obj.defect) = 0
  rw [← discriminantBilinObject_pairing]
  exact ((discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff
    (isotropicDiscriminant L hL P) (n : L.obj.defect)).mp n.2
    (m : L.obj.defect) hm

/-- The restricted form vanishes on a member of `D` against all of `D^⊥`, on the right. -/
theorem isotropicDiscriminantRestrictedBilinMap_right_vanishing
    (L : IntegralLatticeCat R) (hL : IsFractionFieldPerfect R L)
    (P : Submodule R L.obj.carrier) (m : ↥(isotropicDiscriminantOrthogonal L hL P))
    (hm : m ∈ isotropicDiscriminantInOrthogonal L hL P) :
    (isotropicDiscriminantRestrictedBilinMap L hL P).flip m = 0 := by
  ext n
  rw [LinearMap.zero_apply]
  change discriminantBilinMap R L hL (n : L.obj.defect) (m : L.obj.defect) = 0
  rw [discriminantBilinMap_isSymmetric R L hL]
  rw [← discriminantBilinObject_pairing]
  exact ((discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff
    (isotropicDiscriminant L hL P) (n : L.obj.defect)).mp n.2
    (m : L.obj.defect) hm

/-- The discriminant bilinear form descended to `D^⊥/D`. -/
noncomputable def isotropicSubquotientBilinMap (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    LinearMap.BilinMap R
      (↥(isotropicDiscriminantOrthogonal L hL P) ⧸
        isotropicDiscriminantInOrthogonal L hL P)
      (FractionValueQuotient R) :=
  (isotropicDiscriminantRestrictedBilinMap L hL P).liftQ₂
    (isotropicDiscriminantInOrthogonal L hL P)
    (isotropicDiscriminantInOrthogonal L hL P)
    (isotropicDiscriminantRestrictedBilinMap_left_vanishing L hL P)
    (isotropicDiscriminantRestrictedBilinMap_right_vanishing L hL P)

/-- The descended bilinear form evaluated on representatives. -/
@[simp]
theorem isotropicSubquotientBilinMap_mk (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier)
    (x y : ↥(isotropicDiscriminantOrthogonal L hL P)) :
    isotropicSubquotientBilinMap L hL P (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      discriminantBilinMap R L hL (x : L.obj.defect) (y : L.obj.defect) :=
  rfl

/-- The descended discriminant form on `D^⊥/D` as a formed module. -/
noncomputable def isotropicSubquotientBilinObject (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    BilinModuleCat R (FractionValueQuotient R) :=
  BilinModuleCat.ofBilinMap (isotropicSubquotientBilinMap L hL P)

/-- The descended discriminant form is symmetric. -/
theorem isotropicSubquotientBilinMap_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier)
    (x y : ↥(isotropicDiscriminantOrthogonal L hL P) ⧸
      isotropicDiscriminantInOrthogonal L hL P) :
    isotropicSubquotientBilinMap L hL P x y =
      isotropicSubquotientBilinMap L hL P y x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      rw [isotropicSubquotientBilinMap_mk, isotropicSubquotientBilinMap_mk]
      exact discriminantBilinMap_isSymmetric R L hL _ _

/-- The descended discriminant form is symmetric, as a formed module. -/
theorem isotropicSubquotientBilinObject_isSymmetric (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier) :
    (isotropicSubquotientBilinObject L hL P).IsSymmetric := by
  intro x y
  exact isotropicSubquotientBilinMap_isSymmetric L hL P x y

/-- **Form preservation.** The polarization of the descended quadratic refinement on `D^⊥/D` is the
descended discriminant bilinear form of `L`, transported along `doubleValueMap`: the two descended
forms agree on this discriminant subquotient. -/
theorem polar_isotropicSubquotientQuadraticMap (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (P : Submodule R L.obj.carrier) (hP : L.obj.IsTotallyIsotropic P)
    (x y : ↥(isotropicDiscriminantOrthogonal L hL P)) :
    QuadraticMap.polar (isotropicSubquotientQuadraticMap L hL hEven P hP)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      doubleValueMap R (isotropicSubquotientBilinMap L hL P
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) := by
  rw [isotropicSubquotientQuadraticMap_polar, isotropicSubquotientBilinMap_mk,
    ← discriminantBilinObject_pairing]

end LeanCategories.Lattices.Valued
