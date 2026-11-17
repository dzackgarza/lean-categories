/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspPlaneImageIndex

/-! # The per-plane line count: the three presentations, and the two regimes

`CuspPlaneImageIndex` decided the finite-index question for `planeMatrixImage b` and stated the
corpus bound at that subgroup. What it did **not** do is identify the corpus bound's left-hand side
with the object the research page counts. This module does that, and states the infinite regime as a
theorem.

## 1. The three presentations

The count `sec-descent-flags` asks for is the number of orbits of the image
`Δ = planeStabilizerImage P` on the primitive `ℤ`-lines lying in `P` (`PlaneLines L P`). Three
presentations of that number are available, and this module proves they are one number, in a chain
of `Nat.card` equalities:

* **lines** — `MulAction.orbitRel.Quotient ↥(planeStabilizerImage P) (PlaneLines L P)`;
* **`ℚ`-points** — `MulAction.orbitRel.Quotient ↥(planeMatrixImage b) (OnePoint ℚ)`, where the
  matrix image acts on `ℙ¹(ℚ)` through its matrix in the basis `b` (`subgroupRatHom`);
* **`CuspOrbits`** — Mathlib's `CuspOrbits (gl2Image (planeMatrixImage b))`, available only under
  `[FiniteIndex (planeMatrixImage b)]`, because `CuspOrbits` is the orbit set of the *cusp set*
  `IsCusp`, and only for an arithmetic (here: finite-index) subgroup is that set `ℙ¹(ℚ)`.

`natCard_planeLineOrbits_eq_planePointOrbits` is the first link, through `planeLineEquivPoint` and
the equivariance `planeLineEquivPoint_smul`, with the group isomorphism
`planeStabilizerImageEquivMatrixImage` (the image of the stabilizer in its matrix form).
`natCard_orbitRelQuotient_eq_cuspOrbits` is the second, through `isCusp_gl2Image_iff`: the cusps of
`gl2Image Γ` are the rational points when `Γ` has finite index, because a finite-index subgroup of
`GL(2, ℤ)` is arithmetic (`gl2Image_isArithmetic`) and `isCusp_SL2Z_iff` computes the cusps of the
modular group.

## 2. The count, and its one hypothesis

`natCard_planeLineOrbits_le_index` states the bound for the object the page counts:
`Nat.card` of the `Δ`-orbits on the primitive lines is at most `(planeMatrixImage b).index`, under
`[FiniteIndex (planeMatrixImage b)]` and nothing else. That hypothesis is the *only* one, and it is
not automatic: `not_finiteIndex_of_finite_planeMatrixImage` in `CuspPlaneImageIndex` shows a plane
whose image is finite has infinite index, and the only plane in this tree whose image is computed is
the split plane of `U ⊕ U`, where the index is one (`natCard_planeLineOrbits_splitPlane_le_one`
below). A finite-index image for another plane would be a theorem about arithmetic images that the
tree does not have.

The count is a bound, not an equality, and not a coincidence of notation: the corpus lemma
`natCard_cuspOrbits_le_index_GL2` is itself a bound, because the map from cosets to cusp orbits is a
surjection and not a bijection. So the page may cite "at most `index` orbits' worth of primitive
lines", and at the split plane "at most one", which together with non-emptiness is the transitivity
the page names.

## 3. The infinite regime, as a theorem

`infinite_planeLineOrbits_of_finite_planeMatrixImage`: **if** the plane's image in `GL(2, ℤ)` is
**finite**, then the orbit set on the primitive lines of `P` is **infinite**, so the count is not a
natural number at all. The proof is two steps and neither is a remark: a finite group acting on an
infinite type has infinitely many orbits (`infinite_orbitRelQuotient_of_infinite`, from the
surjection `G × Q → X` onto the type), and `ℙ¹(ℚ)` is infinite (`infinite_onePoint_rat`).
`CuspPlaneImageIndex`'s `not_finiteIndex_of_finite_planeMatrixImage` is the index half; this is the
orbit-set half.

**This theorem is about the orbit set directly and not about `CuspOrbits`**, and that is forced.
`CuspOrbits 𝒢` is the orbit set of `cuspsSubMulAction 𝒢`, whose carrier is `{c | IsCusp c 𝒢}`, and
`IsCusp` asks for a *parabolic* element of `𝒢` fixing `c`. A finite subgroup of `GL(2, ℝ)` has no
parabolic element — a parabolic element is not a scalar matrix and every positive power of it is
parabolic, so it has infinite order (`isParabolic_not_isOfFinOrder`) — so for a finite image the
cusp set is *empty* (`isCusp_finite_gl2Image_empty`), `CuspOrbits` is the quotient of the empty set,
and its `Nat.card` is `0` (`natCard_cuspOrbits_of_finite`). Reporting that `0` as "no orbits" would
be exactly the substitution this module is written to prevent: `Nat.card` is `0` both for an empty
orbit set and for an infinite one (`Nat.card_eq_zero_of_infinite`), so the two regimes are
indistinguishable at `Nat.card` and must be separated by a statement about the orbit set itself. The
infinite-regime theorem is therefore `Infinite`, not an equation with `0`, and it carries no
`[FiniteIndex]` hypothesis, no `IsCusp`, and no `CuspOrbits`.

## 4. What the research page may cite

`sec-descent-flags` (`.tmp-sources/research-discriminant-descent-b636d06011.md`, line 125) counts
the flags `V ⊂ P` and names its own missing input: "the extra mathematical content is transitivity
of the integral plane stabilizer on the primitive lines in a fixed discriminant subgroup". The
per-plane half of that is now formal: the plane stabilizer's image has at most `index` orbits on the
primitive lines of `P` for a finite-index image, with no other hypothesis, and at most one at the
split plane of `U ⊕ U`. The discriminant refinement — the fixed-subgroup transitivity, and
`F_{J,C}` — is not in this module and is not claimed by it.

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head `9fdc1827` under
`orbit quotient equivariant bijection`, `finite group acting on infinite set finitely many orbits`,
`cusps rational points arithmetic subgroup orbit quotient` and `orbitRel quotient card congr show`.
The hits are Mathlib's own `MulAction.orbitRel.Quotient` API
(`orbitRel.Quotient.orbit_eq_orbit_out`, `MulAction.selfEquivSigmaOrbits`) and TauCeti's
`GroupTheory/DoubleCoset/Orbits.lean`, which is the double-coset dictionary already used by
`CuspSchreierImage`, not an orbit-count transport. Nothing in the corpus has the transport of an
orbit count across a `MulEquiv`-twisted bijection, nor the finite-group/infinite-orbit-set lemma,
nor the emptiness of the cusp set of a finite image, so all three are proved here. The owners used
are Mathlib's `Quotient.map_mk`, `Quotient.out_eq`, `MulAction.orbitRel_apply`,
`MulAction.mem_orbit_iff`, `Subgroup.equivMapOfInjective`, `MulEquiv.subgroupMap`,
`MulEquiv.subgroupCongr`, `Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero`,
`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`, `isCusp_SL2Z_iff`, `OnePoint.map_smul`,
`isOfFinOrder_of_finite`, `IsOfFinOrder.exists_pow_eq_one` and `Matrix.IsParabolic.pow`, and the
repository's `planeLineEquivPoint`, `planeLineEquivPoint_smul`, `planeMatrixImage`,
`planeMatrixAction`, `planeStabilizerImage`, `PlaneLines`, `sl2Part` and `sl2Part_isFiniteRelIndex`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

/-! ## Moving an orbit count across an equivariant bijection

`Nat.card` of an orbit quotient is invariant under an equivariant bijection, and this holds across a
group isomorphism as well as within one group. Both are used below: the lines/`ℚ`-points link
changes
the group (the stabilizer's image to its matrix form), and so does the `ℚ`-points/cusps link.
-/

namespace LeanCategories.ForMathlib

open MulAction

/-- **Orbit relations agree when the action commutes with a bijection.** -/
theorem orbitRel_iff_of_equiv {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (a b : X) :
    MulAction.orbitRel G X a b ↔ MulAction.orbitRel G Y (e a) (e b) := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, by rw [← he]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, e.injective (by rw [he, hg])⟩

/-- The orbit quotients of two equivariantly equivalent `G`-types. -/
noncomputable def orbitRelQuotientEquiv {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient G Y where
  toFun := Quotient.map e.toFun fun a b h => (orbitRel_iff_of_equiv e he a b).mp h
  invFun := Quotient.map e.invFun fun a b h =>
    (orbitRel_iff_of_equiv e he (e.symm a) (e.symm b)).mpr (by simpa using h)
  left_inv q := by
    induction q using Quotient.inductionOn
    simp [Quotient.map_mk]
  right_inv q := by
    induction q using Quotient.inductionOn
    simp [Quotient.map_mk]

/-- **An equivariant bijection preserves the number of orbits.** -/
theorem natCard_orbitRelQuotient_congr {G X Y : Type*} [Group G] [MulAction G X]
    [MulAction G Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Nat.card (MulAction.orbitRel.Quotient G X) = Nat.card (MulAction.orbitRel.Quotient G Y) :=
  Nat.card_congr (orbitRelQuotientEquiv e he)

/-- **Orbit relations agree when the actions are matched by a group isomorphism.** -/
theorem orbitRel_iff_of_mulEquiv {G H X Y : Type*} [Group G] [Group H] [MulAction G X]
    [MulAction H Y] (eG : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = eG g • e x) (a b : X) :
    MulAction.orbitRel G X a b ↔ MulAction.orbitRel H Y (e a) (e b) := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨eG g, by rw [← he]⟩
  · rintro ⟨h, hh⟩
    refine ⟨eG.symm h, e.injective ?_⟩
    rw [he, MulEquiv.apply_symm_apply, hh]

/-- The orbit quotients of two types whose actions are matched by a group isomorphism. -/
noncomputable def orbitRelQuotientEquivOfMulEquiv {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (eG : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = eG g • e x) :
    MulAction.orbitRel.Quotient G X ≃ MulAction.orbitRel.Quotient H Y where
  toFun := Quotient.map e.toFun fun a b h => (orbitRel_iff_of_mulEquiv eG e he a b).mp h
  invFun := Quotient.map e.invFun fun a b h =>
    (orbitRel_iff_of_mulEquiv eG e he (e.symm a) (e.symm b)).mpr (by simpa using h)
  left_inv q := by
    induction q using Quotient.inductionOn
    simp [Quotient.map_mk]
  right_inv q := by
    induction q using Quotient.inductionOn
    simp [Quotient.map_mk]

/-- **A group isomorphism matched by an equivariant bijection preserves the number of orbits.** -/
theorem natCard_orbitRelQuotient_congr_mulEquiv {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (eG : G ≃* H) (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = eG g • e x) :
    Nat.card (MulAction.orbitRel.Quotient G X) = Nat.card (MulAction.orbitRel.Quotient H Y) :=
  Nat.card_congr (orbitRelQuotientEquivOfMulEquiv eG e he)

/-- **A finite group acting on an infinite type has infinitely many orbits.** The finite union of
the finitely many orbits is the whole type, and each orbit is finite because it is the image of the
finite group. -/
theorem finite_of_finite_orbitRelQuotient {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (h : Finite (MulAction.orbitRel.Quotient G X)) : Finite X := by
  classical
  have := h
  refine Finite.of_surjective (fun p : G × MulAction.orbitRel.Quotient G X => p.1 • p.2.out) ?_
  intro x
  have hq : (⟦(Quotient.mk'' x : MulAction.orbitRel.Quotient G X).out⟧
      : MulAction.orbitRel.Quotient G X) = ⟦x⟧ := Quotient.out_eq _
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
  refine ⟨(g⁻¹, Quotient.mk'' x), ?_⟩
  dsimp only
  rw [← hg, inv_smul_smul]

/-- **The orbit set of a finite group action on an infinite type is infinite.** -/
theorem infinite_orbitRelQuotient_of_infinite {G X : Type*} [Group G] [MulAction G X]
    [Finite G] [Infinite X] : Infinite (MulAction.orbitRel.Quotient G X) :=
  Infinite.mk fun h => @Infinite.not_finite X ‹Infinite X› (finite_of_finite_orbitRelQuotient h)

end LeanCategories.ForMathlib

namespace LeanCategories.Lattices.Valued

open scoped Matrix MatrixGroups

universe u

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-! ## The matrix image acting on `ℙ¹(ℚ)` -/

/-- **A subgroup of `GL(2, ℤ)` acts on `ℙ¹(ℚ)`** by its matrices with rational coefficients. This is
the action `planeLineEquivPoint_smul` transfers the line action to, at `planeMatrixImage b`. -/
noncomputable def subgroupRatHom (Γ : Subgroup (GL (Fin 2) ℤ)) :
    ↥Γ →* GL (Fin 2) ℚ :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ)).comp Γ.subtype

noncomputable instance instMulActionSubgroupPoint (Γ : Subgroup (GL (Fin 2) ℤ)) :
    MulAction ↥Γ (OnePoint ℚ) :=
  MulAction.compHom (OnePoint ℚ) (subgroupRatHom Γ)

/-- The plane stabilizer's image, identified with its matrix image in the basis `b`. -/
noncomputable def planeStabilizerImageEquivMatrixImage
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    ↥(planeStabilizerImage P) ≃* ↥(planeMatrixImage (P := P) b) :=
  (MulEquiv.subgroupMap (planeMatrixEquiv b) (planeStabilizerImage P)).trans
    (MulEquiv.subgroupCongr rfl)

/-! ## The first link: lines are `ℚ`-points -/

/-- **The correspondence of `planeLineEquivPoint` is equivariant** for the group isomorphism taking
the plane stabilizer's image to its matrix image. This is `planeLineEquivPoint_smul` read through
`planeMatrixImageRat`. -/
theorem planeLineEquivPoint_equivariant (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) :
    planeLineEquivPoint b (δ • q) =
      planeStabilizerImageEquivMatrixImage b δ • planeLineEquivPoint b q := by
  rw [planeLineEquivPoint_smul]
  rfl

/-- **The primitive lines of `P` and the `ℚ`-points of the dual plane have the same number of
orbits**: the first presentation of the per-plane count and the second. -/
theorem natCard_planeLineOrbits_eq_planePointOrbits
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    Nat.card (MulAction.orbitRel.Quotient ↥(planeStabilizerImage P) (PlaneLines L P)) =
      Nat.card (MulAction.orbitRel.Quotient ↥(planeMatrixImage (P := P) b) (OnePoint ℚ)) :=
  LeanCategories.ForMathlib.natCard_orbitRelQuotient_congr_mulEquiv
    (planeStabilizerImageEquivMatrixImage b) (planeLineEquivPoint b)
    (planeLineEquivPoint_equivariant b)

/-- `ℙ¹(ℚ)` is infinite. -/
theorem infinite_onePoint_rat : Infinite (OnePoint ℚ) :=
  Infinite.of_injective (fun q : ℚ => OnePoint.some q) (fun _ _ h => OnePoint.coe_injective h)

/-- **The third presentation, in the infinite regime**: a finite matrix image has infinitely many
orbits on the `ℚ`-points. -/
theorem infinite_planePointOrbits_of_finite_planeMatrixImage
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (h : Finite ↥(planeMatrixImage (P := P) b)) :
    Infinite (MulAction.orbitRel.Quotient ↥(planeMatrixImage (P := P) b) (OnePoint ℚ)) :=
  @LeanCategories.ForMathlib.infinite_orbitRelQuotient_of_infinite
    ↥(planeMatrixImage (P := P) b) (OnePoint ℚ) _ _ h infinite_onePoint_rat

/-- **The infinite regime for the count the page states**: if the plane's image in `GL(2, ℤ)` is
finite, then the orbit set on the primitive lines of `P` is infinite, so there is no natural number
counting them. This is `not_finiteIndex_of_finite_planeMatrixImage`'s orbit-set half, and it is
stated about the orbit set and not about `CuspOrbits` (see the module docstring). -/
theorem infinite_planeLineOrbits_of_finite_planeMatrixImage
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (h : Finite ↥(planeMatrixImage (P := P) b)) :
    Infinite (MulAction.orbitRel.Quotient ↥(planeStabilizerImage P) (PlaneLines L P)) := by
  refine (Equiv.infinite_iff (LeanCategories.ForMathlib.orbitRelQuotientEquivOfMulEquiv
    (planeStabilizerImageEquivMatrixImage b) (planeLineEquivPoint b)
    (planeLineEquivPoint_equivariant b))).mpr ?_
  exact infinite_planePointOrbits_of_finite_planeMatrixImage b h

/-! ## The second link: `ℚ`-points are the cusps, when the index is finite

`CuspOrbits 𝒢` is the orbit set of `cuspsSubMulAction 𝒢`, whose carrier is `{c | IsCusp c 𝒢}`. For
`𝒢 = gl2Image Γ` with `Γ ≤ GL(2, ℤ)` of finite index, `𝒢` is arithmetic, its cusp set is Mathlib's
`ℙ¹(ℚ)` (`isCusp_SL2Z_iff`), and its cusp orbits are its orbits on `ℙ¹(ℚ)`. This is the only place
the finite-index hypothesis is used.
-/

end LeanCategories.Lattices.Valued

namespace LeanCategories.ForMathlib

open Matrix Matrix.SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

/-- **The image of a finite-index subgroup of `GL(2, ℤ)` in `GL(2, ℝ)` is arithmetic**: it is
commensurable with the image of its determinant-one part, which is a finite-index subgroup of
`SL(2, ℤ)`. -/
instance gl2Image_isArithmetic (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    (gl2Image Γ).IsArithmetic := by
  have hbase : Subgroup.IsArithmetic ((sl2Part Γ).map (mapGL (R := ℤ) ℝ)) := inferInstance
  refine Subgroup.IsArithmetic.mk ?_
  have hcomm : Subgroup.Commensurable ((sl2Part Γ).map (mapGL (R := ℤ) ℝ)) (gl2Image Γ) := by
    refine ⟨sl2Part_isFiniteRelIndex Γ, ?_⟩
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
      Subgroup.relIndex_eq_one.mpr (sl2Part_le_gl2Image Γ)]
    exact one_ne_zero
  exact (Subgroup.Commensurable.symm hcomm).trans hbase.is_commensurable

/-- **The cusps of the image of a finite-index subgroup are the rational points.** -/
theorem isCusp_gl2Image_iff (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] {c : OnePoint ℝ} :
    IsCusp c (gl2Image Γ) ↔ ∃ q : OnePoint ℚ, OnePoint.map (Rat.cast : ℚ → ℝ) q = c := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
  exact Set.mem_range

/-- The rational points map injectively into the real ones. -/
theorem onePointMap_rat_injective :
    Function.Injective (OnePoint.map (Rat.cast : ℚ → ℝ)) := by
  intro a b h
  cases a with
  | infty =>
    cases b with
    | infty => rfl
    | coe q => exact absurd h (by simp)
  | coe a =>
    cases b with
    | infty => exact absurd h.symm (by simp)
    | coe q => exact congrArg OnePoint.some (Rat.cast_injective (OnePoint.coe_injective h))

/-- **The rational point of a cusp**, chosen from `isCusp_gl2Image_iff`. -/
noncomputable def pointOfCusp (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (c : ↥(cuspsSubMulAction (gl2Image Γ))) : OnePoint ℚ :=
  ((isCusp_gl2Image_iff Γ).mp c.2).choose

theorem map_pointOfCusp (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (c : ↥(cuspsSubMulAction (gl2Image Γ))) :
    OnePoint.map (Rat.cast : ℚ → ℝ) (pointOfCusp Γ c) = (c : OnePoint ℝ) :=
  ((isCusp_gl2Image_iff Γ).mp c.2).choose_spec

/-- **The rational point as a cusp.** -/
noncomputable def cuspOfPoint (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] (q : OnePoint ℚ) :
    ↥(cuspsSubMulAction (gl2Image Γ)) :=
  ⟨OnePoint.map (Rat.cast : ℚ → ℝ) q, (isCusp_gl2Image_iff Γ).mpr ⟨q, rfl⟩⟩

theorem cuspOfPoint_val (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] (q : OnePoint ℚ) :
    ((cuspOfPoint Γ q : ↥(cuspsSubMulAction (gl2Image Γ))) : OnePoint ℝ) =
      OnePoint.map (Rat.cast : ℚ → ℝ) q := rfl

/-- **The cusp set of the image of a finite-index subgroup is `ℙ¹(ℚ)`.** This is the bijection
between the second presentation of the per-plane count and the third. -/
noncomputable def cuspEquivPoint (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    ↥(cuspsSubMulAction (gl2Image Γ)) ≃ OnePoint ℚ where
  toFun := pointOfCusp Γ
  invFun := cuspOfPoint Γ
  left_inv c := Subtype.ext (by rw [cuspOfPoint_val, map_pointOfCusp])
  right_inv q :=
    onePointMap_rat_injective (by rw [map_pointOfCusp]; rfl)

theorem cuspEquivPoint_apply (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (c : ↥(cuspsSubMulAction (gl2Image Γ))) : cuspEquivPoint Γ c = pointOfCusp Γ c := rfl

/-- The correspondence inverts `cuspOfPoint`. -/
theorem cuspEquivPoint_cuspOfPoint (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (q : OnePoint ℚ) : cuspEquivPoint Γ (cuspOfPoint Γ q) = q :=
  (cuspEquivPoint Γ).right_inv q

/-- The correspondence is inverted by `cuspOfPoint`. -/
theorem cuspOfPoint_cuspEquivPoint (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (c : ↥(cuspsSubMulAction (gl2Image Γ))) : cuspOfPoint Γ (cuspEquivPoint Γ c) = c :=
  (cuspEquivPoint Γ).left_inv c

/-- The finite-index subgroup, identified with its image in `GL(2, ℝ)`. -/
noncomputable def gl2ImageEquiv (Γ : Subgroup (GL (Fin 2) ℤ)) :
    ↥Γ ≃* ↥(gl2Image Γ) :=
  Subgroup.equivMapOfInjective Γ gl2ToReal gl2ToReal_injective

/-- **The action of a subgroup of `GL(2, ℤ)` on `ℙ¹(ℚ)` is the action of its image on the
corresponding cusp**: the coefficient extension `ℤ → ℚ → ℝ` does not see the difference. -/
theorem gl2ImageEquiv_smul_point (Γ : Subgroup (GL (Fin 2) ℤ)) (k : ↥Γ) (q : OnePoint ℚ) :
    OnePoint.map (Rat.cast : ℚ → ℝ) (k • q) =
      ((gl2ImageEquiv Γ k : ↥(gl2Image Γ)) : GL (Fin 2) ℝ) • OnePoint.map (Rat.cast : ℚ → ℝ) q := by
  have h := OnePoint.map_smul (algebraMap ℚ ℝ)
    (GeneralLinearGroup.map (algebraMap ℤ ℚ) (k : GL (Fin 2) ℤ)) q
  rw [show (GeneralLinearGroup.map (algebraMap ℚ ℝ))
        (GeneralLinearGroup.map (algebraMap ℤ ℚ) (k : GL (Fin 2) ℤ)) =
      GeneralLinearGroup.map ((algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ)) (k : GL (Fin 2) ℤ)
    from rfl] at h
  rw [← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] at h
  exact h

/-- The cusp of the translate is the translate of the cusp. -/
theorem gl2ImageEquiv_smul_cuspOfPoint (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (k : ↥Γ) (q : OnePoint ℚ) :
    gl2ImageEquiv Γ k • cuspOfPoint Γ q = cuspOfPoint Γ (k • q) := by
  refine Subtype.ext ?_
  exact (gl2ImageEquiv_smul_point Γ k q).symm

/-- **The cusps are the `ℚ`-points as an action**, for the group isomorphism `gl2ImageEquiv`. -/
theorem cuspEquivPoint_equivariant (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (k : ↥Γ) (c : ↥(cuspsSubMulAction (gl2Image Γ))) :
    cuspEquivPoint Γ (gl2ImageEquiv Γ k • c) = k • cuspEquivPoint Γ c := by
  conv_lhs => rw [← cuspOfPoint_cuspEquivPoint Γ c]
  rw [gl2ImageEquiv_smul_cuspOfPoint, cuspEquivPoint_cuspOfPoint]

/-- **The same, on the image side**, which is the form the transport of the orbit count consumes. -/
theorem cuspEquivPoint_equivariant' (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex]
    (g : ↥(gl2Image Γ)) (c : ↥(cuspsSubMulAction (gl2Image Γ))) :
    cuspEquivPoint Γ (g • c) = (gl2ImageEquiv Γ).symm g • cuspEquivPoint Γ c := by
  conv_lhs => rw [← MulEquiv.apply_symm_apply (gl2ImageEquiv Γ) g]
  exact cuspEquivPoint_equivariant Γ ((gl2ImageEquiv Γ).symm g) c

/-- **The `ℚ`-points and the cusp orbits count the same number of orbits**: the second presentation
of the per-plane count and the third. -/
theorem natCard_orbitRelQuotient_eq_cuspOrbits (Γ : Subgroup (GL (Fin 2) ℤ)) [Γ.FiniteIndex] :
    Nat.card (MulAction.orbitRel.Quotient ↥Γ (OnePoint ℚ)) =
      Nat.card (_root_.CuspOrbits (gl2Image Γ)) :=
  (natCard_orbitRelQuotient_congr_mulEquiv (gl2ImageEquiv Γ).symm (cuspEquivPoint Γ)
    (cuspEquivPoint_equivariant' Γ)).symm

/-! ### Why the infinite regime cannot be stated about `CuspOrbits`

A finite image has no cusp at all: a parabolic element has infinite order, every positive power of
it is parabolic, and `1` is not, so it is not of finite order in a finite group. The cusp set is
therefore empty, `CuspOrbits` is the quotient of the empty set, and its `Nat.card` is `0` — the
same value `Nat.card` gives an infinite orbit set. This is why the infinite-regime theorem above is
about the orbit set and not about `CuspOrbits`.
-/

/-- **A parabolic element has infinite order.** -/
theorem isParabolic_not_isOfFinOrder {g : GL (Fin 2) ℝ} (hg : IsParabolic g) :
    ¬ IsOfFinOrder g := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hgn⟩
  have hp := hg.pow hn.ne'
  rw [hgn] at hp
  exact hp.1 ⟨1, by simp⟩

/-- **An element of a finite subgroup has finite order.** -/
theorem isOfFinOrder_of_mem_finite {G : Type*} [Group G] {H : Subgroup G} (hH : Finite ↥H)
    {g : G} (hg : g ∈ H) : IsOfFinOrder g := by
  obtain ⟨n, hn, hgn⟩ := (@isOfFinOrder_of_finite ↥H _ hH (⟨g, hg⟩ : ↥H)).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg (fun y : ↥H => (y : G)) hgn⟩

/-- **A finite image of a subgroup of `GL(2, ℤ)` has no cusps.** -/
theorem isCusp_finite_gl2Image_empty (Γ : Subgroup (GL (Fin 2) ℤ))
    (h : Finite ↥(gl2Image Γ)) (c : OnePoint ℝ) : ¬ IsCusp c (gl2Image Γ) :=
  fun ⟨_, hg, hpar, _⟩ => isParabolic_not_isOfFinOrder hpar (isOfFinOrder_of_mem_finite h hg)

/-- **The cusp set of a finite image is empty.** -/
theorem isEmpty_cuspsSubMulAction_of_finite (Γ : Subgroup (GL (Fin 2) ℤ))
    (h : Finite ↥(gl2Image Γ)) : IsEmpty ↥(cuspsSubMulAction (gl2Image Γ)) :=
  ⟨fun c => isCusp_finite_gl2Image_empty Γ h c.1 c.2⟩

/-- **`CuspOrbits` of a finite image is the quotient of the empty set**, so its `Nat.card` is `0`.
This `0` is not a count of zero orbits: it is the empty cusp set, and the orbit set of the same
group on `ℙ¹(ℚ)` is infinite. -/
theorem natCard_cuspOrbits_of_finite (Γ : Subgroup (GL (Fin 2) ℤ))
    (h : Finite ↥(gl2Image Γ)) : Nat.card (_root_.CuspOrbits (gl2Image Γ)) = 0 := by
  have h1 : IsEmpty ↥(cuspsSubMulAction (gl2Image Γ)) := isEmpty_cuspsSubMulAction_of_finite Γ h
  have h2 : IsEmpty (_root_.CuspOrbits (gl2Image Γ)) :=
    ⟨fun q => Quotient.inductionOn q (fun c => h1.elim c)⟩
  exact @Nat.card_of_isEmpty _ h2

end LeanCategories.ForMathlib

/-! ## The count, under the one hypothesis

`[FiniteIndex (planeMatrixImage b)]` is the whole hypothesis. The two decided planes of
`CuspPlaneImageIndex` bracket it: at the split plane of `U ⊕ U` it holds with index one, and for a
plane with a finite image it fails (`not_finiteIndex_of_finite_planeMatrixImage`), where the count
is not a natural number but an infinite orbit set
(`infinite_planeLineOrbits_of_finite_planeMatrixImage`).
-/

namespace LeanCategories.Lattices.Valued

open scoped Matrix MatrixGroups

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-- **The three presentations of the per-plane count are one number.** The primitive lines of `P`,
the `ℚ`-points of the dual plane, and Mathlib's cusp orbits of the matrix image in `GL(2, ℤ)` have
the same cardinality, under the single hypothesis `[FiniteIndex (planeMatrixImage b)]` — which the
third presentation needs because `CuspOrbits` orbits the *cusp set*, and only a finite-index (hence
arithmetic) image has cusp set `ℙ¹(ℚ)`. -/
theorem natCard_planeLineOrbits_eq_natCard_cuspOrbits
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    [(planeMatrixImage (P := P) b).FiniteIndex] :
    Nat.card (MulAction.orbitRel.Quotient ↥(planeStabilizerImage P) (PlaneLines L P)) =
      Nat.card (_root_.CuspOrbits
        (LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := P) b))) :=
  (natCard_planeLineOrbits_eq_planePointOrbits b).trans
    (LeanCategories.ForMathlib.natCard_orbitRelQuotient_eq_cuspOrbits (planeMatrixImage (P := P) b))

/-- **The per-plane line count of `sec-descent-flags`.** For a plane whose stabilizer's image in
`GL(2, ℤ)` has finite index, the number of `planeStabilizerImage P`-orbits on the primitive
isotropic lines lying in `P` is at most the index of that image. This is
`natCard_cuspOrbits_le_index_GL2` carried through `planeLineEquivPoint` to the object the page
counts; it is a bound and not an equality, because the corpus lemma's coset-to-cusp-orbit map is a
surjection. -/
theorem natCard_planeLineOrbits_le_index
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    [(planeMatrixImage (P := P) b).FiniteIndex] :
    Nat.card (MulAction.orbitRel.Quotient ↥(planeStabilizerImage P) (PlaneLines L P)) ≤
      (planeMatrixImage (P := P) b).index :=
  (natCard_planeLineOrbits_eq_natCard_cuspOrbits b).trans_le
    (natCard_cuspOrbits_planeMatrixImage_le_index b)

/-- **The count at the split plane of `U ⊕ U`**: at most one orbit, because the image is all of
`GL(2, ℤ)`. Together with non-emptiness this is the transitivity of the plane stabilizer on the
primitive lines of the plane, which is the input `sec-descent-flags` names. -/
theorem natCard_planeLineOrbits_splitPlane_le_one
    (b : Module.Basis (Fin 2) ℤ ↥splitPlane.toSubmodule) :
    Nat.card (MulAction.orbitRel.Quotient ↥(planeStabilizerImage splitPlane)
      (PlaneLines twoHyperbolicPlanes splitPlane)) ≤ 1 := by
  refine (@natCard_planeLineOrbits_le_index twoHyperbolicPlanes splitPlane b
    (planeMatrixImage_splitPlane_finiteIndex b)).trans ?_
  exact le_of_eq (planeMatrixImage_splitPlane_index b)

/-- **The two regimes at one plane, side by side.** If the plane's matrix image is finite then its
`CuspOrbits` is empty — `Nat.card` is `0` because there is no cusp at all — while the orbit set on
the primitive lines of the plane is infinite
(`infinite_planeLineOrbits_of_finite_planeMatrixImage`). The `0` is therefore not a count of zero
orbits, which is why the infinite-regime theorem is about the orbit set. -/
theorem natCard_cuspOrbits_of_finite_planeMatrixImage
    (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (h : Finite ↥(planeMatrixImage (P := P) b)) :
    Nat.card (_root_.CuspOrbits
      (LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := P) b))) = 0 := by
  have h' : Finite ↥(LeanCategories.ForMathlib.gl2Image (planeMatrixImage (P := P) b)) :=
    @Finite.of_surjective _ _ h _
      (LeanCategories.ForMathlib.gl2ImageEquiv (planeMatrixImage (P := P) b)).surjective
  exact LeanCategories.ForMathlib.natCard_cuspOrbits_of_finite _ h'

end LeanCategories.Lattices.Valued
