/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReductionBlocks
public import LeanCategories.Lattices.Valued.FiniteOrthogonalCount

/-!
# The level of a primitive isotropic reduction, and the unconditional discriminant isometry

The metric-dual saturation of `P` restricts to an equivalence with the dual of the complement `C`
(`complementDualEquiv`), and the level `P ⊆ L♯` is the preimage of the transpose duality block
under those coordinates (`levelMap_range_coordinates`). That gives the order of the intrinsic
isotropic discriminant `D` without any hypothesis on it:

* `natCard_isotropicDiscriminant`: `|D|` is the absolute determinant of the duality block between
  `P` and its complement;
* `natCard_extendDualSubquotients`: the reduced discriminant `A_Q` and the subquotient `D^⊥/D` have
  the same order, by the orthogonal-complement order formula and the adapted Gram determinant.

Those two counts turn the canonical comparison map `A_Q → D^⊥/D` into a linear equivalence with no
cardinality hypothesis (`extendDualDiscriminantEquiv`), and the comparison preserves the bilinear
form (`extendDualDiscriminantEquiv_pairing`), the even quadratic refinement
(`extendDualDiscriminantEquiv_quadratic`) and commutes with the exact-image stabilizer action
(`extendDualDiscriminantEquiv_equivariant`).
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

namespace ReductionBlockData

attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module

/- The saturated metric dual is a submodule of the metric dual, itself a submodule of the rational
span, so its carrier is a doubly nested subtype. Instance search for the ambient additive group
structure on that nested carrier does not find its way through the two levels on its own; the
structure of the metric dual is recorded here once, which is all the nesting needs. -/
noncomputable local instance addCommGroupMetricDual (L : IntegralLatticeCat ℤ) :
    AddCommGroup ↥(metricDual ℤ L) :=
  inferInstanceAs (AddCommGroup ↥(metricDual ℤ L))

variable {L : IntegralLatticeCat ℤ} {D : IsotropicReductionData L} {hN : L.obj.IsSymmetric}
  (B : ReductionBlockData L D hN) (hL : IsFractionFieldPerfect ℤ L)

/-- Isotropy is inherited by the whole rational span: two elements with denominators in the same
primitive isotropic submodule have zero pairing. -/
theorem rationalizedForm_zero_of_left_mem_rationalSpan {w z : RationalSpan ℤ L}
    (hw : w ∈ rationalSpanSubmodule L D.submodule)
    (hz : z ∈ rationalSpanSubmodule L D.submodule) :
    rationalizedForm ℤ L w z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      induction hw using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨q, hq, rfl⟩ := hy
          rw [rational_pairing_eq]
          have hz' := (L.obj.mem_orthogonalSubmodule_iff _ _).mp (D.submodule_le_perp hp)
          have hp' := hz' q hq
          rw [hp', map_zero]
      | zero => exact LinearMap.BilinForm.zero_left _
      | add x y hx hy ihx ihy =>
          rw [LinearMap.BilinForm.add_left, ihx, ihy, add_zero]
      | smul a x hx ih =>
          rw [LinearMap.BilinForm.smul_left, ih, mul_zero]
  | zero => exact LinearMap.BilinForm.zero_right _
  | add x y hx hy ihx ihy =>
      rw [LinearMap.BilinForm.add_right, ihx, ihy, add_zero]
  | smul a x hx ih =>
      rw [LinearMap.BilinForm.smul_right, ih, mul_zero]

/-- Restriction of a saturated metric-dual functional to the complementary submodule. -/
noncomputable def restrictComplementDual :
    ↥(isotropicDiscriminantPreimage L D.submodule) →ₗ[ℤ] (↥B.c →ₗ[ℤ] ℤ) where
  toFun w := (metricDualToValueDual ℤ L w).comp B.c.subtype
  map_add' w x := by
    ext c
    exact congrArg (fun F : L.obj.valueDual => F (c : L.obj.carrier))
      ((metricDualToValueDual ℤ L).map_add w x)
  map_smul' n w := by
    ext c
    exact congrArg (fun F : L.obj.valueDual => F (c : L.obj.carrier))
      ((metricDualToValueDual ℤ L).map_smul n w)

@[simp] theorem restrictComplementDual_apply (w : ↥(isotropicDiscriminantPreimage L D.submodule))
    (c : ↥B.c) :
    B.restrictComplementDual w c = metricDualToValueDual ℤ L w (c : L.obj.carrier) := by
  change ((metricDualToValueDual ℤ L w).comp B.c.subtype) c = _
  rfl

include hL
/-- Restriction to the complement is onto: extend a complement functional by zero on `P^⊥`. -/
theorem restrictComplementDual_surjective :
    Function.Surjective B.restrictComplementDual := by
  let h : IsCompl D.perp B.c := ⟨disjoint_iff.mpr B.c_inf, codisjoint_iff.mpr B.c_sup⟩
  intro f
  let F : L.obj.valueDual := LinearMap.ofIsCompl h 0 f
  have hFperp : ∀ x : ↥D.perp, F (x : L.obj.carrier) = 0 := by
    intro x
    exact LinearMap.ofIsCompl_apply_left h (φ := (0 : ↥D.perp →ₗ[ℤ] ℤ)) (ψ := f) x
  let w := rieszToMetricDual ℤ L hL F
  have hwspan : (w : RationalSpan ℤ L) ∈ rationalSpanSubmodule L D.submodule :=
    rieszEmbedding_mem_rationalSpan_of_apply_perp_eq_zero D hL F hFperp
  have hw : w ∈ isotropicDiscriminantPreimage L D.submodule := hwspan
  refine ⟨⟨w, hw⟩, ?_⟩
  apply LinearMap.ext
  intro c
  simp only [restrictComplementDual_apply]
  rw [metricDualToValueDual_rieszToMetricDual]
  exact LinearMap.ofIsCompl_apply_right h (φ := (0 : ↥D.perp →ₗ[ℤ] ℤ)) (ψ := f) c

omit hL in
/-- The rational span of the isotropic submodule is orthogonal to the span of its integral
orthogonal complement. -/
theorem rationalizedForm_zero_of_right_mem_rationalSpan_perp {w : RationalSpan ℤ L}
    (hw : w ∈ rationalSpanSubmodule L D.submodule) {z : L.obj.carrier} (hz : z ∈ D.perp) :
    rationalizedForm ℤ L w (toRationalSpan ℤ L z) = 0 := by
  have hz' : toRationalSpan ℤ L z ∈ (rationalizedForm ℤ L).orthogonal
      (rationalSpanSubmodule L D.submodule) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, hp, rfl⟩ := hx
        rw [rational_pairing_eq]
        have hz0 := (L.obj.mem_orthogonalSubmodule_iff _ _).mp hz p hp
        rw [hz0, map_zero]
    | zero => exact LinearMap.BilinForm.zero_left _
    | add x y hx hy ihx ihy =>
        rw [LinearMap.BilinForm.add_left, ihx, ihy, add_zero]
    | smul a x hx ih =>
        rw [LinearMap.BilinForm.smul_left_of_tower, ih, smul_zero]
  exact hz' w hw

include hL
/-- Restricting a saturated metric-dual element to the complement is injective. -/
theorem restrictComplementDual_injective :
    ∀ w₁ w₂ : ↥(isotropicDiscriminantPreimage L D.submodule),
      B.restrictComplementDual w₁ = B.restrictComplementDual w₂ → w₁ = w₂ := by
  intro w₁ w₂ hw
  apply Subtype.ext
  apply (rieszMetricDualEquiv ℤ L hL).symm.injective
  apply LinearMap.ext
  intro x
  have heval_zero (w : ↥(isotropicDiscriminantPreimage L D.submodule))
      {z : L.obj.carrier} (hz : z ∈ D.perp) :
      (rieszMetricDualEquiv ℤ L hL).symm w z = 0 := by
    change metricDualToValueDual ℤ L w z = 0
    apply (IsFractionRing.injective ℤ (FractionRing ℤ))
    calc
      algebraMap ℤ (FractionRing ℤ) (metricDualToValueDual ℤ L w z) =
          rationalizedForm ℤ L w (toRationalSpan ℤ L z) :=
        metricDualToValueDual_apply ℤ (L := L) w z
      _ = 0 := rationalizedForm_zero_of_right_mem_rationalSpan_perp w.2 hz
      _ = algebraMap ℤ (FractionRing ℤ) 0 :=
        (map_zero (algebraMap ℤ (FractionRing ℤ))).symm
  have hx : x ∈ D.perp ⊔ B.c := by rw [B.c_sup]; exact Submodule.mem_top
  obtain ⟨p, hp, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, map_add, heval_zero w₁ hp, heval_zero w₂ hp, zero_add, zero_add]
  exact congrArg (fun F : ↥B.c →ₗ[ℤ] ℤ => F ⟨c, hc⟩) hw

include hL
/-- The saturated metric dual is the full complement dual. -/
noncomputable def complementDualEquiv : ↥(isotropicDiscriminantPreimage L D.submodule) ≃ₗ[ℤ]
    (↥B.c →ₗ[ℤ] ℤ) :=
  LinearEquiv.ofBijective B.restrictComplementDual
    ⟨restrictComplementDual_injective B hL, restrictComplementDual_surjective B hL⟩

@[simp] theorem complementDualEquiv_apply
    (w : ↥(isotropicDiscriminantPreimage L D.submodule)) :
    (B.complementDualEquiv hL) w = B.restrictComplementDual w := rfl

omit hL in
/-- The integral isotropic submodule, included in its metric-dual saturation. -/
noncomputable def levelMap (D : IsotropicReductionData L) : ↥D.submodule →ₗ[ℤ]
    ↥(isotropicDiscriminantPreimage L D.submodule) where
  toFun p := ⟨toMetricDual ℤ L p, by
    change (toMetricDual ℤ L (p : L.obj.carrier) : RationalSpan ℤ L) ∈
      rationalSpanSubmodule L D.submodule
    exact Submodule.subset_span ⟨p, p.2, rfl⟩⟩
  map_add' p q := Subtype.ext ((toMetricDual ℤ L).map_add p q)
  map_smul' a p := Subtype.ext ((toMetricDual ℤ L).map_smul a p)

omit hL in
@[simp] theorem levelMap_apply (D : IsotropicReductionData L) (p : ↥D.submodule) :
    (levelMap D p : metricDual ℤ L) = toMetricDual ℤ L p := rfl

omit hL in
/-- The level injection is injective. -/
theorem levelMap_injective (D : IsotropicReductionData L) :
    Function.Injective (levelMap D) := by
  intro p q hpq
  apply Subtype.ext
  apply toMetricDual_injective ℤ L
  exact congrArg Subtype.val hpq

omit hL in
/-- The discriminant projection restricted to the saturated metric dual. -/
noncomputable def saturationToDiscriminant (D : IsotropicReductionData L) :
    ↥(isotropicDiscriminantPreimage L D.submodule) →ₗ[ℤ] L.obj.defect :=
  (metricDualToDiscriminant ℤ L).comp (isotropicDiscriminantPreimage L D.submodule).subtype

/-- Its kernel is exactly the integral isotropic line. -/
theorem saturationToDiscriminant_ker :
    LinearMap.ker (saturationToDiscriminant D) = LinearMap.range (levelMap D) := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx⟩ := (metricDualToDiscriminant_eq_zero_iff ℤ hL w).mp hw
    have hx' : (toMetricDual ℤ L x : RationalSpan ℤ L) = (w : RationalSpan ℤ L) :=
      congrArg Subtype.val hx
    change toRationalSpan ℤ L x = (w : RationalSpan ℤ L) at hx'
    have hxspan : toRationalSpan ℤ L x ∈ rationalSpanSubmodule L D.submodule := by
      rw [hx']
      exact w.2
    refine ⟨⟨x, mem_of_toRationalSpan_mem_rationalSpan L D.submodule D.primitive hxspan⟩,
      Subtype.ext hx⟩
  · rintro ⟨p, rfl⟩
    change metricDualToDiscriminant ℤ L (toMetricDual ℤ L p) = 0
    apply (metricDualToDiscriminant_eq_zero_iff ℤ hL _).mpr
    exact ⟨p, rfl⟩

/-- The saturation projects onto the intrinsic isotropic discriminant subgroup. -/
theorem saturationToDiscriminant_range :
    LinearMap.range (saturationToDiscriminant D) = isotropicDiscriminant L hL D.submodule := by
  let S := isotropicDiscriminantPreimage L D.submodule
  calc
    LinearMap.range (saturationToDiscriminant D) =
        S.subtype.range.map (metricDualToDiscriminant ℤ L) :=
      LinearMap.range_comp S.subtype (metricDualToDiscriminant ℤ L)
    _ = S.map (metricDualToDiscriminant ℤ L) := by rw [S.range_subtype]
    _ = isotropicDiscriminant L hL D.submodule :=
      (isotropicDiscriminant_eq_map_preimage L hL D.submodule).symm

/-- Evaluation of the level injection in the dual coordinates of the complement. -/
theorem complementDualEquiv_levelMap_apply (p : ↥D.submodule) (j : Fin B.r) :
    B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D p)) j =
      ∑ i, B.pBasis.equivFun p i * B.dualityMatrix.transpose j i := by
  have hcoord : ∀ q : ↥D.submodule,
      B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D q)) j =
        L.obj.pairing (q : L.obj.carrier) (B.cBasis j) := by
    intro q
    rw [Module.Basis.dualBasis_equivFun, complementDualEquiv_apply, restrictComplementDual_apply,
      levelMap_apply, metricDualToValueDual_toMetricDual ℤ hL, BilinModuleCat.bilinMap_apply]
  have key : ∀ k : Fin B.r,
      B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D (B.pBasis k))) j =
        (Matrix.mulVec B.dualityMatrix.transpose (B.pBasis.equivFun (B.pBasis k))) j := by
    intro k
    rw [hcoord, Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
    · rw [Module.Basis.equivFun_self, if_pos rfl, Matrix.transpose_apply, mul_one]
      rfl
    · intro b _ hb
      rw [Module.Basis.equivFun_self, if_neg fun h => hb h.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  let Λ : ↥D.submodule →ₗ[ℤ] ℤ :=
    (LinearMap.proj j).comp
      ((B.cBasis.dualBasis.equivFun : (↥B.c →ₗ[ℤ] ℤ) →ₗ[ℤ] (Fin B.r → ℤ)).comp
        ((B.complementDualEquiv hL :
          ↥(isotropicDiscriminantPreimage L D.submodule) →ₗ[ℤ] (↥B.c →ₗ[ℤ] ℤ)).comp
          (levelMap D)))
  let Ρ : ↥D.submodule →ₗ[ℤ] ℤ :=
    (LinearMap.proj j).comp
      ((Matrix.toLin' B.dualityMatrix.transpose).comp
        (B.pBasis.equivFun : ↥D.submodule →ₗ[ℤ] (Fin B.r → ℤ)))
  have hΛΡ : Λ = Ρ := by
    refine B.pBasis.ext fun k => ?_
    show B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D (B.pBasis k))) j
      = (Matrix.toLin' B.dualityMatrix.transpose (B.pBasis.equivFun (B.pBasis k))) j
    rw [Matrix.toLin'_apply]
    exact key k
  have hfin := LinearMap.congr_fun hΛΡ p
  rw [show Λ p = B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D p)) j
    from rfl, show Ρ p = (Matrix.mulVec B.dualityMatrix.transpose (B.pBasis.equivFun p)) j
      from rfl] at hfin
  rw [hfin, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The coordinates of the saturated metric dual in the dual basis of the complement, as an
additive homomorphism. -/
noncomputable def complementDualCoordinates (hL : IsFractionFieldPerfect ℤ L) :
    ↥(isotropicDiscriminantPreimage L D.submodule) →+ (Fin B.r → ℤ) :=
  ((B.complementDualEquiv hL).trans B.cBasis.dualBasis.equivFun).toAddEquiv.toAddMonoidHom

/-- Coordinates identify the level subgroup with the range of the transpose duality block. -/
theorem levelMap_range_coordinates :
    (LinearMap.range (levelMap D)).toAddSubgroup.map (complementDualCoordinates B hL) =
      (LinearMap.range (Matrix.toLin (Pi.basisFun ℤ (Fin B.r))
        (Pi.basisFun ℤ (Fin B.r)) B.dualityMatrix.transpose)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    refine ⟨B.pBasis.equivFun p, ?_⟩
    ext j
    change Matrix.mulVec B.dualityMatrix.transpose (B.pBasis.equivFun p) j =
      B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D p)) j
    rw [Matrix.mulVec, dotProduct]
    simpa only [mul_comm] using (B.complementDualEquiv_levelMap_apply hL p j).symm
  · rintro ⟨v, rfl⟩
    let p : ↥D.submodule := B.pBasis.equivFun.symm v
    refine ⟨levelMap D p, ⟨p, rfl⟩, ?_⟩
    ext j
    change B.cBasis.dualBasis.equivFun ((B.complementDualEquiv hL) (levelMap D p)) j =
      Matrix.mulVec B.dualityMatrix.transpose v j
    rw [Matrix.mulVec, dotProduct]
    calc
      _ = ∑ i, B.pBasis.equivFun p i * B.dualityMatrix.transpose j i :=
        B.complementDualEquiv_levelMap_apply hL p j
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hp : B.pBasis.equivFun p = v := B.pBasis.equivFun.apply_symm_apply v
        have hpi := congrFun hp i
        rw [← hpi, mul_comm]

/-- The duality block has nonzero determinant, by fraction-field perfection and the Schur
formula. -/
theorem dualityMatrix_det_ne_zero : B.dualityMatrix.det ≠ 0 := by
  have hgram : (gramMatrix L B.basis).det ≠ 0 :=
    (isFractionFieldPerfect_iff_determinant_ne_zero ℤ L B.basis).mp hL
  have hblock : B.blockGramMatrix.det ≠ 0 := by
    have hmap : ((gramMatrix L B.basis).map (Int.castRingHom ℚ)).det =
        ((gramMatrix L B.basis).det : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) _).symm
    rw [B.blockGramMatrix_eq_gramMatrix, hmap]
    exact_mod_cast hgram
  have habs : |B.blockGramMatrix.det| ≠ 0 := abs_ne_zero.mpr hblock
  rw [B.abs_det_blockGramMatrix] at habs
  have hdQ : B.dualityMatrixQ.det ≠ 0 := by
    intro hd
    apply habs
    simp [hd]
  intro hd
  apply hdQ
  have hmap : B.dualityMatrixQ.det = (B.dualityMatrix.det : ℚ) := by
    rw [dualityMatrixQ]
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  rw [hmap, hd]
  simp

omit hL in
/-- The level subgroup has the index of the transpose duality block. -/
theorem levelSubgroup_index (hL : IsFractionFieldPerfect ℤ L) :
    (LinearMap.range (levelMap D)).toAddSubgroup.index =
      (LinearMap.range (Matrix.toLin (Pi.basisFun ℤ (Fin B.r))
        (Pi.basisFun ℤ (Fin B.r)) B.dualityMatrix.transpose)).toAddSubgroup.index := by
  have he : Function.Bijective (complementDualCoordinates B hL) :=
    ((B.complementDualEquiv hL).trans B.cBasis.dualBasis.equivFun).toAddEquiv.bijective
  rw [← AddSubgroup.index_map_of_bijective he ((LinearMap.range (levelMap D)).toAddSubgroup),
    levelMap_range_coordinates (B := B) (hL := hL)]

omit hL in
/-- The isotropic discriminant subgroup has the cardinality of the level cokernel. -/
theorem natCard_isotropicDiscriminant_eq_index (hL : IsFractionFieldPerfect ℤ L) :
    Nat.card ↥(isotropicDiscriminant L hL D.submodule) =
      (LinearMap.range (levelMap D)).toAddSubgroup.index := by
  rw [← saturationToDiscriminant_ker (D := D) (hL := hL),
    ← saturationToDiscriminant_range (D := D) (hL := hL)]
  exact (AddSubgroup.index_ker (LinearMap.toAddMonoidHom (saturationToDiscriminant D))).symm

/-- **Level-cardinality theorem.** The intrinsic isotropic discriminant subgroup has order the
absolute determinant of the duality block between `P` and its complement. -/
theorem natCard_isotropicDiscriminant :
    Nat.card ↥(isotropicDiscriminant L hL D.submodule) = Int.natAbs B.dualityMatrix.det := by
  have hdet : B.dualityMatrix.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact B.dualityMatrix_det_ne_zero hL
  have hf : Function.Injective (Matrix.toLin (Pi.basisFun ℤ (Fin B.r))
      (Pi.basisFun ℤ (Fin B.r)) B.dualityMatrix.transpose) := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    simpa only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply] using hxy
  let bf : Module.Basis (Fin B.r) ℤ (LinearMap.range (Matrix.toLin (Pi.basisFun ℤ (Fin B.r))
      (Pi.basisFun ℤ (Fin B.r)) B.dualityMatrix.transpose)) :=
    (Pi.basisFun ℤ (Fin B.r)).map (LinearEquiv.ofInjective _ hf)
  have hrange := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin B.r))
    (LinearMap.range (Matrix.toLin (Pi.basisFun ℤ (Fin B.r))
      (Pi.basisFun ℤ (Fin B.r)) B.dualityMatrix.transpose)).toAddSubgroup bf
  have hdet' : (Pi.basisFun ℤ (Fin B.r)).det (fun i => (bf i : Fin B.r → ℤ)) =
      B.dualityMatrix.det := by
    calc
      (Pi.basisFun ℤ (Fin B.r)).det (fun i => (bf i : Fin B.r → ℤ)) =
          B.dualityMatrix.transpose.det := by
        rw [Module.Basis.det_apply]
        congr 1
        ext i j
        rw [Module.Basis.toMatrix_apply]
        change (Pi.basisFun ℤ (Fin B.r)).repr
          (Matrix.toLin (Pi.basisFun ℤ (Fin B.r)) (Pi.basisFun ℤ (Fin B.r))
            B.dualityMatrix.transpose (Pi.basisFun ℤ (Fin B.r) j)) i = _
        rw [← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
      _ = B.dualityMatrix.det := Matrix.det_transpose _
  rw [natCard_isotropicDiscriminant_eq_index (D := D) (hL := hL),
    levelSubgroup_index (B := B) (hL := hL), hrange, hdet']

include B
/-- The two reduced and intrinsic discriminant orders agree, by the orthogonal-complement
order formula and the adapted Gram determinant. -/
theorem natCard_extendDualSubquotients :
    Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule) := by
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Finite ℤ L.obj.carrier := D.finite
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  letI : Finite L.obj.defect := IsotropicReductionData.defect_finite L hL
  letI : Finite (discriminantBilinObject ℤ L hL).carrier :=
    inferInstanceAs (Finite L.obj.defect)
  letI : Module.Finite ℤ (D.reductionLattice hN).obj.carrier :=
    D.reductionLattice_finite hN
  have horthogonal := natCard_quotient_orthogonal_mul_sq
    (discriminantBilinObject ℤ L hL) (discriminantBilinObject_isPerfect ℤ L hL)
    (discriminantBilinObject_isSymmetric ℤ L hL) (isotropicDiscriminant L hL D.submodule)
    (isotropicDiscriminant_isTotallyIsotropic L hL D.submodule D.isotropic)
  have hlevel := B.natCard_isotropicDiscriminant hL
  have hred := natCard_defect_eq_natAbs_determinant (D.reductionLattice hN)
    (D.reductionLattice_isFractionFieldPerfect hN) B.reductionBasis
  have hlarge := natCard_defect_eq_natAbs_determinant L hL B.basis
  have hdQ : B.dualityMatrixQ.det = (B.dualityMatrix.det : ℚ) := by
    rw [dualityMatrixQ]
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  have hrQ : B.reductionGramMatrixQ.det =
      ((gramMatrix (D.reductionLattice hN) B.reductionBasis).det : ℚ) := by
    rw [reductionGramMatrixQ]
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  have hcast : ∀ n : ℤ, |((n : ℚ))| = ((n.natAbs : ℕ) : ℚ) := by
    intro n
    have h1 : |((n : ℚ))| = ((|n| : ℤ) : ℚ) := by rw [Int.cast_abs]
    have h2 : ((|n| : ℤ) : ℚ) = ((n.natAbs : ℕ) : ℚ) := by
      rw [← Int.natCast_natAbs]
      simp
    rw [h1, h2]
  have hschur : Nat.card L.obj.defect = Nat.card (D.reductionLattice hN).obj.defect *
      (Nat.card ↥(isotropicDiscriminant L hL D.submodule) *
        Nat.card ↥(isotropicDiscriminant L hL D.submodule)) := by
    have hq : (Nat.card L.obj.defect : ℚ) =
        (Nat.card (D.reductionLattice hN).obj.defect : ℚ) *
          ((Nat.card ↥(isotropicDiscriminant L hL D.submodule) : ℚ) *
            (Nat.card ↥(isotropicDiscriminant L hL D.submodule) : ℚ)) := by
      calc
        (Nat.card L.obj.defect : ℚ) = |((gramMatrix L B.basis).det : ℤ)| := by
          rw [hlarge, Nat.cast_natAbs]
          rfl
        _ = |B.blockGramMatrix.det| := by
          have hmap : ((gramMatrix L B.basis).map (Int.castRingHom ℚ)).det =
              ((gramMatrix L B.basis).det : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) _).symm
          rw [B.blockGramMatrix_eq_gramMatrix, hmap]
          exact Int.cast_abs
        _ = |B.reductionGramMatrixQ.det| *
            (|B.dualityMatrixQ.det| * |B.dualityMatrixQ.det|) := B.abs_det_blockGramMatrix
        _ = (Nat.card (D.reductionLattice hN).obj.defect : ℚ) *
            ((Nat.card ↥(isotropicDiscriminant L hL D.submodule) : ℚ) *
              (Nat.card ↥(isotropicDiscriminant L hL D.submodule) : ℚ)) := by
          rw [hdQ, hrQ]
          have hredQ : (((gramMatrix (D.reductionLattice hN) B.reductionBasis).det.natAbs : ℕ) :
                ℚ) = (Nat.card (D.reductionLattice hN).obj.defect : ℚ) := by
            exact_mod_cast hred.symm
          have hlevelQ : ((B.dualityMatrix.det.natAbs : ℕ) : ℚ) =
              (Nat.card ↥(isotropicDiscriminant L hL D.submodule) : ℚ) := by
            exact_mod_cast hlevel.symm
          calc
            |((gramMatrix (D.reductionLattice hN) B.reductionBasis).det : ℚ)| *
                (|(B.dualityMatrix.det : ℚ)| * |(B.dualityMatrix.det : ℚ)|) =
                (((gramMatrix (D.reductionLattice hN) B.reductionBasis).det.natAbs : ℕ) : ℚ) *
                  (((B.dualityMatrix.det.natAbs : ℕ) : ℚ) *
                    ((B.dualityMatrix.det.natAbs : ℕ) : ℚ)) :=
              congrArg₂ (· * ·) (hcast _) (congrArg₂ (· * ·) (hcast _) (hcast _))
            _ = _ := congrArg₂ (fun a b : ℚ => a * (b * b)) hredQ hlevelQ
    exact_mod_cast hq
  have hdpos : 0 < Nat.card ↥(isotropicDiscriminant L hL D.submodule) *
      Nat.card ↥(isotropicDiscriminant L hL D.submodule) := by
    rw [hlevel]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (B.dualityMatrix_det_ne_zero hL))
      (Int.natAbs_pos.mpr (B.dualityMatrix_det_ne_zero hL))
  change Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule) *
    Nat.card ↥(isotropicDiscriminant L hL D.submodule) ^ 2 =
      Nat.card L.obj.defect at horthogonal
  rw [pow_two] at horthogonal
  rw [hschur] at horthogonal
  exact (Nat.mul_right_cancel hdpos horthogonal).symm

end ReductionBlockData

local instance integralLattice_projective_int (L : IntegralLatticeCat ℤ) :
    Module.Projective ℤ L.obj.carrier := L.property.1

attribute [local instance 10000] Submodule.Quotient.module

/-- The intrinsic isotropic discriminant quotient is finite over `ℤ`. -/
noncomputable instance isotropicDiscriminantSubquotientFinite (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hL : IsFractionFieldPerfect ℤ L) :
    Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule) := by
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Finite ℤ L.obj.carrier := D.finite
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  letI : Finite L.obj.defect := IsotropicReductionData.defect_finite L hL
  letI : Finite (discriminantBilinObject ℤ L hL).carrier :=
    inferInstanceAs (Finite L.obj.defect)
  exact Finite.of_surjective (fun x : ↥(isotropicDiscriminantOrthogonal L hL D.submodule) =>
    (Submodule.Quotient.mk x : ↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule))
    (Submodule.mkQ_surjective _)

/-- **Unconditional natural discriminant isometry over `ℤ`.** No order hypothesis is required:
the level-cardinality theorem and the finite duality formula supply the count. -/
noncomputable def extendDualDiscriminantEquiv (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect ℤ L) {C : Submodule ℤ L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥) :
    (D.reductionLattice hN).obj.defect ≃ₗ[ℤ]
      (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule) := by
  letI : Module.Projective ℤ L.obj.carrier := L.property.1
  letI : Module.Finite ℤ L.obj.carrier := D.finite
  letI : Module.Free ℤ L.obj.carrier := inferInstance
  let B := reductionBlockData L D hN
  exact LinearEquiv.ofBijective (extendDualSubquotientHom D hN hL hsup hinf)
    (extendDualSubquotientHom_bijective_of_natCard_eq D hN hL hsup hinf
      (B.natCard_extendDualSubquotients hL))

theorem extendDualDiscriminantEquiv_apply (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect ℤ L) {C : Submodule ℤ L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (x : (D.reductionLattice hN).obj.defect) :
    extendDualDiscriminantEquiv L D hN hL hsup hinf x =
      extendDualSubquotientHom D hN hL hsup hinf x := rfl

/-- The unconditional equivalence preserves the discriminant bilinear form. -/
theorem extendDualDiscriminantEquiv_pairing (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect ℤ L) {C : Submodule ℤ L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (x y : (D.reductionLattice hN).obj.defect) :
    isotropicSubquotientBilinMap L hL D.submodule
        (extendDualDiscriminantEquiv L D hN hL hsup hinf x)
        (extendDualDiscriminantEquiv L D hN hL hsup hinf y) =
      discriminantBilinMap ℤ (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) x y :=
  extendDualSubquotientHom_pairing D hN hL hsup hinf x y

/-- The unconditional equivalence preserves the full-norm quadratic refinement in `ℚ / 2ℤ`. -/
theorem extendDualDiscriminantEquiv_quadratic (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect ℤ L) [Module.Free ℤ L.obj.carrier]
    [Module.Finite ℤ L.obj.carrier] (hEven : IsEven L)
    {C : Submodule ℤ L.obj.carrier} (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (x : (D.reductionLattice hN).obj.defect) :
    isotropicSubquotientQuadraticMap L hL hEven D.submodule D.isotropic
        (extendDualDiscriminantEquiv L D hN hL hsup hinf x) =
      evenDiscriminantQuadraticMap (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) (D.reduction_isEven hN hEven) x := by
  exact extendDualSubquotientHom_quadratic D hN hL hEven hsup hinf x

/-- The unconditional natural isometry is equivariant for the two stabilizer actions. -/
theorem extendDualDiscriminantEquiv_equivariant (L : IntegralLatticeCat ℤ)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect ℤ L) {C : Submodule ℤ L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (g : D.isotropicStabilizer) (x : (D.reductionLattice hN).obj.defect) :
    extendDualDiscriminantEquiv L D hN hL hsup hinf
        ((reductionDiscriminantRepresentation D hN g).1 x) =
      (isotropicDiscriminantSubquotientAction L hL D.submodule g.1 g.2).1
        (extendDualDiscriminantEquiv L D hN hL hsup hinf x) :=
  extendDualSubquotientHom_equivariant_representation D hN hL hsup hinf g x

end LeanCategories.Lattices.Valued
