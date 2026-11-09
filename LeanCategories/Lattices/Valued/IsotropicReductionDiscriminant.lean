/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PrimitiveReduction
public import LeanCategories.Lattices.Valued.IsotropicDiscriminantAction
public import LeanCategories.Lattices.Valued.ReductionDiscriminant
public import LeanCategories.Modules.Flags
public import Mathlib.LinearAlgebra.FreeModule.PID
public import LeanCategories.Lattices.Valued.DiscriminantQuotient
public import LeanCategories.Lattices.Valued.QuadraticSubquotient

@[expose] public section

namespace LeanCategories.Lattices.Valued

universe u

open LeanCategories.Modules.Bilinear.Valued
open OrthogonalGroup

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R} {r : ℕ}

-- The dual extension step for discriminant isotropy. This file does not use the zero map
-- Q → D^⊥/D on integral representatives, which is trivial in the discriminant module.
-- Instead, use a saturated complement of P^⊥ and extend functionals on P^⊥/P by zero.


/-- Orthogonal submodules are primitive over a domain: a multiple can vanish on `P^⊥` only when
the original vector was orthogonal to `P`. -/
theorem orthogonal_isPrimitive (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :
    IsPrimitiveSubmodule (L.obj.orthogonalSubmodule P) := by
  rw [isPrimitiveSubmodule_iff_saturation_le]
  intro x hx
  obtain ⟨a, ha, hax⟩ := hx
  rw [L.obj.mem_orthogonalSubmodule_iff] at hax ⊢
  intro p hp
  have h0 := hax p hp
  rw [L.obj.pairing_smul_right] at h0
  exact (smul_eq_zero.mp h0).resolve_left ha

/-- Saturation makes `P^⊥` projectively complemented in a finite free lattice over a PID. -/
theorem exists_data_complement (D : IsotropicReductionData L)
    [IsPrincipalIdealRing R] [Module.Free R L.obj.carrier] :
    ∃ C : Submodule R L.obj.carrier, D.perp ⊔ C = ⊤ ∧ D.perp ⊓ C = ⊥ := by
  let _ : Module.Finite R L.obj.carrier := D.finite
  let _ : Module.Projective R (L.obj.carrier ⧸ D.perp) :=
    Modules.saturatedProjective D.perp (orthogonal_isPrimitive L D.submodule)
  exact Modules.existsSaturatedComplement D.perp

/-- Extension of an `R`-linear functional on `P^⊥/P` to one on `L`, using a complement `C` to
`P^⊥`: zero on `C` and given by `f` on `P^⊥`. -/
noncomputable def extendDual (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reduction hN).valueDual) : L.obj.valueDual :=
  LinearMap.ofIsCompl ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
    (f.comp D.kernel.mkQ) 0

omit [IsDomain R] in
@[simp] theorem extendDual_apply_perp (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reduction hN).valueDual) (x : ↥D.perp) :
    extendDual D hN hsup hinf f (x : L.obj.carrier) =
      f (Submodule.Quotient.mk x) := by
  let h : IsCompl D.perp C := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  exact LinearMap.ofIsCompl_apply_left h (φ := f.comp D.kernel.mkQ) (ψ := 0) x

omit [IsDomain R] in
/-- The extension vanishes on the chosen complement. -/
@[simp] theorem extendDual_apply_complement (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reduction hN).valueDual) (x : ↥C) :
    extendDual D hN hsup hinf f (x : L.obj.carrier) = 0 := by
  let h : IsCompl D.perp C := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  exact LinearMap.ofIsCompl_apply_right h (φ := f.comp D.kernel.mkQ) (ψ := 0) x

/-- The dual extension, bundled as a linear map in the functional. -/
noncomputable def extendDualHom (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) :
    (D.reduction hN).valueDual →ₗ[R] L.obj.valueDual where
  toFun := extendDual D hN hsup hinf
  map_add' f g := by
    let h : IsCompl D.perp C := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
    ext z
    obtain ⟨w, c, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h z
    simp [extendDual, LinearMap.add_apply]
    rfl
  map_smul' a f := by
    let h : IsCompl D.perp C := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
    ext z
    obtain ⟨w, c, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h z
    simp [extendDual, LinearMap.smul_apply, smul_eq_mul]
    rfl

/-- The rational span of `P^⊥` is the rational orthogonal of the rational span of `P`. -/
theorem rationalSpanSubmodule_perp (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) :
    rationalSpanSubmodule L (L.obj.orthogonalSubmodule P) =
      (rationalizedForm R L).orthogonal (rationalSpanSubmodule L P) := by
  apply le_antisymm
  · rw [rationalSpanSubmodule, Submodule.span_le]
    rintro y ⟨w, hw, rfl⟩
    change ∀ z ∈ rationalSpanSubmodule L P,
      rationalizedForm R L z (toRationalSpan R L w) = 0
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ => rationalizedForm R L z (toRationalSpan R L w) = 0)
      ?_ ?_ ?_ ?_ hz
    · rintro y ⟨p, hp, rfl⟩
      rw [rational_pairing_eq L p w,
        (L.obj.mem_orthogonalSubmodule_iff P w).mp hw p hp, map_zero]
    · exact LinearMap.BilinForm.zero_left _
    · intro x y _ _ hx hy
      rw [LinearMap.BilinForm.add_left, hx, hy, add_zero]
    · intro a x _ hx
      rw [LinearMap.BilinForm.smul_left_of_tower, hx, smul_zero]
  · intro z hz
    exact mem_span_orthogonal_of_mem_orthogonal L P hz

/-- The Riesz vector of an integral functional vanishing on `P^⊥` lies in `K ⊗ P`. -/
theorem rieszEmbedding_mem_rationalSpan_of_apply_perp_eq_zero
    (D : IsotropicReductionData L) (hL : IsFractionFieldPerfect R L)
    (F : L.obj.valueDual) (hF : ∀ x : ↥D.perp, F (x : L.obj.carrier) = 0) :
    rieszEmbedding R L hL F ∈ rationalSpanSubmodule L D.submodule := by
  let _ : Module.Finite R L.obj.carrier := D.finite
  have hnondeg : (rationalizedForm R L).Nondegenerate :=
    rationalizedForm_nondegenerate_of_isNondegenerate L D.nondegenerate
  have hrefl : (rationalizedForm R L).IsRefl := by
    intro x y h
    rw [rationalizedForm_isSymmetric R L x y] at h
    exact h
  have hz : rieszEmbedding R L hL F ∈ rationalSpanSubmodule L D.submodule := by
    have hz' : rieszEmbedding R L hL F ∈ (rationalizedForm R L).orthogonal
        ((rationalizedForm R L).orthogonal (rationalSpanSubmodule L D.submodule)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      have hzspan : z ∈ rationalSpanSubmodule L D.perp :=
        mem_span_orthogonal_of_mem_orthogonal L D.submodule hz
      refine Submodule.span_induction
        (p := fun z _ => rationalizedForm R L z (rieszEmbedding R L hL F) = 0)
        ?_ ?_ ?_ ?_ hzspan
      · rintro y ⟨w, hw, rfl⟩
        rw [rationalizedForm_isSymmetric R L,
          rationalizedForm_rieszEmbedding R L hL F w, hF ⟨w, hw⟩, map_zero]
      · exact LinearMap.BilinForm.zero_left _
      · intro x y _ _ hx hy
        rw [LinearMap.BilinForm.add_left, hx, hy, add_zero]
      · intro a x _ hx
        rw [LinearMap.BilinForm.smul_left_of_tower, hx, smul_zero]
    rw [LinearMap.BilinForm.orthogonal_orthogonal hnondeg hrefl] at hz'
    exact hz'
  exact hz

/-- An integral functional vanishing on `P^⊥` has discriminant class in `D`. -/
theorem defectProjection_mem_isotropicDiscriminant_of_apply_perp_eq_zero
    (D : IsotropicReductionData L) (hL : IsFractionFieldPerfect R L)
    (F : L.obj.valueDual) (hF : ∀ x : ↥D.perp, F (x : L.obj.carrier) = 0) :
    L.obj.defectProjection F ∈ isotropicDiscriminant L hL D.submodule := by
  refine ⟨rieszToMetricDual R L hL F,
    rieszEmbedding_mem_rationalSpan_of_apply_perp_eq_zero D hL F hF, ?_⟩
  change L.obj.defectProjection
    (metricDualToValueDual R L (rieszToMetricDual R L hL F)) = L.obj.defectProjection F
  rw [metricDualToValueDual_rieszToMetricDual]

/-- Extension followed by discriminant projection, on integral functionals on `Q`. -/
noncomputable def extendDualDefectHom (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) :
    (D.reduction hN).valueDual →ₗ[R] L.obj.defect where
  toFun f := L.obj.defectProjection ((extendDualHom D hN hsup hinf) f)
  map_add' f g := by simp
  map_smul' a f := by simp

omit [IsDomain R] in
@[simp] theorem extendDualDefectHom_apply (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reduction hN).valueDual) :
    extendDualDefectHom D hN hsup hinf f =
      L.obj.defectProjection (extendDual D hN hsup hinf f) := by
  simp only [extendDualDefectHom, extendDualHom]
  rfl

/-- The discriminant class of an extended functional is orthogonal to `D`. -/
theorem extendDualDefectHom_mem_perp (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) (hL : IsFractionFieldPerfect R L)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) (f : (D.reduction hN).valueDual) :
    extendDualDefectHom D hN hsup hinf f ∈ isotropicDiscriminantPerp L hL D.submodule := by
  rw [isotropicDiscriminantPerp]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [extendDualDefectHom_apply,
    ← metricDualToValueDual_rieszToMetricDual R L hL (extendDual D hN hsup hinf f)]
  change (discriminantBilinObject R L hL).pairing
    (metricDualToDiscriminant R L y)
    (metricDualToDiscriminant R L (rieszToMetricDual R L hL
      (extendDual D hN hsup hinf f))) = 0
  rw [discriminant_pairing_metricDualToDiscriminant R hL]
  let W : Submodule (FractionRing R) (RationalSpan R L) :=
    { carrier := {w | rationalizedForm R L w
        (rieszEmbedding R L hL (extendDual D hN hsup hinf f)) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change rationalizedForm R L (a + b)
          (rieszEmbedding R L hL (extendDual D hN hsup hinf f)) = 0
        rw [LinearMap.BilinForm.add_left, ha, hb, add_zero]
      smul_mem' := by
        intro a w hw
        change rationalizedForm R L (a • w)
          (rieszEmbedding R L hL (extendDual D hN hsup hinf f)) = 0
        rw [LinearMap.BilinForm.smul_left_of_tower, hw, smul_zero] }
  have hle : rationalSpanSubmodule L D.submodule ≤ W := by
    apply Submodule.span_le.mpr
    rintro w ⟨p, hp, rfl⟩
    change rationalizedForm R L (toRationalSpan R L p)
      (rieszEmbedding R L hL (extendDual D hN hsup hinf f)) = 0
    rw [rationalizedForm_isSymmetric R L,
      rationalizedForm_rieszEmbedding R L hL]
    have hp0 : extendDual D hN hsup hinf f p = 0 := by
      rw [extendDual_apply_perp D hN hsup hinf f ⟨p, D.submodule_le_perp hp⟩]
      rw [show (Submodule.Quotient.mk
        (⟨p, D.submodule_le_perp hp⟩ : ↥D.perp) : ↥D.perp ⧸ D.kernel) = 0 from
        (Submodule.Quotient.mk_eq_zero D.kernel).mpr hp]
      exact map_zero f
    rw [hp0, map_zero]
  have hW := hle hy
  change fractionValueProjection R
    (rationalizedForm R L (metricDualInclusion R L y)
      (rieszEmbedding R L hL (extendDual D hN hsup hinf f))) = 0
  rw [hW, map_zero]

/-- The extension of a reduced adjoint differs from the ambient adjoint by a member of `D`. -/
theorem extendDual_reducedAdjoint_sub_adjoint_mem_discriminant
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥) (w : ↥D.perp) :
    L.obj.defectProjection
      (extendDual D hN hsup hinf ((D.reduction hN).adjoint (Submodule.Quotient.mk w)) -
        L.obj.adjoint (w : L.obj.carrier)) ∈ isotropicDiscriminant L hL D.submodule := by
  apply defectProjection_mem_isotropicDiscriminant_of_apply_perp_eq_zero D hL
  intro x
  simp only [LinearMap.sub_apply]
  rw [extendDual_apply_perp]
  let qx : (D.reduction hN).carrier := Submodule.Quotient.mk x
  let qw : (D.reduction hN).carrier := Submodule.Quotient.mk w
  change (D.reduction hN).adjoint qw qx - L.obj.pairing (w : L.obj.carrier) x = 0
  have hpair : (D.reduction hN).adjoint qw qx =
      L.obj.pairing (w : L.obj.carrier) (x : L.obj.carrier) := by
    rw [BilinModuleCat.bilinMap_apply]
    simpa only [qw, qx] using D.reduction_pairing_mk hN w x
  rw [hpair]
  exact sub_self _

/-- Extend on functionals, then pass from `A_Q` to `D^⊥/D`. -/
noncomputable def extendDualSubquotientHom (D : IsotropicReductionData L)
    [IsPrincipalIdealRing R] (hN : L.obj.IsSymmetric) (hL : IsFractionFieldPerfect R L)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) :
    (D.reductionLattice hN).obj.defect →ₗ[R]
      (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule) := by
  let E : (D.reductionLattice hN).obj.valueDual →ₗ[R]
      ↥(isotropicDiscriminantOrthogonal L hL D.submodule) :=
    LinearMap.codRestrict _ (extendDualDefectHom D hN hsup hinf)
      (extendDualDefectHom_mem_perp D hN hL hsup hinf)
  let Φ : (D.reductionLattice hN).obj.valueDual →ₗ[R]
      (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule) :=
    (isotropicDiscriminantInOrthogonal L hL D.submodule).mkQ.comp E
  refine Submodule.liftQ (LinearMap.range (D.reductionLattice hN).obj.adjoint) Φ ?_
  intro f hf
  obtain ⟨q, rfl⟩ := hf
  induction q using Submodule.Quotient.induction_on with
  | _ w =>
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk
      (⟨extendDualDefectHom D hN hsup hinf
        ((D.reductionLattice hN).obj.adjoint (Submodule.Quotient.mk w)),
        extendDualDefectHom_mem_perp D hN hL hsup hinf _⟩ :
          ↥(isotropicDiscriminantOrthogonal L hL D.submodule)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change extendDualDefectHom D hN hsup hinf
      ((D.reductionLattice hN).obj.adjoint (Submodule.Quotient.mk w)) ∈
        isotropicDiscriminant L hL D.submodule
    have hmem := extendDual_reducedAdjoint_sub_adjoint_mem_discriminant
      D hN hL hsup hinf w
    have heq : L.obj.defectProjection
        (extendDual D hN hsup hinf ((D.reduction hN).adjoint (Submodule.Quotient.mk w)) -
          L.obj.adjoint (w : L.obj.carrier)) =
        extendDualDefectHom D hN hsup hinf
          ((D.reductionLattice hN).obj.adjoint (Submodule.Quotient.mk w)) := by
      rw [map_sub, L.obj.exact_adjoint_defect.apply_apply_eq_zero, sub_zero]
      rfl
    exact heq ▸ hmem

/-- The representative formula for the induced map `A_Q → D^⊥/D`. -/
@[simp] theorem extendDualSubquotientHom_mk (D : IsotropicReductionData L)
    [IsPrincipalIdealRing R] (hN : L.obj.IsSymmetric) (hL : IsFractionFieldPerfect R L)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) (f : (D.reductionLattice hN).obj.valueDual) :
    extendDualSubquotientHom D hN hL hsup hinf (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk
        ⟨extendDualDefectHom D hN hsup hinf f,
          extendDualDefectHom_mem_perp D hN hL hsup hinf f⟩ := rfl

omit [IsDomain R] in
/-- Evaluation on `P` vanishes after extending a reduced functional. -/
theorem extendDual_apply_mem_isotropic (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reduction hN).valueDual) {x : L.obj.carrier} (hx : x ∈ D.submodule) :
    extendDual D hN hsup hinf f x = 0 := by
  have hxp : x ∈ D.perp := D.submodule_le_perp hx
  rw [extendDual_apply_perp D hN hsup hinf f ⟨x, hxp⟩]
  have hz : (Submodule.Quotient.mk (⟨x, hxp⟩ : ↥D.perp) :
      (D.reduction hN).carrier) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero D.kernel).mpr hx
  rw [hz]
  exact map_zero f

omit [IsDomain R] in
/-- The Riesz vector of a functional vanishing on `P` is orthogonal to `K ⊗ P`. -/
theorem rieszEmbedding_orthogonal_rationalSpan (L : IntegralLatticeCat R)
    (hL : IsFractionFieldPerfect R L) (P : Submodule R L.obj.carrier)
    {F : L.obj.valueDual} (h : ∀ x ∈ P, F x = 0) {z : RationalSpan R L}
    (hz : z ∈ rationalSpanSubmodule L P) :
    rationalizedForm R L (rieszEmbedding R L hL F) z = 0 := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      rw [rationalizedForm_rieszEmbedding R L hL F q, h q hq, map_zero]
  | zero => exact LinearMap.BilinForm.zero_right _
  | add y z _ _ hy hz => rw [LinearMap.BilinForm.add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [LinearMap.BilinForm.smul_right_of_tower, hy, smul_zero]

omit [IsDomain R] in
/-- The extension of a reduced adjoint minus the ambient adjoint vanishes on `P^⊥`. -/
theorem extendDual_reducedAdjoint_sub_adjoint_apply_perp
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) (w : ↥D.perp) (x : ↥D.perp) :
    (extendDual D hN hsup hinf ((D.reduction hN).adjoint (Submodule.Quotient.mk w)) -
      L.obj.adjoint (w : L.obj.carrier)) (x : L.obj.carrier) = 0 := by
  simp only [LinearMap.sub_apply]
  rw [extendDual_apply_perp]
  let qx : (D.reduction hN).carrier := Submodule.Quotient.mk x
  let qw : (D.reduction hN).carrier := Submodule.Quotient.mk w
  change (D.reduction hN).adjoint qw qx - L.obj.pairing (w : L.obj.carrier) x = 0
  have hpair : (D.reduction hN).adjoint qw qx =
      L.obj.pairing (w : L.obj.carrier) (x : L.obj.carrier) := by
    rw [BilinModuleCat.bilinMap_apply]
    simpa only [qw, qx] using D.reduction_pairing_mk hN w x
  rw [hpair]
  exact sub_self _

/-- In a finite perfect lattice, a nonzero multiple of any integral functional is an adjoint. -/
theorem exists_smul_adjoint (M : IntegralLatticeCat R) [Module.Finite R M.obj.carrier]
    (hM : IsFractionFieldPerfect R M) (f : M.obj.valueDual) :
    ∃ a : R, a ≠ 0 ∧ ∃ q : M.obj.carrier, a • f = M.obj.adjoint q := by
  obtain ⟨a, ha, q, hq⟩ := exists_clear_denominator M (rieszEmbedding R M hM f)
  refine ⟨a, ha, q, ?_⟩
  apply (rieszMetricDualEquiv R M hM).injective
  apply Subtype.ext
  change rieszEmbedding R M hM (a • f) = rieszEmbedding R M hM (M.obj.adjoint q)
  rw [map_smul, rieszEmbedding_adjoint]
  exact hq

/-- Raw Riesz pairing after extension, evaluated against a reduced adjoint. -/
theorem rieszDualBilinMap_extendDual_reducedAdjoint
    [IsPrincipalIdealRing R] (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f : (D.reductionLattice hN).obj.valueDual) (w : ↥D.perp) :
    rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf ((D.reductionLattice hN).obj.adjoint
          (Submodule.Quotient.mk w))) =
      rieszDualBilinMap R (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) f
        ((D.reductionLattice hN).obj.adjoint (Submodule.Quotient.mk w)) := by
  let Q := D.reductionLattice hN
  let hQ := D.reductionLattice_isFractionFieldPerfect hN
  let q : Q.obj.carrier := Submodule.Quotient.mk w
  let F := extendDual D hN hsup hinf f
  let E := extendDual D hN hsup hinf ((D.reduction hN).adjoint (Submodule.Quotient.mk w))
  have hzero : rieszDualBilinMap R L hL F (E - L.obj.adjoint (w : L.obj.carrier)) = 0 := by
    change rationalizedForm R L (rieszEmbedding R L hL F)
      (rieszEmbedding R L hL (E - L.obj.adjoint (w : L.obj.carrier))) = 0
    exact rieszEmbedding_orthogonal_rationalSpan L hL D.submodule
      (fun p hp => extendDual_apply_mem_isotropic D hN hsup hinf f hp)
      (rieszEmbedding_mem_rationalSpan_of_apply_perp_eq_zero D hL _
        (extendDual_reducedAdjoint_sub_adjoint_apply_perp D hN hsup hinf w))
  have hsum : E = L.obj.adjoint (w : L.obj.carrier) +
      (E - L.obj.adjoint (w : L.obj.carrier)) := by abel
  calc
    rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf ((D.reductionLattice hN).obj.adjoint
          (Submodule.Quotient.mk w))) =
        rieszDualBilinMap R L hL F E := rfl
    _ = rieszDualBilinMap R L hL F
        (L.obj.adjoint (w : L.obj.carrier) +
          (E - L.obj.adjoint (w : L.obj.carrier))) :=
      congrArg (fun z => rieszDualBilinMap R L hL F z) hsum
    _ = rieszDualBilinMap R L hL F (L.obj.adjoint (w : L.obj.carrier)) +
        rieszDualBilinMap R L hL F (E - L.obj.adjoint (w : L.obj.carrier)) := by
      rw [map_add]
    _ = algebraMap R (FractionRing R) (F (w : L.obj.carrier)) := by
      rw [rieszDualBilinMap_adjoint_right, hzero, add_zero]
    _ = algebraMap R (FractionRing R) (f q) := by
      change algebraMap R (FractionRing R)
        (extendDual D hN hsup hinf f (w : L.obj.carrier)) = _
      have heval : extendDual D hN hsup hinf f (w : L.obj.carrier) = f q := by
        exact extendDual_apply_perp D hN hsup hinf
          (show (D.reduction hN).valueDual from f) w
      rw [heval]
    _ = rieszDualBilinMap R Q hQ f (Q.obj.adjoint q) := by
      rw [rieszDualBilinMap_adjoint_right]

/-- Raw Riesz pairings agree after dual extension. -/
theorem rieszDualBilinMap_extendDual [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (f g : (D.reductionLattice hN).obj.valueDual) :
    rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf g) =
      rieszDualBilinMap R (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) f g := by
  let Q := D.reductionLattice hN
  let hQ := D.reductionLattice_isFractionFieldPerfect hN
  let _ : Module.Finite R Q.obj.carrier := D.reductionLattice_finite hN
  obtain ⟨a, ha, q, hq⟩ := exists_smul_adjoint Q hQ g
  induction q using Submodule.Quotient.induction_on with
  | _ w =>
    have hs₁ := congrArg (fun t : Q.obj.valueDual =>
      rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf t)) hq
    have hs₂ := congrArg (fun t : Q.obj.valueDual =>
      rieszDualBilinMap R Q hQ f t) hq
    have hext : extendDual D hN hsup hinf (a • g) =
        a • extendDual D hN hsup hinf g :=
      (extendDualHom D hN hsup hinf).map_smul a g
    rw [hext] at hs₁
    simp only [map_smul] at hs₁ hs₂
    rw [rieszDualBilinMap_extendDual_reducedAdjoint D hN hL hsup hinf f w] at hs₁
    have hscaled := hs₂.trans hs₁.symm
    have hz : a • (rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf g) - rieszDualBilinMap R Q hQ f g) = 0 := by
      calc
        a • (rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
            (extendDual D hN hsup hinf g) - rieszDualBilinMap R Q hQ f g) =
            a • rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
              (extendDual D hN hsup hinf g) - a • rieszDualBilinMap R Q hQ f g :=
          smul_sub _ _ _
        _ = 0 := sub_eq_zero.mpr hscaled.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left ha)

/-- **Bilinear form preservation.** The induced map `A_Q → D^⊥/D` is an isometry on every
pair of discriminant classes. -/
theorem extendDualSubquotientHom_pairing [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (x y : (D.reductionLattice hN).obj.defect) :
    isotropicSubquotientBilinMap L hL D.submodule
        (extendDualSubquotientHom D hN hL hsup hinf x)
        (extendDualSubquotientHom D hN hL hsup hinf y) =
      discriminantBilinMap R (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    induction y using Submodule.Quotient.induction_on with
    | _ g =>
      rw [extendDualSubquotientHom_mk, extendDualSubquotientHom_mk,
        isotropicSubquotientBilinMap_mk, discriminantBilinMap_mk]
      change fractionValueProjection R (rieszDualBilinMap R L hL
        (extendDual D hN hsup hinf f) (extendDual D hN hsup hinf g)) = _
      rw [rieszDualBilinMap_extendDual]

/-- **Quadratic-form preservation.** In the even case the same map preserves the full-norm
quadratic refinement valued in `Frac(R) / 2R`, not merely its bilinear shadow. -/
theorem extendDualSubquotientHom_quadratic [IsPrincipalIdealRing R]
    [Module.Free R L.obj.carrier] [Module.Finite R L.obj.carrier] (D : IsotropicReductionData L)
    (hN : L.obj.IsSymmetric) (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    {C : Submodule R L.obj.carrier} (hsup : D.perp ⊔ C = ⊤)
    (hinf : D.perp ⊓ C = ⊥) (x : (D.reductionLattice hN).obj.defect) :
    isotropicSubquotientQuadraticMap L hL hEven D.submodule D.isotropic
        (extendDualSubquotientHom D hN hL hsup hinf x) =
      evenDiscriminantQuadraticMap (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN)
        (D.reduction_isEven hN hEven) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    rw [extendDualSubquotientHom_mk, isotropicSubquotientQuadraticMap_mk]
    change doubleFractionValueProjection R
      (rieszDualBilinMap R L hL (extendDual D hN hsup hinf f)
        (extendDual D hN hsup hinf f)) =
      doubleFractionValueProjection R (rieszDualBilinMap R (D.reductionLattice hN)
        (D.reductionLattice_isFractionFieldPerfect hN) f f)
    rw [rieszDualBilinMap_extendDual]

/-- The comparison is injective, since it preserves the nondegenerate discriminant pairing. -/
theorem extendDualSubquotientHom_injective [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥) :
    Function.Injective (extendDualSubquotientHom D hN hL hsup hinf) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply (D.reductionDiscriminant_isNondegenerate hN).1
  intro y
  let y' : (D.reductionLattice hN).obj.defect := y
  change discriminantBilinMap R (D.reductionLattice hN)
    (D.reductionLattice_isFractionFieldPerfect hN) x y' = 0
  rw [← extendDualSubquotientHom_pairing D hN hL hsup hinf, hx, map_zero]
  rfl

/-- Two functionals agreeing on `P^⊥` have defect classes differing by an element of `D`. -/
theorem defectProjection_sub_mem_isotropicDiscriminant
    (D : IsotropicReductionData L) (hL : IsFractionFieldPerfect R L)
    {F G : L.obj.valueDual} (h : ∀ x : ↥D.perp, F (x : L.obj.carrier) = G (x : L.obj.carrier)) :
    L.obj.defectProjection F - L.obj.defectProjection G ∈
      isotropicDiscriminant L hL D.submodule := by
  rw [← map_sub]
  exact defectProjection_mem_isotropicDiscriminant_of_apply_perp_eq_zero D hL _
    (fun x => by rw [LinearMap.sub_apply, h x, sub_self])

/-- The stabilizer action on the discriminant of `Q`, as a group homomorphism. -/
noncomputable def reductionDiscriminantRepresentation [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric) : D.isotropicStabilizer →*
      BilinModuleCat.OrthogonalGroup (D.reductionDiscriminant hN) :=
  (OrthogonalGroup.discriminantRepresentation
    (D.reductionLattice_isFractionFieldPerfect hN)).comp (D.reductionIsometry hN)

/-- The kernel of the induced quotient action. -/
noncomputable abbrev reductionDiscriminantActionKernel [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric) : Subgroup D.isotropicStabilizer :=
  MonoidHom.ker (reductionDiscriminantRepresentation D hN)

/-- A stabilizing isometry as an orthogonal-group element of the packaged reduced lattice. -/
noncomputable def reductionOrthogonalAction [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric) (g : D.isotropicStabilizer) :
    OrthogonalGroup (D.reductionLattice hN) :=
  ⟨D.quotientEquiv hN g.2, D.quotientEquiv_pairing hN g.2⟩

/-- The stabilizer-equivariance identity on representatives of the extension comparison. -/
theorem actOnDefect_extendDual_sub_mem_discriminant [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (g : D.isotropicStabilizer) (f : (D.reductionLattice hN).obj.valueDual) :
    actOnDefect g.1 (extendDualDefectHom D hN hsup hinf f) -
        extendDualDefectHom D hN hsup hinf
          (actOnValueDual (reductionOrthogonalAction D hN g) f) ∈
      isotropicDiscriminant L hL D.submodule := by
  change L.obj.defectProjection (actOnValueDual g.1 (extendDual D hN hsup hinf f)) -
    L.obj.defectProjection (extendDual D hN hsup hinf
      (actOnValueDual (reductionOrthogonalAction D hN g) f)) ∈ _
  apply defectProjection_sub_mem_isotropicDiscriminant D hL
  intro x
  calc
    actOnValueDual g.1 (extendDual D hN hsup hinf f) (x : L.obj.carrier) =
        extendDual D hN hsup hinf f (D.perpEquiv (inv_mem g.2) x : L.obj.carrier) := rfl
    _ = f (Submodule.Quotient.mk (D.perpEquiv (inv_mem g.2) x)) :=
      extendDual_apply_perp D hN hsup hinf f (D.perpEquiv (inv_mem g.2) x)
    _ = actOnValueDual (reductionOrthogonalAction D hN g) f
        (Submodule.Quotient.mk x) := rfl
    _ = extendDual D hN hsup hinf
        (actOnValueDual (reductionOrthogonalAction D hN g) f) (x : L.obj.carrier) :=
      (extendDual_apply_perp D hN hsup hinf
        (actOnValueDual (reductionOrthogonalAction D hN g) f) x).symm

/-- **Stabilizer equivariance.** The natural comparison map `A_Q → D^⊥/D` commutes with the
exact-image stabilizer action, as an equality of values on every discriminant class. -/
theorem extendDualSubquotientHom_equivariant [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (g : D.isotropicStabilizer) (x : (D.reductionLattice hN).obj.defect) :
    extendDualSubquotientHom D hN hL hsup hinf
        (actOnDefect (reductionOrthogonalAction D hN g) x) =
      isotropicDiscriminantSubquotientEquiv L hL D.submodule g.1 g.2
        (extendDualSubquotientHom D hN hL hsup hinf x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f =>
    rw [actOnDefect_mk, extendDualSubquotientHom_mk, extendDualSubquotientHom_mk]
    apply (Submodule.Quotient.eq _).mpr
    have hmem := actOnDefect_extendDual_sub_mem_discriminant D hN hL hsup hinf g f
    simp only [isotropicDiscriminantInOrthogonal, actOnPerp]
    change extendDualDefectHom D hN hsup hinf
        (actOnValueDual (reductionOrthogonalAction D hN g) f) -
      actOnDefect g.1 (extendDualDefectHom D hN hsup hinf f) ∈
        isotropicDiscriminant L hL D.submodule
    rw [← neg_sub]
    exact (isotropicDiscriminant L hL D.submodule).neg_mem hmem

/-- The same commuting square, stated for the packaged stabilizer representations. -/
theorem extendDualSubquotientHom_equivariant_representation [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    (g : D.isotropicStabilizer) (x : (D.reductionLattice hN).obj.defect) :
    extendDualSubquotientHom D hN hL hsup hinf
        ((reductionDiscriminantRepresentation D hN g).1 x) =
      (isotropicDiscriminantSubquotientAction L hL D.submodule g.1 g.2).1
        (extendDualSubquotientHom D hN hL hsup hinf x) := by
  change extendDualSubquotientHom D hN hL hsup hinf
    (actOnDefect (reductionOrthogonalAction D hN g) x) = _
  exact extendDualSubquotientHom_equivariant D hN hL hsup hinf g x

/-- A proved equality of finite cardinalities promotes the canonical injection to a bijection. -/
theorem extendDualSubquotientHom_bijective_of_natCard_eq [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    [Finite (D.reductionLattice hN).obj.defect]
    [Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule)]
    (hcard : Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule)) :
    Function.Bijective (extendDualSubquotientHom D hN hL hsup hinf) := by
  exact (Nat.bijective_iff_injective_and_card
    (extendDualSubquotientHom D hN hL hsup hinf)).mpr
    ⟨extendDualSubquotientHom_injective D hN hL hsup hinf, hcard⟩

/-- The natural discriminant equivalence, once its finite carrier count is supplied by the
independent dual-quotient calculation. -/
noncomputable def extendDualDiscriminantEquivOfNatCardEq [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    [Finite (D.reductionLattice hN).obj.defect]
    [Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule)]
    (hcard : Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule)) :
    (D.reductionLattice hN).obj.defect ≃ₗ[R]
      (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule) :=
  LinearEquiv.ofBijective (extendDualSubquotientHom D hN hL hsup hinf)
    (extendDualSubquotientHom_bijective_of_natCard_eq D hN hL hsup hinf hcard)

@[simp] theorem extendDualDiscriminantEquivOfNatCardEq_apply [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    [Finite (D.reductionLattice hN).obj.defect]
    [Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule)]
    (hcard : Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule))
    (x : (D.reductionLattice hN).obj.defect) :
    extendDualDiscriminantEquivOfNatCardEq D hN hL hsup hinf hcard x =
      extendDualSubquotientHom D hN hL hsup hinf x := rfl

@[simp] theorem extendDualDiscriminantEquivOfNatCardEq_symm_apply
    [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    [Finite (D.reductionLattice hN).obj.defect]
    [Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule)]
    (hcard : Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule))
    (x : ↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule) :
    extendDualSubquotientHom D hN hL hsup hinf
      ((extendDualDiscriminantEquivOfNatCardEq D hN hL hsup hinf hcard).symm x) = x :=
  (extendDualDiscriminantEquivOfNatCardEq D hN hL hsup hinf hcard).apply_symm_apply x

/-- The two-sided inverse computed by the canonical bijection. -/
noncomputable def extendDualDiscriminantInverseOfNatCardEq [IsPrincipalIdealRing R]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    (hL : IsFractionFieldPerfect R L) {C : Submodule R L.obj.carrier}
    (hsup : D.perp ⊔ C = ⊤) (hinf : D.perp ⊓ C = ⊥)
    [Finite (D.reductionLattice hN).obj.defect]
    [Finite (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule)]
    (hcard : Nat.card (D.reductionLattice hN).obj.defect =
      Nat.card (↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
        isotropicDiscriminantInOrthogonal L hL D.submodule))
    (x : ↥(isotropicDiscriminantOrthogonal L hL D.submodule) ⧸
      isotropicDiscriminantInOrthogonal L hL D.submodule) :
    (D.reductionLattice hN).obj.defect :=
  (extendDualDiscriminantEquivOfNatCardEq D hN hL hsup hinf hcard).symm x

end LeanCategories.Lattices.Valued

