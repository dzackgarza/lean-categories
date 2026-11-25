/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Lattices.Valued.ConicalMemberDescent
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The three open clauses of #166 on the split space of signature `(2,2)`

Red tests for the round-2 clauses of `dzackgarza/lean-categories#166`, on the smallest model that
distinguishes them: `W = ℚ⁴` with the split form `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂` of signature `(2,2)`,
the plane `J = ⟨e₀, e₂⟩` with its positive generator `r_J = e₀ ∧ e₂`, the hyperbolic plane
`⟨e₀, e₁⟩`, and the fibre `I = ⟨e₀⟩`.

* **The partner change** (clause 3): with the same generator `e₀`, the hyperbolic partner `e₁` and
  the partner `e₁ + e₂` (isotropic, pairing `1` with `e₀`) present the same cone of classes in
  `I^⊥/I`.
  `lineIpar` is the second presentation, and `partner_change_wedge` is the carrier-level statement:
  the two sheets are carried to the same element of `⋀²W(ℝ)` because they differ by the generator.
* **The orientation flip** (clause 2): `splitPlane.flip` has the positive basis `(e₂, e₀)`, so its
  positive generator is `-r_J`. `flip_not_coherent_at_lineI` says one fibre cannot present both
  orientations, and `flip_carrier_at_lineIneg` states what the flip contributes at the fibre whose
  sheet is the negative one: the antipodal ray.
* **The plane centre** (clause 1): `plane_centre` says the isotropic centre of `C_{J,+}` is the
  plane itself, and `plane_span_isotropic` records that the member's own isotropic generators span
  `J`.

The analytic side conditions of the centre (`(associated splitQ).Nondegenerate`, `sigPos` and
nondegeneracy of the fibre form) are carried as hypotheses of the example rather than computed here:
this file is about the plane and the presentations, not about the signature bookkeeping.
-/

open LeanCategories.Lattices.Valued
open QuadraticMap

namespace ConicalPlaneSplit22

/-! ## The split space of signature `(2,2)` -/

/-- The rational vector space `ℚ⁴` of the split form. -/
abbrev W := Fin 4 → ℚ

/-- The first hyperbolic basis vector. -/
def v0 : W := ![1, 0, 0, 0]

/-- The second hyperbolic basis vector: the hyperbolic partner of `v0`. -/
def v1 : W := ![0, 1, 0, 0]

/-- The third basis vector: isotropic, and the second vector of the plane `J`. -/
def v2 : W := ![0, 0, 1, 0]

/-- The fourth basis vector: the hyperbolic partner of `v2`. -/
def v3 : W := ![0, 0, 0, 1]

/-- The split form `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂` of signature `(2,2)`. -/
def splitForm : LinearMap.BilinForm ℚ W :=
  LinearMap.mk₂ ℚ (fun x y => x 0 * y 1 + x 1 * y 0 - x 2 * y 3 - x 3 * y 2)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro a x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro a x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem splitForm_apply (x y : W) :
    splitForm x y = x 0 * y 1 + x 1 * y 0 - x 2 * y 3 - x 3 * y 2 := rfl

theorem splitForm_symm : splitForm.IsSymm :=
  ⟨by intro x y; rw [splitForm_apply, splitForm_apply]; ring⟩

/-! ## The real form of the split space -/

theorem splitForm_baseChange_symm : (splitForm.baseChange ℝ).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℝ (LinearMap.BilinForm.isSymm_iff.mp splitForm_symm))

/-- The real quadratic form of the split space: the base change of `splitForm`. -/
noncomputable def splitQ : QuadraticForm ℝ (realified W) :=
  (splitForm.baseChange ℝ).toQuadraticMap

theorem splitQ_associated (u w : W) :
    (QuadraticMap.associated splitQ) (rationalPoint u) (rationalPoint w)
      = (splitForm u w : ℝ) := by
  unfold splitQ
  rw [QuadraticMap.associated_left_inverse (S := ℝ) splitForm_baseChange_symm.eq]
  simp only [rationalPoint_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
  norm_num

/-! ## The isotropic plane `J = ⟨e₀, e₂⟩` -/

/-- The rational isotropic plane `⟨e₀, e₂⟩`. -/
def J : Submodule ℚ W := Submodule.span ℚ ({v0, v2} : Set W)

theorem v0_mem_J : v0 ∈ J := Submodule.subset_span (Set.mem_insert _ _)

theorem v2_mem_J : v2 ∈ J :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The plane is totally isotropic. -/
theorem J_isotropic : ∀ x ∈ J, ∀ y ∈ J, splitForm x y = 0 := by
  intro x hx y hy
  rw [J, Submodule.mem_span_pair] at hx hy
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  simp [splitForm_apply, v0, v2]

theorem v0_ne : v0 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [v0] at this

theorem v2_ne : v2 ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [v2] at this

theorem v0_v2_li : LinearIndependent ℚ (![v0, v2] : Fin 2 → W) := by
  rw [linearIndependent_fin2]
  refine ⟨v2_ne, fun a ha => ?_⟩
  have h := congrFun ha 0
  simp [v0, v2] at h

theorem pair_li : LinearIndependent ℚ
    (![⟨v0, v0_mem_J⟩, ⟨v2, v2_mem_J⟩] : Fin 2 → ↥J) := by
  refine LinearIndependent.of_comp (Submodule.subtype J) ?_
  have h : (Submodule.subtype J) ∘ (![⟨v0, v0_mem_J⟩, ⟨v2, v2_mem_J⟩] : Fin 2 → ↥J)
      = (![v0, v2] : Fin 2 → W) := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact v0_v2_li

theorem pair_span : ⊤ ≤ Submodule.span ℚ
    (Set.range (![⟨v0, v0_mem_J⟩, ⟨v2, v2_mem_J⟩] : Fin 2 → ↥J)) := by
  intro x _
  have hx : (x : W) ∈ Submodule.span ℚ ({v0, v2} : Set W) := x.2
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨a, b, hab⟩ := hx
  have hx' : x = a • ⟨v0, v0_mem_J⟩ + b • ⟨v2, v2_mem_J⟩ := by
    refine Subtype.ext ?_
    simpa using hab.symm
  rw [hx']
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (0 : Fin 2))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (1 : Fin 2))))

/-- The positive basis of the plane: `(e₀, e₂)`, whose wedge is the positive rational generator
`r_J = e₀ ∧ e₂` of `⋀²J(ℚ)` (Example 6.3, p. 29). -/
noncomputable def planeBasis : Module.Basis (Fin 2) ℚ ↥J :=
  Module.Basis.mk pair_li pair_span

theorem planeBasis_zero : planeBasis 0 = ⟨v0, v0_mem_J⟩ := Module.Basis.mk_apply _ _ _

theorem planeBasis_one : planeBasis 1 = ⟨v2, v2_mem_J⟩ := Module.Basis.mk_apply _ _ _

theorem J_two_dim : Module.finrank ℚ ↥J = 2 := by
  rw [Module.finrank_eq_card_basis planeBasis]
  simp

/-! ## The genuine oriented plane of the split space -/

/-- **The genuine oriented isotropic plane** on the split space of signature `(2,2)`, with the
positive rational generator `r_J = e₀ ∧ e₂`. -/
noncomputable def splitPlane : ConicalPlane splitForm where
  plane := J
  isotropic := J_isotropic
  two_dim := J_two_dim
  basis := planeBasis

theorem splitPlane_dir : splitPlane.dir = v0 := by
  rw [ConicalPlane.dir, splitPlane, planeBasis_zero]

theorem splitPlane_dirAlt : splitPlane.dirAlt = v2 := by
  rw [ConicalPlane.dirAlt, splitPlane, planeBasis_one]

/-! ## The two witnessing lines of the plane -/

theorem v0_iso : splitForm v0 v0 = 0 := by rw [splitForm_apply]; simp [v0]

theorem v1_iso : splitForm v1 v1 = 0 := by rw [splitForm_apply]; simp [v1]

theorem v0_v1_pairing : splitForm v0 v1 = 1 := by rw [splitForm_apply]; simp [v0, v1]

theorem genI_iso : splitForm (v0 + v2) (v0 + v2) = 0 := by
  rw [splitForm_apply]
  simp [v0, v2]

theorem genI_v1_pairing : splitForm (v0 + v2) v1 = 1 := by
  rw [splitForm_apply]
  simp [v0, v1, v2]

/-- A line spanned by an isotropic vector is totally isotropic. -/
theorem span_iso_of (g : W) (hg : splitForm g g = 0) :
    ∀ x ∈ Submodule.span ℚ ({g} : Set W), ∀ y ∈ Submodule.span ℚ ({g} : Set W),
      splitForm x y = 0 := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hg, mul_zero]

theorem v1_ne : v1 ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [v1] at this

theorem genI_ne : v0 + v2 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [v0, v2] at this

/-- The sheet vector of the fibre of `I`: `e₂ − e₃` lies in `I^⊥/I = ⟨e₀, e₁⟩^⊥`. -/
theorem v2_sub_v3_mem_I : v2 - v3 ∈ planeComplement splitForm v0 v1 := by
  rw [mem_planeComplement_iff]
  refine ⟨?_, ?_⟩ <;> rw [splitForm_apply] <;> simp [v0, v1, v2, v3]

/-- The sheet vector of the fibre of `I'`: `e₂ − e₁ − e₃` lies in
`I'^⊥/I' = ⟨e₀ + e₂, e₁⟩^⊥`. -/
theorem v2_sub_v1_sub_v3_mem_II : v2 - v1 - v3 ∈ planeComplement splitForm (v0 + v2) v1 := by
  rw [mem_planeComplement_iff]
  refine ⟨?_, ?_⟩ <;> rw [splitForm_apply] <;> simp [v0, v1, v2, v3]

/-- The first witnessing line `I = ⟨e₀⟩`, its hyperbolic partner `e₁`, and the sheet of its fibre
given by the positive vector `e₂ − e₃` of the reduction `I^⊥/I`. -/
noncomputable def lineI : ConicalLine splitForm splitQ where
  line := Submodule.span ℚ ({v0} : Set W)
  isotropic := span_iso_of v0 v0_iso
  one_dim := finrank_span_singleton v0_ne
  gen := v0
  line_eq := rfl
  gen_iso := v0_iso
  gen_ne := v0_ne
  partner := v1
  partner_iso := v1_iso
  pairing := v0_v1_pairing
  sheet := rationalPoint ⟨v2 - v3, v2_sub_v3_mem_I⟩
  sheet_pos := by
    rw [fibreForm_rationalPoint splitQ_associated]
    have h : splitForm (v2 - v3) (v2 - v3) = 2 := by
      rw [splitForm_apply]; simp [v2, v3]; norm_num
    rw [h]
    norm_num

/-- The second witnessing line `I' = ⟨e₀ + e₂⟩` of the same plane, with the same hyperbolic
partner `e₁`, and the sheet of its fibre given by the positive vector `e₂ − e₁ − e₃`. -/
noncomputable def lineII : ConicalLine splitForm splitQ where
  line := Submodule.span ℚ ({v0 + v2} : Set W)
  isotropic := span_iso_of (v0 + v2) genI_iso
  one_dim := finrank_span_singleton genI_ne
  gen := v0 + v2
  line_eq := rfl
  gen_iso := genI_iso
  gen_ne := genI_ne
  partner := v1
  partner_iso := v1_iso
  pairing := genI_v1_pairing
  sheet := rationalPoint ⟨v2 - v1 - v3, v2_sub_v1_sub_v3_mem_II⟩
  sheet_pos := by
    rw [fibreForm_rationalPoint splitQ_associated]
    have h : splitForm (v2 - v1 - v3) (v2 - v1 - v3) = 2 := by
      rw [splitForm_apply]; simp [v1, v2, v3]; norm_num
    rw [h]
    norm_num

theorem sheet_lineI : lineI.sheet = rationalPoint ⟨v2 - v3, v2_sub_v3_mem_I⟩ := rfl

theorem sheet_lineII :
    lineII.sheet = rationalPoint ⟨v2 - v1 - v3, v2_sub_v1_sub_v3_mem_II⟩ := rfl

theorem lineI_le : lineI.line ≤ splitPlane.plane := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact v0_mem_J

theorem lineII_le : lineII.line ≤ splitPlane.plane := by
  refine Submodule.span_le.2 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact Submodule.add_mem _ v0_mem_J v2_mem_J

/-! ## The correctly oriented ray of the plane in each fibre -/

theorem planeRay_lineI : lineI.planeRay splitPlane lineI_le = v2 := by
  have hb : (⟨lineI.gen, lineI.gen_mem_of_le splitPlane lineI_le⟩ : ↥splitPlane.plane)
      = splitPlane.basis 0 := Subtype.ext (by
    change lineI.gen = (splitPlane.basis 0 : W)
    rw [← ConicalPlane.dir, splitPlane_dir]
    rfl)
  have hcoord : splitPlane.basis.repr
      ⟨lineI.gen, lineI.gen_mem_of_le splitPlane lineI_le⟩ 0 = 1 := by
    rw [hb, splitPlane.basis.repr_self]
    simp
  rw [ConicalLine.planeRay,
    ConicalPlane.rayOf_eq_smul_dirAlt _ (lineI.gen_mem_of_le splitPlane lineI_le) lineI.gen_ne
      (by rw [hcoord]; norm_num),
    splitPlane_dirAlt, hcoord, inv_one, one_smul]

theorem planeRay_lineII : lineII.planeRay splitPlane lineII_le = v2 := by
  have hb : (⟨lineII.gen, lineII.gen_mem_of_le splitPlane lineII_le⟩ : ↥splitPlane.plane)
      = splitPlane.basis 0 + splitPlane.basis 1 := Subtype.ext (by
    change lineII.gen = ((splitPlane.basis 0 : ↥splitPlane.plane) : W) +
      ((splitPlane.basis 1 : ↥splitPlane.plane) : W)
    rw [← ConicalPlane.dir, ← ConicalPlane.dirAlt, splitPlane_dir, splitPlane_dirAlt]
    rfl)
  have hcoord : splitPlane.basis.repr
      ⟨lineII.gen, lineII.gen_mem_of_le splitPlane lineII_le⟩ 0 = 1 := by
    rw [hb, map_add, splitPlane.basis.repr_self, splitPlane.basis.repr_self]
    simp
  rw [ConicalLine.planeRay,
    ConicalPlane.rayOf_eq_smul_dirAlt _ (lineII.gen_mem_of_le splitPlane lineII_le) lineII.gen_ne
      (by rw [hcoord]; norm_num),
    splitPlane_dirAlt, hcoord, inv_one, one_smul]

theorem fibreRayProj_lineI :
    ((fibreRayProj splitForm_symm lineI splitPlane lineI_le : ↥lineI.space) : W) = v2 := by
  rw [fibreRayProj_val, planeRay_lineI]
  have h : splitForm v2 lineI.partner = 0 := by
    change splitForm v2 v1 = 0
    rw [splitForm_apply]; simp [v1, v2]
  rw [h, zero_smul, sub_zero]

theorem fibreRayProj_lineII :
    ((fibreRayProj splitForm_symm lineII splitPlane lineII_le : ↥lineII.space) : W) = v2 := by
  rw [fibreRayProj_val, planeRay_lineII]
  have h : splitForm v2 lineII.partner = 0 := by
    change splitForm v2 v1 = 0
    rw [splitForm_apply]; simp [v1, v2]
  rw [h, zero_smul, sub_zero]

/-- **The oriented ray is not the opposite one**: in the fibre of `I` the class of `r_J` pairs
strictly positively with the sheet of the fibre's cone (`C_J ⊆ ∂C_I`, §1B, p. 11). -/
theorem sheet_pairing_lineI :
    0 < (associated (fibreForm splitQ lineI.space))
      (rationalPoint (fibreRayProj splitForm_symm lineI splitPlane lineI_le)) lineI.sheet := by
  rw [associated_fibreForm, realifyMap_rationalPoint, sheet_lineI, realifyMap_rationalPoint,
    fibreRayProj_lineI, splitQ_associated]
  have h : splitForm v2 (v2 - v3) = 1 := by rw [splitForm_apply]; simp [v2, v3]
  rw [h]
  norm_num

theorem sheet_pairing_lineII :
    0 < (associated (fibreForm splitQ lineII.space))
      (rationalPoint (fibreRayProj splitForm_symm lineII splitPlane lineII_le)) lineII.sheet := by
  rw [associated_fibreForm, realifyMap_rationalPoint, sheet_lineII, realifyMap_rationalPoint,
    fibreRayProj_lineII, splitQ_associated]
  have h : splitForm v2 (v2 - v1 - v3) = 1 := by
    rw [splitForm_apply]; simp [v1, v2, v3]
  rw [h]
  norm_num

theorem fibreRay_lineI :
    fibreRay splitForm_symm lineI splitPlane lineI_le
      = fibreRayProj splitForm_symm lineI splitPlane lineI_le :=
  fibreRay_eq_fibreRayProj_of_nonneg splitForm_symm lineI splitPlane lineI_le
    (le_of_lt sheet_pairing_lineI)

theorem fibreRay_lineII :
    fibreRay splitForm_symm lineII splitPlane lineII_le
      = fibreRayProj splitForm_symm lineII splitPlane lineII_le :=
  fibreRay_eq_fibreRayProj_of_nonneg splitForm_symm lineII splitPlane lineII_le
    (le_of_lt sheet_pairing_lineII)

theorem fibreRay_isotropic_lineI :
    (fibreForm splitQ lineI.space)
      (rationalPoint (fibreRay splitForm_symm lineI splitPlane lineI_le)) = 0 :=
  fibreRay_isotropic splitQ_associated splitForm_symm lineI splitPlane lineI_le

theorem fibreRay_isotropic_lineII :
    (fibreForm splitQ lineII.space)
      (rationalPoint (fibreRay splitForm_symm lineII splitPlane lineII_le)) = 0 :=
  fibreRay_isotropic splitQ_associated splitForm_symm lineII splitPlane lineII_le

theorem fibreRay_ne_zero_lineI :
    fibreRay splitForm_symm lineI splitPlane lineI_le ≠ 0 :=
  fibreRay_ne_zero splitForm_symm lineI splitPlane lineI_le

theorem fibreRay_ne_zero_lineII :
    fibreRay splitForm_symm lineII splitPlane lineII_le ≠ 0 :=
  fibreRay_ne_zero splitForm_symm lineII splitPlane lineII_le

/-! ## The carrier of a plane member in `⋀²V(ℝ)`

Definition 2.1, p. 10, puts the conical locus in `so(φ)(ℝ) ≅ ⋀²V(ℝ)`, and
`ConicalMember.carrier` is the image of a member there. The carrier of a plane member at a
witnessing line is the image of its half line `fibreRay` under `e ⊗ c ↦ e ∧ c`.

The half line is *sign-sensitive*: `fibreRay` chooses the sign of the class of the plane's ray by
pairing it with the sheet of the line's cone. The sheet of a `ConicalLine` and the orientation of a
`ConicalPlane` are independent data, so the source's `C_J ⊂ ∂C_I` (§1B, p. 11) is a condition on the
pair — `ConicalPlane.IsPositiveAt`, which `ConicalMember.plane` requires. This section checks the
condition at the two witnessing lines of the split plane, computes the carrier at each, and records
what the *other* sheet would have contributed: the antipodal ray. -/

theorem R_ne_zero : wedgeTwo (rationalPoint v0) (rationalPoint v2) ≠ 0 := by
  have h := wedgeTwo_dir_ne_zero splitPlane
  rw [splitPlane_dir, splitPlane_dirAlt] at h
  exact h

/-! ## `lineI` with its sheet negated: the same line, the other cone -/

/-- **`lineI` with its sheet negated.** It has the same line, generator and hyperbolic partner, and
its sheet is `-sheet`; it is a `ConicalLine` because the fibre form is even, `Q (-s) = Q s`, so the
negated sheet is again a positive vector of the same reduction `I^⊥/I`. This is a legitimate piece
of source data — the other cone `C_I` of the same fibre — and it is *not* a presentation of the
half line `C_J` of the plane `splitPlane` whose sheet `lineI` is. -/
noncomputable abbrev lineIneg : ConicalLine splitForm splitQ where
  line := lineI.line
  isotropic := lineI.isotropic
  one_dim := lineI.one_dim
  gen := lineI.gen
  line_eq := lineI.line_eq
  gen_iso := lineI.gen_iso
  gen_ne := lineI.gen_ne
  partner := lineI.partner
  partner_iso := lineI.partner_iso
  pairing := lineI.pairing
  sheet := -lineI.sheet
  sheet_pos := by
    have h : fibreForm splitQ (planeComplement splitForm lineI.gen lineI.partner) (-lineI.sheet) =
        fibreForm splitQ (planeComplement splitForm lineI.gen lineI.partner) lineI.sheet := by
      simp only [fibreForm, QuadraticMap.comp_apply, QuadraticMap.map_neg]
    rw [h]
    exact lineI.sheet_pos

theorem sheet_lineIneg : lineIneg.sheet = -lineI.sheet := rfl

theorem lineIneg_le : lineIneg.line ≤ splitPlane.plane := lineI_le

/-- The two lines are the same line: the negation of the sheet does not change the isotropic line,
only the choice of its cone `C_I`. -/
theorem lineIneg_line : lineIneg.line = lineI.line := rfl

/-- `rayOf` depends on the membership proof only propositionally, so the ray of the plane at
`lineIneg` is the ray at `lineI`: the ray is computed from the line and the plane's orientation, and
neither has changed. -/
theorem planeRay_lineIneg : lineIneg.planeRay splitPlane lineIneg_le = v2 := by
  have h : lineIneg.planeRay splitPlane lineIneg_le =
      lineI.planeRay splitPlane lineI_le := by
    simp only [ConicalLine.planeRay]
  rw [h, planeRay_lineI]

/-- The plane's ray in the fibre is the same vector: it is computed from the line's generator and
the plane's orientation, and neither has changed. -/
theorem fibreRayProj_lineIneg :
    ((fibreRayProj splitForm_symm lineIneg splitPlane lineIneg_le : ↥lineIneg.space) : W)
      = v2 := by
  rw [fibreRayProj_val]
  have h : splitForm v2 lineIneg.partner = 0 := by
    change splitForm v2 v1 = 0
    rw [splitForm_apply]; simp [v1, v2]
  rw [planeRay_lineIneg, h, zero_smul, sub_zero]

/-- The class of the plane's ray pairs *negatively* with the negated sheet: the sign is reversed,
since the fibre form is linear in its second argument. -/
theorem sheet_pairing_lineIneg :
    (associated (fibreForm splitQ lineIneg.space))
      (rationalPoint (fibreRayProj splitForm_symm lineIneg splitPlane lineIneg_le))
        lineIneg.sheet < 0 := by
  rw [associated_fibreForm, realifyMap_rationalPoint, sheet_lineIneg, map_neg, sheet_lineI,
    realifyMap_rationalPoint, fibreRayProj_lineIneg, map_neg, splitQ_associated]
  have h : splitForm v2 (v2 - v3) = 1 := by rw [splitForm_apply]; simp [v2, v3]
  rw [h]
  norm_num

/-- **The half line of the negated sheet is the opposite class.** -/
theorem fibreRay_lineIneg :
    fibreRay splitForm_symm lineIneg splitPlane lineIneg_le
      = - fibreRayProj splitForm_symm lineIneg splitPlane lineIneg_le :=
  fibreRay_eq_neg_of_pairing_neg splitForm_symm lineIneg splitPlane lineIneg_le
    sheet_pairing_lineIneg

/-! ## The coherence of each sheet with the plane's orientation -/

/-- The sheet of `lineI` is coherent with the orientation of `splitPlane`: the plane's ray pairs
positively with it, `C_J ⊂ ∂C_I` (§1B, p. 11). -/
theorem isPositiveAt_lineI : splitPlane.IsPositiveAt lineI lineI_le :=
  (fibreRayProj_sheet_pos_iff splitForm_symm lineI splitPlane lineI_le).mp sheet_pairing_lineI

/-- The same for the second witnessing line `I' = ⟨e₀ + e₂⟩`. -/
theorem isPositiveAt_lineII : splitPlane.IsPositiveAt lineII lineII_le :=
  (fibreRayProj_sheet_pos_iff splitForm_symm lineII splitPlane lineII_le).mp sheet_pairing_lineII

/-- **The negated sheet is *not* coherent with the same oriented plane**: it pairs negatively with
the plane's ray, so the plane does not present through it. This is the repair: `ConicalMember.plane`
takes the coherence as data, and the two sheets of one fibre are not interchangeable presentations
of the plane. -/
theorem not_isPositiveAt_lineIneg : ¬ splitPlane.IsPositiveAt lineIneg lineIneg_le := by
  intro h
  have hpos := (fibreRayProj_sheet_pos_iff splitForm_symm lineIneg splitPlane lineIneg_le).mpr h
  linarith [sheet_pairing_lineIneg]

/-! ## Clause 3: the partner change at the carrier -/

/-- `e₁ + e₂` is an isotropic partner of `e₀`: `e₂` is isotropic and orthogonal to `e₁`. -/
theorem v1_add_v2_iso : splitForm (v1 + v2) (v1 + v2) = 0 := by
  rw [splitForm_apply]
  simp [v1, v2]

theorem v0_v1v2_pairing : splitForm v0 (v1 + v2) = 1 := by
  rw [splitForm_apply]
  simp [v0, v1, v2]

/-- The sheet of the second presentation: `e₂ − e₀ − e₃` lies in `I^⊥` and is orthogonal to the new
partner `e₁ + e₂`, so it is a vector of the reduction `I^⊥/I` carried by that complement. -/
theorem v2_sub_v0_sub_v3_mem_Ipar : v2 - v0 - v3 ∈ planeComplement splitForm v0 (v1 + v2) := by
  rw [mem_planeComplement_iff]
  refine ⟨?_, ?_⟩ <;> rw [splitForm_apply] <;> simp [v0, v1, v2, v3]

/-- **The same oriented fibre at a different partner**: the same line, the same generator `e₀`, and
the hyperbolic partner `e₁ + e₂` in place of `e₁`. Its sheet `e₂ − e₀ − e₃` presents the class of
`e₂ − e₃` in `I^⊥/I`: the two differ by the generator. -/
noncomputable def lineIpar : ConicalLine splitForm splitQ where
  line := Submodule.span ℚ ({v0} : Set W)
  isotropic := span_iso_of v0 v0_iso
  one_dim := finrank_span_singleton v0_ne
  gen := v0
  line_eq := rfl
  gen_iso := v0_iso
  gen_ne := v0_ne
  partner := v1 + v2
  partner_iso := v1_add_v2_iso
  pairing := v0_v1v2_pairing
  sheet := rationalPoint ⟨v2 - v0 - v3, v2_sub_v0_sub_v3_mem_Ipar⟩
  sheet_pos := by
    rw [fibreForm_rationalPoint splitQ_associated]
    have h : splitForm (v2 - v0 - v3) (v2 - v0 - v3) = 2 := by
      rw [splitForm_apply]; simp [v0, v2, v3]; norm_num
    rw [h]
    norm_num

/-- The two presentations have the same generator, so the same line. -/
theorem lineIpar_gen : lineIpar.gen = lineI.gen := rfl

/-- **The two sheets differ by the generator**, so they present the same class in `I^⊥/I`. -/
theorem sheet_diff_mem_lineSpan :
    rationalPoint ((⟨v2 - v0 - v3, v2_sub_v0_sub_v3_mem_Ipar⟩ : ↥lineIpar.space) : W)
        - rationalPoint ((⟨v2 - v3, v2_sub_v3_mem_I⟩ : ↥lineI.space) : W)
      ∈ lineSpan lineI := by
  have hsub : ((⟨v2 - v0 - v3, v2_sub_v0_sub_v3_mem_Ipar⟩ : ↥lineIpar.space) : W)
      - ((⟨v2 - v3, v2_sub_v3_mem_I⟩ : ↥lineI.space) : W) = (-1 : ℚ) • v0 := by
    simp only [neg_one_smul]
    abel
  rw [← map_sub, hsub, rationalPoint_rat_smul, lineSpan]
  exact Submodule.smul_mem _ (-1 : ℝ) (Submodule.subset_span (Set.mem_singleton _))

/-- **Clause 3 at the carrier**: the partner change does not change the element of `⋀²W(ℝ)` that the
sheet is carried to. The complements `I^⊥/I ≅ ⟨e₀, e₁⟩^⊥` and `I^⊥/I ≅ ⟨e₀, e₁ + e₂⟩^⊥` differ, but
`e₀ ∧ ·` kills the difference, which is a multiple of `e₀`. -/
theorem partner_change_wedge :
    wedgeLeft (rationalPoint lineIpar.gen)
        (rationalPoint ((⟨v2 - v0 - v3, v2_sub_v0_sub_v3_mem_Ipar⟩ : ↥lineIpar.space) : W)) =
      wedgeLeft (rationalPoint lineI.gen)
        (rationalPoint ((⟨v2 - v3, v2_sub_v3_mem_I⟩ : ↥lineI.space) : W)) := by
  rw [lineIpar_gen]
  exact wedgeLeft_eq_of_sub_mem_span sheet_diff_mem_lineSpan

/-! ## Clause 2: the two orientations of the plane -/

/-- **The flip is a different presentation of the same plane**: its positive generator is `-r_J`. -/
theorem flip_generator :
    wedgeTwo (rationalPoint splitPlane.flip.dir) (rationalPoint splitPlane.flip.dirAlt) =
      -wedgeTwo (rationalPoint v0) (rationalPoint v2) := by
  rw [ConicalPlane.flip_wedge, splitPlane_dir, splitPlane_dirAlt]

/-- **The comparison in the model**: the flipped plane's ray at `lineI` is the negative of the ray,
moved along the line by `planeRayFlipCoeff`, which here is `0` because the generator is a basis
vector. -/
theorem planeRay_flip_lineI :
    lineI.planeRay splitPlane.flip lineI_le
      = -(lineI.planeRay splitPlane lineI_le)
        + planeRayFlipCoeff lineI splitPlane lineI_le • lineI.gen :=
  ConicalLine.planeRay_flip lineI splitPlane lineI_le

/-- The coefficient of the comparison is `0` at `lineI`: `e₀` is the first basis vector, so the
flipped ray is exactly `-e₂`. -/
theorem planeRayCoeff_lineI : planeRayFlipCoeff lineI splitPlane lineI_le = 0 := by
  have hgen : (⟨lineI.gen, lineI.gen_mem_of_le splitPlane lineI_le⟩ : ↥splitPlane.plane)
      = splitPlane.basis 0 :=
    Subtype.ext (by rw [← ConicalPlane.dir, splitPlane_dir]; rfl)
  have h0 : planeRayCoeffA lineI splitPlane lineI_le = 1 := by
    rw [planeRayCoeffA, hgen, splitPlane.basis.repr_self]
    simp
  have h1 : planeRayCoeffB lineI splitPlane lineI_le = 0 := by
    rw [planeRayCoeffB, hgen, splitPlane.basis.repr_self]
    simp
  rw [planeRayFlipCoeff, h0, h1]
  norm_num

/-- **Clause 2 closed at the denial**: at `lineI`, where `splitPlane` is coherent, the flipped
orientation is not — one fibre cannot present both orientations of a plane. -/
theorem flip_not_coherent_at_lineI : ¬ splitPlane.flip.IsPositiveAt lineI lineI_le :=
  ConicalMember.not_isPositiveAt_flip lineI splitPlane lineI_le isPositiveAt_lineI

/-- **Clause 2 at the carrier**: at the fibre whose sheet is the negative one — where the flipped
orientation is the coherent one — the carrier is the *antipodal* ray of `r_J`, not the ray. It is
therefore not the carrier of `C_{J,+}`, and the two orientations are not identified here. -/
theorem flip_carrier_at_lineIneg
    (hcoh : splitPlane.flip.IsPositiveAt lineIneg lineIneg_le) :
    (ConicalMember.plane lineIneg splitPlane.flip lineIneg_le hcoh :
        ConicalMember splitForm splitQ).carrier splitForm_symm =
      {x : ⋀[ℝ]^2 (realified W) | ∃ t : ℝ, 0 ≤ t ∧
        t • (-(wedgeTwo (rationalPoint v0) (rationalPoint v2))) = x} := by
  rw [ConicalMember.carrier_plane_flip splitForm_symm lineIneg splitPlane lineIneg_le hcoh,
    splitPlane_dir, splitPlane_dirAlt]

/-- **The antipodal carrier is not the half line `C_{J,+}`**: the flipped orientation contributes a
different subset of `⋀²W(ℝ)`, because `r_J = e₀ ∧ e₂ ≠ 0`. -/
theorem flip_carrier_ne_posRay
    (hcoh : splitPlane.flip.IsPositiveAt lineIneg lineIneg_le) :
    (ConicalMember.plane lineIneg splitPlane.flip lineIneg_le hcoh :
        ConicalMember splitForm splitQ).carrier splitForm_symm ≠
      {x : ⋀[ℝ]^2 (realified W) | ∃ t : ℝ, 0 ≤ t ∧
        t • wedgeTwo (rationalPoint splitPlane.dir) (rationalPoint splitPlane.dirAlt) = x} :=
  ConicalMember.carrier_plane_flip_ne_posRay splitForm_symm lineIneg splitPlane lineIneg_le hcoh

/-- **The flip leaves the member's centre at `J`**: the two orientations present the same plane, so
the isotropic centre does not move — what the flip changes is the carrier, above. -/
theorem flip_centre (hnd : (associated splitQ).Nondegenerate)
    (hpos : sigPos (fibreForm splitQ lineIneg.space) = 1)
    (hndf : (fibreForm splitQ lineIneg.space).Nondegenerate)
    (hcoh : splitPlane.flip.IsPositiveAt lineIneg lineIneg_le) :
    (ConicalMember.plane lineIneg splitPlane.flip lineIneg_le hcoh :
        ConicalMember splitForm splitQ).isotropicCenter splitForm_symm
        (fun F => facialDecomposition F.closure) = realify splitPlane.plane :=
  ConicalMember.isotropicCenter_plane_flip splitQ_associated splitForm_symm hnd lineIneg
    splitPlane lineIneg_le hcoh hpos hndf

/-! ## Clause 1: the isotropic centre of `C_{J,+}` -/
/-! ## Clause 1: the isotropic centre of `C_{J,+}` -/

/-- **The member's isotropic generators span the plane**: `e₀`, `e₂` are isotropic and span `J`. -/
theorem plane_span_isotropic :
    realify splitPlane.plane = Submodule.span ℝ
      ({rationalPoint v0, rationalPoint v2} : Set (realified W)) := by
  rw [ConicalPlane.realify_eq_span_isotropic, splitPlane_dir, splitPlane_dirAlt]

theorem dir_iso : splitForm splitPlane.dir splitPlane.dir = 0 := by
  rw [splitPlane_dir]; exact v0_iso

theorem dirAlt_iso : splitForm splitPlane.dirAlt splitPlane.dirAlt = 0 := by
  rw [splitPlane_dirAlt, splitForm_apply]
  simp [v2]

/-- **Clause 1 at the plane**: the isotropic centre of `C_{J,+}` is `J` itself. The analytic side
conditions — nondegeneracy of the ambient form, and the signature/nondegeneracy of the fibre form —
are carried, not computed here. -/
theorem plane_centre (hnd : (associated splitQ).Nondegenerate)
    (hpos : sigPos (fibreForm splitQ lineI.space) = 1)
    (hndf : (fibreForm splitQ lineI.space).Nondegenerate) :
    (ConicalMember.plane lineI splitPlane lineI_le isPositiveAt_lineI :
        ConicalMember splitForm splitQ).isotropicCenter splitForm_symm
        (fun F => facialDecomposition F.closure) = realify splitPlane.plane :=
  ConicalMember.isotropicCenter_plane_bailyBorel splitQ_associated splitForm_symm hnd lineI
    splitPlane lineI_le isPositiveAt_lineI hpos hndf

/-- The centre is the span of the member's isotropic generators, not a larger space: its value is
the plane, as the generators' span is. -/
theorem plane_centre_eq_span_isotropic (hnd : (associated splitQ).Nondegenerate)
    (hpos : sigPos (fibreForm splitQ lineI.space) = 1)
    (hndf : (fibreForm splitQ lineI.space).Nondegenerate) :
    (ConicalMember.plane lineI splitPlane lineI_le isPositiveAt_lineI :
        ConicalMember splitForm splitQ).isotropicCenter splitForm_symm
        (fun F => facialDecomposition F.closure) =
      Submodule.span ℝ ({rationalPoint v0, rationalPoint v2} : Set (realified W)) := by
  rw [plane_centre hnd hpos hndf, plane_span_isotropic]

end ConicalPlaneSplit22
