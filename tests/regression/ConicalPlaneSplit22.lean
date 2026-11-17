/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Lattices.Valued.Semifan

/-!
# A genuine oriented rational isotropic plane of a split space of signature `(2,2)`

Regression for `dzackgarza/lean-categories#165`: the carrier `ConicalPlane` of
`LeanCategories.Lattices.Valued.ConicalLocus` must be inhabited, and the ray of the plane in the
fibre of a witnessing line must be the image of the *positive* rational generator `r_J ∈ ⋀²J(ℚ)`
of Looijenga, *Compactifications defined by arrangements II* (math/0201218v2), Example 6.3, p. 29 —
not the opposite half line.

The space is `W = ℚ⁴` with the split form `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂` of signature `(2,2)`. The
isotropic plane is `J = ⟨e₀, e₂⟩`, positively oriented by `r_J = e₀ ∧ e₂`. Its two witnessing lines
are `I = ⟨e₀⟩` and `I' = ⟨e₀ + e₂⟩`; the ray of `J` in *both* fibres is the class of `e₂` (the
image of `r_J` under the inclusion `⋀²J ⊂ I ⊗ I^⊥/I` of §1B, p. 11), it is a nonzero isotropic
vector of each fibre form, and it lies strictly inside the closed sheet of the fibre's cone
(`0 < e₂ · sheet` in both fibres), so that `fibreRay` is that class and not its opposite.

Before #165 the carrier stored a single vector `ray` with
`ray_not_mem_of_line : ∀ I ≤ plane, finrank I = 1 → ray ∉ I`, which no vector satisfies: applied to
`I = ⟨ray⟩` it gives `ray ∉ ⟨ray⟩`. The first commit of this file carried exactly that construction
and the elaboration error it produced; no instance of the old carrier exists.
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

end ConicalPlaneSplit22
