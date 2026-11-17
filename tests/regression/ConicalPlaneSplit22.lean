/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Lattices.Valued.ConicalMember
import Mathlib.LinearAlgebra.ExteriorPower.Basis

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

## The second defect: the sheet of a fibre is not a presentation of an oriented plane

Deriving the ray from `r_J` is not enough, because `fibreRay` still chooses its *sign* by pairing the
class of `r_J` with the sheet of the line's cone, and the sheet is independent data: `lineI` with
its sheet negated (`lineIneg`) is a `ConicalLine` with the same line, generator and partner, since
the fibre form is even. Through it the same oriented plane `splitPlane` has the opposite carrier
`{t • (-r_J) | 0 ≤ t}` in `⋀²V(ℝ)`. The red commit of this file (26413a39) proved exactly that,
with the carrier identity `{t • r_J | 0 ≤ t}` at `lineI` and `carrier_lineI_ne_lineIneg`.

The repair is `ConicalPlane.IsPositiveAt`, the source's `C_J ⊂ ∂C_I` (§1B, p. 11) and "`r_J` can be
regarded as an isotropic vector in `(C_I)_+`" (Example 6.3, p. 29), required by
`ConicalMember.plane`. At it, the carrier is the closed ray of `r_J`
(`ConicalMember.carrier_plane_eq_positiveRay`), so the two witnessing lines agree
(`carrier_lineI_eq_lineII`); `not_isPositiveAt_lineIneg` says the negated sheet is not a
presentation of this plane, and `carrier_fibre_lineIneg_eq_negRay` /
`carrier_lineI_ne_carrier_fibre_lineIneg` record what it contributes at the level of the fibre
member, which needs no coherence: the antipodal ray. The two orientations of a plane, and the two
sheets of a fibre, remain legitimate source data — only their pairing is constrained.
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
negated sheet is again a positive vector of the same reduction `I^⊥/I`. This is a legitimate piece of
source data — the other cone `C_I` of the same fibre — and it is *not* a presentation of the
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

/-! ## The carrier at the coherent presentations -/

/-- **The carrier of the plane at `lineI` is the closed ray of `r_J`**, `{t • r_J | 0 ≤ t}`: the
positive generator of Example 6.3, p. 29, carried through the inclusion `⋀²J ⊂ I ⊗ I^⊥/I`. -/
theorem carrier_lineI_eq_posRay :
    (ConicalMember.plane lineI splitPlane lineI_le isPositiveAt_lineI :
        ConicalMember splitForm splitQ).carrier splitForm_symm =
      {x : ⋀[ℝ]^2 (realified W) |
        ∃ t : ℝ, 0 ≤ t ∧ t • wedgeTwo (rationalPoint v0) (rationalPoint v2) = x} := by
  rw [ConicalMember.carrier_plane_eq_positiveRay splitForm_symm lineI splitPlane lineI_le
    isPositiveAt_lineI, splitPlane_dir, splitPlane_dirAlt]

/-- The same at the second witnessing line `I' = ⟨e₀ + e₂⟩`. -/
theorem carrier_lineII_eq_posRay :
    (ConicalMember.plane lineII splitPlane lineII_le isPositiveAt_lineII :
        ConicalMember splitForm splitQ).carrier splitForm_symm =
      {x : ⋀[ℝ]^2 (realified W) |
        ∃ t : ℝ, 0 ≤ t ∧ t • wedgeTwo (rationalPoint v0) (rationalPoint v2) = x} := by
  rw [ConicalMember.carrier_plane_eq_positiveRay splitForm_symm lineII splitPlane lineII_le
    isPositiveAt_lineII, splitPlane_dir, splitPlane_dirAlt]

/-- **The two source-valid witnessing lines of the split plane give the same carrier**: the plane
member's image in `⋀²V(ℝ)` does not depend on the line, at the presentations the source allows. -/
theorem carrier_lineI_eq_lineII :
    (ConicalMember.plane lineI splitPlane lineI_le isPositiveAt_lineI :
        ConicalMember splitForm splitQ).carrier splitForm_symm =
      (ConicalMember.plane lineII splitPlane lineII_le isPositiveAt_lineII :
        ConicalMember splitForm splitQ).carrier splitForm_symm :=
  ConicalMember.carrier_plane_eq_of_witness splitForm_symm lineI lineII splitPlane lineI_le lineII_le
    isPositiveAt_lineI isPositiveAt_lineII

/-! ## What the other sheet contributes

`ConicalMember` has no plane member at the negated sheet — that is the repair — but the *fibre*
member generated by the plane's class in that fibre is a member of the conical locus without any
coherence requirement, and its carrier is the opposite ray. That is the red fact the regression
above records at the level of the definitions: the sign of the class is not a function of the plane
alone. -/

/-- The carrier of the fibre member generated by a single vector in a fibre. -/
theorem mem_carrier_fibre_hull_iff (F : ConicalLine splitForm splitQ) (y : ↥F.space)
    (x : ⋀[ℝ]^2 (realified W)) :
    x ∈ (ConicalMember.fibre F
        (PointedCone.hull ℝ ({rationalPoint y} : Set (realified ↥F.space))) :
        ConicalMember splitForm splitQ).carrier splitForm_symm ↔
      ∃ t : ℝ, 0 ≤ t ∧
        t • (wedgeLeft (rationalPoint F.gen) (realifyMap F.space (rationalPoint y))) = x := by
  simp only [ConicalMember.carrier, Set.mem_image]
  constructor
  · rintro ⟨z, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_hull_singleton] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact ⟨t, ht, by rw [map_smul, map_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨realifyMap F.space (t • rationalPoint y),
      ⟨t • rationalPoint y, mem_hull_singleton.2 ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
    rw [map_smul, map_smul]

/-- The plane's class at the negated sheet, carried to `⋀²V(ℝ)`, is `-r_J`: the half line of that
fibre is the opposite class (`fibreRay_lineIneg`), and the projection moves it by a multiple of the
line's generator only. -/
theorem wedgeLeft_fibreRay_lineIneg :
    wedgeLeft (rationalPoint lineIneg.gen) (realifyMap lineIneg.space
        (rationalPoint (fibreRay splitForm_symm lineIneg splitPlane lineIneg_le))) =
      - wedgeTwo (rationalPoint v0) (rationalPoint v2) := by
  rw [fibreRay_lineIneg]
  simp only [map_neg]
  have h := wedgeLeft_fibreRayProj splitForm_symm lineIneg splitPlane lineIneg_le
  rw [planeRay_lineIneg] at h
  rw [h]
  rfl

/-- **The other sheet contributes the opposite ray.** The fibre member above the plane's class in
the fibre of `lineIneg` is carried to `{t • (-r_J) | 0 ≤ t}`, and this carrier is not the one the
plane has at `lineI`. -/
theorem carrier_fibre_lineIneg_eq_negRay :
    (ConicalMember.fibre lineIneg
        (PointedCone.hull ℝ
          ({rationalPoint (fibreRay splitForm_symm lineIneg splitPlane lineIneg_le)} :
            Set (realified ↥lineIneg.space))) :
        ConicalMember splitForm splitQ).carrier splitForm_symm =
      {x : ⋀[ℝ]^2 (realified W) |
        ∃ t : ℝ, 0 ≤ t ∧ t • (-(wedgeTwo (rationalPoint v0) (rationalPoint v2))) = x} := by
  refine Set.ext fun x => ?_
  rw [mem_carrier_fibre_hull_iff, Set.mem_ofPred]
  refine exists_congr fun t => ?_
  rw [wedgeLeft_fibreRay_lineIneg]

/-- **The carrier is not a function of the plane alone.** The fibre member above the plane's class
in the fibre of `lineIneg` has the antipodal carrier, so it differs from the plane member's carrier
at `lineI`; the sign is a property of the presentation, and the repair is to require the coherent
one rather than to let both through. -/
theorem carrier_lineI_ne_carrier_fibre_lineIneg :
    (ConicalMember.plane lineI splitPlane lineI_le isPositiveAt_lineI :
        ConicalMember splitForm splitQ).carrier splitForm_symm ≠
      (ConicalMember.fibre lineIneg
        (PointedCone.hull ℝ
          ({rationalPoint (fibreRay splitForm_symm lineIneg splitPlane lineIneg_le)} :
            Set (realified ↥lineIneg.space))) :
        ConicalMember splitForm splitQ).carrier splitForm_symm := by
  intro h
  have hmem : wedgeTwo (rationalPoint v0) (rationalPoint v2) ∈
      (ConicalMember.fibre lineIneg
        (PointedCone.hull ℝ
          ({rationalPoint (fibreRay splitForm_symm lineIneg splitPlane lineIneg_le)} :
            Set (realified ↥lineIneg.space))) :
        ConicalMember splitForm splitQ).carrier splitForm_symm := by
    rw [← h, carrier_lineI_eq_posRay]
    exact Set.mem_ofPred.2 ⟨1, zero_le_one, by rw [one_smul]⟩
  rw [carrier_fibre_lineIneg_eq_negRay] at hmem
  obtain ⟨t, ht, htR⟩ := hmem
  have hR : wedgeTwo (rationalPoint v0) (rationalPoint v2) = 0 := by
    set R := wedgeTwo (rationalPoint v0) (rationalPoint v2) with hRdef
    have h1 : t • (-R) = R := htR
    have h1' : -(t • R) = R := by rw [smul_neg] at h1; exact h1
    have h3 : t • R = -R := neg_eq_iff_eq_neg.mp h1'
    have h2 : (t + 1) • R = 0 := by
      rw [add_smul, one_smul, h3]
      abel
    rcases smul_eq_zero.1 h2 with h4 | h4
    · exact absurd h4 (by linarith)
    · exact h4
  exact R_ne_zero hR

end ConicalPlaneSplit22
