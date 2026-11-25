/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Lattices.Valued.ConicalRefinement
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The line case of Looijenga's Lemma 6.6, strict, on the split space of signature `(2,2)`

Red test for `dzackgarza/lean-categories#169`, on the model of
`tests/regression/ConicalPlaneSplit22.lean` and `tests/regression/ConicalMemberCentre166.lean`:
`W = ℚ⁴` with the split form `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂`, the `ℚ`-isotropic line `I = ⟨e₀⟩` with
hyperbolic partner `e₁`, and the fibre `C_{I,+}` of the reduction `I^⊥/I = ⟨e₂, e₃⟩`, whose form is
`−2 x₂ x₃` of signature `(1,1)` and whose closed cone is the quadrant spanned by the two isotropic
directions `e₂` and `−e₃`.

The member `σ` is the ray through the sheet `e₂ − e₃`, a sub-wedge of `C_{I,+}` of dimension one in
the fibre. Then

`V_σ = I ⊕ ⟨e₂ − e₃⟩  ⊊  I^⊥ = V_{C_{I,+}}`,

the strictness witnessed by `e₂`: it lies in `I^⊥` and not in `I ⊕ ⟨e₂ − e₃⟩`. The two assertions at
the end are the line case of Lemma 6.6 through the landed theorem
`vSigma_le_of_carrier_subset` (`carrier_eq` gives it its hypothesis) and the strictness through
`vSigma`.

**On the admissible-decomposition instances.** The assertion is at the member level, which is where
`vSigma_le_of_carrier_subset` — the whole content of the line case, consumed by
`vSigma_le_of_refinesConicalLocus` — lives; no `IsAdmissibleDecomposition` instance is needed for it,
and none is constructed here. Supplying one on this model means discharging `hcut` for
`isAdmissibleDecomposition_semifanArrangement` at the two fibres of the model, which is the
arrangement's arithmetic input, not the line case.
-/

open LeanCategories.Lattices.Valued
open QuadraticMap

namespace ConicalRefinementSplit22

/-! ## The split space of signature `(2,2)` -/

/-- The rational vector space `ℚ⁴` of the split form. -/
abbrev W := Fin 4 → ℚ

def v0 : W := ![1, 0, 0, 0]
def v1 : W := ![0, 1, 0, 0]
def v2 : W := ![0, 0, 1, 0]
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

theorem splitForm_baseChange_symm : (splitForm.baseChange ℝ).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℝ (LinearMap.BilinForm.isSymm_iff.mp splitForm_symm))

noncomputable def splitQ : QuadraticForm ℝ (realified W) :=
  (splitForm.baseChange ℝ).toQuadraticMap

theorem splitQ_associated (u w : W) :
    (QuadraticMap.associated splitQ) (rationalPoint u) (rationalPoint w)
      = (splitForm u w : ℝ) := by
  unfold splitQ
  rw [QuadraticMap.associated_left_inverse (S := ℝ) splitForm_baseChange_symm.eq]
  simp only [rationalPoint_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
  norm_num

theorem v0_iso : splitForm v0 v0 = 0 := by rw [splitForm_apply]; simp [v0]
theorem v1_iso : splitForm v1 v1 = 0 := by rw [splitForm_apply]; simp [v1]
theorem v0_v1_pairing : splitForm v0 v1 = 1 := by rw [splitForm_apply]; simp [v0, v1]

theorem v0_ne : v0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [v0] at this

theorem span_iso_of (g : W) (hg : splitForm g g = 0) :
    ∀ x ∈ Submodule.span ℚ ({g} : Set W), ∀ y ∈ Submodule.span ℚ ({g} : Set W),
      splitForm x y = 0 := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hg, mul_zero]

/-! ## The fibre of `I = ⟨e₀⟩` -/

/-- The sheet vector `e₂ − e₃` of the fibre: it lies in `I^⊥/I = ⟨e₀, e₁⟩^⊥` and has square `2`. -/
theorem v2_sub_v3_mem_I : v2 - v3 ∈ planeComplement splitForm v0 v1 := by
  rw [mem_planeComplement_iff]
  refine ⟨?_, ?_⟩ <;> rw [splitForm_apply] <;> simp [v0, v1, v2, v3]

theorem v2_mem_I : v2 ∈ planeComplement splitForm v0 v1 := by
  rw [mem_planeComplement_iff]
  refine ⟨?_, ?_⟩ <;> rw [splitForm_apply] <;> simp [v0, v1, v2]

theorem v2_sq : splitForm v2 v2 = 0 := by rw [splitForm_apply]; simp [v2]

/-- The `ℚ`-isotropic line `I = ⟨e₀⟩`, its hyperbolic partner `e₁`, and the sheet of its fibre given
by the positive vector `e₂ − e₃` of the reduction `I^⊥/I`. -/
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

theorem sheet_lineI : lineI.sheet = rationalPoint ⟨v2 - v3, v2_sub_v3_mem_I⟩ := rfl

/-- **The sub-wedge `σ`**: the ray of the sheet `e₂ − e₃` in the fibre of `I`, a member of
Definition 6.1 (i) — nonzero, and not an isotropic half line. -/
noncomputable def sigma : PointedCone ℝ (realified ↥(lineI).space) :=
  PointedCone.hull ℝ ({lineI.sheet} : Set (realified ↥(lineI).space))

theorem sigma_ne_bot : sigma ≠ ⊥ := by
  intro h
  have hmem : lineI.sheet ∈ (sigma : Set (realified ↥(lineI).space)) :=
    PointedCone.subset_hull (Set.mem_singleton _)
  rw [h] at hmem
  have hz : lineI.sheet = 0 := by simpa using hmem
  have hp : 0 < (fibreForm splitQ (lineI).space) lineI.sheet := (lineI).sheet_pos
  rw [hz] at hp
  simp at hp

/-- The sheet lies in the fibre's cone, hence in its rational closure `C_{I,+}`. -/
theorem sheet_mem_closure : lineI.sheet ∈ (lineI.closure : Set (realified ↥(lineI).space)) := by
  have hcone : lineI.sheet ∈ (lineI.cone : Set (realified ↥(lineI).space)) := by
    rw [cone_eq_hull_openStratum]
    exact PointedCone.subset_hull (sheet_mem_openStratum lineI)
  have hb : lineI.sheet ∈ rationalBoundary lineI.cone :=
    ⟨⟨⟨v2 - v3, v2_sub_v3_mem_I⟩, Set.mem_univ _, rfl⟩, subset_closure hcone⟩
  have : lineI.sheet ∈ rationalClosure lineI.cone := by
    rw [rationalClosure_eq_hull]
    exact PointedCone.subset_hull hb
  exact this

theorem sigma_le_closure : sigma ≤ lineI.closure := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := PointedCone.mem_hull_singleton.1 hx
  exact PointedCone.smul_mem lineI.closure ht sheet_mem_closure

/-- The carrier of `σ` lies in the carrier of `C_{I,+}`: the hypothesis of the line case. -/
theorem carrier_subset : (ConicalMember.fibre lineI sigma).carrier splitForm_symm ⊆
    (ConicalMember.fibre lineI (lineI).closure).carrier splitForm_symm :=
  ConicalMember.carrier_fibre_mono splitForm_symm lineI sigma_le_closure

/-! ## The two assertions -/

/-- **The line case of Lemma 6.6 at `σ = ⟨e₂ − e₃⟩`**: the support space of the sub-wedge is
contained in that of `C_{I,+}`, through the landed `vSigma_le_of_carrier_subset`. -/
theorem vSigma_line_case (_hpos : sigPos (fibreForm splitQ (lineI).space) = 1) :
    vSigma lineI sigma ≤ vSigma lineI (lineI).closure :=
  vSigma_le_of_carrier_subset splitQ_associated splitForm_symm sigma_ne_bot carrier_subset

/-- The witness `e₂` of the fibre, as an element of the real form of the fibre's space. -/
noncomputable def w : realified W :=
  realifyMap (lineI).space (rationalPoint (⟨v2, v2_mem_I⟩ : ↥(lineI).space))

theorem w_eq : w = rationalPoint v2 := by
  rw [w, realifyMap_rationalPoint]

/-- `e₂` lies in `V_{C_{I,+}} = I^⊥`. -/
theorem w_mem_big (hpos : sigPos (fibreForm splitQ (lineI).space) = 1) :
    w ∈ vSigma lineI (lineI).closure := by
  rw [ConicalLine.vSigma_closure_eq_ker splitQ_associated splitForm_symm lineI hpos,
    LinearMap.mem_ker, w_eq]
  change (associated splitQ) (rationalPoint (V := W) v0) (rationalPoint (V := W) v2) = 0
  rw [splitQ_associated, splitForm_apply]
  simp [v0, v2]

/-- **`e₂` is not in `V_σ = I ⊕ ⟨e₂ − e₃⟩`**: the functional `x ↦ x · (e₂ + e₃)` vanishes on the
line and on `σ`, and takes the value `−1` at `e₂`. -/
theorem w_not_mem_small : w ∉ vSigma lineI sigma := by
  intro hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
  have hker_line : ∀ y ∈ lineSpan (BQ := splitForm) (Q := splitQ) lineI,
      (associated splitQ) (rationalPoint (v2 + v3)) y = 0 := by
    intro y hy
    rw [show lineSpan (BQ := splitForm) (Q := splitQ) lineI
        = Submodule.span ℝ ({(rationalPoint v0 : realified W)} : Set (realified W)) from rfl,
      Submodule.mem_span_singleton] at hy
    obtain ⟨t, rfl⟩ := hy
    rw [LinearMap.map_smul, smul_eq_mul, splitQ_associated, splitForm_apply]
    simp [v0, v2, v3]
  have hker_map : (associated splitQ) (rationalPoint (v2 + v3)) b = 0 := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hb
    have hspan : Submodule.span ℝ (sigma : Set (realified ↥(lineI).space))
        = Submodule.span ℝ ({lineI.sheet} : Set (realified ↥(lineI).space)) := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · intro x hx
        exact PointedCone.hull_le_span ℝ ({lineI.sheet} : Set _) hx
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Submodule.subset_span (PointedCone.subset_hull (Set.mem_singleton _))
    rw [hspan, Submodule.mem_span_singleton] at hy
    obtain ⟨t, rfl⟩ := hy
    rw [map_smul, LinearMap.map_smul, smul_eq_mul]
    have hsheet : realifyMap (lineI).space lineI.sheet = rationalPoint (v2 - v3) := by
      rw [sheet_lineI, realifyMap_rationalPoint]
    rw [hsheet, splitQ_associated, splitForm_apply]
    simp [v2, v3]
  have hw : (associated splitQ) (rationalPoint (v2 + v3)) w = -1 := by
    rw [w_eq, splitQ_associated, splitForm_apply]
    simp [v2, v3]
  rw [← hab, map_add, hker_line a ha, hker_map, add_zero] at hw
  exact absurd hw (by norm_num)

/-- **The inclusion is strict**: `V_σ ⊊ V_{C_{I,+}}`. -/
theorem vSigma_strict (hpos : sigPos (fibreForm splitQ (lineI).space) = 1) :
    vSigma lineI sigma < vSigma lineI (lineI).closure :=
  lt_of_le_not_ge (vSigma_line_case hpos) fun hge => w_not_mem_small (hge (w_mem_big hpos))

end ConicalRefinementSplit22
