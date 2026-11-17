/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
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
import LeanCategories.Lattices.Valued.Semifan

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

/-! ## The defect: the carrier at `55966097` admits no instance

The field `ray_not_mem_of_line` of the carrier at `55966097` demands a single vector `ray` that lies
outside *every* isotropic line of the plane. The construction below is the one a user of that
carrier would write on this concrete split space: the plane `J = ⟨e₀, e₂⟩` with the ray `e₂`. Its last
field is a statement about all lines `I ≤ J`, and it is refuted by `I = ⟨ray⟩` itself, which is a line
of `J` containing `ray`; no term inhabits it. The commit that introduced this file carries the
elaboration error at that field. -/

/-- **The construction the old carrier promises, attempted on the split space**: fails at
`ray_not_mem_of_line`, whose negation is exactly the hypothesis `hmem`. -/
noncomputable def splitPlaneOld : ConicalPlane splitForm where
  plane := J
  isotropic := J_isotropic
  two_dim := J_two_dim
  ray := v2
  ray_mem := v2_mem_J
  ray_ne := v2_ne
  ray_not_mem_of_line := by
    intro I _hI _h1 hmem
    exact hmem

/-- **The recorded contradiction of the old fields**: taking `I = ⟨ray⟩` in
`ray_not_mem_of_line` gives `ray ∉ ⟨ray⟩`, which `ray_mem` refutes. Hence the old carrier is empty
and every statement quantified over it is vacuous. -/
theorem is_empty_conicalPlane : IsEmpty (ConicalPlane splitForm) where
  false G := by
    have h1 : Module.finrank ℚ ↥(Submodule.span ℚ ({G.ray} : Set W)) = 1 :=
      finrank_span_singleton G.ray_ne
    have hI : Submodule.span ℚ ({G.ray} : Set W) ≤ G.plane :=
      Submodule.span_le.2 (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact G.ray_mem)
    exact G.ray_not_mem_of_line _ hI h1 (Submodule.subset_span (Set.mem_singleton G.ray))

end ConicalPlaneSplit22
