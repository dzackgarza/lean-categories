/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCategories.Lattices.Valued.ConicalRefinement
import LeanCategories.Lattices.Valued.SemifanArrangement
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The plane case of Lemma 6.6 in signature `(2,3)`: `J^⊥ ⊋ J`

Red test for `dzackgarza/lean-categories#169`, in the smallest signature in which the plane case can
fail. The `(2,2)` model of `tests/regression/ConicalRefinementSplit22.lean` cannot decide it, because
there every `ℚ`-isotropic plane is self-orthogonal, so `J^⊥ = J` and every support space of a half
line is the plane itself. Here `W = ℚ⁵` carries the split form

`x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂ − x₄y₄`

of signature `(2,3)`; `I = ⟨e₀⟩` with partner `e₁` has fibre `I^⊥/I = ⟨e₂, e₃, e₄⟩` of signature
`(1,2)` and form `−2x₂x₃ − x₄²`; the `ℚ`-isotropic plane is `J = ⟨e₀, u⟩` with

`u = e₂ − 2e₃ + 2e₄`,

an isotropic vector in the *smooth* part of the fibre's null cone (`−2·1·(−2) − 2² = 0`).

The assertions:

* `J_ne_perp` (`J^⊥ ≠ J`) and `perp_strict`: `J ⊊ J^⊥`, with `e₂ + 2e₃` as the witness — it is
  orthogonal to `J` (`2·1 − 2 − 0 = 0`) and not in `J`, so `J^⊥/J` is one-dimensional here and the
  window `[J, J^⊥]` in which every support space of `C_{J,+}` lies is nondegenerate.
* `wall_through_J` and `wall_value`: the wall `ψ = x₃ + x₄` vanishes on `J`, and in the fibre its
  trace cuts `u^⊥` down to `⟨u⟩`: `J^⊥ ⊓ ker ψ = J`. So the arrangement `Σ({ψ})`, which refines
  `Σ(bb)`, has `J_{Σ({ψ})} = J` while `J_{Σ(bb)} = J^⊥` — the two support spaces of the same half
  line `C_{J,+}` are *strictly* nested in signature `(2,3)`, which no `(2,2)` model can show. The
  inclusion `J ⊆ J^⊥` is the plane case of Lemma 6.6 for that pair, and it is proved with no
  subordinate hypothesis as `vSigmaPlane_semifanArrangement_le_facial` in
  `LeanCategories.Lattices.Valued.ConicalRefinement`.
-/

open LeanCategories.Lattices.Valued
open QuadraticMap

namespace ConicalPlaneRefinement23

/-! ## The split space of signature `(2,3)` -/

abbrev W := Fin 5 → ℚ

def v0 : W := ![1, 0, 0, 0, 0]
def v1 : W := ![0, 1, 0, 0, 0]
def v2 : W := ![0, 0, 1, 0, 0]
def v3 : W := ![0, 0, 0, 1, 0]
def v4 : W := ![0, 0, 0, 0, 1]

/-- The split form `x₀y₁ + x₁y₀ − x₂y₃ − x₃y₂ − x₄y₄` of signature `(2,3)`. -/
def splitForm : LinearMap.BilinForm ℚ W :=
  LinearMap.mk₂ ℚ (fun x y => x 0 * y 1 + x 1 * y 0 - x 2 * y 3 - x 3 * y 2 - x 4 * y 4)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro a x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intro x y z; simp only [Pi.add_apply]; ring)
    (by intro a x y; simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem splitForm_apply (x y : W) :
    splitForm x y = x 0 * y 1 + x 1 * y 0 - x 2 * y 3 - x 3 * y 2 - x 4 * y 4 := rfl

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

/-! ## The isotropic plane `J = ⟨e₀, u⟩`, `u = e₂ − 2e₃ + 2e₄` -/

/-- The isotropic vector `u = e₂ − 2e₃ + 2e₄` of the fibre: it spans the class of the plane `J` in
`I^⊥/I`, and it lies in the smooth part of the fibre's null cone. -/
def uvec : W := v2 - (2 : ℚ) • v3 + (2 : ℚ) • v4

theorem uvec_sq : splitForm uvec uvec = 0 := by
  rw [splitForm_apply]; simp [uvec, v2, v3, v4]; norm_num

theorem v0_iso : splitForm v0 v0 = 0 := by rw [splitForm_apply]; simp [v0]
theorem uvec_orth_v0 : splitForm v0 uvec = 0 := by
  rw [splitForm_apply]; simp [v0, uvec, v2, v3, v4]

/-- The `ℚ`-isotropic plane `J = ⟨e₀, u⟩`. -/
def J : Submodule ℚ W := Submodule.span ℚ ({v0, uvec} : Set W)

theorem v0_mem_J : v0 ∈ J := Submodule.subset_span (Set.mem_insert _ _)
theorem uvec_mem_J : uvec ∈ J :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem J_isotropic : ∀ x ∈ J, ∀ y ∈ J, splitForm x y = 0 := by
  intro x hx y hy
  rw [J, Submodule.mem_span_pair] at hx hy
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.add_apply,
    smul_eq_mul]
  rw [v0_iso, uvec_sq, splitForm_symm.eq uvec v0, uvec_orth_v0]
  ring

theorem v0_ne : v0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [v0] at this

theorem uvec_ne : uvec ≠ 0 := by
  intro h; have := congrFun h 2; simp [uvec, v2, v3, v4] at this

theorem v0_uvec_li : LinearIndependent ℚ (![v0, uvec] : Fin 2 → W) := by
  rw [linearIndependent_fin2]
  refine ⟨uvec_ne, fun a ha => ?_⟩
  have h : a = 0 := by
    have h2 := congrFun ha 2
    simpa [v0, uvec, v2, v3, v4] using h2
  exact v0_ne (by simpa [h] using ha.symm)

/-! ## `J^⊥` and its strictness -/

/-- **The witness of `J^⊥ ⊋ J`**: `e₂ + 2e₃` is orthogonal to `J` and is not in `J`. -/
def perpWitness : W := v2 + (2 : ℚ) • v3

theorem perpWitness_orth {x : W} (hx : x ∈ J) : splitForm x perpWitness = 0 := by
  rw [J, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.add_apply,
    smul_eq_mul, splitForm_apply]
  simp [v0, uvec, perpWitness, v2, v3, v4]

theorem perpWitness_notMem : perpWitness ∉ J := by
  intro h
  rw [J, Submodule.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  have h2 := congrFun hab 2
  have h3 := congrFun hab 3
  simp [v0, uvec, perpWitness, v2, v3, v4] at h2 h3
  linarith

theorem perpWitness_ne : perpWitness ≠ 0 := by
  intro h; have := congrFun h 2; simp [perpWitness, v2, v3] at this

/-- **`J ⊊ J^⊥` in this signature**: the plane is not self-orthogonal, so the window
`[J, J^⊥]` between the two possible support spaces of a half line is nondegenerate. In the `(2,2)`
model of `ConicalRefinementSplit22` this statement is false for every plane. -/
theorem J_lt_perp :
    J < LinearMap.BilinForm.orthogonal splitForm J := by
  refine lt_of_le_of_ne (fun x hx => ?_) ?_
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [splitForm_symm.eq (x := y) (y := x)]
    exact J_isotropic x hx y hy
  · intro heq
    apply perpWitness_notMem
    rw [heq]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact perpWitness_orth hy

/-! ## The wall through `J`, and the value it forces at the half line -/

/-- The `ℚ`-linear functional `ψ = x₃ + x₄`: it vanishes on the plane `J = ⟨e₀, u⟩`, so its
hyperplane is a wall through `J` in the sense of `planeWalls`. -/
def psi : W →ₗ[ℚ] ℚ where
  toFun x := x 3 + x 4
  map_add' := by intro a b; simp only [Pi.add_apply]; ring
  map_smul' := by intro a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem psi_v0 : psi v0 = 0 := by simp [psi, v0]

theorem psi_uvec : psi uvec = 0 := by simp [psi, uvec, v2, v3, v4]

theorem psi_zero_on_J {x : W} (hx : x ∈ J) : psi x = 0 := by
  rw [J, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  simp only [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, psi_v0, psi_uvec]
  ring

theorem psi_perpWitness : psi perpWitness = 2 := by
  simp [psi, perpWitness, v2, v3]

/-- **The value at the half line, in the fibre**: a vector orthogonal to `J` and to the wall `ψ` lies
in `J`. So `J^⊥ ⊓ ker ψ = J`, i.e. `J_{Σ({ψ})} = J ⊊ J^⊥ = J_{Σ(bb)}`: the two support spaces of the
same half line are strictly nested in signature `(2,3)`. -/
theorem JH_eq_J {x : W} (hperp : ∀ y ∈ J, splitForm y x = 0) (hpsi : psi x = 0) : x ∈ J := by
  have h1 : splitForm v0 x = 0 := hperp v0 v0_mem_J
  have h2 : splitForm uvec x = 0 := hperp uvec uvec_mem_J
  rw [splitForm_apply] at h1 h2
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk] at hpsi
  simp [v0, uvec, v2, v3, v4] at h1 h2
  rw [J, Submodule.mem_span_pair]
  refine ⟨x 0, x 2, ?_⟩
  funext i
  fin_cases i <;> simp [v0, uvec, v2, v3, v4] <;> linarith

end ConicalPlaneRefinement23
