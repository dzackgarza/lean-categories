/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.Constructions
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- Twice the coordinates of a standard simple-root basis for `E₈`. -/
def e8RootNumerator : Fin 8 → Fin 8 → ℤ := ![
  ![ 1, -1, -1, -1, -1, -1, -1,  1],
  ![ 2,  2,  0,  0,  0,  0,  0,  0],
  ![-2,  2,  0,  0,  0,  0,  0,  0],
  ![ 0, -2,  2,  0,  0,  0,  0,  0],
  ![ 0,  0, -2,  2,  0,  0,  0,  0],
  ![ 0,  0,  0, -2,  2,  0,  0,  0],
  ![ 0,  0,  0,  0, -2,  2,  0,  0],
  ![ 0,  0,  0,  0,  0, -2,  2,  0]]

/-- The inner products of the doubled roots are exactly divisible by four. -/
theorem e8RootDot_exists (i j : Fin 8) :
    ∃ z : ℤ, ∑ k, e8RootNumerator i k * e8RootNumerator j k = 4 * z := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e8RootNumerator, Fin.sum_univ_succ]
  all_goals first
    | exact ⟨2, by decide⟩
    | exact ⟨-1, by decide⟩

/-- The exact integral inner product of two standard `E₈` roots. -/
noncomputable def e8RootInnerProduct (i j : Fin 8) : ℤ :=
  Classical.choose (e8RootDot_exists i j)

theorem e8RootInnerProduct_spec (i j : Fin 8) :
    ∑ k, e8RootNumerator i k * e8RootNumerator j k =
      4 * e8RootInnerProduct i j :=
  Classical.choose_spec (e8RootDot_exists i j)

theorem e8RootInnerProduct_comm (i j : Fin 8) :
    e8RootInnerProduct i j = e8RootInnerProduct j i := by
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  rw [← e8RootInnerProduct_spec i j, ← e8RootInnerProduct_spec j i]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The negative `E₈` Gram matrix derived from the standard roots above. -/
noncomputable def e8GramMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j ↦ -e8RootInnerProduct i j

theorem e8GramMatrix_isSymm : e8GramMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by
    simp only [e8GramMatrix]
    rw [e8RootInnerProduct_comm]

/-- The negative definite `E₈` root lattice in its simple-root basis. -/
noncomputable def e8Lattice : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap (Matrix.toBilin' e8GramMatrix), ?_, ?_⟩
  · change Module.Projective ℤ (Fin 8 → ℤ)
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr
      e8GramMatrix_isSymm).eq x y

/-- The negative `E₈` lattice as a finite projective lattice. -/
noncomputable def e8FiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨e8Lattice, ?_⟩
  change Module.Finite ℤ (Fin 8 → ℤ)
  infer_instance

@[simp]
theorem e8Lattice_pairing (x y : e8Lattice.obj.carrier) :
    e8Lattice.obj.pairing x y = Matrix.toBilin' e8GramMatrix x y :=
  rfl

/-- The simple-root basis has the standard `E₈` Gram matrix. -/
theorem e8Lattice_gramMatrix :
    gramMatrix e8Lattice (Pi.basisFun ℤ (Fin 8)) = e8GramMatrix := by
  exact LinearMap.BilinForm.toMatrix'_toBilin' e8GramMatrix

/-- The form of the integral hyperbolic plane. -/
def hyperbolicPlaneBilinMap : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y ↦ x.1 * y.2 + x.2 * y.1)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)
    (fun _ _ _ ↦ by simp; ring)

/-- The integral hyperbolic plane `U`. -/
def hyperbolicPlane : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap hyperbolicPlaneBilinMap, ?_, ?_⟩
  · change Module.Projective ℤ (ℤ × ℤ)
    infer_instance
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
  change x₁ * y₂ + x₂ * y₁ = y₁ * x₂ + y₂ * x₁
  ring

/-- The hyperbolic plane as a finite projective lattice. -/
def hyperbolicPlaneFiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨hyperbolicPlane, ?_⟩
  change Module.Finite ℤ (ℤ × ℤ)
  infer_instance

@[simp]
theorem hyperbolicPlane_pairing (x y : hyperbolicPlane.obj.carrier) :
    hyperbolicPlane.obj.pairing x y = x.1 * y.2 + x.2 * y.1 :=
  rfl

/-- The `K3` lattice `3U ⊥ 2E₈`, with negative `E₈`. -/
noncomputable def k3Lattice : IntegralLatticeCat ℤ :=
  orthogonalSum (orthogonalPower hyperbolicPlane 3)
    (orthogonalPower e8Lattice 2)

/-- The `K3` lattice as a finite projective lattice. -/
noncomputable def k3FiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨k3Lattice, ?_⟩
  change Module.Finite ℤ ((Fin 3 → ℤ × ℤ) × (Fin 2 → Fin 8 → ℤ))
  infer_instance

end LeanCategories.Lattices.Valued
