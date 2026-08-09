/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
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

/-- The root construction gives the standard negative `E₈` matrix. -/
theorem e8GramMatrix_eq : e8GramMatrix = ![
    ![-2,  0,  1,  0,  0,  0,  0,  0],
    ![ 0, -2,  0,  1,  0,  0,  0,  0],
    ![ 1,  0, -2,  1,  0,  0,  0,  0],
    ![ 0,  1,  1, -2,  1,  0,  0,  0],
    ![ 0,  0,  0,  1, -2,  1,  0,  0],
    ![ 0,  0,  0,  0,  1, -2,  1,  0],
    ![ 0,  0,  0,  0,  0,  1, -2,  1],
    ![ 0,  0,  0,  0,  0,  0,  1, -2]] := by
  ext i j
  have h := e8RootInnerProduct_spec i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e8GramMatrix, e8RootNumerator, Fin.sum_univ_succ] at h ⊢ <;>
    omega

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

/-- An integral inverse for the negative `E₈` Gram matrix. -/
def e8GramMatrixInverse : Matrix (Fin 8) (Fin 8) ℤ := ![
  ![ -4,  -5,  -7, -10,  -8,  -6, -4, -2],
  ![ -5,  -8, -10, -15, -12,  -9, -6, -3],
  ![ -7, -10, -14, -20, -16, -12, -8, -4],
  ![-10, -15, -20, -30, -24, -18, -12, -6],
  ![ -8, -12, -16, -24, -20, -15, -10, -5],
  ![ -6,  -9, -12, -18, -15, -12,  -8, -4],
  ![ -4,  -6,  -8, -12, -10,  -8,  -6, -3],
  ![ -2,  -3,  -4,  -6,  -5,  -4,  -3, -2]]

/-- The displayed integral matrix is a right inverse. -/
theorem e8GramMatrix_mul_inverse :
    e8GramMatrix * e8GramMatrixInverse = 1 := by
  rw [e8GramMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e8GramMatrixInverse, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The negative `E₈` Gram determinant is a unit. -/
theorem e8GramMatrix_isUnit_det : IsUnit e8GramMatrix.det :=
  Matrix.isUnit_det_of_right_inverse e8GramMatrix_mul_inverse

/-- The negative `E₈` lattice is unimodular. -/
theorem e8Lattice_isUnimodular : IsUnimodular e8Lattice := by
  rw [isUnimodular_iff_isUnit_determinant e8Lattice (Pi.basisFun ℤ (Fin 8))]
  simpa [determinant, e8Lattice_gramMatrix] using e8GramMatrix_isUnit_det

/-- The negative `E₈` lattice is even. -/
theorem e8Lattice_isEven : IsEven e8Lattice := by
  apply isEven_of_basis e8Lattice (Pi.basisFun ℤ (Fin 8))
  intro i
  rw [Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  change Matrix.toBilin' e8GramMatrix
    ((Pi.basisFun ℤ (Fin 8)) i) ((Pi.basisFun ℤ (Fin 8)) i) = 2 * -1
  simp only [Pi.basisFun_apply, Matrix.toBilin'_single]
  rw [e8GramMatrix_eq]
  fin_cases i <;> norm_num

/-- The Gram matrix of the integral hyperbolic plane. -/
def hyperbolicPlaneGramMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem hyperbolicPlaneGramMatrix_isSymm : hyperbolicPlaneGramMatrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hyperbolicPlaneGramMatrix]

/-- The integral hyperbolic plane `U`. -/
def hyperbolicPlane : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap
    (Matrix.toBilin' hyperbolicPlaneGramMatrix), ?_, ?_⟩
  · change Module.Projective ℤ (Fin 2 → ℤ)
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr
      hyperbolicPlaneGramMatrix_isSymm).eq x y

/-- The hyperbolic plane as a finite projective lattice. -/
def hyperbolicPlaneFiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨hyperbolicPlane, ?_⟩
  change Module.Finite ℤ (Fin 2 → ℤ)
  infer_instance

@[simp]
theorem hyperbolicPlane_pairing (x y : hyperbolicPlane.obj.carrier) :
    hyperbolicPlane.obj.pairing x y =
      Matrix.toBilin' hyperbolicPlaneGramMatrix x y :=
  rfl

/-- The standard basis has the hyperbolic Gram matrix. -/
theorem hyperbolicPlane_gramMatrix :
    gramMatrix hyperbolicPlane (Pi.basisFun ℤ (Fin 2)) =
      hyperbolicPlaneGramMatrix := by
  exact LinearMap.BilinForm.toMatrix'_toBilin' hyperbolicPlaneGramMatrix

/-- The integral hyperbolic plane is unimodular. -/
theorem hyperbolicPlane_isUnimodular : IsUnimodular hyperbolicPlane := by
  rw [isUnimodular_iff_isUnit_determinant hyperbolicPlane
    (Pi.basisFun ℤ (Fin 2))]
  rw [determinant, hyperbolicPlane_gramMatrix, hyperbolicPlaneGramMatrix,
    Matrix.det_fin_two]
  norm_num

/-- The integral hyperbolic plane is even. -/
theorem hyperbolicPlane_isEven : IsEven hyperbolicPlane := by
  apply isEven_of_basis hyperbolicPlane (Pi.basisFun ℤ (Fin 2))
  intro i
  rw [Ideal.mem_span_singleton]
  refine ⟨0, ?_⟩
  change Matrix.toBilin' hyperbolicPlaneGramMatrix
    ((Pi.basisFun ℤ (Fin 2)) i) ((Pi.basisFun ℤ (Fin 2)) i) = 2 * 0
  simp only [Pi.basisFun_apply, Matrix.toBilin'_single]
  fin_cases i <;> norm_num [hyperbolicPlaneGramMatrix]

/-- The `K3` lattice `3U ⊥ 2E₈`, with negative `E₈`. -/
noncomputable def k3Lattice : IntegralLatticeCat ℤ :=
  orthogonalSum (orthogonalPower hyperbolicPlane 3)
    (orthogonalPower e8Lattice 2)

/-- The `K3` lattice as a finite projective lattice. -/
noncomputable def k3FiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨k3Lattice, ?_⟩
  change Module.Finite ℤ ((Fin 3 → Fin 2 → ℤ) × (Fin 2 → Fin 8 → ℤ))
  infer_instance

/-- The `K3` lattice is unimodular. -/
theorem k3Lattice_isUnimodular : IsUnimodular k3Lattice :=
  isUnimodular_orthogonalSum _ _
    (isUnimodular_orthogonalPower hyperbolicPlane 3 hyperbolicPlane_isUnimodular)
    (isUnimodular_orthogonalPower e8Lattice 2 e8Lattice_isUnimodular)

/-- The `K3` lattice is even. -/
theorem k3Lattice_isEven : IsEven k3Lattice :=
  isEven_orthogonalSum _ _
    (isEven_orthogonalPower hyperbolicPlane 3 hyperbolicPlane_isEven)
    (isEven_orthogonalPower e8Lattice 2 e8Lattice_isEven)

end LeanCategories.Lattices.Valued
