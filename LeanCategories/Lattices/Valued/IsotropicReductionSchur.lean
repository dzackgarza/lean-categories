/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The adapted block Gram determinant for arbitrary `C`, `E`

With the adapted Gram matrix of `P ⊆ P^⊥ ⊆ L` in the block order `(Q, P, W)`,

    X = [[M, 0, C], [0, 0, B], [Cᵀ, Bᵀ, E]],

the Schur complement of the `M`-block is the corner `[[0,B],[Bᵀ,E − Cᵀ M⁻¹ C]]`, whose determinant
is `±(det B)²`; hence `|det X| = |det M| · |det B|²` for *arbitrary* `C` and `E`.
-/

@[expose] public section

open Matrix

namespace Schur

variable {r m : ℕ}

/-- `[0 C]` as a matrix with `(Fin r ⊕ Fin r)`-columns. -/
def wideBlock (C : Matrix (Fin m) (Fin r) ℚ) : Matrix (Fin m) (Fin r ⊕ Fin r) ℚ :=
  Matrix.of fun j => Sum.elim (fun _ => 0) (C j)

/-- The transpose of `wideBlock`. -/
def tallBlock (C : Matrix (Fin m) (Fin r) ℚ) : Matrix (Fin r ⊕ Fin r) (Fin m) ℚ :=
  Matrix.of fun i j => Sum.elim (fun _ => 0) (C j) i

@[simp] theorem wide_inl (C : Matrix (Fin m) (Fin r) ℚ) (j : Fin m) (i : Fin r) :
    wideBlock C j (Sum.inl i) = 0 := rfl

@[simp] theorem wide_inr (C : Matrix (Fin m) (Fin r) ℚ) (j : Fin m) (k : Fin r) :
    wideBlock C j (Sum.inr k) = C j k := rfl

@[simp] theorem tall_inl (C : Matrix (Fin m) (Fin r) ℚ) (i : Fin r) (j : Fin m) :
    tallBlock C (Sum.inl i) j = 0 := rfl

@[simp] theorem tall_inr (C : Matrix (Fin m) (Fin r) ℚ) (k : Fin r) (j : Fin m) :
    tallBlock C (Sum.inr k) j = C j k := rfl

/-- The `Q`-`W` corner of the Schur complement: `[0 Cᵀ] X [0 C]ᵀ` only has a `W`-part. -/
theorem tall_mul_mul_wide (C : Matrix (Fin m) (Fin r) ℚ) (X : Matrix (Fin m) (Fin m) ℚ) :
    tallBlock C * X * wideBlock C =
      fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) 0 0 (Cᵀ * X * C) := by
  ext (i | i) (j | j)
  · simp [Matrix.mul_apply, fromBlocks_apply₁₁]
  · simp [Matrix.mul_apply, fromBlocks_apply₁₂]
  · simp [Matrix.mul_apply, fromBlocks_apply₂₁]
  · simp only [Matrix.mul_apply, fromBlocks_apply₂₂, tall_inr, Matrix.transpose_apply, wide_inr]


/-! ## The determinant for arbitrary `C`, `E` -/

/-- The corner `[[0,B],[Bᵀ,E]]` has determinant `±(det B)²`; in absolute value `(det B)²`. -/
theorem abs_det_corner (B : Matrix (Fin r) (Fin r) ℚ) (E : Matrix (Fin r) (Fin r) ℚ) :
    |(fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) B Bᵀ E).det| = |B.det| * |B.det| := by
  have hswap : fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) B Bᵀ E =
      (fromBlocks Bᵀ E (0 : Matrix (Fin r) (Fin r) ℚ) B).submatrix
        (Equiv.sumComm (Fin r) (Fin r)) id := by
    ext (i | i) (j | j) <;> rfl
  rw [hswap, det_permute, det_fromBlocks_zero₂₁, det_transpose, abs_mul, abs_mul]
  have hs : |((((Equiv.Perm.sign (Equiv.sumComm (Fin r) (Fin r)) : ℤˣ) : ℤ) : ℚ))| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin r) (Fin r))) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [hs, one_mul]

/-- The adapted Gram matrix in the block order `(Q, P, W)`. -/
def blockGram (B : Matrix (Fin r) (Fin r) ℚ) (M : Matrix (Fin m) (Fin m) ℚ)
    (C : Matrix (Fin m) (Fin r) ℚ) (E : Matrix (Fin r) (Fin r) ℚ) :
    Matrix (Fin m ⊕ (Fin r ⊕ Fin r)) (Fin m ⊕ (Fin r ⊕ Fin r)) ℚ :=
  fromBlocks M (wideBlock C) (tallBlock C) (fromBlocks 0 B Bᵀ E)

/-- **The adapted block Gram determinant for arbitrary `C`, `E`**:
`|det X| = |det M| · |det B|²`.  The Schur complement of the `M`-block has corner
`[[0,B],[Bᵀ,E − Cᵀ M⁻¹ C]]`. -/
theorem abs_det_blockGram (B : Matrix (Fin r) (Fin r) ℚ) (M : Matrix (Fin m) (Fin m) ℚ)
    (C : Matrix (Fin m) (Fin r) ℚ) (E : Matrix (Fin r) (Fin r) ℚ) (hM : M.det ≠ 0) :
    |(blockGram B M C E).det| = |M.det| * (|B.det| * |B.det|) := by
  have : Invertible M.det := invertibleOfNonzero hM
  have : Invertible M := M.invertibleOfDetInvertible
  have h := det_fromBlocks₁₁ M (wideBlock C) (tallBlock C)
    (fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) B Bᵀ E)
  have hsub : fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) B Bᵀ E -
      tallBlock C * ⅟M * wideBlock C =
      fromBlocks (0 : Matrix (Fin r) (Fin r) ℚ) B Bᵀ (E - Cᵀ * ⅟M * C) := by
    rw [tall_mul_mul_wide]
    ext (i | i) (j | j) <;> simp [Matrix.sub_apply]
  rw [blockGram, h, hsub, abs_mul, abs_det_corner]

end Schur