/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# Jordan blocks and Jordan canonical form

This file records the definitions from Dummit--Foote, Chapter 12, §12.3,
The Jordan Canonical Form, p. 491. It proves no existence, uniqueness, or
classification theorem.

The implementation reuses Mathlib's `Matrix.blockDiagonal'`,
`Matrix.reindex`, `Matrix.GeneralLinearGroup`, and `LinearMap.toMatrix`.
-/

namespace LeanCategories.Algebra

universe u v w

section JordanBlocks

variable (K : Type u) [Field K]

/-- The `n`-by-`n` Jordan block with eigenvalue `λ`.

The diagonal entries are `λ`, the superdiagonal entries are `1`, and all
other entries are zero. The positivity condition on `n` belongs to a
Jordan-matrix datum, so this definition also permits the empty matrix.
-/
def JordanBlock (n : ℕ) (eigenvalue : K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then eigenvalue else if i.val + 1 = j.val then 1 else 0

@[simp]
theorem JordanBlock_apply_diag (n : ℕ) (eigenvalue : K) (i : Fin n) :
    JordanBlock K n eigenvalue i i = eigenvalue := by
  simp [JordanBlock]

@[simp]
theorem JordanBlock_apply_superdiag (n : ℕ) (eigenvalue : K) {i j : Fin n}
    (h : i.val + 1 = j.val) : JordanBlock K n eigenvalue i j = 1 := by
  have hne : i.val ≠ j.val := by omega
  simp [JordanBlock, Fin.ext_iff, hne, h]

end JordanBlocks

section JordanMatrices

variable (K : Type u) [Field K]

/-- The finite block data of a Jordan matrix.

Every block has positive size. The ambient matrix index is the dependent
sum of the block positions and the coordinates inside each block.
-/
structure JordanMatrix where
  blockCount : ℕ
  blockSize : Fin blockCount → ℕ
  eigenvalue : Fin blockCount → K
  blockSize_pos : ∀ i, 0 < blockSize i

namespace JordanMatrix

variable (J : JordanMatrix K)

/-- The block-diagonal matrix represented by a Jordan matrix datum. -/
def matrix : Matrix (Σ i, Fin (J.blockSize i)) (Σ i, Fin (J.blockSize i)) K :=
  Matrix.blockDiagonal' fun i => JordanBlock K (J.blockSize i) (J.eigenvalue i)

/-- Reindex a Jordan matrix datum to a chosen finite matrix index. -/
def reindex {n : Type v} (e : n ≃ Σ i, Fin (J.blockSize i)) : Matrix n n K :=
  Matrix.reindex e.symm e.symm (JordanMatrix.matrix K J)

end JordanMatrix

end JordanMatrices

section Similarity

variable (K : Type u) [Field K]

/-- Similarity of square matrices by an element of the general linear group. -/
def SimilarMatrices {n : Type v} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup n K,
    (P⁻¹ : Matrix n n K) * A * (P : Matrix n n K) = B

/-- A square matrix is a Jordan matrix after a finite reindexing. -/
def IsJordanMatrix {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  ∃ J : JordanMatrix K, ∃ e : n ≃ Σ i, Fin (J.blockSize i),
    A = JordanMatrix.reindex K J e

/-- A square matrix is in Jordan canonical form up to similarity. -/
def IsJordanCanonical {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : Prop :=
  ∃ J : JordanMatrix K, ∃ e : n ≃ Σ i, Fin (J.blockSize i),
    SimilarMatrices K A (JordanMatrix.reindex K J e)

end Similarity

section LinearMaps

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]

/-- A linear map has Jordan canonical matrix in the chosen finite basis. -/
def IsJordanCanonicalInBasis {n : Type w} [Fintype n] [DecidableEq n]
    (f : V →ₗ[K] V) (b : Module.Basis n K V) : Prop :=
  IsJordanCanonical K (LinearMap.toMatrix b b f)

/-- A finite-dimensional endomorphism admits a chosen basis with Jordan matrix. -/
def HasJordanCanonicalForm [Module.Finite K V] (f : V →ₗ[K] V) : Prop :=
  ∃ n : ℕ, ∃ b : Module.Basis (Fin n) K V,
    IsJordanCanonicalInBasis (K := K) (V := V) f b

end LinearMaps

end LeanCategories.Algebra
