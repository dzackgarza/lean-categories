/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Block-triangular general-linear groups

For a map `b : ι → κ` assigning basis indices to blocks, this file identifies the split extension
of the block-triangular group by its product of diagonal general-linear groups. The normal factor
is the block-unipotent kernel. The semidirect-product equivalence sends `(u, d)` to `u * section d`,
so both the conjugation action and the factor order are explicit.

The elementary-generation theorem and the transport to stabilizers of adapted flags are proved in
this module and `LeanCategories.Modules.Flags`, respectively. No form-preservation condition is
imposed: this is general-linear, not orthogonal, group theory.
-/

@[expose] public section

open scoped Matrix

namespace LeanCategories.Modules

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [LinearOrder κ] [CommRing R]

/-- The indices belonging to one block. -/
abbrev BlockIndex (b : ι → κ) (k : κ) := {i // b i = k}

/-- The subgroup of invertible matrices which are upper block-triangular for `b`. -/
def blockTriangularSubgroup (b : ι → κ) : Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {A | Matrix.BlockTriangular (A : Matrix ι ι R) b}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' hA hB := hA.mul hB
  inv_mem' {A} hA := by
    change Matrix.BlockTriangular (↑A⁻¹ : Matrix ι ι R) b
    letI : Invertible (A : Matrix ι ι R) := A.invertible
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hA

@[simp] theorem mem_blockTriangularSubgroup {b : ι → κ}
    {A : Matrix.GeneralLinearGroup ι R} :
    A ∈ blockTriangularSubgroup b ↔ Matrix.BlockTriangular (A : Matrix ι ι R) b :=
  Iff.rfl

/-- An inverse of a block-triangular unit is again block-triangular. -/
theorem blockTriangular_inv {b : ι → κ} {A : Matrix.GeneralLinearGroup ι R}
    (hA : Matrix.BlockTriangular (A : Matrix ι ι R) b) :
    Matrix.BlockTriangular (↑A⁻¹ : Matrix ι ι R) b := by
  letI : Invertible (A : Matrix ι ι R) := A.invertible
  simpa only [Matrix.GeneralLinearGroup.coe_inv] using
    Matrix.blockTriangular_inv_of_blockTriangular hA

/-- Multiplication restricts to each diagonal block of two block-triangular matrices. -/
theorem toSquareBlock_mul_of_blockTriangular {b : ι → κ} {A B : Matrix ι ι R}
    (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (k : κ) :
    (A * B).toSquareBlock b k = A.toSquareBlock b k * B.toSquareBlock b k := by
  let p : ι → Prop := fun i => b i = k
  change (A * B).toBlock p p = A.toBlock p p * B.toBlock p p
  rw [Matrix.toBlock_mul_eq_add p p p]
  have hz : A.toBlock p (fun i => ¬p i) * B.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_trichotomy (b (l : ι)) k with hl | hl | hl
    · have hzero : A (i : ι) (l : ι) = 0 := hA (by rw [i.property]; exact hl)
      simp [hzero]
    · exact (l.property hl).elim
    · have hzero : B (l : ι) (j : ι) = 0 := hB (by rw [j.property]; exact hl)
      simp [hzero]
  rw [hz, add_zero]

@[simp] theorem toSquareBlock_one (b : ι → κ) (k : κ) :
    (1 : Matrix ι ι R).toSquareBlock b k = 1 :=
  Matrix.toBlock_one_self _

/-- The diagonal-block unit determined by an element of the block-triangular group. -/
def diagonalUnit (b : ι → κ) (A : blockTriangularSubgroup (R := R) b) (k : κ) :
    Matrix.GeneralLinearGroup (BlockIndex b k) R where
  val := (A.1.1 : Matrix ι ι R).toSquareBlock b k
  inv := (↑A.1⁻¹ : Matrix ι ι R).toSquareBlock b k
  val_inv := by
    rw [← toSquareBlock_mul_of_blockTriangular A.2 (blockTriangular_inv A.2)]
    change ((((A.1 : Matrix.GeneralLinearGroup ι R) * A.1⁻¹ :
      Matrix.GeneralLinearGroup ι R)) : Matrix ι ι R).toSquareBlock b k = 1
    rw [mul_inv_cancel]
    exact toSquareBlock_one b k
  inv_val := by
    rw [← toSquareBlock_mul_of_blockTriangular (blockTriangular_inv A.2) A.2]
    change (((A.1⁻¹ * A.1 : Matrix.GeneralLinearGroup ι R)) :
      Matrix ι ι R).toSquareBlock b k = 1
    rw [inv_mul_cancel]
    exact toSquareBlock_one b k

/-- Projection from a block-triangular group to the product of its diagonal general-linear
parts. -/
def diagonalHom (b : ι → κ) :
    blockTriangularSubgroup (R := R) b →* ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R :=
  MonoidHom.pi fun k =>
    { toFun := fun A => diagonalUnit b A k
      map_one' := by
        apply Units.ext
        change (1 : Matrix ι ι R).toSquareBlock b k = 1
        exact toSquareBlock_one b k
      map_mul' := fun A B => Matrix.GeneralLinearGroup.ext fun _ _ =>
        congr_fun₂ (toSquareBlock_mul_of_blockTriangular A.2 B.2 k) _ _ }

/-- The block-unipotent kernel of the diagonal projection. -/
def blockUnipotentSubgroup (b : ι → κ) := (diagonalHom (R := R) b).ker

/-- Reindexing and block-diagonal insertion give the diagonal section into the full general-linear
group. -/
def blockDiagonalGL (b : ι → κ) :
    (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) →* Matrix.GeneralLinearGroup ι R :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (Equiv.sigmaFiberEquiv b)).toMulEquiv).toMonoidHom.comp
    ((Units.map (Matrix.blockDiagonal'RingHom (BlockIndex b) R).toMonoidHom).comp
      MulEquiv.piUnits.symm.toMonoidHom)

@[simp] theorem blockDiagonalGL_val_apply {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) (i j : ι) :
    ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) i j =
      Matrix.blockDiagonal' (fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R))
        ⟨b i, i, rfl⟩ ⟨b j, j, rfl⟩ :=
  rfl

/-- The diagonal section is block-triangular. -/
theorem blockDiagonalGL_blockTriangular {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    Matrix.BlockTriangular ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) :
      Matrix ι ι R) b := by
  rw [show ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R) =
    Matrix.reindexAlgEquiv R R (Equiv.sigmaFiberEquiv b)
      (Matrix.blockDiagonal' fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R)) from rfl]
  rw [Matrix.coe_reindexAlgEquiv, Matrix.blockTriangular_reindex_iff]
  have hb : b ∘ (Equiv.sigmaFiberEquiv b) = Sigma.fst := by
    funext x
    rcases x with ⟨k, i, hi⟩
    simpa only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply] using hi
  rw [hb]
  exact Matrix.blockTriangular_blockDiagonal'
    (R := R) (fun k => (D k : Matrix (BlockIndex b k) (BlockIndex b k) R))

/-- The block-diagonal splitting, valued in the block-triangular group. -/
def blockDiagonalSection (b : ι → κ) :
    (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) →*
      blockTriangularSubgroup (R := R) b where
  toFun D := ⟨blockDiagonalGL b D, blockDiagonalGL_blockTriangular D⟩
  map_one' := Subtype.ext (blockDiagonalGL b).map_one
  map_mul' D E := Subtype.ext ((blockDiagonalGL b).map_mul D E)

@[simp] theorem diagonalHom_blockDiagonalSection {b : ι → κ}
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    diagonalHom b (blockDiagonalSection b D) = D := by
  funext k
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((blockDiagonalGL b D : Matrix.GeneralLinearGroup ι R) : Matrix ι ι R)
    (i : ι) (j : ι) = (D k : Matrix (BlockIndex b k) (BlockIndex b k) R) i j
  rw [blockDiagonalGL_val_apply]
  have hi : (⟨b (i : ι), (i : ι), rfl⟩ : Σ k, BlockIndex b k) = ⟨k, i⟩ := by
    rcases i with ⟨i, rfl⟩
    rfl
  have hj : (⟨b (j : ι), (j : ι), rfl⟩ : Σ k, BlockIndex b k) = ⟨k, j⟩ := by
    rcases j with ⟨j, rfl⟩
    rfl
  rw [hi, hj]
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _

/-- The short exact sequence from the block-unipotent group to the diagonal graded pieces. -/
def blockDiagonalGroupExtension (b : ι → κ) :
    GroupExtension (blockUnipotentSubgroup (R := R) b) (blockTriangularSubgroup (R := R) b)
      (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) where
  inl := (blockUnipotentSubgroup (R := R) b).subtype
  rightHom := diagonalHom b
  inl_injective := Subtype.coe_injective
  range_inl_eq_ker_rightHom := (blockUnipotentSubgroup b).range_subtype
  rightHom_surjective D := ⟨blockDiagonalSection b D, diagonalHom_blockDiagonalSection D⟩

/-- The displayed diagonal splitting of the block-triangular group extension. -/
def blockDiagonalSplitting (b : ι → κ) :
    (blockDiagonalGroupExtension (R := R) b).Splitting where
  toMonoidHom := blockDiagonalSection b
  rightInverse_rightHom := diagonalHom_blockDiagonalSection (R := R)

/-- The block-triangular group is the semidirect product of its unipotent kernel and the product of
its diagonal general-linear groups. The action is conjugation by the diagonal section. -/
noncomputable def blockTriangularSemidirectEquiv (b : ι → κ) :
    blockUnipotentSubgroup (R := R) b ⋊[(blockDiagonalSplitting b).conjAct]
      (∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) ≃*
        blockTriangularSubgroup (R := R) b :=
  (blockDiagonalSplitting b).semidirectProductMulEquiv

/-- In the semidirect-product identification, the pair `(u, d)` maps to `u` followed by the diagonal
section `d`; in particular, the unipotent factor is on the left. -/
@[simp] theorem blockTriangularSemidirectEquiv_apply (b : ι → κ)
    (u : blockUnipotentSubgroup (R := R) b)
    (D : ∀ k, Matrix.GeneralLinearGroup (BlockIndex b k) R) :
    blockTriangularSemidirectEquiv b ⟨u, D⟩ = u.1 * blockDiagonalSection b D :=
  rfl

end LeanCategories.Modules
