/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleLattice
public import LeanCategories.Lattices.Valued.CobleReductionSignature
public import LeanCategories.Lattices.Valued.LatticeCone
public import LeanCategories.Lattices.Valued.Signature

/-!
# The signature of `T_Co`, from its Gram matrix (#120)

`cobleLattice` is `T_Co = ⟨2⟩ ⊕ (E₈(−2) ⊕ U(2))` (`CobleLattice`), built as the orthogonal sum
`⟨2⟩ ⊥ (E₈ ⊥ U)` scaled by `2`. Its Gram matrix in the block basis is the block sum
`rankOneGramMatrix 2 ⊥ (2 • e8GramMatrix ⊥ 2 • hyperbolicPlaneGramMatrix)`, and every signature
statement here is a computation on that Gram matrix: `matrixSignature_reindex` transports the
signature from the block indexing to `Fin 11`, `matrixSignature_blockSum` splits the blocks, and
each block's signature is that block's theorem — `matrixSignature_diagonal` for `⟨2⟩`,
`cobleE8Block_matrixSignature` for `E₈(−2)`, and `hyperbolicPlane_matrixSignature` with
`matrixSignature_smul_pos` for `U(2)`. The numerals in `cobleFiniteLattice_integralSignature` are
produced by `norm_num` from those theorems; no signature is assumed anywhere.

## References

* I. Dolgachev, S. Kondō, *The rationality of the moduli spaces of Coble surfaces and of nodal
  Enriques surfaces*, Izv. Math. 77:3 (2013), §2–3.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## `T_Co` as a finite projective integral lattice -/

/-- `T_Co` as a finite projective integral lattice, so that it has a real form and a signature. -/
noncomputable def cobleFiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ :=
  ⟨cobleLattice, by
    show Module.Finite ℤ ↥cobleLattice.obj.carrier
    infer_instance⟩

/-- The Gram matrix of `T_Co` in its standard basis is the computed Gram matrix. -/
theorem gramMatrix_cobleBasis : gramMatrix cobleLattice cobleBasis = cobleGramMatrix := by
  ext i j
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  exact (cobleGramMatrix_apply i j).symm

/-! ## The real Gram matrix as a reindexed block matrix -/

/-- The real Gram matrix of `T_Co` is the real block matrix, reindexed to `Fin 11`. -/
theorem cobleGramReal_eq_reindex :
    cobleGramReal =
      Matrix.reindex cobleBlockEquiv.symm cobleBlockEquiv.symm
        (cobleBlockGramMatrix.map (Int.castRingHom ℝ)) := by
  ext i j
  simp [cobleGramReal, cobleGramMatrix, Matrix.reindex_apply]

/-- The block structure of the Gram matrix of `T_Co`: the block sum of the Gram matrices of `⟨2⟩`,
`E₈(−2)` and `U(2)`. -/
theorem cobleBlockGramMatrix_eq_blockSum :
    cobleBlockGramMatrix =
      matrixBlockSum (rankOneGramMatrix 2)
        (matrixBlockSum ((2 : ℤ) • e8GramMatrix)
          ((2 : ℤ) • hyperbolicPlaneGramMatrix)) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp only [matrixBlockSum, cobleBlockGramMatrix_inl_inl, cobleBlockGramMatrix_inl_inr,
      cobleBlockGramMatrix_inr_inl, cobleBlockGramMatrix_inr_inl_inl,
      cobleBlockGramMatrix_inr_inl_inr, cobleBlockGramMatrix_inr_inr_inl,
      cobleBlockGramMatrix_inr_inr_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.smul_apply, smul_eq_mul, rankOneGramMatrix, Matrix.of_apply] <;>
    ring

/-- The block structure of the real block Gram matrix of `T_Co`. -/
theorem cobleBlockGramMatrix_map_eq :
    cobleBlockGramMatrix.map (Int.castRingHom ℝ) =
      matrixBlockSum ((rankOneGramMatrix 2).map (Int.castRingHom ℝ))
        (matrixBlockSum (((2 : ℤ) • e8GramMatrix).map (Int.castRingHom ℝ))
          (((2 : ℤ) • hyperbolicPlaneGramMatrix).map (Int.castRingHom ℝ))) := by
  rw [cobleBlockGramMatrix_eq_blockSum, matrixBlockSum_map, matrixBlockSum_map]

/-! ## The signature of each block -/

/-- The `⟨2⟩` block is positive definite of rank one. -/
theorem rankOneGramMatrix_two_matrixSignature :
    matrixSignature ℝ ((rankOneGramMatrix 2).map (Int.castRingHom ℝ)) = (1, 0, 0) := by
  rw [show (rankOneGramMatrix 2).map (Int.castRingHom ℝ) =
      Matrix.diagonal (fun _ : Fin 1 => (2 : ℝ)) from by
    ext i j
    fin_cases i
    fin_cases j
    simp [rankOneGramMatrix, Matrix.diagonal]]
  rw [matrixSignature_diagonal]
  norm_num

/-- The `E₈(−2)` block is negative definite of rank eight. -/
theorem cobleE8GramBlock_matrixSignature :
    matrixSignature ℝ (((2 : ℤ) • e8GramMatrix).map (Int.castRingHom ℝ)) = (0, 8, 0) := by
  have h : ((2 : ℤ) • e8GramMatrix).map (Int.castRingHom ℝ) =
      cobleE8Block.map (Int.castRingHom ℝ) := by
    rw [cobleE8Block_eq]
  rw [h]
  exact cobleE8Block_matrixSignature

/-- The `U(2)` block has signature `(1, 1, 0)`. -/
theorem hyperbolicPlaneGramMatrix_two_matrixSignature :
    matrixSignature ℝ (((2 : ℤ) • hyperbolicPlaneGramMatrix).map (Int.castRingHom ℝ)) =
      (1, 1, 0) := by
  have h : ((2 : ℤ) • hyperbolicPlaneGramMatrix).map (Int.castRingHom ℝ) =
      (2 : ℝ) • hyperbolicPlaneGramMatrix.map (Int.castRingHom ℝ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    norm_num
  rw [h, matrixSignature_smul_pos _ (by norm_num), hyperbolicPlane_matrixSignature]

/-! ## The signature of `T_Co` -/

/-- **The signature of `T_Co` in the block indexing**, computed from the Gram matrix. -/
theorem matrixSignature_cobleBlockGramReal :
    matrixSignature ℝ (cobleBlockGramMatrix.map (Int.castRingHom ℝ)) = (2, 9, 0) := by
  rw [cobleBlockGramMatrix_map_eq, matrixSignature_blockSum, matrixSignature_blockSum,
    rankOneGramMatrix_two_matrixSignature, cobleE8GramBlock_matrixSignature,
    hyperbolicPlaneGramMatrix_two_matrixSignature]
  norm_num

/-- **The signature of `T_Co` in its standard basis**, computed from the Gram matrix. -/
theorem matrixSignature_cobleGramReal : matrixSignature ℝ cobleGramReal = (2, 9, 0) := by
  rw [cobleGramReal_eq_reindex, matrixSignature_reindex]
  exact matrixSignature_cobleBlockGramReal

set_option backward.isDefEq.respectTransparency.types false in
/-- **The signature of `T_Co`**, from its Gram matrix: `sigPos = 2`, `sigNeg = 9`, no null part. -/
theorem cobleFiniteLattice_integralSignature :
    integralSignature cobleFiniteLattice = (2, 9, 0) := by
  let b : Module.Basis (Fin 11) ℤ ↥cobleFiniteLattice.obj.obj.carrier := cobleBasis
  rw [integralSignature_eq_matrixSignature cobleFiniteLattice b]
  have hb : gramMatrix cobleFiniteLattice.obj b = cobleGramMatrix := gramMatrix_cobleBasis
  rw [hb]
  exact matrixSignature_cobleGramReal

/-- The positive index of `T_Co`. -/
theorem cobleFiniteLattice_sigPos : (integralSignature cobleFiniteLattice).1 = 2 := by
  rw [cobleFiniteLattice_integralSignature]

/-- The negative index of `T_Co`. -/
theorem cobleFiniteLattice_sigNeg : (integralSignature cobleFiniteLattice).2.1 = 9 := by
  rw [cobleFiniteLattice_integralSignature]

end LeanCategories.Lattices.Valued
