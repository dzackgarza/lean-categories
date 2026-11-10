/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CobleReduction
public import LeanCategories.Lattices.Valued.Standard
public import LeanCategories.Lattices.Valued.Signature

/-!
# The `E₈(−2)` half of the signature of the reduction `Q = e^⊥/e` of `T_Co` (#114)

`T_Co = ⟨2⟩ ⊕ E(2)` with `E = E₈ ⊕ U` (see `CobleLattice`), with `e = e₁` the first isotropic
vector of the `U` summand. The `⟨2⟩` and `E₈(−2)` summands survive the reduction `Q = e^⊥/ℤe` and
the `U` summand does not, so the Gram matrix of `Q` in the classes of `e₀, e₃, …, e₁₀` is the block
sum `⟨2⟩ ⊕ E₈(−2)` and the real signature of `Q` is `(1, 8, 0)`.

This file supplies the `E₈(−2)` half of that computation: the eight `E₈(−2)` basis vectors of
`T_Co` span the submatrix `cobleE8Block` of the computed Gram matrix, which is twice the negative
`E₈` form (`cobleE8Block_eq`), hence a negative definite form of rank eight
(`cobleE8Block_matrixSignature`), via the explicit real change of basis `cobleE8RealChange` obtained
by scaling the real root-coordinate matrix of `E₈`.

**Not here:** the classes of `e₀, e₃, …, e₁₀` are not yet packaged as a `ℤ`-basis of `Q`, and the
`⟨2⟩ ⊕ E₈(−2)` Gram matrix and the signature `(1, 8, 0)` of `Q` are not yet stated. Those need the
coordinate equivalence `Q ≃ₗ[ℤ] (Fin 1 ⊕ Fin 8 → ℤ)` together with the pairing computation on the
nine classes.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The `E₈(−2)` block of the Gram matrix of `T_Co` -/

/-- The `E₈(−2)` block of the Gram matrix of `T_Co`: the pairings of the eight `E₈(−2)` basis
vectors. -/
noncomputable def cobleE8Block : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => cobleGramMatrix (cobleE8Index i) (cobleE8Index j)

/-- The `E₈(−2)` block is twice the negative `E₈` form: it is the `E₈` block of the computed Gram
matrix of the constructed lattice. -/
theorem cobleE8Block_eq : cobleE8Block = (2 : ℤ) • e8GramMatrix := by
  ext i j
  rw [cobleE8Block, cobleGramMatrix, Matrix.of_apply, cobleBlockEquiv_cobleE8Index,
    cobleBlockEquiv_cobleE8Index, cobleBlockGramMatrix_inr_inl_inl, Matrix.smul_apply,
    smul_eq_mul]

/-- The real `E₈(−2)` block, written as a negative Gram matrix `-(Bᵀ * B)` of an invertible real
change of basis. -/
noncomputable def cobleE8RealChange : Matrix (Fin 8) (Fin 8) ℝ :=
  Real.sqrt 2 • e8RealRootChange

theorem e8RealRootChange_mulVec_injective :
    Function.Injective e8RealRootChange.mulVec := by
  intro x y h
  have h' := congrArg (fun z => e8RealRootChangeInverse.mulVec z) h
  simpa [Matrix.mulVec_mulVec, e8RealRootChange_leftInverse, Matrix.one_mulVec] using h'

theorem cobleE8RealChange_mulVec_injective :
    Function.Injective cobleE8RealChange.mulVec := by
  have hsq : Real.sqrt 2 ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt hpos
  intro x y h
  have h3 : Real.sqrt 2 • e8RealRootChange.mulVec x = Real.sqrt 2 • e8RealRootChange.mulVec y := by
    simpa [cobleE8RealChange, Matrix.smul_mulVec] using h
  exact e8RealRootChange_mulVec_injective (smul_right_injective (Fin 8 → ℝ) hsq h3)

/-- The real `E₈(−2)` block is the negative Gram matrix of the invertible change
`cobleE8RealChange`. -/
theorem cobleE8Block_map_eq :
    cobleE8Block.map (Int.castRingHom ℝ) =
      -(cobleE8RealChange.transpose * cobleE8RealChange) := by
  have hmap : cobleE8Block.map (Int.castRingHom ℝ) =
      (2 : ℝ) • (e8GramMatrix.map (Int.castRingHom ℝ)) := by
    rw [cobleE8Block_eq]
    ext i j
    change (((2 : ℤ) * e8GramMatrix i j : ℤ) : ℝ) = (2 : ℝ) * ((e8GramMatrix i j : ℤ) : ℝ)
    rw [Int.cast_mul]
    norm_num
  rw [hmap, e8RealGram_factorization, cobleE8RealChange, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), smul_neg]

/-- **The `E₈(−2)` block is negative definite of rank eight.** -/
theorem cobleE8Block_matrixSignature :
    matrixSignature ℝ (cobleE8Block.map (Int.castRingHom ℝ)) = (0, 8, 0) := by
  rw [cobleE8Block_map_eq]
  exact matrixSignature_neg_transpose_mul_self _ cobleE8RealChange_mulVec_injective

end LeanCategories.Lattices.Valued
