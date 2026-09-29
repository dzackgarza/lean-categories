/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Total
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.Data.Rat.Cast.Lemmas

@[expose] public section

/-!
# Integral lattices given by Gram matrices, and their duals

For an integral Gram matrix `G : Matrix (Fin n) (Fin n) ℤ`:

* `lattice G` is `ℤⁿ` with the form `(x, y) ↦ xᵀ G y`, valued in `ℤ`;
* `dual G` is the dual lattice `L^♯ = {v ∈ L ⊗ ℚ | B(v, L) ⊆ ℤ} = {v ∈ ℚⁿ | Gᵀ v ∈ ℤⁿ}` with the
  restriction of the rational form, valued in `ℚ` (Conway–Sloane, *SPLAG*, ch. 2 §2.2);
* `toDual G : lattice G ⟶ dual G` is the inclusion `L ⊆ L^♯`, with `ℤ ⊆ ℚ` on values. Its
  cokernel is the discriminant group `L^♯ / L`.

No nondegeneracy is assumed: these are the definitions for every Gram matrix. The root lattice
`A_n` has Gram matrix the Cartan matrix `CartanMatrix.A n`, and `A_n^♯ / A_n ≅ ℤ/(n+1)`
(*SPLAG*, ch. 4 §6.1).
-/

open CategoryTheory

namespace LeanCategories.Lattices.Integral

open LeanCategories.Modules.Bilinear.Valued

variable {n : ℕ}

/-- `ℤⁿ` with the form `(x, y) ↦ xᵀ G y`. -/
noncomputable def lattice (G : Matrix (Fin n) (Fin n) ℤ) : BilWFormCat.{0} ℤ :=
  BilWFormCat.of (ModuleCat.of ℤ (Fin n → ℤ)) (ModuleCat.of ℤ ℤ)
    (TensorProduct.lift (Matrix.toLinearMap₂' ℤ G))

/-- The coordinatewise inclusion `ℤⁿ ⊆ ℚⁿ`. -/
def castLinear : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) :=
  LinearMap.pi fun i => (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj i)

@[simp]
theorem castLinear_apply (x : Fin n → ℤ) (i : Fin n) : castLinear x i = (x i : ℚ) := rfl

/-- The rational form of `G` on `ℚⁿ`, as a `ℤ`-bilinear map. -/
noncomputable def rationalForm (G : Matrix (Fin n) (Fin n) ℤ) :
    (Fin n → ℚ) →ₗ[ℤ] (Fin n → ℚ) →ₗ[ℤ] ℚ :=
  (Matrix.toLinearMap₂' ℚ (G.map (Int.cast : ℤ → ℚ))).restrictScalars₁₂ ℤ ℤ

/-- The dual lattice `{v ∈ ℚⁿ | Gᵀ v ∈ ℤⁿ}`: the `v` with `B(v, e_j) ∈ ℤ` for every `j`. -/
noncomputable def dualSubmodule (G : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℚ) :=
  (LinearMap.range castLinear).comap
    (((G.map (Int.cast : ℤ → ℚ)).transpose.mulVecLin).restrictScalars ℤ)

/-- The dual lattice with the restriction of the rational form. -/
noncomputable def dual (G : Matrix (Fin n) (Fin n) ℤ) : BilWFormCat.{0} ℤ :=
  BilWFormCat.of (ModuleCat.of ℤ (dualSubmodule G)) (ModuleCat.of ℤ ℚ)
    (TensorProduct.lift
      ((rationalForm G).compl₁₂ (dualSubmodule G).subtype (dualSubmodule G).subtype))

theorem castLinear_mem_dual (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    castLinear x ∈ dualSubmodule G := by
  refine ⟨G.transpose.mulVec x, funext fun j => ?_⟩
  simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.transpose_apply, mul_comm]

theorem cast_form (G : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ℤ) :
    ((Matrix.toLinearMap₂' ℤ G x y : ℤ) : ℚ) =
      Matrix.toLinearMap₂' ℚ (G.map (Int.cast : ℤ → ℚ)) (castLinear x) (castLinear y) := by
  simp only [Matrix.toLinearMap₂'_apply, Matrix.map_apply, castLinear_apply, smul_eq_mul]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The inclusion `L ⊆ L^♯`, with `ℤ ⊆ ℚ` on values. -/
noncomputable def toDual (G : Matrix (Fin n) (Fin n) ℤ) : lattice G ⟶ dual G :=
  BilWFormCat.homMk (castLinear.codRestrict (dualSubmodule G) (castLinear_mem_dual G))
    (Int.castAddHom ℚ).toIntLinearMap (by
      intro x y
      exact cast_form G x y)

/-- The root lattice `A_n`: Gram matrix `CartanMatrix.A n`. -/
noncomputable abbrev rootA (n : ℕ) : BilWFormCat.{0} ℤ := lattice (CartanMatrix.A n)

/-- The dual `A_n^♯`. -/
noncomputable abbrev rootADual (n : ℕ) : BilWFormCat.{0} ℤ := dual (CartanMatrix.A n)

/-- `A_n ⊆ A_n^♯`. -/
noncomputable def rootAToDual (n : ℕ) : rootA n ⟶ rootADual n := toDual (CartanMatrix.A n)

end LeanCategories.Lattices.Integral
