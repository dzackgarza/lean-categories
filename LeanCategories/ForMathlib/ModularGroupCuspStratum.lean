/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.ModularGroupPresentation

/-!
# The cusp stratum of `SL(2, ℤ)` (lean-categories#89, item 1)

The Euclidean descent in `LeanCategories.ForMathlib.ModularGroupPresentation`
(`colHeight_step`, `exists_lift_mul_colHeight_le_one`) reduces any `A : SL(2, ℤ)` to first-column
height at most one, so the completeness of the presentation `⟨S, T | S⁴, (TS)³ = S²⟩` hinges on that
stratums' word-level statement: every word whose product has `colHeight ≤ 1` is relation-equivalent
to a fixed word for that product.

This file records what that stratum is structurally, and refutes the natural shortcut.

* It is invariant under *left* multiplication by `S` and `S⁻¹` (`colHeight_le_one_S_mul`) and under
  *right* multiplication by every `T ^ k` (`colHeight_le_one_mul_T_zpow`), since right multiplication
  by a power of `T` leaves the first column alone.
* It is **not** invariant under left multiplication by `T`: `[[1,0],[1,1]]` has height one while
  `T * [[1,0],[1,1]] = [[2,1],[1,1]]` has height two (`colHeight_le_one_T_mul_false`).

So the stratum is a union of `⟨S⟩`-left cosets and `⟨T⟩`-right cosets — the eight double cosets of
the previous commit — and a word-level induction that strips letters alternately from either end
does not stay inside it. That is why the cusp half is not bookkeeping: it is where the amalgam
normal form for `ℤ/4 *_{ℤ/2} ℤ/6` enters.
-/

open scoped MatrixGroups Pointwise

@[expose] public section

open Matrix Matrix.SpecialLinearGroup

namespace ModularGroup

lemma S_mul_zero_zero (A : SL(2, ℤ)) : (S * A).1 0 0 = -A.1 1 0 := by
  rw [show (S * A).1 = (S).1 * A.1 from rfl, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  simp

lemma S_mul_one_zero (A : SL(2, ℤ)) : (S * A).1 1 0 = A.1 0 0 := by
  rw [show (S * A).1 = (S).1 * A.1 from rfl, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  simp

lemma T_mul_one_zero' (A : SL(2, ℤ)) : (T * A).1 1 0 = A.1 1 0 := by
  rw [show (T * A).1 = (T).1 * A.1 from rfl, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  simp

lemma T_mul_zero_zero' (A : SL(2, ℤ)) : (T * A).1 0 0 = A.1 0 0 + A.1 1 0 := by
  rw [show (T * A).1 = (T).1 * A.1 from rfl, coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- The cusp stratum is closed under left multiplication by `S` and `S⁻¹`. -/
theorem colHeight_le_one_S_mul (A : SL(2, ℤ)) (hA : colHeight A.1 ≤ 1) :
    colHeight (S * A).1 ≤ 1 ∧ colHeight (S⁻¹ * A).1 ≤ 1 := by
  have ha : |A.1 0 0| ≤ 1 := by
    have := colHeight_apply A.1
    rw [this] at hA
    omega
  have hc : |A.1 1 0| ≤ 1 := by
    have := colHeight_apply A.1
    rw [this] at hA
    omega
  refine ⟨?_, ?_⟩
  · rw [colHeight_apply, S_mul_zero_zero, S_mul_one_zero, abs_neg]
    omega
  · rw [colHeight_apply, S_inv_mul_zero_zero, S_inv_mul_one_zero]
    simp only [abs_neg]
    omega

/-- The cusp stratum is closed under right multiplication by `T ^ k`: right multiplication leaves
the first column alone. -/
theorem colHeight_le_one_mul_T_zpow (A : SL(2, ℤ)) (k : ℤ) (hA : colHeight A.1 ≤ 1) :
    colHeight (A * T ^ k).1 ≤ 1 := by
  have h0 : (A * T ^ k).1 0 0 = A.1 0 0 := by
    rw [show (A * T ^ k).1 = A.1 * (T ^ k).1 from rfl, coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp
  have h1 : (A * T ^ k).1 1 0 = A.1 1 0 := by
    rw [show (A * T ^ k).1 = A.1 * (T ^ k).1 from rfl, coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]
    simp
  rw [colHeight_apply, h0, h1]
  exact hA

/-- The naive hope — that the cusp stratum is also closed under left multiplication by `T` — is
false: `[[1,0],[1,1]]` has first-column height one and `T * [[1,0],[1,1]] = [[2,1],[1,1]]` has
height two. -/
theorem colHeight_le_one_T_mul_false :
    colHeight (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ≤ 1 ∧
      ¬ colHeight (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) ≤ 1 := by
  constructor <;> decide

end ModularGroup
