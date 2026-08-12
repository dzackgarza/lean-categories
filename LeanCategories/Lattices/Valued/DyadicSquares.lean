/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

namespace LeanCategories.Lattices.Valued

open PadicInt

section Dyadic

/-- Two has dyadic norm one half. -/
theorem norm_two_padicIntTwo : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  have h : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_cast
  rw [← h, norm_p]
  norm_num

/-- An approximate square root within `1/4` forces a dyadic unit to be a square.

This is Hensel's lemma applied to `X ^ 2 - u`. At the prime two the derivative `2 * r`
has norm `1/2`, so the Hensel bound is `‖r * r - u‖ < 1/4` rather than `< 1`. -/
theorem isSquare_of_sub_sq_norm_lt {u r : ℤ_[2]} (hu : ‖u‖ = 1)
    (h : ‖r * r - u‖ < 1 / 4) : IsSquare u := by
  have hr : ‖r‖ = 1 := by
    rcases eq_or_lt_of_le (norm_le_one r) with h1 | hlt
    · exact h1
    · exfalso
      have hr2 : ‖r * r‖ < 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg r]
      have hlt1 : ‖u‖ < 1 := by
        have hsum : u = r * r + -(r * r - u) := by ring
        rw [hsum]
        exact norm_lt_one_add hr2 (by rw [norm_neg]; linarith)
      exact absurd hu (ne_of_lt hlt1)
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C u with hF
  have hval : F.aeval r = r * r - u := by simp [hF, pow_two]
  have hderiv : F.derivative.aeval r = 2 * r := by
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, map_mul, map_pow, Polynomial.aeval_X]
    norm_num
  have hnorm : ‖F.aeval r‖ < ‖F.derivative.aeval r‖ ^ 2 := by
    rw [hval, hderiv, norm_mul, norm_two_padicIntTwo, hr]
    norm_num
    linarith
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 - u = 0 := by simpa [hF] using hz
  exact ⟨z, by linear_combination -hz2⟩

/-- A dyadic integer congruent to one modulo eight is a square. -/
theorem isSquare_of_toZModPow_three_eq_one {u : ℤ_[2]} (h : toZModPow 3 u = 1) :
    IsSquare u := by
  have hmem : (1 : ℤ_[2]) - u ∈ RingHom.ker (toZModPow (p := 2) 3) := by
    simp [RingHom.mem_ker, h]
  rw [ker_toZModPow] at hmem
  have hle := (norm_le_pow_iff_mem_span_pow ((1 : ℤ_[2]) - u) 3).mpr hmem
  norm_num at hle
  have hu : ‖u‖ = 1 := by
    rcases eq_or_lt_of_le (norm_le_one u) with h1 | hlt
    · exact h1
    · exfalso
      have hone : ‖(1 : ℤ_[2])‖ < 1 := by
        have hsum : (1 : ℤ_[2]) = (1 - u) + u := by ring
        rw [hsum]
        exact norm_lt_one_add (by linarith) hlt
      simp at hone
  refine isSquare_of_sub_sq_norm_lt hu (r := 1) ?_
  rw [one_mul]
  linarith

/-- Every invertible residue modulo eight squares to one. -/
theorem mul_self_eq_one_of_exists_inv_zmod_eight {x : ZMod 8} (hx : ∃ y, x * y = 1) :
    x * x = 1 := by
  revert x
  decide

/-- A dyadic unit that is a square is congruent to one modulo eight. -/
theorem toZModPow_three_eq_one_of_isSquare {u : ℤ_[2]} (hu : ‖u‖ = 1) (h : IsSquare u) :
    toZModPow 3 u = 1 := by
  obtain ⟨v, rfl⟩ := h
  have hv : ‖v‖ = 1 := by
    have hmul : ‖v‖ * ‖v‖ = 1 := by rw [← norm_mul]; exact hu
    nlinarith [norm_nonneg v]
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp (isUnit_iff.mpr hv)
  rw [map_mul]
  refine mul_self_eq_one_of_exists_inv_zmod_eight ⟨toZModPow 3 w, ?_⟩
  rw [← map_mul, hw, map_one]

/-- A dyadic unit is a square exactly when it is congruent to one modulo eight. -/
theorem isSquare_iff_toZModPow_three_eq_one {u : ℤ_[2]} (hu : ‖u‖ = 1) :
    IsSquare u ↔ toZModPow 3 u = 1 :=
  ⟨toZModPow_three_eq_one_of_isSquare hu, isSquare_of_toZModPow_three_eq_one⟩

end Dyadic

end LeanCategories.Lattices.Valued
