/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.ModularGroupPresentation

/-!
# Tests for the presentations of `SL(2, ℤ)` and `GL(2, ℤ)` (lean-categories#89)

Each declaration the presentation module proves for the two acceptance items is instantiated here on
the smallest input that decides it: the two relations on the `2 × 2` matrices, the relators in both
generator systems, the semidirect product, and the `SL` part of the adjoined presentation.

The completeness of either presentation (`ModularGroup.Sl2zPresentationComplete`,
`LeanCategories.ForMathlib.Gl2zPresentationComplete`) is a statement about all words, so no test
module can decide it; it is recorded, not tested.
-/

open scoped MatrixGroups Pointwise

open Matrix Matrix.SpecialLinearGroup

namespace LeanCategories.ForMathlib

open ModularGroup

example : S ^ 4 = 1 := S_pow_four

example : (T * ModularGroup.S) ^ 3 = ModularGroup.S ^ 2 := T_mul_S_pow_three_eq_S_sq

example : (T * ModularGroup.S) ^ 3 * ModularGroup.S ^ (-2 : ℤ) = 1 :=
  T_mul_S_pow_three_mul_zpow

example : ∀ r ∈ sl2zRelators, FreeGroup.lift sl2zGenVal r = 1 := sl2zRelators_map_one

example : Function.Surjective sl2zToGroup := sl2zToGroup_surjective

example : Group.Generators (SL(2, ℤ)) (Fin 2) := sl2zGenerators

example : (T * S : SL(2, ℤ)) ^ 6 = 1 := T_mul_S_pow_six

example : (PresentedGroup.of (rels := sl2zRelators) (0 : Fin 2)) ^ 2 ≠ 1 := of_zero_sq_ne_one

example : (PresentedGroup.of (rels := sl2zRelators) (1 : Fin 2) *
    PresentedGroup.of (rels := sl2zRelators) (0 : Fin 2)) ^ 6 = 1 :=
  of_one_mul_of_zero_pow_six

example : PresentedGroup sl2zRelators ≃* PresentedGroup sl2zAmalgamRelators := sl2zAmalgamEquiv

example : (PresentedGroup.of (rels := sl2zAmalgamRelators) (1 : Fin 2)) ^ 3 =
    (PresentedGroup.of (rels := sl2zAmalgamRelators) (0 : Fin 2)) ^ 2 := amalgamR_cube

example : GeneralLinearGroup.det eGL = -1 := det_eGL

example : eGL ^ 2 = 1 := eGL_sq

example : eGL * SpecialLinearGroup.toGL ModularGroup.S * eGL⁻¹ =
    SpecialLinearGroup.toGL ModularGroup.S⁻¹ := eGL_conj_S

example : eGL * SpecialLinearGroup.toGL ModularGroup.T * eGL⁻¹ =
    SpecialLinearGroup.toGL ModularGroup.T⁻¹ := eGL_conj_T

example : (Subgroup.closure {eGL}).IsComplement'
    (GeneralLinearGroup.det (n := Fin 2) (R := ℤ)).ker := gl2z_isComplement

example : ∀ r ∈ gl2zRelators, FreeGroup.lift gl2zGenVal r = 1 := gl2zRelators_map_one

example : Function.Surjective gl2zToGroup := gl2zToGroup_surjective

example : sl2zInGl (PresentedGroup.of (0 : Fin 2)) = PresentedGroup.of (0 : Fin 3) :=
  sl2zInGl_of 0

example : gl2zToGroup ((PresentedGroup.of (2 : Fin 3)) ^ 2) = 1 := gl2zToGroup_of_two_sq

/-! ### Component 1 of item 1's completeness: the descent, on the smallest inputs

`colHeight` is instantiated on the two generators and on `T ^ 2 * S` — the smallest matrix here of
height two, its first column being `(2, 1)` — and `colHeight_step` on `T ^ 2 * S` and on
`S⁻¹ * (T ^ 2 * S)`, whose first column `(1, -2)` forces the other branch (`|a| < |c|`). -/

example : colHeight (S : SL(2, ℤ)).1 = 1 := by decide

example : colHeight (T : SL(2, ℤ)).1 = 1 := by decide

example : colHeight ((T ^ 2 * S : SL(2, ℤ))).1 = 2 := by decide

example : 0 < colHeight (S⁻¹ : SL(2, ℤ)).1 := colHeight_pos _

example (A : SL(2, ℤ)) : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := det_entries A

example : (S⁻¹ : SL(2, ℤ)).1 = !![0, 1; -1, 0] := coe_S_inv_matrix

example (A : SL(2, ℤ)) (q : ℤ) :
    (T ^ q * A).1 0 0 = A.1 0 0 + q * A.1 1 0 := T_zpow_mul_zero_zero A q

example : |(S : SL(2, ℤ)).1 0 0| = |(S : SL(2, ℤ)).1 1 0| →
    |(S : SL(2, ℤ)).1 1 0| = 1 := abs_eq_one_of_abs_eq S

example : ∃ (ε : Fin 2) (q : ℤ) (A' : SL(2, ℤ)),
    (T ^ 2 * S : SL(2, ℤ)) = S ^ (ε : ℕ) * T ^ q * A' ∧
      colHeight A'.1 < colHeight ((T ^ 2 * S : SL(2, ℤ))).1 :=
  colHeight_step _ (by decide)

example : ∃ (ε : Fin 2) (q : ℤ) (A' : SL(2, ℤ)),
    (S⁻¹ * (T ^ 2 * S) : SL(2, ℤ)) = S ^ (ε : ℕ) * T ^ q * A' ∧
      colHeight A'.1 < colHeight ((S⁻¹ * (T ^ 2 * S) : SL(2, ℤ))).1 :=
  colHeight_step _ (by decide)

example : ∃ (u : FreeGroup (Fin 2)) (A₀ : SL(2, ℤ)),
    colHeight A₀.1 ≤ 1 ∧ (T ^ 2 * S : SL(2, ℤ)) = FreeGroup.lift sl2zGenVal u * A₀ :=
  exists_word_mul_colHeight_le_one 2 _ (by decide)

example (B : SL(2, ℤ)) :
    ∃ u : FreeGroup (Fin 2), colHeight (FreeGroup.lift sl2zGenVal u * B).1 ≤ 1 :=
  exists_lift_mul_colHeight_le_one B

/-! ### Component 2's arithmetic half, on the smallest inputs

The eight lifts are checked on their first columns — `cuspLift_five` is the one whose first column
is `(-1, -1)` — right multiplication by `T` is checked to leave `colHeight` alone, and the
classification is checked in both directions: `S` (height one) must be one of the eight cosets, and
each of the eight times a power of `T` must have height one. -/

example : (cuspLift 2).1 = !![0, -1; 1, 0] := cuspLift_two

example : (cuspLift 5).1 = !![-1, 0; -1, -1] := cuspLift_five

example : colHeight (cuspLift 4).1 = 1 := colHeight_cuspLift 4

example : colHeight ((cuspLift 6).1) = 1 := colHeight_cuspLift 6

example : colHeight ((S * T ^ (3 : ℤ) : SL(2, ℤ))).1 = colHeight (S : SL(2, ℤ)).1 :=
  colHeight_mul_T_zpow S 3

example : ((cuspLift 4 * T ^ (3 : ℤ) : SL(2, ℤ))).1 = !![1, 3; 1, 4] := by decide

example : ∃ (i : Fin 8) (b : ℤ), (S : SL(2, ℤ)) = cuspLift i * T ^ b :=
  (colHeight_le_one_iff S).mp (by decide)

example : ∃ (i : Fin 8) (b : ℤ), ((-S * T ^ (5 : ℤ) : SL(2, ℤ))) = cuspLift i * T ^ b :=
  (colHeight_le_one_iff _).mp (by decide)

example : colHeight ((cuspLift 5 * T ^ (2 : ℤ) : SL(2, ℤ))).1 ≤ 1 :=
  (colHeight_le_one_iff _).mpr ⟨5, 2, rfl⟩

example : firstColumn (S : SL(2, ℤ)) = (0, 1) := by decide

example : firstColumn ((S * T ^ (9 : ℤ) : SL(2, ℤ))) = firstColumn (S : SL(2, ℤ)) :=
  firstColumn_mul_T_zpow S 9

example : (cuspLift 4 * T ^ (3 : ℤ) : SL(2, ℤ)) ≠ cuspLift 4 * T ^ (4 : ℤ) := by decide

example : (cuspLift 3 * T ^ (2 : ℤ) : SL(2, ℤ)) ≠ cuspLift 5 * T ^ (2 : ℤ) := by decide

example (h : (cuspLift 4 * T ^ (3 : ℤ) : SL(2, ℤ)) = cuspLift 4 * T ^ (3 : ℤ)) :
    ((4, (3 : ℤ)) : Fin 8 × ℤ) = ((4, (3 : ℤ)) : Fin 8 × ℤ) :=
  cuspLift_pair_injective h

example : ∃! p : Fin 8 × ℤ, (S : SL(2, ℤ)) = cuspLift p.1 * T ^ p.2 :=
  (colHeight_le_one_iff_existsUnique S).mp (by decide)

example : ∃! p : Fin 8 × ℤ, ((-S * T ^ (5 : ℤ) : SL(2, ℤ))) = cuspLift p.1 * T ^ p.2 :=
  (colHeight_le_one_iff_existsUnique _).mp (by decide)

/-! ### Item 1 as an amalgam: the pushed identification, on the smallest inputs -/

example : cyclicGen 4 ^ 4 = 1 := cyclicGen_pow 4

example : cyclicGen 6 ^ 6 = 1 := cyclicGen_pow 6

example : cyclicTwoToFour (cyclicGen 2) = cyclicGen 4 ^ 2 := cyclicTwoToFour_gen

example : cyclicTwoToSix (cyclicGen 2) = cyclicGen 6 ^ 3 := cyclicTwoToSix_gen

example : cyclicFourToAmalgam (cyclicGen 4) = PresentedGroup.of (0 : Fin 2) :=
  cyclicFourToAmalgam_gen

example : (PresentedGroup.of (rels := sl2zAmalgamRelators) (1 : Fin 2)) ^ 6 = 1 :=
  amalgamR_pow_six

example : (Monoid.PushoutI.of (φ := amalgamMap) true (cyclicGen 6)) ^ 3 =
    (Monoid.PushoutI.of (φ := amalgamMap) false (cyclicGen 4)) ^ 2 := pushout_gen_six_cube

example : PresentedGroup sl2zAmalgamRelators ≃* AmalgamPushout := amalgamPushoutEquiv

example : pushoutToAmalgam (Monoid.PushoutI.of (φ := amalgamMap) false (cyclicGen 4)) =
    PresentedGroup.of (0 : Fin 2) := by
  simp only [pushoutToAmalgam, Monoid.PushoutI.lift_of]
  exact cyclicFourToAmalgam_gen

/-! ### The stabilizer of the cusp `∞`: `T` fixes it, `S` does not -/

example : (T : SL(2, ℤ)).1 1 0 = 0 := by decide

example : ∃ b : ℤ, (T ^ (5 : ℤ) : SL(2, ℤ)) = T ^ b ∨
    (T ^ (5 : ℤ) : SL(2, ℤ)) = -(T ^ b) :=
  eq_T_zpow_or_neg_of_cusp_fixed _ (by decide)

example : ∃ b : ℤ, (-1 : SL(2, ℤ)) = T ^ b ∨ (-1 : SL(2, ℤ)) = -(T ^ b) :=
  eq_T_zpow_or_neg_of_cusp_fixed _ (by decide)

example : (S : SL(2, ℤ)).1 1 0 = 1 := by decide

example : colHeight (S : SL(2, ℤ)).1 = 1 := colHeight_letters.1

example : colHeight ((T * S : SL(2, ℤ)) ^ 5).1 = 1 := colHeight_letters.2.2.2.2.2

/-! ### The column dictionary, on the smallest inputs -/

example : col (S : SL(2, ℤ)) 0 = (0, 1) := by decide

example : col ((S * S : SL(2, ℤ))) 0 = col (S : SL(2, ℤ)) 1 :=
  (col_mul_S S).1

example : col ((S * S : SL(2, ℤ))) 1 = -col (S : SL(2, ℤ)) 0 :=
  (col_mul_S S).2

example : col ((T * S ^ 2 : SL(2, ℤ))) 0 = -col (T : SL(2, ℤ)) 0 :=
  (col_mul_S_sq T).1

example : col ((T * S : SL(2, ℤ))) 0 = col (1 : SL(2, ℤ)) 0 + col (1 : SL(2, ℤ)) 1 :=
  (col_mul_R 1).1

example : edgeLines ((T : SL(2, ℤ)) * S) = edgeLines (T : SL(2, ℤ)) := edgeLines_mul_S T

example : triangleLines ((1 : SL(2, ℤ)) * (T * S)) = triangleLines (1 : SL(2, ℤ)) :=
  triangleLines_mul_R 1

example : (col (1 : SL(2, ℤ)) 0 + col (1 : SL(2, ℤ)) 1) ∈ triangleLines (1 : SL(2, ℤ)) := by
  simp [triangleLines]

example : (col (1 : SL(2, ℤ)) 0) ∈ edgeLines (1 : SL(2, ℤ)) := by
  simp [edgeLines]

example : fdet ((1 : ℤ), 0) ((0 : ℤ), 1) = 1 := by decide

example : ∃ ε₁ ε₂ : ℤ, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
    ((1 : ℤ), 1) = (ε₁ * (1 : ℤ) + ε₂ * 0, ε₁ * 0 + ε₂ * 1) :=
  eq_pm_of_adjacent (1, 0) (0, 1) (1, 1) (by decide) (by decide) (by decide)

example : ∃ ε₁ ε₂ : ℤ, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
    ((1 : ℤ), -1) = (ε₁ * (1 : ℤ) + ε₂ * 0, ε₁ * 0 + ε₂ * 1) :=
  eq_pm_of_adjacent (1, 0) (0, 1) (1, -1) (by decide) (by decide) (by decide)

end LeanCategories.ForMathlib
