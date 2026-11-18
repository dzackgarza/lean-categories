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

end LeanCategories.ForMathlib
