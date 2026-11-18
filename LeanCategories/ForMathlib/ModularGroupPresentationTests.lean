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

end LeanCategories.ForMathlib
