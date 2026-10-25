/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.ShiftedDualNumbers
public meta import LeanCategories.Catalogue.Semantics.Algebra.ShiftedDualNumbers

@[expose] public section

namespace CasCatalogue.Algebra.ShiftedDualNumberTests
open ShiftedDualNumbers

example : shiftedComparison.hom (AdjoinRoot.root sourcePolynomial) =
    AdjoinRoot.root targetPolynomial + 1 := by run_tac shiftedEvaluation

example : shiftedComparison.inv (AdjoinRoot.root targetPolynomial) =
    AdjoinRoot.root sourcePolynomial - 1 := by run_tac shiftedEvaluation

example : shiftedComparison.hom ((AdjoinRoot.root sourcePolynomial) ^ 3 + 2) =
    (AdjoinRoot.root targetPolynomial + 1) ^ 3 + 2 := by run_tac shiftedEvaluation

example (c : ℚ) : shiftedComparison.hom (sourceConstants c) = targetConstants c := by
  run_tac shiftedEvaluation

example (c : ℚ) : shiftedComparison.inv (targetConstants c) = sourceConstants c := by
  run_tac shiftedEvaluation

/-- The selected action cannot silently be replaced by the target's chosen generator. -/
example : shiftedComparison.hom (AdjoinRoot.root sourcePolynomial) ≠
    AdjoinRoot.root targetPolynomial := by
  fail_if_success
    have : shiftedComparison.hom (AdjoinRoot.root sourcePolynomial) =
        AdjoinRoot.root targetPolynomial := by run_tac shiftedEvaluation
  exact shiftedComparison_root_ne

/-- The defining square-zero relation is transported along the actual comparison. -/
example : (AdjoinRoot.root targetPolynomial + 1) ^ 2 = 0 :=
  target_shifted_root_square

end CasCatalogue.Algebra.ShiftedDualNumberTests
