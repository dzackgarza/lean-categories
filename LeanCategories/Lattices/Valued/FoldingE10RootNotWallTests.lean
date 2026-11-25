/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingE10RootNotWall

/-!
# Probe for the `E₁₀(2)` counterexample, on the smallest input that decides it

The counterexample is a single vector, `α₁ + α₃`. The probe reads off the two facts that matter —
negative square, and no simple root is parallel to it at `i = 1`, the index whose coordinate is `1` —
and the combined statement, which is what the `hcomplete` caveat in `FoldingInvariantChamber.lean`
and `FoldingInvariantConverse.lean` cites.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

/-- `α₁ + α₃` has negative square. -/
example : e10FiniteLattice.obj.obj.pairing (e10Root 1 + e10Root 3)
    (e10Root 1 + e10Root 3) = -4 :=
  e10_reflected_root_square

/-- It is not `k • α₁` for any nonzero `k`. -/
example (k : ℤ) (hk : k ≠ 0) : e10Root 1 + e10Root 3 ≠ k • e10Root 1 := by
  intro h
  exact e10_reflected_root_not_multiple ⟨k, 1, hk, h⟩

/-- The three facts together. -/
example : IsReflectiveRoot e10FiniteLattice.obj (e10Root 1 + e10Root 3) :=
  e10_root_not_multiple_of_wall.1

#print axioms e10_root_not_multiple_of_wall

end LeanCategories.Lattices.Valued
