/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpE8FoldNotRoot

/-!
# Probe: the folded `E₈` root of `T_dP` is not a root of `T_dP`

AEGS **printed p. 12**: `div(α^I) ≠ 2` in `T_dP`. The probes below do not restate that; they use it.

* the fold of the first `E₈` simple root has an odd pairing, so no `div = 2`;
* it is therefore outside the roots of `T_dP`;
* as a cross-check that the block arithmetic is not slipped a sign, the pairing of two adjacent
  *folds* is `2` — twice the single-block entry, as `tdpFoldedE8Root_pairing` predicts.

The last one is the guard against the failure mode this file could have had: an odd single-block
entry that is really a sign error would still pass a `≠ 0` test, but not the two-fold consistency.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The fold has an odd ambient pairing. -/
example :
    ¬ ∀ y : tdpFiniteLattice.obj.obj.carrier,
        (2 : ℤ) ∣ tdpFiniteLattice.obj.obj.pairing
          (foldedVector tdpIsometry (tdpE8Root 0)) y :=
  tdpFoldedE8Root_not_two_dvd

/-- So it is not a root of `T_dP`. -/
example :
    foldedVector tdpIsometry (tdpE8Root 0) ∉ negativeReflectiveRoots tdpFiniteLattice :=
  tdpFoldedE8Root_not_mem_negativeReflectiveRoots

/-- Cross-check: two adjacent folds pair by `2`, twice the single-block entry. -/
example :
    tdpFiniteLattice.obj.obj.pairing (foldedVector tdpIsometry (tdpE8Root 0))
      (foldedVector tdpIsometry (tdpE8Root 2)) = 2 := by
  rw [tdpFoldedE8Root_pairing, e8GramMatrix_eq]
  decide

end LeanCategories.Lattices.Valued
