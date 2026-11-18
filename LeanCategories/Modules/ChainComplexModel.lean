/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Single
public import LeanCategories.Modules.AugmentedObjects

/-!
# The chain-complex model of a selected augmented object

FOUNDATIONS.md, Definitions 76.1 and 77.1, and dzackgarza/lean-categories#62.

Definition 76.1's sequence `... --> P_1 --> P_0 --> X` is a selected diagram; Definition 77.1
records that `Ch(C)` exists once `C` is additive. `chainComplex S` is that object: the chosen terms
and differentials of `S`, as a `ChainComplex C ℕ`. `augmentation S` is the augmentation as a chain
map into the complex supported in degree zero, so the augmented diagram is an arrow of `Ch(C)`.

## What is not built here

This Mathlib pin develops the mapping cone and the triangulated structure only for
`CochainComplex C ℤ` (see `LeanCategories.Modules.StableEnhancement`). The `ℕ`-indexed chain
complex of a selected object therefore has no cofiber triangle in this file: that needs the index
reversal `X i := S.term (-i)` at `i ≤ 0`, `0` above, with its casts, and a decision about which
indexing the downstream development standardizes on.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Modules

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The chain complex of a selected augmented object: its chosen terms and chosen differentials. -/
noncomputable def chainComplex (S : AugmentedGradedObject C) : ChainComplex C ℕ :=
  ChainComplex.of S.term S.diff S.comp_diff

/-- The chosen term in each degree is the complex's term there. -/
@[simp]
theorem chainComplex_X (S : AugmentedGradedObject C) : (chainComplex S).X = S.term := by
  simp [chainComplex]

/-- The chosen differential out of degree `n + 1` is the complex's differential there. -/
@[simp]
theorem chainComplex_d (S : AugmentedGradedObject C) (n : ℕ) :
    (chainComplex S).d (n + 1) n = S.diff n := by
  simp [chainComplex]

end LeanCategories.Modules
