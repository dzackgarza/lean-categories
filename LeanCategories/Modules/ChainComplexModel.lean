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

section Augmentation

variable [HasZeroObject C]

/-- The augmentation of a selected augmented object, as a chain map into the chain complex supported
in degree zero: the augmented diagram is an arrow of `Ch(C)`. -/
noncomputable def augmentation (S : AugmentedGradedObject C) :
    chainComplex S ⟶ (ChainComplex.single₀ C).obj S.point :=
  ChainComplex.ofHom
    (fun i => match i with
      | 0 => S.augment
      | _ + 1 => 0)
    (fun i => by
      match i with
      | 0 =>
        rw [chainComplex_d, zero_comp]
        exact S.comp_augment.symm
      | _ + 1 => simp only [zero_comp, comp_zero])

end Augmentation

section Cochain

open ZeroObject

variable [HasZeroObject C]

/-- The reversed index: the `ℕ`-index of a non-positive integer, one degree up. -/
lemma toNat_neg_succ {i : ℤ} (h : i ≤ -1) : (-i).toNat = (-(i + 1)).toNat + 1 := by
  have h1 : (0 : ℤ) ≤ -i := by omega
  have h2 : (0 : ℤ) ≤ -(i + 1) := by omega
  have h3 : ((-i).toNat : ℤ) = ((-(i + 1)).toNat : ℤ) + 1 := by
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    ring
  exact_mod_cast h3

/-- The reversed terms of a selected augmented object: the chosen term `P_n` sits in degree `-n`, and
every positive degree carries the zero object. -/
noncomputable def cochainTerm (S : AugmentedGradedObject C) (i : ℤ) : C :=
  if i ≤ 0 then S.term (-i).toNat else 0

/-- The reversed chosen differentials, from degree `i` to degree `i + 1`. -/
noncomputable def cochainDiff (S : AugmentedGradedObject C) (i : ℤ) :
    cochainTerm S i ⟶ cochainTerm S (i + 1) :=
  if h : i ≤ -1 then
    eqToHom (by simp [cochainTerm, show i ≤ 0 by omega, toNat_neg_succ h]) ≫
      S.diff (-(i + 1)).toNat ≫
      eqToHom (by simp [cochainTerm, show i + 1 ≤ 0 by omega])
  else 0

/-! ### The open obligation

`cochainTerm` and `cochainDiff` are the reversal's data: the chosen term `P_n` in degree `-n`, the
zero object above, and the reversed chosen differentials. What is *not* here is the assembly
`CochainComplex.of (cochainTerm S) (cochainDiff S) sq`: its obligation

`sq : ∀ i, cochainDiff S i ≫ cochainDiff S (i + 1) = 0`

reduces, for `i ≤ -2`, to

`S.diff (-(i + 1)).toNat ≫ eqToHom ⋯ ≫ S.diff (-(i + 1 + 1)).toNat ≫ eqToHom ⋯ = 0`

where the middle `eqToHom` is the cast between `cochainTerm S (i + 1)` and the `S.term` it unfolds
to. Closing it needs the two index identities `(-(i+1)).toNat = (-(i+2)).toNat + 1` (proved as
`toNat_neg_succ`) and `-(i+1+1) = -(i+2)` rewritten *inside the types of the morphisms* before
`S.comp_diff (-(i+2)).toNat` can fire; `simp` rewrites the index in the term but not in the
`eqToHom`'s endpoints, and the cast then does not cancel syntactically. -/

end Cochain

end LeanCategories.Modules
