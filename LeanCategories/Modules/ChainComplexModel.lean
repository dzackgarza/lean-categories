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

/-- The reversed terms: the chosen term `P_0` sits in degree `0`, `P_{n+1}` in degree `-(n+1)`, and
every positive degree carries the zero object. -/
noncomputable def cochainTerm (S : AugmentedGradedObject C) : ℤ → C
  | Int.ofNat 0 => S.term 0
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc m => S.term (m + 1)

/-- The reversed chosen differentials: in a negative degree the chosen differential of `S`, and zero
from degree `0` upwards. -/
noncomputable def cochainDiff (S : AugmentedGradedObject C) (i : ℤ) :
    cochainTerm S i ⟶ cochainTerm S (i + 1) :=
  match i with
  | Int.ofNat 0 => 0
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc 0 => S.diff 0
  | Int.negSucc (k + 1) => S.diff (k + 1)

/-- The `ℤ`-indexed cochain complex of a selected augmented object: the chain complex read with its
degrees reversed, so that the mapping-cone and triangulated API of this Mathlib pin — which exists
only for `CochainComplex C ℤ` — applies to it. -/
noncomputable def cochainComplexOf (S : AugmentedGradedObject C) : CochainComplex C ℤ :=
  CochainComplex.of (cochainTerm S) (cochainDiff S) (by
    intro i
    match i with
    | Int.ofNat 0 => exact zero_comp
    | Int.ofNat (_ + 1) => exact zero_comp
    | Int.negSucc 0 => exact comp_zero
    | Int.negSucc (k + 1) =>
      match k with
      | 0 => exact S.comp_diff 0
      | j + 1 => exact S.comp_diff (j + 1))

/-! ### The open obligation (cochain level)

`cochainAugmentation S : cochainComplexOf S ⟶ single₀Cochain S.point` is not here. Its commutation
fails for a type-checking reason: with the components defined by `match` on the degree, the goal
is not type-correct under implicit transparency, so

`simp only [zero_comp, comp_zero]`

makes no progress (`LeanCategories/Modules/ChainComplexModel.lean` failed at the degree-zero branch),
and `S.comp_augment` cannot be applied through the unreduced `single₀Cochain.match_1` motive. The
chain-level `augmentation` above avoids this by using `ChainComplex.single₀`, whose object and
differential are given by structure fields rather than by a `match` on `ℤ`. -/

end Cochain

end LeanCategories.Modules
