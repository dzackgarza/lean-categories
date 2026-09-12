/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SplitComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-!
# k-split complexes and augmented resolutions

Weibel, *An Introduction to Homological Algebra* (1994), Definition 8.7.7,
pp. 286--293 (FC05-C08-U083).

For a `k`-algebra `R`, a chain complex of `R`-modules is `k`-split when its
underlying complex of `k`-modules is split exact.  An augmented resolution is
`k`-split when the augmented underlying `k`-complex is split exact.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe u v

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]

/-- Restriction of scalars from `R`-modules to `k`-modules. -/
noncomputable abbrev kRestriction : ModuleCat R ⥤ ModuleCat k :=
  ModuleCat.restrictScalars (algebraMap k R)

/-- The underlying `k`-chain complex of an `R`-chain complex. -/
noncomputable def restrictChainComplex
    (P : ChainComplex (ModuleCat R) ℕ) : ChainComplex (ModuleCat k) ℕ :=
  ((kRestriction k R).mapHomologicalComplex (ComplexShape.down ℕ)).obj P

/-- Weibel's `k`-split condition for a chain complex. -/
def IsKSplitComplex (P : ChainComplex (ModuleCat R) ℕ) : Prop :=
  IsSplitExact (restrictChainComplex k R P)

/-- A realization of the underlying augmented `k`-complex of
`P_* → M`.  Its degree `n≥0` terms are the restrictions of `P_n`, degree `-1`
is the restriction of `M`, and all lower degrees vanish.  Requiring this
realization to be split exact is exactly Weibel's augmented `k`-split
condition. -/
structure KSplitAugmentedResolution
    (P : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (ε : P.X 0 ⟶ M) where
  /-- The augmented underlying `k`-complex. -/
  complex : ChainComplex (ModuleCat k) ℤ
  /-- The augmented complex is split exact over `k`. -/
  splitExact : IsSplitExact complex
  /-- Degree `n≥0` identifies with the restricted `P_n`. -/
  degreeIso : ∀ n : ℕ,
    complex.X (n : ℤ) ≅ (kRestriction k R).obj (P.X n)
  /-- Degree `-1` identifies with the restricted augmentation target. -/
  augmentationIso :
    complex.X (-1 : ℤ) ≅ (kRestriction k R).obj M
  /-- The nonnegative differentials are the restricted differentials of `P`. -/
  differential : ∀ n : ℕ,
    complex.d ((n + 1 : ℕ) : ℤ) (n : ℤ) ≫ (degreeIso n).hom =
      (degreeIso (n + 1)).hom ≫ (kRestriction k R).map (P.d (n + 1) n)
  /-- The differential from degree zero to degree `-1` is the restricted
  augmentation map. -/
  augmentationDifferential :
    complex.d (0 : ℤ) (-1 : ℤ) ≫ augmentationIso.hom =
      (degreeIso 0).hom ≫ (kRestriction k R).map ε
  /-- There are no further negative terms. -/
  zeroBelow : ∀ z : ℤ, z < -1 → IsZero (complex.X z)

/-- An augmented resolution is `k`-split when such a split-exact underlying
augmented `k`-complex exists. -/
def IsKSplitAugmentedResolution
    (P : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (ε : P.X 0 ⟶ M) : Prop :=
  Nonempty (KSplitAugmentedResolution k R P M ε)

end LeanCategories.Homological
