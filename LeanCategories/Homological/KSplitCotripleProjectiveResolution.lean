/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CotripleProjective
public import LeanCategories.Homological.KSplitComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# k-split cotriple-projective resolutions

Weibel, *An Introduction to Homological Algebra* (1994), §8.7, pp. 286--293
(FC05-C08-U085).

A `k`-split cotriple-projective resolution of `M` is an augmented resolution
`P_* → M` whose terms are projective relative to the chosen cotriple and whose
augmented underlying `k`-complex is split exact.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe u v

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]

/-- Weibel's `k`-split `T`-projective resolution data. -/
structure KSplitCotripleProjectiveResolution
    (T : Comonad (ModuleCat R)) (M : ModuleCat R) where
  /-- The resolving chain complex. -/
  complex : ChainComplex (ModuleCat R) ℕ
  /-- Its augmentation to `M`, expressed as a morphism to the degree-zero
  single complex. -/
  augmentation : complex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M
  /-- Chosen homology objects for the resolving complex. -/
  [hasHomology : ∀ n : ℕ, complex.HasHomology n]
  /-- It is genuinely a resolution. -/
  quasiIso : QuasiIso augmentation
  /-- Every term is projective relative to the cotriple. -/
  cotripleProjective : ∀ n : ℕ, T.IsCotripleProjective (complex.X n)
  /-- The augmented resolution is split exact after restriction to `k`. -/
  kSplit : IsKSplitAugmentedResolution k R complex M (augmentation.f 0)

end LeanCategories.Homological
