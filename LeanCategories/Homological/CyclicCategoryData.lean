/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Formal morphism data for Connes' cyclic category

Weibel, *An Introduction to Homological Algebra* (1994), Definition 9.6.3,
pp. 330--337 (FC05-C09-U084).

The definition presents a morphism `[n] → [m]` by a monotone map together
with a power of the cyclic generator.  The proposition that these data carry
the cyclic-category composition and category laws is theorem-layer content.
-/

@[expose] public section

namespace LeanCategories.Homological

/-- The formal pair `(α,t^i)` used in Weibel's definition of the cyclic category. -/
structure CyclicMorphismData (n m : ℕ) where
  /-- The underlying monotone simplex-category map. -/
  alpha : Fin (n + 1) →o Fin (m + 1)
  /-- The exponent `0 ≤ i ≤ n` of the cyclic generator at the source. -/
  power : Fin (n + 1)

end LeanCategories.Homological
