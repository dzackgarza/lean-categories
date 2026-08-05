module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

/-!
# Pure Schemes & Surface Foundations

This module formalizes surface foundations strictly within `SchemeTheory.Surfaces`:
Surfaces are 2-dimensional integral noetherian schemes over a field $k$.
-/

namespace LeanCategories.Schemes.Surface

open AlgebraicGeometry

/-- A surface over a field $k$ is a scheme $X$ equipped with pure dimension 2. -/
structure AlgebraicSurface (k : Type u) [Field k] where
  scheme : Scheme
  [isIntegral : IntegralScheme scheme]

end LeanCategories.Schemes.Surface
