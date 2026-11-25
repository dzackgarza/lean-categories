/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SheafPresheafComparison

/-! # Card: `LeanCategories.Homological.expSheafHom_isLocallySurjective`

source: Weibel, *An Introduction to Homological Algebra* (1994), §1.6 (FC05-C01-U057).

Published copy of a result of `LeanCategories.Homological.SheafPresheafComparison`. The definition module keeps the original declaration; this file states it and delegates the proof, and the platform submission replaces that proof term with `by sorry`.
-/

namespace LeanCategories.Cards

open LeanCategories.Homological

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
universe u

/-- The exponential morphism of continuous-function sheaves is locally surjective. -/
theorem LeanCategories_Homological_expSheafHom_isLocallySurjective : ∀ (X : TopCat.{0}),
    TopCat.Presheaf.IsLocallySurjective (expSheafHom X).hom :=
  LeanCategories.Homological.expSheafHom_isLocallySurjective

end LeanCategories.Cards
