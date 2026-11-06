/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SheafPresheafComparison

/-! # Card: `LeanCategories.Homological.noContinuousGlobalLog`

source: Weibel, *An Introduction to Homological Algebra* (1994), §1.6 (FC05-C01-U057).

Published copy of a result from `LeanCategories.Homological.SheafPresheafComparison`; the definition module keeps the original declaration, this file restates it, and the platform submission replaces the delegated proof with `by sorry`.
-/

@[expose] public section

namespace LeanCategories.Cards

open LeanCategories.Homological

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
universe u
open LeanCategories.Homological

/-- There is no continuous logarithm defined on all of `ℂˣ`. -/
theorem LeanCategories_Homological_noContinuousGlobalLog :
    ¬ ∃ l : C(ℂˣ, ℂ),
      ∀ z : ℂˣ, complexExpAddHom (l z) = Additive.ofMul z :=
  LeanCategories.Homological.noContinuousGlobalLog


end LeanCategories.Cards
