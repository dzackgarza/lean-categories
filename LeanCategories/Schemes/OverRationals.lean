/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Schemes over `ℚ`

`Sch/ℚ := Over (Spec ℚ)`, the category of schemes over `Spec ℚ`. The spectrum of a `ℚ`-algebra `A`
is an object of it through `Spec(ℚ → A)` (`specOverRationals`).
-/

open CategoryTheory AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- Schemes over `Spec ℚ`. -/
abbrev SchemesOverRationals : Type 1 := Over (Spec (CommRingCat.of ℚ))

/-- `Spec A` over `Spec ℚ`, for a commutative `ℚ`-algebra `A`. -/
noncomputable def specOverRationals (A : Type) [CommRing A] [Algebra ℚ A] : SchemesOverRationals :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))

end LeanCategories.Schemes
