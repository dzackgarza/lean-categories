/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Hom

/-!
# The ordinary twisted-arrow category

Kerodon 8.1.0.1 (FC17-KER-U00374).

For an ordinary category C, the twisted-arrow category is the category of
elements of the Hom bifunctor. Mathlib already owns both the Hom bifunctor
and the category-of-elements category structure, so the source construction
is exactly their composite carrier.
-/

@[expose] public section

namespace LeanCategories.CategoryTheory

universe v u

/-- The ordinary twisted-arrow category of C (FC17-KER-U00374), realized
as the category of elements of the Hom bifunctor. -/
abbrev TwistedArrow (C : Type u) [_root_.CategoryTheory.Category.{v} C] : Type (max u v) :=
  (_root_.CategoryTheory.Functor.hom C).Elements

end LeanCategories.CategoryTheory
