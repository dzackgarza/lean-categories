/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Cleavages of ordinary fibrations

Definition-level realization of Kerodon FC17-KER-U02048 (tag 01S7).

For a functor `p : E ⥤ C`, a cleavage chooses, for every base arrow
`f : X ⟶ Y` and every object of the fiber over `Y`, a cartesian lift
of `f` with that codomain.

No identity, composition, normalization, or split-cleavage laws are part of
Kerodon's definition and none are imposed here.
-/

@[expose] public section

namespace LeanCategories.CategoryTheory

open _root_.CategoryTheory

universe v₁ v₂ u₁ u₂

variable
  {C : Type u₁} {E : Type u₂}
  [Category.{v₁} C] [Category.{v₂} E]

/-- A chosen cartesian lift of `f : X ⟶ Y` with prescribed codomain
`y` in the fiber over `Y`. -/
structure CartesianLift
    (p : E ⥤ C) {X Y : C} (f : X ⟶ Y) (y : p.Fiber Y) where
  obj : E
  hom : obj ⟶ y.1
  isCartesian : p.IsCartesian f hom

/-- Kerodon 01S7: a cleavage of `p` is a choice of cartesian lift for
every base arrow and every object over its codomain. -/
structure Cleavage (p : E ⥤ C) where
  lift {X Y : C} (f : X ⟶ Y) (y : p.Fiber Y) :
    CartesianLift p f y

end LeanCategories.CategoryTheory
