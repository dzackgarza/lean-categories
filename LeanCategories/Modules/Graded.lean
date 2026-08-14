/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Category.ModuleCat.Basic

@[expose] public section

/-!
# Graded module categories

Mathlib's `CategoryTheory.GradedObject` already provides the category of graded
objects and its degree evaluation functors. This file exposes that construction
for `ModuleCat` without defining a second graded-module category.
-/

namespace LeanCategories.Modules.Mathlib

open CategoryTheory

universe u v

/-- The category of `ι`-graded `R`-modules, using Mathlib's graded-object category. -/
abbrev GradedModuleCat (R : Type u) [Ring R] (ι : Type v) :=
  GradedObject ι (ModuleCat.{v} R)

/-- Evaluation at degree `i` for graded `R`-modules. -/
abbrev gradedModuleEval (R : Type u) [Ring R] (ι : Type v) (i : ι) :
    GradedModuleCat R ι ⥤ ModuleCat.{v} R :=
  GradedObject.eval i

end LeanCategories.Modules.Mathlib
