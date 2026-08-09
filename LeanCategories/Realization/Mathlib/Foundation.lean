/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Semigrp.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import LeanCategories.Model.Atomic

@[expose] public section

/-!
# Mathlib foundation atoms — Sets, Finite, Graded, BinaryOperation

All four fields of `FoundationAtoms` are mathematical.

* `Sets` — `Type u`
* `Finite` — Mathlib `FintypeCat`
* `Graded` — `ℤ`-graded objects in `Type` with forgetful `total` (coproduct of grades)
* `BinaryOperation` — Mathlib `MagmaCat`
-/

namespace LeanCategories.Realization.Mathlib

open CategoryTheory CategoryTheory.Limits
open LeanCategories

universe u

set_option linter.checkUnivs false

/-- Sets as types. -/
def Sets : ObjCat.{u + 1, u} := Cat.of (Type u)

/-- Magmas as Mathlib's bundled magma category. -/
def Magmas : ObjCat.{u + 1, u} := Cat.of MagmaCat.{u}

/-- Finite types. -/
def FiniteSets : ObjCat.{u + 1, u} := Cat.of FintypeCat.{u}

/-- ℤ-graded sets (graded objects in `Type`). -/
def GradedSets : ObjCat.{u + 1, u} := Cat.of (GradedObject ℤ (Type u))

/-- BinaryOperation classifier: MagmaCat → Type. -/
noncomputable def binaryOperation : Classifier Sets where
  total := Magmas
  forget := (forget MagmaCat.{u}).toCatHom

/-- Finite classifier: FintypeCat → Type. -/
noncomputable def finite : Classifier Sets where
  total := FiniteSets
  forget := (forget FintypeCat.{u}).toCatHom

/-- Graded classifier: GradedObject ℤ (Type) → Type via coproduct of grades. -/
noncomputable def graded : Classifier Sets where
  total := GradedSets
  forget := (GradedObject.total ℤ (Type u)).toCatHom

/-- Complete foundation atoms. -/
noncomputable def foundationAtoms : FoundationAtoms.{u + 1, u} where
  Sets := Sets
  finite := finite
  graded := graded
  binaryOperation := binaryOperation

example : foundationAtoms.binaryOperation.total = Magmas := rfl
example : foundationAtoms.finite.total = FiniteSets := rfl
example : foundationAtoms.graded.total = GradedSets := rfl

end LeanCategories.Realization.Mathlib
