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
public import Mathlib.Data.Countable.Defs
public import LeanCategories.CategoryTheory.OneCat.Classifier

@[expose] public section

/-!
# Mathlib foundation atoms — Sets, Finite, Graded, BinaryOperation

All four fields of `FoundationAtoms` are mathematical.

* `Sets` — `Type u`
* `Finite` — Mathlib `FintypeCat`
* `Graded` — `ℤ`-graded objects in `Type` with forgetful `total` (coproduct of grades)
* `BinaryOperation` — Mathlib `MagmaCat`
-/

namespace CategoryTheory.ConcreteCategory

universe w v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- Equality of morphisms `f g : X ⟶ Y` of a concrete category is decidable whenever equality of
functions `CC X → CC Y` is: a morphism is determined by its underlying function
(`ConcreteCategory.coe_ext`), so `f = g` iff `⇑f = ⇑g`. For `Type u` and a finite domain this is
Mathlib's decidable equality of functions out of a `Fintype` into a type with `DecidableEq`; in
particular, equality of global elements `1 ⟶ X` of a set `X` with decidable equality is
decidable. -/
instance decidableEqHom {X Y : C} [DecidableEq (CC X → CC Y)] : DecidableEq (X ⟶ Y) :=
  fun f g => decidable_of_iff (⇑(hom f) = ⇑(hom g)) ⟨coe_ext, fun h => h ▸ rfl⟩

end CategoryTheory.ConcreteCategory

namespace LeanCategories.Foundation.Mathlib

open CategoryTheory CategoryTheory.Limits
open LeanCategories

universe u

set_option linter.checkUnivs false

/-- Sets as types: the bundled category `Type u` (Mathlib `Cat.of (Type u)`), written as the
bundle itself and reducible, so that its objects are reducibly types. A type `X : Type u` is then
an object of `Sets` for instance resolution as well as for elaboration, and the instances Mathlib
gives `Type u` (e.g. its `ConcreteCategory` structure) apply to morphisms of `Sets`. -/
abbrev Sets : ObjCat.{u + 1, u} := ⟨Type u, inferInstance⟩

/-- `Sets` is Mathlib's bundled category of types. -/
theorem sets_eq_cat_of : Sets.{u} = Cat.of (Type u) := rfl

/-- Magmas as Mathlib's bundled magma category. -/
def Magmas : ObjCat.{u + 1, u} := Cat.of MagmaCat.{u}

/-- Finite types: the bundled category `FintypeCat` (Mathlib `Cat.of FintypeCat`), written as the
bundle itself and reducible, as `Sets` is, so that its objects are reducibly objects of
`FintypeCat` and the instances Mathlib gives `FintypeCat` (e.g. its `ConcreteCategory` structure)
apply to morphisms of `FiniteSets`. -/
abbrev FiniteSets : ObjCat.{u + 1, u} := ⟨FintypeCat.{u}, inferInstance⟩

/-- `FiniteSets` is Mathlib's bundled category of finite types. -/
theorem finiteSets_eq_cat_of : FiniteSets.{u} = Cat.of FintypeCat.{u} := rfl

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

/-- The finite classifier's forgetful functor is full: finite types are a full subcategory of
types (Mathlib `FintypeCat`, `ObjectProperty.full_ι`). -/
instance : (finite.{u}.forget.toFunctor).Full :=
  inferInstanceAs (forget FintypeCat.{u}).Full

/-- The finite classifier's forgetful functor is faithful. -/
instance : (finite.{u}.forget.toFunctor).Faithful :=
  inferInstanceAs (forget FintypeCat.{u}).Faithful

/-- Graded classifier: GradedObject ℤ (Type) → Type via coproduct of grades. -/
noncomputable def graded : Classifier Sets where
  total := GradedSets
  forget := (GradedObject.total ℤ (Type u)).toCatHom

end LeanCategories.Foundation.Mathlib
