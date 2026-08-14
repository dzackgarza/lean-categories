/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.Countable.Defs
public import Mathlib.Logic.Encodable.Basic

@[expose] public section

/-!
# Finite, countable, and enumerated sets

This file uses Mathlib's `Finite`, `Countable`, and `Encodable` notions.
Countable sets form a full subcategory of types. An enumerated set retains a
chosen `Encodable` structure, while its morphisms are ordinary functions.
-/

open CategoryTheory

universe u

namespace LeanCategories.Foundation

/-- The category of countable types and all functions between them. -/
abbrev CountableSetCat :=
  ObjectProperty.FullSubcategory (C := Type u) Countable

namespace CountableSetCat

/-- Regard a type with a Mathlib `Countable` instance as a countable set. -/
abbrev of (X : Type u) [Countable X] : CountableSetCat.{u} :=
  ⟨X, inferInstance⟩

/-- The canonical inclusion of countable sets into sets. -/
abbrev incl : CountableSetCat.{u} ⥤ Type u :=
  ObjectProperty.ι _

end CountableSetCat

/-- A type equipped with a chosen Mathlib `Encodable` structure. -/
structure EnumeratedSetCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The chosen encoding into natural numbers. -/
  [enumeration : Encodable carrier]

attribute [instance] EnumeratedSetCat.enumeration

namespace EnumeratedSetCat

instance : CoeSort EnumeratedSetCat.{u} (Type u) :=
  ⟨carrier⟩

/-- Regard a type with a chosen Mathlib `Encodable` instance as an enumerated set. -/
abbrev of (X : Type u) [Encodable X] : EnumeratedSetCat.{u} :=
  ⟨X⟩

instance : Category EnumeratedSetCat.{u} :=
  inferInstanceAs (Category (InducedCategory (Type u) carrier))

/-- Forget the chosen enumeration. -/
def forget : EnumeratedSetCat.{u} ⥤ Type u where
  obj X := X.carrier
  map f := f.hom

end EnumeratedSetCat

/-- Every finite set is countable. -/
def finiteToCountable : FintypeCat.{u} ⥤ CountableSetCat.{u} :=
  ObjectProperty.lift (Countable : ObjectProperty (Type u)) FintypeCat.incl fun X ↦ by
    change Countable X.obj
    exact @Finite.to_countable X.obj X.property

/-- Forget the chosen enumeration and retain the induced countability proof. -/
def enumeratedToCountable : EnumeratedSetCat.{u} ⥤ CountableSetCat.{u} :=
  ObjectProperty.lift (Countable : ObjectProperty (Type u)) EnumeratedSetCat.forget fun X ↦ by
    change Countable X.carrier
    exact @Encodable.countable X.carrier X.enumeration

end LeanCategories.Foundation
