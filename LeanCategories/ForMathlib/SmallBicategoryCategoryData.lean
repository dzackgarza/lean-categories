/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Raw category data for small bicategories

Definition-level realization of Kerodon FC17-KER-U00307 (tag 0090).

Kerodon defines `2Cat_Lax` to have small bicategories as objects and lax
functors as morphisms, and similarly specifies the pseudofunctor,
strict-pseudofunctor, and strictly-unitary-lax subcategories.  Mathlib already
supplies all four morphism types together with identity and composition.

This file bundles the varying object bicategories and installs only
`CategoryStruct` data.  The ordinary-category identity and associativity laws
are proof obligations, so full `Category` instances and the subcategory
inclusion functors are deferred beyond Sweep III.
-/

@[expose] public section

namespace LeanCategories.BicategoryCategory

open CategoryTheory

universe u


/-- A small bicategory whose objects, 1-cells, and 2-cells all live in the
same universe. -/
structure SmallBicategory where
  carrier : Type u
  bicategory : CategoryTheory.Bicategory.{u, u} carrier

attribute [instance] SmallBicategory.bicategory

/-- A small strict bicategory, for the object class of Kerodon's
`2Cat_Str`. -/
structure SmallStrictBicategory where
  carrier : Type u
  bicategory : CategoryTheory.Bicategory.{u, u} carrier
  strict : CategoryTheory.Bicategory.Strict carrier

attribute [instance] SmallStrictBicategory.bicategory SmallStrictBicategory.strict

/-- Type synonym carrying the raw category structure of `2Cat_Lax`. -/
def TwoCatLaxData := SmallBicategory.{u}

/-- Type synonym carrying the raw category structure of `2Cat`. -/
def TwoCatData := SmallBicategory.{u}

/-- Type synonym carrying the raw category structure of `2Cat_ULax`. -/
def TwoCatULaxData := SmallBicategory.{u}

/-- Type synonym carrying the raw category structure of `2Cat_Str`. -/
def TwoCatStrData := SmallStrictBicategory.{u}

namespace TwoCatLaxData

instance : CategoryStruct TwoCatLaxData where
  Hom B C :=
    let _ := B.bicategory
    let _ := C.bicategory
    LaxFunctor B.carrier C.carrier
  id B :=
    let _ := B.bicategory
    LaxFunctor.id B.carrier
  comp {B C D} F G := by
    let _ := B.bicategory
    let _ := C.bicategory
    let _ := D.bicategory
    exact LaxFunctor.comp F G

end TwoCatLaxData

namespace TwoCatData

instance : CategoryStruct TwoCatData where
  Hom B C :=
    let _ := B.bicategory
    let _ := C.bicategory
    Pseudofunctor B.carrier C.carrier
  id B :=
    let _ := B.bicategory
    Pseudofunctor.id B.carrier
  comp {B C D} F G := by
    let _ := B.bicategory
    let _ := C.bicategory
    let _ := D.bicategory
    exact Pseudofunctor.comp F G

end TwoCatData

namespace TwoCatULaxData

instance : CategoryStruct TwoCatULaxData where
  Hom B C :=
    let _ := B.bicategory
    let _ := C.bicategory
    StrictlyUnitaryLaxFunctor B.carrier C.carrier
  id B :=
    let _ := B.bicategory
    StrictlyUnitaryLaxFunctor.id B.carrier
  comp {B C D} F G := by
    let _ := B.bicategory
    let _ := C.bicategory
    let _ := D.bicategory
    exact StrictlyUnitaryLaxFunctor.comp F G

end TwoCatULaxData

namespace TwoCatStrData

instance : CategoryStruct TwoCatStrData where
  Hom B C :=
    let _ := B.bicategory
    let _ := C.bicategory
    StrictPseudofunctor B.carrier C.carrier
  id B :=
    let _ := B.bicategory
    StrictPseudofunctor.id B.carrier
  comp {B C D} F G := by
    let _ := B.bicategory
    let _ := C.bicategory
    let _ := D.bicategory
    exact StrictPseudofunctor.comp F G

end TwoCatStrData

end LeanCategories.BicategoryCategory
