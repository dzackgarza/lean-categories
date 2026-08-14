/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import LeanCategories.Algebra.Concrete.Magmas

@[expose] public section

/-!
# Rings

This file owns the concrete categories of rings, commutative rings, and division rings.
-/

namespace LeanCategories.Algebra

open CategoryTheory

universe u

def Rings : ObjCat.{u + 1, u} := Cat.of RingCat.{u}
def CommutativeRings : ObjCat.{u + 1, u} := Cat.of CommRingCat.{u}

abbrev DomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsDomain R)

abbrev FieldCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => Field R)

abbrev LocalRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsLocalRing R)

/-- The canonical inclusion of local commutative rings into commutative rings. -/
abbrev localRingIncl : LocalRingCat.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι (C := CommRingCat.{u}) (fun R => IsLocalRing R)

/-- The forgetful functor from local commutative rings to commutative rings. -/
abbrev localRingForgetful : LocalRingCat.{u} ⥤ CommRingCat.{u} := localRingIncl

/- Local homomorphisms between commutative local rings. -/
abbrev LocalRingHomProperty : MorphismProperty LocalRingCat.{u} :=
  fun f => IsLocalHom f.hom.hom

/-- The category of local homomorphisms between commutative local rings. -/
abbrev LocalRingHomCat : Type (u + 1) :=
  MorphismProperty.Arrow LocalRingHomProperty ⊤ ⊤

/-- The canonical inclusion of local-ring homomorphisms into local-ring arrows. -/
abbrev localRingHomIncl : LocalRingHomCat.{u} ⥤ CategoryTheory.Arrow LocalRingCat.{u} :=
  MorphismProperty.Arrow.forget LocalRingHomProperty ⊤ ⊤

abbrev DedekindDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsDedekindDomain R)

abbrev PrincipalIdealDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u})
    (fun R => IsDomain R ∧ IsPrincipalIdealRing R)

abbrev UniqueFactorizationDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u})
    (fun R => IsDomain R ∧ UniqueFactorizationMonoid R)

abbrev EuclideanDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => EuclideanDomain R)

abbrev ValuationRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := DomainCat.{u})
    (fun R => @ValuationRing R inferInstance R.property)

abbrev DiscreteValuationRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := DomainCat.{u})
    (fun R => @IsDiscreteValuationRing R inferInstance R.property)

def IsDivisionRing (R : RingCat.{u}) : Prop := Nonempty (DivisionRing R)

abbrev DivisionRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := RingCat.{u}) IsDivisionRing

noncomputable def divisionOnRings : Classifier Rings where
  total := Cat.of DivisionRingCat.{u}
  forget := (ObjectProperty.ι (C := RingCat.{u}) IsDivisionRing).toCatHom

noncomputable def DivisionRings : ObjCat.{u + 1, u} := divisionOnRings.total

end LeanCategories.Algebra
