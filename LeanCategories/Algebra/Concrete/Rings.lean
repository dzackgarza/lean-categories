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
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Ring
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

/-- Fields: commutative rings whose own structure is a field (Mathlib's `IsField`). Not
`Nonempty (Field R)`, which asks for *some* field structure on the carrier, unrelated to `R`'s. -/
abbrev FieldCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsField R)

abbrev LocalRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsLocalRing R)

/-- Noetherian commutative rings, using Mathlib's `IsNoetherianRing` predicate. -/
abbrev NoetherianRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsNoetherianRing R)

/-- Artinian commutative rings, using Mathlib's `IsArtinianRing` predicate. -/
abbrev ArtinianRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u}) (fun R => IsArtinianRing R)

/-- Integrally closed domains, using Mathlib's `IsIntegrallyClosed` predicate. -/
abbrev IntegrallyClosedDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := DomainCat.{u})
    (fun R => IsIntegrallyClosed R.1)

/-- The canonical inclusion of local commutative rings into commutative rings. -/
abbrev localRingIncl : LocalRingCat.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι (C := CommRingCat.{u}) (fun R => IsLocalRing R)

/-- The canonical inclusion of Noetherian commutative rings. -/
abbrev noetherianRingIncl : NoetherianRingCat.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι (C := CommRingCat.{u}) (fun R => IsNoetherianRing R)

/-- The canonical inclusion of Artinian commutative rings. -/
abbrev artinianRingIncl : ArtinianRingCat.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι (C := CommRingCat.{u}) (fun R => IsArtinianRing R)

/-- The canonical inclusion of integrally closed domains. -/
abbrev integrallyClosedDomainIncl : IntegrallyClosedDomainCat.{u} ⥤ DomainCat.{u} :=
  ObjectProperty.ι (C := DomainCat.{u})
    (fun R => IsIntegrallyClosed R.1)

/- Local homomorphisms between commutative local rings. -/
abbrev LocalRingHomProperty : MorphismProperty LocalRingCat.{u} :=
  fun {_ _} f => IsLocalHom f.hom.hom

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

/-- Euclidean domains: commutative rings admitting a Euclidean-domain structure *whose ring
structure is `R`'s own*. (`Nonempty (EuclideanDomain R)` alone would ask for an unrelated ring
structure on the carrier.) -/
abbrev EuclideanDomainCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u})
    (fun R => ∃ E : EuclideanDomain R, E.toCommRing = inferInstanceAs (CommRing R))

abbrev ValuationRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := DomainCat.{u})
    (fun R => @ValuationRing R.1 inferInstance R.property)

abbrev DiscreteValuationRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := DomainCat.{u})
    (fun R => @IsDiscreteValuationRing R.1 inferInstance R.property)

/-- `R`'s own ring structure is a division ring: nontrivial, and every nonzero element is a unit.
(Not `Nonempty (DivisionRing R)`, which asks for *some* division-ring structure on the carrier,
unrelated to `R`'s.) -/
def IsDivisionRing (R : RingCat.{u}) : Prop := Nontrivial R ∧ ∀ a : R, a ≠ 0 → IsUnit a

abbrev DivisionRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := RingCat.{u}) IsDivisionRing

noncomputable def divisionOnRings : Classifier Rings where
  total := Cat.of DivisionRingCat.{u}
  forget := (ObjectProperty.ι (C := RingCat.{u}) IsDivisionRing).toCatHom

noncomputable def DivisionRings : ObjCat.{u + 1, u} := divisionOnRings.total

end LeanCategories.Algebra
