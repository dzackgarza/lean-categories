/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Integral dependence and valuation routes

Mathlib owns the standard notions in this chapter. This file exposes their
exact predicates, subalgebras, subcategories, and canonical inclusion maps.
It does not introduce a second integral or valuation theory.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

/-! ### Integral dependence -/

/** An element integral over a ring through a ring homomorphism. */
abbrev integralElement {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (x : A) : Prop :=
  RingHom.IsIntegralElem f x

/** An algebra integral over its base ring. */
abbrev integralAlgebraProperty (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] : Prop :=
  Algebra.IsIntegral R A

/** An element integral over the base ring of an algebra. */
abbrev integralElementOver (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (x : A) : Prop :=
  IsIntegral R x

/** The full subcategory of integral commutative `R`-algebras. */
abbrev IntegralAlgebraCat (R : Type u) [CommRing R] : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.IsIntegral R A)

/** The inclusion of integral commutative `R`-algebras. */
abbrev integralAlgebraIncl (R : Type u) [CommRing R] :
    IntegralAlgebraCat.{u, v} R ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.IsIntegral R A)

/-! ### Integral closures -/

/** Mathlib's integral closure subalgebra of `R` in an `R`-algebra `A`. */
abbrev integralClosureSubalgebra (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] : Subalgebra R A :=
  _root_.integralClosure R A

/** The canonical inclusion of an integral closure into its ambient algebra. */
abbrev integralClosureIncl (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] : integralClosureSubalgebra R A →ₐ[R] A :=
  Subalgebra.val

/** The characteristic predicate for an integral closure. */
abbrev integralClosureProperty (A R B : Type*) [CommRing R] [CommSemiring A]
    [CommRing B] [Algebra R B] [Algebra A B] : Prop :=
  IsIntegralClosure A R B

/** The full subcategory of commutative `R`-algebras integrally closed in `A`. */
abbrev IntegrallyClosedInCat (R : Type u) [CommRing R] (A : Type v)
    [CommRing A] [Algebra R A] : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun B : CommAlgCat.{v} R => IsIntegrallyClosedIn B A)

/** The inclusion of algebras integrally closed in `A`. */
abbrev integrallyClosedInIncl (R : Type u) [CommRing R] (A : Type v)
    [CommRing A] [Algebra R A] :
    IntegrallyClosedInCat.{u, v} R A ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun B : CommAlgCat.{v} R => IsIntegrallyClosedIn B A)

/-! ### Valuation rings and valuations -/

/** The valuation-ring predicate, with Mathlib's integral-domain hypothesis. */
abbrev valuationRingProperty (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ValuationRing R

/** The discrete-valuation-ring predicate. */
abbrev discreteValuationRingProperty (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsDiscreteValuationRing R

/** The inclusion of valuation rings into integral domains. */
abbrev valuationRingIncl : ValuationRingCat.{u} ⥤ DomainCat.{u} :=
  ObjectProperty.ι (C := DomainCat.{u})
    (fun R => @ValuationRing R inferInstance R.property)

/** The inclusion of discrete valuation rings into integral domains. */
abbrev discreteValuationRingIncl : DiscreteValuationRingCat.{u} ⥤ DomainCat.{u} :=
  ObjectProperty.ι (C := DomainCat.{u})
    (fun R => @IsDiscreteValuationRing R inferInstance R.property)

/** Mathlib's valuation structure on a field with values in an ordered group. */
abbrev valuationStructure (K : Type u) (Γ : Type v) [Field K]
    [LinearOrderedCommGroupWithZero Γ] :=
  Valuation K Γ

/** Mathlib's valuation subring of a valued field. */
abbrev valuationSubring (K : Type u) [Field K] {Γ : Type v}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ValuationSubring K :=
  v.valuationSubring

/** The canonical inclusion of a valuation subring into its field. */
abbrev valuationSubringIncl (K : Type u) [Field K] (V : ValuationSubring K) :
    V →+* K :=
  V.subtype

end LeanCategories.Algebra
