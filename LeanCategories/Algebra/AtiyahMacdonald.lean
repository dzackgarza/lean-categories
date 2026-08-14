/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Atiyah--Macdonald commutative-algebra routes

This module gives the standard catalogue names for constructions already owned
by Mathlib. It does not define a second commutative-algebra hierarchy.

The pinned Mathlib source uses `Finite (MaximalSpectrum R)` for semilocality.
The source has no separate `Semilocal` class, so this file exposes that exact
predicate and its full subcategory.
-/

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import LeanCategories.Algebra.Concrete.CommAlgebras
public import LeanCategories.Algebra.Concrete.Rings
public import LeanCategories.Modules.Mathlib

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

section Rings

variable (R : Type u) [CommRing R]

/** Semilocality in the form used by pinned Mathlib. */
abbrev SemilocalRingProperty : Prop := Finite (MaximalSpectrum R)

/** The full subcategory of commutative semilocal rings. */
abbrev SemilocalRingCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := CommRingCat.{u})
    (fun S => Finite (MaximalSpectrum S))

/** The canonical inclusion of semilocal rings into commutative rings. */
abbrev semilocalRingIncl : SemilocalRingCat.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι (C := CommRingCat.{u})
    (fun S => Finite (MaximalSpectrum S))

/** The nilradical of a commutative ring. */
abbrev nilradical : Ideal R := _root_.nilradical R

/** The Jacobson radical of a commutative ring. */
abbrev ringJacobsonRadical : Ideal R := Ring.jacobson R

end Rings

section Ideals

variable {R : Type u} [CommRing R]

/** The radical of an ideal. */
abbrev idealRadical (I : Ideal R) : Ideal R := I.radical

/** The Jacobson radical of an ideal. */
abbrev idealJacobsonRadical (I : Ideal R) : Ideal R := I.jacobson

/** The sum of two ideals. */
abbrev idealSum (I J : Ideal R) : Ideal R := I + J

/** The intersection of two ideals. */
abbrev idealIntersection (I J : Ideal R) : Ideal R := I ⊓ J

/** The product of two ideals. */
abbrev idealProduct (I J : Ideal R) : Ideal R := I * J

/** Coprimality of two ideals. */
abbrev coprimeIdeals (I J : Ideal R) : Prop := IsCoprime I J

/** The ideal quotient `I : J`, represented by Mathlib's colon ideal. */
abbrev idealQuotient (I J : Ideal R) : Ideal R := I.colon (J : Set R)

/** The annihilator ideal of an `R`-module. */
abbrev moduleAnnihilator (M : Type v) [AddCommGroup M] [Module R M] : Ideal R :=
  Module.annihilator R M

end Ideals

section AlgebraFiniteness

variable (R : Type u) [CommRing R]

/** Commutative `R`-algebras finite as `R`-modules. */
abbrev ModuleFiniteAlgebraCat : Type (max u (v + 1)) :=
  CommAlgCat.ModuleFinite (v := v) R

/** Commutative `R`-algebras of finite type. */
abbrev FiniteTypeAlgebraCat : Type (max u (v + 1)) :=
  CommAlgCat.FiniteType (v := v) R

/** Commutative `R`-algebras of finite presentation. */
abbrev FinitePresentationAlgebraCat : Type (max u (v + 1)) :=
  CommAlgCat.FinitePresentation (v := v) R

/** Commutative `R`-algebras that are faithfully flat as `R`-modules. */
abbrev FaithfullyFlatAlgebraCat : Type (max u (v + 1)) :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Module.FaithfullyFlat R A)

/** Inclusion of module-finite commutative algebras. */
abbrev moduleFiniteAlgebraIncl :
    ModuleFiniteAlgebraCat (v := v) R ⥤ CommAlgCat.{v} R :=
  CommAlgCat.moduleFiniteIncl (v := v) R

/** Inclusion of finite-type commutative algebras. */
abbrev finiteTypeAlgebraIncl :
    FiniteTypeAlgebraCat (v := v) R ⥤ CommAlgCat.{v} R :=
  CommAlgCat.finiteTypeIncl (v := v) R

/** Inclusion of finite-presentation commutative algebras. */
abbrev finitePresentationAlgebraIncl :
    FinitePresentationAlgebraCat (v := v) R ⥤ CommAlgCat.{v} R :=
  CommAlgCat.finitePresentationIncl (v := v) R

/** Inclusion of faithfully flat commutative algebras. */
abbrev faithfullyFlatAlgebraIncl :
    FaithfullyFlatAlgebraCat (v := v) R ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Module.FaithfullyFlat R A)

end AlgebraFiniteness

end LeanCategories.Algebra

