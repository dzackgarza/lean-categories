/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finiteness subcategories of commutative algebras

This file exposes the full subcategories cut out by Mathlib's unrestricted
`Module.Finite`, `Algebra.FiniteType`, and `Algebra.FinitePresentation`
predicates.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

namespace CommAlgCat

variable (R : Type u) [CommRing R]

/-- Commutative `R`-algebras which are finite as `R`-modules. -/
abbrev ModuleFinite (R : Type u) [CommRing R] : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Module.Finite R A)

/-- The inclusion of module-finite commutative `R`-algebras. -/
abbrev moduleFiniteIncl (R : Type u) [CommRing R] : ModuleFinite R ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Module.Finite R A)

/-- The forgetful functor from module-finite algebras to commutative rings. -/
abbrev moduleFiniteToCommRing : ModuleFinite R ⥤ CommRingCat.{v} :=
  moduleFiniteIncl R ⋙ (forget₂ (CommAlgCat.{v} R) CommRingCat.{v})

/-- Commutative `R`-algebras of finite type. -/
abbrev FiniteType (R : Type u) [CommRing R] : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.FiniteType R A)

/-- The inclusion of finite-type commutative `R`-algebras. -/
abbrev finiteTypeIncl (R : Type u) [CommRing R] : FiniteType R ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.FiniteType R A)

/-- Commutative `R`-algebras of finite presentation. -/
abbrev FinitePresentation (R : Type u) [CommRing R] : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.FinitePresentation R A)

/-- The inclusion of finite-presentation commutative `R`-algebras. -/
abbrev finitePresentationIncl (R : Type u) [CommRing R] : FinitePresentation R ⥤ CommAlgCat.{v} R :=
  ObjectProperty.ι (C := CommAlgCat.{v} R)
    (fun A : CommAlgCat.{v} R => Algebra.FinitePresentation R A)

/-- The forgetful functor from finite-type algebras to commutative rings. -/
abbrev finiteTypeToCommRing : FiniteType R ⥤ CommRingCat.{v} :=
  finiteTypeIncl R ⋙ (forget₂ (CommAlgCat.{v} R) CommRingCat.{v})

/-- The forgetful functor from finite-presentation algebras to commutative rings. -/
abbrev finitePresentationToCommRing : FinitePresentation R ⥤ CommRingCat.{v} :=
  finitePresentationIncl R ⋙ (forget₂ (CommAlgCat.{v} R) CommRingCat.{v})

end CommAlgCat
end LeanCategories.Algebra
