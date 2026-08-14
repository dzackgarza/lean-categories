/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Ideal.IsPrimary

@[expose] public section

/-!
# Categories of ideals

The ambient category uses the canonical preorder category on `Ideal R`.
The full subcategories below use Mathlib's ideal predicates directly.
-/

namespace LeanCategories.Algebra

open CategoryTheory

universe u

variable (R : Type u) [CommSemiring R]

/-- The category of ideals of `R`, ordered by inclusion. -/
def Ideals := Cat.of (Ideal R)

/-- The full subcategory of principal ideals. -/
abbrev PrincipalIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.IsPrincipal)

/-- The full subcategory of maximal ideals. -/
abbrev MaximalIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.IsMaximal)

/-- The full subcategory of prime ideals. -/
abbrev PrimeIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.IsPrime)

/-- The full subcategory of radical ideals. -/
abbrev RadicalIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.IsRadical)

/-- The full subcategory of primary ideals. -/
abbrev PrimaryIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.IsPrimary)

/-- The canonical inclusion of principal ideals into all ideals. -/
abbrev principalIdealIncl : PrincipalIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.IsPrincipal)

/-- The canonical inclusion of maximal ideals into all ideals. -/
abbrev maximalIdealIncl : MaximalIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.IsMaximal)

/-- The canonical inclusion of prime ideals into all ideals. -/
abbrev primeIdealIncl : PrimeIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.IsPrime)

/-- The canonical inclusion of radical ideals into all ideals. -/
abbrev radicalIdealIncl : RadicalIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.IsRadical)

/-- The canonical inclusion of primary ideals into all ideals. -/
abbrev primaryIdealIncl : PrimaryIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.IsPrimary)

end LeanCategories.Algebra
