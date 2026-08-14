/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

/-!
# Categories of ideals

The ambient category uses the canonical preorder category on `Ideal R`.
The full subcategories below use Mathlib's ideal predicates directly.
-/

namespace LeanCategories.Algebra

open CategoryTheory

universe u v

variable (R : Type u) [CommSemiring R]

/-! ### Extended and contracted ideals in rings of fractions -/

/-- The extension of an ideal to the ring of fractions at `S`. -/
abbrev extendedIdeal (I : Ideal R) (S : Submonoid R) : Ideal (Localization S) :=
  I.map (algebraMap R (Localization S))

/-- The contraction of an ideal from the ring of fractions at `S`. -/
abbrev contractedIdeal (S : Submonoid R) (J : Ideal (Localization S)) : Ideal R :=
  J.under R

 /-- The category of ideals of `R`, ordered by inclusion. -/
def Ideals := Cat.of (Ideal R)

section RingHom

variable {S : Type v} [CommSemiring S]

/-- The order homomorphism on ideals induced by extension along `f`. -/
def idealMapOrderHom (f : R →+* S) : Ideal R →o Ideal S where
  toFun I := I.map f
  monotone' _ _ h := Ideal.map_mono h

/-- The functor on ideal preorders induced by extension along `f`. -/
abbrev idealMapFunctor (f : R →+* S) : Ideals R ⥤ Ideals S :=
  (idealMapOrderHom R f).toFunctor

/-- The order homomorphism on ideals induced by contraction along `f`. -/
def idealComapOrderHom (f : R →+* S) : Ideal S →o Ideal R where
  toFun I := I.comap f
  monotone' _ _ h := Ideal.comap_mono h

/-- The functor on ideal preorders induced by contraction along `f`. -/
abbrev idealComapFunctor (f : R →+* S) : Ideals S ⥤ Ideals R :=
  (idealComapOrderHom R f).toFunctor

/-- Ideal extension is left adjoint to ideal contraction on the ideal preorders. -/
def idealMapComapAdjunction (f : R →+* S) : idealMapFunctor R f ⊣ idealComapFunctor R f :=
  (show GaloisConnection (fun I : Ideal R => I.map f) (fun J : Ideal S => J.comap f) from
    fun I J => Ideal.map_le_iff_le_comap).adjunction

@[simp]
theorem idealMapFunctor_obj (f : R →+* S) (I : Ideal R) :
    (idealMapFunctor R f).obj I = I.map f := rfl

@[simp]
theorem idealComapFunctor_obj (f : R →+* S) (I : Ideal S) :
    (idealComapFunctor R f).obj I = I.comap f := rfl

end RingHom

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

/-- The full subcategory of finitely generated ideals. -/
abbrev FinitelyGeneratedIdealCat (R : Type u) [CommSemiring R] :=
  ObjectProperty.FullSubcategory (C := Ideal R) (fun I => I.FG)

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

/-- The canonical inclusion of finitely generated ideals into all ideals. -/
abbrev finitelyGeneratedIdealIncl : FinitelyGeneratedIdealCat R ⥤ Ideal R :=
  ObjectProperty.ι (C := Ideal R) (fun I => I.FG)

end LeanCategories.Algebra
