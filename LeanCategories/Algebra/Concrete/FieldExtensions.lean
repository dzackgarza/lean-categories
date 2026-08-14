/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.FiniteDimensional
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Categories of field extensions

These are full subcategories of `CommAlgCat K`.  The carrier predicates are
Mathlib's standard predicates; this file introduces no field-extension data.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

namespace FieldExtension

variable (K : Type u) [Field K]

/-- Commutative `K`-algebras whose carriers are fields. -/
abbrev Cat : Type _ :=
  ObjectProperty.FullSubcategory (C := CommAlgCat.{v} K)
    (fun A : CommAlgCat.{v} K => IsField A)

/-- The inclusion of field extensions into commutative `K`-algebras. -/
abbrev incl : Cat K ⥤ CommAlgCat.{v} K :=
  ObjectProperty.ι (C := CommAlgCat.{v} K)
    (fun A : CommAlgCat.{v} K => IsField A)

/-- The forgetful functor from field extensions to commutative rings. -/
abbrev toCommRing : Cat K ⥤ CommRingCat.{v} :=
  incl K ⋙ forget₂ (CommAlgCat.{v} K) CommRingCat.{v}

/-- Field extensions which are algebraic over `K`. -/
abbrev Algebraic : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => Algebra.IsAlgebraic K A.1.1)

/-- The inclusion of algebraic field extensions. -/
abbrev algebraicIncl : Algebraic K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => Algebra.IsAlgebraic K A.1.1)

/-- Field extensions which are finite as `K`-modules. -/
abbrev Finite : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => Module.Finite K A.1.1)

/-- The inclusion of finite field extensions. -/
abbrev finiteIncl : Finite K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => Module.Finite K A.1.1)

/-- Field extensions which are separable over `K`. -/
abbrev Separable : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => Algebra.IsSeparable K A.1.1)

/-- The inclusion of separable field extensions. -/
abbrev separableIncl : Separable K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => Algebra.IsSeparable K A.1.1)

/-- Field extensions which are normal over `K`. -/
abbrev Normal : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => _root_.Normal K A.1.1)

/-- The inclusion of normal field extensions. -/
abbrev normalIncl : Normal K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => _root_.Normal K A.1.1)

/-! ### Galois extensions

`IsGalois` is Mathlib's standard predicate.  In particular, this category
does not add a finite-dimensional hypothesis: Mathlib's definition already
includes the required algebraicity through separability.
-/

/-- Field extensions which are Galois over `K`. -/
abbrev Galois : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => _root_.IsGalois K A.1.1)

/-- The inclusion of Galois field extensions into field extensions. -/
abbrev galoisIncl : Galois K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => _root_.IsGalois K A.1.1)

end FieldExtension
end LeanCategories.Algebra
