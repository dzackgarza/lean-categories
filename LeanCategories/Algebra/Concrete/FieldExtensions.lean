/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.CategoryTheory.Category.Preorder
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

/-! ### Intermediate fields -/

/-- The category of intermediate fields of `L/K`.

This is the canonical preorder category on Mathlib's `IntermediateField K L`.
Its morphisms are the order relations given by field inclusion.
-/
abbrev IntermediateFieldCat (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] : Type _ :=
  Cat.of (IntermediateField K L)

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
    (fun A : Cat K =>
      letI : Field A.1.1 := A.2.toField
      _root_.Normal K A.1.1)

/-- The inclusion of normal field extensions. -/
abbrev normalIncl : Normal K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K =>
      letI : Field A.1.1 := A.2.toField
      _root_.Normal K A.1.1)

/-- Field extensions which are purely inseparable over `K`.

This uses Mathlib's unrestricted `IsPurelyInseparable` predicate.
-/
abbrev PurelyInseparable : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K => IsPurelyInseparable K A.1.1)

/-- The inclusion of purely inseparable field extensions into field extensions. -/
abbrev purelyInseparableIncl : PurelyInseparable K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K => IsPurelyInseparable K A.1.1)

/-! ### Galois extensions

`IsGalois` is Mathlib's standard predicate.  In particular, this category
does not add a finite-dimensional hypothesis: Mathlib's definition already
includes the required algebraicity through separability.
-/

/-- Field extensions which are Galois over `K`. -/
abbrev Galois : Type _ :=
  ObjectProperty.FullSubcategory (C := Cat K)
    (fun A : Cat K =>
      letI : Field A.1.1 := A.2.toField
      _root_.IsGalois K A.1.1)

/-- The inclusion of Galois field extensions into field extensions. -/
abbrev galoisIncl : Galois K ⥤ Cat K :=
  ObjectProperty.ι (C := Cat K)
    (fun A : Cat K =>
      letI : Field A.1.1 := A.2.toField
      _root_.IsGalois K A.1.1)

/-! ### Automorphism groups -/

/-- The automorphism group of a field extension, as `K`-algebra automorphisms.

This is defined for every field extension.  A Galois, finite, or separable
hypothesis is not part of the automorphism-group definition.
-/
abbrev galoisGroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Type _ :=
  L ≃ₐ[K] L

/-- The preorder category of subgroups of the `K`-algebra automorphism group of `L`.

Its objects are all subgroups, and its morphisms are inclusions.
-/
abbrev GaloisSubgroupCat (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] : Type _ :=
  Cat.of (Subgroup (galoisGroup K L))

/-- The intermediate field of `L` fixed by a subgroup of its `K`-algebra automorphisms. -/
abbrev fixedField (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (H : Subgroup (galoisGroup K L)) : IntermediateField K L :=
  IntermediateField.fixedField H

/-! ### The lattice of intermediate fields -/

/-- The intersection (infimum) of two intermediate fields in `L`. -/
abbrev intersection (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K L) : IntermediateField K L :=
  E₁ ⊓ E₂

/-- The infimum of two intermediate fields in `L`. -/
abbrev infimum (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K L) : IntermediateField K L :=
  E₁ ⊓ E₂

/-- The compositum (supremum) of two intermediate fields in `L`. -/
abbrev compositum (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K L) : IntermediateField K L :=
  E₁ ⊔ E₂

/-- The supremum of two intermediate fields in `L`. -/
abbrev supremum (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E₁ E₂ : IntermediateField K L) : IntermediateField K L :=
  E₁ ⊔ E₂

/-- The field closure of a subset of `L` over `K`. -/
abbrev fieldClosure (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (S : Set L) : IntermediateField K L :=
  IntermediateField.adjoin K S

/-- The field generated by a subset of `L` over `K`. -/
abbrev adjoin (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (S : Set L) : IntermediateField K L :=
  IntermediateField.adjoin K S

/-! ### Normal closures -/

/-- The normal closure of `L/K` inside an ambient field extension `E/K`.

This is Mathlib's `IntermediateField.normalClosure`; the project adds no
alternative closure construction.
-/
noncomputable abbrev normalClosure (K : Type u) (L E : Type v) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] : IntermediateField K E :=
  IntermediateField.normalClosure K L E

end FieldExtension
end LeanCategories.Algebra
