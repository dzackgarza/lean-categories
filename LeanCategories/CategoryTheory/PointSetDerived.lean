/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.CategoryTheory.Homotopical
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section

open _root_.CategoryTheory

namespace LeanCategories.CategoryTheory

universe vC uC vD uD vHC uHC vHD uHD

variable {C : Type uC} [_root_.CategoryTheory.Category.{vC} C]
variable {D : Type uD} [_root_.CategoryTheory.Category.{vD} D]
variable [HomotopicalCategory C] [HomotopicalCategory D]
variable {HC : Type uHC} [_root_.CategoryTheory.Category.{vHC} HC]
variable {HD : Type uHD} [_root_.CategoryTheory.Category.{vHD} HD]

/-- Riehl's point-set left derived functor (FC03-C06-U034), relative to chosen localization
functors `LC : C ⥤ HC` and `LD : D ⥤ HD`.

The point-set functor `LF : C ⥤ D` is required to be homotopical.  Its induced functor on the
localized categories is supplied as `derived`, with `descends` witnessing that it is genuinely
induced by `LF`.  The induced comparison is then required to be Mathlib's total left derived
functor, i.e. a right Kan extension along `LC`. -/
structure PointSetLeftDerived (F : C ⥤ D) (LC : C ⥤ HC) (LD : D ⥤ HD)
    [LC.IsLocalization (HomotopicalCategory.W C)]
    [LD.IsLocalization (HomotopicalCategory.W D)] where
  /-- The point-set left derived functor on the original categories. -/
  LF : C ⥤ D
  /-- `LF` preserves weak equivalences. -/
  homotopical : IsHomotopical LF
  /-- The point-set comparison to the original functor. -/
  comparison : LF ⟶ F
  /-- The functor induced by `LF` on the localized categories. -/
  derived : HC ⥤ HD
  /-- `derived` is genuinely induced by `LF` after localization. -/
  descends : LC ⋙ derived ≅ LF ⋙ LD
  /-- The induced functor is the total left derived functor of `F` after localizing the target. -/
  isDerived : derived.IsLeftDerivedFunctor
    (descends.hom ≫ _root_.CategoryTheory.Functor.whiskerRight comparison LD)
    (HomotopicalCategory.W C)

/-- Riehl's point-set right derived functor (FC03-C06-U034), relative to chosen localization
functors `LC : C ⥤ HC` and `LD : D ⥤ HD`. -/
structure PointSetRightDerived (F : C ⥤ D) (LC : C ⥤ HC) (LD : D ⥤ HD)
    [LC.IsLocalization (HomotopicalCategory.W C)]
    [LD.IsLocalization (HomotopicalCategory.W D)] where
  /-- The point-set right derived functor on the original categories. -/
  RF : C ⥤ D
  /-- `RF` preserves weak equivalences. -/
  homotopical : IsHomotopical RF
  /-- The point-set comparison from the original functor. -/
  comparison : F ⟶ RF
  /-- The functor induced by `RF` on the localized categories. -/
  derived : HC ⥤ HD
  /-- `derived` is genuinely induced by `RF` after localization. -/
  descends : LC ⋙ derived ≅ RF ⋙ LD
  /-- The induced functor is the total right derived functor of `F` after localizing the target. -/
  isDerived : derived.IsRightDerivedFunctor
    (_root_.CategoryTheory.Functor.whiskerRight comparison LD ≫ descends.inv)
    (HomotopicalCategory.W C)

end LeanCategories.CategoryTheory
