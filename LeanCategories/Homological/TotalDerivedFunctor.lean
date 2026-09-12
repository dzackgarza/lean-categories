/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Total derived functors

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 10.5.1
and its dual, pp. 390--393 (FC05-C10-U055, FC05-C10-U057).

A total right derived functor is a triangulated functor on the localized
category equipped with the universal transformation `F → L ⋙ RF`; a total
left derived functor is the dual construction with `L ⋙ LF → F`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category* C] [Category* D] [Category* H]
  [Preadditive D] [Preadditive H]
  [HasZeroObject D] [HasZeroObject H]
  [HasShift D ℤ] [HasShift H ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor H n).Additive]
  [Pretriangulated D] [Pretriangulated H]

/-- Source-faithful data of a total right derived functor.

`derived.IsRightDerivedFunctor unit W` is Mathlib's exact Kan-extension
formalization of Weibel's universal property; the additional fields record
that the derived functor is triangulated. -/
structure TotalRightDerivedFunctor
    (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] where
  /-- The derived functor on the localization. -/
  derived : D ⥤ H
  /-- Compatibility with the translation functors. -/
  [commShift : derived.CommShift ℤ]
  /-- The derived functor preserves distinguished triangles. -/
  [triangulated : derived.IsTriangulated]
  /-- Weibel's comparison transformation `ξ : F → RF ∘ L`. -/
  unit : F ⟶ L ⋙ derived
  /-- The universal property of the right derived functor. -/
  [isDerived : derived.IsRightDerivedFunctor unit W]

/-- Source-faithful data of a total left derived functor. -/
structure TotalLeftDerivedFunctor
    (F : C ⥤ H) (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] where
  /-- The derived functor on the localization. -/
  derived : D ⥤ H
  /-- Compatibility with the translation functors. -/
  [commShift : derived.CommShift ℤ]
  /-- The derived functor preserves distinguished triangles. -/
  [triangulated : derived.IsTriangulated]
  /-- Weibel's comparison transformation `ξ : LF ∘ L → F`. -/
  counit : L ⋙ derived ⟶ F
  /-- The dual universal property of the left derived functor. -/
  [isDerived : derived.IsLeftDerivedFunctor counit W]

/-- Restrict a total right derived functor to a chosen full subcategory of its domain.

This is the construction underlying Weibel's domain decorations such as `RᵇF`, `R⁺F`, and
`R_BF`.  Uniqueness and the induced comparison transformations are theorem-layer consequences
of the universal property.

Source: Weibel, §10.5, pp. 390--393 (FC05-C10-U056). -/
def TotalRightDerivedFunctor.restrictTo
    {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (RF : TotalRightDerivedFunctor F L W)
    (P : ObjectProperty D) : P.FullSubcategory ⥤ H :=
  ObjectProperty.ι P ⋙ RF.derived

/-- The corresponding domain-restriction convention for a total left derived functor. -/
def TotalLeftDerivedFunctor.restrictTo
    {F : C ⥤ H} {L : C ⥤ D} {W : MorphismProperty C}
    [L.IsLocalization W] (LF : TotalLeftDerivedFunctor F L W)
    (P : ObjectProperty D) : P.FullSubcategory ⥤ H :=
  ObjectProperty.ι P ⋙ LF.derived

end LeanCategories.Homological
