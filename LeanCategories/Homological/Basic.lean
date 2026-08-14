/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Homological categories over a ring

These abbreviations give the standard integral-indexed homological categories
of modules over a ring without introducing alternatives to Mathlib's types.
-/

@[expose] public section

universe u v w

namespace LeanCategories.Homological

/-- Integral-indexed chain complexes of modules over `R`. -/
abbrev ChainComplexOverRing (R : Type u) [Ring R] :=
  ChainComplex (ModuleCat.{v} R) ℤ

/-- Integral-indexed cochain complexes of modules over `R`. -/
abbrev CochainComplexOverRing (R : Type u) [Ring R] :=
  CochainComplex (ModuleCat.{v} R) ℤ

/-- The degree-`n` homology functor for integral-indexed cochain complexes over `R`. -/
abbrev HomologyFunctorOverRing (R : Type u) [Ring R] (n : ℤ) :
    CochainComplexOverRing R ⥤ ModuleCat.{v} R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n

/-- The homotopy category of integral-indexed chain complexes over `R`. -/
abbrev HomotopyCategoryOverRing (R : Type u) [Ring R] :=
  HomotopyCategory (ModuleCat.{v} R) (ComplexShape.down ℤ)

/-- The derived category of modules over `R`. -/
abbrev DerivedCategoryOverRing (R : Type u) [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] :=
  DerivedCategory (ModuleCat.{v} R)

/-- The internal-Hom functor on `R`-modules. -/
abbrev InternalHomOverRing (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  CategoryTheory.ihom M

/-- The degree-`n` Ext-group of `R`-modules. -/
abbrev ExtOverRing (R : Type u) [Ring R] [Small.{v} R]
    (M N : ModuleCat.{v} R) (n : ℕ) : Type v :=
  CategoryTheory.Abelian.Ext M N n

/-- The degree-`n` Tor-group of `R`-modules. -/
abbrev TorOverRing (R : Type u) [CommRing R] [Small.{v} R]
    (M N : ModuleCat.{v} R) (n : ℕ) : Type v :=
  ((CategoryTheory.Tor (ModuleCat.{v} R) n).obj M).obj N

/-- The degree-`n` sheaf cohomology functor on abelian sheaves. -/
abbrev SheafCohomologyFunctor {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] :
    Sheaf J AddCommGrpCat.{v} ⥤ AddCommGrpCat.{w} :=
  CategoryTheory.Sheaf.functorH J n

end LeanCategories.Homological
