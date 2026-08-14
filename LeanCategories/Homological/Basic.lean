/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory

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

end LeanCategories.Homological
