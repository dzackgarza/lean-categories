/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

/-- Reduced schemes as the full subcategory cut out by Mathlib's `IsReduced` predicate.

The predicate is closed under isomorphisms in Mathlib, so this is the corresponding
full replete subcategory of `Scheme`.
-/
abbrev ReducedSchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u}) (fun X : Scheme.{u} => IsReduced X)

/-- The inclusion of reduced schemes into all schemes. -/
abbrev reducedSchemeIncl : ReducedSchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u}) (fun X : Scheme.{u} => IsReduced X)

/-- Affine schemes as the full subcategory cut out by Mathlib's `IsAffine` predicate. -/
abbrev AffineSchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u}) (fun X : Scheme.{u} => IsAffine X)

/-- The inclusion of affine schemes into all schemes. -/
abbrev affineSchemeIncl : AffineSchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u}) (fun X : Scheme.{u} => IsAffine X)

/-- Integral schemes as the full subcategory cut out by Mathlib's `IsIntegral` predicate. -/
abbrev IntegralSchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u}) (fun X : Scheme.{u} => IsIntegral X)

/-- The inclusion of integral schemes into all schemes. -/
abbrev integralSchemeIncl : IntegralSchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u}) (fun X : Scheme.{u} => IsIntegral X)

end LeanCategories.Schemes
