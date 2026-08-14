/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
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

/-- Noetherian schemes as the full subcategory cut out by Mathlib's `IsNoetherian` predicate. -/
abbrev NoetherianSchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u}) (fun X : Scheme.{u} => IsNoetherian X)

/-- The inclusion of Noetherian schemes into all schemes. -/
abbrev noetherianSchemeIncl : NoetherianSchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u}) (fun X : Scheme.{u} => IsNoetherian X)

/-- Quasi-affine schemes as the full subcategory cut out by Mathlib's `IsQuasiAffine` predicate. -/
abbrev QuasiAffineSchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u})
    (fun X : Scheme.{u} => Scheme.IsQuasiAffine X)

/-- The inclusion of quasi-affine schemes into all schemes. -/
abbrev quasiAffineSchemeIncl : QuasiAffineSchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u}) (fun X : Scheme.{u} => Scheme.IsQuasiAffine X)

/-- Scheme morphisms whose structural arrow is an open immersion. -/
abbrev OpenImmersionSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsOpenImmersion ⊤ ⊤

/-- The canonical inclusion of open-immersion scheme morphisms into all scheme arrows. -/
abbrev openImmersionSchemeMorphismIncl :
    OpenImmersionSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsOpenImmersion ⊤ ⊤

/-- Scheme morphisms whose structural arrow is a closed immersion. -/
abbrev ClosedImmersionSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsClosedImmersion ⊤ ⊤

/-- The canonical inclusion of closed-immersion scheme morphisms into all scheme arrows. -/
abbrev closedImmersionSchemeMorphismIncl :
    ClosedImmersionSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsClosedImmersion ⊤ ⊤

/-- Scheme morphisms whose structural arrow is étale. -/
abbrev EtaleSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @Etale ⊤ ⊤

/-- The canonical inclusion of étale scheme morphisms into all scheme arrows. -/
abbrev etaleSchemeMorphismIncl :
    EtaleSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @Etale ⊤ ⊤

/-- Scheme morphisms whose structural arrow is finite. -/
abbrev FiniteSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsFinite ⊤ ⊤

/-- The canonical inclusion of finite scheme morphisms into all scheme arrows. -/
abbrev finiteSchemeMorphismIncl :
    FiniteSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsFinite ⊤ ⊤

end LeanCategories.Schemes
