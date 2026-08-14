/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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

/- Scheme morphisms whose structural arrow is affine. -/
abbrev AffineSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsAffineHom ⊤ ⊤

/- The canonical inclusion of affine scheme morphisms into all scheme arrows. -/
abbrev affineSchemeMorphismIncl :
    AffineSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsAffineHom ⊤ ⊤

/-- Scheme morphisms whose structural arrow is an open immersion. -/
abbrev OpenImmersionSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsOpenImmersion ⊤ ⊤

/-- The canonical inclusion of open-immersion scheme morphisms into all scheme arrows. -/
abbrev openImmersionSchemeMorphismIncl :
    OpenImmersionSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsOpenImmersion ⊤ ⊤

/- Scheme morphisms whose structural arrow is surjective. -/
abbrev SurjectiveSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @Surjective ⊤ ⊤

/- The canonical inclusion of surjective scheme morphisms into all scheme arrows. -/
abbrev surjectiveSchemeMorphismIncl :
    SurjectiveSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @Surjective ⊤ ⊤

/-- Scheme morphisms whose structural arrow is a closed immersion. -/
/- Scheme morphisms whose structural arrow is dominant. -/
abbrev DominantSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsDominant ⊤ ⊤

/- The canonical inclusion of dominant scheme morphisms into all scheme arrows. -/
abbrev dominantSchemeMorphismIncl :
    DominantSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsDominant ⊤ ⊤

/- Scheme morphisms whose structural arrow is a closed immersion. -/
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

/-- Scheme morphisms whose structural arrow is formally unramified. -/
abbrev FormallyUnramifiedSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @FormallyUnramified ⊤ ⊤

/-- The canonical inclusion of formally unramified scheme morphisms into all scheme arrows. -/
abbrev formallyUnramifiedSchemeMorphismIncl :
    FormallyUnramifiedSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @FormallyUnramified ⊤ ⊤

/-- Scheme morphisms that are locally of finite type. -/
abbrev LocallyOfFiniteTypeSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @LocallyOfFiniteType ⊤ ⊤

/-- The canonical inclusion of locally finite-type scheme morphisms into all scheme arrows. -/
abbrev locallyOfFiniteTypeSchemeMorphismIncl :
    LocallyOfFiniteTypeSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @LocallyOfFiniteType ⊤ ⊤

/-- Scheme morphisms that are locally of finite presentation. -/
abbrev LocallyOfFinitePresentationSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @LocallyOfFinitePresentation ⊤ ⊤

/-- The canonical inclusion of locally finite-presentation scheme morphisms into all scheme arrows. -/
abbrev locallyOfFinitePresentationSchemeMorphismIncl :
    LocallyOfFinitePresentationSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @LocallyOfFinitePresentation ⊤ ⊤

/-- Scheme morphisms that are locally quasi-finite. -/
abbrev LocallyQuasiFiniteSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @LocallyQuasiFinite ⊤ ⊤

/-- The canonical inclusion of locally quasi-finite scheme morphisms into all scheme arrows. -/
abbrev locallyQuasiFiniteSchemeMorphismIncl :
    LocallyQuasiFiniteSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @LocallyQuasiFinite ⊤ ⊤

/-- Scheme morphisms whose structural arrow is finite. -/
abbrev FiniteSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsFinite ⊤ ⊤

/-- The canonical inclusion of finite scheme morphisms into all scheme arrows. -/
abbrev finiteSchemeMorphismIncl :
    FiniteSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsFinite ⊤ ⊤

/-- Scheme morphisms whose structural arrow is integral. -/
abbrev IntegralSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsIntegralHom ⊤ ⊤

/-- The canonical inclusion of integral scheme morphisms into all scheme arrows. -/
abbrev integralSchemeMorphismIncl :
    IntegralSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsIntegralHom ⊤ ⊤

/-- Scheme morphisms whose structural arrow is proper. -/
abbrev ProperSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsProper ⊤ ⊤

/-- The canonical inclusion of proper scheme morphisms into all scheme arrows. -/
abbrev properSchemeMorphismIncl :
    ProperSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsProper ⊤ ⊤

/-- Scheme morphisms whose structural arrow is universally closed. -/
abbrev UniversallyClosedSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @UniversallyClosed ⊤ ⊤

/-- The canonical inclusion of universally closed scheme morphisms into all scheme arrows. -/
abbrev universallyClosedSchemeMorphismIncl :
    UniversallyClosedSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @UniversallyClosed ⊤ ⊤

/- Scheme morphisms whose structural arrow is universally open. -/
abbrev UniversallyOpenSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @UniversallyOpen ⊤ ⊤

/- The canonical inclusion of universally open scheme morphisms into all scheme arrows. -/
abbrev universallyOpenSchemeMorphismIncl :
    UniversallyOpenSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @UniversallyOpen ⊤ ⊤

/-- Scheme morphisms whose structural arrow is smooth. -/
abbrev SmoothSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @Smooth ⊤ ⊤

/-- The canonical inclusion of smooth scheme morphisms into all scheme arrows. -/
abbrev smoothSchemeMorphismIncl :
    SmoothSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @Smooth ⊤ ⊤

/-- Scheme morphisms whose structural arrow is flat. -/
abbrev FlatSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @Flat ⊤ ⊤

/-- The canonical inclusion of flat scheme morphisms into all scheme arrows. -/
abbrev flatSchemeMorphismIncl :
    FlatSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @Flat ⊤ ⊤

/-- Scheme morphisms whose structural arrow is quasi-compact. -/
abbrev QuasiCompactSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @QuasiCompact ⊤ ⊤

/-- The canonical inclusion of quasi-compact scheme morphisms into all scheme arrows. -/
abbrev quasiCompactSchemeMorphismIncl :
    QuasiCompactSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @QuasiCompact ⊤ ⊤

/-- Scheme morphisms whose structural arrow is separated. -/
abbrev SeparatedSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @IsSeparated ⊤ ⊤

/-- The canonical inclusion of separated scheme morphisms into all scheme arrows. -/
abbrev separatedSchemeMorphismIncl :
    SeparatedSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @IsSeparated ⊤ ⊤

/-- Scheme morphisms whose structural arrow is quasi-separated. -/
abbrev QuasiSeparatedSchemeMorphismCat : Type (u + 1) :=
  MorphismProperty.Arrow (T := Scheme.{u}) @QuasiSeparated ⊤ ⊤

/-- The canonical inclusion of quasi-separated scheme morphisms into all scheme arrows. -/
abbrev quasiSeparatedSchemeMorphismIncl :
    QuasiSeparatedSchemeMorphismCat.{u} ⥤ CategoryTheory.Arrow (Scheme.{u}) :=
  MorphismProperty.Arrow.forget @QuasiSeparated ⊤ ⊤

end LeanCategories.Schemes
