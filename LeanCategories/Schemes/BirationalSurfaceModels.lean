/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.Varieties
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.Basic

/-!
# Birational models and minimal surfaces

The definitions preceding II.15 and in II.15 of Beauville, *Complex Algebraic Surfaces*,
second edition, define domination by the existence of a birational morphism, and minimality
by requiring every birational morphism to another smooth projective surface to be an
isomorphism (`FC12-C02-U017`, `FC12-C02-U018`).

All morphisms here respect the complex structure. Birationality is the variety notion:
the specified morphism restricts to an isomorphism between dense open subschemes. The
predicate records the restriction equation, rather than unrelated object-level
birationality. This is not the more general generic-stalk definition for arbitrary schemes
of Stacks Project, Tag 01RN. No existence of minimal models or order laws is asserted.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical structure map of projective space over the complex numbers. -/
def complexProjectiveSpaceToSpec (n : ℕ) :
    ProjectiveSpace ℂ n ⟶ Spec (.of ℂ) :=
  ProjectiveSpace.structureMorphism ℂ n ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (projectiveSpaceGrading ℂ n 0)))

/-- A smooth projective complex surface, with its structure morphism. Projectivity is
expressed by a closed immersion over `Spec ℂ`; the dimension is the relative dimension
of the smooth structure morphism. -/
structure SmoothProjectiveComplexSurface where
  scheme : Scheme
  structureMap : scheme ⟶ Spec (.of ℂ)
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension 2 structureMap
  projective : ∃ (n : ℕ) (ι : scheme ⟶ ProjectiveSpace ℂ n),
    IsClosedImmersion ι ∧ ι ≫ complexProjectiveSpaceToSpec n = structureMap

/-- The variety notion of birationality for a specified morphism: its restriction to
dense open subschemes is an isomorphism. -/
def IsBirationalOnDenseOpens {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ e : X.PartialIso Y, e.source.ι ≫ f = e.iso.hom ≫ e.target.ι

namespace SmoothProjectiveComplexSurface

/-- A complex scheme morphism between two surfaces. -/
abbrev Hom (S T : SmoothProjectiveComplexSurface) :=
  {f : S.scheme ⟶ T.scheme // f ≫ T.structureMap = S.structureMap}

/-- Beauville's domination relation: a birational morphism goes from the dominating
surface to the dominated surface. -/
def Dominates (S T : SmoothProjectiveComplexSurface) : Prop :=
  ∃ f : Hom S T, IsBirationalOnDenseOpens f.val

/-- The smooth projective complex surfaces birational to a fixed surface, before
passing to isomorphism classes. -/
def BirationalModels (S : SmoothProjectiveComplexSurface) :=
  {T : SmoothProjectiveComplexSurface //
    Scheme.BirationalOver S.structureMap T.structureMap}

/-- Beauville II.15: every birational morphism from a minimal surface to another
smooth projective complex surface is an isomorphism. -/
def IsMinimal (S : SmoothProjectiveComplexSurface) : Prop :=
  ∀ (T : SmoothProjectiveComplexSurface) (f : Hom S T),
    IsBirationalOnDenseOpens f.val → IsIso f.val

end SmoothProjectiveComplexSurface

end LeanCategories.Schemes
