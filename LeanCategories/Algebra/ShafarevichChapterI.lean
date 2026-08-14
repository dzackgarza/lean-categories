/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import LeanCategories.Algebra.DummitFooteChapter15
public import LeanCategories.Algebra.DimensionTheory

/-!
# Shafarevich, Basic Algebraic Geometry I: affine routes

This module gives the Chapter I affine vocabulary its canonical routes. Point-set
affine algebraic sets and coordinate algebras use the existing Dummit--Foote
routes. Scheme properties, regular functions, rational maps, products, fibers,
local rings, and function fields use Mathlib's scheme constructions. No second
variety hierarchy is introduced.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace LeanCategories.Algebra.Shafarevich

universe u v

section AffinePointSets

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {σ : Type v}

/** Points of affine space over the coefficient field. */
abbrev AffineSpacePoints : Type (max u v) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.AffineSpacePoints (σ := σ) (K := K)

/** An affine algebraic set, as a zero locus of polynomial equations. */
abbrev AffineAlgebraicSet (V : Set (σ → K)) : Prop :=
  LeanCategories.Algebra.DummitFoote.Chapter15.AffineAlgebraicSet (k := k) (K := K) V

/** The ideal of polynomial functions vanishing on a point set. */
abbrev VanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.IdealOfSubset (k := k) V

/** The coordinate algebra of an affine algebraic set. */
abbrev CoordinateAlgebra (V : Set (σ → K)) : CommRingCat.{max u v} :=
  LeanCategories.Algebra.DummitFoote.Chapter15.CoordinateRingCat (k := k) V

/** An irreducible affine variety, presented by a prime polynomial ideal. */
abbrev IrreducibleAffineVariety (V : Set (σ → K)) : Prop :=
  LeanCategories.Algebra.DummitFoote.Chapter15.AffineVariety (k := k) (K := K) V

/** Prime ideals that present affine varieties. */
abbrev AffineVarietyPrimeIdeal : Type (max u v) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.AffineVarietyPrimeIdeal k σ

/** The coordinate algebra of a prime-presented affine variety. */
abbrev AffineVarietyCoordinateAlgebra
    (P : AffineVarietyPrimeIdeal (k := k) (σ := σ)) : Type (max u v) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.varietyCoordinateRing P

end AffinePointSets

section SchemeRoutes

variable {X Y S : Scheme.{u}}

/** Affine integral schemes: the scheme-theoretic route for affine varieties. */
abbrev AffineVarietySchemeCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (C := Scheme.{u})
    (fun X : Scheme.{u} => IsAffine X ∧ IsIntegral X)

/** The inclusion of affine integral schemes into schemes. */
abbrev affineVarietySchemeIncl :
    AffineVarietySchemeCat.{u} ⥤ Scheme.{u} :=
  ObjectProperty.ι (C := Scheme.{u})
    (fun X : Scheme.{u} => IsAffine X ∧ IsIntegral X)

/** The category containing regular scheme morphisms. */
abbrev RegularMapCat : Type (u + 1) := CategoryTheory.Arrow (Scheme.{u})

/** A regular function on a scheme over an open subset. */
abbrev RegularFunction (X : Scheme.{u}) (U : X.Opens) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.RegularFunction X U

/** A global regular function on a scheme. */
abbrev GlobalRegularFunction (X : Scheme.{u}) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.GlobalRegularFunction X

/** A rational map of schemes, represented by Mathlib's partial-map quotient. */
abbrev RationalMap (X Y : Scheme.{u}) : Type u :=
  Scheme.RationalMap X Y

/** The rational function field of an irreducible scheme. */
noncomputable abbrev RationalFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    CommRingCat.{u} :=
  X.functionField

/** The scheme-theoretic product over the terminal scheme. */
abbrev SchemeProduct (X Y : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from X) (terminal.from Y)

/** The scheme-theoretic fiber of a morphism at a point. */
abbrev SchemeFiber (f : X ⟶ Y) (y : Y) : Scheme.{u} :=
  f.fiber y

/** The local ring of a scheme at a point. */
abbrev LocalRingAtPoint (X : Scheme.{u}) (x : X) :=
  X.presheaf.stalk x

/** The structure-sheaf stalk on an affine scheme at a prime. */
abbrev AffineLocalRingAtPrime (R : Type u) [CommRing R] (p : PrimeSpectrum R) :=
  LeanCategories.Algebra.DummitFoote.Chapter15.StructureSheafStalk R p

/** The global-sections functor restricted to affine integral schemes. */
abbrev affineVarietyGlobalSections :
    AffineVarietySchemeCat.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineVarietySchemeIncl.op ⋙ Scheme.Γ)

end SchemeRoutes

end LeanCategories.Algebra.Shafarevich
