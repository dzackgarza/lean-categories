/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Topology.Irreducible
public import LeanCategories.Algebra.Local
public import LeanCategories.Schemes.Properties
public import LeanCategories.Schemes.Spectra

/-!
# Dummit--Foote Chapter 15 routes

This module exposes the Chapter 15 definitions through Mathlib's polynomial,
scheme, spectrum, structure-sheaf, integral-closure, and localization APIs.
It does not introduce a second category of varieties. Classical affine
algebraic sets use Mathlib's `MvPolynomial.zeroLocus` and `vanishingIdeal`;
scheme morphisms and regular functions use the existing scheme and sheaf
objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Algebra.DummitFoote.Chapter15

universe u v

/-! ## Affine polynomial geometry -/

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {σ : Type v}

/** The points of affine `σ`-space over `K`. */
abbrev AffineSpacePoints := σ → K

/** Affine `σ`-space over the scheme `Spec K`, using Mathlib's construction. */
abbrev AffineSpaceScheme (σ : Type u) (K : Type u) [CommRing K] : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace σ (AlgebraicGeometry.Spec (CommRingCat.of K))

/** The zero locus of an ideal of polynomial equations. */
abbrev ZeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → K) :=
  MvPolynomial.zeroLocus K I

/** The ideal of polynomial functions vanishing on a point set. */
abbrev IdealOfSubset (V : Set (σ → K)) : Ideal (MvPolynomial σ k) :=
  MvPolynomial.vanishingIdeal k V

/** The affine-algebraic-set predicate. */
def AffineAlgebraicSet (V : Set (σ → K)) : Prop :=
  ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus K I

/** The coordinate ring of a point set, as the quotient by its vanishing ideal. */
abbrev CoordinateRing (V : Set (σ → K)) : Type (max u v) :=
  MvPolynomial σ k ⧸ MvPolynomial.vanishingIdeal k V

/** The coordinate ring as a commutative-ring object. */
abbrev CoordinateRingCat (V : Set (σ → K)) : CommRingCat.{max u v} :=
  CommRingCat.of (CoordinateRing V)

/** An affine variety in its prime-ideal presentation. */
def AffineVariety (V : Set (σ → K)) : Prop :=
  ∃ P : Ideal (MvPolynomial σ k), P.IsPrime ∧ V = MvPolynomial.zeroLocus K P

/** Prime ideals presenting affine varieties. */
abbrev AffineVarietyPrimeIdeal (k : Type u) (σ : Type v) [CommRing k] : Type (max u v) :=
  {P : Ideal (MvPolynomial σ k) // P.IsPrime}

/** The point set represented by a prime ideal. */
abbrev varietyPoints (P : AffineVarietyPrimeIdeal k σ) : Set (σ → K) :=
  MvPolynomial.zeroLocus K P.1

/** The coordinate ring of a prime-ideal affine variety. */
abbrev varietyCoordinateRing
    (P : AffineVarietyPrimeIdeal k σ) : Type (max u v) :=
  MvPolynomial σ k ⧸ P.1

/-! ## Scheme routes for regular functions, maps, and irreducibility -/

/** The full category of affine schemes from Mathlib's `IsAffine` property. */
abbrev AffineSchemeCategory := LeanCategories.Schemes.AffineSchemeCat

/** The full category of integral schemes, the scheme-level affine variety route. */
abbrev IntegralSchemeCategory := LeanCategories.Schemes.IntegralSchemeCat

/** The canonical inclusion of affine schemes into schemes. */
abbrev affineSchemeInclusion :
    AffineSchemeCategory.{u} ⥤ Scheme.{u} :=
  LeanCategories.Schemes.affineSchemeIncl

/** The canonical inclusion of integral schemes into schemes. */
abbrev integralSchemeInclusion :
    IntegralSchemeCategory.{u} ⥤ Scheme.{u} :=
  LeanCategories.Schemes.integralSchemeIncl

/** A regular function on a scheme over an open set. */
abbrev RegularFunction (X : Scheme.{u}) (U : X.Opens) :=
  Γ(X, U)

/** A global regular function on a scheme. */
abbrev GlobalRegularFunction (X : Scheme.{u}) :=
  Γ(X, ⊤)

/** A regular morphism, represented by a scheme morphism. */
abbrev RegularMorphism (X Y : Scheme.{u}) := X ⟶ Y

/** Irreducibility of a topological subset, using Mathlib's definition. */
abbrev IrreducibleSubset {X : Type u} [TopologicalSpace X] (s : Set X) : Prop :=
  IsIrreducible s

/** The Zariski topological space of a commutative ring's prime spectrum. */
abbrev ZariskiSpace (R : Type u) [CommRing R] : TopCat.{u} :=
  LeanCategories.Schemes.PrimeSpectrumTopCat R

/** The Zariski topology on the prime spectrum. */
abbrev ZariskiTopology (R : Type u) [CommRing R] :
    TopologicalSpace (PrimeSpectrum R) := inferInstance

/** The affine scheme corresponding to a commutative ring. */
abbrev AffineScheme (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

/** The category of scheme morphisms, used for regular maps. */
abbrev SchemeMorphismCategory := CategoryTheory.Arrow (Scheme.{u})

/-! ## Integral and Noetherian ring terms -/

/** A Noetherian commutative ring. */
abbrev NoetherianRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R

/** An integral element in an algebra. */
abbrev IntegralElement (R : Type u) (A : Type v) [CommRing R] [Ring A]
    [Algebra R A] (x : A) : Prop :=
  IsIntegral R x

/** An integral ring extension. */
abbrev IntegralExtension (R : Type u) (A : Type v) [CommRing R]
    [Ring A] [Algebra R A] : Prop :=
  Algebra.IsIntegral R A

/** The integral closure of `R` in an `R`-algebra `A`. */
abbrev IntegralClosure (R : Type u) (A : Type v) [CommRing R]
    [CommRing A] [Algebra R A] :=
  integralClosure R A

/-! ## Localization, local rings, spectra, and sheaves -/

/** Localization of a commutative ring at a submonoid. */
abbrev LocalizationRing (R : Type u) [CommSemiring R] (S : Submonoid R) :=
  Localization S

/** Localization of a module at a submonoid. */
abbrev LocalizationModule (R : Type u) (M : Type v) [CommSemiring R]
    [AddCommMonoid M] [Module R M] (S : Submonoid R) :=
  LocalizedModule S M

/** Localization at the complement of a prime ideal. */
abbrev PrimeLocalization (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime] :=
  Localization.AtPrime P

/** The local-ring property. */
abbrev LocalRing (R : Type u) [CommRing R] : Prop := IsLocalRing R

/** A local ring homomorphism. */
abbrev LocalRingHom {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) : Prop := IsLocalHom f

/** The prime spectrum as a type. */
abbrev PrimeSpectrumType (R : Type u) [CommRing R] := PrimeSpectrum R

/** The prime-spectrum functor to Zariski topological spaces. */
abbrev PrimeSpectrumTopologicalFunctor : CommRingCat.{u}ᵒᵖ ⥤ TopCat.{u} :=
  LeanCategories.Schemes.PrimeSpectrumFunctor

/** The structure sheaf on the affine scheme `Spec R`. */
abbrev StructureSheaf (R : Type u) [CommRing R] :=
  AlgebraicGeometry.Spec.structureSheaf (CommRingCat.of R)

/** The stalk of the structure sheaf at a prime. */
abbrev StructureSheafStalk (R : Type u) [CommRing R] (p : PrimeSpectrum R) :=
  (AlgebraicGeometry.Spec.structureSheaf (CommRingCat.of R)).presheaf.stalk p

/** The canonical localization-to-stalk algebra equivalence. */
abbrev StructureSheafStalkLocalizationIso (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃ₐ[R] StructureSheafStalk R p :=
  AlgebraicGeometry.Spec.stalkIso R p

end LeanCategories.Algebra.DummitFoote.Chapter15
