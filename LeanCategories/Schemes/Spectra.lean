/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Topological spectra

Mathlib supplies the Zariski topologies on prime and maximal spectra.
These abbreviations place those existing spaces in `TopCat`.
-/

public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.AlgebraicGeometry.Spec

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace LeanCategories.Schemes

/-! ### Standard Zariski subsets

These names expose Mathlib's exact constructions. They do not introduce a
second representation of the Zariski topology.
-/

/-- The Zariski closed subset `V(I)` of `PrimeSpectrum R`. -/
abbrev primeSpectrumClosedSet (R : Type u) [CommRing R] (I : Ideal R) :
    Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus I

/-- The basic Zariski open subset `D(f)` of `PrimeSpectrum R`. -/
abbrev primeSpectrumBasicOpen (R : Type u) [CommRing R] (f : R) :
    TopologicalSpace.Opens (PrimeSpectrum R) :=
  PrimeSpectrum.basicOpen f

/-- The ideal of functions vanishing on a subset of `PrimeSpectrum R`. -/
abbrev primeSpectrumVanishingIdeal (R : Type u) [CommRing R]
    (s : Set (PrimeSpectrum R)) : Ideal R :=
  PrimeSpectrum.vanishingIdeal s

/-- The prime spectrum of a commutative ring as an object of `TopCat`. -/
abbrev PrimeSpectrumTopCat (R : Type u) [CommRing R] : TopCat.{u} :=
  TopCat.of (PrimeSpectrum R)

/-- The maximal spectrum of a commutative ring as an object of `TopCat`. -/
abbrev MaximalSpectrumTopCat (R : Type u) [CommRing R] : TopCat.{u} :=
  TopCat.of (MaximalSpectrum R)

/-- The prime spectrum as Mathlib's contravariant functor on commutative rings. -/
abbrev PrimeSpectrumFunctor : CommRingCat.{u}ᵒᵖ ⥤ TopCat.{u} :=
  AlgebraicGeometry.Spec.toTop

end LeanCategories.Schemes
