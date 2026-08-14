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
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace LeanCategories.Schemes

/-- The prime spectrum of a commutative ring as an object of `TopCat`. -/
abbrev PrimeSpectrumTopCat (R : Type u) [CommRing R] : TopCat.{u} :=
  TopCat.of (PrimeSpectrum R)

/-- The maximal spectrum of a commutative ring as an object of `TopCat`. -/
abbrev MaximalSpectrumTopCat (R : Type u) [CommRing R] : TopCat.{u} :=
  TopCat.of (MaximalSpectrum R)

end LeanCategories.Schemes
