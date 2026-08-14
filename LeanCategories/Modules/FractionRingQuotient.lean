/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace LeanCategories.Modules

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/-- The quotient `Frac(R) / R`, as an `R`-module. -/
abbrev FractionRingQuotient :=
  FractionRing R ⧸ LinearMap.range (Algebra.linearMap R (FractionRing R))

/-- The `R`-module object `Frac(R) / R`. -/
def fractionRingQuotientModule : ModuleCat R :=
  ModuleCat.of R (FractionRingQuotient R)

/-- The canonical fraction-ring model of the abelian group `ℚ / ℤ`. -/
abbrev RationalQuotientIntegers := FractionRingQuotient ℤ

/-- The `ℤ`-module object `ℚ / ℤ`. -/
def rationalQuotientIntegersModule : ModuleCat ℤ :=
  fractionRingQuotientModule ℤ

end LeanCategories.Modules
