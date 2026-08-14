/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.FractionRingQuotient
public import LeanCategories.Modules.Bilinear.Valued
public import LeanCategories.Modules.Quadratic.Valued

@[expose] public section

/-!
# Forms valued in `Frac(R) / R`

These are the standard formed-module categories with the value module fixed to
Mathlib's fraction-ring quotient.
-/

namespace LeanCategories.Modules

universe u

variable (R : Type u) [CommRing R] [IsDomain R]

/-- Bilinear modules whose form takes values in `Frac(R) / R`. -/
abbrev FractionQuotientBilinModuleCat :=
  Bilinear.Valued.BilinModuleCat R (FractionRingQuotient R)

/-- Quadratic modules whose form takes values in `Frac(R) / R`. -/
abbrev FractionQuotientQuadModuleCat :=
  Quadratic.Valued.QuadModuleCat R (FractionRingQuotient R)

/-- Bilinear abelian groups whose form takes values in `ℚ / ℤ`. -/
abbrev RationalQuotientBilinModuleCat :=
  FractionQuotientBilinModuleCat ℤ

/-- Quadratic abelian groups whose form takes values in `ℚ / ℤ`. -/
abbrev RationalQuotientQuadModuleCat :=
  FractionQuotientQuadModuleCat ℤ

end LeanCategories.Modules
