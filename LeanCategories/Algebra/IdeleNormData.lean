/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IdeleGroup
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped BigOperators

namespace LeanCategories

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The infinite-place factor in Neukirch's absolute idèle norm (FC09-C06-U009).

This is only the displayed product data.  Positivity and multiplicativity are
result-layer statements and are not packaged here. -/
def infiniteIdeleAbsoluteNormData (a : InfiniteIdeleGroup K) : ℝ :=
  (∏ v : InfinitePlace K, ‖(a v : v.Completion)‖ ^ v.mult)⁻¹

/-- The finite-place factor in Neukirch's absolute idèle norm (FC09-C06-U009).

The restricted-product condition implies that almost every local factor is one,
but that assertion is deliberately not construction data here. -/
def finiteIdeleAbsoluteNormData (a : FiniteIdeleGroup K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a v : v.adicCompletion K)‖⁻¹

/-- Raw absolute norm of an idèle, as the product of the inverse normalized
absolute values over all infinite and finite places (FC09-C06-U009).

The product formula for principal idèles, continuity, multiplicativity, positivity,
and descent to the idèle class group are separate result-layer obligations. -/
def ideleAbsoluteNormData (a : IdeleGroup K) : ℝ :=
  infiniteIdeleAbsoluteNormData K a.1 * finiteIdeleAbsoluteNormData K a.2

end LeanCategories
