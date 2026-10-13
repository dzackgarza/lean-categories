/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.FormalWeightConvolutionData

/-!
# Weyl-function coefficient data

Definition-level realization of Humphreys FC14-C06-U061.

Humphreys defines

  `q = ∏_{α > 0} (e_{α/2} - e_{-α/2})`.

Writing `ρ = (1/2) ∑_{α>0} α`, this is the symmetric normalization

  `q = e_ρ ∏_{α>0} (1 - e_{-α})`.

TauCeti's proof-complete Weyl-denominator owner uses the second finite product
and expands it over the powerset of the positive roots.  The declarations
below port that finite coefficient formula into the cone-supported function
carrier of FC14-C06-U059.  No convolution-totality, support-closure, or
commutative-algebra law is required to state the coefficient graph.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

/-- The coefficient of Humphreys' symmetric Weyl function at `lambda`,
written as the finite powerset expansion of
`e_ρ * ∏_{α>0} (1 - e_{-α})`. -/
def weylFunctionCoefficientData
    {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E] [CommRing F]
    (positiveRoots : Finset E) (lambda : E) : F := by
  classical
  exact ∑ T ∈ positiveRoots.powerset,
    if lambda = halfSumPositiveRoots positiveRoots - ∑ alpha ∈ T, alpha then
      (-1 : F) ^ T.card
    else
      0

/-- Exact coefficient graph of Humphreys' Weyl function `q` inside the
cone-supported formal-weight carrier `X`.

Existence of an element of `X` with these coefficients, its identification
with the iterated convolution product, and its Weyl anti-invariance are
result-layer statements. -/
def IsWeylFunctionData
    {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E] [CommRing F]
    (positiveRoots : Finset E)
    (q : ConeSupportedWeightFunctionData E F positiveRoots) : Prop :=
  ∀ lambda : E, q.1 lambda = weylFunctionCoefficientData positiveRoots lambda

end LeanCategories.Algebra
