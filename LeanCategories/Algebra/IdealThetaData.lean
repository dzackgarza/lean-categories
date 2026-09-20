/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public noncomputable section

open scoped BigOperators nonZeroDivisors

namespace LeanCategories.Algebra

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- Neukirch's absolute discriminant of a nonzero fractional ideal:
`d_a = N(a)^2 |d_K|` (FC09-C07-U057). -/
def idealDiscriminantData
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2 *
    |(NumberField.discr K : ℝ)|

/-- The source normalization `d_a^(1/[K:Q])` used in the ideal theta
series (FC09-C07-U057). -/
def idealThetaScaleData
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  idealDiscriminantData K I ^ ((Module.finrank ℚ K : ℝ)⁻¹)

/-- The all-embeddings Hermitian expression
`Σ_τ τ(a) z_τ conjugate(τ(a))` occurring in Neukirch's theta exponent.

Using all complex embeddings directly preserves the source metric
normalization and avoids the `2^(-r₂)` coordinate-volume convention of
the unscaled mixed embedding. -/
def idealThetaPairingData
    (z : (K →+* ℂ) → ℂ) (a : K) : ℂ :=
  ∑ τ : K →+* ℂ, τ a * z τ * Complex.conj (τ a)

/-- One summand of Neukirch's normalized ideal theta series
(FC09-C07-U057). -/
def neukirchIdealThetaSummand
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (z : (K →+* ℂ) → ℂ)
    (a : {a : K // a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}) : ℂ :=
  Complex.exp <|
    (Real.pi : ℂ) * Complex.I *
      ((idealThetaScaleData K I : ℂ)⁻¹ * idealThetaPairingData K z a.1)

/-- Neukirch's ideal theta series as the total lattice `tsum`
(FC09-C07-U057).

Summability, holomorphy, the lattice-covolume comparison, and the relation
to the partial zeta/Gamma integral are result-layer statements and are not
constructor fields. -/
def neukirchIdealTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (z : (K →+* ℂ) → ℂ) : ℂ :=
  ∑' a : {a : K // a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)},
    neukirchIdealThetaSummand K I z a

end LeanCategories.Algebra
