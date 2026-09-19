/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Riemann theta-series data

Peters--Sterk FC11-C16-U027. Only the displayed lattice series is
recorded here. Summability, holomorphy and quasi-periodicity are result
content for later sweeps.
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix

namespace LeanCategories.Algebra

/-- One summand in the Riemann theta series attached to a complex matrix `Z`. -/
def riemannThetaSummand {g : ℕ} (Z : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) (x : Fin g → ℤ) : ℂ :=
  let xc : Fin g → ℂ := fun i => x i
  Complex.exp <|
    2 * (Real.pi : ℂ) * Complex.I *
      Matrix.dotProduct xc (z + (1 / 2 : ℂ) • (Z *ᵥ xc))

/-- Peters--Sterk FC11-C16-U027: `theta_Z(z)` as the total lattice `tsum`.

No convergence hypothesis is a constructor field: `tsum` is total, while the
source's everywhere-convergence statement belongs to theorem realization. -/
def riemannTheta {g : ℕ} (Z : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' x : Fin g → ℤ, riemannThetaSummand Z z x

end LeanCategories.Algebra
