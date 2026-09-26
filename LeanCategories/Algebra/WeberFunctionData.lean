/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Weber-function data

Definition-level realization of Neukirch FC09-C06-U071.

For a complex lattice `Γ`, the Weierstrass function and lattice invariants
used by Neukirch have their standard lattice-series formulas.  Lean's `tsum`
is a total operation, so those formulas define the source objects directly;
summability, holomorphy, periodicity, the Weierstrass equation, and
nonvanishing of the discriminant are theorem content rather than inputs.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Nonzero elements of a complex lattice. -/
abbrev NonzeroComplexLatticePointData (Gamma : Submodule ℤ ℂ) :=
  {w : Gamma // (w.1 : ℂ) ≠ 0}

/-- The Weierstrass elliptic function attached to `Gamma`, by its defining
lattice series.  At lattice poles this total formula has the ambient field's
division-by-zero convention; the meromorphic interpretation is result data. -/
def weierstrassPData (Gamma : Submodule ℤ ℂ) (z : ℂ) : ℂ :=
  1 / z ^ 2 +
    ∑' w : NonzeroComplexLatticePointData Gamma,
      (1 / (z - (w.1.1 : ℂ)) ^ 2 - 1 / (w.1.1 : ℂ) ^ 2)

/-- The lattice invariant `g₂(Gamma)=60 Σ'_{w≠0} w⁻⁴`. -/
def weberG2Data (Gamma : Submodule ℤ ℂ) : ℂ :=
  60 * ∑' w : NonzeroComplexLatticePointData Gamma,
    1 / (w.1.1 : ℂ) ^ 4

/-- The lattice invariant `g₃(Gamma)=140 Σ'_{w≠0} w⁻⁶`. -/
def weberG3Data (Gamma : Submodule ℤ ℂ) : ℂ :=
  140 * ∑' w : NonzeroComplexLatticePointData Gamma,
    1 / (w.1.1 : ℂ) ^ 6

/-- The Weierstrass discriminant `Delta(Gamma)=g₂³-27g₃²`. -/
def weberDiscriminantData (Gamma : Submodule ℤ ℂ) : ℂ :=
  weberG2Data Gamma ^ 3 - 27 * weberG3Data Gamma ^ 2

/-- Neukirch's Weber function `tau_Gamma`, constructed directly from the
lattice invariants and Weierstrass function. -/
def weberFunctionData (Gamma : Submodule ℤ ℂ) (z : ℂ) : ℂ :=
  let g2 := weberG2Data Gamma
  let g3 := weberG3Data Gamma
  let Delta := weberDiscriminantData Gamma
  let wp := weierstrassPData Gamma z
  if g2 * g3 ≠ 0 then
    -((2 : ℂ) ^ 7 * (3 : ℂ) ^ 5) * (g2 * g3 / Delta) * wp
  else if g2 = 0 then
    -((2 : ℂ) ^ 9 * (3 : ℂ) ^ 6) * (g3 / Delta) * wp ^ 3
  else
    ((2 : ℂ) ^ 8 * (3 : ℂ) ^ 4) * (g2 ^ 2 / Delta) * wp ^ 2

end LeanCategories.Algebra
