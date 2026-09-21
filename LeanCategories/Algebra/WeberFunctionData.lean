/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Data.Complex.Basic

/-!
# Weber-function source data

Definition-level realization of Neukirch FC09-C06-U071.

For a lattice `Γ ⊂ ℂ`, Neukirch forms the Weber function from the lattice
invariants `g₂`, `g₃`, `Δ` and the Weierstrass elliptic function `℘_Γ` by the
displayed three-case formula.

The checked libraries do not construct the analytic function `℘_Γ` for an
arbitrary complex lattice.  Sweep III therefore records the analytic objects
already present in the source as raw input data and transcribes the Weber
formula itself.  The statements that these inputs are the analytic lattice
invariants, that `Δ ≠ 0`, and all modular/complex-multiplication properties of
the resulting function are result-layer mathematics.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Raw analytic data attached in the source to a complex lattice `Γ`.

The `lattice` field records the source parameter.  The remaining fields are
the source-supplied analytic invariants and Weierstrass `℘`-function.  No
analytic existence or identity is made a constructor obligation in Sweep III.
-/
structure WeberLatticeData where
  /-- The period lattice `Γ ⊂ ℂ`. -/
  lattice : Submodule ℤ ℂ
  /-- The lattice invariant `g₂(Γ)`. -/
  g2 : ℂ
  /-- The lattice invariant `g₃(Γ)`. -/
  g3 : ℂ
  /-- The discriminant `Δ(Γ)`. -/
  discriminant : ℂ
  /-- The Weierstrass elliptic function `℘_Γ`. -/
  weierstrassP : ℂ → ℂ

/-- Neukirch's Weber function `τ_Γ` from FC09-C06-U071.

This is exactly the displayed piecewise formula.  For genuine lattice data,
nonvanishing of the discriminant excludes the degenerate simultaneous case
`g₂ = g₃ = 0`; that fact is not required to define the raw function here. -/
def weberFunctionData (D : WeberLatticeData) (z : ℂ) : ℂ :=
  if D.g2 * D.g3 ≠ 0 then
    -((2 : ℂ) ^ 7 * (3 : ℂ) ^ 5) *
      (D.g2 * D.g3 / D.discriminant) * D.weierstrassP z
  else if D.g2 = 0 then
    -((2 : ℂ) ^ 9 * (3 : ℂ) ^ 6) *
      (D.g3 / D.discriminant) * (D.weierstrassP z) ^ 3
  else
    ((2 : ℂ) ^ 8 * (3 : ℂ) ^ 4) *
      (D.g2 ^ 2 / D.discriminant) * (D.weierstrassP z) ^ 2

end LeanCategories.Algebra
