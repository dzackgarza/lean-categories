/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Constant-coefficient linear-system data

Definition-level realization of Lee FC08-CD-U011.

For a complexified two-dimensional constant-coefficient system, Lee uses an
eigenvector mode

`t ↦ exp(λt) Z₀`

and, in the defective repeated-eigenvalue case, chooses `Z₁` with
`(A - λI) Z₁ = Z₀` and uses the second mode

`t ↦ exp(λt) (t Z₀ + Z₁)`.

This file records only that chain relation and the two explicit expressions.
Their ODE equations, linear independence, spanning, Jordan existence, and
real-form consequences are result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

/-- Lee's chosen length-two generalized-eigenvector chain relation in
FC08-CD-U011, relative to an already supplied eigenvector `z₀`.

Mathlib already owns generalized eigenspaces and generalized eigenvectors;
this predicate records only the source's more specific displayed choice
`(A - λI) z₁ = z₀`. -/
def IsLengthTwoGeneralizedEigenvectorChain
    (A : Module.End ℂ (Fin 2 → ℂ)) (lambda : ℂ)
    (z₀ z₁ : Fin 2 → ℂ) : Prop :=
  (A - lambda • (1 : Module.End ℂ (Fin 2 → ℂ))) z₁ = z₀

/-- The eigenvector-mode expression `exp(λt) Z₀` from FC08-CD-U011.

That this expression solves `Z' = AZ` when `Z₀` is a `λ`-eigenvector is
a result about this data and is not part of the definition. -/
def eigenvectorModeData
    (lambda : ℂ) (z₀ : Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ :=
  Complex.exp (lambda * (t : ℂ)) • z₀

/-- The defective repeated-eigenvalue mode
`exp(λt) (t Z₀ + Z₁)` from FC08-CD-U011.

The source uses this expression after choosing `Z₁` with
`(A - λI) Z₁ = Z₀`; proving that it is a second solution, is independent
from the eigenvector mode, or participates in a basis is result work. -/
def generalizedEigenvectorModeData
    (lambda : ℂ) (z₀ z₁ : Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ :=
  Complex.exp (lambda * (t : ℂ)) • ((t : ℂ) • z₀ + z₁)

end LeanCategories.Topology
