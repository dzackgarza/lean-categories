/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.Chain

/-!
# Exponential representatives of root reflections

Definition-level realization of Humphreys FC14-C04-U008.

For nonzero root `α` and chosen root vectors `x_α ∈ L_α`,
`y_α ∈ L_{-α}`, the source writes
`τ_α = exp(ad x_α) exp(ad (-y_α)) exp(ad x_α)`.

Pinned Mathlib proves that the adjoint endomorphism of every vector in a
nonzero root space is nilpotent, so each exponential is already a finite
algebraic construction. This file records only their displayed product as
a linear endomorphism. That it is an inner Lie automorphism, restricts to
the root reflection on the Cartan, and carries `L_β` to `L_{σ_α β}` are
result clauses and remain outside Sweep III.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Algebra

open LieAlgebra LieModule

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L]

/-- Humphreys' raw exponential representative
`exp(ad x_α) exp(ad (-y_α)) exp(ad x_α)`.

The nilpotence witnesses are supplied by Mathlib's root-space theorem, not
by caller-provided proof data. -/
def rootReflectionRepresentativeData
    (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
    [IsTriangularizable K H L] [FiniteDimensional K L]
    {α : H → K} (hα : α ≠ 0) {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H (-α)) :
    Module.End K L :=
  let hxNil : _root_.IsNilpotent (ad K L x) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα hx
  let hyNeg : -y ∈ rootSpace H (-α) := (rootSpace H (-α)).neg_mem hy
  let hyNil : _root_.IsNilpotent (ad K L (-y)) :=
    LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hα) hyNeg
  IsNilpotent.exp (ad K L x) * IsNilpotent.exp (ad K L (-y)) *
    IsNilpotent.exp (ad K L x)

end LeanCategories.Algebra
