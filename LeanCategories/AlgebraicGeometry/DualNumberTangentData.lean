/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Dual-number tangent data

Definition-level realization of Humphreys FC16-C03-U008.

For a commutative Hopf algebra `A = K[G]`, the `K[ε]`-points of the
affine group are the convolution group of algebra maps `A → K[ε]`.
Reduction modulo `ε` is postcomposition with the canonical projection
`K[ε] → K`; the tangent fiber at the identity is its identity fiber.

That reduction is a group homomorphism, and the identification of its
identity fiber with the additive group of counit-valued derivations, are
result/comparison clauses and are not bundled here.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

open WithConv

universe u v

variable
  {K : Type u} {A : Type v}
  [CommRing K] [CommRing A] [HopfAlgebra K A]

/-- The group-valued functor of points evaluated on the dual numbers,
presented through the coordinate Hopf algebra. -/
abbrev DualNumberPoint :=
  WithConv (A →ₐ[K] DualNumber K)

/-- The ordinary `K`-points of the same affine group. -/
abbrev ClassicalPoint :=
  WithConv (A →ₐ[K] K)

/-- Reduction of a dual-number point modulo `ε`, as raw point data.
No homomorphism law is asserted here. -/
def dualNumberReduction
    (ψ : DualNumberPoint (K := K) (A := A)) :
    ClassicalPoint (K := K) (A := A) :=
  toConv ((TrivSqZeroExt.fstHom K K K).comp ψ.ofConv)

/-- The fibre of the dual-number tangent-bundle projection over a
classical `K`-point. -/
def dualNumberFiberAt
    (g : ClassicalPoint (K := K) (A := A)) :
    Set (DualNumberPoint (K := K) (A := A)) :=
  {ψ | dualNumberReduction ψ = g}

/-- Humphreys' tangent fiber at the identity: the dual-number points
whose reduction is the identity `K`-point. -/
def dualNumberTangentFiber : Set (DualNumberPoint (K := K) (A := A)) :=
  dualNumberFiberAt 1

/-- The raw carrier of the identity tangent fiber. -/
abbrev DualNumberTangentPoint :=
  {ψ : DualNumberPoint (K := K) (A := A) // ψ ∈ dualNumberTangentFiber}

end LeanCategories.AlgebraicGeometry
