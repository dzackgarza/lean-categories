/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Tangent convolution data

Definition-level realization of Humphreys FC16-C03-U003.

For the coordinate bialgebra `A = K[G]`, a tangent functional at the
identity is a `K`-linear functional satisfying the Leibniz rule with
respect to the counit.  Such a functional acts on `A` by right
convolution, equivalently by contracting the second tensor factor of
`Δ(f)`.

Closure of convolution commutators in the tangent-functional carrier,
the induced Lie bracket, and the Lie-ring/Lie-algebra laws are result
content and are not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

open Coalgebra TensorProduct WithConv

universe u v

variable
  {K : Type u} {A : Type v}
  [CommRing K] [CommRing A] [Bialgebra K A]

/-- A linear tangent functional at the identity of an affine group,
written directly as the counit-Leibniz predicate. -/
def IsCounitTangentFunctional (x : A →ₗ[K] K) : Prop :=
  ∀ a b : A,
    x (a * b) =
      Coalgebra.counit (R := K) a * x b +
        Coalgebra.counit (R := K) b * x a

/-- The raw carrier of tangent functionals at the identity.  No Lie
structure is bundled here. -/
abbrev CounitTangentFunctional :=
  {x : A →ₗ[K] K // IsCounitTangentFunctional x}

/-- Humphreys' right-convolution operator `f ↦ f * x`: convolution of
the identity map of the coordinate algebra with the tangent functional
embedded back into the coordinate algebra by the scalar map. -/
def rightConvolutionOperator (x : CounitTangentFunctional (K := K) (A := A)) :
    A →ₗ[K] A :=
  WithConv.ofConv
    ((toConv (LinearMap.id) : WithConv (A →ₗ[K] A)) *
      toConv ((Algebra.linearMap K A).comp x.1))

/-- Pointwise form of the right-convolution action. -/
def rightConvolution
    (x : CounitTangentFunctional (K := K) (A := A)) (f : A) : A :=
  rightConvolutionOperator x f

end LeanCategories.AlgebraicGeometry
