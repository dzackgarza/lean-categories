/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Divisor objects exposed by Mathlib

The pinned Mathlib checkout has no declarations for Weil divisors, Cartier divisors, or effective
Cartier divisors. It does provide `AlgebraicGeometry.AlgebraicCycle`, the exact locally finite
coefficient object on a scheme, together with its pushforward API.

This file exposes the integer-coefficient cycle object as a standard `ModuleCat` object and adds
the source predicates needed to isolate Hartshorne's Weil-divisor setting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

variable (X : Scheme.{u})

/-- A scheme is regular in codimension one when every codimension-one local ring is regular.

Here codimension is Mathlib's `Order.coheight` on the specialization order of the scheme. By
`Scheme.ringKrullDim_stalk_eq_coheight`, the condition `coheight x = 1` is exactly that the local
ring `𝒪_{X,x}` has Krull dimension one.

Source: Hartshorne, *Algebraic Geometry*, II.6, p. 129 (FC06-C02-U151). -/
def IsRegularInCodimensionOne : Prop :=
  ∀ x : X, Order.coheight x = 1 → IsRegularLocalRing (X.presheaf.stalk x)

/-- Hartshorne's standing hypothesis `(*)` for the Weil-divisor discussion: the scheme is
Noetherian, integral, separated, and regular in codimension one.

Source: Hartshorne, *Algebraic Geometry*, II.6, p. 129 (FC06-C02-U152). -/
class DivisorStandingHypothesis : Prop where
  noetherian : IsNoetherian X
  integral : IsIntegral X
  separated : X.IsSeparated
  regularInCodimensionOne : IsRegularInCodimensionOne X

attribute [instance] DivisorStandingHypothesis.noetherian
  DivisorStandingHypothesis.integral DivisorStandingHypothesis.separated

/-- The integer-coefficient algebraic cycle group on a scheme `X`. -/
abbrev IntegerAlgebraicCycle := AlgebraicCycle X ℤ

/-- The integer-coefficient algebraic cycle group, exposed as a standard module object. -/
abbrev integerAlgebraicCycleModule : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (IntegerAlgebraicCycle X)

end LeanCategories.Schemes
