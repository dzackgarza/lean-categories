/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
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

open AlgebraicGeometry CategoryTheory TopologicalSpace

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

/-- A prime divisor on `X`, represented as an actual integral closed subscheme together with its
generic point in `X`, required to have codimension one.

The closed subscheme is supplied by Mathlib's `IdealSheafData.subscheme`; its inclusion is a
closed immersion. The equality of its range with the closure of `genericPoint` makes the chosen
point the generic point of the underlying irreducible closed subset. This is the formal bridge
between Hartshorne's closed-integral-subscheme formulation and the codimension-one-point
formulation used by order-of-vanishing constructions.

Source: Hartshorne, *Algebraic Geometry*, II.6, p. 129 (FC06-C02-U153). -/
structure PrimeDivisor where
  /-- The ideal sheaf defining the closed subscheme. -/
  ideal : X.IdealSheafData
  /-- The closed subscheme is integral. -/
  integral : IsIntegral ideal.subscheme
  /-- Its generic point, viewed in the ambient scheme. -/
  genericPoint : X
  /-- The chosen point is the generic point of the underlying closed subset. -/
  range_eq_closure_genericPoint : Set.range ideal.subschemeι = closure {genericPoint}
  /-- The prime divisor has codimension one in `X`. -/
  codimension_one : Order.coheight genericPoint = 1

/-- The group `Div X` of Weil divisors: the free abelian group on prime divisors. -/
abbrev WeilDivisor := PrimeDivisor X →₀ ℤ

namespace WeilDivisor

/-- A Weil divisor is effective when every prime-divisor coefficient is nonnegative. -/
def IsEffective (D : WeilDivisor X) : Prop := ∀ Y, 0 ≤ D Y

/-- The basis Weil divisor associated to a prime divisor. -/
noncomputable def prime (Y : PrimeDivisor X) : WeilDivisor X := by
  classical
  exact Finsupp.single Y 1

end WeilDivisor

namespace PrimeDivisor

variable {X}

/-- Under Hartshorne's standing hypotheses, the local ring at the generic point of a prime
divisor is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk [DivisorStandingHypothesis X] (Y : PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk Y.genericPoint) := by
  have hregular : IsRegularLocalRing (X.presheaf.stalk Y.genericPoint) :=
    DivisorStandingHypothesis.regularInCodimensionOne Y.genericPoint Y.codimension_one
  have hdim : ringKrullDim (X.presheaf.stalk Y.genericPoint) = (1 : WithBot ℕ∞) := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, Y.codimension_one]
    rfl
  have hfinrank :
      (↑(Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk Y.genericPoint))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk Y.genericPoint))) : WithBot ℕ∞) = 1 :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hregular).trans hdim
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  exact_mod_cast hfinrank

/-- The order-of-vanishing valuation attached to a prime divisor. -/
noncomputable def valuation [DivisorStandingHypothesis X] (Y : PrimeDivisor X) :
    X.functionField →*₀ WithZero (Multiplicative ℤ) :=
  X.ordHom Y.genericPoint Y.codimension_one

end PrimeDivisor

/-- The integer-coefficient algebraic cycle group on a scheme `X`. -/
abbrev IntegerAlgebraicCycle := AlgebraicCycle X ℤ

/-- The integer-coefficient algebraic cycle group, exposed as a standard module object. -/
abbrev integerAlgebraicCycleModule : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (IntegerAlgebraicCycle X)

end LeanCategories.Schemes
