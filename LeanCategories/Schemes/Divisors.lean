/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Divisor objects exposed by Mathlib

The pinned Mathlib checkout has no declarations for Weil divisors, Cartier divisors, or effective
Cartier divisors. It does provide `AlgebraicGeometry.AlgebraicCycle`, the exact locally finite
coefficient object on a scheme, together with its pushforward API.

This file exposes the integer-coefficient cycle object as a standard `ModuleCat` object. It does
not introduce a divisor category or morphisms that Mathlib does not provide.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u

variable (X : Scheme.{u})

/-- The integer-coefficient algebraic cycle group on a scheme `X`. -/
abbrev IntegerAlgebraicCycle := AlgebraicCycle X ℤ

/-- The integer-coefficient algebraic cycle group, exposed as a standard module object. -/
abbrev integerAlgebraicCycleModule : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (IntegerAlgebraicCycle X)

end LeanCategories.Schemes
