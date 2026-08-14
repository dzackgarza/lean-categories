/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Standard algebra-construction routes

Mathlib owns the standard polynomial, power-series, Laurent-series, tensor,
tensor-algebra, exterior-algebra, and symmetric-algebra constructions. This
module exposes their canonical definitions and algebra structures directly.
-/

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

@[expose] public section
