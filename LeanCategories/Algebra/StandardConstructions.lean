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
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import LeanCategories.Algebra.FreeAlgebras

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) [CommRing R]

/-- The category of (not necessarily commutative) algebras over `R`.

This is the project name for Mathlib's canonical `AlgCat` category. -/
abbrev AlgebraCat := AlgCat

namespace AlgebraCat

/-- The polynomial algebra over `R`. -/
abbrev polynomial : AlgebraCat R := .of R (Polynomial R)

/-- The formal power-series algebra over `R`. -/
abbrev powerSeries : AlgebraCat R := .of R (PowerSeries R)

/- Laurent series have a canonical constant-term embedding of `R`. -/
instance : Algebra R (LaurentSeries R) :=
  RingHom.toAlgebra (HahnSeries.C : R →+* LaurentSeries R)

/-- The formal Laurent-series algebra over `R`. -/
abbrev laurentSeries : AlgebraCat R := .of R (LaurentSeries R)

end AlgebraCat
end LeanCategories.Algebra
