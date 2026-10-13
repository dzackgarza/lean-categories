/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular matrix Lie-algebra carrier data

Humphreys FC14-C01-U011.

Sweep III records only the three matrix carriers. Closure under commutators,
the vector-space decomposition and the displayed commutator equalities are
result-layer statements.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (R : Type u) [CommRing R]

/-- Humphreys' upper-triangular carrier t(n,F) (FC14-C01-U011). -/
def upperTriangularLieCarrierData (n : ℕ) : Set (Matrix (Fin n) (Fin n) R) :=
  {A | A.IsUpperTriangular}

/-- Humphreys' strictly upper-triangular carrier n(n,F) (FC14-C01-U011):
diagonal and lower entries vanish. -/
def strictUpperTriangularLieCarrierData (n : ℕ) : Set (Matrix (Fin n) (Fin n) R) :=
  {A | ∀ i j, j ≤ i → A i j = 0}

/-- Humphreys' diagonal carrier d(n,F) (FC14-C01-U011). -/
def diagonalLieCarrierData (n : ℕ) : Set (Matrix (Fin n) (Fin n) R) :=
  {A | ∀ i j, i ≠ j → A i j = 0}

end LeanCategories.Algebra
