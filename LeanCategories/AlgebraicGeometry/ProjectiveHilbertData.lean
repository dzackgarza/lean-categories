/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.HilbertPolynomialData
public import LeanCategories.AlgebraicGeometry.ProjectiveCoordinateRing
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Hilbert polynomial and degree data for projective algebraic sets

Definition-level realization of Hartshorne FC06-C01-U141.

For `Y ⊆ P^n`, the degree-`d` piece of the homogeneous coordinate ring is
the quotient of degree-`d` homogeneous polynomials by the degree-`d` part of
the homogeneous vanishing ideal.  This degreewise description avoids any
need to construct a global quotient grading.

The Hilbert polynomial is selected from eventual equality with the dimensions
of these pieces, exactly as in FC06-C01-U140.  For an `r`-dimensional `Y`,
the degree is `r!` times its leading coefficient.

Hilbert--Serre eventual equality, polynomial uniqueness, the fact that the
degree formula is integral, and identification with a globally graded
coordinate quotient are result clauses and are not proved here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The degree-`d` part of the vanishing ideal, viewed inside the degree-`d`
homogeneous-polynomial module. -/
def projectiveVanishingIdealDegreePart {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) (d : ℕ) :
    Submodule k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) :=
  let I : Submodule k (MvPolynomial (Fin (n + 1)) k) :=
    (projectiveVanishingIdeal k Y.carrier).restrictScalars k
  I.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d).subtype

/-- The concrete degree-`d` piece `S(Y)_d` of the homogeneous coordinate
ring: homogeneous degree-`d` polynomials modulo those vanishing on `Y`. -/
abbrev projectiveCoordinateRingDegreePiece {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) (d : ℕ) :=
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d) ⧸
    projectiveVanishingIdealDegreePart k Y d

/-- Hartshorne's Hilbert function of a projective algebraic set. -/
def projectiveHilbertFunctionData {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) : ℕ → ℤ :=
  fun d => (Module.finrank k (projectiveCoordinateRingDegreePiece k Y d) : ℤ)

/-- Hartshorne's projective Hilbert polynomial `P_Y=P_{S(Y)}`, named by
the eventual-equality characterization from FC06-C01-U140. -/
def projectiveHilbertPolynomialData {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) : Polynomial ℚ :=
  LeanCategories.Algebra.eventualPolynomialData
    (projectiveHilbertFunctionData k Y)

/-- The rational value `r!` times the leading coefficient of `P_Y`, which is
Hartshorne's defining degree formula for an `r`-dimensional projective
algebraic set.  Its integrality/positivity are theorem-layer facts. -/
def projectiveDegreeValueData {n : ℕ}
    (Y : ProjectiveAlgebraicSet k n) (r : ℕ) : ℚ :=
  (r.factorial : ℚ) * (projectiveHilbertPolynomialData k Y).leadingCoeff

end LeanCategories.AlgebraicGeometry
