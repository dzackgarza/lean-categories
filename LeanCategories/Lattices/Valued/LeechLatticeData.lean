/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Explicit Leech-lattice coordinate data

Supporting construction for Peters--Sterk FC11-C17-U030.

The integer Gram matrix is the `GRAM` entry of Gabriele Nebe and
N. J. A. Sloane's Catalogue of Lattices, `LAMBDA24 (The Leech Lattice)`:
https://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/Leech.html
(entry last modified 18 July 2014; inspected 23 September 2026).
Its normalization is determinant one, with minimum squared norm four.
The `GRAM` entries are used directly, not the floating-point triangular
basis or the unnormalized integer `BASIS` entries on the same page.

This supplies a concrete free carrier and its specified form, rather than
asking for an arbitrary rank-24 lattice satisfying a characterization.
The quadratic map uses the upper-triangular polynomial coefficients:
diagonal entries are halved, and off-diagonal upper entries are unchanged.
Thus no division operation on the lattice or integrality proof is needed
as input. Native matrix-to-bilinear and bilinear-to-quadratic constructors
provide the existing algebraic structure.

Evenness, positive definiteness, unimodularity, absence of roots, and
identification with other presentations of the Leech lattice are results.
No proof of those properties, or of the polar-form comparison, is added.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- Coordinates in the fixed Nebe--Sloane basis of the Leech lattice. -/
abbrev LeechCarrierData := Fin 24 → ℤ

/-- The integral Gram matrix in the catalogue's `GRAM` normalization. -/
def leechGramMatrixData : Matrix (Fin 24) (Fin 24) ℤ :=
  !![8, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 2, 4, 2, 2, 2, 0, 0, 0, -3;
     4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 0, 0, -1;
     4, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 0, 0, -1;
     4, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 0, 0, -1;
     4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, -1;
     4, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 0, 0, 0, -1;
     4, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 0, 0, 0, -1;
     2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 0, 0, 1;
     4, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, -1;
     4, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 1, 0, -1;
     4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 1, 2, 1, 0, 0, 1, -1;
     2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1;
     4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, -1;
     2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 1, 1;
     2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2, 1, 2, 1;
     2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2, 1, 1, 1;
     4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, -1;
     2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 1, 1;
     2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 1;
     2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 1;
     0, 1, 1, 1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2;
     -3, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 2, 2, 2, 4]

/-- The specified integral bilinear form on the concrete Leech carrier. -/
def leechBilinearData : LinearMap.BilinForm ℤ LeechCarrierData :=
  Matrix.toBilin' leechGramMatrixData

/-- Polynomial coefficients for the half-norm, without dividing vectors
or requiring a proof of integrality from the caller. -/
def leechQuadraticCoefficientData (i j : Fin 24) : ℤ :=
  match compare i.val j.val with
  | .lt => leechGramMatrixData i j
  | .eq => leechGramMatrixData i i / 2
  | .gt => 0

/-- The integral half-norm polynomial in the fixed Leech coordinates.
The comparison of its polar form with `leechBilinearData` is a result. -/
def leechQuadraticData : QuadraticForm ℤ LeechCarrierData :=
  (Matrix.toBilin' leechQuadraticCoefficientData).toQuadraticMap

end LeanCategories.Lattices.Valued
