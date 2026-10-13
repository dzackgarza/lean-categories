/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Odd-rank semi-discriminant polynomial data

Definition-level realization of Peters--Sterk FC11-C06-U030.

For odd rank, write a quadratic form in basis coordinates using variables
`a_{ii}=q(e_i)` and `a_{ij}=b_q(e_i,e_j)` for `i<j`.  Its polar Gram
matrix has diagonal entries `2 a_{ii}` and off-diagonal entries `a_{ij}`.
The determinant of this universal matrix has even integral coefficients.
Peters--Sterk denote its coefficientwise half by `P`.

Sweep III constructs that universal polynomial and its specialization to a
quadratic module.  The facts that every coefficient of the determinant is
even, that the polar determinant equals twice this specialization, and that
the specialization changes by a unit square under basis change are result
statements and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

/-- Divide the integral coefficients of a multivariate polynomial by two.

For the universal odd-rank polar determinant below all coefficients are even;
that divisibility is a result-layer statement. -/
def halveIntMvPolynomial {σ : Type*} (p : MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ :=
  (AddMonoidAlgebra.coeff p).sum fun d c =>
    MvPolynomial.monomial d (c / 2)

/-- Variables used for the universal odd-rank quadratic Gram matrix.  We keep
ordered pairs as the ambient variable type; the universal matrix itself uses
only the canonical pairs `(min i j, max i j)`. -/
abbrev OddRankQuadraticVariable (n : ℕ) :=
  Fin (2 * n + 1) × Fin (2 * n + 1)

/-- The universal polar Gram matrix in odd rank `2n+1`.

Diagonal variables record quadratic coefficients `q(e_i)`, hence acquire the
factor `2` under polarization.  Off-diagonal variables record the polar
coefficients directly. -/
def oddRankUniversalPolarGram (n : ℕ) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1))
      (MvPolynomial (OddRankQuadraticVariable n) ℤ) :=
  fun i j =>
    if i = j then
      2 * MvPolynomial.X (i, i)
    else
      MvPolynomial.X (min i j, max i j)

/-- Peters--Sterk's universal odd-rank polynomial `P`: the coefficientwise
half of the determinant of the universal polar Gram matrix. -/
def oddRankSemiDiscriminantPolynomial (n : ℕ) :
    MvPolynomial (OddRankQuadraticVariable n) ℤ :=
  halveIntMvPolynomial (Matrix.det (oddRankUniversalPolarGram n))

variable (R : Type u) [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Basis coefficients used to specialize the universal odd-rank polynomial.

The diagonal coefficient is `q(e_i)`; an off-diagonal coefficient is the
polar value `b_q(e_i,e_j)`. -/
def oddRankQuadraticCoefficient
    {n : ℕ} (Q : QuadraticMap R M R)
    (b : Module.Basis (Fin (2 * n + 1)) R M) :
    OddRankQuadraticVariable n → R
  | (i, j) =>
      if i = j then Q (b i) else Q.polarBilin (b i) (b j)

/-- The basis-dependent representative obtained by specializing the universal
odd-rank semi-discriminant polynomial.

Its square class is the semi-discriminant of the next source definition.
Basis covariance and the passage to that square class are separate
result/definition units. -/
def oddRankSemiDiscriminantRepresentative
    {n : ℕ} (Q : QuadraticMap R M R)
    (b : Module.Basis (Fin (2 * n + 1)) R M) : R :=
  MvPolynomial.eval₂ (Int.castRingHom R)
    (oddRankQuadraticCoefficient R M Q b)
    (oddRankSemiDiscriminantPolynomial n)

end LeanCategories.Modules.Quadratic.Valued
