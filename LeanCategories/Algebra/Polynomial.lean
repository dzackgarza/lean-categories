/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.StandardConstructions
public import Mathlib.Algebra.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Algebra.Matrix.Basic

@[expose] public section

/-!
# Polynomial-ring lexicon

This file routes the Chapter 7--9 polynomial and ring terms to Mathlib's
existing objects. It adds no polynomial algorithms.
Mathlib has the relevant polynomial invariants, monomial orders, leading terms,
and division construction already.
-/

namespace LeanCategories.Algebra

universe u v

/-! ### Ring constructions -/

variable (R : Type u) [CommRing R]

/** The commutative polynomial ring `R[X]`. */
abbrev polynomialRing : Type u := Polynomial R

/** The quotient ring `R / I`, using Mathlib's ideal quotient. */
abbrev ringQuotient (I : Ideal R) : CommRingCat :=
  CommRingCat.of (R ⧸ I)

/** The canonical quotient ring homomorphism. */
abbrev ringQuotientMap (I : Ideal R) : R →+* ringQuotient R I :=
  Ideal.Quotient.mk I

section MatrixRing

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/** The matrix ring `M_ι(R)`, using Mathlib's canonical matrix ring. */
abbrev matrixRing : Type v := Matrix ι ι R

/** The scalar embedding into the matrix ring. */
abbrev matrixRingScalar : R →+* matrixRing R :=
  Matrix.scalar ι R

end MatrixRing

/-! ### Univariate polynomial terms -/

/** The degree in `WithBot ℕ` used by Mathlib's polynomial API. */
abbrev polynomialDegree (p : polynomialRing R) : WithBot ℕ :=
  p.degree

/** The natural-number degree of a polynomial. */
abbrev polynomialNatDegree (p : polynomialRing R) : ℕ :=
  p.natDegree

/** Evaluation as a ring homomorphism along a coefficient map. */
abbrev polynomialEvaluationHom {S : Type v} [Semiring S] (f : R →+* S) (x : S) :
    polynomialRing R →+* S :=
  Polynomial.eval₂RingHom f x

/** Evaluation in an `R`-algebra as an algebra homomorphism. */
abbrev polynomialAlgebraEvaluation {S : Type v} [Semiring S] [Algebra R S] (x : S) :
    polynomialRing R →ₐ[R] S :=
  Polynomial.aeval x

section GCDDomain

variable [NormalizedGCDMonoid R]

/** The content of a polynomial. */
abbrev polynomialContent (p : polynomialRing R) : R :=
  p.content

/** The predicate that a polynomial is primitive. */
abbrev primitivePolynomial (p : polynomialRing R) : Prop :=
  p.IsPrimitive

end GCDDomain

/** The predicate that a polynomial is Eisenstein at an ideal. */
abbrev eisensteinPolynomial (p : polynomialRing R) (P : Ideal R) : Prop :=
  p.IsEisensteinAt P

/-! ### Multivariate polynomials and monomial orders -/

variable {σ : Type v}

/** The multivariate polynomial ring `R[σ]`. */
abbrev multivariatePolynomialRing : Type (max u v) :=
  MvPolynomial σ R

/** A monomial order on the exponent monoid `σ →₀ ℕ`. */
abbrev polynomialMonomialOrder : Type v :=
  MonomialOrder σ

/** The ordered degree of a multivariate polynomial. */
abbrev multivariatePolynomialDegree (m : polynomialMonomialOrder) 
    (p : multivariatePolynomialRing R) : σ →₀ ℕ :=
  m.degree p

/** The leading coefficient for a monomial order. */
abbrev multivariatePolynomialLeadingCoeff (m : polynomialMonomialOrder)
    (p : multivariatePolynomialRing R) : R :=
  m.leadingCoeff p

/** The leading term for a monomial order. */
abbrev multivariatePolynomialLeadingTerm (m : polynomialMonomialOrder)
    (p : multivariatePolynomialRing R) : multivariatePolynomialRing R :=
  m.leadingTerm p

/** The S-polynomial for a monomial order. */
abbrev multivariatePolynomialSPolynomial (m : polynomialMonomialOrder)
    (f g : multivariatePolynomialRing R) : multivariatePolynomialRing R :=
  m.sPolynomial f g

/** The standard lexicographic monomial order. */
noncomputable abbrev lexicographicMonomialOrder [WellFoundedGT σ] :
    polynomialMonomialOrder :=
  MonomialOrder.lex

/-!
Mathlib supplies division and reduction with respect to a monomial order.
These aliases expose that implementation. They do not define a Groebner basis.
-/

abbrev multivariatePolynomialReduction (m : polynomialMonomialOrder)
    {b :  multivariatePolynomialRing R} (hb : IsUnit (m.leadingCoeff b))
    (f : multivariatePolynomialRing R) : multivariatePolynomialRing R :=
  m.reduce hb f

abbrev multivariatePolynomialDivision {ι : Type*} (m : polynomialMonomialOrder)
    {b : ι → multivariatePolynomialRing R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : multivariatePolynomialRing R) :=
  m.div hb f

end LeanCategories.Algebra

namespace MonomialOrder

/-!
The following definition is adapted from the reference implementation in
`WuProver/groebner_proj`, `Groebner/Groebner.lean`:
https://github.com/WuProver/groebner_proj/blob/42910339be485d279407382576e767223898c543/Groebner/Groebner.lean

That project credits Junyu Guo and Hao Shen and is released under the Apache
License 2.0. This port carries only the definition. Its reduction and
S-polynomial operations remain Mathlib's pinned implementations.
-/
def IsGroebnerBasis {σ : Type*} {m : MonomialOrder σ} {R : Type*}
    [CommSemiring R] (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) =
    Ideal.span (m.leadingTerm '' G)

end MonomialOrder
