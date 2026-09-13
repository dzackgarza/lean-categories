/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.ClassicalProjectiveSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective zero loci

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §2, pp. 8--13
(FC06-C01-U040).

A homogeneous polynomial has a well-defined vanishing predicate on projective
space.  For a set `T` of homogeneous polynomials, `Z(T)` is their common zero
set.  For a homogeneous ideal `a`, `Z(a)` is the zero set of its homogeneous
elements.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

open scoped LinearAlgebra.Projectivization

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- A homogeneous polynomial in the homogeneous coordinates of `P^n_k`, with
its degree existentially remembered. -/
structure ProjectiveHomogeneousPolynomial (n : ℕ) where
  polynomial : MvPolynomial (Fin (n + 1)) k
  degree : ℕ
  homogeneous : polynomial.IsHomogeneous degree

/-- A homogeneous polynomial vanishes at a projective point when it vanishes
on every nonzero representative of that point.

This formulation is manifestly independent of the choice of homogeneous
coordinates and is equivalent to evaluating on any one representative.

Source: Hartshorne, Chapter I, §2, pp. 8--9 (FC06-C01-U040). -/
def ProjectiveHomogeneousPolynomial.VanishesAt {n : ℕ}
    (f : ProjectiveHomogeneousPolynomial k n)
    (P : ProjectivePointSpace k n) : Prop :=
  ∀ (x : Fin (n + 1) → k) (hx : x ≠ 0),
    Projectivization.mk k x hx = P → MvPolynomial.eval x f.polynomial = 0

/-- The common projective zero set `Z(T)` of a family of homogeneous
polynomials. -/
def projectiveZeroLocus {n : ℕ}
    (T : Set (ProjectiveHomogeneousPolynomial k n)) :
    Set (ProjectivePointSpace k n) :=
  {P | ∀ f ∈ T, f.VanishesAt k P}

/-- A polynomial is a homogeneous element of an ideal when it lies in the
ideal and is homogeneous of some degree. -/
def homogeneousElementsOfIdeal {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    Set (ProjectiveHomogeneousPolynomial k n) :=
  {f | f.polynomial ∈ I}

/-- The projective zero set `Z(a)` of an ideal, formed from its homogeneous
elements.  When `a` is homogeneous this is Hartshorne's notation literally. -/
def projectiveZeroLocusOfIdeal {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    Set (ProjectivePointSpace k n) :=
  projectiveZeroLocus k (homogeneousElementsOfIdeal k I)

end LeanCategories.AlgebraicGeometry
