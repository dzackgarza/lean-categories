/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.ClassicalVariety
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Affine coordinate rings

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §1, pp. 1--7
(FC06-C01-U021).

For an affine algebraic set `Y ⊆ A^n_k`, its affine coordinate ring is

`A(Y) = k[x₁,…,xₙ] / I(Y)`,

where `I(Y)` is the ideal of polynomials vanishing on `Y`.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The affine coordinate ring of a subset of classical affine space.

Source: Hartshorne, Chapter I, §1, p. 5 (FC06-C01-U021). -/
abbrev affineCoordinateRingOfSet {n : ℕ}
    (Y : Set (AffinePointSpace k n)) :=
  MvPolynomial (Fin n) k ⧸ MvPolynomial.vanishingIdeal k Y

/-- The affine coordinate ring `A(Y)` of an affine variety. -/
abbrev AffineVariety.coordinateRing {n : ℕ} (Y : AffineVariety k n) :=
  affineCoordinateRingOfSet k Y.carrier

/-- The quotient map from the polynomial ring to `A(Y)`. -/
def AffineVariety.coordinateRingQuotient {n : ℕ} (Y : AffineVariety k n) :
    MvPolynomial (Fin n) k →+* Y.coordinateRing :=
  Ideal.Quotient.mk (MvPolynomial.vanishingIdeal k Y.carrier)

end LeanCategories.AlgebraicGeometry
