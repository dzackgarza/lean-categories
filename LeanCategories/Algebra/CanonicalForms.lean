/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import LeanCategories.Algebra.Polynomial

@[expose] public section

/-!
# Rational canonical data

This file defines the companion blocks and invariant-factor data used by rational
canonical form. Mathlib supplies the polynomial and block-diagonal infrastructure.
-/

namespace LeanCategories.Algebra

universe u

variable (R : Type u) [CommRing R]

/-- A monic nonconstant polynomial, the datum used for a companion block. -/
def IsCompanionPolynomial (f : Polynomial R) : Prop :=
  f.Monic ∧ f.natDegree ≠ 0

/-- The companion matrix of a monic nonconstant polynomial.

The convention is for `X^n + a_(n-1) X^(n-1) + ... + a_0`: ones occur on the
subdiagonal and the last column is `(-a_0, ..., -a_(n-1))`.
-/
def companionMatrix {f : Polynomial R} (hf : IsCompanionPolynomial R f) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  fun i j =>
    if j.1 + 1 = i.1 then 1
    else if j.1 + 1 = f.natDegree then -f.coeff i.1
    else 0

@[simp]
theorem companionMatrix_apply_subdiagonal {f : Polynomial R}
    (hf : IsCompanionPolynomial R f) (i j : Fin f.natDegree)
    (h : j.1 + 1 = i.1) : companionMatrix R hf i j = 1 := by
  simp [companionMatrix, h]

@[simp]
theorem companionMatrix_apply_off_last_column {f : Polynomial R}
    (hf : IsCompanionPolynomial R f) (i j : Fin f.natDegree)
    (hij : j.1 + 1 ≠ i.1) (hj : j.1 + 1 ≠ f.natDegree) :
    companionMatrix R hf i j = 0 := by
  simp [companionMatrix, hij, hj]

/-- Ordered monic nonconstant invariant factors. -/
structure InvariantFactorData (r : ℕ) where
  factor : Fin r → Polynomial R
  monic : ∀ i, (factor i).Monic
  nonconstant : ∀ i, (factor i).natDegree ≠ 0
  divisibility : ∀ ⦃i j : Fin r⦄, i ≤ j → factor i ∣ factor j

/-- The index type of the companion blocks in a rational canonical matrix. -/
abbrev invariantFactorIndex {r : ℕ} (d : InvariantFactorData R r) : Type u :=
  Σ i : Fin r, Fin (d.factor i).natDegree

/-- The total dimension of a rational canonical matrix. -/
def invariantFactorDimension {r : ℕ} (d : InvariantFactorData R r) : ℕ :=
  Fintype.card (invariantFactorIndex R d)

/-- The rational canonical matrix associated with ordered invariant factors. -/
def rationalCanonicalMatrix {r : ℕ} (d : InvariantFactorData R r) :
    Matrix (invariantFactorIndex R d) (invariantFactorIndex R d) R :=
  Matrix.blockDiagonal' fun i =>
    companionMatrix R ⟨d.monic i, d.nonconstant i⟩

end LeanCategories.Algebra
