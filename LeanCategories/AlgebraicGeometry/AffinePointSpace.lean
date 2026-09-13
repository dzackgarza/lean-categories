/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Classical affine point space

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §1, pp. 1--7
(FC06-C01-U001).

Throughout Chapter I Hartshorne fixes an algebraically closed field `k` and
writes affine `n`-space as the point set

`A^n_k = k^n`.

A point is therefore an `n`-tuple of field elements, and its affine
coordinates are the coordinate projections.  This is the classical
point-set convention used before the later scheme-theoretic affine space.
-/

@[expose] public section

namespace LeanCategories.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Hartshorne's classical affine `n`-space `A^n_k = k^n`.

Source: Hartshorne, Chapter I, §1, p. 1 (FC06-C01-U001). -/
abbrev AffinePointSpace (n : ℕ) := Fin n → k

/-- The `i`th affine coordinate of a point of `A^n_k`. -/
def affineCoordinate {n : ℕ} (i : Fin n) : AffinePointSpace k n → k :=
  fun p => p i

/-- A point of affine space from its ordered affine coordinates. -/
def affinePoint {n : ℕ} (x : Fin n → k) : AffinePointSpace k n := x

@[simp]
theorem affineCoordinate_affinePoint {n : ℕ} (i : Fin n) (x : Fin n → k) :
    affineCoordinate k i (affinePoint k x) = x i :=
  rfl

end LeanCategories.AlgebraicGeometry
