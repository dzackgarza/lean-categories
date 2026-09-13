/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AffinePointSpace
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Classical projective point space

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §2, pp. 8--13
(FC06-C01-U038).

Projective `n`-space is the quotient of `A^{n+1}_k \ {0}` by nonzero scalar
multiplication.  A nonzero representative

`(x₀, …, xₙ)`

is a system of homogeneous coordinates for the corresponding projective
point, unique up to multiplication by a nonzero scalar.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

open scoped LinearAlgebra.Projectivization

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Hartshorne's classical projective `n`-space
`P^n_k = (k^{n+1} \ {0}) / kˣ`.

Mathlib's `Projectivization` is literally this quotient.

Source: Hartshorne, Chapter I, §2, p. 8 (FC06-C01-U038). -/
abbrev ProjectivePointSpace (n : ℕ) :=
  Projectivization k (Fin (n + 1) → k)

/-- A nonzero `(n+1)`-tuple representing a projective point. -/
abbrev HomogeneousCoordinates (n : ℕ) :=
  {x : Fin (n + 1) → k // x ≠ 0}

/-- The projective point represented by a system of homogeneous coordinates. -/
def projectivePoint {n : ℕ} (x : HomogeneousCoordinates k n) :
    ProjectivePointSpace k n :=
  Projectivization.mk k x.1 x.2

/-- A chosen nonzero representative of a projective point; its entries are a
system of homogeneous coordinates. -/
def homogeneousCoordinates {n : ℕ} (P : ProjectivePointSpace k n) :
    HomogeneousCoordinates k n :=
  ⟨Projectivization.rep P, Projectivization.rep_nonzero P⟩

/-- The `i`th coordinate of the chosen homogeneous-coordinate representative. -/
def homogeneousCoordinate {n : ℕ} (P : ProjectivePointSpace k n)
    (i : Fin (n + 1)) : k :=
  (homogeneousCoordinates k P).1 i

@[simp]
theorem projectivePoint_homogeneousCoordinates {n : ℕ}
    (P : ProjectivePointSpace k n) :
    projectivePoint k (homogeneousCoordinates k P) = P :=
  Projectivization.mk_rep P

/-- Two nonzero coordinate tuples represent the same projective point exactly
when one is a nonzero scalar multiple of the other. -/
theorem projectivePoint_eq_iff {n : ℕ}
    (x y : HomogeneousCoordinates k n) :
    projectivePoint k x = projectivePoint k y ↔
      ∃ a : kˣ, a • (y.1 : Fin (n + 1) → k) = x.1 :=
  Projectivization.mk_eq_mk_iff k x.1 y.1 x.2 y.2

end LeanCategories.AlgebraicGeometry
