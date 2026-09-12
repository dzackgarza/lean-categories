/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Differential graded algebras

Weibel, *An Introduction to Homological Algebra* (1994), DG-Algebras 4.5.2,
pp. 111--114 (FC05-C04-U071).

We use homological grading: the differential lowers degree by one and satisfies
`d(ab)=d(a)b+(-1)^p a d(b)` for homogeneous `a` of degree `p`.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (R : Type u) [CommRing R]
variable (A : Type v) [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- Graded commutativity: homogeneous elements of degrees `p,q` commute with
the Koszul sign `(-1)^(pq)`. -/
def IsGradedCommutative : Prop :=
  ∀ (p q : ℤ) (a b : A), a ∈ 𝒜 p → b ∈ 𝒜 q →
    a * b = (p * q).negOnePow • (b * a)

/-- A homologically graded differential algebra over `R`. -/
structure DifferentialGradedAlgebra where
  /-- The differential. -/
  d : A →ₗ[R] A
  /-- The differential squares to zero. -/
  d_sq : d.comp d = 0
  /-- The differential lowers internal degree by one. -/
  d_mem : ∀ (p : ℤ) {a : A}, a ∈ 𝒜 p → d a ∈ 𝒜 (p - 1)
  /-- The graded Leibniz identity. -/
  leibniz : ∀ (p : ℤ) {a : A}, a ∈ 𝒜 p → ∀ b : A,
    d (a * b) = d a * b + p.negOnePow • (a * d b)

end LeanCategories.Homological
