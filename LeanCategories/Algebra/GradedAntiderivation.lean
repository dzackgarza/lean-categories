/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Maps of degree and graded antiderivations

Definition-level realization of Lee FC08-C14-U036.  This file records only the
two predicates introduced in the source.  The assertions that the exterior
derivative has degree one, is an antiderivation, squares to zero, or is unique
with these properties are result content and are intentionally absent.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u v

variable (R : Type u) [CommRing R]
variable (A : Type v) [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- A linear endomorphism has degree `m` when it sends the degree-`k` piece
into the degree-`k+m` piece for every `k`. -/
def IsMapOfDegree (m : ℤ) (T : A →ₗ[R] A) : Prop :=
  ∀ (k : ℤ) {a : A}, a ∈ 𝒜 k → T a ∈ 𝒜 (k + m)

/-- A linear endomorphism is an antiderivation when it satisfies the graded
Leibniz rule on homogeneous elements. -/
def IsAntiderivation (T : A →ₗ[R] A) : Prop :=
  ∀ (k l : ℤ) {a b : A}, a ∈ 𝒜 k → b ∈ 𝒜 l →
    T (a * b) = T a * b + k.negOnePow • (a * T b)

end LeanCategories.Algebra
