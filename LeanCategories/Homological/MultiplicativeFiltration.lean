/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.DifferentialGradedAlgebra

/-!
# Multiplicative filtrations of DG algebras

Weibel, *An Introduction to Homological Algebra* (1994), Construction 5.4.8,
pp. 131--134 (FC05-C05-U033).

The definition layer is the filtration itself: an increasing filtration by
`R`-submodules, preserved by the differential and multiplicative in filtration
degree.  The induced products on the associated spectral sequence and the
identification of `E∞` with the associated graded algebra are theorem-layer.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable (R : Type u) [CommRing R]
variable (A : Type v) [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- An increasing multiplicative filtration on a differential graded algebra. -/
structure MultiplicativeDGFiltration (D : DifferentialGradedAlgebra R A 𝒜) where
  /-- The filtration terms `F_p A`. -/
  F : ℤ → Submodule R A
  /-- The filtration is increasing. -/
  monotone : Monotone F
  /-- The differential preserves filtration degree. -/
  d_mem : ∀ (p : ℤ) {a : A}, a ∈ F p → D.d a ∈ F p
  /-- Products add filtration degrees. -/
  mul_mem : ∀ (p q : ℤ) {a b : A}, a ∈ F p → b ∈ F q → a * b ∈ F (p + q)

end LeanCategories.Homological
