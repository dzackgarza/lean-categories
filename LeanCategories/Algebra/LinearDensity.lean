/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Linear densities

Definition-level realization of Lee FC08-C16-U048.  A density on an
`n`-dimensional real vector space is characterized by its transformation law
under every linear endomorphism.  Positivity, classification, uniqueness, and
smooth density bundles are result or later-definition content and are absent.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

/-- Lee's linear-density predicate: `μ` transforms by the absolute determinant
under every endomorphism, on every `n`-tuple. -/
def IsLinearDensity {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (μ : (Fin n → V) → ℝ) : Prop :=
  ∀ (f : V →ₗ[ℝ] V) (v : Fin n → V),
    μ (f ∘ v) = |LinearMap.det f| * μ v

end LeanCategories.Algebra
