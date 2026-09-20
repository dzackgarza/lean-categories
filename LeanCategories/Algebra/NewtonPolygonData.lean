/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Lower boundary of a planar convex hull, used in Neukirch FC09-C02-U070. -/
def lowerConvexEnvelope (s : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | p ∈ convexHull ℝ s ∧
    ∀ y : ℝ, y < p.2 → (p.1, y) ∉ convexHull ℝ s}

/-- Nonzero coefficient points `(i,height(a_i))`; zero coefficients are omitted by `support`. -/
def newtonCoefficientPoints {K : Type*} [Semiring K]
    (height : K → ℝ) (f : Polynomial K) : Set (ℝ × ℝ) :=
  {p | ∃ i : ℕ, i ∈ f.support ∧
    p = ((i : ℝ), height (f.coeff i))}

/-- Newton polygon as the lower convex envelope of the coefficient point set. -/
def newtonPolygonFromHeights {K : Type*} [Semiring K]
    (height : K → ℝ) (f : Polynomial K) : Set (ℝ × ℝ) :=
  lowerConvexEnvelope (newtonCoefficientPoints height f)

end LeanCategories.Algebra
