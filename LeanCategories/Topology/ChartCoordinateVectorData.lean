/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.DerivationBundle

/-!
# Raw chart-coordinate vector data

Definition-level realization of Lee FC08-C03-U021.

Lee's coordinate vector attached to a chart is specified first by its action on
a function: take the corresponding partial derivative of the function written
in chart coordinates.  In Lee's tangent model, proving that this raw functional
is a PointDerivation, identifying it with the inverse differential of the
chart, and proving that the resulting family is a basis are separate result
clauses.  Sweep III therefore records only the source formula below.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

/-- The Euclidean coordinate model used by an n-dimensional chart. -/
abbrev EuclideanCoordinateSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A real-valued function on the source of a coordinate chart. -/
abbrev ChartLocalFunction
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanCoordinateSpace n)) :=
  e.source → ℝ

/-- Raw coordinate-vector functionals on functions defined on the chart source.

No derivation law, tangent-space membership, or basis property is bundled into
this data. -/
abbrev ChartCoordinateVectorData
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanCoordinateSpace n)) :=
  Fin n → ChartLocalFunction e → ℝ

/-- The coordinate representation of a chart-local function, extended by zero
off the chart target.  Only its restriction to the chart target is used below,
so the off-target value is auxiliary data rather than a locality assertion. -/
def chartLocalFunctionInCoordinates
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanCoordinateSpace n))
    (f : ChartLocalFunction e) : EuclideanCoordinateSpace n → ℝ := by
  classical
  exact fun y ↦
    if hy : y ∈ e.target then
      f ⟨e.symm y, e.map_target hy⟩
    else
      0

/-- The raw i-th coordinate-vector functional determined by a chart e at
p: differentiate f composed with e inverse within the chart target at e p in
the standard i-th coordinate direction.

For a smooth chart containing p and a smooth function, this is Lee's formula
for the corresponding coordinate vector at p.  Showing that it is a
PointDerivation, and that these functionals form the coordinate basis, belongs
to the result layer. -/
def chartCoordinateVectorData
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanCoordinateSpace n)) (p : e.source) :
    ChartCoordinateVectorData e :=
  fun i f ↦
    fderivWithin ℝ (chartLocalFunctionInCoordinates e f) e.target (e p.1)
      (EuclideanSpace.single i 1)

end LeanCategories.Topology
