/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real

@[expose] public section

/-!
# Munkres manifold terminology

This file records the dimension-specific terminology from Munkres, *Topology*,
§36. Munkres includes Hausdorffness and a countable basis in the definition of
an `m`-manifold; Mathlib keeps these hypotheses separate from `IsManifold`, so
the predicate below packages all three requirements.
-/

namespace LeanCategories.Topology

universe u

/-- Munkres' topological `m`-manifold interface: a Hausdorff, second-countable
space locally modelled on `ℝ^m`. -/
def IsMunkresManifold (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) 0 X

/-- A curve is a 1-manifold in Munkres' terminology (FC02-C04-U038). -/
def IsCurve (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) X] : Prop :=
  IsMunkresManifold 1 X

/-- A surface is a 2-manifold in Munkres' terminology (FC02-C04-U038). -/
def IsSurface (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] : Prop :=
  IsMunkresManifold 2 X

end LeanCategories.Topology
