/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableGroupData
public import Mathlib.Topology.KrullDimension

/-!
# Rank data for an algebraic group

Definition-level realization of Humphreys FC16-C08-U007.

For a connected algebraic group, Humphreys defines the rank as the dimension
of a maximal torus. A maximal torus is supplied to this layer rather than
constructed here: existence and conjugacy of maximal tori are result content
from the preceding unit. The dimension itself is the topological Krull
dimension of the underlying affine scheme.

The assertion that different maximal tori give the same value is likewise
result content and is not proved in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- The dimension datum of a torus, expressed intrinsically as the
topological Krull dimension of its underlying affine scheme. -/
noncomputable def torusDimensionData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (_hT : IsTorusData T) : WithBot ℕ∞ :=
  topologicalKrullDim T.1.X.left

/-- Humphreys' rank datum from a supplied maximal torus.

The caller supplies the argument as a maximal torus of the ambient connected
algebraic group. Maximality, existence, and independence of the chosen
maximal torus are result-layer obligations, not constructor fields here. -/
noncomputable def algebraicGroupRankFromMaximalTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (hT : IsTorusData T) : WithBot ℕ∞ :=
  torusDimensionData T hT

end LeanCategories.AlgebraicGeometry
