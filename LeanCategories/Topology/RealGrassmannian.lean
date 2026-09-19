/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Topology.Constructions

/-!
# Real Grassmann manifolds

Hatcher, *Algebraic Topology*, Section 4.2, p. 381 (`FC07-C04-U068`), defines
`G_n(ℝ^k)` as the set of `n`-dimensional vector subspaces of `ℝ^k`, with the quotient
topology induced by sending an orthonormal `n`-frame to its span.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set Submodule

/-- The real Stiefel space `V_n(ℝ^k)`, represented by orthonormal `n`-frames in `ℝ^k`. -/
def RealStiefel (n k : ℕ) :=
  {v : Fin n → EuclideanSpace ℝ (Fin k) // Orthonormal ℝ v}

/-- The underlying set of the real Grassmann manifold: the `n`-dimensional linear subspaces
of `ℝ^k`. Its topology is installed below from the Stiefel projection. -/
def RealGrassmannian (n k : ℕ) :=
  {V : Submodule ℝ (EuclideanSpace ℝ (Fin k)) // finrank ℝ V = n}

/-- The Stiefel projection sends an orthonormal frame to its linear span. -/
def stiefelToRealGrassmannian (n k : ℕ) : RealStiefel n k → RealGrassmannian n k :=
  fun v ↦ ⟨span ℝ (range v.1), by
    rw [finrank_span_eq_card v.2.linearIndependent, Fintype.card_fin]⟩

/-- Hatcher's quotient topology on `G_n(ℝ^k)`, induced by the projection from the Stiefel
space of orthonormal frames. -/
instance realGrassmannianTopologicalSpace (n k : ℕ) : TopologicalSpace (RealGrassmannian n k) :=
  TopologicalSpace.coinduced (stiefelToRealGrassmannian n k)
    (inferInstance : TopologicalSpace (RealStiefel n k))

end LeanCategories.Topology
