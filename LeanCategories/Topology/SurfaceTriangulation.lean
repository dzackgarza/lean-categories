/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set

/-- Geometric realization of a finite family of faces by barycentric coordinates. -/
def GeometricRealization (V : Type*) [Fintype V] (F : Finset (Finset V)) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ t ∈ F, ∀ v ∉ t, x v = 0}

/-- A finite geometric triangulation of a topological space: a finite vertex type, a finite family
of triangular faces, and a homeomorphism from their geometric realization. -/
structure GeometricTriangulation (S : Type*) [TopologicalSpace S] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  faces : Finset (Finset Vertex)
  faces_card : ∀ t ∈ faces, t.card = 3
  homeo : GeometricRealization Vertex faces ≃ₜ S

attribute [instance] GeometricTriangulation.vertexFintype
attribute [instance] GeometricTriangulation.vertexDecidableEq

/-- A space is triangulable when it admits a finite geometric triangulation. -/
def IsTriangulable (S : Type*) [TopologicalSpace S] : Prop :=
  Nonempty (GeometricTriangulation S)

end LeanCategories.Topology
