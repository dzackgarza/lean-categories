/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas
public import LeanCategories.Topology.SurfaceSchemes

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


/-- A closed nondegenerate triangular region in the complex plane. -/
structure ClosedTriangularRegion where
  polygon : Polygon ℂ 3
  affineIndependent : AffineIndependent ℝ polygon

namespace ClosedTriangularRegion

/-- The filled triangular region. -/
def carrier (T : ClosedTriangularRegion) : Set ℂ :=
  convexHull ℝ (Set.range T.polygon)

/-- The `i`th straight edge of the triangle. -/
def edge (T : ClosedTriangularRegion) (i : Fin 3) : Set ℂ :=
  segment ℝ (T.polygon i) (T.polygon (finRotate 3 i))

/-- The `i`th vertex. -/
def vertex (T : ClosedTriangularRegion) (i : Fin 3) : ℂ := T.polygon i

lemma edge_subset_carrier (T : ClosedTriangularRegion) (i : Fin 3) :
    T.edge i ⊆ T.carrier := by
  rw [edge, carrier]
  exact segment_subset_convexHull (Set.mem_range_self i) (Set.mem_range_self (finRotate 3 i))

end ClosedTriangularRegion

/-- A curved triangle in a topological space, in Munkres' sense. -/
structure CurvedTriangle (X : Type*) [TopologicalSpace X] where
  triangle : ClosedTriangularRegion
  carrier : Set X
  homeo : triangle.carrier ≃ₜ carrier

namespace CurvedTriangle

variable {X : Type*} [TopologicalSpace X]

/-- Image of a triangle vertex in the ambient space. -/
def vertex (A : CurvedTriangle X) (i : Fin 3) : X :=
  A.homeo ⟨A.triangle.vertex i, by
    rw [ClosedTriangularRegion.carrier]
    exact (subset_convexHull ℝ (Set.range A.triangle.polygon)) (Set.mem_range_self i)⟩

/-- Image of a straight triangle edge in the ambient space. -/
def edge (A : CurvedTriangle X) (i : Fin 3) : Set X :=
  {x | ∃ z : A.triangle.carrier,
    z.1 ∈ A.triangle.edge i ∧ (A.homeo z : A.carrier).1 = x}

/-- The transition between two curved-triangle edges is induced by an affine equivalence of
straight planar segments. -/
def HasLinearTransition (A B : CurvedTriangle X) (i j : Fin 3) : Prop :=
  ∃ L : ℂ ≃ᵃ[ℝ] ℂ,
    L '' A.triangle.edge i = B.triangle.edge j ∧
    ∀ z : A.triangle.carrier, z.1 ∈ A.triangle.edge i →
      ∃ w : B.triangle.carrier,
        w.1 = L z.1 ∧ (A.homeo z : A.carrier).1 = (B.homeo w : B.carrier).1

end CurvedTriangle

/-- Munkres' source-level triangulation structure (FC02-C12-U034). -/
structure MunkresTriangulation (X : Type*) [TopologicalSpace X] where
  count : ℕ
  triangle : Fin count → CurvedTriangle X
  covers : ⋃ i, (triangle i).carrier = Set.univ
  compatible : ∀ ⦃i j : Fin count⦄, i ≠ j →
    ((triangle i).carrier ∩ (triangle j).carrier = ∅) ∨
    (∃ a b : Fin 3,
      (triangle i).carrier ∩ (triangle j).carrier = {(triangle i).vertex a} ∧
      (triangle i).vertex a = (triangle j).vertex b) ∨
    (∃ a b : Fin 3,
      (triangle i).carrier ∩ (triangle j).carrier = (triangle i).edge a ∧
      (triangle i).edge a = (triangle j).edge b ∧
      CurvedTriangle.HasLinearTransition (triangle i) (triangle j) a b)

/-- A compact Hausdorff space is triangulable in Munkres' sense when it admits such a finite
curved-triangle decomposition. -/
def IsMunkresTriangulable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] : Prop :=
  Nonempty (MunkresTriangulation X)

end LeanCategories.Topology
