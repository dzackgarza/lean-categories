/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Coherent
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Arcs, wedges of circles, and linear graphs

Definition-level realizations of Munkres FC02-C10-U004/U016/U019/U030,
FC02-C11-U050/U053, and FC02-C14-U001/U005/U008/U010.

The arc parametrization follows the mapped Apache-2.0 Schoenflies reference
`alonamaloh/schoenflies-lean@05a43d29cde026618777db3d4e4316204ccca237`,
while retaining Munkres' intrinsic topological-space formulation rather than specializing
to embedded plane graphs.
-/

namespace LeanCategories.Topology

open Set

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- An arc is a subspace homeomorphic to the unit interval (FC02-C10-U004). -/
def IsArc (A : Set X) : Prop :=
  Nonempty (unitInterval ≃ₜ A)

/-- An arc with named endpoints. -/
def IsArcBetween (A : Set X) (p q : X) : Prop :=
  ∃ e : unitInterval ≃ₜ A, ((e 0 : A) : X) = p ∧ ((e 1 : A) : X) = q

/-- A point is an endpoint of an arc when some arc parametrization takes an endpoint to it. -/
def IsArcEndpoint (A : Set X) (p : X) : Prop :=
  ∃ q : X, IsArcBetween A p q ∨ IsArcBetween A q p

/-- The set of endpoints carried by an arc. -/
def arcEndpointSet (A : Set X) : Set X :=
  {p | IsArcEndpoint A p}

/-- Munkres' general linear graph: a coherent union of arcs whose distinct edges meet, if at all,
in one common endpoint (FC02-C14-U001). -/
structure IsLinearGraph {ι : Type v} (edge : ι → Set X) : Prop where
  edge_isArc : ∀ i, IsArc (edge i)
  covers : ⋃ i, edge i = Set.univ
  edge_inter : ∀ ⦃i j : ι⦄, i ≠ j →
    (edge i ∩ edge j).Subsingleton ∧
      ∀ ⦃p⦄, p ∈ edge i ∩ edge j →
        IsArcEndpoint (edge i) p ∧ IsArcEndpoint (edge j) p
  coherent : Topology.IsCoherentWith (Set.range edge)

/-- The finite linear-graph notion used earlier by Munkres: a Hausdorff union of finitely many
arc edges, pairwise meeting only at common endpoints (FC02-C08-U023/FC02-C10-U016). -/
def IsFiniteLinearGraph {ι : Type v} (edge : ι → Set X) : Prop :=
  T2Space X ∧ (Set.range edge).Finite ∧
    (∀ i, IsArc (edge i)) ∧
    (⋃ i, edge i) = Set.univ ∧
    ∀ ⦃i j : ι⦄, i ≠ j →
      (edge i ∩ edge j).Subsingleton ∧
        ∀ ⦃p⦄, p ∈ edge i ∩ edge j →
          IsArcEndpoint (edge i) p ∧ IsArcEndpoint (edge j) p

/-- The vertices determined by the endpoints of the edge family. -/
def linearGraphVertexSet {ι : Type v} (edge : ι → Set X) : Set X :=
  {p | ∃ i, IsArcEndpoint (edge i) p}

/-- A subgraph is a union of edges of the ambient linear graph (definitional part of
FC02-C14-U005). Closedness and inheritance of the linear-graph axioms are theorem-sweep content. -/
def IsLinearSubgraph {ι : Type v} (edge : ι → Set X) (Y : Set X) : Prop :=
  ∃ s : Set ι, Y = ⋃ i ∈ s, edge i

/-- The closed star of a vertex is the union of all incident edges (FC02-C14-U008). -/
def linearGraphClosedStar {ι : Type v} (edge : ι → Set X) (x : X) : Set X :=
  ⋃ i ∈ {i | IsArcEndpoint (edge i) x}, edge i

/-- The star of a vertex is its closed star with all other vertices removed (FC02-C14-U008). -/
def linearGraphStar {ι : Type v} (edge : ι → Set X) (x : X) : Set X :=
  linearGraphClosedStar edge x \ (linearGraphVertexSet edge \ {x})

/-- A simple loop: a unit-interval path that closes only by identifying its two endpoints
(FC02-C10-U030). -/
def IsSimpleLoop (f : unitInterval → X) : Prop :=
  Continuous f ∧ f 0 = f 1 ∧ Set.InjOn f ({0, 1}ᶜ : Set unitInterval)

/-- A theta space is a Hausdorff space formed from three arcs with the same two endpoints and no
other pairwise intersections (FC02-C10-U019). -/
def IsThetaSpace (X : Type u) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∃ A B C : Set X, ∃ p q : X, p ≠ q ∧
    IsArcBetween A p q ∧ IsArcBetween B p q ∧ IsArcBetween C p q ∧
    A ∪ B ∪ C = Set.univ ∧
    A ∩ B = {p, q} ∧ A ∩ C = {p, q} ∧ B ∩ C = {p, q}

/-- The standard topological circle. -/
abbrev UnitCircle := Metric.sphere (0 : ℂ) 1

/-- A subspace is a circle when it is homeomorphic to the standard unit circle. -/
def IsCircle (A : Set X) : Prop :=
  Nonempty (UnitCircle ≃ₜ A)

/-- Munkres' finite wedge-of-circles definition (FC02-C11-U050). -/
def IsFiniteWedgeOfCircles {ι : Type v} (S : ι → Set X) (p : X) : Prop :=
  T2Space X ∧ (Set.range S).Finite ∧ (∀ i, IsCircle (S i)) ∧
    (⋃ i, S i) = Set.univ ∧
    ∀ ⦃i j : ι⦄, i ≠ j → S i ∩ S j = {p}

/-- Munkres' arbitrary wedge-of-circles definition: pairwise intersection at the wedge point plus
coherence of the ambient topology with the circle family (FC02-C11-U053). -/
def IsWedgeOfCircles {ι : Type v} (S : ι → Set X) (p : X) : Prop :=
  (∀ i, IsCircle (S i)) ∧ (⋃ i, S i) = Set.univ ∧
    (∀ ⦃i j : ι⦄, i ≠ j → S i ∩ S j = {p}) ∧
    Topology.IsCoherentWith (Set.range S)

end LeanCategories.Topology
