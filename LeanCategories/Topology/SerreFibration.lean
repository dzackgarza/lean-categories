/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SurfaceTriangulation
public import LeanCategories.Topology.HomotopyLifting
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Serre fibrations

Weibel, *An Introduction to Homological Algebra*, Definition 5.3.1, p. 127
(FC05-C05-U015), following Mac Lane, *Homology*, XI.2.

Weibel tests the homotopy lifting property against finite polyhedra.  Munkres,
*Elements of Algebraic Topology*, §§2–3, models a polyhedron by a simplicial complex and its
geometric realization.  The finite-polyhedron predicate below packages precisely a finite abstract
simplicial complex together with a homeomorphism from its barycentric realization.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set
open scoped unitInterval

/-- The finite set of simplices of an abstract simplicial complex on a finite vertex set.
This is the finite-complex data underlying a finite polyhedron in Munkres,
*Elements of Algebraic Topology*, §§2–3. -/
def finiteSimplicialFaces {V : Type*} [Fintype V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) : Finset (Finset V) :=
  (K : Set (Finset V)).toFinite.toFinset

/-- A finite polyhedron presented by a finite abstract simplicial complex and a homeomorphism from
its barycentric geometric realization.  This is the standard simplicial-complex definition of a
finite polyhedron; see Munkres, *Elements of Algebraic Topology*, §§2–3. -/
structure FinitePolyhedronStructure (P : Type*) [TopologicalSpace P] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : AbstractSimplicialComplex Vertex
  homeo : GeometricRealization Vertex (finiteSimplicialFaces complex) ≃ₜ P

attribute [instance] FinitePolyhedronStructure.vertexFintype
attribute [instance] FinitePolyhedronStructure.vertexDecidableEq

/-- A topological space is a finite polyhedron when it is homeomorphic to the realization of a
finite simplicial complex.  See Munkres, *Elements of Algebraic Topology*, §§2–3. -/
def IsFinitePolyhedron (P : Type*) [TopologicalSpace P] : Prop :=
  Nonempty (FinitePolyhedronStructure P)

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- A Serre fibration in the sense of Weibel, *An Introduction to Homological Algebra*,
Definition 5.3.1, p. 127: a based continuous map with the homotopy lifting property against every
finite polyhedron.  The fiber in Weibel's displayed sequence is represented canonically by
`SerreFibration.Fiber`, the inverse image of `basePoint`. -/
structure SerreFibration (π : C(E, B)) where
  /-- The chosen basepoint of the total space in Weibel Definition 5.3.1. -/
  totalPoint : E
  /-- The chosen basepoint `*_B` of the base in Weibel Definition 5.3.1. -/
  basePoint : B
  /-- The projection is a map of based spaces. -/
  map_point : π totalPoint = basePoint
  /-- Weibel's homotopy lifting property for every finite polyhedron `P` and unit interval `I`:
a homotopy in the base whose time-zero map lifts through `π` admits a homotopy lift with that
prescribed time-zero map. -/
  liftHomotopy : ∀ (P : Type*) [TopologicalSpace P],
    IsFinitePolyhedron P → HasHomotopyLiftingProperty π P

namespace SerreFibration

variable {π : C(E, B)} (S : SerreFibration π)

/-- The fiber `F = π⁻¹(*_B)` in Weibel Definition 5.3.1, p. 127. -/
def Fiber := {e : E // π e = S.basePoint}

instance : TopologicalSpace S.Fiber := by
  unfold Fiber
  infer_instance

/-- The inclusion `F → E` in the defining Serre-fibration sequence of Weibel Definition 5.3.1. -/
def fiberInclusion : C(S.Fiber, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The basepoint of the fiber, induced by the chosen basepoint of the total space. -/
def fiberPoint : S.Fiber :=
  ⟨S.totalPoint, S.map_point⟩

end SerreFibration

end LeanCategories.Topology
