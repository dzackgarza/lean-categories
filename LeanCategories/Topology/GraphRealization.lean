/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

/-!
# Topological realization of graph edge paths

Definition-level port for FC02-C14-U012, adapted from
`finite-graph-fundamental-group@dd57e3ab8bc5a7042fcc5498e778b008d87ac032`
to the pinned Mathlib API.
-/

open Set Function Quiver
open unitInterval
noncomputable section
universe u
namespace LeanCategories.Topology

abbrev graphRealizationPre (V : Type u) [Quiver.{u} V] :=
  WithDiscreteTopology V ⊕ Σ _e : WithDiscreteTopology (Quiver.Total V), I

abbrev graphDiscreteVertex {V : Type u} (v : V) : WithDiscreteTopology V :=
  WithTopology.toTopology (⊥ : TopologicalSpace V) v

abbrev graphDiscreteEdge {V : Type u} [Quiver.{u} V] (e : Quiver.Total V) :
    WithDiscreteTopology (Quiver.Total V) :=
  WithTopology.toTopology (⊥ : TopologicalSpace (Quiver.Total V)) e

inductive graphRealizationGenerator {V : Type u} [Quiver.{u} V] :
    graphRealizationPre V → graphRealizationPre V → Prop
  | source (e : Quiver.Total V) :
      graphRealizationGenerator
        (Sum.inr ⟨graphDiscreteEdge e, 0⟩) (Sum.inl (graphDiscreteVertex e.left))
  | target (e : Quiver.Total V) :
      graphRealizationGenerator
        (Sum.inr ⟨graphDiscreteEdge e, 1⟩) (Sum.inl (graphDiscreteVertex e.right))

instance graphRealizationSetoid {V : Type u} [Quiver.{u} V] :
    Setoid (graphRealizationPre V) :=
  Relation.EqvGen.setoid (graphRealizationGenerator (V := V))

abbrev graphRealization (V : Type u) [Quiver.{u} V] :=
  Quotient (graphRealizationSetoid (V := V))

abbrev graphRealizationQuotient {V : Type u} [Quiver.{u} V] :
    graphRealizationPre V → graphRealization V := Quotient.mk'

def graphVertex {V : Type u} [Quiver.{u} V] (v : V) : graphRealization V :=
  graphRealizationQuotient (Sum.inl (graphDiscreteVertex v))

def graphEdgePath {V : Type u} [Quiver.{u} V] (e : Quiver.Total V) :
    C(I, graphRealization V) where
  toFun t := graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩)
  continuous_toFun :=
    continuous_quotient_mk'.comp <|
      continuous_inr.comp (continuous_sigmaMk (i := graphDiscreteEdge e))

@[simp] theorem graphEdgePath_zero {V : Type u} [Quiver.{u} V] (e : Quiver.Total V) :
    graphEdgePath e 0 = graphVertex e.left := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (graphRealizationGenerator.source e))

@[simp] theorem graphEdgePath_one {V : Type u} [Quiver.{u} V] (e : Quiver.Total V) :
    graphEdgePath e 1 = graphVertex e.right := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (graphRealizationGenerator.target e))

def graphRealizationForwardPath {V : Type u} [Quiver.{u} V]
    {a b : V} (e : a ⟶ b) : Path (graphVertex a) (graphVertex b) where
  toContinuousMap := graphEdgePath ⟨a, b, e⟩
  source' := graphEdgePath_zero ⟨a, b, e⟩
  target' := graphEdgePath_one ⟨a, b, e⟩

def graphRealizationSymmetricEdgePath {V : Type u} [Quiver.{u} V]
    {a b : V} (e : (Quiver.symmetrifyQuiver V).Hom a b) :
    Path (graphVertex (V := V) a) (graphVertex (V := V) b) :=
  match e with
  | Sum.inl e => graphRealizationForwardPath e
  | Sum.inr e => (graphRealizationForwardPath e).symm

def graphRealizationQuiverPath {V : Type u} [Quiver.{u} V]
    {a b : V}
    (p : @Quiver.Path (Quiver.Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    Path (graphVertex (V := V) a) (graphVertex (V := V) b) := by
  induction p with
  | nil => exact Path.refl _
  | cons p e ih => exact ih.trans (graphRealizationSymmetricEdgePath e)

end LeanCategories.Topology
