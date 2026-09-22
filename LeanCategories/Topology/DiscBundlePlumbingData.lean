/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Plumbing disc bundles along a tree

Definition-level realization of Peters--Sterk FC11-C04-U049.

The source starts with weighted oriented two-disc bundles over `S²`.  For every
edge of a tree, one chooses a small base disc in each endpoint bundle, writes
the bundle over that disc as `D²_base × D²_fiber`, and identifies the two
product regions after interchanging base and fibre coordinates.

The target library has the generic topological ingredients but no owner for
the weight/Euler-number classification of oriented disc bundles over `S²`.
That missing global geometric predicate is therefore an explicit interface.
The local bundle charts, the base/fibre flip, the equivalence relation generated
by the edge identifications, and the resulting quotient topology are all
constructed here.  Claims that the quotient is a manifold with boundary, or
identifications of its boundary, are result-layer content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u v

/-- The standard closed two-disc used for both base and fibre coordinates in
the plumbing charts. -/
abbrev PlumbingDisc : Type u := TopCat.disk.{u} 2

/-- The standard two-sphere serving as the base of each disc-bundle piece. -/
abbrev PlumbingSphere : Type u := TopCat.sphere.{u} 2

/-- The source gluing map `(z,w) ↦ (w,z)` between two product disc charts. -/
def plumbingFlip : PlumbingDisc.{u} × PlumbingDisc.{u} ≃ₜ
    PlumbingDisc.{u} × PlumbingDisc.{u} :=
  Homeomorph.prodComm _ _

/-- Missing global geometric interface: a total space and projection represent
the oriented two-disc bundle over `S²` with the indicated integral weight.

This isolates precisely the disc-bundle classification layer that is absent
from the target library; the plumbing operation itself does not assume any
unproved classification theorem. -/
structure WeightedDiscBundleInterface where
  IsOrientedDiscBundleOfWeight :
    (weight : ℤ) → (totalSpace : TopCat.{u}) →
      (totalSpace → PlumbingSphere.{u}) → Prop

/-- Source data for plumbing weighted disc bundles along a finite tree.

Each oriented incidence `v -- w` carries a local trivialization of the bundle
at `v` together with a small base disc inside that chart.  Distinct incidences
at a vertex use disjoint base discs, matching the usual simultaneous plumbing
construction. -/
structure DiscBundleTreePlumbingData
    (V : Type v) [Fintype V] [DecidableEq V]
    (I : WeightedDiscBundleInterface.{u}) where
  graph : SimpleGraph V
  isTree : graph.IsTree
  weight : V → ℤ
  totalSpace : V → TopCat.{u}
  projection : ∀ v, totalSpace v → PlumbingSphere.{u}
  isWeightedDiscBundle : ∀ v,
    I.IsOrientedDiscBundleOfWeight (weight v) (totalSpace v) (projection v)
  localTrivialization : ∀ {v w}, graph.Adj v w →
    Bundle.Trivialization PlumbingDisc.{u} (projection v)
  baseDisc : ∀ {v w} (_h : graph.Adj v w), Set PlumbingSphere.{u}
  baseDisc_subset : ∀ {v w} (h : graph.Adj v w),
    baseDisc h ⊆ (localTrivialization h).baseSet
  baseDiscChart : ∀ {v w} (h : graph.Adj v w),
    baseDisc h ≃ₜ PlumbingDisc.{u}
  baseDiscs_disjoint : ∀ {v w z}
    (hvw : graph.Adj v w) (hvz : graph.Adj v z),
    w ≠ z → Disjoint (baseDisc hvw) (baseDisc hvz)

/-- The part of the total space over the chosen base disc for an oriented tree
edge. -/
def discBundlePlumbingRegion
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I)
    {v w : V} (h : P.graph.Adj v w) : Set (P.totalSpace v) :=
  P.projection v ⁻¹' P.baseDisc h

/-- Product coordinates `D²_base × D²_fiber` on a chosen plumbing region. -/
def discBundlePlumbingChart
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I)
    {v w : V} (h : P.graph.Adj v w) :
    discBundlePlumbingRegion P h ≃ₜ
      PlumbingDisc.{u} × PlumbingDisc.{u} :=
  ((P.localTrivialization h).preimageHomeomorph (P.baseDisc_subset h)).trans
    ((P.baseDiscChart h).prodCongr (Homeomorph.refl _))

/-- One generating identification in the plumbing quotient: points in chart
regions belonging to adjacent vertices are identified when their coordinates
agree after swapping base and fibre. -/
def discBundlePlumbingIdentification
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I)
    (x y : Σ v, P.totalSpace v) : Prop :=
  ∃ h : P.graph.Adj x.1 y.1,
    ∃ hx : x.2 ∈ discBundlePlumbingRegion P h,
      ∃ hy : y.2 ∈ discBundlePlumbingRegion P h.symm,
        discBundlePlumbingChart P h ⟨x.2, hx⟩ =
          plumbingFlip (discBundlePlumbingChart P h.symm ⟨y.2, hy⟩)

/-- The equivalence relation generated by all edgewise base/fibre-flip
identifications. -/
def discBundlePlumbingSetoid
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I) : Setoid (Σ v, P.totalSpace v) :=
  Relation.EqvGen.setoid (discBundlePlumbingIdentification P)

/-- The topological plumbing of the supplied weighted disc bundles along the
tree: the disjoint union of the bundle total spaces modulo the generated
base/fibre-flip identifications, with the quotient topology. -/
abbrev plumbedDiscBundleTree
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I) : Type (max u v) :=
  Quotient (discBundlePlumbingSetoid P)

/-- The plumbing quotient bundled as a topological space. -/
def plumbedDiscBundleTreeTopCat
    {V : Type v} [Fintype V] [DecidableEq V]
    {I : WeightedDiscBundleInterface.{u}}
    (P : DiscBundleTreePlumbingData V I) : TopCat.{max u v} :=
  TopCat.of (plumbedDiscBundleTree P)

end LeanCategories.Topology
