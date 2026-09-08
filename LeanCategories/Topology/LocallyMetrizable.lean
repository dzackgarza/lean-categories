/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

namespace LeanCategories.Topology

open Set

universe u

/-- A topological space is locally metrizable when every point has a neighborhood
whose subspace topology is metrizable. This is Munkres FC02-C06-U031 and adapts
the `PiBase.LocallyMetrizableSpace` interface from
`felixpernegger/pibase-lean@ff65933ec375d67a44013e4a26140893cab27acb` (Apache-2.0). -/
class LocallyMetrizableSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_metrizable_mem_nhds : ∀ x : X, ∃ s : Set X, s ∈ _root_.nhds x ∧ TopologicalSpace.MetrizableSpace s

end LeanCategories.Topology
