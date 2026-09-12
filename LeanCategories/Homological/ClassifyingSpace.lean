/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Classifying spaces of groups

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.10.4,
§6.10, pp. 203--205 (FC05-C06-U125).

A classifying space `BG` is a CW complex with fundamental group `G` and
contractible universal cover `EG`.  This file records exactly the data of such
a model.  Identifying group (co)homology with the (co)homology of `BG` is the
subsequent theorem layer.
-/

@[expose] public section

namespace LeanCategories.Homological

universe uG uB uE

/-- Data of a classifying-space model `BG` for a group `G`, together with its
contractible covering space `EG`.

Source: Weibel, Definition 6.10.4, pp. 203--205 (FC05-C06-U125). -/
structure ClassifyingSpaceData
    (G : Type uG) [Group G]
    (BG : Type uB) [TopologicalSpace BG]
    (EG : Type uE) [TopologicalSpace EG] where
  /-- Basepoint used to identify the fundamental group with `G`. -/
  basepoint : BG
  /-- The base space is a CW complex. -/
  cw : Topology.CWComplex (Set.univ : Set BG)
  /-- The chosen universal-cover projection `EG → BG`. -/
  cover : EG → BG
  /-- The chosen projection is a covering map. -/
  isCoveringMap : IsCoveringMap cover
  /-- The universal cover is contractible. -/
  contractible : ContractibleSpace EG
  /-- The fundamental group of `BG` is the prescribed group `G`. -/
  fundamentalGroupEquiv : FundamentalGroup BG basepoint ≃* G

end LeanCategories.Homological
