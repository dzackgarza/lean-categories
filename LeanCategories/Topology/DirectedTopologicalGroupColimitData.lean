/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Order.Category.Preord
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Directed colimit data for topological groups

Definition-level realization of Neukirch FC09-C04-U012.

For projective systems of topological groups, Mathlib's category
`Grp TopCat` already has the required limits.  For a directed diagram

`F : I ⥤ Grp TopCat`,

Neukirch's inductive limit has the algebraic filtered colimit of the stage
groups as carrier and the final topology for the canonical stage maps.
Mathlib already constructs the algebraic filtered colimit in `GrpCat`;
this file transports the internal topological groups to ordinary groups and
puts the literal final topology on that native group colimit.  Thus the group
operations are the actual quotient operations constructed by Mathlib, not
selected candidate operations.

Mathlib's filtered-colimit implementation proves representative independence
and the group laws as part of constructing that group.  Continuity of the
resulting group operations and the universal property in topological groups
remain later propositions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonObj

namespace LeanCategories.Topology

universe u

variable
  {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The native projective-limit object for a system of topological groups.

This is the already-library-owned half of FC09-C04-U012. -/
abbrev topologicalGroupProjectiveLimitData
    (F : Iᵒᵖ ⥤ Grp TopCat.{u}) : Grp TopCat.{u} :=
  limit F

/-- Forget the topology of each internal topological group while retaining its
actual group structure. -/
noncomputable def directedTopologicalGroupUnderlyingDiagram
    (F : I ⥤ Grp TopCat.{u}) : I ⥤ GrpCat.{u} :=
  F ⋙ (CategoryTheory.forget TopCat.{u}).mapGrp ⋙
    GrpTypeEquivalenceGrp.functor

/-- The algebraic filtered colimit of the stage groups.  This is Mathlib's
quotient construction, so multiplication, inverse, identity, and all group
laws are constructed here rather than supplied. -/
noncomputable def directedTopologicalGroupColimitGroupData
    (F : I ⥤ Grp TopCat.{u}) : GrpCat.{u} :=
  GrpCat.FilteredColimits.colimit (directedTopologicalGroupUnderlyingDiagram F)

/-- Neukirch's final topology on the algebraic direct limit. -/
noncomputable def directedTopologicalGroupColimitTopologyData
    (F : I ⥤ Grp TopCat.{u}) :
    TopologicalSpace (directedTopologicalGroupColimitGroupData F) :=
  ⨆ i, (F.obj i).X.str.coinduced
    ((GrpCat.FilteredColimits.colimitCocone
      (directedTopologicalGroupUnderlyingDiagram F)).ι.app i)

/-- The direct-limit group carrier equipped with Neukirch's final topology. -/
noncomputable def directedTopologicalGroupColimitCarrierData
    (F : I ⥤ Grp TopCat.{u}) : TopCat.{u} := by
  letI : TopologicalSpace (directedTopologicalGroupColimitGroupData F) :=
    directedTopologicalGroupColimitTopologyData F
  exact TopCat.of (directedTopologicalGroupColimitGroupData F)

/-- The canonical continuous map from a stage into the underlying topological
colimit.  Its group-homomorphism property belongs to the result layer because
the target group operations are only being specified in this file. -/
noncomputable def directedTopologicalGroupColimitInclusionData
    (F : I ⥤ Grp TopCat.{u}) (i : I) :
    (F.obj i).X ⟶ directedTopologicalGroupColimitCarrierData F := by
  refine TopCat.ofHom
    ⟨(GrpCat.FilteredColimits.colimitCocone
        (directedTopologicalGroupUnderlyingDiagram F)).ι.app i, ?_⟩
  rw [continuous_iff_coinduced_le]
  change
    (F.obj i).X.str.coinduced
        ((GrpCat.FilteredColimits.colimitCocone
          (directedTopologicalGroupUnderlyingDiagram F)).ι.app i) ≤
      directedTopologicalGroupColimitTopologyData F
  exact le_iSup (fun j =>
    (F.obj j).X.str.coinduced
      ((GrpCat.FilteredColimits.colimitCocone
        (directedTopologicalGroupUnderlyingDiagram F)).ι.app j)) i

/-- The multiplication in one stage of an internal topological group. -/
def directedTopologicalGroupStageMulData
    (F : I ⥤ Grp TopCat.{u}) (i : I)
    (x y : (F.obj i).X) : (F.obj i).X :=
  μ[(F.obj i).X] (x, y)

/-- The identity element in one stage of an internal topological group. -/
def directedTopologicalGroupStageOneData
    (F : I ⥤ Grp TopCat.{u}) (i : I) : (F.obj i).X :=
  η[(F.obj i).X] PUnit.unit

/-- The inverse in one stage of an internal topological group. -/
def directedTopologicalGroupStageInvData
    (F : I ⥤ Grp TopCat.{u}) (i : I)
    (x : (F.obj i).X) : (F.obj i).X :=
  ι[(F.obj i).X] x

/-- Identity, multiplication, and inversion on the direct-limit carrier. -/
structure DirectedTopologicalGroupColimitOperationData
    (F : I ⥤ Grp TopCat.{u}) where
  one : directedTopologicalGroupColimitCarrierData F
  mul :
    directedTopologicalGroupColimitCarrierData F →
      directedTopologicalGroupColimitCarrierData F →
        directedTopologicalGroupColimitCarrierData F
  inv :
    directedTopologicalGroupColimitCarrierData F →
      directedTopologicalGroupColimitCarrierData F

/-- Neukirch's direct-limit group operations, taken directly from Mathlib's
filtered-colimit group construction.  No candidate or choice is involved. -/
noncomputable def directedTopologicalGroupColimitOperationData
    (F : I ⥤ Grp TopCat.{u}) :
    DirectedTopologicalGroupColimitOperationData F := by
  letI : TopologicalSpace (directedTopologicalGroupColimitGroupData F) :=
    directedTopologicalGroupColimitTopologyData F
  exact
    { one := 1
      mul := (· * ·)
      inv := Inv.inv }

end LeanCategories.Topology
