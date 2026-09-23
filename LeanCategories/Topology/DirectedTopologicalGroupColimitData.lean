/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.Order.Category.Preord
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Directed colimit data for topological groups

Definition-level realization of Neukirch FC09-C04-U012.

For projective systems of topological groups, Mathlib's category
`Grp TopCat` already has the required limits.  The surviving source-level
gap is the inductive-limit construction.  For a directed diagram

`F : I ⥤ Grp TopCat`,

the underlying topological colimit already exists in `TopCat`.  Neukirch
defines its group operations by choosing representatives in a common stage:

* the product of the classes of `x,y ∈ G_i` is the class of `xy`;
* the inverse of the class of `x ∈ G_i` is the class of `x⁻¹`;
* the identity is the class of the identity of any stage.

Sweep III records precisely this carrier/topology and these stagewise formulas.
Independence of representatives/stages, the group axioms, continuity,
homomorphism properties of the canonical maps, and the colimit universal
property in topological groups are result-layer statements.
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

/-- The underlying topological inductive limit of a directed system of
topological groups. -/
abbrev directedTopologicalGroupColimitCarrierData
    (F : I ⥤ Grp TopCat.{u}) : TopCat.{u} :=
  colimit (F ⋙ Grp.forget TopCat)

/-- The canonical continuous map from a stage into the underlying topological
colimit.  Its group-homomorphism property belongs to the result layer because
the target group operations are only being specified in this file. -/
def directedTopologicalGroupColimitInclusionData
    (F : I ⥤ Grp TopCat.{u}) (i : I) :
    (F.obj i).X ⟶ directedTopologicalGroupColimitCarrierData F :=
  colimit.ι (F ⋙ Grp.forget TopCat) i

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

end LeanCategories.Topology
