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

/-- Raw identity, multiplication, and inversion operations on the underlying
topological colimit.

No group laws or continuity proofs are fields of this structure. -/
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

/-- The exact representative graph for Neukirch's direct-limit group
operations.

The identity is the image of the identity at every stage, multiplication of
two elements represented in one stage is represented by their stagewise
product, and inversion is represented by stagewise inversion.  Consistency of
these equations across different stages and representatives is deliberately
not proved here. -/
def IsDirectedTopologicalGroupColimitOperationData
    (F : I ⥤ Grp TopCat.{u})
    (D : DirectedTopologicalGroupColimitOperationData F) : Prop :=
  (∀ i : I,
      D.one =
        directedTopologicalGroupColimitInclusionData F i
          (directedTopologicalGroupStageOneData F i)) ∧
  (∀ (i : I) (x y : (F.obj i).X),
      D.mul
          (directedTopologicalGroupColimitInclusionData F i x)
          (directedTopologicalGroupColimitInclusionData F i y) =
        directedTopologicalGroupColimitInclusionData F i
          (directedTopologicalGroupStageMulData F i x y)) ∧
  (∀ (i : I) (x : (F.obj i).X),
      D.inv (directedTopologicalGroupColimitInclusionData F i x) =
        directedTopologicalGroupColimitInclusionData F i
          (directedTopologicalGroupStageInvData F i x))

/-- A default raw operation triple used only to make the candidate type
inhabited for `Classical.epsilon`.

This declaration asserts no source equation. -/
def directedTopologicalGroupColimitDefaultOperationData
    (F : I ⥤ Grp TopCat.{u}) :
    DirectedTopologicalGroupColimitOperationData F := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  let z : directedTopologicalGroupColimitCarrierData F :=
    directedTopologicalGroupColimitInclusionData F i
      (directedTopologicalGroupStageOneData F i)
  exact
    { one := z
      mul := fun _ _ => z
      inv := fun _ => z }

/-- Neukirch's direct-limit group-operation data, selected from the exact
stage-representative graph.

The theorem layer proves that this selected triple satisfies
`IsDirectedTopologicalGroupColimitOperationData`, then derives the group laws,
continuity, and the homomorphism properties of the canonical inclusions.
Sweep III performs none of those proofs. -/
def directedTopologicalGroupColimitOperationData
    (F : I ⥤ Grp TopCat.{u}) :
    DirectedTopologicalGroupColimitOperationData F :=
  @Classical.epsilon
    (DirectedTopologicalGroupColimitOperationData F)
    ⟨directedTopologicalGroupColimitDefaultOperationData F⟩
    (IsDirectedTopologicalGroupColimitOperationData F)

end LeanCategories.Topology
