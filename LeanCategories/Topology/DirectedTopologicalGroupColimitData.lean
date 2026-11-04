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

/-- The group structure carried by a group object in `TopCat`: each operation of the
internal group is a morphism of topological spaces, hence a function of points, and the
internal group axioms are the pointwise group laws. -/
noncomputable instance grpObjGroup (X : TopCat.{u}) [GrpObj X] : Group X where
  mul a b := μ[X] (a, b)
  one := η[X] PUnit.unit
  inv a := ι[X] a
  mul_assoc a b c := by
    have h := MonObj.mul_assoc (X := X)
    exact ConcreteCategory.congr_hom h ((a, b), c)
  one_mul a := by
    have h := MonObj.one_mul (X := X)
    exact ConcreteCategory.congr_hom h (PUnit.unit, a)
  mul_one a := by
    have h := MonObj.mul_one (X := X)
    exact ConcreteCategory.congr_hom h (a, PUnit.unit)
  inv_mul_cancel a := by
    have h := GrpObj.left_inv (X := X)
    exact ConcreteCategory.congr_hom h a

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
    (F : I ⥤ Grp TopCat.{u}) : I ⥤ GrpCat.{u} where
  obj i := GrpCat.of (F.obj i).X
  map f := GrpCat.ofHom
    { toFun := fun a => (F.map f).hom.hom a
      map_one' := by
        have h := IsMonHom.one_hom (f := (F.map f).hom.hom)
        exact ConcreteCategory.congr_hom h PUnit.unit
      map_mul' := fun a b => by
        have h := IsMonHom.mul_hom (f := (F.map f).hom.hom)
        exact ConcreteCategory.congr_hom h (a, b) }
  map_id i := by
    ext a
    simp
  map_comp f g := by
    ext a
    simp

/-- The algebraic filtered colimit of the stage groups.  This is Mathlib's
quotient construction, so multiplication, inverse, identity, and all group
laws are constructed here rather than supplied. -/
noncomputable def directedTopologicalGroupColimitGroupData
    (F : I ⥤ Grp TopCat.{u}) : GrpCat.{u} :=
  let D : I ⥤ GrpCat.{u} := directedTopologicalGroupUnderlyingDiagram F
  GrpCat.FilteredColimits.colimit D

/-- Mathlib's filtered-colimit cocone for the underlying group diagram, with the
diagram's universes pinned so that later `ι.app` uses do not leave them as metavariables. -/
noncomputable def directedTopologicalGroupUnderlyingCocone (F : I ⥤ Grp TopCat.{u}) :
    Cocone (directedTopologicalGroupUnderlyingDiagram F : I ⥤ GrpCat.{u}) :=
  let D : I ⥤ GrpCat.{u} := directedTopologicalGroupUnderlyingDiagram F
  GrpCat.FilteredColimits.colimitCocone D

/-- Neukirch's final topology on the algebraic direct limit. -/
noncomputable def directedTopologicalGroupColimitTopologyData
    (F : I ⥤ Grp TopCat.{u}) :
    TopologicalSpace (directedTopologicalGroupColimitGroupData F) :=
  ⨆ i, (F.obj i).X.str.coinduced
    ((directedTopologicalGroupUnderlyingCocone F).ι.app i)

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
  letI : TopologicalSpace (directedTopologicalGroupColimitGroupData F) :=
    directedTopologicalGroupColimitTopologyData F
  refine TopCat.ofHom
    ⟨(directedTopologicalGroupUnderlyingCocone F).ι.app i, ?_⟩
  refine continuous_iff_coinduced_le.mpr ?_
  change
    (F.obj i).X.str.coinduced
        ((directedTopologicalGroupUnderlyingCocone F).ι.app i) ≤
      directedTopologicalGroupColimitTopologyData F
  exact le_iSup (fun j =>
    (F.obj j).X.str.coinduced
      ((directedTopologicalGroupUnderlyingCocone F).ι.app j)) i

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
  letI : Group (directedTopologicalGroupColimitCarrierData F) :=
    inferInstanceAs (Group (directedTopologicalGroupColimitGroupData F))
  exact
    { one := 1
      mul := (· * ·)
      inv := Inv.inv }

end LeanCategories.Topology
