/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Topological join

Definition-level realization of Hatcher FC07-C00-U020.  The join of `X` and `Y` is the
quotient of `X × Y × I` that forgets the `Y` coordinate at the bottom endpoint and the
`X` coordinate at the top endpoint.  Only the quotient data is recorded here.
-/

noncomputable section

namespace LeanCategories.Topology

universe u v

/-- Cylinder used before taking the join quotient. -/
abbrev JoinCylinder (X : Type u) (Y : Type v) := (X × Y) × unitInterval

/-- Class labels for the topological join quotient. -/
inductive JoinClass (X : Type u) (Y : Type v)
  | bottom (x : X)
  | top (y : Y)
  | point (p : JoinCylinder X Y)

/-- Classify a join-cylinder point by the coordinate that survives at each endpoint. -/
noncomputable def joinClassify (X : Type u) (Y : Type v)
    (p : JoinCylinder X Y) : JoinClass X Y :=
  if p.2 = 0 then JoinClass.bottom p.1.1
  else if p.2 = 1 then JoinClass.top p.1.2
  else JoinClass.point p

/-- The equivalence relation defining the classical topological join. -/
noncomputable def joinSetoid (X : Type u) (Y : Type v) : Setoid (JoinCylinder X Y) :=
  Setoid.ker (joinClassify X Y)

/-- Hatcher's join `X * Y`. -/
noncomputable abbrev Join (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :=
  Quotient (joinSetoid X Y)

/-- The quotient map into the topological join. -/
noncomputable def joinMk (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (t : unitInterval) : Join X Y :=
  Quotient.mk (joinSetoid X Y) ((x, y), t)

end LeanCategories.Topology
