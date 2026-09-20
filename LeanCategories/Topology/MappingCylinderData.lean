/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Mapping-cylinder quotient data

Definition-level realization of Hatcher FC07-C00-U002.

For a continuous map `f : X → Y`, the mapping cylinder is

`M_f = ((X × I) ⊔ Y) / ((x,1) ~ f(x))`.

This file records exactly that quotient carrier and its two canonical maps.
The statement that the target copy of `Y` is a deformation retract is a
result clause and is not proved or carried as constructor data in Sweep III.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

universe u v

/-- The disjoint union before identifying the top of the cylinder with the
target. -/
abbrev MappingCylinderPre (X : Type u) (Y : Type v) :=
  Sum (X × unitInterval) Y

/-- Labels for equivalence classes in the mapping cylinder. -/
inductive MappingCylinderClass (X : Type u) (Y : Type v)
  | target (y : Y)
  | cylinder (p : X × unitInterval)

/-- Classifier imposing exactly `(x,1) ~ f(x)`. -/
def mappingCylinderClassify {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    MappingCylinderPre X Y → MappingCylinderClass X Y
  | .inr y => .target y
  | .inl p => if p.2 = 1 then .target (f p.1) else .cylinder p

/-- The equivalence relation defining the mapping cylinder. -/
def mappingCylinderSetoid {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    Setoid (MappingCylinderPre X Y) :=
  Setoid.ker (mappingCylinderClassify f)

/-- Hatcher's mapping cylinder `M_f`. -/
abbrev MappingCylinder {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :=
  Quotient (mappingCylinderSetoid f)

/-- The canonical cylinder map `X × I → M_f`. -/
def mappingCylinderMkCylinder {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) (t : unitInterval) : MappingCylinder f :=
  Quotient.mk _ (.inl (x, t))

/-- The canonical target map `Y → M_f`. -/
def mappingCylinderMkTarget {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (y : Y) : MappingCylinder f :=
  Quotient.mk _ (.inr y)

end LeanCategories.Topology
