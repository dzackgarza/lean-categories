/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

/-!
# Mapping-cone quotient data

Hatcher, *Algebraic Topology*, Chapter 0 (FC07-C00-U029).

This file records only the quotient carrier for `Y ∪_f CX` and its canonical
quotient maps.  The quotient-identification laws and comparison with `M_f / X`
are result-layer material and are intentionally not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u v

/-- The disjoint sum before the mapping-cone identifications are imposed. -/
abbrev MappingConePre (X : Type u) (Y : Type v) := Y ⊕ (X × unitInterval)

/-- Class labels for the mapping-cone quotient. -/
inductive MappingConeClass (X : Type u) (Y : Type v)
  | base
  | target (y : Y)
  | cylinder (p : X × unitInterval)

/-- Classify mapping-cone representatives: collapse the bottom cylinder slice,
attach the top slice along `f`, and retain every interior cylinder point. -/
noncomputable def mappingConeClassify {X : Type u} {Y : Type v} (f : X → Y)
    (p : MappingConePre X Y) : MappingConeClass X Y :=
  match p with
  | Sum.inl y => .target y
  | Sum.inr (x, t) =>
      if t = 0 then .base
      else if t = 1 then .target (f x)
      else .cylinder (x, t)

/-- The equivalence relation defining the mapping cone of the continuous map `f`. -/
noncomputable def mappingConeSetoid {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (f : ContinuousMap X Y) :
    Setoid (MappingConePre X Y) :=
  Setoid.ker (mappingConeClassify f)

/-- Hatcher's mapping-cone carrier `Y ∪_f CX`. -/
noncomputable abbrev MappingCone {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (f : ContinuousMap X Y) : Type (max u v) :=
  Quotient (mappingConeSetoid f)

/-- The quotient map from the target summand into the mapping cone. -/
noncomputable def mappingConeMkTarget {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (f : ContinuousMap X Y) (y : Y) : MappingCone f :=
  Quotient.mk (mappingConeSetoid f) (Sum.inl y)

/-- The quotient map from the cylinder summand into the mapping cone. -/
noncomputable def mappingConeMkCylinder {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (f : ContinuousMap X Y) (x : X) (t : unitInterval) : MappingCone f :=
  Quotient.mk (mappingConeSetoid f) (Sum.inr (x, t))

end LeanCategories.Topology
