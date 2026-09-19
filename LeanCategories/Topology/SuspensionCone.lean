/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Unreduced cone and suspension

Definition-level realization of Hatcher FC07-C00-U019.  The cone collapses the bottom
slice of `X × I`, while the suspension collapses the bottom and top slices separately.
Only the quotient data is recorded here.
-/

noncomputable section

namespace LeanCategories.Topology

universe u

/-- Class labels for the unreduced cone quotient. -/
inductive ConeClass (X : Type u)
  | base
  | point (p : X × unitInterval)

/-- Classify a cylinder point by collapsing the bottom slice `X × {0}`. -/
noncomputable def coneClassify (X : Type u) (p : X × unitInterval) : ConeClass X :=
  if p.2 = 0 then ConeClass.base else ConeClass.point p

/-- The equivalence relation whose only non-singleton class is the bottom slice. -/
noncomputable def coneSetoid (X : Type u) : Setoid (X × unitInterval) :=
  Setoid.ker (coneClassify X)

/-- Hatcher's unreduced cone `CX = (X × I)/(X × {0})`. -/
noncomputable abbrev Cone (X : Type u) [TopologicalSpace X] := Quotient (coneSetoid X)

/-- The quotient map into the unreduced cone. -/
noncomputable def coneMk (X : Type u) [TopologicalSpace X]
    (x : X) (t : unitInterval) : Cone X :=
  Quotient.mk (coneSetoid X) (x, t)

/-- Class labels for the unreduced suspension quotient. -/
inductive SuspensionClass (X : Type u)
  | bottom
  | top
  | point (p : X × unitInterval)

/-- Classify a cylinder point by collapsing each endpoint slice to its own class. -/
noncomputable def suspensionClassify (X : Type u) (p : X × unitInterval) : SuspensionClass X :=
  if p.2 = 0 then SuspensionClass.bottom
  else if p.2 = 1 then SuspensionClass.top
  else SuspensionClass.point p

/-- The equivalence relation collapsing `X × {0}` and `X × {1}` separately. -/
noncomputable def suspensionSetoid (X : Type u) : Setoid (X × unitInterval) :=
  Setoid.ker (suspensionClassify X)

/-- Hatcher's unreduced suspension `SX = (X × I)/(X × {0}, X × {1})`. -/
noncomputable abbrev Suspension (X : Type u) [TopologicalSpace X] :=
  Quotient (suspensionSetoid X)

/-- The quotient map into the unreduced suspension. -/
noncomputable def suspensionMk (X : Type u) [TopologicalSpace X]
    (x : X) (t : unitInterval) : Suspension X :=
  Quotient.mk (suspensionSetoid X) (x, t)

end LeanCategories.Topology
