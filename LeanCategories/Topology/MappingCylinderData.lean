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

/-- The target-end inclusion `Y → M_f` as a continuous map. -/
def mappingCylinderTargetInclusion {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(Y, MappingCylinder f) where
  toFun := mappingCylinderMkTarget f
  continuous_toFun := continuous_quotient_mk'.comp continuous_inr

/-- Evaluation of a mapping-cylinder classifier at the target end. -/
def mappingCylinderClassValue {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    MappingCylinderClass X Y → Y
  | .target y => y
  | .cylinder p => f p.1

/-- The representative-level projection of a mapping cylinder onto its target
end.  It sends the whole cylinder line over `x` to `f x` and is the
identity on the target summand. -/
def mappingCylinderProjectionPre {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (z : MappingCylinderPre X Y) : Y :=
  mappingCylinderClassValue f (mappingCylinderClassify f z)

/-- Hatcher's canonical projection `M_f → Y` onto the target end. -/
def mappingCylinderProjection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(MappingCylinder f, Y) where
  toFun :=
    Quotient.lift
      (mappingCylinderProjectionPre f)
      (by
        intro a b h
        change mappingCylinderClassify f a = mappingCylinderClassify f b at h
        exact congrArg (mappingCylinderClassValue f) h)
  continuous_toFun :=
    have hpre : Continuous (mappingCylinderProjectionPre f) := by
      have hleft : Continuous (fun p : X × unitInterval => f p.1) :=
        f.continuous.comp continuous_fst
      have hright : Continuous (fun y : Y => y) := continuous_id
      have heq :
          mappingCylinderProjectionPre f =
            Sum.elim (fun p : X × unitInterval => f p.1) (fun y : Y => y) := by
        funext z
        rcases z with p | y
        · by_cases hp : p.2 = 1
          · simp [mappingCylinderProjectionPre, mappingCylinderClassValue,
              mappingCylinderClassify, hp]
          · simp [mappingCylinderProjectionPre, mappingCylinderClassValue,
              mappingCylinderClassify, hp]
        · rfl
      rw [heq]
      exact Continuous.sumElim hleft hright
    hpre.quotient_lift (by
      intro a b h
      change mappingCylinderClassify f a = mappingCylinderClassify f b at h
      exact congrArg (mappingCylinderClassValue f) h)

end LeanCategories.Topology
