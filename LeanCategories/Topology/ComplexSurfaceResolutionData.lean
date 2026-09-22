/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Complex-surface resolution data

Definition-level support for complex-surface resolution constructions occurring
in Peters--Sterk FC11.

The checked Lean ecosystem has no category of possibly singular complex
analytic surfaces with a minimal-resolution construction.  Sweep III therefore
separates the raw resolution data (a source surface and a map) from the
predicates that say this data is analytic, is an isomorphism off the exceptional
locus, and is minimal.  No existence, uniqueness, smoothness, holomorphicity,
or minimality theorem is proved here.

The interface also retains the isolated-singularity and exceptional-curve
predicates used by the Hirzebruch--Jung construction.  This is one owner for
the missing analytic vocabulary rather than parallel source-specific wrappers.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

/-- Predicate interface for the complex-analytic notions needed to state
surface-resolution definitions before the corresponding analytic theory is
available in the target library.

The fields are predicates, not evidence for any particular surface or map. -/
structure ComplexSurfaceResolutionInterface where
  IsSmoothComplexSurface : TopCat.{u} → Prop
  IsIsolatedSurfaceSingularity :
    (X : TopCat.{u}) → X → Prop
  IsHolomorphicMap :
    {X Y : TopCat.{u}} → (X → Y) → Prop
  IsBiholomorphicOutside :
    {X Y : TopCat.{u}} → (f : X → Y) → Set Y → Prop
  IsMinimalResolution :
    {X Y : TopCat.{u}} → (f : X → Y) → Prop
  IsProjectiveLineCurve :
    {X : TopCat.{u}} → Set X → Prop
  HasSelfIntersection :
    {X : TopCat.{u}} → Set X → ℤ → Prop
  MeetTransverselyInOnePoint :
    {X : TopCat.{u}} → Set X → Set X → Prop

namespace ComplexSurfaceResolutionInterface

/-- Specialization of biholomorphicity away from an exceptional locus to a
single isolated target point. -/
def IsBiholomorphicOutsideFiber
    (I : ComplexSurfaceResolutionInterface.{u})
    {X Y : TopCat.{u}} (f : X → Y) (p : Y) : Prop :=
  I.IsBiholomorphicOutside f {p}

end ComplexSurfaceResolutionInterface

/-- Raw data of a resolution candidate of a topological target.

Analytic and minimality conditions are deliberately not bundled into the
constructor, so defining or selecting the data does not require proving them. -/
structure ComplexSurfaceResolutionData (Y : TopCat.{u}) where
  source : TopCat.{u}
  map : source → Y

instance (Y : TopCat.{u}) : Nonempty (ComplexSurfaceResolutionData Y) :=
  ⟨{ source := Y, map := id }⟩

/-- The defining resolution conditions on raw complex-surface resolution data,
with a specified exceptional locus in the target. -/
def IsComplexSurfaceResolutionData
    (I : ComplexSurfaceResolutionInterface.{u})
    {Y : TopCat.{u}} (exceptionalLocus : Set Y)
    (R : ComplexSurfaceResolutionData Y) : Prop :=
  I.IsSmoothComplexSurface R.source ∧
    I.IsHolomorphicMap R.map ∧
      I.IsBiholomorphicOutside R.map exceptionalLocus

/-- The defining conditions for a minimal complex-surface resolution.

This is a predicate on raw data; no witness satisfying it is constructed in
Sweep III. -/
def IsMinimalComplexSurfaceResolutionData
    (I : ComplexSurfaceResolutionInterface.{u})
    {Y : TopCat.{u}} (exceptionalLocus : Set Y)
    (R : ComplexSurfaceResolutionData Y) : Prop :=
  IsComplexSurfaceResolutionData I exceptionalLocus R ∧
    I.IsMinimalResolution R.map

end LeanCategories.Topology
