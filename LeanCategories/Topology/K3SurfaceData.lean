/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.ComplexSurfaceResolutionData
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Complex K3-surface definition data

Definition-level realization of the defining clause in Peters--Sterk
FC11-B-U027.

The source defines a complex K3 surface to be a simply connected complex
surface with trivial canonical bundle.  The project already has a shared
predicate interface for smooth complex surfaces, but the checked ecosystem has
no holomorphic canonical-line-bundle owner on that carrier.  The interface
below adds exactly that missing analytic predicate.

HasTrivialCanonicalBundle is deliberately primitive here.  In particular,
this file does not replace holomorphic triviality by the existence of a
nowhere-vanishing holomorphic two-form: the comparison between those
descriptions is result content.  Likewise, the assertions that Kummer surfaces,
smooth quartics, and smooth intersections of three quadrics are K3 surfaces are
examples/results and are not encoded in this Sweep-III owner.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

/-- Shared complex-surface interface augmented by the source notion that the
holomorphic canonical bundle is trivial. -/
structure K3SurfaceInterface extends ComplexSurfaceResolutionInterface.{u} where
  HasTrivialCanonicalBundle : TopCat.{u} → Prop

/-- Peters--Sterk's complex K3-surface predicate: a smooth complex surface that
is simply connected and has trivial canonical bundle. -/
def IsK3SurfaceData
    (I : K3SurfaceInterface.{u}) (X : TopCat.{u}) : Prop :=
  I.IsSmoothComplexSurface X ∧
    SimplyConnectedSpace X ∧
      I.HasTrivialCanonicalBundle X

end LeanCategories.Topology
