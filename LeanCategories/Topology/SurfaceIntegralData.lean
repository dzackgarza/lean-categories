/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Surface-integral formula

Definition-level realization of Lee FC08-C16-U045.

For a compact oriented hypersurface with chosen unit normal `N`, Lee defines the
surface integral of a vector field `X` by integrating its normal component
`⟨X,N⟩` against the induced Riemannian area form.

The metric pairing, restriction to the hypersurface, induced area-form
integration, and normal-field geometry are supplied by their existing owners.
Sweep III records only the scalar integral formula below.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- Lee's surface integral of a vector field with respect to a chosen unit
normal: integrate the scalar normal component over the surface. -/
def surfaceIntegral
    {VectorField NormalField SurfaceScalarFunction : Type*}
    (normalComponent : VectorField → NormalField → SurfaceScalarFunction)
    (integralSurfaceScalar : SurfaceScalarFunction → ℝ)
    (X : VectorField)
    (N : NormalField) : ℝ :=
  integralSurfaceScalar (normalComponent X N)

end LeanCategories.Topology
