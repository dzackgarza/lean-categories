/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Intrinsic ambient data for the Jacobian of a Riemann surface

Peters--Sterk FC11-C16-U026 defines the Jacobian as
`H⁰(C, Ω¹_C)ᵛ / ι(H₁(C, ℤ))`.

The accepted reference is mrdouglasny/jacobian-challenge at revision
8ce1ec28aed1c78b3b39d0bae26e2858c82f5143, Apache-2.0, especially
`Jacobians/RiemannSurface/OneForm.lean` and
`Jacobians/Jacobian/Construction.lean`.

The reference's one-form owner explicitly identifies Mathlib's holomorphic
sections of the cotangent bundle as the intrinsic representation. Reuse that
owner rather than porting its chart-cocycle submodule, closure proofs, finite
basis, or universe-transfer machinery. The cotangent bundle is the native Hom
bundle from the tangent bundle to the trivial complex line.

This file records the holomorphic one-form space and its complex dual.
The integral, raw homology-period map, and quotient are at the separate
`RiemannSurfacePeriodIntegralData`, `RiemannSurfaceHomologyPeriodData`, and
`RiemannSurfaceJacobianQuotientData` owners. This ambient space alone is not
the Jacobian. No finite-dimensional, period-lattice, complex-torus, or
projectivity result is asserted here.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Holomorphic one-forms as native analytic sections of the complex
cotangent bundle, with no selected basis or chart-coefficient presentation. -/
abbrev CurveHolomorphicOneFormData :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ)

/-- The numerator `H⁰(C, Ω¹_C)ᵛ` in the source definition of the Jacobian.
The integral-period quotient, not this vector space, is the Jacobian. -/
abbrev CurveJacobianDualData := Module.Dual ℂ (CurveHolomorphicOneFormData X)

end LeanCategories.Algebra
