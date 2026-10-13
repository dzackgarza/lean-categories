/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.ComplexSurfaceResolutionData
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Point-blowup data for complex surfaces

Definition-level realization of Peters--Sterk FC11-B-U035.

The local blowup chart is the standard incidence subset of affine space times
projective space, following the checked Atlas `Lec8Blowup` reference.  Only
the defining subset and projection are recorded here.  Exceptional-fiber and
away-from-center equivalences are theorem content.

The `(-1)`-curve definition reuses the existing complex-surface resolution
interface: a projective-line curve is the source's smooth rational curve
carrier, and its self-intersection is required to be `-1`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Topology

universe u

/-- A `(-1)`-curve: a smooth rational/projective-line curve of
self-intersection `-1`. -/
def ComplexSurfaceResolutionInterface.IsMinusOneCurveData
    (I : ComplexSurfaceResolutionInterface.{u})
    {X : TopCat.{u}} (E : Set X) : Prop :=
  I.IsProjectiveLineCurve E ∧ I.HasSelfIntersection E (-1)

namespace PointBlowupData

variable (k : Type*) [Field k] (n : ℕ)

/-- The blowup of affine `n`-space at the origin, as the incidence locus
`{(x,ℓ) | x ∈ ℓ} ⊂ 𝔸ⁿ × ℙⁿ⁻¹`. -/
def affineOrigin :
    Set ((Fin n → k) × ℙ k (Fin n → k)) :=
  {p | (p.1 : Fin n → k) ∈ p.2.submodule}

/-- Projection from the incidence-model blowup to affine space. -/
def projection (p : affineOrigin k n) : Fin n → k :=
  p.1.1

/-- The two-dimensional local chart used for the blowup of a smooth surface
at a point after choosing local coordinates centered at that point. -/
abbrev surfaceChart :=
  affineOrigin k 2

end PointBlowupData

end LeanCategories.Topology
