/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic

/-!
# Milnor-tube and fibre carriers

Supporting definitions for Peters--Sterk FC11-C18-U025, Version JUNE 2024,
printed pp. 332--333 (PDF pages 339--340), Section 18.2.A.

The source restricts a holomorphic representative `f : ℂ^(n+1) → ℂ` to
`{z | ‖z‖² < η} ∩ f⁻¹(Δ*(r))`. The displayed inequality is strict, and
`η` bounds the squared Euclidean norm, not the norm itself. The use of
`EuclideanSpace` retains that norm rather than the finite-product sup norm.

The carriers and restriction map below are defined for any function and
radii. In the source specialization, `f(0)=0`, the origin is its only
critical point on the chosen neighbourhood, and the positive parameters
are chosen sufficiently small. Local triviality, independence of those
choices, smoothness and the sphere-bouquet comparison are not asserted.
The section assumes even complex dimension for its symmetric intersection
lattice; the raw fibre carrier makes sense in every dimension.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- The source ambient complex coordinates with their Euclidean norm. -/
abbrev MilnorCoordinateSpaceData (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

/-- The punctured open parameter disk `Δ*(r)`. -/
def milnorPuncturedDiskData (r : ℝ) : Set ℂ :=
  Metric.ball 0 r \ {0}

/-- The source's small tube over the punctured parameter disk. -/
def milnorTubeSetData {n : ℕ} (f : MilnorCoordinateSpaceData n → ℂ)
    (η r : ℝ) : Set (MilnorCoordinateSpaceData n) :=
  {z | ‖z‖ ^ 2 < η} ∩ f ⁻¹' milnorPuncturedDiskData r

/-- The Milnor-tube carrier with its native subspace topology. -/
abbrev MilnorTubeData {n : ℕ} (f : MilnorCoordinateSpaceData n → ℂ)
    (η r : ℝ) : Type := milnorTubeSetData f η r

/-- Restriction of `f` to the actual tube and punctured-disk carriers.
Its codomain membership is already part of each tube point. -/
def milnorTubeProjectionData {n : ℕ} (f : MilnorCoordinateSpaceData n → ℂ)
    (η r : ℝ) : MilnorTubeData f η r → milnorPuncturedDiskData r :=
  fun z ↦ ⟨f z.1, z.2.2⟩

/-- The fibre over the chosen nonzero parameter, inside the source's
Euclidean neighbourhood. -/
def milnorFiberSetData {n : ℕ} (f : MilnorCoordinateSpaceData n → ℂ)
    (η : ℝ) {r : ℝ} (t : milnorPuncturedDiskData r) :
    Set (MilnorCoordinateSpaceData n) :=
  {z | ‖z‖ ^ 2 < η ∧ f z = t.1}

/-- The actual level-set fibre, carrying the native subspace topology.
It is not a supplied abstract space or a sphere-bouquet replacement. -/
abbrev MilnorFiberData {n : ℕ} (f : MilnorCoordinateSpaceData n → ℂ)
    (η : ℝ) {r : ℝ} (t : milnorPuncturedDiskData r) : Type :=
  milnorFiberSetData f η t

end LeanCategories.Topology
