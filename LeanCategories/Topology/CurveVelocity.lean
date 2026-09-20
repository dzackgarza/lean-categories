/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Velocity vectors of manifold curves

Definition-level realization of Lee FC08-C03-U039. The velocity of a real
parameterized curve is the manifold derivative evaluated on the unit tangent
vector. Chain rules, derivation-model formulas, coordinate formulas, and
uniqueness statements are result content and are not included here.
-/

@[expose] public noncomputable section

open scoped Manifold

namespace LeanCategories.Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Velocity of a real-parameterized curve at `t`, differentiated within the
parameter set `s`. -/
def curveVelocityWithin (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    TangentSpace I (γ t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)

/-- Velocity of a real-parameterized curve at `t`, with unrestricted derivative. -/
def curveVelocity (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (t : ℝ) :
    TangentSpace I (γ t) :=
  curveVelocityWithin I γ Set.univ t

end LeanCategories.Topology
