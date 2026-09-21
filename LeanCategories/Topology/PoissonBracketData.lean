/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Poisson bracket data

Definition-level realization of Lee FC08-C22-U035.

Lee defines the Poisson bracket by
`{f,g}(x) = ω_x(X_f(x), X_g(x))`.  The Hamiltonian-field operation is the
already-routed FC08-C22-U025 input.  This file records only that pointwise
formula.  Smoothness of the resulting scalar function and all Poisson/Lie
identities are result-layer obligations.
-/

@[expose] public noncomputable section

open scoped ContDiff Manifold

namespace LeanCategories.Topology

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Lee's Poisson bracket at the data level (FC08-C22-U035).

`omega` is the pointwise bilinear form of the already supplied symplectic
structure, and `hamiltonianField` is the FC08-C22-U025 operation
`f ↦ X_f`.  The output is deliberately the underlying scalar function:
proving it smooth is result work, not constructor data. -/
def poissonBracketData
    (omega : ∀ x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hamiltonianField :
      C^∞⟮I, M; ℝ⟯ → ∀ x : M, TangentSpace I x)
    (f g : C^∞⟮I, M; ℝ⟯) : M → ℝ :=
  fun x => omega x (hamiltonianField f x) (hamiltonianField g x)

end LeanCategories.Topology
