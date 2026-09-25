/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.DerivationBundle
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Pointwise dual frames and coframes

Definition-level realization of Lee FC08-C11-U021 in Lee's point-derivation
tangent model.  A rough local frame/coframe is represented by its pointwise
basis data.  The source's equation `εⁱ(Eⱼ) = δⁱⱼ` is recorded as the duality
relation, and a frame has its canonical pointwise dual coframe by native linear
algebra.  Converse existence/uniqueness and smoothness are result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- A rough local frame over `U`, in Lee's point-derivation tangent model:
at every point of `U` it is an ordered basis of the tangent space. -/
abbrev RoughLocalFrame (I : ModelWithCorners ℝ E H) (U : Set M) (n : ℕ) :=
  (p : U) → Module.Basis (Fin n) ℝ (PointDerivation I p.1)

/-- A rough local coframe over `U`: at every point it is an ordered basis of
the dual of Lee's point-derivation tangent space. -/
abbrev RoughLocalCoframe (I : ModelWithCorners ℝ E H) (U : Set M) (n : ℕ) :=
  (p : U) → Module.Basis (Fin n) ℝ (Module.Dual ℝ (PointDerivation I p.1))

/-- The coframe dual to a rough local frame, obtained pointwise by taking the
linear dual basis.  Source: Lee, Chapter 11 (FC08-C11-U021). -/
def dualCoframe {I : ModelWithCorners ℝ E H} {U : Set M} {n : ℕ}
    (e : RoughLocalFrame I U n) : RoughLocalCoframe I U n :=
  fun p ↦ (e p).dualBasis

/-- A frame and coframe are dual when their pointwise bases are dual.  This is
Lee's defining equation `εⁱ(Eⱼ) = δⁱⱼ` without adjoining the separate theorem
that every coframe has a unique dual frame. -/
def AreDualFrameCoframe {I : ModelWithCorners ℝ E H} {U : Set M} {n : ℕ}
    (e : RoughLocalFrame I U n) (ε : RoughLocalCoframe I U n) : Prop :=
  ∀ p, ε p = (e p).dualBasis

end LeanCategories.Topology
