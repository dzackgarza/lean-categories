/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SingularCupProduct

/-!
# Raw integral intersection-form data

Definition-level realization of the cup-evaluation formula underlying
Peters--Steenbrink FC11-C02-U018.

For an oriented compact four-manifold, the integral intersection pairing is
obtained by cupping two degree-two cohomology classes and evaluating the
degree-four class on the fundamental class.  The target pin currently owns the
raw singular-cochain cup formula but not the quotient-level integral singular
cohomology product.  Sweep III therefore records exactly the representative
formula and a fundamental-evaluation datum.

The assertions that a fundamental cycle exists, that evaluation kills
boundaries, that the formula descends to `H²`, kills torsion, induces a
symmetric form on `H²/tors`, and is unimodular by Poincare duality are
result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

variable (X : Type u) [TopologicalSpace X]

/-- Raw evaluation on degree-four singular cochains, standing for evaluation
against a chosen integral fundamental representative.

For an actual oriented compact four-manifold the source supplies this from its
fundamental class.  Cycle/descent properties are not constructor fields. -/
structure FourManifoldFundamentalEvaluationData where
  eval : RawSingularCochain X ℤ 4 →+ ℤ

/-- The representative-level integral intersection pairing
`(φ, ψ) ↦ ⟨φ ∪ ψ, [X]⟩` (FC11-C02-U018). -/
def rawFourManifoldIntersectionPairing
    (ω : FourManifoldFundamentalEvaluationData X)
    (φ ψ : RawSingularCochain X ℤ 2) : ℤ :=
  ω.eval (singularCupCochain 2 2 φ ψ)

/-- Raw predicate saying that an integer-valued pairing on degree-two singular
cochains is the cup-evaluation pairing determined by `ω`.

This exposes the source formula without claiming quotient-level
well-definedness. -/
def IsRawFourManifoldIntersectionPairing
    (ω : FourManifoldFundamentalEvaluationData X)
    (b : RawSingularCochain X ℤ 2 → RawSingularCochain X ℤ 2 → ℤ) : Prop :=
  ∀ φ ψ, b φ ψ = rawFourManifoldIntersectionPairing X ω φ ψ

end LeanCategories.Topology
