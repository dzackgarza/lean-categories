/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.CohomologyRingData
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

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

The quotient-level carrier used by Peters--Sterk FC11-B-U005 is also recorded
here. The already-realized singular-cohomology cup product supplies the
degree-two-by-degree-two to degree-four product; a candidate evaluation on
degree-four cohomology is selected by its exact representative graph against
the raw fundamental evaluation, and a candidate bilinear form on degree-two
cohomology modulo torsion is selected by its exact quotient-representative
graph.

Existence/independence of these descents, the fact that torsion is killed,
symmetry and unimodularity remain result-layer statements. No such theorem is
proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

open AlgebraicTopology CategoryTheory
open scoped TensorProduct

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

section QuotientLevel

variable (Y : Type) [TopologicalSpace Y]

/-- Integral singular cohomology in degree two. -/
abbrev FourManifoldSecondCohomologyData :=
  singularCohomologyModuleData ℤ (TopCat.of Y) (ModuleCat.of ℤ ℤ) 2

/-- Integral singular cohomology in degree four. -/
abbrev FourManifoldFourthCohomologyData :=
  singularCohomologyModuleData ℤ (TopCat.of Y) (ModuleCat.of ℤ ℤ) 4

/-- The source carrier H²(X,Z) modulo torsion. -/
abbrev FourManifoldTorsionFreeSecondCohomologyData :=
  (FourManifoldSecondCohomologyData Y : Type) ⧸
    Submodule.torsion ℤ (FourManifoldSecondCohomologyData Y : Type)

/-- Candidate evaluation of degree-four cohomology on the fundamental class. -/
abbrev FourManifoldCohomologyEvaluationCandidateData :=
  (FourManifoldFourthCohomologyData Y : Type) →ₗ[ℤ] ℤ

/-- Exact representative graph saying that a degree-four cohomology
evaluation descends the supplied raw fundamental evaluation. -/
def IsFourManifoldCohomologyEvaluationData
    (ω : FourManifoldFundamentalEvaluationData Y)
    (ev : FourManifoldCohomologyEvaluationCandidateData Y) : Prop :=
  let K := singularCochainComplexData ℤ (TopCat.of Y) (ModuleCat.of ℤ ℤ)
  ∀ z : K.cycles 4,
    ev ((K.homologyπ 4).hom z) =
      ω.eval (fun σ =>
        singularCochainEvalData ℤ (TopCat.of Y)
          ((TopCat.toSSetObjEquiv (TopCat.of Y)
            (Opposite.op (SimplexCategory.mk 4))).symm σ)
          ((K.iCycles 4).hom z))

/-- Degree-four cohomology evaluation selected from the exact fundamental
representative graph. Its existence and independence of cocycle
representatives remain result content. -/
noncomputable def fourManifoldCohomologyEvaluationData
    (ω : FourManifoldFundamentalEvaluationData Y) :
    FourManifoldCohomologyEvaluationCandidateData Y :=
  Classical.epsilon (IsFourManifoldCohomologyEvaluationData Y ω)

/-- Candidate integral bilinear form on H²(X,Z) modulo torsion. -/
abbrev FourManifoldIntersectionFormCandidateData :=
  LinearMap.BilinForm ℤ (FourManifoldTorsionFreeSecondCohomologyData Y)

/-- The source cup/evaluation value on a pair of integral degree-two
cohomology representatives. -/
noncomputable def fourManifoldIntersectionRepresentativeValueData
    (ω : FourManifoldFundamentalEvaluationData Y)
    (x y : FourManifoldSecondCohomologyData Y) : ℤ :=
  let ev : FourManifoldCohomologyEvaluationCandidateData Y :=
    fourManifoldCohomologyEvaluationData Y ω
  let cup : FourManifoldFourthCohomologyData Y :=
    singularCohomologyCupMulData ℤ (TopCat.of Y) (p := 2) (q := 2) x y
  ev cup

/-- Exact quotient-representative graph for the compact-surface intersection
form: it is cup product in degree two followed by fundamental-class
evaluation. -/
def IsFourManifoldIntersectionFormData
    (ω : FourManifoldFundamentalEvaluationData Y)
    (Q : FourManifoldIntersectionFormCandidateData Y) : Prop :=
  ∀ x y : FourManifoldSecondCohomologyData Y,
    Q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      fourManifoldIntersectionRepresentativeValueData Y ω x y

/-- Peters--Sterk's integral intersection form on H²(X,Z) modulo torsion,
selected from the exact cup/evaluation quotient graph. -/
noncomputable def fourManifoldIntersectionFormData
    (ω : FourManifoldFundamentalEvaluationData Y) :
    FourManifoldIntersectionFormCandidateData Y :=
  Classical.epsilon (IsFourManifoldIntersectionFormData Y ω)

/-- The source signature (b+,b-) of the real scalar extension of the
intersection form. -/
noncomputable def fourManifoldIntersectionSignatureData
    (ω : FourManifoldFundamentalEvaluationData Y) : ℕ × ℕ :=
  let Q := fourManifoldIntersectionFormData Y ω
  let QReal : LinearMap.BilinForm ℝ
      (ℝ ⊗[ℤ] (FourManifoldTorsionFreeSecondCohomologyData Y)) :=
    LinearMap.BilinForm.baseChange ℝ Q
  (sigPos (LinearMap.BilinMap.toQuadraticMap QReal),
    sigNeg (LinearMap.BilinMap.toQuadraticMap QReal))

/-- The source index b+ - b-. -/
noncomputable def fourManifoldIntersectionIndexData
    (ω : FourManifoldFundamentalEvaluationData Y) : ℤ :=
  let sig := fourManifoldIntersectionSignatureData Y ω
  (sig.1 : ℤ) - (sig.2 : ℤ)

end QuotientLevel

end LeanCategories.Topology
