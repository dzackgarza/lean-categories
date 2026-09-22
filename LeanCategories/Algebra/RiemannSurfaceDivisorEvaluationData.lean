/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceDivisorData

/-!
# Rational-function evaluation on curve divisors

Definition-level realization of Peters--Sterk FC11-C16-U025.

The source defines

  f(D) = product over x in supp(D) of f(x)^(n_x)

when the support of the rational function is disjoint from the support of
the divisor. The pinned Jacobian reference supplies the divisor and
meromorphic-germ infrastructure but does not itself package this evaluation.

Its meromorphic representatives intentionally ignore the literal value
stored at a zero or pole. We therefore do not use the raw point value as a
surrogate for rational-function evaluation. Instead, the regular value at a
point is selected from the punctured-neighborhood limit of the germ. Under
the source disjoint-support hypothesis, the result layer proves these limits
exist and are nonzero. Sweep III records the exact finite product and the
corresponding unit-valued selection only; existence, nonvanishing, functorial
behavior, and Weil reciprocity are not proved here.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Predicate characterizing the finite complex value of a rational-function
germ at a regular point. Punctured neighborhoods make this independent of
the arbitrary representative value stored at the point itself. -/
def IsCurveRegularValueData
    (f : NonzeroCurveRationalFunctionData X) (p : X) (z : ℂ) : Prop :=
  Tendsto f.toFun (𝓝[≠] p) (𝓝 z)

/-- Selected regular value of a rational-function germ at a point.

When the order at the point is zero, meromorphy supplies existence and
uniqueness; those facts are result-layer statements. -/
def curveRegularValueData
    (f : NonzeroCurveRationalFunctionData X) (p : X) : ℂ :=
  Classical.epsilon (IsCurveRegularValueData f p)

/-- Support of a rational function: its zero/pole locus, expressed directly
by nonzero vanishing order. -/
def curveRationalFunctionSupportData
    (f : NonzeroCurveRationalFunctionData X) : Set X :=
  {p : X | curveOrderAtData p f.toFun ≠ 0}

/-- The source hypothesis that the support of f is disjoint from the support
of D. -/
def CurveDivisorEvaluationAdmissibleData
    (f : NonzeroCurveRationalFunctionData X)
    (D : CurveDivisorData X) : Prop :=
  Disjoint
    (curveRationalFunctionSupportData f)
    (↑(curveDivisorSupportData D) : Set X)

/-- The displayed complex product underlying Peters--Sterk's f(D). -/
def curveDivisorEvaluationComplexData
    (f : NonzeroCurveRationalFunctionData X)
    (D : CurveDivisorData X) : ℂ :=
  ∏ p ∈ curveDivisorSupportData D,
    (curveRegularValueData f p) ^ (FreeAbelianGroup.coeff p D)

/-- Predicate saying that a complex unit represents the displayed divisor
evaluation product. -/
def IsCurveDivisorEvaluationUnitData
    (f : NonzeroCurveRationalFunctionData X)
    (D : CurveDivisorData X) (u : ℂˣ) : Prop :=
  (u : ℂ) = curveDivisorEvaluationComplexData f D

/-- Peters--Sterk's unit-valued divisor evaluation f(D), under the defining
disjoint-support hypothesis.

The proof that the displayed product is nonzero under this hypothesis is
result content, so Sweep III selects the unit by its coercion formula rather
than proving nonvanishing merely to construct it. -/
def curveDivisorEvaluationData
    (f : NonzeroCurveRationalFunctionData X)
    (D : CurveDivisorData X)
    (_h : CurveDivisorEvaluationAdmissibleData f D) : ℂˣ :=
  Classical.epsilon (IsCurveDivisorEvaluationUnitData f D)

end LeanCategories.Algebra
