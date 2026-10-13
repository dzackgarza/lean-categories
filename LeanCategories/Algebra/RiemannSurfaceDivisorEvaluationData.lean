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

The source formula is a finite product of the point values of the rational
function. Sweep III records that displayed complex-valued product literally.
Under the disjoint-support hypothesis, regularity and nonvanishing upgrade
the result to an element of C^×; those are result-layer facts and are not
used here to manufacture a unit.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

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
    (f p) ^ (FreeAbelianGroup.coeff p D)

end LeanCategories.Algebra
