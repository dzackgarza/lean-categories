/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of Rado Kirov's canonical-form definitions in
Vilin97/lean-pool, Apache-2.0, revision
3fc79f0a795f19fffcc59eee3efaf5faa52de3c3.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceDivisorData
public import LeanCategories.Algebra.RiemannSurfacePeriodIntegralData

/-!
# Canonical-divisor data of a holomorphic one-form

Peters--Sterk FC11-C16-U030 defines a canonical divisor as the divisor of
a nonzero holomorphic one-form. The reference's
`CanonicalForms/OneDimensional.lean::RS.canonicalDivisorOf` is the divisor
of its explicit reference form; `CanonicalForms/Quotient.lean::MForm.ord`
uses the meromorphic order of the local coefficient.

For the source's holomorphic specialization, the intrinsic cotangent
section and its chart coefficient already have project owners. Reuse them
and the native meromorphic order rather than porting a second meromorphic
form carrier, its quotient, or its module laws. The finite divisor is
specified by its coefficient formula, as at the existing principal-divisor
owner. Its finite support, selection specification, chart independence,
degree, and independence up to linear equivalence are separate results.

The compact connected curve and the chosen nonzero form are explicit.
No existence of such a form is asserted; in particular this construction
does not assert that a genus-zero curve has one. Complete original-prose
acceptance and target-pin validation remain open.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Order of a holomorphic one-form, computed from its existing
inverse-chart pullback coefficient at the chart center. -/
def curveHolomorphicOneFormOrderData
    (form : CurveHolomorphicOneFormData X) (p : X) : WithTop ℤ :=
  meromorphicOrderAt (curveOneFormChartCoefficientData form p)
    ((extChartAt 𝓘(ℂ) p) p)

/-- The source coefficient formula for the divisor of a one-form.
This predicate does not replace the one-form by a supplied divisor. -/
def IsCurveCanonicalDivisorData (form : CurveHolomorphicOneFormData X)
    (D : CurveDivisorData X) : Prop :=
  ∀ p : X, FreeAbelianGroup.coeff p D =
    (curveHolomorphicOneFormOrderData form p).untop₀

/-- Canonical divisor seeded by a specified nonzero holomorphic form.
Selection is by the local order formula; the assertion that it satisfies
that formula is not proved in the definitions sweep. -/
def curveCanonicalDivisorData [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (form : CurveHolomorphicOneFormData X) (_hform : form ≠ 0) :
    CurveDivisorData X :=
  Classical.epsilon (IsCurveCanonicalDivisorData form)

/-- Class of the specified canonical divisor in the existing curve
Picard-group carrier. Independence of the chosen form remains a result. -/
def curveCanonicalDivisorClassData [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (form : CurveHolomorphicOneFormData X) (hform : form ≠ 0) :
    CurvePicardGroupData X :=
  QuotientAddGroup.mk (curveCanonicalDivisorData form hform)

end LeanCategories.Algebra
