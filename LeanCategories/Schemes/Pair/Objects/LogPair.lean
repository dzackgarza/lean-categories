module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes.Pair

open AlgebraicGeometry

/-- Standard singularity classes for log pairs. -/
inductive SingularityClass where
  | klt | plt | lc | dlt | slc

/-- A log pair consists of a scheme and a rational boundary divisor. -/
structure LogPair where
  X : Scheme
  boundaryComponents : Type
  coefficient : boundaryComponents → ℚ
  coefficient_bounds : ∀ D, 0 ≤ coefficient D ∧ coefficient D ≤ 1
  valuation : Type
  discrepancy : valuation → ℚ

/-- A pair has a singularity class when its discrepancies satisfy the corresponding threshold. -/
def HasSingularity (P : LogPair) : SingularityClass → Prop
  | .klt => ∀ E, -1 < P.discrepancy E
  | .plt => ∀ E, -1 < P.discrepancy E
  | .lc => ∀ E, -1 ≤ P.discrepancy E
  | .dlt => (∀ E, -1 ≤ P.discrepancy E) ∧
      (P.boundaryComponents → Nonempty P.valuation)
  | .slc => ∀ E, -1 ≤ P.discrepancy E

end LeanCategories.Schemes.Pair
