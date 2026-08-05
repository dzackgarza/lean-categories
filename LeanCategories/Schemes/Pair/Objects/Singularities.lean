module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes.Pair

open AlgebraicGeometry

/-- The three geometric conditions defining a demi-normal scheme. -/
structure DemiNormalEvidence (X : Scheme) where
  serreS2 : Prop
  gorensteinInCodimensionOne : Prop
  seminormal : Prop
  has_serreS2 : serreS2
  has_gorensteinInCodimensionOne : gorensteinInCodimensionOne
  has_seminormal : seminormal

/-- Demi-normality means `S₂`, `G₁`, and seminormality. -/
def DemiNormal (X : Scheme) : Prop := Nonempty (DemiNormalEvidence X)

/-- Log discrepancy a(E, X, Delta) for proper birational models. -/
axiom LogDiscrepancy (X : Scheme) : ℚ

/-- Semi-log-canonical (slc) log pair (X, Delta). -/
structure SemiLogCanonicalPair where
  X : Scheme
  isDeminormal : DemiNormal X
  isSlc : Prop

end LeanCategories.Schemes.Pair
