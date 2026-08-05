module

public import LeanCategories.Schemes.Divisor.Objects.DivisorClass

@[expose] public section

namespace LeanCategories.Schemes.Divisor

/-- Pullback-stable positivity data selected from a divisor group. -/
structure PositivityData {X : AlgebraicGeometry.Scheme} (D : DivisorGroup X) where
  positive : Set D.group
  excludes_zero : (0 : D.group) ∉ positive

/-- The positivity construction on a divisor group. -/
def PositivityFunctor {X : AlgebraicGeometry.Scheme} (D : DivisorGroup X) :
    PositivityData D where
  positive := PositiveDivisors X D
  excludes_zero := by simp [PositiveDivisors]

end LeanCategories.Schemes.Divisor
