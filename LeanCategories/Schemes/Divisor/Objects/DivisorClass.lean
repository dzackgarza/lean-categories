module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes.Divisor

open AlgebraicGeometry

/-- Cartier/Weil divisor groups Div(X) and Cl(X) as AddCommGroup objects. -/
structure DivisorGroup (X : Scheme) where
  group : Type _
  [addCommGroup : AddCommGroup group]

attribute [instance] DivisorGroup.addCommGroup

structure DivisorHom (X : Scheme) (D1 D2 : DivisorGroup X) where
  hom : D1.group →+ D2.group

/-- Positivity functor DivisorGroup -> Pic(X). -/
def PositiveDivisors (X : Scheme) (D : DivisorGroup X) : Set D.group :=
  {d | d ≠ 0}

end LeanCategories.Schemes.Divisor
