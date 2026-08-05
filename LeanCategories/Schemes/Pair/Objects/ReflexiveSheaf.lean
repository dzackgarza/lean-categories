module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes.Pair

open AlgebraicGeometry

/-- Relative dualizing sheaf omega_{X/S}[m]. -/
structure ReflexiveSheaf (X : Scheme) where
  sheaf : Type _
  reflexive : Prop
  power : ℕ

/-- Q-Gorenstein data: a positive reflexive power of the dualizing sheaf is invertible. -/
structure QGorenstein (X : Scheme) where
  index : ℕ
  positive_index : 0 < index
  dualizingPower : ReflexiveSheaf X
  correct_power : dualizingPower.power = index
  invertible : Prop

end LeanCategories.Schemes.Pair
