module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

structure Curve (k : Type*) [Field k] where
  scheme : Scheme
  genus : ℕ
  isSmooth : Prop
  isNodal : Prop

end LeanCategories.Schemes
