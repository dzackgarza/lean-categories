module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Full subcategory Surface_k ⊂ Scheme_k of 2D integral schemes over k. -/
structure Surface (k : Type*) [Field k] where
  scheme : Scheme
  divisorClass : Type
  canonicalClass : divisorClass
  intersection : divisorClass → divisorClass → ℤ
  intersection_symm : ∀ D E, intersection D E = intersection E D

end LeanCategories.Schemes
