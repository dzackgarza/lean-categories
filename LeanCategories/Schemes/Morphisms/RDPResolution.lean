module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- ADE type of a rational double point. -/
inductive ADEType where
  | A (n : ℕ)
  | D (n : ℕ)
  | E6 | E7 | E8

/-- Minimal resolution of a surface with rational double points. -/
structure RDPResolution (X : Scheme) where
  X_tilde : Scheme
  π : X_tilde ⟶ X
  exceptionalCurves : List (Set X_tilde)
  singularityTypes : List ADEType
  minimal : Prop
  resolves : Prop

end LeanCategories.Schemes
