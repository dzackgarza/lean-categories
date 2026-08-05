module

public import LeanCategories.Schemes.Morphisms.RDPResolution

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- The ABCDE label of an anticanonical quotient surface. -/
inductive ABCDEType where
  | A | B | C | D | E

/-- Anticanonical quotient surface map with its folded singularity type. -/
structure AnticanonicalQuotient (X : Scheme) where
  quotient : Scheme
  π : X ⟶ quotient
  quotientType : ABCDEType
  finite : Prop
  anticanonical : Prop

end LeanCategories.Schemes
