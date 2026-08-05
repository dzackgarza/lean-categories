module

public import LeanCategories.ComplexManifolds.Objects.Domain

@[expose] public section

namespace LeanCategories.ComplexManifolds

/-- An arithmetic orbifold quotient Γ\D with Baily-Borel compactification data. -/
structure ArithmeticQuotient (D : Domain) where
  Γ : Type
  [groupGamma : Group Γ]
  action : Γ → D.periodVector → D.periodVector
  preserves_domain : ∀ g, Set.MapsTo (action g) D.points D.points
  quotient : Type
  orbitMap : D.periodVector → quotient
  bailyBorel : Type
  openEmbedding : quotient → bailyBorel

attribute [instance] ArithmeticQuotient.groupGamma

end LeanCategories.ComplexManifolds
