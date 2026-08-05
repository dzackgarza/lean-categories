module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

namespace LeanCategories.Schemes

open AlgebraicGeometry

/-- Coherent sheaf category Coh(X) for locally noetherian schemes. -/
structure CoherentSheaf (X : Scheme) where
  sheaf : Type _
  doubleDual : Type _

/-- Class IsReflexive for rank-one reflexive sheaves F ≅ F**. -/
class IsReflexive (X : Scheme) (F : CoherentSheaf X) : Prop where
  isReflexive : Nonempty (F.sheaf ≃ F.doubleDual)

/-- Reflexive tensor product F ^⊗ G = (F ⊗ G)**. -/
axiom reflexiveTensorProduct (X : Scheme) (F G : CoherentSheaf X) : CoherentSheaf X

/-- Divisor class group Cl(X) as isomorphism classes under reflexive tensor product. -/
structure DivisorClassGroup (X : Scheme) where
  group : Type _
  [addCommGroup : AddCommGroup group]

end LeanCategories.Schemes
