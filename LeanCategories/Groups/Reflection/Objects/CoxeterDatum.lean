module

public import LeanCategories.Groups.Reflection.Objects.OrientedHyperbolic

@[expose] public section

namespace LeanCategories.Groups.Reflection

/-- A chamber in the chosen positive cone. -/
structure Chamber (L : OrientedHyperbolicLattice) where
  points : Set L.carrier
  lies_in_positive_cone : points ⊆ PositiveCone L

/-- Coxeter data with a genuine group representation by form-preserving linear equivalences. -/
structure CoxeterDatum (L : OrientedHyperbolicLattice) where
  simpleRoots : List L.carrier
  coxeterExponent : Fin simpleRoots.length → Fin simpleRoots.length → ℕ
  exponent_symm : ∀ i j, coxeterExponent i j = coxeterExponent j i
  W : Type
  [groupW : Group W]
  representation : W →* (L.carrier ≃ₗ[ℤ] L.carrier)
  preserves_form : ∀ w x y, L.form (representation w x) (representation w y) = L.form x y

attribute [instance] CoxeterDatum.groupW

/-- One certified Vinberg step: a new root satisfying all previously imposed inequalities. -/
structure VinbergStep {L : OrientedHyperbolicLattice} (D : CoxeterDatum L) where
  root : L.carrier
  negative_norm : L.form root root < 0
  compatible : ∀ α ∈ D.simpleRoots, L.form root α ≤ 0

end LeanCategories.Groups.Reflection
