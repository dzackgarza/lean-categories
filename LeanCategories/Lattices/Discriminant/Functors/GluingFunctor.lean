module

public import LeanCategories.Lattices.Discriminant.Objects.Basic
public import LeanCategories.Lattices.Integral.Morphisms.Overlattice

@[expose] public section

namespace LeanCategories.Lattices.Discriminant

open LeanCategories.Lattices.Integral

/-- The gluing construction: given an isotropic subgroup H ≤ A_L,
    produce the overlattice L_H with A_{L_H} = H⊥/H.
    This is the inverse direction of Nikulin's overlattice equivalence.
    See Nikulin, Theorem 1.4.1. -/
axiom gluingConstruction (L : IntegralLattice) (hEven : IsEven L)
    (H : IsotropicSubgroup L hEven) : IntegralLattice

/-- The discriminant group of the glued lattice is H⊥/H. -/
axiom gluing_discriminant (L : IntegralLattice) (hEven : IsEven L)
    (H : IsotropicSubgroup L hEven) :
    Nonempty (discrGroup (gluingConstruction L hEven H) ≃+
              (DiscriminantGroup L ⧸ H.subgroup))

/-- The gluing construction preserves evenness. -/
axiom gluing_preserves_even (L : IntegralLattice) (hEven : IsEven L)
    (H : IsotropicSubgroup L hEven) :
    IsEven (gluingConstruction L hEven H)

/-- The gluing construction is functorial on isotropic subgroups:
    H₁ ≤ H₂ implies L_{H₂} is an overlattice of L_{H₁}. -/
axiom gluing_monotone (L : IntegralLattice) (hEven : IsEven L)
    (H₁ H₂ : IsotropicSubgroup L hEven) (h : H₁.subgroup ≤ H₂.subgroup) :
    Nonempty ((gluingConstruction L hEven H₁).carrier →ₗ[ℤ]
              (gluingConstruction L hEven H₂).carrier)

end LeanCategories.Lattices.Discriminant
