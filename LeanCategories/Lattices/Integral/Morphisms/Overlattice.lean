module

public import LeanCategories.Lattices.Integral.Objects.EvenLat
public import LeanCategories.Lattices.Integral.Objects.Dual
public import LeanCategories.Lattices.Discriminant.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- An overlattice of L is an intermediate lattice L ⊆ L' ⊆ L*. -/
structure Overlattice (L : IntegralLattice) where
  sublattice : Submodule ℤ (DualModule L)
  contains_image : LinearMap.range (adjointMap L) ≤ sublattice

/-- An isotropic subgroup H of A_L = L*/L is one on which the
    induced bilinear form vanishes. -/
structure IsotropicSubgroup (L : IntegralLattice) (hEven : IsEven L) where
  subgroup : AddSubgroup (DiscriminantGroup L)
  isotropic : ∀ x ∈ subgroup,
    LeanCategories.Lattices.Discriminant.discrQuadraticForm L hEven x = 0

@[ext]
theorem Overlattice.ext {L : IntegralLattice} {M N : Overlattice L}
    (h : M.sublattice = N.sublattice) : M = N := by
  cases M
  cases N
  cases h
  rfl

instance (L : IntegralLattice) : PartialOrder (Overlattice L) :=
  PartialOrder.lift Overlattice.sublattice fun _ _ => Overlattice.ext

@[ext]
theorem IsotropicSubgroup.ext {L : IntegralLattice} {hEven : IsEven L}
    {H K : IsotropicSubgroup L hEven} (h : H.subgroup = K.subgroup) : H = K := by
  cases H
  cases K
  cases h
  rfl

instance (L : IntegralLattice) (hEven : IsEven L) : PartialOrder (IsotropicSubgroup L hEven) :=
  PartialOrder.lift IsotropicSubgroup.subgroup fun _ _ => IsotropicSubgroup.ext

end LeanCategories.Lattices.Integral
