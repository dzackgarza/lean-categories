/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableWeightData

/-!
# Roots for a diagonalizable subgroup

Definition-level realization of Humphreys FC16-C06-U027, following the
adjoint-weight-space construction in TauCeti.

For a diagonalizable subgroup acting through the restriction of an adjoint
representation, the root space of a character is exactly its character weight
space, and the roots are the nontrivial characters with nonzero root space.

The coordinate presentation of the restricted adjoint representation is input
data here.  Its rationality, the identification of the trivial-character space
with the fixed/centralizer Lie algebra, and the inclusion of the subgroup Lie
algebra in that fixed space are result content and are not proved in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- The root space for a character of a diagonalizable subgroup, given
coordinate data for the restricted adjoint representation. -/
noncomputable def adjointRootSpaceData
    {K : Type u} [Field K] [IsAlgClosed K]
    (D : AffineAlgebraicGroup K) (𝔤 : Type u)
    [AddCommGroup 𝔤] [Module K 𝔤]
    (Ad : RationalRepresentationCoordinateData D 𝔤)
    (χ : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra D)) :
    Submodule K 𝔤 :=
  characterWeightSpaceData D 𝔤 Ad χ

/-- The trivial-character root space of the supplied restricted adjoint
representation. -/
noncomputable def adjointZeroWeightSpaceData
    {K : Type u} [Field K] [IsAlgClosed K]
    (D : AffineAlgebraicGroup K) (𝔤 : Type u)
    [AddCommGroup 𝔤] [Module K 𝔤]
    (Ad : RationalRepresentationCoordinateData D 𝔤) :
    Submodule K 𝔤 :=
  characterZeroWeightSpaceData D 𝔤 Ad

/-- Humphreys' roots relative to a diagonalizable subgroup: the nontrivial
characters whose root spaces in the restricted adjoint representation are
nonzero. -/
noncomputable def rootsRelativeToDiagonalizableSubgroupData
    {K : Type u} [Field K] [IsAlgClosed K]
    (D : AffineAlgebraicGroup K) (𝔤 : Type u)
    [AddCommGroup 𝔤] [Module K 𝔤]
    (Ad : RationalRepresentationCoordinateData D 𝔤) :
    Set (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra D)) :=
  {χ | χ ≠ 1 ∧ adjointRootSpaceData D 𝔤 Ad χ ≠ ⊥}

end LeanCategories.AlgebraicGeometry
