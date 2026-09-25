/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableWeightData
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Weights and multiplicities of rational representations

Definition-level realization of Humphreys FC16-C11-U001.

After restricting a rational representation to a maximal torus, its weight
space for a character is exactly the diagonalizable-group weight space from
FC16-C06-U026.  A representation weight is any character with nonzero weight
space, including the trivial character when its weight space is nonzero.
Its multiplicity is the dimension of that weight space.

That the Weyl group permutes the weights and preserves their multiplicities
is result content and is not proved in Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- The weight space of a rational representation restricted to a supplied
maximal torus. -/
noncomputable def rationalRepresentationWeightSpaceData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData T V)
    (chi : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T)) :
    Submodule K V :=
  characterWeightSpaceData T V D chi

/-- The support of the torus weight decomposition of the supplied rational
representation.  Unlike the root support, the trivial character is allowed. -/
noncomputable def rationalRepresentationWeightsData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData T V) :
    Set (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T)) :=
  {chi | rationalRepresentationWeightSpaceData T V D chi ≠ ⊥}

/-- The multiplicity of a character is the dimension of its weight space. -/
noncomputable def rationalRepresentationWeightMultiplicityData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData T V)
    (chi : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T)) : ℕ :=
  Module.finrank K (rationalRepresentationWeightSpaceData T V D chi)

end LeanCategories.AlgebraicGeometry
