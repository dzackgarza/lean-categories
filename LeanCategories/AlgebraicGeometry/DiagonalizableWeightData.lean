/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableGroupData

/-!
# Weight spaces for diagonalizable-group representations

Definition-level realization of Humphreys FC16-C06-U026, following the
weight-space construction in TauCeti.

The coordinate realization of a rational representation already supplies
its coaction. For a character chi, the chi-weight space is the kernel of
the difference between this coaction and the linear map v |-> v tensor chi.
Nontrivial characters with nonzero weight space are the nonzero weights.

The direct-sum decomposition is already the defining U013 diagonalizability
predicate. Its general validity for a d-group, the finite-support theorem,
and the identification of the trivial-character space with invariants are
result content and are not reproved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- The chi-weight submodule of a coordinate rational representation. -/
noncomputable def characterWeightSpaceData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V)
    (χ : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G)) :
    Submodule K V :=
  LinearMap.ker
    (rationalRepresentationCoactionData G V D -
      (TensorProduct.mk K V
        (AffineAlgebraicGroup.coordinateHopfAlgebra G)).flip χ.val)

/-- The zero/trivial-character weight space. -/
noncomputable def characterZeroWeightSpaceData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V) :
    Submodule K V :=
  characterWeightSpaceData G V D 1

/-- Humphreys' nonzero weights: nontrivial characters whose weight space is
nonzero. The trivial character is represented multiplicatively by 1. -/
noncomputable def characterWeightsData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V) :
    Set (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G)) :=
  {χ | χ ≠ 1 ∧ characterWeightSpaceData G V D χ ≠ ⊥}

end LeanCategories.AlgebraicGeometry
