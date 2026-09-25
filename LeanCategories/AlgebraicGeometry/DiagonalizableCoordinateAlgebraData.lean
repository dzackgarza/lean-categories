/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableGroupData
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Character-group coordinate algebra data

Definition/construction-level realization of Humphreys FC16-C06-U022,
adapted from the diagonalizable-group construction used in TauCeti.

For an affine algebraic group G, its characters are the group-like elements
of K[G]. The group algebra K[X(G)] therefore has the native commutative Hopf
structure, and evaluation of its basis characters gives a canonical
bialgebra map

K[X(G)] -> K[G].

For a diagonalizable group the source identifies this map as an isomorphism
and derives the contravariant classification by finitely generated abelian
groups. Those are result-layer statements and are not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- Humphreys' group-algebra coordinate model K[X(G)] built from the
character group of an affine algebraic group. -/
abbrev characterGroupCoordinateHopfAlgebraData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) : CommHopfAlgCat K :=
  CommHopfAlgCat.of K
    (MonoidAlgebra K
      (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G)))

/-- Evaluation of formal character basis elements gives the canonical
bialgebra map K[X(G)] -> K[G]. For diagonalizable G, invertibility of this
map is theorem/result content. -/
noncomputable def characterGroupCoordinateEvaluationData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) :
    MonoidAlgebra K
        (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G)) →ₐc[K]
      AffineAlgebraicGroup.coordinateHopfAlgebra G :=
  MonoidAlgebra.liftGroupLikeBialgHom

end LeanCategories.AlgebraicGeometry
