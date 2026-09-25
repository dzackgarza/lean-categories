/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.DiagonalizableGroupData
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Cocharacters and the character--cocharacter pairing

Definition-level realization of Humphreys FC16-C06-U021, adapted from the
geometric construction in TauCeti.

For an affine algebraic group G, a cocharacter from the multiplicative group
to G is represented contravariantly by the induced morphism of coordinate
Hopf algebras K[G] -> K[T,T^-1].

If chi is a character, its image under a cocharacter is group-like in the
Laurent-polynomial Hopf algebra. Mathlib's group-algebra classification of
group-like elements says that this image is T^n for an integer n; that
integer is the character--cocharacter pairing.

The source's assertion that this pairing is perfect for a torus is result
content and is not included in this Sweep-III file. Likewise, no finite
freeness or dual-lattice comparison theorem is imported from the reference.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.AlgebraicGeometry

universe u

/-- The coordinate Hopf algebra of the multiplicative group over K,
presented as Laurent polynomials. -/
abbrev multiplicativeGroupCoordinateHopfAlgebraData
    (K : Type u) [Field K] : CommHopfAlgCat K :=
  CommHopfAlgCat.of K (LaurentPolynomial K)

/-- The source-facing cocharacter carrier Y(G) = Hom(G_m,G), written
contravariantly on coordinate Hopf algebras. -/
abbrev AlgebraicGroupCocharacterData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) :=
  AffineAlgebraicGroup.coordinateHopfAlgebra G ⟶
    multiplicativeGroupCoordinateHopfAlgebraData K

/-- A character composed with a cocharacter is a Laurent group-like element,
so Mathlib's group-algebra classification supplies its exponent. Keeping the
equation in the value records the direct meaning of the pairing without using
the reference's later duality theorem. -/
noncomputable def characterCocharacterExponentData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    (χ : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G))
    (λ : AlgebraicGroupCocharacterData G) :
    {n : ℤ //
      AddMonoidAlgebra.single n (1 : K) = λ.hom χ.val} := by
  have hχ :
      IsGroupLikeElem K (λ.hom χ.val) :=
    χ.isGroupLikeElem_val.map λ.hom
  exact
    let h := (AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one).1 hχ
    ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Humphreys' integer character--cocharacter pairing: its value is the
exponent of the power map obtained by composing a character and cocharacter. -/
noncomputable def characterCocharacterPairingData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    (χ : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G))
    (λ : AlgebraicGroupCocharacterData G) : ℤ :=
  characterCocharacterExponentData G χ λ

end LeanCategories.AlgebraicGeometry
