/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.BorelSubgroupData
public import LeanCategories.AlgebraicGeometry.TorusCocharacterData

/-!
# Regular cocharacters

Definition-level realization of Humphreys FC16-C09-U012.

A cocharacter is already represented contravariantly by a Hopf-algebra map.
On classical points this gives a literal map from the multiplicative-group
points into the ambient algebraic-group points by precomposition.  Its point
image therefore needs no image-subgroup existence theorem.

The source calls the cocharacter regular when the family of Borel subgroups
containing this image is finite.  The topology on the classical point group
is an input to this definition-level layer; constructing the intended
Zariski topology and proving that the point image is an algebraic torus are
result/comparison obligations, not fields of the definition.

For Humphreys' cocharacter in a maximal torus T of G, apply these definitions
to the composite cocharacter G_m -> T -> G.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

open CategoryTheory
open WithConv

universe u

/-- Classical points of an affine algebraic group, in coordinate-Hopf form. -/
abbrev AlgebraicGroupClassicalPointData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) :=
  WithConv (AffineAlgebraicGroup.coordinateHopfAlgebra G →ₐ[K] K)

/-- Classical points of the multiplicative group in Laurent-coordinate form. -/
abbrev MultiplicativeGroupClassicalPointData
    (K : Type u) [Field K] :=
  WithConv (LaurentPolynomial K →ₐ[K] K)

/-- Evaluation of a cocharacter on a classical multiplicative-group point. -/
def cocharacterClassicalPointData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    (lam : AlgebraicGroupCocharacterData G)
    (t : MultiplicativeGroupClassicalPointData K) :
    AlgebraicGroupClassicalPointData G :=
  toConv (t.ofConv.comp lam.hom)

/-- The point-image of a cocharacter.  No assertion that this set is already
bundled as a closed algebraic subgroup is needed for the regularity predicate. -/
def cocharacterClassicalPointImageData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    (lam : AlgebraicGroupCocharacterData G) :
    Set (AlgebraicGroupClassicalPointData G) :=
  Set.range (cocharacterClassicalPointData G lam)

/-- The Borel subgroups of the ambient classical-point group containing the
point-image of a cocharacter. -/
def borelSubgroupsContainingCocharacterImageData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    [TopologicalSpace (AlgebraicGroupClassicalPointData G)]
    (lam : AlgebraicGroupCocharacterData G) :
    Set (Subgroup (AlgebraicGroupClassicalPointData G)) :=
  {B |
    IsBorelSubgroup B ∧
      cocharacterClassicalPointImageData G lam ⊆ (B : Set _)}

/-- A cocharacter is regular when only finitely many Borel subgroups contain
its point-image. -/
def IsRegularCocharacterData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    [TopologicalSpace (AlgebraicGroupClassicalPointData G)]
    (lam : AlgebraicGroupCocharacterData G) : Prop :=
  (borelSubgroupsContainingCocharacterImageData G lam).Finite

/-- The set of regular cocharacters. -/
def regularCocharactersData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K)
    [TopologicalSpace (AlgebraicGroupClassicalPointData G)] :
    Set (AlgebraicGroupCocharacterData G) :=
  {lam | IsRegularCocharacterData G lam}

/-- Compose a cocharacter of a subgroup/torus with a supplied inclusion into
an ambient affine algebraic group, written contravariantly on coordinates. -/
def cocharacterInAmbientGroupData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G T : AffineAlgebraicGroup K)
    (inclusionCoordinate :
      AffineAlgebraicGroup.coordinateHopfAlgebra G ⟶
        AffineAlgebraicGroup.coordinateHopfAlgebra T)
    (lam : AlgebraicGroupCocharacterData T) :
    AlgebraicGroupCocharacterData G :=
  inclusionCoordinate ≫ lam

/-- Humphreys' regularity predicate for a cocharacter of a torus inside an
ambient group: test the composite cocharacter in the ambient Borel geometry. -/
def IsRegularCocharacterInAmbientData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G T : AffineAlgebraicGroup K)
    [TopologicalSpace (AlgebraicGroupClassicalPointData G)]
    (inclusionCoordinate :
      AffineAlgebraicGroup.coordinateHopfAlgebra G ⟶
        AffineAlgebraicGroup.coordinateHopfAlgebra T)
    (lam : AlgebraicGroupCocharacterData T) : Prop :=
  IsRegularCocharacterData G
    (cocharacterInAmbientGroupData G T inclusionCoordinate lam)

/-- The source set Y(T)_reg of regular cocharacters relative to the supplied
ambient inclusion T -> G. -/
def regularCocharactersInAmbientData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G T : AffineAlgebraicGroup K)
    [TopologicalSpace (AlgebraicGroupClassicalPointData G)]
    (inclusionCoordinate :
      AffineAlgebraicGroup.coordinateHopfAlgebra G ⟶
        AffineAlgebraicGroup.coordinateHopfAlgebra T) :
    Set (AlgebraicGroupCocharacterData T) :=
  {lam | IsRegularCocharacterInAmbientData G T inclusionCoordinate lam}

end LeanCategories.AlgebraicGeometry
