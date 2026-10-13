/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.RationalRepresentationData
public import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Diagonalizable algebraic groups

Definition-level realization of Humphreys FC16-C06-U013.

A diagonalizable group (`d`-group) is defined by the condition that every
rational representation decomposes into character weight spaces.  Using the
coordinate presentation of FC16-C02-U013, the representation map determines
the raw coaction in a chosen basis by its matrix coefficients.  A character
is already a group-like element of `K[G]`, and a vector has weight `χ` exactly
when its coaction is `v ⊗ χ`.

The finite-sum existence and uniqueness predicate below is the internal direct
sum condition without requiring a separately bundled comodule instance.  The
equivalent characterization by closed subgroups of diagonal matrix groups is
the following result layer and is not part of the definition.
-/

@[expose] public noncomputable section

open scoped TensorProduct BigOperators

namespace LeanCategories.AlgebraicGeometry

open Algebra.TensorProduct

universe u

/-- The raw coaction associated to a coordinate presentation of a rational
representation.  On a basis vector `v_j` it is
`Σ_i v_i ⊗ ρ*(X_ij)`. -/
def rationalRepresentationCoactionData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V) :
    V →ₗ[K] V ⊗[K] AffineAlgebraicGroup.coordinateHopfAlgebra G :=
  D.basis.constr K fun j =>
    ∑ i : Fin D.n,
      D.basis i ⊗ₜ[K]
        D.coordinate (generalLinearGenericMatrixData K D.n i j)

/-- A vector has character weight `χ` when its coordinate coaction is
`v ⊗ χ`. -/
def IsCharacterWeightVectorData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V)
    (χ : GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G))
    (v : V) : Prop :=
  rationalRepresentationCoactionData G V D v =
    v ⊗ₜ[K] (χ : AffineAlgebraicGroup.coordinateHopfAlgebra G)

/-- Exact internal-direct-sum predicate for the character weight spaces of a
rational representation.

The first clause says every vector is a finite sum of weight vectors.  The
second says any finite weight-vector sum equal to zero has every summand zero,
which is exactly uniqueness/directness. -/
def HasCharacterWeightDecompositionData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type u)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V) : Prop :=
  let X := GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra G)
  (∀ v : V,
    ∃ s : Finset X, ∃ w : X → V,
      (∀ χ : X, χ ∈ s → IsCharacterWeightVectorData G V D χ (w χ)) ∧
        v = ∑ χ ∈ s, w χ) ∧
  (∀ (s : Finset X) (w : X → V),
    (∀ χ : X, χ ∈ s → IsCharacterWeightVectorData G V D χ (w χ)) →
      (∑ χ ∈ s, w χ) = 0 →
        ∀ χ : X, χ ∈ s → w χ = 0)

/-- Humphreys' definition of a diagonalizable group: every rational
representation is the direct sum of its character weight spaces. -/
def IsDiagonalizableGroupData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) : Prop :=
  ∀ (V : Type u) (_ : AddCommGroup V) (_ : Module K V)
    (D : RationalRepresentationCoordinateData G V),
    IsRationalRepresentationCoordinateData G V D →
      HasCharacterWeightDecompositionData G V D

/-- Humphreys' definition of a torus: a connected diagonalizable algebraic
group.  The equivalent classification by powers of `G_m` is result content. -/
def IsTorusData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) : Prop :=
  IsDiagonalizableGroupData G ∧
    IsConnected (Set.univ : Set G.1.X.left)

end LeanCategories.AlgebraicGeometry
