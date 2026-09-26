/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AffineAlgebraicGroup
public import LeanCategories.AlgebraicGeometry.GeneralLinearGroupData
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Rational representations of affine algebraic groups

Definition-level realization of Humphreys FC16-C02-U013.

For affine algebraic groups, a morphism `G → GL(V)` is contravariantly a
coordinate-algebra morphism `O(GL(V)) → K[G]` compatible with multiplication,
identity and inversion.  After choosing a finite basis of `V`, the target
coordinate ring is the determinant localization realized in FC16-C02-U004.

The declarations below record the coordinate map and the exact three
compatibility equations.  The chosen basis is presentation data only and is
existentially hidden by `IsRationalRepresentationData`.  Equivalence with the
scheme-theoretic group morphism, basis independence, and the associated point
action/comodule are reference-owned result-layer statements.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace LeanCategories.AlgebraicGeometry

open Algebra.TensorProduct

universe u v

/-- A basis presentation and coordinate-algebra map for a candidate rational
representation.  No representation law is a structure field. -/
structure RationalRepresentationCoordinateData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type v)
  [AddCommGroup V] [Module K V] where
  n : ℕ
  basis : Module.Basis (Fin n) K V
  coordinate : GeneralLinearCoordinateRingData K n →ₐ[K]
    AffineAlgebraicGroup.coordinateHopfAlgebra G

/-- Exact coordinate-ring graph of a rational representation.

The equations say precisely that the opposite map is a morphism of group
objects: multiplication, identity and inversion are respected. -/
def IsRationalRepresentationCoordinateData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type v)
    [AddCommGroup V] [Module K V]
    (D : RationalRepresentationCoordinateData G V) : Prop :=
  (Algebra.TensorProduct.map D.coordinate D.coordinate).comp
        (generalLinearOperationData K D.n).comul =
      (AffineAlgebraicGroup.coordinateComultiplication G).comp D.coordinate ∧
    (AffineAlgebraicGroup.coordinateCounit G).comp D.coordinate =
      (generalLinearOperationData K D.n).counit ∧
    (AffineAlgebraicGroup.coordinateAntipode G).comp D.coordinate =
      D.coordinate.comp (generalLinearOperationData K D.n).antipode

/-- A rational representation presented in a finite basis, with the three
group-morphism compatibilities included as structure fields.  The GL
operations are the canonical maps constructed in FC16-C02-U004. -/
structure RationalRepresentationData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type v)
    [AddCommGroup V] [Module K V] where
  presentation : RationalRepresentationCoordinateData G V
  isRational : IsRationalRepresentationCoordinateData G V presentation

/-- Humphreys' basis-free terminology: a rational representation on `V` is
one admitting a finite basis presentation whose coordinate map satisfies the
exact algebraic-group morphism graph above. -/
def IsRationalRepresentationData
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : AffineAlgebraicGroup K) (V : Type v)
    [AddCommGroup V] [Module K V] : Prop :=
  Nonempty (RationalRepresentationData G V)

end LeanCategories.AlgebraicGeometry
