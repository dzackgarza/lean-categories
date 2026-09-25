/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Definition-level data for the general linear algebraic group

Realization of the construction part of Humphreys FC16-C02-U004.

The underlying affine scheme of `GL_n` is the principal open `det ≠ 0` in
matrix affine space. Algebraically its coordinate ring is
`K[X_ij][det(X)⁻¹]`.

Multiplication, identity and inversion are contravariantly represented by
algebra maps whose values on the localized generic matrix are respectively
matrix multiplication, the identity matrix and the nonsingular inverse.

The predicates below state those maps by exact generic-coordinate graphs.
Their existence as maps out of the determinant localization, the Hopf/group
identities among them, and the fact that the resulting group scheme is an
affine algebraic group are result-layer facts. No such proof is placed in a
Sweep-III constructor.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace LeanCategories.AlgebraicGeometry

open _root_.AlgebraicGeometry
open Algebra.TensorProduct

universe u

/-- Polynomial coordinate ring of `n × n` matrices. -/
abbrev MatrixCoordinateRingData (K : Type u) [CommRing K] (n : ℕ) :=
  MvPolynomial (Fin n × Fin n) K

/-- Humphreys' coordinate ring of `GL_n`, obtained by inverting the generic
determinant. -/
abbrev GeneralLinearCoordinateRingData (K : Type u) [CommRing K] (n : ℕ) :=
  Localization.Away
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))

/-- The canonical algebra map from matrix coordinates into the determinant
localization. -/
def generalLinearCoordinateMapData (K : Type u) [CommRing K] (n : ℕ) :
    MatrixCoordinateRingData K n →ₐ[K] GeneralLinearCoordinateRingData K n :=
  IsScalarTower.toAlgHom K (MatrixCoordinateRingData K n)
    (GeneralLinearCoordinateRingData K n)

/-- The generic matrix on the determinant principal open. -/
def generalLinearGenericMatrixData (K : Type u) [CommRing K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (GeneralLinearCoordinateRingData K n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
    (generalLinearCoordinateMapData K n)

/-- The affine scheme underlying `GL_n`. -/
def generalLinearSchemeData (K : Type u) [CommRing K] (n : ℕ) : Scheme.{u} :=
  Spec (.of (GeneralLinearCoordinateRingData K n))

/-- The canonical morphism from `GL_n` to matrix affine space. Since the
source ring is the localization away from `det`, this is exactly the source's
principal-open presentation; identifying its image with `det ≠ 0` is the
standard localization comparison result. -/
def generalLinearPrincipalOpenMapData (K : Type u) [CommRing K] (n : ℕ) :
    generalLinearSchemeData K n ⟶
      Spec (.of (MatrixCoordinateRingData K n)) :=
  Spec.map (CommRingCat.ofHom (generalLinearCoordinateMapData K n).toRingHom)

/-- Candidate coordinate maps for multiplication, identity and inversion.
This is raw construction data only: no bialgebra or Hopf laws are fields. -/
structure GeneralLinearOperationData (K : Type u) [CommRing K] (n : ℕ) where
  comul : GeneralLinearCoordinateRingData K n →ₐ[K]
    GeneralLinearCoordinateRingData K n ⊗[K] GeneralLinearCoordinateRingData K n
  counit : GeneralLinearCoordinateRingData K n →ₐ[K] K
  antipode : GeneralLinearCoordinateRingData K n →ₐ[K]
    GeneralLinearCoordinateRingData K n

/-- Exact generic-coordinate graph of the three structure maps of `GL_n`.

An algebra map out of the determinant localization is uniquely determined by
its restriction to matrix coordinates. Thus these formulas pin the candidate
maps to ordinary matrix multiplication, identity and inversion without
requiring the extension-existence or Hopf-law proofs. -/
def IsGeneralLinearOperationData (K : Type u) [CommRing K] (n : ℕ)
    (D : GeneralLinearOperationData K n) : Prop :=
  (∀ i j : Fin n,
    D.comul (generalLinearGenericMatrixData K n i j) =
      ∑ k : Fin n,
        generalLinearGenericMatrixData K n i k ⊗ₜ[K]
          generalLinearGenericMatrixData K n k j) ∧
  (∀ i j : Fin n,
    D.counit (generalLinearGenericMatrixData K n i j) =
      if i = j then 1 else 0) ∧
  (∀ i j : Fin n,
    D.antipode (generalLinearGenericMatrixData K n i j) =
      (generalLinearGenericMatrixData K n)⁻¹ i j)

/-- Multiplication morphism on the tensor-coordinate presentation, induced
contravariantly by a candidate comultiplication. The canonical pullback-Spec
isomorphism identifies this source with `GL_n ×_K GL_n`. -/
def generalLinearMultiplicationMapData (K : Type u) [CommRing K] (n : ℕ)
    (D : GeneralLinearOperationData K n) :
    Spec (.of
      (GeneralLinearCoordinateRingData K n ⊗[K]
        GeneralLinearCoordinateRingData K n)) ⟶
      generalLinearSchemeData K n :=
  Spec.map (CommRingCat.ofHom D.comul.toRingHom)

/-- Identity section induced contravariantly by the candidate counit. -/
def generalLinearIdentityMapData (K : Type u) [CommRing K] (n : ℕ)
    (D : GeneralLinearOperationData K n) :
    Spec (.of K) ⟶ generalLinearSchemeData K n :=
  Spec.map (CommRingCat.ofHom D.counit.toRingHom)

/-- Inversion morphism induced contravariantly by the candidate antipode. -/
def generalLinearInversionMapData (K : Type u) [CommRing K] (n : ℕ)
    (D : GeneralLinearOperationData K n) :
    generalLinearSchemeData K n ⟶ generalLinearSchemeData K n :=
  Spec.map (CommRingCat.ofHom D.antipode.toRingHom)

end LeanCategories.AlgebraicGeometry
