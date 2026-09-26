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

noncomputable def matrixMonoidComulData (K : Type u) [CommRing K] (n : ℕ) :
    MatrixCoordinateRingData K n →ₐ[K]
      MatrixCoordinateRingData K n ⊗[K] MatrixCoordinateRingData K n :=
  MvPolynomial.aeval fun ij : Fin n × Fin n =>
    ∑ k : Fin n, MvPolynomial.X (ij.1, k) ⊗ₜ[K] MvPolynomial.X (k, ij.2)

noncomputable def matrixMonoidCounitData (K : Type u) [CommRing K] (n : ℕ) :
    MatrixCoordinateRingData K n →ₐ[K] K :=
  MvPolynomial.aeval fun ij : Fin n × Fin n =>
    (1 : Matrix (Fin n) (Fin n) K) ij.1 ij.2

@[simp] lemma matrixMonoidComulData_X
    (K : Type u) [CommRing K] (n : ℕ) (i j : Fin n) :
    matrixMonoidComulData K n (MvPolynomial.X (i, j)) =
      ∑ k : Fin n, MvPolynomial.X (i, k) ⊗ₜ[K] MvPolynomial.X (k, j) := by
  simp [matrixMonoidComulData]

@[simp] lemma matrixMonoidCounitData_X
    (K : Type u) [CommRing K] (n : ℕ) (i j : Fin n) :
    matrixMonoidCounitData K n (MvPolynomial.X (i, j)) =
      if i = j then 1 else 0 := by
  simp [matrixMonoidCounitData, Matrix.one_apply]

private lemma matrixMonoidComulData_genericMatrix
    (K : Type u) [CommRing K] (n : ℕ) :
    (Matrix.mvPolynomialX (Fin n) (Fin n) K).map (matrixMonoidComulData K n) =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
          (includeLeft : MatrixCoordinateRingData K n →ₐ[K]
            MatrixCoordinateRingData K n ⊗[K] MatrixCoordinateRingData K n) *
        (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
          (includeRight : MatrixCoordinateRingData K n →ₐ[K]
            MatrixCoordinateRingData K n ⊗[K] MatrixCoordinateRingData K n) := by
  ext i j
  simp [Matrix.mul_apply]

private lemma matrixMonoidCounitData_genericMatrix
    (K : Type u) [CommRing K] (n : ℕ) :
    (Matrix.mvPolynomialX (Fin n) (Fin n) K).map (matrixMonoidCounitData K n) = 1 := by
  ext i j
  simp [Matrix.one_apply]

private lemma matrixMonoidComulData_determinant
    (K : Type u) [CommRing K] (n : ℕ) :
    matrixMonoidComulData K n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)) =
      Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K) ⊗ₜ[K]
        Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K) := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, matrixMonoidComulData_genericMatrix,
    Matrix.det_mul]
  rw [← AlgHom.mapMatrix_apply
      (includeLeft : MatrixCoordinateRingData K n →ₐ[K]
        MatrixCoordinateRingData K n ⊗[K] MatrixCoordinateRingData K n),
    ← AlgHom.mapMatrix_apply
      (includeRight : MatrixCoordinateRingData K n →ₐ[K]
        MatrixCoordinateRingData K n ⊗[K] MatrixCoordinateRingData K n),
    ← AlgHom.map_det, ← AlgHom.map_det]
  simp

private lemma matrixMonoidCounitData_determinant
    (K : Type u) [CommRing K] (n : ℕ) :
    matrixMonoidCounitData K n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)) = 1 := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, matrixMonoidCounitData_genericMatrix,
    Matrix.det_one]

@[simp] lemma generalLinearDetGenericMatrixData
    (K : Type u) [CommRing K] (n : ℕ) :
    Matrix.det (generalLinearGenericMatrixData K n) =
      generalLinearCoordinateMapData K n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)) := by
  rw [generalLinearGenericMatrixData, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

private lemma generalLinearDetGenericMatrixData_isUnit
    (K : Type u) [CommRing K] (n : ℕ) :
    IsUnit (Matrix.det (generalLinearGenericMatrixData K n)) := by
  rw [generalLinearDetGenericMatrixData]
  exact IsLocalization.Away.algebraMap_isUnit
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))

noncomputable def generalLinearComulBaseData
    (K : Type u) [CommRing K] (n : ℕ) :
    MatrixCoordinateRingData K n →ₐ[K]
      GeneralLinearCoordinateRingData K n ⊗[K] GeneralLinearCoordinateRingData K n :=
  (Algebra.TensorProduct.map
      (generalLinearCoordinateMapData K n) (generalLinearCoordinateMapData K n)).comp
    (matrixMonoidComulData K n)

lemma generalLinearComulBaseData_determinant_isUnit
    (K : Type u) [CommRing K] (n : ℕ) :
    IsUnit (generalLinearComulBaseData K n
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) := by
  rw [generalLinearComulBaseData, AlgHom.comp_apply, matrixMonoidComulData_determinant,
    map_tmul]
  have h : IsUnit
      (generalLinearCoordinateMapData K n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) :=
    IsLocalization.Away.algebraMap_isUnit
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))
  have hl : IsUnit
      ((includeLeft : GeneralLinearCoordinateRingData K n →ₐ[K]
        GeneralLinearCoordinateRingData K n ⊗[K] GeneralLinearCoordinateRingData K n)
        (generalLinearCoordinateMapData K n
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)))) :=
    h.map includeLeft
  have hr : IsUnit
      ((includeRight : GeneralLinearCoordinateRingData K n →ₐ[K]
        GeneralLinearCoordinateRingData K n ⊗[K] GeneralLinearCoordinateRingData K n)
        (generalLinearCoordinateMapData K n
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)))) :=
    h.map includeRight
  convert hl.mul hr using 1 <;> simp

noncomputable def generalLinearComulData
    (K : Type u) [CommRing K] (n : ℕ) :
    GeneralLinearCoordinateRingData K n →ₐ[K]
      GeneralLinearCoordinateRingData K n ⊗[K] GeneralLinearCoordinateRingData K n :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))
    (generalLinearComulBaseData_determinant_isUnit K n)

noncomputable def generalLinearCounitData
    (K : Type u) [CommRing K] (n : ℕ) :
    GeneralLinearCoordinateRingData K n →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))
    (f := matrixMonoidCounitData K n)
    (by
      rw [matrixMonoidCounitData_determinant]
      exact isUnit_one)

noncomputable def generalLinearAntipodeBaseData
    (K : Type u) [CommRing K] (n : ℕ) :
    MatrixCoordinateRingData K n →ₐ[K] GeneralLinearCoordinateRingData K n :=
  MvPolynomial.aeval fun ij : Fin n × Fin n =>
    ((generalLinearGenericMatrixData K n)⁻¹) ij.1 ij.2

lemma generalLinearAntipodeBaseData_determinant_isUnit
    (K : Type u) [CommRing K] (n : ℕ) :
    IsUnit (generalLinearAntipodeBaseData K n
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))) := by
  rw [generalLinearAntipodeBaseData, AlgHom.map_det]
  rw [Matrix.mvPolynomialX_mapMatrix_aeval]
  exact Matrix.isUnit_nonsing_inv_det _
    (generalLinearDetGenericMatrixData_isUnit K n)

noncomputable def generalLinearAntipodeData
    (K : Type u) [CommRing K] (n : ℕ) :
    GeneralLinearCoordinateRingData K n →ₐ[K] GeneralLinearCoordinateRingData K n :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K))
    (generalLinearAntipodeBaseData_determinant_isUnit K n)

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

noncomputable def generalLinearOperationData
    (K : Type u) [CommRing K] (n : ℕ) : GeneralLinearOperationData K n where
  comul := generalLinearComulData K n
  counit := generalLinearCounitData K n
  antipode := generalLinearAntipodeData K n

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
