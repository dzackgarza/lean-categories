/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Instances.Matrix

/-!
# Topological orthogonal groups

For a finite matrix `B`, its orthogonal group is the subgroup of the matrix general linear group
defined by `Aᵀ B A = B`. The subgroup topology gives its canonical topological-group structure.
-/

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type v} [CommRing R]

/-- The orthogonal group of a Gram matrix. -/
def MatrixOrthogonalGroup (B : Matrix n n R) :
    Subgroup (Matrix.GeneralLinearGroup n R) where
  carrier := {A | A.1.transpose * B * A.1 = B}
  one_mem' := by simp
  mul_mem' := by
    intro A C hA hC
    change A.1.transpose * B * A.1 = B at hA
    change C.1.transpose * B * C.1 = B at hC
    change (A.1 * C.1).transpose * B * (A.1 * C.1) = B
    rw [Matrix.transpose_mul]
    calc
      C.1.transpose * A.1.transpose * B * (A.1 * C.1) =
          C.1.transpose * (A.1.transpose * B * A.1) * C.1 := by
            simp only [mul_assoc]
      _ = C.1.transpose * B * C.1 := by rw [hA]
      _ = B := hC
  inv_mem' := by
    intro A hA
    change A.1.transpose * B * A.1 = B at hA
    change A⁻¹.1.transpose * B * A⁻¹.1 = B
    calc
      A⁻¹.1.transpose * B * A⁻¹.1 =
          A⁻¹.1.transpose * (A.1.transpose * B * A.1) * A⁻¹.1 := by rw [hA]
      _ = (↑(A * A⁻¹) : Matrix n n R).transpose * B * ↑(A * A⁻¹) := by
        simp only [Units.val_mul, Matrix.transpose_mul, mul_assoc]
      _ = B := by simp

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The matrix orthogonal group inherits its topology from the matrix general linear group. -/
example (B : Matrix n n R) : TopologicalSpace (MatrixOrthogonalGroup B) := inferInstance

/-- Matrix orthogonal groups are topological groups. -/
example (B : Matrix n n R) : IsTopologicalGroup (MatrixOrthogonalGroup B) := inferInstance

/-- The matrix orthogonal group is closed in the matrix general linear group. -/
theorem matrixOrthogonalGroup_isClosed [T2Space R] (B : Matrix n n R) :
    IsClosed (MatrixOrthogonalGroup B : Set (Matrix.GeneralLinearGroup n R)) := by
  apply isClosed_eq
  · exact ((Units.continuous_val.matrix_transpose.mul continuous_const).mul
      Units.continuous_val)
  · exact continuous_const

/-- Over a compact Hausdorff coefficient ring, the matrix orthogonal group is compact. -/
theorem matrixOrthogonalGroup_isCompact [T2Space R] [CompactSpace R]
    (B : Matrix n n R) : IsCompact (Set.univ : Set (MatrixOrthogonalGroup B)) := by
  letI : CompactSpace (Matrix n n R) := Pi.compactSpace
  letI : CompactSpace (Matrix.GeneralLinearGroup n R) := inferInstance
  letI : CompactSpace (MatrixOrthogonalGroup B) :=
    (matrixOrthogonalGroup_isClosed B).isClosedEmbedding_subtypeVal.compactSpace
  exact isCompact_univ

/-- Matrix orthogonal groups over locally compact Hausdorff rings are locally compact. -/
noncomputable instance matrixOrthogonalGroupLocallyCompactSpace
    [T2Space R] [LocallyCompactSpace R] (B : Matrix n n R) :
    LocallyCompactSpace (MatrixOrthogonalGroup B) := by
  letI : LocallyCompactSpace (n → R) := Pi.locallyCompactSpace_of_finite
  letI : LocallyCompactSpace (Matrix n n R) := Pi.locallyCompactSpace_of_finite
  letI : LocallyCompactSpace (Matrix.GeneralLinearGroup n R) := inferInstance
  exact (matrixOrthogonalGroup_isClosed B).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The canonical Mathlib Haar measure on a matrix orthogonal group. -/
noncomputable def matrixOrthogonalHaarMeasure [T2Space R] [LocallyCompactSpace R]
    (B : Matrix n n R) :
    @MeasureTheory.Measure (MatrixOrthogonalGroup B) (borel (MatrixOrthogonalGroup B)) := by
  letI : MeasurableSpace (MatrixOrthogonalGroup B) := borel _
  letI : BorelSpace (MatrixOrthogonalGroup B) := ⟨rfl⟩
  exact MeasureTheory.Measure.haar

end Topology

end LeanCategories.Modules.Bilinear.Valued
