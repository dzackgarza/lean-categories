/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# Dynkin-diagram data

Definition-level realization of Humphreys FC14-C03-U040.  Starting from
ordered Cartan data, this file records the underlying Coxeter edge
multiplicity together with the asymmetric Cartan pair that orients a
multiple edge.

The root-length comparison identifying the arrow with the shorter root,
the reconstruction of Cartan integers from a diagram, and classification
results are not included here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- The ordered pair of Cartan entries attached to vertices `i,j`.  Keeping
the order retains the asymmetric information that distinguishes, for
example, the two orientations of a double edge. -/
def dynkinCartanPair {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) : ℤ × ℤ :=
  (A i j, A j i)

/-- Multiplicity of the underlying Coxeter edge. -/
noncomputable def dynkinEdgeMultiplicity {ι : Type*} (A : Matrix ι ι ℤ) :
    ι → ι → ℕ := by
  classical
  exact fun i j => if i = j then 0 else Int.toNat (A i j * A j i)

/-- Support of the Dynkin diagram: distinct vertices joined by a nonzero
Coxeter edge multiplicity. -/
noncomputable def dynkinAdjacent {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) : Prop :=
  i ≠ j ∧ dynkinEdgeMultiplicity A i j ≠ 0

/-- Raw orientation datum for a multiple edge from `i` toward `j`:
the `i,j` Cartan entry has larger absolute value than the reversed entry.
For root-system Cartan data, comparison with root lengths is a separate
result. -/
noncomputable def dynkinArrowToward {ι : Type*} (A : Matrix ι ι ℤ) (i j : ι) : Prop :=
  i ≠ j ∧
    1 < dynkinEdgeMultiplicity A i j ∧
    Int.natAbs (A j i) < Int.natAbs (A i j)

end LeanCategories.Algebra
