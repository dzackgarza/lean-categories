/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan

@[expose] public noncomputable section

namespace LeanCategories.Algebra

/-- Edge-multiplicity data of a Coxeter multigraph. -/
abbrev CoxeterGraphData (ι : Type*) := ι → ι → ℕ

/-- Humphreys FC14-C03-U039: off-diagonal edge multiplicity `a_ij a_ji`
from supplied Cartan-matrix data. Value bounds are theorem content. -/
noncomputable def coxeterGraphOfCartanMatrix {ι : Type*}
    (A : Matrix ι ι ℤ) : CoxeterGraphData ι := by
  classical
  exact fun i j => if i = j then 0 else Int.toNat (A i j * A j i)

end LeanCategories.Algebra
