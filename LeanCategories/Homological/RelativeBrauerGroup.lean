/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Relative Brauer classes

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.6.11,
pp. 182--188 (FC05-C06-U075).

For a finite Galois extension `L/K`, the relative Brauer group consists of the
Brauer classes of central simple `K`-algebras which split after scalar extension
to `L`.  This file records the underlying class predicate.  Closure under the
Brauer-group operation and the crossed-product identification with `H²` are
result-level statements.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped TensorProduct

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- A central simple `K`-algebra splits over `L` when its scalar extension is a
matrix algebra over `L`. -/
def CSASplitsOver (A : CSA K) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧
    Nonempty ((L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L)

/-- The relative Brauer classes `Br(L/K)` as the subset of `Br(K)` represented
by central simple algebras split by `L`. -/
def relativeBrauerClasses : Set (BrauerGroup K) :=
  {c | ∃ A : CSA K,
    (Quotient.mk (Brauer.CSA_Setoid K) A : BrauerGroup K) = c ∧ CSASplitsOver K L A}

end LeanCategories.Homological
