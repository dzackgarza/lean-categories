/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.KostantIntegralFormData
public import Mathlib.Algebra.Module.Lattice

/-!
# Admissible lattices for the Kostant integral form

Definition-level realization of Humphreys FC14-C07-U032.

For a finite-dimensional module `V), Humphreys calls a `ℤ`-lattice
admissible when it is invariant under the Kostant integral form
`U(L)_ℤ`.  The source lattice condition is finite generation, full
scalar span, and the displayed `ℤ`-rank bound.

Existence of admissible lattices, their weight-space decomposition, and
the assertion that `U(L)_ℤ v⁺` is the minimal admissible lattice
containing a chosen maximal vector are result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w x

variable (K : Type u) (L : Type v) (V : Type w)
variable [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- The canonical action of `U(L)` induced by the given `L`-module. -/
def kostantUEARepresentation :
    UniversalEnvelopingAlgebra K L →ₐ[K] Module.End K V :=
  UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)

/-- Humphreys' lattice condition from §27.1 for a `ℤ`-submodule of
a characteristic-zero `K`-vector space. -/
def IsHumphreysLatticeData (M : Submodule ℤ V) : Prop :=
  M.FG ∧
    Submodule.span K (M : Set V) = ⊤ ∧
    Module.rank ℤ M ≤ Module.rank K V

/-- An admissible lattice is a Humphreys lattice preserved by the
root-generated Kostant integral form `U(L)_ℤ`. -/
def IsKostantAdmissibleLatticeData {Phi : Type x}
    (rootVector : Phi → L) (M : Submodule ℤ V) : Prop :=
  IsHumphreysLatticeData K V M ∧
    ∀ u : kostantIntegralFormData K L rootVector, ∀ v : M,
      kostantUEARepresentation K L V
          (u : UniversalEnvelopingAlgebra K L) (v : V) ∈ M

end LeanCategories.Algebra
