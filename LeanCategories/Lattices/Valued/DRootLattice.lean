/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DefiniteNondegenerate

/-!
# The type-`D` root lattices

`Standard.lean` presents `Dₙ` for `4 ≤ n` by the Gram matrix of the standard roots
`e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₂ + eₙ₋₁`, and proves that matrix negative definite. This file
joins `Dₙ` to the categories of `DefiniteIndefinite.lean`.

* `dDefiniteLattice` is `Dₙ` as an object of `DefiniteLatticeCat`.
* The presenting basis has constant diagonal `-2`, so every basis vector is a root and the
  roots span: `dDefiniteLattice_isRootLattice`.
* `dRootLatticeObject` is `Dₙ` as an object of `RootLatticeCat`, next to `aRootLatticeObject`
  and `e8RootLatticeObject`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The type-`D` lattice as an object of the definite category. -/
def dDefiniteLattice (n : ℕ) (hn : 4 ≤ n) : DefiniteLatticeCat :=
  ⟨dRootFiniteLattice n hn, Or.inr (dRootLattice_isNegativeDefinite n hn)⟩

/-- The standard type-`D` roots span, so `Dₙ` is a root lattice. -/
theorem dDefiniteLattice_isRootLattice (n : ℕ) (hn : 4 ≤ n) :
    isRootLattice (dDefiniteLattice n hn) := by
  refine span_isRoot_eq_top_of_basis (dRootFiniteLattice n hn)
    (Pi.basisFun ℤ (Fin n)) fun i ↦ ?_
  rw [pairing_basis_self_eq_gramMatrix_diag, dRootFiniteLattice_gramMatrix,
    dRootGramMatrix_diag]

/-- The type-`D` root lattice as an object of `RootLatticeCat`. -/
def dRootLatticeObject (n : ℕ) (hn : 4 ≤ n) : RootLatticeCat :=
  ⟨dDefiniteLattice n hn, dDefiniteLattice_isRootLattice n hn⟩

end LeanCategories.Lattices.Valued
