/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.RootLattice
public import LeanCategories.Lattices.Valued.Standard

/-!
# Definite lattices are nondegenerate, and the standard root lattices

`Signature.lean` states definiteness through the null part of `integralSignature`, and
`RootSystem.lean` builds a Mathlib root pairing out of the reflective vectors of any
nondegenerate lattice. This file joins the two.

* A definite lattice is nondegenerate. `Theta.lean` already proves that a nonzero vector of a
  positive definite lattice has a positive self-pairing, which is the real-signature statement
  transported back to the integers by a Gram matrix. A vector of the radical pairs to zero with
  itself, so it is zero. Negation of the form covers the negative definite case.
* `rootPairingOfDefinite` feeds a definite lattice to `reflectiveRootPairing`, so the Mathlib
  root pairing API applies to every definite lattice, and in particular to every object of
  `RootLatticeCat`.
* The standard lattices `A_n`, `E₆`, `E₇` and `E₈` of `Standard.lean` satisfy `isRootLattice`.
  Each is presented by a Gram matrix with constant diagonal `-2`, so every vector of the
  presenting basis is a root, and a basis spans. `DRootLattice.lean` does the same for `Dₙ`, so
  every simply-laced type has an object of `RootLatticeCat`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- A nonzero vector of a definite lattice has a nonzero self-pairing. -/
theorem pairing_self_ne_zero_of_isDefiniteLattice (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) {x : L.obj.obj.carrier} (hx : x ≠ 0) :
    L.obj.obj.pairing x x ≠ 0 := by
  rcases hL with hpos | hneg
  · exact (L.pairing_self_pos hpos hx).ne'
  · have h := (oppositeFiniteProjectiveLattice L).pairing_self_pos
      (FiniteProjectiveLatticeCat.isPositiveDefiniteLattice_opposite L hneg) hx
    change 0 < (oppositeLattice L.obj).obj.pairing x x at h
    rw [oppositeLattice_pairing, neg_pos] at h
    exact h.ne

/-- A definite integral lattice is nondegenerate: its radical is zero because a radical vector
pairs to zero with itself. -/
theorem isNondegenerate_of_isDefiniteLattice (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) : L.obj.obj.IsNondegenerate := by
  rw [BilinModuleCat.isNondegenerate_iff_adjoint_injective_of_isSymmetric _ L.obj.property.2,
    injective_iff_map_eq_zero]
  intro x hx
  by_contra hxne
  refine pairing_self_ne_zero_of_isDefiniteLattice L hL hxne ?_
  exact LinearMap.congr_fun hx x

/-- The Mathlib root pairing on the reflective vectors of a definite lattice. Nondegeneracy is
the only hypothesis `reflectiveRootPairing` needs beyond regularity of `2`, and definiteness
supplies it. -/
noncomputable def rootPairingOfDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) :
    RootPairing (ReflectiveRoot L) ℤ L.obj.obj.carrier
      (Module.Dual ℤ L.obj.obj.carrier) :=
  reflectiveRootPairing L (isNondegenerate_of_isDefiniteLattice L hL)
    (IsRegular.of_ne_zero two_ne_zero)

/-- The Weyl group of a definite lattice, acting through its orthogonal group. -/
noncomputable def weylSubgroupOfDefinite (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (hL : isDefiniteLattice L) : Subgroup (OrthogonalGroup L.obj) :=
  reflectiveWeylSubgroup L (isNondegenerate_of_isDefiniteLattice L hL)
    (IsRegular.of_ne_zero two_ne_zero)

/-- The root pairing of a definite root lattice. -/
noncomputable def rootLatticeRootPairing (L : RootLatticeCat) :
    RootPairing (ReflectiveRoot L.obj.obj) ℤ L.obj.obj.obj.obj.carrier
      (Module.Dual ℤ L.obj.obj.obj.obj.carrier) :=
  rootPairingOfDefinite L.obj.obj L.obj.property

/-- The self-pairings of a basis are the diagonal of the Gram matrix in that basis. -/
theorem pairing_basis_self_eq_gramMatrix_diag {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat ℤ) (b : Module.Basis I ℤ L.obj.carrier) (i : I) :
    L.obj.pairing (b i) (b i) = gramMatrix L b i i := by
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply]
  rfl

/-- A lattice whose basis vectors all have self-pairing `-2` is spanned by its roots: each
basis vector is itself a root. -/
theorem span_isRoot_eq_top_of_basis {I : Type*} (L : FiniteProjectiveLatticeCat ℤ ℤ)
    (b : Module.Basis I ℤ L.obj.obj.carrier)
    (hb : ∀ i, L.obj.obj.pairing (b i) (b i) = -2) :
    Submodule.span ℤ {x : L.obj.obj.carrier | IsRoot L.obj x} = ⊤ := by
  rw [eq_top_iff, ← b.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Or.inr (Or.inl (hb i))

/-- The diagonal of the type-`A` Gram matrix is `-2`: each standard root `eᵢ - eᵢ₊₁` has two
nonzero coordinates, and the matrix is the negative of the coordinate dot product. -/
theorem aRootGramMatrix_diag (n : ℕ) (i : Fin n) : aRootGramMatrix n i i = -2 := by
  have hvalue (k : Fin (n + 1)) :
      aRootVector n i k * aRootVector n i k =
        (if k = i.castSucc then (1 : ℤ) else 0) + (if k = i.succ then 1 else 0) := by
    simp only [aRootVector, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> simp_all
  simp only [aRootGramMatrix]
  simp_rw [hvalue]
  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
  norm_num

/-- The type-`A` lattice as an object of the definite category. -/
def aDefiniteLattice (n : ℕ) : DefiniteLatticeCat :=
  ⟨aRootFiniteLattice n, Or.inr (aRootLattice_isNegativeDefinite n)⟩

/-- The standard type-`A` roots span, so `A_n` is a root lattice. -/
theorem aDefiniteLattice_isRootLattice (n : ℕ) : isRootLattice (aDefiniteLattice n) := by
  refine span_isRoot_eq_top_of_basis (aRootFiniteLattice n) (Pi.basisFun ℤ (Fin n)) fun i ↦ ?_
  rw [pairing_basis_self_eq_gramMatrix_diag, aRootFiniteLattice_gramMatrix,
    aRootGramMatrix_diag]

/-- The type-`A` root lattice as an object of `RootLatticeCat`. -/
def aRootLatticeObject (n : ℕ) : RootLatticeCat :=
  ⟨aDefiniteLattice n, aDefiniteLattice_isRootLattice n⟩

/-- The diagonal of the `E₈` Gram matrix is `-2`. -/
theorem e8GramMatrix_diag (i : Fin 8) : e8GramMatrix i i = -2 := by
  rw [e8GramMatrix_eq]
  fin_cases i <;> norm_num

/-- The `E₈` lattice as an object of the definite category. -/
noncomputable def e8DefiniteLattice : DefiniteLatticeCat :=
  ⟨e8FiniteLattice, Or.inr e8Lattice_isNegativeDefinite⟩

/-- The simple roots of `E₈` span, so `E₈` is a root lattice. -/
theorem e8DefiniteLattice_isRootLattice : isRootLattice e8DefiniteLattice := by
  refine span_isRoot_eq_top_of_basis e8FiniteLattice (Pi.basisFun ℤ (Fin 8)) fun i ↦ ?_
  rw [pairing_basis_self_eq_gramMatrix_diag]
  change gramMatrix e8Lattice (Pi.basisFun ℤ (Fin 8)) i i = -2
  rw [e8Lattice_gramMatrix, e8GramMatrix_diag]

/-- The `E₈` root lattice as an object of `RootLatticeCat`. -/
noncomputable def e8RootLatticeObject : RootLatticeCat :=
  ⟨e8DefiniteLattice, e8DefiniteLattice_isRootLattice⟩

/-- The diagonal of the `E₇` Gram matrix is `-2`. -/
theorem e7GramMatrix_diag (i : Fin 7) : e7GramMatrix i i = -2 := by
  rw [e7GramMatrix_eq]
  fin_cases i <;> norm_num

/-- The `E₇` lattice as an object of the definite category. -/
noncomputable def e7DefiniteLattice : DefiniteLatticeCat :=
  ⟨e7FiniteLattice, Or.inr e7Lattice_isNegativeDefinite⟩

/-- The simple roots of `E₇` span, so `E₇` is a root lattice. -/
theorem e7DefiniteLattice_isRootLattice : isRootLattice e7DefiniteLattice := by
  refine span_isRoot_eq_top_of_basis e7FiniteLattice (Pi.basisFun ℤ (Fin 7)) fun i ↦ ?_
  rw [pairing_basis_self_eq_gramMatrix_diag]
  change gramMatrix e7Lattice (Pi.basisFun ℤ (Fin 7)) i i = -2
  rw [e7Lattice_gramMatrix, e7GramMatrix_diag]

/-- The `E₇` root lattice as an object of `RootLatticeCat`. -/
noncomputable def e7RootLatticeObject : RootLatticeCat :=
  ⟨e7DefiniteLattice, e7DefiniteLattice_isRootLattice⟩

/-- The diagonal of the `E₆` Gram matrix is `-2`. -/
theorem e6GramMatrix_diag (i : Fin 6) : e6GramMatrix i i = -2 := by
  rw [e6GramMatrix_eq]
  fin_cases i <;> norm_num

/-- The `E₆` lattice as an object of the definite category. -/
noncomputable def e6DefiniteLattice : DefiniteLatticeCat :=
  ⟨e6FiniteLattice, Or.inr e6Lattice_isNegativeDefinite⟩

/-- The simple roots of `E₆` span, so `E₆` is a root lattice. -/
theorem e6DefiniteLattice_isRootLattice : isRootLattice e6DefiniteLattice := by
  refine span_isRoot_eq_top_of_basis e6FiniteLattice (Pi.basisFun ℤ (Fin 6)) fun i ↦ ?_
  rw [pairing_basis_self_eq_gramMatrix_diag]
  change gramMatrix e6Lattice (Pi.basisFun ℤ (Fin 6)) i i = -2
  rw [e6Lattice_gramMatrix, e6GramMatrix_diag]

/-- The `E₆` root lattice as an object of `RootLatticeCat`. -/
noncomputable def e6RootLatticeObject : RootLatticeCat :=
  ⟨e6DefiniteLattice, e6DefiniteLattice_isRootLattice⟩

end LeanCategories.Lattices.Valued
