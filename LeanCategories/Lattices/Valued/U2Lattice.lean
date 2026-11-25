/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.Standard

/-!
# The lattice `U(2)` (`#116`)

AEGS, **printed p. 11**: *"The Coxeter diagrams for the lattices `(18,0,0)_1 = U ⊕ E₈²` and
`(18,2,0)_1 = U(2) ⊕ E₈²`, cf. [AE22], are shown in Figure 5."* The Figure-5 wall set is therefore a
chamber of `U(2) ⊕ E₈²`, not of `T_dP` — the latter is `U ⊥ U(2) ⊥ E₈ ⊥ E₈`, of rank 20 by
`TdpIndex`, while `(18,2,0)_1` has rank 18. (An earlier draft of this development's report
attributed Figure 5 to `T_dP`; that was wrong, and this line is the correction.)

This file supplies the first summand, `U(2)` = the hyperbolic plane with its form doubled, and the
fact the source's rule needs about it: it is **even** (**printed p. 10**).

* `u2GramMatrix` — `2 • hyperbolicPlaneGramMatrix`;
* `u2Lattice`, `u2FiniteLattice` — the lattice and its bundled finite projective form;
* `u2_pairing` — its pairing, `2 (x₀y₁ + x₁y₀)`, so that the wall set can be computed against it;
* `u2_isEven` — every square is even.

## LC-09 record

`rg "u2Lattice|U2"` over `Lattices/Valued/` finds only `tdpU2Gram` (the block inside `T_dP`), never
the standalone lattice. Mathlib has no `U(2)`. Corpus: nothing for `"U(2) hyperbolic plane
doubled"`. No port; the construction is the one already used for `hyperbolicPlane` in
`Standard.lean`.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: `U(2)` and Figure 5 **printed p. 11**; the even
  2-elementary rule **printed p. 10**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The Gram matrix of `U(2)`: the hyperbolic plane with its form doubled. -/
noncomputable def u2GramMatrix : Matrix (Fin 2) (Fin 2) ℤ := (2 : ℤ) • hyperbolicPlaneGramMatrix

theorem u2GramMatrix_isSymm : u2GramMatrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [u2GramMatrix, hyperbolicPlaneGramMatrix]

/-- **`U(2)`** (AEGS printed p. 11). -/
noncomputable def u2Lattice : IntegralLatticeCat ℤ := by
  refine ⟨BilinModuleCat.ofBilinMap (Matrix.toBilin' u2GramMatrix), ?_, ?_⟩
  · change Module.Projective ℤ (Fin 2 → ℤ)
    infer_instance
  · intro x y
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr u2GramMatrix_isSymm).eq x y

/-- `U(2)` as a finite projective lattice. -/
noncomputable def u2FiniteLattice : FiniteProjectiveLatticeCat ℤ ℤ := by
  refine ⟨u2Lattice, ?_⟩
  change Module.Finite ℤ (Fin 2 → ℤ)
  infer_instance

/-- The pairing of `U(2)`: `2 (x₀y₁ + x₁y₀)`. -/
theorem u2_pairing (x y : Fin 2 → ℤ) :
    u2Lattice.obj.pairing x y = 2 * (x 0 * y 1 + x 1 * y 0) := by
  change Matrix.toBilin' u2GramMatrix x y = _
  rw [u2GramMatrix, Matrix.toBilin'_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [hyperbolicPlaneGramMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **`U(2)` is even**: every square is `4 y₀ y₁` (**printed p. 10**). -/
theorem u2_isEven (y : Fin 2 → ℤ) : (2 : ℤ) ∣ u2Lattice.obj.pairing y y :=
  ⟨2 * (y 0 * y 1), by rw [u2_pairing]; ring⟩

end LeanCategories.Lattices.Valued
