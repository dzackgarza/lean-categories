/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.VinbergE10Chamber

/-!
# A root of `E₁₀(2)`'s chamber that is no multiple of a simple root (`#116`)

`FoldingInvariantChamber.lean` and `FoldingInvariantConverse.lean` record, as the reason the
chamber-folding hypotheses are not derivable from `IsChamberWithWalls`, that in `E₁₀(2)` "a
reflection of a simple root is a root that is not a multiple of any simple root". That was a hand
computation and
its first statement named the wrong roots. This file makes it a theorem, with the right ones.

The `E₁₀` Cartan matrix has `C₀₁ = 0`, so the reflection in `α₀` *fixes* `α₁`; the pair to use is
`(α₃, α₁)`, where `C₁₃ = -1`. Since `e10SimpleRoot_pairing i j = -2 C_ij`, `α₁ · α₃ = 2` and
`α₃² = -4`, so the reflection in `α₃` carries `α₁` to `α₁ - 2·(2/(-4))·α₃ = α₁ + α₃`.

* `e10RootCoord_root` — the simple-root coordinates of a simple root are the unit vector;
* `e10_reflected_root_coord` — the coordinates of `α₁ + α₃` are `e₁ + e₃`;
* `e10_reflected_root_square` — its square is `-4`;
* `e10_reflected_root_reflective` — it is reflective (the divisibility holds with quotient
  `b ⬝ C c`, from `e10Root_sum_pairing`);
* `e10_reflected_root_not_multiple` — **it is no nonzero integer multiple of a simple root**;
* `e10_root_not_multiple_of_wall` — the three together: a negative reflective root of the lattice
  which is not an integer multiple of any wall root. So `hcomplete` fails for this chamber.

## LC-09 record

Searched for a computation of a reflected simple root in `E₁₀(2)` and for the coordinates of a root
in
the simple-root basis: `rg "e10RootCoord|e10Root_sum_coord|e10Root_pairing_coord"` gives
`VinbergE10Chamber.lean`'s coordinate machinery (used there for the reflective-norm argument) and no
statement about a specific reflected root; `rg "isReflectiveRoot_of_isometry|latticeReflection"`
gives
`WeylCone.lean:172,232` — reflectivity of an isometric image, which would need a nondegeneracy
hypothesis on `E₁₀(2)` that this repository does not supply, so the divisibility is done directly.
Mathlib's `LinearAlgebra/RootSystem` is the finite-type API and does not apply here. The
Formalization Corpus returns no files. Nothing ported.

## References

* È. B. Vinberg, *The groups of unit elements of certain quadratic forms*, Mat. Sb. 87 (1972), §1
  (the `E₁₀` chamber and its diagram), as formalized in `VinbergE10Chamber.lean`.
-/

@[expose] public section

open Matrix
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The simple-root coordinates of a simple root are the corresponding unit vector. -/
theorem e10RootCoord_root (i : Fin 10) :
    e10RootCoord (e10Root i) = Pi.single i 1 := by
  have hleft : e10RootMatrixInverse * e10RootMatrix = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, e10RootMatrix, e10RootMatrixInverse]
    fin_cases i <;> fin_cases j <;> decide
  have hmat : e10Root i = e10RootMatrix *ᵥ (Pi.single i 1) := by
    funext c
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · simp [e10RootMatrix, Pi.single_eq_same]
    · intro j _ hj
      simp [e10RootMatrix, Pi.single_eq_of_ne hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp only [e10RootCoord, hmat, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]

theorem e10RootCoord_root_right (i : Fin 10) : e10RootCoord (e10Root i) = Pi.single i 1 :=
  e10RootCoord_root i

/-- The coordinates of `α₁ + α₃` are `e₁ + e₃`. -/
theorem e10_reflected_root_coord :
    e10RootCoord (e10Root 1 + e10Root 3) = Pi.single 1 1 + Pi.single 3 1 := by
  rw [e10RootCoord, Matrix.mulVec_add]
  congr 1
  · exact e10RootCoord_root_right 1
  · exact e10RootCoord_root_right 3

/-- Its square is `-4`: `-2 · (b ⬝ᵥ C b)` with `b = e₁ + e₃`. -/
theorem e10_reflected_root_square :
    e10FiniteLattice.obj.obj.pairing (e10Root 1 + e10Root 3) (e10Root 1 + e10Root 3) = -4 := by
  change Matrix.toBilin' e10BlockGram
    (∑ i, e10RootCoord (e10Root 1 + e10Root 3) i • e10Root i)
    (∑ j, e10RootCoord (e10Root 1 + e10Root 3) j • e10Root j) = -4
  rw [e10Root_sum_pairing, e10_reflected_root_coord]
  simp only [Pi.single_apply, Pi.add_apply, Matrix.mulVec, dotProduct, e10Cartan,
    Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val']
  norm_num

/-- The dot product form of the square: `b ⬝ (C b) = 2` for `b = e₁ + e₃`, which is `v² = -4`
under `e10Root_sum_pairing`. -/
theorem e10_reflected_root_dot :
    e10RootCoord (e10Root 1 + e10Root 3) ⬝ᵥ
        (e10Cartan *ᵥ e10RootCoord (e10Root 1 + e10Root 3)) = 2 := by
  rw [e10_reflected_root_coord]
  simp only [Pi.single_apply, Pi.add_apply, Matrix.mulVec, dotProduct, e10Cartan,
    Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val']
  norm_num

/-- **`α₁ + α₃` is a reflective root of `E₁₀(2)`.** -/
theorem e10_reflected_root_reflective :
    IsReflectiveRoot e10FiniteLattice.obj (e10Root 1 + e10Root 3) := by
  refine ⟨?_, ?_⟩
  · change IsRegular (e10FiniteLattice.obj.obj.pairing (e10Root 1 + e10Root 3)
      (e10Root 1 + e10Root 3))
    rw [e10_reflected_root_square]
    exact IsRegular.of_ne_zero (by norm_num)
  · intro y
    have hv : e10Root 1 + e10Root 3
        = ∑ i, e10RootCoord (e10Root 1 + e10Root 3) i • e10Root i :=
      (e10Root_sum_coord _).symm
    have hy : y = ∑ i, e10RootCoord y i • e10Root i := (e10Root_sum_coord y).symm
    rw [hv, hy]
    change Matrix.toBilin' e10BlockGram
        (∑ i, e10RootCoord (e10Root 1 + e10Root 3) i • e10Root i)
        (∑ i, e10RootCoord (e10Root 1 + e10Root 3) i • e10Root i) ∣
      2 * Matrix.toBilin' e10BlockGram
        (∑ i, e10RootCoord (e10Root 1 + e10Root 3) i • e10Root i)
        (∑ i, e10RootCoord y i • e10Root i)
    rw [e10Root_sum_pairing, e10Root_sum_pairing, e10_reflected_root_dot]
    exact ⟨e10RootCoord (e10Root 1 + e10Root 3) ⬝ᵥ (e10Cartan *ᵥ e10RootCoord y),
      by ring⟩

/-- **`α₁ + α₃` is no nonzero integer multiple of a simple root.** -/
theorem e10_reflected_root_not_multiple :
    ¬ ∃ (k : ℤ) (i : Fin 10), k ≠ 0 ∧ e10Root 1 + e10Root 3 = k • e10Root i := by
  rintro ⟨k, i, _hk, h⟩
  have hcoord : ∀ j : Fin 10,
      e10RootCoord (e10Root 1 + e10Root 3) j = k * e10RootCoord (e10Root i) j := by
    intro j
    have h' := congrFun (congrArg e10RootCoord h) j
    simpa [e10RootCoord, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_add_distrib,
      mul_add, mul_assoc, mul_left_comm, mul_comm] using h'
  have h1 := hcoord 1
  have h3 := hcoord 3
  rw [e10_reflected_root_coord, e10RootCoord_root] at h1 h3
  simp only [Pi.add_apply] at h1 h3
  fin_cases i <;> simp_all

/-- **The counterexample in one statement.** -/
theorem e10_root_not_multiple_of_wall :
    IsReflectiveRoot e10FiniteLattice.obj (e10Root 1 + e10Root 3) ∧
      e10FiniteLattice.obj.obj.pairing (e10Root 1 + e10Root 3) (e10Root 1 + e10Root 3) < 0 ∧
      ¬ ∃ (k : ℤ) (i : Fin 10), k ≠ 0 ∧ e10Root 1 + e10Root 3 = k • e10Root i :=
  ⟨e10_reflected_root_reflective, by rw [e10_reflected_root_square]; norm_num,
    e10_reflected_root_not_multiple⟩

end LeanCategories.Lattices.Valued
