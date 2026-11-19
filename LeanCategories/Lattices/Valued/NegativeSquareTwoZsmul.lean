/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.WeylCone

/-!
# A negative-square lattice vector is not 2-torsion (`#116`)

The doubled form of the folded chamber theorem
(`FoldingInvariantChamberOfTwoSmulSigns.isChamberWithWalls_invariant_of_two_smul_folded_signs`)
carries `2 • ρ ≠ 0` as a hypothesis, because the development has no `NoZeroSMulDivisors` instance
for a general lattice carrier (only for model carriers such as `CobleLattice` and
`CuspWorkedInstance`, where the carrier is `Fin n → ℤ`). This file discharges it for the case that
matters: a root has negative square, and a negative-square vector cannot be 2-torsion.

The argument goes through the real form, where the scalar laws are the ordinary `ℝ`-module ones:
if `2 • x = 0` then `toRealForm` of it is zero, hence `2 • toRealForm x = 0`, hence
`toRealForm x = 0` (ℝ is a field), hence the real pairing of `x` with itself is `0`, which is the
cast of `⟨x, x⟩` — a contradiction with `⟨x, x⟩ < 0`. At the lattice level the corresponding steps
(`pairing (2 • x) y = 2 * pairing x y`) do not fire: the carrier's scalar action is `ZSMul.toSMul`,
not `DistribSMul`, so the proofs must be done after `toRealForm`.

* `two_zsmul_ne_zero_of_pairing_neg` — `⟨x, x⟩ < 0` implies `2 • x ≠ 0`.

No source to cite: this is bookkeeping about integral lattices, not a statement of the paper. It is
what makes AEGS Lemma 3.8's chamber statement (**printed p. 12**) consumable over `ℤ`.

## LC-09 record

`rg "two_zsmul|zsmul_ne_zero|NoZeroSMulDivisors"` over the repository gives instances only for the
model carriers (`CobleLattice.lean:344`, `CuspWorkedInstance.lean:62`), never a general one, and no
lemma of this shape; Mathlib's `smul_eq_zero` needs `NoZeroSMulDivisors`, which is what is missing.
Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **A vector of negative square is not 2-torsion.** Equivalently, `2 • x = 0` forces `⟨x, x⟩ = 0`,
which contradicts negative square. The proof is carried out in the real form, where the scalar laws
apply. -/
theorem two_zsmul_ne_zero_of_pairing_neg {x : L.obj.obj.carrier}
    (h : L.obj.obj.pairing x x < 0) : (2 : ℤ) • x ≠ 0 := by
  intro h0
  have h1 : toRealForm L ((2 : ℤ) • x) = 0 := by
    rw [h0]
    change (1 : ℝ) ⊗ₜ[ℤ] (0 : L.obj.obj.carrier) = 0
    rw [TensorProduct.tmul_zero]
  have hzs : toRealForm L ((2 : ℤ) • x) = (2 : ℝ) • toRealForm L x := by
    change (1 : ℝ) ⊗ₜ[ℤ] ((2 : ℤ) • x) = (2 : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] x)
    rw [← Int.cast_smul_eq_zsmul ℤ (2 : ℤ) x]
    rw [TensorProduct.tmul_smul]
    exact (Int.cast_smul_eq_zsmul ℝ (2 : ℤ) ((1 : ℝ) ⊗ₜ[ℤ] x)).symm
  rw [hzs] at h1
  have h2 : toRealForm L x = 0 := (smul_eq_zero.mp h1).resolve_left (by norm_num)
  have h3 : ((L.obj.obj.pairing x x : ℤ) : ℝ) = 0 := by
    rw [← realFormPairing_toRealForm]
    rw [h2]
    simp
  have h4 : L.obj.obj.pairing x x = 0 := by exact_mod_cast h3
  exact absurd h4 (ne_of_lt h)

end LeanCategories.Lattices.Valued
