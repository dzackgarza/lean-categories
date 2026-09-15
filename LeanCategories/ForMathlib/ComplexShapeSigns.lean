/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Tensor signs for nonnegative cochain complexes

Mathlib supplies tensor signs for chain complexes indexed by `ℕ` and for
cochain complexes indexed by `ℤ`.  The same Koszul sign convention applies to
cochain complexes indexed by `ℕ`: the vertical differential on the summand of
bidegree `(p,q)` is multiplied by `(-1)^p`.

This instance lets the existing generic total-complex machinery totalize two
`CochainComplex C ℕ` objects without introducing a source-specific totalizer.
-/

@[expose] public section

namespace ComplexShape

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard Koszul tensor signs on nonnegative cochain complexes. -/
instance tensorSignsUpNat : TensorSigns (up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

end ComplexShape
