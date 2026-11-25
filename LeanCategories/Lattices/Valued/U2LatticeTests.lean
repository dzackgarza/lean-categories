/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.U2Lattice

/-!
# Probe: `U(2)`

The first summand of AEGS's Figure-5 lattice `(18,2,0)_1 = U(2) ⊕ E₈²` (**printed p. 11**).
The probes decide the two facts the wall set will need: the pairing formula, and evenness. The
second is a guard — `U(2)` is the doubled plane, so its squares are `4 y₀ y₁`, not even by accident.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The pairing is twice the hyperbolic one. -/
example (x y : Fin 2 → ℤ) :
    u2Lattice.obj.pairing x y = 2 * (x 0 * y 1 + x 1 * y 0) := u2_pairing x y

/-- `U(2)` is even. -/
example (y : Fin 2 → ℤ) : (2 : ℤ) ∣ u2Lattice.obj.pairing y y := u2_isEven y

end LeanCategories.Lattices.Valued
