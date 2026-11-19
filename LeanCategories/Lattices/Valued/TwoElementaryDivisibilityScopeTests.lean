/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.TwoElementaryDivisibilityScope

/-!
# Probe: `div ∣ 2` is not free

The hyperbolic plane is even (`hyperbolicPlane_isEven`, `Standard.lean`) and unimodular, hence
2-elementary in the weakest sense. The probes below decide that the hypothesis `h2e` of
`pairing_eq_neg_two_or_neg_four_of_two_elementary` nevertheless **fails** on it, at a nonzero
vector.

That is the point the module records: AEGS's `(−2)`/`(−4)` rule (**printed p. 10**) needs
`div(α) ∣ 2` *at the root*, and that is not inherited from evenness or from 2-elementarity. It
must be checked on the lattice in question, which for `T_dP`/`T_En` is a separate unit.

Nothing here bears on the roots of `U` themselves: they are `(−2)`-vectors and the rule holds
there trivially. What is not free is its hypothesis.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The obstruction witness is a nonzero vector. -/
example :
    (show hyperbolicPlane.obj.carrier from Pi.single (0 : Fin 2) (3 : ℤ)) ≠ 0 :=
  hyperbolicPlane_single_three_ne_zero

/-- And the hypothesis fails there, so the rule does not apply to `U` as a whole. -/
example :
    ¬ ∀ x : hyperbolicPlane.obj.carrier, x ≠ 0 →
        ∃ (y₁ y₂ : hyperbolicPlane.obj.carrier) (c₁ c₂ : ℤ),
          c₁ * hyperbolicPlane.obj.pairing x y₁ +
            c₂ * hyperbolicPlane.obj.pairing x y₂ = 2 :=
  hyperbolicPlane_div_hypothesis_fails

end LeanCategories.Lattices.Valued
