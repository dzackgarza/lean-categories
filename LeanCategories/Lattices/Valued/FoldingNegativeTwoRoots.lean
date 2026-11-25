/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingCarrierBridge

/-!
# `(−2)`-roots of `M^σ` are roots of `L` (`#116`)

The residual in `FoldingInvariantChamberOfAmbientSigns` is the class restriction `hsub`: roots of
`M^σ` that are not roots of `L`. This file removes half of it.

A vector of square `−2` in an even lattice is always reflective: the condition is
`x² ∣ 2 · ⟨x, y⟩`, and `−2` divides `2 · anything`. So a `(−2)`-root of `M^σ` is a `(−2)`-vector of
`L` — the pairing agrees on the fixed part — and therefore a root of `L`. The residual is thus
carried by the **`(−4)`-roots** alone, which is exactly AEGS Lemma 3.4's shape: type (3) has
`α² = −2` for the *ambient* root and `α^I² = −4` for the fold that is new in `T_En`
(**printed p. 12**).

* `isReflectiveRoot_of_pairing_self_eq_neg_two` — square `−2` implies reflective, in any lattice;
* `isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two` — hence a `(−2)`-root of `M^σ` is a root
  of `L`, read through the carrier bridge;
* `pairing_ne_neg_two_of_not_isReflectiveRoot` — contrapositive: the residual is `(−4)`-only.

Source: AEGS Lemma 3.4 (**printed pp. 11–12**), types (1)–(3), for the shape of the statement; the
divisibility criterion itself is AEGS §3.4 (**printed p. 10**, "a root is a vector `α` with
`α² < 0` such that `w_α(Λ) = Λ`").

## LC-09 record

`rg "isReflectiveRoot_of|square_neg_two|pairing_self_eq"` gives nothing; the existing root lemmas
(`WeylCone.lean`, `FoldingWitness.lean`) all take reflectivity as a hypothesis rather than producing
it from the square. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **A vector of square `−2` is reflective**, in any integral lattice: `−2 ∣ 2 · ⟨x, y⟩`. -/
theorem isReflectiveRoot_of_pairing_self_eq_neg_two {x : L.obj.obj.carrier}
    (h : L.obj.obj.pairing x x = -2) : IsReflectiveRoot L.obj x := by
  refine ⟨?_, ?_⟩
  · change IsRegular (L.obj.obj.pairing x x)
    rw [h]
    exact IsRegular.of_ne_zero (by norm_num)
  · intro y
    change L.obj.obj.pairing x x ∣ 2 * L.obj.obj.pairing x y
    rw [h]
    exact ⟨-(L.obj.obj.pairing x y), by ring⟩

/-- **A `(−2)`-root of `M^σ` is a root of `L`** — read through the carrier bridge. -/
theorem isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier}
    (h : (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2) :
    IsReflectiveRoot L.obj (invariantCarrierToAmbient (L := L) g ρ) := by
  refine isReflectiveRoot_of_pairing_self_eq_neg_two (L := L) ?_
  have hcoe : L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ)
      (invariantCarrierToAmbient (L := L) g ρ)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ := by
    rw [invariantCarrierToAmbient_apply]
    exact (invariantFixedLattice_pairing (L := L) g
      (show ↥(involutionFixedSubmodule g) from ρ)
      (show ↥(involutionFixedSubmodule g) from ρ)).symm
  rw [hcoe, h]

/-- **The residual is `(−4)`-only**: a root of `M^σ` that is not a root of `L` does not have square
`−2`. -/
theorem pairing_ne_neg_two_of_not_isReflectiveRoot (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier}
    (h : ¬ IsReflectiveRoot L.obj (invariantCarrierToAmbient (L := L) g ρ)) :
    (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ ≠ -2 := by
  intro h2
  exact h (isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two (L := L) g h2)

end LeanCategories.Lattices.Valued
