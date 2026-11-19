/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingNegativeTwoRoots

/-!
# The `(−4)` residual: a `(−4)`-vector is a root exactly when its pairings are even (`#116`)

After `FoldingNegativeTwoRoots`, the roots of `M^σ` that are not roots of `L` have square `−4`. This
file locates them exactly.

For `x` with `x² = −4`, the reflection condition `x² ∣ 2⟨x, y⟩` is `−4 ∣ 2⟨x, y⟩`, which holds
exactly when `⟨x, y⟩` is even. So on square `−4`:

  `IsReflectiveRoot L x ↔ ∀ y, 2 ∣ ⟨x, y⟩`,

i.e. the `(−4)`-roots of `L` are the `(−4)`-vectors of `2L^∨`. That is the boundary of the residual:
a `(−4)`-root of `M^σ` is a root of `L` iff it lies in `2L^∨`, and the type (3) roots are exactly
those that do not.

This is the shape AEGS give on **printed pp. 11–12**: Lemma 3.4's type (3) is characterised there by
`div(α^I) ≠ 2` in `T_dP` while `div(α^I) = 2` in `T_En` — the same statement in divisibility
language — and §3.4 (**printed p. 10**) is where roots are defined by the divisibility condition.
The paper then decides *which* `(−4)`-vectors occur by Namikawa's orbit classification; that
classification is what this file does **not** supply, and it is the remaining gap.

* `isReflectiveRoot_iff_two_dvd_pairing` — the criterion on square `−4`;
* `isReflectiveRoot_invariantToAmbient_iff_two_dvd_pairing` — the same at `M^σ`, through the bridge.

## LC-09 record

`rg "two_dvd_pairing|neg_four|square_neg_four"` gives nothing in the repository;
`LinearMap.IsReflective` in Mathlib has `dvd_two_mul` but no case analysis on the square. Nothing
ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **On square `−4`, reflectivity is evenness of all pairings.** `−4 ∣ 2⟨x,y⟩` holds exactly when
`⟨x, y⟩` is even, so the `(−4)`-roots of `L` are its `(−4)`-vectors in `2L^∨`. -/
theorem isReflectiveRoot_iff_two_dvd_pairing {x : L.obj.obj.carrier}
    (h : L.obj.obj.pairing x x = -4) :
    IsReflectiveRoot L.obj x ↔ ∀ y, (2 : ℤ) ∣ L.obj.obj.pairing x y := by
  constructor
  · intro hx y
    have hd := hx.dvd_two_mul y
    change L.obj.obj.pairing x x ∣ 2 * L.obj.obj.pairing x y at hd
    rw [h] at hd
    obtain ⟨k, hk⟩ := hd
    exact ⟨-k, by linarith⟩
  · intro h2
    refine ⟨?_, ?_⟩
    · change IsRegular (L.obj.obj.pairing x x)
      rw [h]
      exact IsRegular.of_ne_zero (by norm_num)
    · intro y
      change L.obj.obj.pairing x x ∣ 2 * L.obj.obj.pairing x y
      rw [h]
      obtain ⟨k, hk⟩ := h2 y
      exact ⟨-k, by rw [hk]; ring⟩

/-- **The residual, exactly**: a `(−4)`-root of `M^σ` is a root of `L` iff all its ambient pairings
are even. The roots where this fails are AEGS Lemma 3.4's type (3). -/
theorem isReflectiveRoot_invariantToAmbient_iff_two_dvd_pairing (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier}
    (h : (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4) :
    IsReflectiveRoot L.obj (invariantToAmbient (L := L) g ρ)
      ↔ ∀ y : L.obj.obj.carrier,
          (2 : ℤ) ∣ L.obj.obj.pairing (invariantToAmbient (L := L) g ρ) y := by
  refine isReflectiveRoot_iff_two_dvd_pairing (L := L) ?_
  have hcoe : L.obj.obj.pairing (invariantToAmbient (L := L) g ρ)
      (invariantToAmbient (L := L) g ρ)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ := by
    rw [invariantToAmbient_apply]
    exact (invariantFixedLattice_pairing (L := L) g
      (show ↥(involutionFixedSubmodule g) from ρ)
      (show ↥(involutionFixedSubmodule g) from ρ)).symm
  rw [hcoe, h]

end LeanCategories.Lattices.Valued
