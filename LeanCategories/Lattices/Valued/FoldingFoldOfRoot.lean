/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamber

/-!
# A fold of an orthogonal root is a root of `M^σ` (`#116`)

`isChamberWithWalls_invariant_of_square_criterion` takes `hroot`: every fold of a wall root is a
root of `M^σ`. Folding's own definition filters those folds (`foldedRootSet`), so the hypothesis has
so far been carried rather than derived. This file derives it in the case the paper singles out.

AEGS Lemma 3.4's forward direction (**printed pp. 11–12**) says that a fold of a root is a root,
with a case analysis on the type. Type (3) is the case where `α` is not fixed and `α · I(α) = 0`;
the fold then has square `2α² = −4` and is a *new* root of `T_En`. The argument is two lines of
bilinearity, and it is abstract:

* `⟨α + gα, α + gα⟩ = 2α² + 2⟨α, gα⟩ = 2α²` when `α ⊥ gα`;
* for `x ∈ M^σ`, `⟨α + gα, x⟩ = 2⟨α, x⟩`;
* so `(α^J)² = 2α²` divides `2⟨α^J, x⟩ = 4⟨α, x⟩` exactly when `α²` divides `2⟨α, x⟩` — which is
  what `α` being a root says.

* `isReflectiveRoot_foldedVector_of_orthogonal` — the type (3) case.

What this does **not** cover is the general fold of a root with `α · gα ≠ 0`; there the identity
`(α^J)² = 2α² + 2α·gα` need not divide the doubled pairings, and the paper's other two types are the
fixed cases (types (1) and (2)), where the fold is `α` itself and reflectivity transfers from `L`
because `M^σ ⊆ L` (`FoldingNegativeTwoRoots` covers square `−2`; the fixed case at square `−4` is
`isReflectiveRoot_iff_two_dvd_pairing`).

## LC-09 record

`rg "isReflectiveRoot_foldedVector|foldOfRoot|folded.*reflective"` gives nothing: the repository has
the *identity* `α_I² = 2α² + 2α·Iα` (`pairing_folded_self_of_not_fixed`) and the pairing law
`⟨x, α^J⟩ = 2⟨x, α⟩` for fixed `x` (`pairing_fixed_folded_of_not_fixed`), but never combines them
into reflectivity. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **AEGS Lemma 3.4, type (3): a fold of an orthogonal root is a root of `M^σ`.**

If `α` is a reflective root of `L`, is not fixed by `g`, and `α ⊥ gα`, then `α^J = α + gα` is a
reflective root of the invariant lattice. The invariant lattice's pairing *is* the ambient pairing
on the fixed part (by `rfl`), which is why the two ambient identities transfer without a
transport. -/
theorem isReflectiveRoot_foldedVector_of_orthogonal (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {α : L.obj.obj.carrier} (hα : IsReflectiveRoot L.obj α)
    (horth : L.obj.obj.pairing α (g.1 α) = 0) (hne : g.1 α ≠ α) :
    IsReflectiveRoot (invariantFixedLattice g).obj
      (⟨foldedVector g α, foldedVector_mem_fixed g hg α⟩ : involutionFixedSubmodule g) := by
  have hsq : L.obj.obj.pairing (foldedVector g α) (foldedVector g α)
      = 2 * L.obj.obj.pairing α α := by
    rw [pairing_folded_self_of_not_fixed g hne, horth, mul_zero, add_zero]
  have hp : L.obj.obj.pairing α α ≠ 0 := fun h0 => IsRegular.ne_zero hα.regular h0
  -- the folded vector doubles the pairing with a fixed vector, in `pairing` form
  have hpair : ∀ y : L.obj.obj.carrier, y ∈ involutionFixedSubmodule g →
      L.obj.obj.pairing (foldedVector g α) y = 2 * L.obj.obj.pairing α y := by
    intro y hy
    have hy' : g.1 y = y := (mem_involutionFixedSubmodule_iff g).mp hy
    have hgy : L.obj.obj.pairing (g.1 α) y = L.obj.obj.pairing α y := by
      calc L.obj.obj.pairing (g.1 α) y
          = L.obj.obj.pairing (g.1 α) (g.1 y) := by rw [hy']
        _ = L.obj.obj.pairing α y := g.property α y
    rw [foldedVector_of_not_fixed g hne, BilinModuleCat.pairing_add_left, hgy]
    ring
  refine ⟨?_, ?_⟩
  · change IsRegular (L.obj.obj.pairing (foldedVector g α) (foldedVector g α))
    rw [hsq]
    exact IsRegular.of_ne_zero (mul_ne_zero (by norm_num) hp)
  · intro x
    change L.obj.obj.pairing (foldedVector g α) (foldedVector g α) ∣
      2 * L.obj.obj.pairing (foldedVector g α)
        ((show ↥(involutionFixedSubmodule g) from x) : L.obj.obj.carrier)
    rw [hsq, hpair _ (show ↥(involutionFixedSubmodule g) from x).2]
    have hd : L.obj.obj.pairing α α ∣ 2 * L.obj.obj.pairing α
        ((show ↥(involutionFixedSubmodule g) from x) : L.obj.obj.carrier) :=
      hα.dvd_two_mul _
    obtain ⟨k, hk⟩ := hd
    exact ⟨k, by rw [hk]; ring⟩

end LeanCategories.Lattices.Valued
