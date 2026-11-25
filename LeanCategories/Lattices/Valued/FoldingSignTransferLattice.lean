/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamberOfSigns
public import LeanCategories.Lattices.Valued.FoldingSignTransfer

/-!
# The fold transfer at the invariant lattice's carrier (`#116`)

`FoldingSignTransfer.two_smul_eq_sum_smul_foldedVector` states the fold transfer at the *ambient*
carrier. The chamber theorem

`FoldingInvariantChamberOfTwoSmulSigns.isChamberWithWalls_invariant_of_two_smul_folded_signs`
consumes its one-sign hypothesis at the *invariant lattice's* carrier, with the summands
`foldedWallFamily g hg R i`. The two carriers are definitionally the same — the invariant lattice is
`formedSublattice L.obj (involutionFixedSubmodule g)`, whose carrier is
`↥(involutionFixedSubmodule g)` — but not syntactically, which is the carrier obstruction of
`results/issue-116-report.md`.

This file restates the transfer in the form the chamber theorem takes, so the two compose without a
transport at the point of use. The proof is the coercion of the ambient statement along the
submodule embedding:
`↑(2 • ρ) = 2 • ↑ρ`, and `↑(Σ …) = Σ … • ↑(foldedWallFamily …) = Σ … • foldedVector …` by
`Submodule.coe_sum` and the definition of `foldedWallFamily`.

* `two_smul_eq_sum_smul_foldedWallFamily` — the transfer at `M^σ`'s carrier.

Source: AEGS Definition 3.3 (printed p. 11) for the fold, and Lemma 3.4's proof (printed p. 12) for
the
`ε`; the statement is bookkeeping, not a paper claim.

## LC-09 record

`rg "foldedWallFamily"` gives `FoldingInvariantChamberOfSigns` (the definition and the chamber
theorem) and nothing else; the transfer lives only at the ambient carrier. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The fold transfer at the invariant lattice's carrier.**

If `ρ ∈ M^σ` and `ρ = Σ cᵢ Rᵢ` in `M^σ`'s ambient lattice, and `ε` is a family with
`Rᵢ + gRᵢ = εᵢ • Rᵢ^g`, then `2ρ = Σ (cᵢ εᵢ) • Rᵢ^g` **as an identity in `M^σ`** — the form the
folded chamber theorem's one-sign hypothesis is stated in. -/
theorem two_smul_eq_sum_smul_foldedWallFamily (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    {n : ℕ} {R : Fin n → L.obj.obj.carrier} {ρ : involutionFixedSubmodule g}
    (ε : Fin n → ℤ) (hε : ∀ i, R i + g.1 (R i) = ε i • foldedVector g (R i))
    (c : Fin n → ℤ) (hc : (ρ : L.obj.obj.carrier) = ∑ i, c i • R i) :
    (2 : ℤ) • ρ = ∑ i, (c i * ε i) • foldedWallFamily (L := L) g hg R i := by
  have hfix : g.1 (ρ : L.obj.obj.carrier) = ρ := (mem_involutionFixedSubmodule_iff g).mp ρ.2
  have hamb := two_smul_eq_sum_smul_foldedVector (L := L) g hfix ε hε c hc
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change (2 : ℤ) • (ρ : L.obj.obj.carrier) = ∑ i, (c i * ε i) • foldedVector g (R i)
  exact hamb

end LeanCategories.Lattices.Valued
