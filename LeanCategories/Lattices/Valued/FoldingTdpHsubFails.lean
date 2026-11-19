/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingTdpFoldEvenOnFixed
public import LeanCategories.Lattices.Valued.FoldingRootHypothesis

/-!
# The root hypothesis fails for the `T_dP` folding (`#116`)

The two preceding files gave the halves: the fold of the first `E₈` simple root is **not** a root of
`T_dP` (`FoldingTdpE8FoldNotRoot.lean`), and it **is** a root of the fixed lattice — its pairings
with
the invariant part are even and its square is `(−4)`
(`FoldingTdpFoldEvenOnFixed.lean`). What was missing was the ability to *state* the second half: the
fixed sublattice as a bundled lattice needs `Module.Projective ℤ ↥(involutionFixedSubmodule g)`,
which the repository supplied nowhere.

This file supplies it, for every submodule of a finite free `ℤ`-module:

* `submodule_projective` — `Module.Projective ℤ ↥P`, from `IsNoetherian.noetherian` (`P.FG`),
  `Module.Finite.of_fg`, and `Module.free_of_finite_type_torsion_free'`.

then supplies the concrete instance by a `show` transport across the bundled carrier, and states the
conclusion:

* `tdp_foldedWallFamily_mem` — the folded `E₈` walls are roots of `M^σ`, by AEGS Lemma 3.4's forward
  direction (`foldedWallFamily_mem_negativeReflectiveRoots`, **printed pp. 11–12**) applied to the
  published family: the roots are reflective of square `−2` and orthogonal to their images;
* `tdp_hsub_fails` — **`hsub` is false** for the `T_dP` folding: the ambient image of a root of
  `M^σ` need not be a root of `T_dP`. That is AEGS's `div(α^I) ≠ 2` (**printed p. 12**), now a
  theorem rather than a remark, and with no hypothesis left: the projectivity instance is supplied.

So the chamber theorem of item 4, though true, cannot be applied to the `T_dP` folding: its root
hypothesis — in either guise, `hsub` or `hsq` (`FoldingRootTransferEquivalence.lean`) — fails there.
An application needs the other lattice.

## LC-09 record

Repository: `rg "Module.Projective ℤ ↥(involutionFixedSubmodule"` finds only hypotheses; no
instance anywhere. `rg "submodule_projective|IsNoetherian.noetherian"` nothing. Mathlib at this pin
has no
synthesizable `Module.Finite` for a submodule, but `Module.Finite.of_fg` and
`Module.free_of_finite_type_torsion_free'` compose — that composition is the content of
`submodule_projective`, which is Mathlib glue, not new mathematics. Corpus: nothing. No port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: `T_dP = U ⊥ U(2) ⊥ E₈ ⊥ E₈` and `I = -I_En`,
  **printed pp. 12–13**; Lemma 3.4 forward and its converse, `div(α^I) ≠ 2` versus `= 2`,
  **printed p. 12**; the even 2-elementary rule, **printed p. 10**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- **Submodules of a finite free `ℤ`-module are projective.** Over a principal ideal domain a
finitely generated torsion-free module is free, and a submodule of a Noetherian module is finitely
generated; this is the composition of the two Mathlib facts. -/
theorem submodule_projective {ι : Type*} [Finite ι] (P : Submodule ℤ (ι → ℤ)) :
    Module.Projective ℤ ↥P := by
  have h : P.FG := IsNoetherian.noetherian P
  have hfin : Module.Finite ℤ ↥P := Module.Finite.of_fg h
  have hfree : Module.Free ℤ ↥P := Module.free_of_finite_type_torsion_free'
  infer_instance

/-- **The fixed sublattice of `tdpIsometry` is projective**, so that `invariantFixedLattice` can be
formed without a hypothesis. The transport across the bundled carrier is by `show`, a definitional
check: `submodule_projective` unifies at `TdpIndex → ℤ`, where `Module.IsTorsionFree` synthesizes,
but not at `tdpFiniteLattice.obj.obj.carrier`. -/
instance : Module.Projective ℤ
    ↥(involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry) :=
  show Module.Projective ℤ ↥(show Submodule ℤ (TdpIndex → ℤ) from
    involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry) from
    submodule_projective _

/-- **The folded `E₈` walls are roots of `M^σ`** — AEGS Lemma 3.4 forward (**printed pp. 11–12**) on
the published family of `FoldingDiagram.lean`. -/
theorem tdp_foldedWallFamily_mem :
    ∀ i, foldedWallFamily tdpIsometry tdpIsometry_mul_self (fun i : Fin 8 => tdpE8Root i) i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry) :=
  foldedWallFamily_mem_negativeReflectiveRoots tdpIsometry tdpIsometry_mul_self
    (fun i : Fin 8 => tdpE8Root i)
    (fun i => isReflectiveRoot_of_pairing_self_eq_neg_two (tdpE8Root_square i))
    (fun i => by rw [tdpE8Root_square i]; norm_num)
    (fun i => Or.inr (by rw [tdpIsometry_tdpE8Root i]; exact tdpE8Root_pairing_image i))

/-- **`hsub` fails for the `T_dP` folding**: the ambient image of a root of `M^σ` is not always a
root of `T_dP`. AEGS's `div(α^I) ≠ 2`, **printed p. 12**. -/
theorem tdp_hsub_fails :
    ¬ ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry),
        invariantCarrierToAmbient (L := tdpFiniteLattice) tdpIsometry ρ ∈
          negativeReflectiveRoots tdpFiniteLattice := by
  intro h
  have himg := h _ (tdp_foldedWallFamily_mem 0)
  rw [invariantCarrierToAmbient_foldedWallFamily] at himg
  exact tdpFoldedE8Root_not_mem_negativeReflectiveRoots himg

end LeanCategories.Lattices.Valued
