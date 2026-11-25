/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingSignTransferLattice
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the fold transfer at the invariant lattice's carrier

The lemma's content is the coercion from the ambient carrier to `M^σ`'s, so what decides it is an
instance where the two sides are *not* syntactically equal: at the plane's identity involution the
fold `uRoot^g` is `uRoot` only propositionally, so the identity

`2 • uRootFixed = Σ (1 * 2) • foldedWallFamily … 0`

has to be proved through the coercion rather than by `rfl`. A wrong coercion or a dropped
coefficient
would fail it.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The transfer at `M^σ`'s carrier, on the plane at the identity involution. -/
example : (2 : ℤ) • uRootFixed =
    ∑ i : Fin 1, (((fun _ : Fin 1 => (1 : ℤ)) i * 2)) •
      foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) (one_mul 1)
        (fun _ : Fin 1 => uRoot) i := by
  refine two_smul_eq_sum_smul_foldedWallFamily (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (ρ := uRootFixed) (ε := fun _ => 2) ?_
    (c := fun _ => 1) ?_
  · intro i
    exact add_apply_eq_two_smul_foldedVector (L := hyperbolicPlaneFiniteLattice)
      (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) rfl
  · rw [Fin.sum_univ_one]
    exact (one_zsmul uRoot).symm

end LeanCategories.Lattices.Valued
