/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingSignTransfer
public import LeanCategories.Lattices.Valued.Standard

/-!
# Probe for the fold transfer, on the smallest input that decides the coefficients

The lemma's content is the scalar `ε ∈ {1,2}` and the arithmetic of the doubled coefficients, so
what decides it is an instance where the coefficients are not all `1`: at the identity involution of
hyperbolic plane every wall is fixed, so `ε = 2`, and a one-term combination with coefficient `3`
must come out with coefficient `3 * 2`.

The non-fixed branch of `ε` is covered by the `by_cases`-free pair of lemmas
(`add_apply_eq_foldedVector_of_not_fixed` is proved for an arbitrary `g` and `x` with `g x ≠ x`),
not by this instance; a nontrivial involution of the plane with a projective fixed sublattice is
`FoldingRootReflection.rootReflection`, which needs the invariant lattice and so a heavier import
than this probe wants.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- The pointwise identity at the identity involution: every vector is fixed, so `x + g x = 2 • x`
and the fold is `x` itself. -/
example (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier) :
    x + (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 x
      = (2 : ℤ) • foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) x :=
  add_apply_eq_two_smul_foldedVector (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) rfl

/-- The transfer on a one-term combination with coefficient `3`: the doubled coefficient is
`3 * 2`. -/
example (x : hyperbolicPlaneFiniteLattice.obj.obj.carrier) :
    (2 : ℤ) • ((3 : ℤ) • x) = ((3 * 2 : ℤ)) •
      foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) x := by
  have hε : ∀ _ : Fin 1, x + (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 x
      = (2 : ℤ) • foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) x :=
    fun _ => add_apply_eq_two_smul_foldedVector (L := hyperbolicPlaneFiniteLattice)
      (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) rfl
  have h := two_smul_eq_sum_smul_foldedVector (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
    (R := fun _ : Fin 1 => x) (ρ := (3 : ℤ) • x) (by rfl) (fun _ => 2) hε (fun _ => 3)
    (by rw [Fin.sum_univ_one])
  simpa using h

end LeanCategories.Lattices.Valued
