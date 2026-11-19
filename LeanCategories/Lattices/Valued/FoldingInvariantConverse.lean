/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamber

/-!
# Lemma 3.4's converse, and what it gives the invariant chamber (`#116`)

`FoldingInvariantChamber.isChamberWithWalls_invariant` produces `IsChamberWithWalls` for `M^σ` from
an interior lattice vector and one further hypothesis, `hcomplete`: every negative reflective
root of `M^σ` is a nonzero integer multiple of a *folded wall* root. Its docstring records that this
is not AEGS Lemma 3.4's converse, and that as stated it fails for a general chamber (`E₁₀(2)`,
where a reflection of a simple root is a root that is not a multiple of any simple root).

This file adds three things, and is explicit about what each does and does not buy.

* **A sign covering implies `hcomplete`** (`hcomplete_of_sign_cover`): if every negative reflective
  root of `M^σ` is a folded wall root or its negative, then it is a nonzero integer multiple of one,
  with multiplier `±1`. That is an implication, and the direction matters: the sign covering is
  **strictly stronger** than `hcomplete`, not weaker. It is the shape a rank-one classification
  delivers (`±(e - f)` for the hyperbolic plane) and nothing more.
* **`hcomplete` is still an assumption, and the sign covering does not remove it.** Both are refuted
  by the same example in `E₁₀(2)` with its simple roots as the wall set: the reflection of `α₁` in
  `α₀` is a negative reflective root which is no integer multiple of a simple root, hence in
  particular not `±` one. Neither hypothesis is a consequence of `IsChamberWithWalls`, and this file
  therefore does **not** recover AEGS Lemma 3.8 from its chamber and maximal-dimension hypotheses.
  What the predicate's `interior_regular` field actually needs is the reflection-group statement
  that every root of `M^σ` is a `W(M^σ)`-translate of a wall root, together with the stability of
  the interior cone under `W(M^σ)`; neither is built here (no action of a reflection group on the
  chambers of `M^σ` exists in this development).
* **The non-orthogonality of a folded root to an interior point**
  (`foldedVector_pairing_ne_zero_of_mem_interior`) — the geometric content `hcomplete` stands in
  for: the fold of *any* ambient root is transverse to an interior point of the chamber, not merely
  the folds of the chosen wall set. This one is a theorem, with no classification hypothesis.

The third of these is proved in the ambient real form at a point of `M^σ ⊗ ℝ`, which is where the
argument lives: an interior point of the chamber is regular
(`IsChamberWithWalls.interior_regular`), it is fixed, and the fold pairs by `2 (z · α)`
(`realForm_pairing_folded_of_not_fixed_part`). Lifting it to the predicate for `M^σ` itself would
need an identification of `realForm M^σ` with the fixed part `M^σ ⊗ ℝ`; that bridge is not built
(`FoldingFixedPartIsometry.lean` records why), so the theorem is stated where it is proved.

## LC-09 record

Searched the repository and Mathlib for a version of Lemma 3.4's converse — "every root of the
invariant lattice is the fold of an ambient root" — and for the statement that a folded root is
non-orthogonal to an interior point: `rg "foldedVector_pairing|converse"` over
`LeanCategories/Lattices/Valued/Folding*.lean` gives only the docstring discussion in
`FoldingInvariantChamber.lean`; Mathlib's `LinearAlgebra/RootSystem/*` has no folding. The
Formalization Corpus returns no files for "folded root converse invariant lattice roots". Nothing
ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13): Lemma 3.4 with its converse, Lemma 3.8.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1, for chambers, walls and the regular locus.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-! ## A folded root is not orthogonal to an interior point -/

/-- **The fold of any root is transverse to an interior point of the chamber.** For `z` in the
interior cone of the wall set `R` that is also fixed by the involution, and any negative
reflective root `α` of the ambient lattice, the pairing of `z` with the fold `α^J` is nonzero — so
the mirror of a folded root misses the open chamber, whichever root it was folded from. -/
theorem foldedVector_pairing_ne_zero_of_mem_interior (g : OrthogonalGroup L.obj)
    {t : (realForm L).obj.carrier} {R : Set L.obj.obj.carrier}
    (hR : IsChamberWithWalls L t R)
    {z : (realForm L).obj.carrier} (hz : z ∈ rootInteriorCone L t R)
    (hzfix : z ∈ realFormFixedPart g)
    {α : L.obj.obj.carrier} (hα : α ∈ negativeReflectiveRoots L) :
    (realForm L).obj.pairing z (toRealForm L (foldedVector g α)) ≠ 0 := by
  have hreg : z ∈ weylRegularLocus L t := hR.interior_regular hz
  have hzα : (realForm L).obj.pairing z (toRealForm L α) ≠ 0 :=
    (mem_weylRegularLocus_iff (L := L) (t := t) (x := z)).mp hreg |>.2 α hα
  by_cases hfix : g.1 α = α
  · rw [foldedVector_of_fixed g hfix]
    exact hzα
  · rw [realForm_pairing_folded_of_not_fixed_part g hzfix hfix]
    exact mul_ne_zero (by norm_num) hzα

/-! ## The sign covering gives `hcomplete` -/

/-- **A sign covering implies `hcomplete`**, with multiplier `1` or `-1`.

The hypothesis is that every negative reflective root of `M^σ` is a folded wall root or its
negative. It is **strictly stronger** than `hcomplete`, not weaker: `hcomplete` allows any nonzero
integer multiple, and this theorem is the implication in that direction. (An earlier version of this
docstring said the opposite; the direction of the implication settles it.) The converse of this
theorem fails, by the same `E₁₀(2)` example that refutes `hcomplete`
(`FoldingInvariantChamber.lean`: the reflection of the simple root `α₁` in `α₀` is a root that is no
integer multiple of a simple root, hence in particular not `±` one). So the sign covering is the
shape a *rank-one* classification delivers (`±(e - f)` for the hyperbolic plane) and nothing more. -/
theorem hcomplete_of_sign_cover (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (hcover : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ρ ∈ foldedRootSet (L := L) g R ∨ -ρ ∈ foldedRootSet (L := L) g R) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ v ∈ foldedRootSet (L := L) g R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v := by
  intro ρ hρ
  rcases hcover ρ hρ with h | h
  · exact ⟨ρ, h, 1, one_ne_zero, (one_zsmul ρ).symm⟩
  · refine ⟨-ρ, h, -1, by norm_num, ?_⟩
    have key : ∀ u : involutionFixedSubmodule g,
        u = (-1 : ℤ) • (-u) := fun u => by
      rw [neg_one_zsmul]
      exact (neg_neg u).symm
    exact key ρ

/-- **The invariant chamber, from a sign covering.** `isChamberWithWalls_invariant` with its
`hcomplete` hypothesis discharged from the sign covering; the interior lattice vector (`hw`, `hwv`)
is still an input, since folding does not produce one. The sign covering is stronger than `hcomplete`
(see `hcomplete_of_sign_cover`), so this is not a weakening of the hypothesis. -/
theorem isChamberWithWalls_invariant_of_sign_cover (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSet (L := L) g R,
      0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w v)
    (hcover : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ρ ∈ foldedRootSet (L := L) g R ∨ -ρ ∈ foldedRootSet (L := L) g R) :
    IsChamberWithWalls (invariantFixedLattice (L := L) g) (toRealForm _ w)
      (foldedRootSet (L := L) g R) :=
  isChamberWithWalls_invariant g R w hw hwv (hcomplete_of_sign_cover g R hcover)

end LeanCategories.Lattices.Valued
