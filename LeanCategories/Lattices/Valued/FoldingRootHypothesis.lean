/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingFoldNonRoot
public import LeanCategories.Lattices.Valued.FoldingChamberOfSquareCriterion

/-!
# `hroot`, derived instead of assumed (`#116`)

`isChamberWithWalls_invariant_of_square_criterion` takes `hroot`: every fold of a wall root is a
root of `M^σ`. `FoldingFoldOfRoot` and `FoldingFoldNonRoot` supply the two halves of the case
analysis; this file assembles them.

For a wall root `α` that is reflective and of negative square, there are two cases:

* **fixed** (`gα = α`): the fold is `α` itself, and reflectivity passes from `L` to `M^σ` because
  `M^σ ⊆ L` — that is the easy direction of AEGS Lemma 3.4 (**printed p. 12**), and
  `isReflectiveRoot_of_mem_of_isReflectiveRoot` states it;
* **not fixed, orthogonal** (`α ⊥ gα`): the fold is a root by
  `isReflectiveRoot_foldedVector_of_orthogonal`, and its square is `2α² < 0`.

So under "every wall root is reflective, of negative square, and either fixed or orthogonal to its
image", `hroot` holds. The hypothesis that remains is the one the paper settles by arithmetic: a
non-fixed, non-orthogonal wall root of square `−4` folds to a vector that is *not* a root
(`foldedWallFamily_not_mem_negativeReflectiveRoots`), so such a wall cannot occur in a wall set
whose folds are all supposed to be roots.

## LC-09 record

`rg "isReflectiveRoot_of_mem|hroot.*derived|mem_negativeReflectiveRoots"` gives the predicate and
the chamber theorems that take `hroot`, but nothing that derives it. Nothing ported.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **Reflectivity passes from `L` to `M^σ` for a fixed vector** — the easy direction of AEGS Lemma
3.4 (printed p. 12). The pairing of `M^σ` is the ambient pairing, and `M^σ ⊆ L`, so the divisibility
condition restricts. -/
theorem isReflectiveRoot_of_mem_of_isReflectiveRoot (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {ρ : involutionFixedSubmodule g} (h : IsReflectiveRoot L.obj (ρ : L.obj.obj.carrier)) :
    IsReflectiveRoot (invariantFixedLattice (L := L) g).obj ρ := by
  have hsq : (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ
      = L.obj.obj.pairing (ρ : L.obj.obj.carrier) (ρ : L.obj.obj.carrier) := rfl
  refine ⟨?_, ?_⟩
  · change IsRegular ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ)
    rw [hsq]
    exact h.regular
  · intro x
    change (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ ∣
      2 * (invariantFixedLattice (L := L) g).obj.obj.pairing ρ x
    rw [hsq]
    have hx : (invariantFixedLattice (L := L) g).obj.obj.pairing ρ x
        = L.obj.obj.pairing (ρ : L.obj.obj.carrier)
          ((show ↥(involutionFixedSubmodule g) from x) : L.obj.obj.carrier) := rfl
    rw [hx]
    exact h.dvd_two_mul _

/-- **`hroot`, derived.** A wall family of reflective roots of negative square, each either fixed or
orthogonal to its image, folds into the negative reflective roots of `M^σ`. -/
theorem foldedWallFamily_mem_negativeReflectiveRoots (g : OrthogonalGroup L.obj) (hg : g * g = 1)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    {n : ℕ} (R : Fin n → L.obj.obj.carrier)
    (hR : ∀ i, IsReflectiveRoot L.obj (R i))
    (hneg : ∀ i, L.obj.obj.pairing (R i) (R i) < 0)
    (hcase : ∀ i, g.1 (R i) = R i ∨ L.obj.obj.pairing (R i) (g.1 (R i)) = 0) :
    ∀ i, foldedWallFamily (L := L) g hg R i ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g) := by
  intro i
  by_cases hfix : g.1 (R i) = R i
  · have hfold : foldedWallFamily (L := L) g hg R i
        = (⟨R i, (mem_involutionFixedSubmodule_iff g).mpr hfix⟩ : involutionFixedSubmodule g) :=
      Subtype.ext (foldedVector_of_fixed g hfix)
    rw [hfold]
    refine ⟨isReflectiveRoot_of_mem_of_isReflectiveRoot (L := L) g (hR i), ?_⟩
    rw [invariantFixedLattice_pairing]
    exact hneg i
  · have horth : L.obj.obj.pairing (R i) (g.1 (R i)) = 0 := by
      rcases hcase i with h | h
      · exact absurd h hfix
      · exact h
    have hfold : foldedWallFamily (L := L) g hg R i
        = (⟨foldedVector g (R i), foldedVector_mem_fixed g hg (R i)⟩ :
            involutionFixedSubmodule g) := Subtype.ext rfl
    rw [hfold]
    refine ⟨isReflectiveRoot_foldedVector_of_orthogonal (L := L) g hg (hR i) horth hfix, ?_⟩
    rw [invariantFixedLattice_pairing, pairing_folded_self_of_not_fixed g hfix, horth, mul_zero,
      add_zero]
    have := hneg i
    linarith

end LeanCategories.Lattices.Valued
