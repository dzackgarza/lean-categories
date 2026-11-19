/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantConverse

/-!
# The one hypothesis the general chamber theorem reduces to (`#116`)

`FoldingInvariantChamberSignCover.chamberOf_invariant_folded_of_sign_cover` proves the invariant
chamber *is* the folded cone from an interior lattice vector and a **sign covering**: every negative
reflective root of `M^σ` is a folded wall root or its negative. That covering is stronger than
`hcomplete`, and neither follows from `IsChamberWithWalls` (`FoldingE10RootNotWall`).

This file names the hypothesis the source actually supplies and proves that it implies both.
`RootsAreFoldsOfWalls g R` — every negative reflective root of `M^σ` is the fold `α^J` of a *wall*
root `α ∈ R` — is AEGS Lemma 3.4's converse ("vice versa, all roots of `T_En` are of these three
types", **printed p. 12**) taken relative to the chamber's wall set, which is the form Lemma 3.8
(**printed p. 12**) uses: the walls of `C^J` are `α^J` for the folded roots of `G(T^dP)^J`.

* `signCover_of_rootsAreFoldsOfWalls` — it implies the sign covering;
* `hcomplete_of_rootsAreFoldsOfWalls` — hence `hcomplete`.

The predicate is stated over the invariant lattice's own elements (`v : M^σ`), which is what makes
it *writable*: `negativeReflectiveRoots` of the lattice and `foldedVector` in the ambient carrier
are on the two sides of the carrier identification, and the element `v` is the one object available
on both.

The predicate itself stays unproved: discharging it needs an action of the reflection group on the
chambers of `M^σ`, which this development does not have.

## LC-09 record

`rg "RootsAreFoldsOfWalls|isChamberWithWalls_invariant_of_sign_cover"` gives the predicate's absence
and the sign-cover route; `rg "isReflectiveRoot_of_isometry"` gives `WeylCone.lean:172` — the tool a
proof of the predicate would need, plus a nondegeneracy hypothesis on `M^σ` that the repository does
not supply. Nothing ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8: Lemma 3.4 and its
  converse (**printed p. 12**), Definition 3.7 (**printed p. 12**), Lemma 3.8 (**printed p. 12**).
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **AEGS Lemma 3.4's converse, relative to a wall set** (printed p. 12), *up to sign*: every
negative reflective root of `M^σ` is the fold of a wall root or its negative. The sign is not a
convenience — a chamber's wall set contains one of `±α`, not both, so `-α^J` is a root that is not
itself a fold (this is why the hyperbolic plane's chamber satisfies this and not the unsigned
version). -/
def RootsAreFoldsOfWalls (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier) : Prop :=
  ∀ v : involutionFixedSubmodule g,
    (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) ∈
        negativeReflectiveRoots (invariantFixedLattice (L := L) g) →
      ∃ α ∈ R, (v : L.obj.obj.carrier) = foldedVector g α ∨
        (v : L.obj.obj.carrier) = -foldedVector g α

/-- **The negation of a root is a root.** The square is unchanged and the divisibility is the one at
`-x`; this is what lets the sign in `RootsAreFoldsOfWalls` produce the second disjunct of the
covering. -/
theorem neg_mem_negativeReflectiveRoots (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] {v : involutionFixedSubmodule g}
    (hv : (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g)) :
    ((-v : involutionFixedSubmodule g) :
        (invariantFixedLattice (L := L) g).obj.obj.carrier) ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g) := by
  have hsq : (invariantFixedLattice (L := L) g).obj.obj.pairing
      ((-v : involutionFixedSubmodule g) : (invariantFixedLattice (L := L) g).obj.obj.carrier)
      ((-v : involutionFixedSubmodule g) : (invariantFixedLattice (L := L) g).obj.obj.carrier)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing
        (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
        (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) := by
    have h1 : (invariantFixedLattice (L := L) g).obj.obj.bilinMap
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier)
        = -(invariantFixedLattice (L := L) g).obj.obj.bilinMap
          (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) := map_neg _ _
    have h2 : (invariantFixedLattice (L := L) g).obj.obj.bilinMap
        (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier)
        = -((invariantFixedLattice (L := L) g).obj.obj.bilinMap
          (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
          (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)) := map_neg _ _
    change (invariantFixedLattice (L := L) g).obj.obj.bilinMap _ _
      = (invariantFixedLattice (L := L) g).obj.obj.bilinMap _ _
    calc (invariantFixedLattice (L := L) g).obj.obj.bilinMap
          ((-v : involutionFixedSubmodule g) :
            (invariantFixedLattice (L := L) g).obj.obj.carrier)
          ((-v : involutionFixedSubmodule g) :
            (invariantFixedLattice (L := L) g).obj.obj.carrier)
        = (-(invariantFixedLattice (L := L) g).obj.obj.bilinMap
            (v : (invariantFixedLattice (L := L) g).obj.obj.carrier))
            ((-v : involutionFixedSubmodule g) :
              (invariantFixedLattice (L := L) g).obj.obj.carrier) := by rw [h1]
      _ = -((invariantFixedLattice (L := L) g).obj.obj.bilinMap
            (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
            ((-v : involutionFixedSubmodule g) :
              (invariantFixedLattice (L := L) g).obj.obj.carrier)) := LinearMap.neg_apply _ _
      _ = -(-((invariantFixedLattice (L := L) g).obj.obj.bilinMap
            (v : (invariantFixedLattice (L := L) g).obj.obj.carrier)
            (v : (invariantFixedLattice (L := L) g).obj.obj.carrier))) := by rw [h2]
      _ = _ := neg_neg _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change IsRegular ((invariantFixedLattice (L := L) g).obj.obj.pairing
      ((-v : involutionFixedSubmodule g) :
        (invariantFixedLattice (L := L) g).obj.obj.carrier) _)
    rw [hsq]
    exact hv.1.regular
  · intro y
    change (invariantFixedLattice (L := L) g).obj.obj.pairing
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier)
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier) ∣
      2 * (invariantFixedLattice (L := L) g).obj.obj.pairing
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier) y
    rw [hsq]
    have hd := hv.1.dvd_two_mul y
    have hb : (invariantFixedLattice (L := L) g).obj.obj.bilinMap
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier)
        = -(invariantFixedLattice (L := L) g).obj.obj.bilinMap
          (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) := map_neg _ _
    have hneg2 : (invariantFixedLattice (L := L) g).obj.obj.pairing
        ((-v : involutionFixedSubmodule g) :
          (invariantFixedLattice (L := L) g).obj.obj.carrier) y
        = -((invariantFixedLattice (L := L) g).obj.obj.pairing
          (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) y) := by
      change (invariantFixedLattice (L := L) g).obj.obj.bilinMap _ y = _
      rw [hb]
      rfl
    rw [hneg2, mul_neg, dvd_neg]
    exact hd
  · rw [hsq]
    exact hv.2

/-- **It implies the sign covering.** A root that is a folded wall root up to sign lies in the
folded
root set or its negative does, by Definition 3.7's filter and `neg_mem_negativeReflectiveRoots`. -/
theorem signCover_of_rootsAreFoldsOfWalls (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (h : RootsAreFoldsOfWalls (L := L) g R) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ρ ∈ foldedRootSet (L := L) g R ∨ -ρ ∈ foldedRootSet (L := L) g R := by
  intro ρ hρ
  set v : involutionFixedSubmodule g := ρ with hv
  have hρv : (v : (invariantFixedLattice (L := L) g).obj.obj.carrier) ∈
      negativeReflectiveRoots (invariantFixedLattice (L := L) g) := by
    rw [hv]; exact hρ
  obtain ⟨α, hα, hfold | hfold⟩ := h v hρv
  · -- `v` is a fold of a wall root: build its membership directly
    have hneg : L.obj.obj.pairing (foldedVector g α) (foldedVector g α) < 0 := by
      rw [← hfold]
      simpa [invariantFixedLattice_pairing] using hρv.2
    have hdvd : ∀ x : involutionFixedSubmodule g,
        L.obj.obj.pairing (foldedVector g α) (foldedVector g α) ∣
          2 * L.obj.obj.pairing (foldedVector g α) (x : L.obj.obj.carrier) := by
      intro x
      rw [← hfold]
      have hx := hρv.1.dvd_two_mul x
      change L.obj.obj.pairing (v : L.obj.obj.carrier) (v : L.obj.obj.carrier) ∣
        2 * L.obj.obj.pairing (v : L.obj.obj.carrier) (x : L.obj.obj.carrier) at hx
      exact hx
    have hmem : v ∈ foldedRootSet (L := L) g R :=
      (mem_foldedRootSet_iff (L := L) g R v).mpr
        ⟨⟨α, hα, hfold.symm⟩, hfold ▸ hneg, fun x => hfold ▸ hdvd x⟩
    exact Or.inl hmem
  · -- `v = -(α^J)`: apply the same argument to `-v`
    have hρneg := neg_mem_negativeReflectiveRoots (L := L) g hρv
    have hfold' : ((-v : involutionFixedSubmodule g) : L.obj.obj.carrier)
        = foldedVector g α := by
      change -(v : L.obj.obj.carrier) = foldedVector g α
      rw [hfold, neg_neg]
    have hneg : L.obj.obj.pairing (foldedVector g α) (foldedVector g α) < 0 := by
      rw [← hfold']
      simpa [invariantFixedLattice_pairing] using hρneg.2
    have hdvd : ∀ x : involutionFixedSubmodule g,
        L.obj.obj.pairing (foldedVector g α) (foldedVector g α) ∣
          2 * L.obj.obj.pairing (foldedVector g α) (x : L.obj.obj.carrier) := by
      intro x
      rw [← hfold']
      have hx := hρneg.1.dvd_two_mul x
      change L.obj.obj.pairing ((-v : involutionFixedSubmodule g) : L.obj.obj.carrier)
          ((-v : involutionFixedSubmodule g) : L.obj.obj.carrier) ∣
        2 * L.obj.obj.pairing ((-v : involutionFixedSubmodule g) : L.obj.obj.carrier)
          (x : L.obj.obj.carrier) at hx
      exact hx
    have hmem : (-v : involutionFixedSubmodule g) ∈ foldedRootSet (L := L) g R :=
      (mem_foldedRootSet_iff (L := L) g R (-v)).mpr
        ⟨⟨α, hα, hfold'.symm⟩, hfold' ▸ hneg, fun x => hfold' ▸ hdvd x⟩
    exact Or.inr hmem

/-- **Hence it implies `hcomplete`**, composing with `hcomplete_of_sign_cover`. -/
theorem hcomplete_of_rootsAreFoldsOfWalls (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (h : RootsAreFoldsOfWalls (L := L) g R) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ∃ v ∈ foldedRootSet (L := L) g R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v :=
  hcomplete_of_sign_cover (L := L) g R (signCover_of_rootsAreFoldsOfWalls (L := L) g R h)

end LeanCategories.Lattices.Valued
