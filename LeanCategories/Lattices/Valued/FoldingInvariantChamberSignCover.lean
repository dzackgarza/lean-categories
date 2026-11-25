/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantConverse

/-!
# The invariant chamber is the folded cone, from the sign covering (`#116`)

`FoldingInvariantChamber.chamberOf_invariant_folded` identifies the chamber of the invariant lattice
with the cone cut out by Definition 3.7's folded root set — but it takes `hcomplete`.
`isChamberWithWalls_invariant_of_sign_cover` takes a sign covering instead. This file carries the
identification across to that hypothesis. **It does not thereby recover AEGS Lemma 3.8 in general:**
the sign covering is *stronger* than `hcomplete` (multiplier `±1`), not weaker, and it is refuted by
the same `E₁₀(2)` example recorded in `FoldingInvariantChamber.lean`. What the two theorems here say
is conditional on a hypothesis that a rank-one classification supplies and that a general chamber
does not.

* `rootInteriorCone_invariant_self` — the interior vector `w` of the involution's lattice lies in
  the interior cone of the folded wall set, which is what `IsChamberWithWalls.chamberOf_eq` needs to
  identify the chamber at `w`;
* `chamberOf_invariant_folded_of_sign_cover` — at that point, the chamber of `M^σ` *is* the folded
  cone, from the sign covering, the interior lattice vector and the signature hypothesis `hpos`.

## LC-09 record

Searched for the statement that an interior vector of the chamber lies in the interior cone of the
wall set (needed to apply `IsChamberWithWalls.chamberOf_eq` at the lattice point):
`rg "chamberOf_eq\|mem_chamberOf"` over `LeanCategories/Lattices/Valued/WeylChambers.lean` gives
`IsChamberWithWalls.chamberOf_eq` (interior cone *is* the chamber of any of its points) and
`mem_chamberOf` (a regular point lies in its chamber) — neither states that the vector defining the
cone is itself in it, which is `mem_rootInteriorCone_iff` plus the hypotheses. Mathlib has no
chamber
theory for indefinite lattices. The Formalization Corpus returns no files. Nothing ported.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13): Lemma 3.8's chamber `C^J`.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- **The interior lattice vector lies in the interior cone of the folded wall set.** With `w² > 0`
and `w · α^J > 0` for every folded wall root, `w` is an interior point of the cone, which is what
identifies the chamber at `w` with that cone. -/
theorem rootInteriorCone_invariant_self (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSet (L := L) g R,
      0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w v) :
    toRealForm (invariantFixedLattice (L := L) g) w ∈
      rootInteriorCone (invariantFixedLattice (L := L) g)
        (toRealForm (invariantFixedLattice (L := L) g) w) (foldedRootSet (L := L) g R) := by
  have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g)
      (toRealForm (invariantFixedLattice (L := L) g) w) := by
    rw [realFormQuadratic_apply, invariant_pairing_toRealForm]
    exact_mod_cast hw
  refine (mem_rootInteriorCone_iff (L := invariantFixedLattice (L := L) g)
    (t := toRealForm (invariantFixedLattice (L := L) g) w)).mpr ⟨⟨hQ, ?_⟩, ?_⟩
  · rw [← realFormPairing_eq_associated (L := invariantFixedLattice (L := L) g),
      ← realFormQuadratic_apply (invariantFixedLattice (L := L) g)
        (toRealForm (invariantFixedLattice (L := L) g) w)]
    exact hQ
  · intro v hv
    rw [realFormPairing_toRealForm (L := invariantFixedLattice (L := L) g) w v]
    exact_mod_cast hwv v hv

/-- **The chamber of the invariant lattice is the folded cone**, from the sign covering. The
hypotheses are the interior lattice vector (`hw`, `hwv`), the sign covering and the signature
condition `hpos`.

The sign covering is *stronger* than `hcomplete` (it pins the multiplier to `±1`) and is refuted by
the same `E₁₀(2)` example, so this theorem is a conditional statement about chambers whose root
classification is rank-one-like, not a derivation of AEGS Lemma 3.8 from the chamber hypotheses. -/
theorem chamberOf_invariant_folded_of_sign_cover (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)] (R : Set L.obj.obj.carrier)
    (w : involutionFixedSubmodule g)
    (hw : 0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSet (L := L) g R,
      0 < (invariantFixedLattice (L := L) g).obj.obj.pairing w v)
    (hcover : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      ρ ∈ foldedRootSet (L := L) g R ∨ -ρ ∈ foldedRootSet (L := L) g R)
    (hpos : (integralSignature (invariantFixedLattice (L := L) g)).1 = 1) :
    chamberOf (invariantFixedLattice (L := L) g) (toRealForm _ w)
        (toRealForm (invariantFixedLattice (L := L) g) w)
      = rootInteriorCone (invariantFixedLattice (L := L) g) (toRealForm _ w)
          (foldedRootSet (L := L) g R) := by
  have hQ : 0 < realFormQuadratic (invariantFixedLattice (L := L) g) (toRealForm _ w) := by
    rw [realFormQuadratic_apply, invariant_pairing_toRealForm]
    exact_mod_cast hw
  exact IsChamberWithWalls.chamberOf_eq (L := invariantFixedLattice (L := L) g)
    (t := toRealForm _ w) hpos hQ
    (isChamberWithWalls_invariant_of_sign_cover g R w hw hwv hcover)
    (rootInteriorCone_invariant_self g R w hw hwv)

end LeanCategories.Lattices.Valued
