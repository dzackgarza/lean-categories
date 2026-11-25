/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingChamberOfAmbientRoots
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness

/-!
# Probe for the chamber theorem with the classification input removed

`isChamberWithWalls_invariant_of_foldedRootSet` carries `hsq`, the `(−2)`/`(−4)` alternative that
AEGS take from Namikawa (**printed p. 12**, Lemma 3.4's converse). That input is used in the
chain for one thing only: to know that a root `ρ` of `M^σ`, read in `L`, is a root of `L`
(`hsub`). For a `(−2)`-root this is
`isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two`, unconditionally.

So the probes below decide two things:

* `…_of_hsub` — the theorem with `hsq` replaced by `hsub`, i.e. one divisibility check per root
  instead of the classification;
* `…_of_square_neg_two` — the theorem with `hsq` replaced by "every root of `M^σ` is `(−2)`", the
  **white** case of the colouring on AEGS **p. 10**. In that case no classification input remains.

The third probe records that the new hypothesis really is weaker: `(−2)`-everywhere implies `hsq`.

None of the remaining hypotheses is discharged — `hw`, `hwamb` are interior-point data, `hR`,
`hneg`, `hcase` are the diagram, `hamb` is Vinberg. The point is which of them the theorem needs.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- `(−2)`-everywhere implies the `(−2)`/`(−4)` alternative: the new hypothesis is weaker. -/
example
    (h2 : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
            (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing
              (invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
                (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ) y) :=
  fun ρ hρ => Or.inl (h2 ρ hρ)

/-- The chamber theorem with `hsub` instead of `hsq`, at Definition 3.7's folded root set. -/
example
    (hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed)
    (hwamb : ∀ i, 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (uInteriorFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      ((fun _ : Fin 1 => uRoot) i))
    (hR : ∀ _ : Fin 1, IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj uRoot)
    (hneg : ∀ _ : Fin 1,
      hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot < 0)
    (hcase : ∀ _ : Fin 1,
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot = uRoot ∨
        hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot
          ((1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot) = 0)
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ ∈
        negativeReflectiveRoots hyperbolicPlaneFiniteLattice)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots hyperbolicPlaneFiniteLattice, ∃ c : Fin 1 → ℤ,
      ρ = ∑ i, c i • (fun _ : Fin 1 => uRoot) i ∧
        ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      (toRealForm _ uInteriorFixed)
      (foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
        (Set.range (fun _ : Fin 1 => uRoot))) :=
  isChamberWithWalls_invariant_of_foldedRootSet_of_hsub (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (w := uInteriorFixed) hw hwamb hR hneg hcase hsub hamb

/-- The chamber theorem in the white case: every root of `M^σ` is `(−2)`, no `hsq`. -/
example
    (hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed)
    (hwamb : ∀ i, 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing
      (uInteriorFixed : hyperbolicPlaneFiniteLattice.obj.obj.carrier)
      ((fun _ : Fin 1 => uRoot) i))
    (hR : ∀ _ : Fin 1, IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj uRoot)
    (hneg : ∀ _ : Fin 1,
      hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot < 0)
    (hcase : ∀ _ : Fin 1,
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot = uRoot ∨
        hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot
          ((1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj).1 uRoot) = 0)
    (h2 : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2)
    (hamb : ∀ ρ ∈ negativeReflectiveRoots hyperbolicPlaneFiniteLattice, ∃ c : Fin 1 → ℤ,
      ρ = ∑ i, c i • (fun _ : Fin 1 => uRoot) i ∧
        ((∀ i, 0 ≤ c i) ∨ ∀ i, c i ≤ 0)) :
    IsChamberWithWalls
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      (toRealForm _ uInteriorFixed)
      (foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)
        (Set.range (fun _ : Fin 1 => uRoot))) :=
  isChamberWithWalls_invariant_of_foldedRootSet_of_square_neg_two
    (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) (one_mul 1)
    (R := fun _ : Fin 1 => uRoot) (w := uInteriorFixed) hw hwamb hR hneg hcase h2 hamb

end LeanCategories.Lattices.Valued
