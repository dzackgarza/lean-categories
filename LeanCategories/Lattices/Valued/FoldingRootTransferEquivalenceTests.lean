/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingRootTransferEquivalence
public import LeanCategories.Lattices.Valued.FoldingSignCoverWitness
public import LeanCategories.Lattices.Valued.Standard

/-!
# Probe: the ambient-pairing clause is not a second input

The report listed two external inputs at item 4, `hamb` (Vinberg) and the ambient-pairing half of
`hsq`. The probes below decide that the second is not independent: with `L` even 2-elementary
(AEGS **printed p. 10**) the p. 10 rule applied to `L` at the image of a root gives `hsq`'s
ambient clause verbatim, and conversely `hsq` gives the transfer. So the two are one input, and
the chain may carry whichever is convenient.

Both directions are exercised at the hyperbolic plane, with the p. 10 hypotheses on `L` carried, not
proved — they are the source's assertion about its lattices.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-- `hsub` and the p. 10 hypotheses on `L` give `hsq`. -/
example
    (hev : ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing y y)
    (h2e : ∀ x : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
      ∃ (y₁ y₂ : hyperbolicPlaneFiniteLattice.obj.obj.carrier) (c₁ c₂ : ℤ),
        c₁ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₁ +
          c₂ * hyperbolicPlaneFiniteLattice.obj.obj.pairing x y₂ = 2)
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ ∈
        negativeReflectiveRoots hyperbolicPlaneFiniteLattice) :
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
  hsq_of_hsub_of_two_elementary (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) hev h2e hsub

/-- `hsq` gives the transfer, with no hypotheses on `L` at all. -/
example
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : hyperbolicPlaneFiniteLattice.obj.obj.carrier,
            (2 : ℤ) ∣ hyperbolicPlaneFiniteLattice.obj.obj.pairing
              (invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
                (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ) y)) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
        (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      invariantCarrierToAmbient (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) ρ ∈
        negativeReflectiveRoots hyperbolicPlaneFiniteLattice :=
  hsub_of_hsq (L := hyperbolicPlaneFiniteLattice)
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) hsq

end LeanCategories.Lattices.Valued
