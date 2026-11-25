/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license or a later version; see the LICENSE file.
-/
module

public import LeanCategories.Lattices.Valued.FoldingNegativeFourRoots
public import LeanCategories.Lattices.Valued.TwoElementaryRootSquare

/-!
# The two faces of the root hypothesis are one (`#116`)

The folding chamber theorem carries a hypothesis about roots of the fixed lattice `M^σ`, in two
equivalent guises:

* `hsq` — every root `ρ` of `M^σ` has square `(−2)`, or `(−4)` with all pairings of its ambient
  image
  `ρ^` even (AEGS **printed p. 12**, Lemma 3.4's converse);
* `hsub` — the ambient image `ρ^` of every root of `M^σ` is a root of `L`.

The report listed `hsq` among the external inputs. It is not independent of `hsub`, and this file
settles the implication in the direction that needs theory:

* `hsub_of_hsq` — `hsq` gives `hsub`: a `(−2)`-root is a root of any integral extension
  (`isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two`) and a `(−4)`-root is one exactly
  when its ambient pairings are even
  (`isReflectiveRoot_invariantCarrierToAmbient_iff_two_dvd_pairing`).
* `hsq_of_hsub_of_two_elementary` — `hsub` gives `hsq`, given that `L` is even 2-elementary
  (**printed p. 10**): the p. 10 rule `square_criterion_of_two_elementary`
  (`TwoElementaryRootSquare.lean`) applied to `L` at `ρ^` produces the alternative verbatim. So the
  ambient-pairing clause carries no information beyond the transfer — AEGS Lemma 3.4's type (3) is
  the whole of it.
* `hsub_iff_hsq_of_two_elementary` — the two are interchangeable.

Consequence for item 4: the external inputs are `hamb` (Vinberg) and *one* root hypothesis, not two.
`hsq` and `hsub` may be carried interchangeably; `hsub` is the weaker interface and `hsq` the one
the
class-restriction corollaries are stated at.

What is not done here: nothing shows that either guise holds in `T_dP` or `T_En`. The p. 10 rule is
applied to `L`, so the hypotheses `hev`, `h2e` are the source's assertion about `T_dP`, cited and
not
reproved, exactly as in `TwoElementaryRootSquare.lean`.

## LC-09 record

Repository: `rg "hsub_of_hsq|hsq_of_hsub"` gives nothing; the two directions exist only *inside*
`isChamberWithWalls_invariant_of_square_criterion` (`FoldingChamberOfSquareCriterion.lean:53`),
never
as statements, so the equivalence was not recorded anywhere. Mathlib has no statement relating
reflectivity of a vector to reflectivity of its image in an extension. The live corpus returns
nothing
for `"IsReflective sublattice"` and `"reflectiveRoot invariant"` (recorded in
`TwoElementaryRootSquare.lean`); no port.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, *Compact moduli of Enriques surfaces of degree
  2*,
  Nagoya Math. J. 259 (2025), arXiv:2312.03638v2: the even 2-elementary rule and the `(−2)`/`(−4)`
  colouring, **printed p. 10**; Lemma 3.4 and its converse, Definition 3.7 and Lemma 3.8,
  **printed p. 12**.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, 2.13, 2.15, as
  cited by the source at **printed p. 12**.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

variable {L : FiniteProjectiveLatticeCat ℤ ℤ}

/-- The ambient pairing of the image is the pairing in `M^σ`. -/
theorem invariantCarrierToAmbient_pairing_self (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (ρ : (invariantFixedLattice (L := L) g).obj.obj.carrier) :
    L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ)
      (invariantCarrierToAmbient (L := L) g ρ)
      = (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ := by
  rw [invariantCarrierToAmbient_apply]
  exact (invariantFixedLattice_pairing (L := L) g
    (show ↥(involutionFixedSubmodule g) from ρ)
    (show ↥(involutionFixedSubmodule g) from ρ)).symm

/-- **`hsq` gives the transfer.** No hypothesis on `L`: this is the `(−2)`/`(−4)` case analysis. -/
theorem hsub_of_hsq (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (hsq : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : L.obj.obj.carrier,
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y)) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      invariantCarrierToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rcases hsq ρ hρ with h2 | ⟨h4, hev⟩
    · exact isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two (L := L) g h2
    · exact (isReflectiveRoot_invariantCarrierToAmbient_iff_two_dvd_pairing (L := L) g h4).mpr hev
  · rw [invariantCarrierToAmbient_pairing_self (L := L) g ρ]
    rcases hsq ρ hρ with h2 | ⟨h4, _⟩
    · rw [h2]; norm_num
    · rw [h4]; norm_num

/-- **The transfer gives `hsq`**, given that `L` is even 2-elementary (**printed p. 10**): the p. 10
rule applied to `L` at the image of the root. -/
theorem hsq_of_hsub_of_two_elementary (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (hev : ∀ y : L.obj.obj.carrier, (2 : ℤ) ∣ L.obj.obj.pairing y y)
    (h2e : ∀ x : L.obj.obj.carrier, x ≠ 0 → ∃ (y₁ y₂ : L.obj.obj.carrier) (c₁ c₂ : ℤ),
      c₁ * L.obj.obj.pairing x y₁ + c₂ * L.obj.obj.pairing x y₂ = 2)
    (hsub : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      invariantCarrierToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L) :
    ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
      (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
        ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
          ∀ y : L.obj.obj.carrier,
            (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y) := by
  intro ρ hρ
  have hL := pairing_eq_neg_two_or_neg_four_of_two_elementary (L := L) hev h2e
    (hsub ρ hρ).1 (hsub ρ hρ).2
  have hcoe := invariantCarrierToAmbient_pairing_self (L := L) g ρ
  rcases hL with h | ⟨h, hy⟩
  · exact Or.inl (by rw [← hcoe]; exact h)
  · exact Or.inr ⟨by rw [← hcoe]; exact h, hy⟩

/-- **The two guises are one**, when `L` is even 2-elementary (**printed p. 10**). -/
theorem hsub_iff_hsq_of_two_elementary (g : OrthogonalGroup L.obj)
    [Module.Projective ℤ (involutionFixedSubmodule g)]
    (hev : ∀ y : L.obj.obj.carrier, (2 : ℤ) ∣ L.obj.obj.pairing y y)
    (h2e : ∀ x : L.obj.obj.carrier, x ≠ 0 → ∃ (y₁ y₂ : L.obj.obj.carrier) (c₁ c₂ : ℤ),
      c₁ * L.obj.obj.pairing x y₁ + c₂ * L.obj.obj.pairing x y₂ = 2) :
    (∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
        invariantCarrierToAmbient (L := L) g ρ ∈ negativeReflectiveRoots L) ↔
      ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice (L := L) g),
        (invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -2 ∨
          ((invariantFixedLattice (L := L) g).obj.obj.pairing ρ ρ = -4 ∧
            ∀ y : L.obj.obj.carrier,
              (2 : ℤ) ∣ L.obj.obj.pairing (invariantCarrierToAmbient (L := L) g ρ) y) :=
  ⟨hsq_of_hsub_of_two_elementary (L := L) g hev h2e, hsub_of_hsq (L := L) g⟩

end LeanCategories.Lattices.Valued
