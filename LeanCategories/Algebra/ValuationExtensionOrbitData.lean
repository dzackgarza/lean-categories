/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ValuationRamificationData
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Valuation-extension orbit data

Definition-level realization of Neukirch FC09-C02-U113.

For a valuation `v` of `K` and an extension field `L/K`, Neukirch writes
`W_v` for the set of extensions of `v` to `L`.  In a Galois extension,
after choosing one extension `w`, the source uses the right-coset carrier
`G_w \ G` and the representative formula

`G_w σ ↦ w σ`.

For a separable extension embedded in a Galois extension `N/K`, with
`H = G(N/L)`, the corresponding carrier is `G_w \ G / H` and the
representative formula is

`G_w σ H ↦ (w σ)|_L`.

Mathlib acts on valuation subrings by direct image.  Therefore the valuation
ring of the source's right action `w σ`, whose value is `x ↦ w(σ x)`, is
`σ⁻¹ • O_w`.

Sweep III records only these carriers and representative-level formulas.
Showing that the representatives still extend `v`, that the formulas are
constant on right/double cosets, transitivity, quotient descent, bijectivity,
and the cardinality/index statements are all result-layer content.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace LeanCategories.Algebra

universe uK uL uN

variable
  {K : Type uK} {L : Type uL}
  [Field K] [Field L] [Algebra K L]

/-- Neukirch's `W_v`: valuation subrings of `L` whose restriction to
`K` is the chosen valuation subring `A`.

No existence theorem is part of this subtype definition. -/
abbrev ValuationExtensionData (A : ValuationSubring K) : Type _ :=
  {B : ValuationSubring L // B.comap (algebraMap K L) = A}

/-- The right-coset carrier `G_w \ G` used by Neukirch.

Mathlib's usual quotient `G ⧸ H` is the left-coset quotient; the source
explicitly uses right cosets `H σ`, hence the explicit `rightRel`. -/
abbrev valuationExtensionRightCosetsData (B : ValuationSubring L) : Type _ :=
  Quotient (QuotientGroup.rightRel (B.decompositionSubgroup K))

/-- Representative-level right action `w σ` on a valuation extension.

Since pointwise scalar action on valuation subrings is direct image, the
valuation ring of `x ↦ w(σ x)` is `σ⁻¹ • O_w`.  The theorem that this
again restricts to the same base valuation is deliberately separate. -/
def valuationExtensionOrbitRepresentativeData
    (B : ValuationSubring L) (σ : L ≃ₐ[K] L) : ValuationSubring L :=
  σ⁻¹ • B

variable
  {N : Type uN} [Field N] [Algebra K N]

/-- The double-coset carrier `G_w \ G / H` for a chosen valuation
extension on a Galois overfield `N` and an intermediate field `E`.

Here `H = Gal(N/E)` is Mathlib's native fixing subgroup. -/
abbrev valuationExtensionDoubleCosetsData
    (B : ValuationSubring N) (E : IntermediateField K N) : Type _ :=
  DoubleCoset.Quotient
    (B.decompositionSubgroup K : Set (N ≃ₐ[K] N))
    (E.fixingSubgroup : Set (N ≃ₐ[K] N))

/-- Representative-level formula for the separable double-coset construction:
`σ` is sent to the restriction of `w σ` to the intermediate field `E`.

The fact that this depends only on the double coset and defines an extension
of the base valuation is result content. -/
def separableValuationExtensionRepresentativeData
    (B : ValuationSubring N) (E : IntermediateField K N)
    (σ : N ≃ₐ[K] N) : ValuationSubring E :=
  (σ⁻¹ • B).comap E.val.toRingHom

end LeanCategories.Algebra
