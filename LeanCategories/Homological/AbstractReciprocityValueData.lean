/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FormationReciprocityData

/-!
# Raw abstract-reciprocity values

Definition-level realization of Neukirch FC09-C04-U059.

For a Frobenius element `σ`, let `Σ` denote its fixed field and choose a
prime element `π_Σ`.  Neukirch's displayed reciprocity value is

`N_{Σ/K}(π_Σ) mod N_{L-tilde/K} A_{L-tilde}`.

The checked ClassFieldTheory reference separates this displayed value from the
later mathematics needed to make it canonical.  Its `reciprocityValueOfPrime`
takes an explicit prime, while the source-specific chosen prime is obtained
from surjectivity of the normalized valuation and prime-choice independence is
proved separately from the unramified-unit cohomology axiom.

Sweep III therefore keeps the norm class as raw data.  The caller supplies the
fixed-field coefficient carrier, its prime-element subset, the already-defined
norm function, the infinite-level norm subgroup, and (for a total map) an
explicit prime choice.  Prime existence, independence of that choice,
multiplicativity, and canonicality are result-layer obligations.
-/

@[expose] public section

namespace LeanCategories.Homological

universe uF uSigma uK

/-- The reciprocity value attached to an explicitly supplied prime element:
`N_{Σ/K}(π_Σ)` modulo the supplied infinite-level norm subgroup.

`primeElements` is the source's fibre `{π | v_Σ(π)=1}`; keeping it as an
explicit subset preserves the prime-element hypothesis without requiring the
existence theorem used to choose such an element. -/
def abstractReciprocityValueOfPrimeData
    {ASigma : Type uSigma} {AK : Type uK} [CommGroup AK]
    (primeElements : Set ASigma)
    (norm : ASigma → AK)
    (N : Subgroup AK)
    (π : primeElements) :
    formationNormQuotientData AK N :=
  QuotientGroup.mk (norm π.1)

/-- Raw reciprocity map obtained after supplying a prime choice in every
Frobenius fixed field.

For each `σ`, `fixedFieldCoefficients σ` is the coefficient carrier
`A_Σ`, `norm σ` is `N_{Σ/K}`, and `chosenPrime σ` is the chosen
`π_Σ`.  The output is only a function on the Frobenius carrier: the source's
choice independence and later multiplicativity theorem are deliberately not
bundled into this definition. -/
def abstractReciprocityMapFromPrimeChoiceData
    {Frob : Type uF} {AK : Type uK} [CommGroup AK]
    (fixedFieldCoefficients : Frob → Type uSigma)
    (primeElements : (σ : Frob) → Set (fixedFieldCoefficients σ))
    (norm : (σ : Frob) → fixedFieldCoefficients σ → AK)
    (chosenPrime : (σ : Frob) → primeElements σ)
    (N : Subgroup AK) :
    Frob → formationNormQuotientData AK N :=
  fun σ =>
    abstractReciprocityValueOfPrimeData
      (primeElements σ) (norm σ) N (chosenPrime σ)

end LeanCategories.Homological
