/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public noncomputable section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace LeanCategories.Algebra

universe u v w

variable {R : Type u} {K : Type v} {G : Type w}
variable [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [CommGroup G]

/-- Neukirch's raw ideal Artin-symbol product (FC09-C06-U075).

For a supplied family of prime Artin symbols, this is the displayed formula
`∏_p Artin(p) ^ ν_p(a)` using the native fractional-ideal multiplicities.
Prime-choice independence, ramification restrictions, multiplicativity, the
resulting homomorphism, and the comparison with the idèlic reciprocity symbol
are deliberately not bundled into this Sweep-III datum. -/
def idealArtinProductData
    (primeArtin : HeightOneSpectrum R → G)
    (a : FractionalIdeal R⁰ K) : G :=
  ∏ᶠ p : HeightOneSpectrum R, primeArtin p ^ FractionalIdeal.count K p a

/-- Serre's raw ideal Artin-symbol extension (FC10-C01-U081), using the same
finite prime-factor product as `idealArtinProductData`.

The source's assertion that this product is independent of choices and defines
a homomorphism on ideals away from ramification remains result content. -/
abbrev serreIdealArtinProductData
    (primeArtin : HeightOneSpectrum R → G)
    (a : FractionalIdeal R⁰ K) : G :=
  idealArtinProductData primeArtin a

end LeanCategories.Algebra
