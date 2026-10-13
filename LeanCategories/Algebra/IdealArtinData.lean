/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import LeanCategories.Algebra.ArithmeticFrobeniusData

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

section Serre

variable {S : Type*} [CommRing S] [Algebra R S]
variable [MulSemiringAction G S] [SMulCommClass G R S]
variable [Finite G] [Algebra.IsInvariant R S G]

/-- Serre's prime Artin-symbol family, constructed from the actual arithmetic
Frobenius family over every height-one prime. The only extra input is the
source finiteness condition ensuring a finite residue field above each prime;
the prime above it is chosen internally and its choice-independence follows
from abelianity. -/
noncomputable def serrePrimeArtinData
    (finiteResidue :
      ∀ p : HeightOneSpectrum R,
        ∃ Q : Ideal.primesOver p.asIdeal S, Finite (S ⧸ Q.1))
    (p : HeightOneSpectrum R) : G :=
  serreArtinSymbolAtPrime
    (R := R) (S := S) (G₀ := G) p.asIdeal (finiteResidue p)

/-- Serre's ideal Artin symbol, obtained by applying the constructed
base-prime Artin symbol to the finite prime factorization of the fractional
ideal. No caller-supplied prime-Artin family remains. -/
noncomputable def serreIdealArtinProductData
    (finiteResidue :
      ∀ p : HeightOneSpectrum R,
        ∃ Q : Ideal.primesOver p.asIdeal S, Finite (S ⧸ Q.1))
    (a : FractionalIdeal R⁰ K) : G :=
  idealArtinProductData
    (serrePrimeArtinData (R := R) (S := S) (G := G) finiteResidue) a

end Serre

end LeanCategories.Algebra
