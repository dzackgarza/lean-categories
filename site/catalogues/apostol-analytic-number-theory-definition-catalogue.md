---
title: "Apostol analytic number theory definition catalogue"
---

``` markdown #projects/github.com__dzackgarza__lean-categories/references/apostol-analytic-number-theory-definition-catalogue
# Apostol analytic number theory definition catalogue

``` markdown #projects/github.com__dzackgarza__lean-categories/references/apostol-analytic-number-theory-definition-catalogue

# Apostol analytic number theory definition catalogue

``` markdown #projects/github.com__dzackgarza__lean-categories/references/apostol-analytic-number-theory-definition-catalogue

# Apostol analytic number theory definition catalogue

# Apostol analytic number theory definition catalogue

# Apostol analytic number theory definition catalogue

# *Introduction to Analytic Number Theory*: definition catalogue

- Author — Tom M. Apostol
- Zotero key — `B2FFGKRT`
- Citekey — `Apo98`
- Source attachment — ``local-write-api-1783387653631-B2FFGKRT_extracted.md``

## Chapter 1. The Fundamental Theorem of Arithmetic

- [x] Divisibility — §1.2, “Divisibility,” p. 14
  - `Dvd.dvd` — `Mathlib/Algebra/Group/Defs.lean`
- [x] Greatest common divisor — §1.3, “Greatest common divisor,” p. 14
  - `Nat.gcd` — `Mathlib/Data/Nat/GCD/Basic.lean`
- [x] Relatively prime integers — §1.3, “Greatest common divisor,” p. 14
  - `Nat.Coprime` — `Mathlib/Data/Nat/GCD/Basic.lean`
- [x] Prime number — §1.4, “Prime numbers,” p. 16
  - `Nat.Prime` — `Mathlib/Data/Nat/Prime/Defs.lean`
- [x] Composite number — §1.4, “Prime numbers,” p. 16
  - `Nat.Prime` — `Mathlib/Data/Nat/Prime/Defs.lean`

## Chapter 2. Arithmetical Functions and Dirichlet Multiplication

- [x] Arithmetical function — §2.1, “Introduction,” p. 24
  - `ArithmeticFunction` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] Möbius function — §2.2, “The Möbius function μ(n),” p. 24
  - `ArithmeticFunction.moebius` — `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`
- [x] Euler totient function — §2.3, “The Euler totient function φ(n),” p. 25
  - `Nat.totient` — `Mathlib/Data/Nat/Totient.lean`
- [x] Dirichlet product — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - `ArithmeticFunction.mul_apply` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] Dirichlet convolution — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - `ArithmeticFunction.mul_apply` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] Identity for Dirichlet convolution — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - `ArithmeticFunction.one_apply` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] Unit function — §2.7, “Dirichlet inverses and the Möbius inversion formula,” p. 30
  - `ArithmeticFunction.zeta` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] von Mangoldt function — §2.8, “The Mangoldt function Λ(n),” p. 32
  - `ArithmeticFunction.vonMangoldt` — `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`
- [x] Multiplicative function — §2.9, “Multiplicative functions,” p. 33
  - `ArithmeticFunction.IsMultiplicative` — `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`
- [x] Liouville function — §2.12, “Liouville's function λ(n),” p. 37
  - `ArithmeticFunction.liouville` — `Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`
- [x] Divisor function σα — §2.13, “The divisor functions σα(n),” p. 38
  - `ArithmeticFunction.sigma` — `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`
- [ ] Bell series — §2.16, “The Bell series of an arithmetical function,” p. 42
- [ ] Derivative of an arithmetical function — §2.18, “Derivatives of arithmetical functions,” p. 45

## Chapter 3. Averages of Arithmetical Functions

- [x] Big O notation — §3.2, “The big oh notation. Asymptotic equality of functions,” p. 53
  - `Asymptotics.IsBigO` — `Mathlib/Analysis/Asymptotics/Defs.lean`
- [x] Asymptotic equality — §3.2, “The big oh notation. Asymptotic equality of functions,” p. 53
  - `Asymptotics.IsEquivalent` — `Mathlib/Analysis/Asymptotics/Defs.lean`
- [ ] Mutually visible lattice points — §3.8, “An application to the distribution of lattice points visible from the origin,” p. 61

## Chapter 4. Some Elementary Theorems on the Distribution of Prime Numbers

- [x] Chebyshev ψ-function — §4.2, “Chebyshev's functions ψ(x) and θ(x),” p. 75
  - `Chebyshev.psi` — `Mathlib/NumberTheory/Chebyshev.lean`
- [x] Chebyshev θ-function — §4.2, “Chebyshev's functions ψ(x) and θ(x),” p. 75
  - `Chebyshev.theta` — `Mathlib/NumberTheory/Chebyshev.lean`
- [x] Summatory Möbius function — §4.9, “The partial sums of the Möbius function,” p. 91
  - `MobiusLemma.M` — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/IEANTN/MobiusLemma.lean`

## Chapter 5. Congruences

- [x] Congruence modulo m — §5.1, “Definition and basic properties of congruences,” p. 106
  - `Nat.ModEq` — `Mathlib/Data/Nat/ModEq.lean`
- [x] Residue class modulo m — §5.2, “Residue classes and complete residue systems,” p. 109
  - `ZMod` — `Mathlib/Data/ZMod/Defs.lean`
- [ ] Complete residue system modulo m — §5.2, “Residue classes and complete residue systems,” p. 109
- [x] Reduced residue system modulo m — §5.4, “Reduced residue systems and the Euler–Fermat theorem,” p. 113
  - `reducedResidues` — `ShouqiaoW__erdos/1002/lean/Erdos1002/RamanujanSums.lean`

## Chapter 6. Finite Abelian Groups and Their Characters

- [x] Group — §6.1, “Definitions,” p. 129
  - `Group` — `Mathlib/Algebra/Group/Defs.lean`
- [x] Abelian group — §6.1, “Definitions,” p. 129
  - `CommGroup` — `Mathlib/Algebra/Group/Defs.lean`
- [x] Finite group — §6.1, “Definitions,” p. 129
  - `Finite` — `Mathlib/Data/Finite/Defs.lean`
- [x] Order of a finite group — §6.1, “Definitions,” p. 129
  - `Nat.card` — `Mathlib/SetTheory/Cardinal/Finite.lean`
- [x] Subgroup — §6.1, “Definitions,” p. 129
  - `Subgroup` — `Mathlib/Algebra/Group/Subgroup/Defs.lean`
- [x] Powers of a group element — §6.3, “Elementary properties of groups,” p. 130
  - `zpowRec` — `Mathlib/Algebra/Group/Defs.lean`
- [x] Character of a group — §6.5, “Characters of finite abelian groups,” p. 133
  - `MulChar` — `Mathlib/NumberTheory/MulChar/Basic.lean`
- [x] Character group — §6.6, “The character group,” p. 135
  - `MulChar` — `Mathlib/NumberTheory/MulChar/Basic.lean`
- [x] Dirichlet character — §6.8, “Dirichlet characters,” p. 137
  - `DirichletCharacter` — `Mathlib/NumberTheory/DirichletCharacter/Basic.lean`

## Chapter 7. Dirichlet's Theorem on Primes in Arithmetic Progressions

- No definition names recovered from the extraction.

## Chapter 8. Periodic Arithmetical Functions and Gauss Sums

- [x] Gauss sum associated with a Dirichlet character — §8.5, “Gauss sums associated with Dirichlet characters,” p. 165
  - `gaussSum` — `Mathlib/NumberTheory/GaussSum.lean`
- [x] Separable Gauss sum — §8.5, “Gauss sums associated with Dirichlet characters,” p. 165
  - Mathlib: `gaussSum` — `Mathlib/NumberTheory/GaussSum.lean`
- [x] Induced modulus — §8.7, “Induced moduli and primitive characters,” p. 167
  - `DirichletCharacter.FactorsThrough` — `Mathlib/NumberTheory/DirichletCharacter/Basic.lean`
- [x] Primitive Dirichlet character — §8.7, “Induced moduli and primitive characters,” p. 167
  - `DirichletCharacter.IsPrimitive` — `Mathlib/NumberTheory/DirichletCharacter/Basic.lean`
- [x] Conductor of a Dirichlet character — §8.9, “The conductor of a character,” p. 171
  - `DirichletCharacter.conductor` — `Mathlib/NumberTheory/DirichletCharacter/Basic.lean`

## Chapter 9. Quadratic Residues and the Quadratic Reciprocity Law

- [x] Quadratic residue modulo p — §9.1, “Quadratic residues,” p. 178
  - `legendreSym` — `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`
- [x] Quadratic nonresidue modulo p — §9.1, “Quadratic residues,” p. 178
  - `legendreSym` — `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`
- [x] Legendre symbol — §9.2, “Legendre's symbol and its properties,” p. 179
  - `legendreSym` — `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`
- [x] Jacobi symbol — §9.7, “The Jacobi symbol,” p. 187
  - `jacobiSym` — `Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean`

## Chapter 10. Primitive Roots

- [x] Exponent of an integer modulo m — §10.1, “The exponent of a number mod m. Primitive roots,” p. 204
  - `orderOf` — `Mathlib/GroupTheory/OrderOfElement.lean`
- [x] Primitive root modulo m — §10.1, “The exponent of a number mod m. Primitive roots,” p. 204
  - `IsPrimitiveRoot` — `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`

## Chapter 11. Dirichlet Series and Euler Products

- [x] Dirichlet series — §11.1, “Introduction,” p. 224
  - `LSeries` — `Mathlib/NumberTheory/LSeries/Basic.lean`
- [x] Half-plane of absolute convergence — §11.2, “The half-plane of absolute convergence of a Dirichlet series,” p. 225
  - `LSeriesSummable` — `Mathlib/NumberTheory/LSeries/Basic.lean`
- [x] Euler product — §11.5, “Euler products,” p. 230
  - `ArithmeticFunction.eulerProduct` — `Mathlib/NumberTheory/ArithmeticFunction/LFunction.lean`
- [x] Half-plane of convergence — §11.6, “The half-plane of convergence of a Dirichlet series,” p. 232
  - `LSeriesSummable` — `Mathlib/NumberTheory/LSeries/Basic.lean`

## Chapter 12. The Functions ζ(s) and L(s, χ)

- [x] Hurwitz zeta function — §12.3, “Integral representation for the Hurwitz zeta function,” p. 251; continued in §12.5, p. 254
  - `hurwitzZeta` — `Mathlib/NumberTheory/LSeries/HurwitzZeta.lean`
- [x] Riemann zeta function — §12.6, “Analytic continuation of ζ(s) and L(s, χ),” p. 255
  - `riemannZeta` — `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`
- [x] Dirichlet L-function — §12.6, “Analytic continuation of ζ(s) and L(s, χ),” p. 255
  - `DirichletCharacter.LFunction` — `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`
- [x] Bernoulli polynomials — §12.11, “Evaluation of ζ(−n,a),” p. 264
  - `Polynomial.bernoulli` — `Mathlib/NumberTheory/BernoulliPolynomials.lean`
- [x] Bernoulli numbers — §12.12, “Properties of Bernoulli numbers and Bernoulli polynomials,” p. 265
  - `bernoulli` — `Mathlib/NumberTheory/Bernoulli.lean`

## Chapter 13. Analytic Proof of the Prime Number Theorem

- [x] Zero-free region for ζ(s) — §13.8, “Zero-free regions for ζ(s),” p. 291
  - `riemannZeta.classicalZeroFree` — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/IEANTN/ZetaDefinitions.lean`
- [x] Riemann hypothesis — §13.9, “The Riemann hypothesis,” p. 293
  - `RiemannHypothesis` — `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`

## Chapter 14. Partitions

- [x] Unrestricted partition — §14.1, “Introduction,” p. 304
  - `Nat.Partition` — `Mathlib/Combinatorics/Enumerative/Partition/Basic.lean`
- [x] Partition function p(n) — §14.1, “Introduction,” p. 304
  - `Fintype.card` — `Mathlib/Data/Fintype/Card.lean`
- [x] Generating function for partitions — §14.3, “Generating functions for partitions,” p. 308
  - `Nat.Partition.genFun` — `Mathlib/Combinatorics/Enumerative/Partition/GenFun.lean`
```

```

```
