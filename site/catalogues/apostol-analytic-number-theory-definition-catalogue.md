---
title: "Apostol analytic number theory definition catalogue"
---

- Author — Tom M. Apostol
- Zotero key — `B2FFGKRT`
- Citekey — `Apo98`
- Source attachment — ``local-write-api-1783387653631-B2FFGKRT_extracted.md``

## Chapter 1. The Fundamental Theorem of Arithmetic

- [x] Divisibility — §1.2, “Divisibility,” p. 14
  - [`Dvd.dvd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Dvd.dvd#doc) — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Greatest common divisor — §1.3, “Greatest common divisor,” p. 14
  - [`Nat.gcd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.gcd#doc) — [`Mathlib/Data/Nat/GCD/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/GCD/Basic.html)
- [x] Relatively prime integers — §1.3, “Greatest common divisor,” p. 14
  - [`Nat.Coprime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.Coprime#doc) — [`Mathlib/Data/Nat/GCD/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/GCD/Basic.html)
- [x] Prime number — §1.4, “Prime numbers,” p. 16
  - [`Nat.Prime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.Prime#doc) — [`Mathlib/Data/Nat/Prime/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html)
- [x] Composite number — §1.4, “Prime numbers,” p. 16
  - [`Nat.Prime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.Prime#doc) — [`Mathlib/Data/Nat/Prime/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html)

## Chapter 2. Arithmetical Functions and Dirichlet Multiplication

- [x] Arithmetical function — §2.1, “Introduction,” p. 24
  - `ArithmeticFunction` — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] Möbius function — §2.2, “The Möbius function μ(n),” p. 24
  - [`ArithmeticFunction.moebius`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.moebius#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html)
- [x] Euler totient function — §2.3, “The Euler totient function φ(n),” p. 25
  - [`Nat.totient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.totient#doc) — [`Mathlib/Data/Nat/Totient.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Totient.html)
- [x] Dirichlet product — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - [`ArithmeticFunction.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.mul_apply#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] Dirichlet convolution — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - [`ArithmeticFunction.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.mul_apply#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] Identity for Dirichlet convolution — §2.6, “The Dirichlet product of arithmetical functions,” p. 29
  - [`ArithmeticFunction.one_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.one_apply#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] Unit function — §2.7, “Dirichlet inverses and the Möbius inversion formula,” p. 30
  - [`ArithmeticFunction.zeta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.zeta#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] von Mangoldt function — §2.8, “The Mangoldt function Λ(n),” p. 32
  - [`ArithmeticFunction.vonMangoldt`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.vonMangoldt#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.html)
- [x] Multiplicative function — §2.9, “Multiplicative functions,” p. 33
  - [`ArithmeticFunction.IsMultiplicative`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.IsMultiplicative#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Defs.html)
- [x] Liouville function — §2.12, “Liouville's function λ(n),” p. 37
  - [`ArithmeticFunction.liouville`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.liouville#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Liouville.html)
- [x] Divisor function σα — §2.13, “The divisor functions σα(n),” p. 38
  - [`ArithmeticFunction.sigma`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.sigma#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Misc.html)
- [ ] Bell series — §2.16, “The Bell series of an arithmetical function,” p. 42
- [ ] Derivative of an arithmetical function — §2.18, “Derivatives of arithmetical functions,” p. 45

## Chapter 3. Averages of Arithmetical Functions

- [x] Big O notation — §3.2, “The big oh notation. Asymptotic equality of functions,” p. 53
  - [`Asymptotics.IsBigO`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Asymptotics.IsBigO#doc) — [`Mathlib/Analysis/Asymptotics/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Defs.html)
- [x] Asymptotic equality — §3.2, “The big oh notation. Asymptotic equality of functions,” p. 53
  - [`Asymptotics.IsEquivalent`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Asymptotics.IsEquivalent#doc) — [`Mathlib/Analysis/Asymptotics/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Defs.html)
- [ ] Mutually visible lattice points — §3.8, “An application to the distribution of lattice points visible from the origin,” p. 61

## Chapter 4. Some Elementary Theorems on the Distribution of Prime Numbers

- [x] Chebyshev ψ-function — §4.2, “Chebyshev's functions ψ(x) and θ(x),” p. 75
  - [`Chebyshev.psi`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Chebyshev.psi#doc) — [`Mathlib/NumberTheory/Chebyshev.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html)
- [x] Chebyshev θ-function — §4.2, “Chebyshev's functions ψ(x) and θ(x),” p. 75
  - [`Chebyshev.theta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Chebyshev.theta#doc) — [`Mathlib/NumberTheory/Chebyshev.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html)
- [x] Summatory Möbius function — §4.9, “The partial sums of the Möbius function,” p. 91
  - [`MobiusLemma.M`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MobiusLemma.M#doc) — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/IEANTN/MobiusLemma.lean`

## Chapter 5. Congruences

- [x] Congruence modulo m — §5.1, “Definition and basic properties of congruences,” p. 106
  - [`Nat.ModEq`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.ModEq#doc) — [`Mathlib/Data/Nat/ModEq.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ModEq.html)
- [x] Residue class modulo m — §5.2, “Residue classes and complete residue systems,” p. 109
  - `ZMod` — [`Mathlib/Data/ZMod/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Defs.html)
- [ ] Complete residue system modulo m — §5.2, “Residue classes and complete residue systems,” p. 109
- [x] Reduced residue system modulo m — §5.4, “Reduced residue systems and the Euler–Fermat theorem,” p. 113
  - `reducedResidues` — `ShouqiaoW__erdos/1002/lean/Erdos1002/RamanujanSums.lean`

## Chapter 6. Finite Abelian Groups and Their Characters

- [x] Group — §6.1, “Definitions,” p. 129
  - `Group` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Abelian group — §6.1, “Definitions,” p. 129
  - `CommGroup` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Finite group — §6.1, “Definitions,” p. 129
  - `Finite` — [`Mathlib/Data/Finite/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finite/Defs.html)
- [x] Order of a finite group — §6.1, “Definitions,” p. 129
  - [`Nat.card`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.card#doc) — [`Mathlib/SetTheory/Cardinal/Finite.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Finite.html)
- [x] Subgroup — §6.1, “Definitions,” p. 129
  - `Subgroup` — [`Mathlib/Algebra/Group/Subgroup/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Defs.html)
- [x] Powers of a group element — §6.3, “Elementary properties of groups,” p. 130
  - `zpowRec` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Character of a group — §6.5, “Characters of finite abelian groups,” p. 133
  - `MulChar` — [`Mathlib/NumberTheory/MulChar/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/MulChar/Basic.html)
- [x] Character group — §6.6, “The character group,” p. 135
  - `MulChar` — [`Mathlib/NumberTheory/MulChar/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/MulChar/Basic.html)
- [x] Dirichlet character — §6.8, “Dirichlet characters,” p. 137
  - `DirichletCharacter` — [`Mathlib/NumberTheory/DirichletCharacter/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Basic.html)

## Chapter 7. Dirichlet's Theorem on Primes in Arithmetic Progressions

- No definition names recovered from the extraction.

## Chapter 8. Periodic Arithmetical Functions and Gauss Sums

- [x] Gauss sum associated with a Dirichlet character — §8.5, “Gauss sums associated with Dirichlet characters,” p. 165
  - `gaussSum` — [`Mathlib/NumberTheory/GaussSum.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/GaussSum.html)
- [x] Separable Gauss sum — §8.5, “Gauss sums associated with Dirichlet characters,” p. 165
  - Mathlib: `gaussSum` — [`Mathlib/NumberTheory/GaussSum.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/GaussSum.html)
- [x] Induced modulus — §8.7, “Induced moduli and primitive characters,” p. 167
  - [`DirichletCharacter.FactorsThrough`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.FactorsThrough#doc) — [`Mathlib/NumberTheory/DirichletCharacter/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Basic.html)
- [x] Primitive Dirichlet character — §8.7, “Induced moduli and primitive characters,” p. 167
  - [`DirichletCharacter.IsPrimitive`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.IsPrimitive#doc) — [`Mathlib/NumberTheory/DirichletCharacter/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Basic.html)
- [x] Conductor of a Dirichlet character — §8.9, “The conductor of a character,” p. 171
  - [`DirichletCharacter.conductor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.conductor#doc) — [`Mathlib/NumberTheory/DirichletCharacter/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletCharacter/Basic.html)

## Chapter 9. Quadratic Residues and the Quadratic Reciprocity Law

- [x] Quadratic residue modulo p — §9.1, “Quadratic residues,” p. 178
  - `legendreSym` — [`Mathlib/NumberTheory/LegendreSymbol/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/Basic.html)
- [x] Quadratic nonresidue modulo p — §9.1, “Quadratic residues,” p. 178
  - `legendreSym` — [`Mathlib/NumberTheory/LegendreSymbol/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/Basic.html)
- [x] Legendre symbol — §9.2, “Legendre's symbol and its properties,” p. 179
  - `legendreSym` — [`Mathlib/NumberTheory/LegendreSymbol/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/Basic.html)
- [x] Jacobi symbol — §9.7, “The Jacobi symbol,” p. 187
  - `jacobiSym` — [`Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.html)

## Chapter 10. Primitive Roots

- [x] Exponent of an integer modulo m — §10.1, “The exponent of a number mod m. Primitive roots,” p. 204
  - `orderOf` — [`Mathlib/GroupTheory/OrderOfElement.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/OrderOfElement.html)
- [x] Primitive root modulo m — §10.1, “The exponent of a number mod m. Primitive roots,” p. 204
  - `IsPrimitiveRoot` — [`Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.html)

## Chapter 11. Dirichlet Series and Euler Products

- [x] Dirichlet series — §11.1, “Introduction,” p. 224
  - `LSeries` — [`Mathlib/NumberTheory/LSeries/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Basic.html)
- [x] Half-plane of absolute convergence — §11.2, “The half-plane of absolute convergence of a Dirichlet series,” p. 225
  - `LSeriesSummable` — [`Mathlib/NumberTheory/LSeries/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Basic.html)
- [x] Euler product — §11.5, “Euler products,” p. 230
  - [`ArithmeticFunction.eulerProduct`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ArithmeticFunction.eulerProduct#doc) — [`Mathlib/NumberTheory/ArithmeticFunction/LFunction.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/LFunction.html)
- [x] Half-plane of convergence — §11.6, “The half-plane of convergence of a Dirichlet series,” p. 232
  - `LSeriesSummable` — [`Mathlib/NumberTheory/LSeries/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Basic.html)

## Chapter 12. The Functions ζ(s) and L(s, χ)

- [x] Hurwitz zeta function — §12.3, “Integral representation for the Hurwitz zeta function,” p. 251; continued in §12.5, p. 254
  - `hurwitzZeta` — [`Mathlib/NumberTheory/LSeries/HurwitzZeta.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/HurwitzZeta.html)
- [x] Riemann zeta function — §12.6, “Analytic continuation of ζ(s) and L(s, χ),” p. 255
  - `riemannZeta` — [`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)
- [x] Dirichlet L-function — §12.6, “Analytic continuation of ζ(s) and L(s, χ),” p. 255
  - [`DirichletCharacter.LFunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirichletCharacter.LFunction#doc) — [`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/DirichletContinuation.html)
- [x] Bernoulli polynomials — §12.11, “Evaluation of ζ(−n,a),” p. 264
  - [`Polynomial.bernoulli`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.bernoulli#doc) — [`Mathlib/NumberTheory/BernoulliPolynomials.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/BernoulliPolynomials.html)
- [x] Bernoulli numbers — §12.12, “Properties of Bernoulli numbers and Bernoulli polynomials,” p. 265
  - `bernoulli` — [`Mathlib/NumberTheory/Bernoulli.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bernoulli.html)

## Chapter 13. Analytic Proof of the Prime Number Theorem

- [x] Zero-free region for ζ(s) — §13.8, “Zero-free regions for ζ(s),” p. 291
  - [`riemannZeta.classicalZeroFree`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=riemannZeta.classicalZeroFree#doc) — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/IEANTN/ZetaDefinitions.lean`
- [x] Riemann hypothesis — §13.9, “The Riemann hypothesis,” p. 293
  - `RiemannHypothesis` — [`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)

## Chapter 14. Partitions

- [x] Unrestricted partition — §14.1, “Introduction,” p. 304
  - [`Nat.Partition`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.Partition#doc) — [`Mathlib/Combinatorics/Enumerative/Partition/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Partition/Basic.html)
- [x] Partition function p(n) — §14.1, “Introduction,” p. 304
  - [`Fintype.card`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Fintype.card#doc) — [`Mathlib/Data/Fintype/Card.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html)
- [x] Generating function for partitions — §14.3, “Generating functions for partitions,” p. 308
  - [`Nat.Partition.genFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.Partition.genFun#doc) — [`Mathlib/Combinatorics/Enumerative/Partition/GenFun.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Partition/GenFun.html)
```

```
