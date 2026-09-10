---
title: "Atiyah and Macdonald definition catalogue"
---

Title: *Introduction to Commutative Algebra*

Authors: M. F. Atiyah and I. G. Macdonald

Zotero key: `XL7FDEDH`

Citekey: `AM18`

Source attachment: ``local-write-api-1783448143508-XL7FDEDH_extracted.md``

## Chapter 1. Rings and Ideals

- [x] Ring — Rings and ring homomorphisms, p. 1
  - Mathlib: `Ring` — [`Mathlib/Algebra/Ring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html)
- [x] Zero ring — Rings and ring homomorphisms, p. 1
  - Lean core: `Subsingleton R` for a ring `R` — `Init/Prelude.lean`
- [x] Ring homomorphism — Rings and ring homomorphisms, p. 2
  - Mathlib: `RingHom` — [`Mathlib/Algebra/Ring/Hom/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Hom/Defs.html)
- [x] Subring — Rings and ring homomorphisms, p. 2
  - Mathlib: `Subring` — [`Mathlib/Algebra/Ring/Subring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Subring/Defs.html)
- [x] Ideal — Ideals. Quotient rings, p. 2
  - Mathlib: `Ideal` — [`Mathlib/RingTheory/Ideal/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Defs.html)
- [x] Quotient ring — Ideals. Quotient rings, p. 2
  - Mathlib: [`Ideal.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.Quotient#doc) — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Residue-class ring — Ideals. Quotient rings, p. 2
  - Mathlib: [`Ideal.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.Quotient#doc) — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Kernel of a ring homomorphism — Ideals. Quotient rings, p. 2
  - Mathlib: [`RingHom.ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RingHom.ker#doc) — `Mathlib/RingTheory/Ideal/Maps.lean:740`
- [x] Image of a ring homomorphism — Ideals. Quotient rings, p. 2
  - Mathlib: [`RingHom.range`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RingHom.range#doc) — `Mathlib/Algebra/Ring/Subring/Basic.lean:241`
- [x] Zero-divisor — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `notMem_nonZeroDivisors_iff` — [`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/NonZeroDivisors.html)
- [x] Nilpotent element — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsNilpotent` — [`Mathlib/RingTheory/Nilpotent/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Basic.html)
- [x] Unit — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsUnit` — `Mathlib/Algebra/Group/Units/Defs.lean:364`
- [x] Integral domain — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsDomain` — `Mathlib/Algebra/Ring/Defs.lean:439`
- [x] Principal ideal — Zero-divisors. Nilpotent elements. Units, p. 3
  - Mathlib: [`Ideal.span`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.span#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Field — Zero-divisors. Nilpotent elements. Units, p. 3
  - Mathlib: `Field` — [`Mathlib/Algebra/Field/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html)
- [x] Prime ideal — Prime ideals and maximal ideals, p. 3
  - Mathlib: [`Ideal.IsPrime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsPrime#doc) — [`Mathlib/RingTheory/Ideal/Prime.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Prime.html)
- [x] Maximal ideal — Prime ideals and maximal ideals, p. 3
  - Mathlib: [`Ideal.IsMaximal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsMaximal#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Local ring — Prime ideals and maximal ideals, p. 4
  - Mathlib: `IsLocalRing` — [`Mathlib/RingTheory/LocalRing/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/Basic.html)
- [x] Residue field — Prime ideals and maximal ideals, p. 4
  - Mathlib: [`Ideal.ResidueField`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.ResidueField#doc) — [`Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/ResidueField/Basic.html)
- [x] Semi-local ring — Prime ideals and maximal ideals, p. 4
  - Mathlib: `Finite (MaximalSpectrum R)` — [`Mathlib/RingTheory/LocalProperties/Semilocal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalProperties/Semilocal.html)
- [x] Nilradical — Nilradical and Jacobson radical, p. 5
  - Mathlib: `nilradical` — [`Mathlib/RingTheory/Nilpotent/Lemmas.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Nilpotent/Lemmas.html)
- [x] Jacobson radical — Nilradical and Jacobson radical, p. 5
  - Mathlib: [`Ring.jacobson`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ring.jacobson#doc) — [`Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.html)
- [x] Radical of an ideal — Nilradical and Jacobson radical, p. 5
  - Mathlib: [`Ideal.radical`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.radical#doc) — `Mathlib/RingTheory/Ideal/Operations.lean:799`
- [x] Sum of ideals — Operations on ideals, p. 6
  - Mathlib: [`Ideal.add`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.add#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Intersection of ideals — Operations on ideals, p. 6
  - Mathlib: [`Ideal.inf`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.inf#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Product of ideals — Operations on ideals, p. 6
  - Mathlib: [`Ideal.mul`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.mul#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Coprime ideals — Operations on ideals, p. 7
  - Mathlib: `IsCoprime` — [`Mathlib/RingTheory/Coprime/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Coprime/Basic.html)
- [x] Annihilator ideal — Operations on ideals, p. 8
  - Mathlib: [`Ideal.annihilator`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.annihilator#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Quotient of ideals — Operations on ideals, p. 8
  - Mathlib: [`Ideal.quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.quotient#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Extension of an ideal — Extension and contraction, p. 9
  - Mathlib: [`Ideal.map`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.map#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Contraction of an ideal — Extension and contraction, p. 9
  - Mathlib: [`Ideal.comap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.comap#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)

## Chapter 2. Modules

- [x] Module — Modules and module homomorphisms, p. 17
  - Mathlib: `Module` — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Module homomorphism — Modules and module homomorphisms, p. 18
  - Mathlib: `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Kernel of a module homomorphism — Modules and module homomorphisms, p. 18
  - Mathlib: [`LinearMap.ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.ker#doc) — `Mathlib/Algebra/Module/Submodule/Ker.lean:60`
- [x] Submodule — Submodules and quotient modules, p. 18
  - Mathlib: `Submodule` — [`Mathlib/Algebra/Module/Submodule/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Defs.html)
- [x] Quotient module — Submodules and quotient modules, p. 18
  - Mathlib: [`Submodule.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.Quotient#doc) — [`Mathlib/Algebra/Module/Submodule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Basic.html)
- [x] Sum of submodules — Operations on submodules, p. 19
  - Mathlib: [`Submodule.sup`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.sup#doc) — `Mathlib/Algebra/Module/Submodule/Lattice.lean:197` (⊔ is an operation of the CompleteLattice instance; no standalone def)
- [x] Intersection of submodules — Operations on submodules, p. 19
  - Mathlib: [`Submodule.inf`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.inf#doc) — `Mathlib/Algebra/Module/Submodule/Lattice.lean:197` (⊓ is an operation of the CompleteLattice instance; no standalone def)
- [x] Product of modules — Operations on submodules, p. 19
  - Mathlib: [`Pi.module`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Pi.module#doc) — [`Mathlib/Algebra/Module/Pi.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Pi.html)
- [x] Direct sum of modules — Direct sum and product, p. 20
  - Mathlib: `DirectSum` — [`Mathlib/Algebra/DirectSum/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html)
- [x] Direct product of modules — Direct sum and product, p. 20
  - Mathlib: [`Pi.module`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Pi.module#doc) — [`Mathlib/Algebra/Module/Pi.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Pi.html)
- [x] Faithful module — Direct sum and product, p. 20
  - Mathlib: `FaithfulSMul` — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Generating set of a module — Finitely generated modules, p. 20
  - Mathlib: [`Submodule.span`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.span#doc) — `Mathlib/LinearAlgebra/Span/Defs.lean:48`
- [x] Finitely generated module — Finitely generated modules, p. 20
  - Mathlib: [`Module.Finite`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Finite#doc) — [`Mathlib/RingTheory/Finiteness/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness/Defs.html)
- [x] Free module — Finitely generated modules, p. 21
  - Mathlib: [`Module.Free`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Free#doc) — [`Mathlib/LinearAlgebra/FreeModule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FreeModule/Basic.html)
- [x] Exact sequence — Exact sequences, p. 22
  - Mathlib: [`Function.Exact`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Function.Exact#doc) — [`Mathlib/Algebra/Exact/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Exact/Basic.html)
- [x] Tensor product of modules — Tensor product of modules, p. 24
  - Mathlib: `TensorProduct` — [`Mathlib/LinearAlgebra/TensorProduct/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorProduct/Defs.html)
- [x] Restriction of scalars — Restriction and extension of scalars, p. 27
  - Mathlib: [`ModuleCat.restrictScalars`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ModuleCat.restrictScalars#doc) — [`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.html)
- [x] Extension of scalars — Restriction and extension of scalars, p. 27
  - Mathlib: [`ModuleCat.extendScalars`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ModuleCat.extendScalars#doc) — [`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.html)
- [x] Flat module — Exactness properties of the tensor product, p. 29
  - Mathlib: [`Module.Flat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Flat#doc) — [`Mathlib/RingTheory/Flat/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Flat/Basic.html)
- [x] Faithfully flat module — Exactness properties of the tensor product, p. 29
  - Mathlib: [`Module.FaithfullyFlat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.FaithfullyFlat#doc) — [`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.html)
- [x] Algebra over a ring — Algebras, pp. 29–30
  - Mathlib: `Algebra` — [`Mathlib/Algebra/Algebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)
- [x] Algebra homomorphism — Algebras, p. 30
  - Mathlib: `AlgHom` — [`Mathlib/Algebra/Algebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)
- [x] Finite algebra — Algebras, p. 30
  - Mathlib: [`Algebra.Finite`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.Finite#doc) — [`Mathlib/RingTheory/Finiteness/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness/Defs.html)
- [x] Algebra of finite type — Algebras, p. 30
  - Mathlib: [`Algebra.FiniteType`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.FiniteType#doc) — [`Mathlib/RingTheory/Finiteness/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness/Defs.html)
- [x] Tensor product of algebras — Tensor product of algebras, p. 30
  - Mathlib: [`Algebra.TensorProduct`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.TensorProduct#doc) — [`Mathlib/RingTheory/TensorProduct/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/Basic.html)

## Chapter 3. Rings and Modules of Fractions

- [x] Multiplicatively closed set — Rings and modules of fractions, p. 36
  - Mathlib: `Submonoid` — [`Mathlib/Algebra/Group/Submonoid/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Submonoid/Defs.html)
- [x] Ring of fractions — Rings and modules of fractions, p. 36
  - Mathlib: `Localization` — [`Mathlib/RingTheory/Localization/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Basic.html)
- [x] Localization of a ring — Rings and modules of fractions, pp. 36–39
  - Mathlib: `Localization` — [`Mathlib/RingTheory/Localization/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Basic.html)
- [x] Module of fractions — Rings and modules of fractions, pp. 36–39
  - Mathlib: `LocalizedModule` — [`Mathlib/RingTheory/Localization/Module.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Module.html)
- [x] Localization of a module — Rings and modules of fractions, pp. 36–39
  - Mathlib: `LocalizedModule` — [`Mathlib/RingTheory/Localization/Module.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Module.html)
- [x] Local property — Local properties, p. 40
  - Mathlib: [`RingHom.PropertyIsLocal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RingHom.PropertyIsLocal#doc) — [`Mathlib/RingTheory/LocalProperties/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalProperties/Basic.html)
- [x] Extended ideal in a ring of fractions — Extended and contracted ideals in rings of fractions, p. 41
  - Mathlib: [`Ideal.map`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.map#doc) — [`Mathlib/RingTheory/Localization/Ideal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Ideal.html)
- [x] Contracted ideal in a ring of fractions — Extended and contracted ideals in rings of fractions, p. 41
  - Mathlib: [`Ideal.comap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.comap#doc) — [`Mathlib/RingTheory/Localization/Ideal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Ideal.html)

## Chapter 4. Primary Decomposition

- [x] Primary ideal — Primary Decomposition, p. 50
  - Mathlib: [`Ideal.IsPrimary`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsPrimary#doc) — [`Mathlib/RingTheory/Ideal/IsPrimary.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/IsPrimary.html)
- [x] Primary decomposition — Primary Decomposition, p. 51
  - Mathlib: [`Ideal.IsMinimalPrimaryDecomposition`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsMinimalPrimaryDecomposition#doc) — [`Mathlib/RingTheory/Lasker.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Lasker.html)
- [x] Minimal primary decomposition — Primary Decomposition, pp. 51–52
  - Mathlib: [`Ideal.IsMinimalPrimaryDecomposition`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsMinimalPrimaryDecomposition#doc) — [`Mathlib/RingTheory/Lasker.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Lasker.html)
- [x] Prime ideal associated with a primary decomposition — Primary Decomposition, p. 52
  - Mathlib: [`IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes#doc) — [`Mathlib/RingTheory/Lasker.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Lasker.html)
- [x] Isolated prime ideal — Primary Decomposition, p. 52
  - LeanCategories: [`LeanCategories.Algebra.Ideal.isolatedPrime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.Ideal.isolatedPrime#doc) — [`LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean)
- [x] Embedded prime ideal — Primary Decomposition, p. 52
  - LeanCategories: [`LeanCategories.Algebra.Ideal.embeddedPrime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.Ideal.embeddedPrime#doc) — [`LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean)

## Chapter 5. Integral Dependence and Valuations

- [x] Element integral over a ring — Integral dependence, p. 59
  - Mathlib: `IsIntegral` — `Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean:53`
- [x] Integral algebra — Integral dependence, p. 60
  - Mathlib: [`Algebra.IsIntegral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.IsIntegral#doc) — `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:36`
- [x] Integral closure — Integral dependence, p. 60
  - Mathlib: `integralClosure` — `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:215`
- [x] Integrally closed integral domain — Integrally closed integral domains. The going-down theorem, p. 60
  - Mathlib: `IsIntegrallyClosed` — `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:74`
- [x] Valuation ring — Valuation rings, p. 65
  - Mathlib: `ValuationSubring` — [`Mathlib/RingTheory/Valuation/ValuationSubring.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Valuation/ValuationSubring.html)

## Chapter 6. Chain Conditions

- [x] Chain of submodules — Chain Conditions, p. 74
  - Mathlib: `RelSeries` — [`Mathlib/Order/RelSeries.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/RelSeries.html)
- [x] Ascending chain condition — Chain Conditions, p. 74
  - Mathlib: `IsNoetherian` — [`Mathlib/RingTheory/Noetherian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Basic.html)
- [x] Descending chain condition — Chain Conditions, p. 74
  - Mathlib: `IsArtinian` — [`Mathlib/RingTheory/Artinian/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Defs.html)
- [x] Noetherian module — Chain Conditions, p. 74
  - Mathlib: `IsNoetherian` — [`Mathlib/RingTheory/Noetherian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Basic.html)
- [x] Artinian module — Chain Conditions, p. 74
  - Mathlib: `IsArtinian` — [`Mathlib/RingTheory/Artinian/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Defs.html)
- [x] Composition series — Chain Conditions, p. 76
  - Mathlib: `CompositionSeries` — `Mathlib/Order/JordanHolder.lean:137`
- [x] Length of a module — Chain Conditions, p. 76
  - Mathlib: [`Module.length`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.length#doc) — [`Mathlib/RingTheory/Length.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Length.html)
- [x] Noetherian ring — Chain Conditions, p. 76
  - Mathlib: `IsNoetherianRing` — [`Mathlib/RingTheory/Noetherian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Basic.html)
- [x] Artinian ring — Chain Conditions, p. 76
  - Mathlib: `IsArtinianRing` — [`Mathlib/RingTheory/Artinian/Ring.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Ring.html)

## Chapter 7. Noetherian Rings

## Chapter 8. Artin Rings

- [x] Dimension of a ring — Artin Rings, p. 90
  - Mathlib: `ringKrullDim` — [`Mathlib/RingTheory/KrullDimension/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/KrullDimension/Basic.html)

## Chapter 9. Discrete Valuation Rings and Dedekind Domains

- [x] Discrete valuation ring — Discrete valuation rings, p. 94
  - Mathlib: `IsDiscreteValuationRing` — [`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DiscreteValuationRing/Basic.html)
- [x] Dedekind domain — Dedekind domains, p. 95
  - Mathlib: `IsDedekindDomain` — [`Mathlib/RingTheory/DedekindDomain/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Basic.html)
- [x] Fractional ideal — Fractional ideals, p. 96
  - Mathlib: `FractionalIdeal` — [`Mathlib/RingTheory/FractionalIdeal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/FractionalIdeal/Basic.html)
- [x] Invertible fractional ideal — Fractional ideals, p. 96
  - Mathlib: [`FractionalIdeal.IsUnit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FractionalIdeal.IsUnit#doc) — [`Mathlib/RingTheory/FractionalIdeal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/FractionalIdeal/Basic.html)

## Chapter 10. Completions

- [x] Topological ring — Topologies and completions, pp. 101–102
  - Mathlib: `TopologicalSpace` — [`Mathlib/Topology/Algebra/Ring/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Ring/Basic.html)
- [x] Completion — Topologies and completions, p. 102
  - Mathlib: `AdicCompletion` — [`Mathlib/RingTheory/AdicCompletion/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/Basic.html)
- [x] Inverse limit — Topologies and completions, p. 103
  - Mathlib: [`CategoryTheory.Limits.limit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.limit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Filtration of a ring — Filtrations, p. 105
  - Mathlib: `Filtration` — [`Mathlib/RingTheory/Filtration.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Filtration.html)
- [x] Filtration of a module — Filtrations, p. 105
  - Mathlib: `Filtration` — [`Mathlib/RingTheory/Filtration.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Filtration.html)
- [x] Adic topology — Filtrations, p. 105
  - Mathlib: `adicTopology` — [`Mathlib/RingTheory/AdicCompletion/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/Basic.html)
- [x] Graded ring — Graded rings and modules, p. 106
  - Mathlib: `GradedAlgebra` — [`Mathlib/RingTheory/GradedAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/GradedAlgebra/Basic.html)
- [x] Graded module — Graded rings and modules, p. 106
  - Mathlib: `GradedModule` — [`Mathlib/Algebra/Module/GradedModule.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/GradedModule.html)
- [x] Associated graded ring — The associated graded ring, p. 111
  - Mathlib: `associatedGraded` — [`Mathlib/RingTheory/Filtration.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Filtration.html)
- [x] Associated graded module — The associated graded ring, pp. 111–112
  - Mathlib: `associatedGraded` — [`Mathlib/RingTheory/Filtration.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Filtration.html)
- [x] Zariski ring — The associated graded ring, p. 114
  - Mathlib: `IsZariskiRing` — [`Mathlib/RingTheory/Filtration.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Filtration.html)

## Chapter 11. Dimension Theory

- [x] Poincaré series — Hilbert functions, p. 116
  - LeanCategories: [`LeanCategories.Algebra.PoincareSeries`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.PoincareSeries#doc) — [`LeanCategories/Algebra/DimensionTheory.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/DimensionTheory.lean)
- [x] Hilbert function — Hilbert functions, p. 118
  - Mathlib: `hilbertFunction` — `Mathlib/RingTheory/Polynomial/HilbertPoly.lean:110` (as `hilbertPoly`)
- [x] Dimension of a Noetherian local ring — Dimension theory of Noetherian local rings, p. 119
  - Mathlib: `ringKrullDim` — [`Mathlib/RingTheory/KrullDimension/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/KrullDimension/Basic.html)
- [x] Height of a prime ideal — Dimension theory of Noetherian local rings, p. 120
  - Mathlib: [`Ideal.height`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.height#doc) — [`Mathlib/RingTheory/Ideal/Height.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Height.html)
- [x] System of parameters — Dimension theory of Noetherian local rings, p. 122
  - LeanCategories: [`LeanCategories.Algebra.IsSystemOfParameters`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.IsSystemOfParameters#doc) — [`LeanCategories/Algebra/DimensionTheory.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/DimensionTheory.lean)
- [x] Regular local ring — Regular local rings, p. 123
  - Mathlib: `IsRegularLocalRing` — [`Mathlib/RingTheory/RegularLocalRing/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RegularLocalRing/Defs.html)
- [x] Field of rational functions of an affine variety — Transcendental dimension, p. 124
  - Mathlib: `FractionRing` — [`Mathlib/RingTheory/FractionalIdeal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/FractionalIdeal/Basic.html)
- [x] Dimension of an affine variety — Transcendental dimension, p. 124
  - Mathlib: `ringKrullDim` — [`Mathlib/RingTheory/KrullDimension/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/KrullDimension/Basic.html)
- [x] Local dimension of a variety at a point — Transcendental dimension, p. 124
  - Mathlib: [`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.ringKrullDim_stalk_eq_coheight#doc) — [`Mathlib/AlgebraicGeometry/Properties.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Properties.html)
