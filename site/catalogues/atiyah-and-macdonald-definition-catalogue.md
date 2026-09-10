---
title: "Atiyah and Macdonald definition catalogue"
---

# Introduction to Commutative Algebra

Title: *Introduction to Commutative Algebra*

Authors: M. F. Atiyah and I. G. Macdonald

Zotero key: `XL7FDEDH`

Citekey: `AM18`

Source attachment: ``local-write-api-1783448143508-XL7FDEDH_extracted.md``

## Chapter 1. Rings and Ideals

- [x] Ring — Rings and ring homomorphisms, p. 1
  - Mathlib: `Ring` — `Mathlib/Algebra/Ring/Defs.lean`
- [x] Zero ring — Rings and ring homomorphisms, p. 1
  - Lean core: `Subsingleton R` for a ring `R` — `Init/Prelude.lean`
- [x] Ring homomorphism — Rings and ring homomorphisms, p. 2
  - Mathlib: `RingHom` — `Mathlib/Algebra/Ring/Hom/Defs.lean`
- [x] Subring — Rings and ring homomorphisms, p. 2
  - Mathlib: `Subring` — `Mathlib/Algebra/Ring/Subring/Defs.lean`
- [x] Ideal — Ideals. Quotient rings, p. 2
  - Mathlib: `Ideal` — `Mathlib/RingTheory/Ideal/Defs.lean`
- [x] Quotient ring — Ideals. Quotient rings, p. 2
  - Mathlib: `Ideal.Quotient` — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Residue-class ring — Ideals. Quotient rings, p. 2
  - Mathlib: `Ideal.Quotient` — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Kernel of a ring homomorphism — Ideals. Quotient rings, p. 2
  - Mathlib: `RingHom.ker` — `Mathlib/RingTheory/Ideal/Maps.lean:740`
- [x] Image of a ring homomorphism — Ideals. Quotient rings, p. 2
  - Mathlib: `RingHom.range` — `Mathlib/Algebra/Ring/Subring/Basic.lean:241`
- [x] Zero-divisor — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `notMem_nonZeroDivisors_iff` — `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`
- [x] Nilpotent element — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsNilpotent` — `Mathlib/RingTheory/Nilpotent/Basic.lean`
- [x] Unit — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsUnit` — `Mathlib/Algebra/Group/Units/Defs.lean:364`
- [x] Integral domain — Zero-divisors. Nilpotent elements. Units, p. 2
  - Mathlib: `IsDomain` — `Mathlib/Algebra/Ring/Defs.lean:439`
- [x] Principal ideal — Zero-divisors. Nilpotent elements. Units, p. 3
  - Mathlib: `Ideal.span` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Field — Zero-divisors. Nilpotent elements. Units, p. 3
  - Mathlib: `Field` — `Mathlib/Algebra/Field/Defs.lean`
- [x] Prime ideal — Prime ideals and maximal ideals, p. 3
  - Mathlib: `Ideal.IsPrime` — `Mathlib/RingTheory/Ideal/Prime.lean`
- [x] Maximal ideal — Prime ideals and maximal ideals, p. 3
  - Mathlib: `Ideal.IsMaximal` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Local ring — Prime ideals and maximal ideals, p. 4
  - Mathlib: `IsLocalRing` — `Mathlib/RingTheory/LocalRing/Basic.lean`
- [x] Residue field — Prime ideals and maximal ideals, p. 4
  - Mathlib: `Ideal.ResidueField` — `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`
- [x] Semi-local ring — Prime ideals and maximal ideals, p. 4
  - Mathlib: `Finite (MaximalSpectrum R)` — `Mathlib/RingTheory/LocalProperties/Semilocal.lean`
- [x] Nilradical — Nilradical and Jacobson radical, p. 5
  - Mathlib: `nilradical` — `Mathlib/RingTheory/Nilpotent/Lemmas.lean`
- [x] Jacobson radical — Nilradical and Jacobson radical, p. 5
  - Mathlib: `Ring.jacobson` — `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`
- [x] Radical of an ideal — Nilradical and Jacobson radical, p. 5
  - Mathlib: `Ideal.radical` — `Mathlib/RingTheory/Ideal/Operations.lean:799`
- [x] Sum of ideals — Operations on ideals, p. 6
  - Mathlib: `Ideal.add` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Intersection of ideals — Operations on ideals, p. 6
  - Mathlib: `Ideal.inf` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Product of ideals — Operations on ideals, p. 6
  - Mathlib: `Ideal.mul` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Coprime ideals — Operations on ideals, p. 7
  - Mathlib: `IsCoprime` — `Mathlib/RingTheory/Coprime/Basic.lean`
- [x] Annihilator ideal — Operations on ideals, p. 8
  - Mathlib: `Ideal.annihilator` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Quotient of ideals — Operations on ideals, p. 8
  - Mathlib: `Ideal.quotient` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Extension of an ideal — Extension and contraction, p. 9
  - Mathlib: `Ideal.map` — `Mathlib/RingTheory/Ideal/Operations.lean`
- [x] Contraction of an ideal — Extension and contraction, p. 9
  - Mathlib: `Ideal.comap` — `Mathlib/RingTheory/Ideal/Operations.lean`

## Chapter 2. Modules

- [x] Module — Modules and module homomorphisms, p. 17
  - Mathlib: `Module` — `Mathlib/Algebra/Module/Defs.lean`
- [x] Module homomorphism — Modules and module homomorphisms, p. 18
  - Mathlib: `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Kernel of a module homomorphism — Modules and module homomorphisms, p. 18
  - Mathlib: `LinearMap.ker` — `Mathlib/Algebra/Module/Submodule/Ker.lean:60`
- [x] Submodule — Submodules and quotient modules, p. 18
  - Mathlib: `Submodule` — `Mathlib/Algebra/Module/Submodule/Defs.lean`
- [x] Quotient module — Submodules and quotient modules, p. 18
  - Mathlib: `Submodule.Quotient` — `Mathlib/Algebra/Module/Submodule/Basic.lean`
- [x] Sum of submodules — Operations on submodules, p. 19
  - Mathlib: `Submodule.sup` — `Mathlib/Algebra/Module/Submodule/Lattice.lean:197` (⊔ is an operation of the CompleteLattice instance; no standalone def)
- [x] Intersection of submodules — Operations on submodules, p. 19
  - Mathlib: `Submodule.inf` — `Mathlib/Algebra/Module/Submodule/Lattice.lean:197` (⊓ is an operation of the CompleteLattice instance; no standalone def)
- [x] Product of modules — Operations on submodules, p. 19
  - Mathlib: `Pi.module` — `Mathlib/Algebra/Module/Pi.lean`
- [x] Direct sum of modules — Direct sum and product, p. 20
  - Mathlib: `DirectSum` — `Mathlib/Algebra/DirectSum/Basic.lean`
- [x] Direct product of modules — Direct sum and product, p. 20
  - Mathlib: `Pi.module` — `Mathlib/Algebra/Module/Pi.lean`
- [x] Faithful module — Direct sum and product, p. 20
  - Mathlib: `FaithfulSMul` — `Mathlib/Algebra/Module/Defs.lean`
- [x] Generating set of a module — Finitely generated modules, p. 20
  - Mathlib: `Submodule.span` — `Mathlib/LinearAlgebra/Span/Defs.lean:48`
- [x] Finitely generated module — Finitely generated modules, p. 20
  - Mathlib: `Module.Finite` — `Mathlib/RingTheory/Finiteness/Defs.lean`
- [x] Free module — Finitely generated modules, p. 21
  - Mathlib: `Module.Free` — `Mathlib/LinearAlgebra/FreeModule/Basic.lean`
- [x] Exact sequence — Exact sequences, p. 22
  - Mathlib: `Function.Exact` — `Mathlib/Algebra/Exact/Basic.lean`
- [x] Tensor product of modules — Tensor product of modules, p. 24
  - Mathlib: `TensorProduct` — `Mathlib/LinearAlgebra/TensorProduct/Defs.lean`
- [x] Restriction of scalars — Restriction and extension of scalars, p. 27
  - Mathlib: `ModuleCat.restrictScalars` — `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`
- [x] Extension of scalars — Restriction and extension of scalars, p. 27
  - Mathlib: `ModuleCat.extendScalars` — `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`
- [x] Flat module — Exactness properties of the tensor product, p. 29
  - Mathlib: `Module.Flat` — `Mathlib/RingTheory/Flat/Basic.lean`
- [x] Faithfully flat module — Exactness properties of the tensor product, p. 29
  - Mathlib: `Module.FaithfullyFlat` — `Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`
- [x] Algebra over a ring — Algebras, pp. 29–30
  - Mathlib: `Algebra` — `Mathlib/Algebra/Algebra/Basic.lean`
- [x] Algebra homomorphism — Algebras, p. 30
  - Mathlib: `AlgHom` — `Mathlib/Algebra/Algebra/Basic.lean`
- [x] Finite algebra — Algebras, p. 30
  - Mathlib: `Algebra.Finite` — `Mathlib/RingTheory/Finiteness/Defs.lean`
- [x] Algebra of finite type — Algebras, p. 30
  - Mathlib: `Algebra.FiniteType` — `Mathlib/RingTheory/Finiteness/Defs.lean`
- [x] Tensor product of algebras — Tensor product of algebras, p. 30
  - Mathlib: `Algebra.TensorProduct` — `Mathlib/RingTheory/TensorProduct/Basic.lean`

## Chapter 3. Rings and Modules of Fractions

- [x] Multiplicatively closed set — Rings and modules of fractions, p. 36
  - Mathlib: `Submonoid` — `Mathlib/Algebra/Group/Submonoid/Defs.lean`
- [x] Ring of fractions — Rings and modules of fractions, p. 36
  - Mathlib: `Localization` — `Mathlib/RingTheory/Localization/Basic.lean`
- [x] Localization of a ring — Rings and modules of fractions, pp. 36–39
  - Mathlib: `Localization` — `Mathlib/RingTheory/Localization/Basic.lean`
- [x] Module of fractions — Rings and modules of fractions, pp. 36–39
  - Mathlib: `LocalizedModule` — `Mathlib/RingTheory/Localization/Module.lean`
- [x] Localization of a module — Rings and modules of fractions, pp. 36–39
  - Mathlib: `LocalizedModule` — `Mathlib/RingTheory/Localization/Module.lean`
- [x] Local property — Local properties, p. 40
  - Mathlib: `RingHom.PropertyIsLocal` — `Mathlib/RingTheory/LocalProperties/Basic.lean`
- [x] Extended ideal in a ring of fractions — Extended and contracted ideals in rings of fractions, p. 41
  - Mathlib: `Ideal.map` — `Mathlib/RingTheory/Localization/Ideal.lean`
- [x] Contracted ideal in a ring of fractions — Extended and contracted ideals in rings of fractions, p. 41
  - Mathlib: `Ideal.comap` — `Mathlib/RingTheory/Localization/Ideal.lean`

## Chapter 4. Primary Decomposition

- [x] Primary ideal — Primary Decomposition, p. 50
  - Mathlib: `Ideal.IsPrimary` — `Mathlib/RingTheory/Ideal/IsPrimary.lean`
- [x] Primary decomposition — Primary Decomposition, p. 51
  - Mathlib: `Ideal.IsMinimalPrimaryDecomposition` — `Mathlib/RingTheory/Lasker.lean`
- [x] Minimal primary decomposition — Primary Decomposition, pp. 51–52
  - Mathlib: `Ideal.IsMinimalPrimaryDecomposition` — `Mathlib/RingTheory/Lasker.lean`
- [x] Prime ideal associated with a primary decomposition — Primary Decomposition, p. 52
  - Mathlib: `IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes` — `Mathlib/RingTheory/Lasker.lean`
- [x] Isolated prime ideal — Primary Decomposition, p. 52
  - LeanCategories: `LeanCategories.Algebra.Ideal.isolatedPrime` — `LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean`
- [x] Embedded prime ideal — Primary Decomposition, p. 52
  - LeanCategories: `LeanCategories.Algebra.Ideal.embeddedPrime` — `LeanCategories/Algebra/AtiyahMacdonald/PrimaryDecomposition.lean`

## Chapter 5. Integral Dependence and Valuations

- [x] Element integral over a ring — Integral dependence, p. 59
  - Mathlib: `IsIntegral` — `Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean:53`
- [x] Integral algebra — Integral dependence, p. 60
  - Mathlib: `Algebra.IsIntegral` — `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:36`
- [x] Integral closure — Integral dependence, p. 60
  - Mathlib: `integralClosure` — `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:215`
- [x] Integrally closed integral domain — Integrally closed integral domains. The going-down theorem, p. 60
  - Mathlib: `IsIntegrallyClosed` — `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:74`
- [x] Valuation ring — Valuation rings, p. 65
  - Mathlib: `ValuationSubring` — `Mathlib/RingTheory/Valuation/ValuationSubring.lean`

## Chapter 6. Chain Conditions

- [x] Chain of submodules — Chain Conditions, p. 74
  - Mathlib: `RelSeries` — `Mathlib/Order/RelSeries.lean`
- [x] Ascending chain condition — Chain Conditions, p. 74
  - Mathlib: `IsNoetherian` — `Mathlib/RingTheory/Noetherian/Basic.lean`
- [x] Descending chain condition — Chain Conditions, p. 74
  - Mathlib: `IsArtinian` — `Mathlib/RingTheory/Artinian/Defs.lean`
- [x] Noetherian module — Chain Conditions, p. 74
  - Mathlib: `IsNoetherian` — `Mathlib/RingTheory/Noetherian/Basic.lean`
- [x] Artinian module — Chain Conditions, p. 74
  - Mathlib: `IsArtinian` — `Mathlib/RingTheory/Artinian/Defs.lean`
- [x] Composition series — Chain Conditions, p. 76
  - Mathlib: `CompositionSeries` — `Mathlib/Order/JordanHolder.lean:137`
- [x] Length of a module — Chain Conditions, p. 76
  - Mathlib: `Module.length` — `Mathlib/RingTheory/Length.lean`
- [x] Noetherian ring — Chain Conditions, p. 76
  - Mathlib: `IsNoetherianRing` — `Mathlib/RingTheory/Noetherian/Basic.lean`
- [x] Artinian ring — Chain Conditions, p. 76
  - Mathlib: `IsArtinianRing` — `Mathlib/RingTheory/Artinian/Ring.lean`

## Chapter 7. Noetherian Rings

## Chapter 8. Artin Rings

- [x] Dimension of a ring — Artin Rings, p. 90
  - Mathlib: `ringKrullDim` — `Mathlib/RingTheory/KrullDimension/Basic.lean`

## Chapter 9. Discrete Valuation Rings and Dedekind Domains

- [x] Discrete valuation ring — Discrete valuation rings, p. 94
  - Mathlib: `IsDiscreteValuationRing` — `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`
- [x] Dedekind domain — Dedekind domains, p. 95
  - Mathlib: `IsDedekindDomain` — `Mathlib/RingTheory/DedekindDomain/Basic.lean`
- [x] Fractional ideal — Fractional ideals, p. 96
  - Mathlib: `FractionalIdeal` — `Mathlib/RingTheory/FractionalIdeal/Basic.lean`
- [x] Invertible fractional ideal — Fractional ideals, p. 96
  - Mathlib: `FractionalIdeal.IsUnit` — `Mathlib/RingTheory/FractionalIdeal/Basic.lean`

## Chapter 10. Completions

- [x] Topological ring — Topologies and completions, pp. 101–102
  - Mathlib: `TopologicalSpace` — `Mathlib/Topology/Algebra/Ring/Basic.lean`
- [x] Completion — Topologies and completions, p. 102
  - Mathlib: `AdicCompletion` — `Mathlib/RingTheory/AdicCompletion/Basic.lean`
- [x] Inverse limit — Topologies and completions, p. 103
  - Mathlib: `CategoryTheory.Limits.limit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Filtration of a ring — Filtrations, p. 105
  - Mathlib: `Filtration` — `Mathlib/RingTheory/Filtration.lean`
- [x] Filtration of a module — Filtrations, p. 105
  - Mathlib: `Filtration` — `Mathlib/RingTheory/Filtration.lean`
- [x] Adic topology — Filtrations, p. 105
  - Mathlib: `adicTopology` — `Mathlib/RingTheory/AdicCompletion/Basic.lean`
- [x] Graded ring — Graded rings and modules, p. 106
  - Mathlib: `GradedAlgebra` — `Mathlib/RingTheory/GradedAlgebra/Basic.lean`
- [x] Graded module — Graded rings and modules, p. 106
  - Mathlib: `GradedModule` — `Mathlib/Algebra/Module/GradedModule.lean`
- [x] Associated graded ring — The associated graded ring, p. 111
  - Mathlib: `associatedGraded` — `Mathlib/RingTheory/Filtration.lean`
- [x] Associated graded module — The associated graded ring, pp. 111–112
  - Mathlib: `associatedGraded` — `Mathlib/RingTheory/Filtration.lean`
- [x] Zariski ring — The associated graded ring, p. 114
  - Mathlib: `IsZariskiRing` — `Mathlib/RingTheory/Filtration.lean`

## Chapter 11. Dimension Theory

- [x] Poincaré series — Hilbert functions, p. 116
  - LeanCategories: `LeanCategories.Algebra.PoincareSeries` — `LeanCategories/Algebra/DimensionTheory.lean`
- [x] Hilbert function — Hilbert functions, p. 118
  - Mathlib: `hilbertFunction` — `Mathlib/RingTheory/Polynomial/HilbertPoly.lean:110` (as `hilbertPoly`)
- [x] Dimension of a Noetherian local ring — Dimension theory of Noetherian local rings, p. 119
  - Mathlib: `ringKrullDim` — `Mathlib/RingTheory/KrullDimension/Basic.lean`
- [x] Height of a prime ideal — Dimension theory of Noetherian local rings, p. 120
  - Mathlib: `Ideal.height` — `Mathlib/RingTheory/Ideal/Height.lean`
- [x] System of parameters — Dimension theory of Noetherian local rings, p. 122
  - LeanCategories: `LeanCategories.Algebra.IsSystemOfParameters` — `LeanCategories/Algebra/DimensionTheory.lean`
- [x] Regular local ring — Regular local rings, p. 123
  - Mathlib: `IsRegularLocalRing` — `Mathlib/RingTheory/RegularLocalRing/Defs.lean`
- [x] Field of rational functions of an affine variety — Transcendental dimension, p. 124
  - Mathlib: `FractionRing` — `Mathlib/RingTheory/FractionalIdeal/Basic.lean`
- [x] Dimension of an affine variety — Transcendental dimension, p. 124
  - Mathlib: `ringKrullDim` — `Mathlib/RingTheory/KrullDimension/Basic.lean`
- [x] Local dimension of a variety at a point — Transcendental dimension, p. 124
  - Mathlib: `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` — `Mathlib/AlgebraicGeometry/Properties.lean`
