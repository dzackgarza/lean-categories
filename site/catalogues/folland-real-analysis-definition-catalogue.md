---
title: "Folland real analysis definition catalogue"
---

``` markdown #projects/github.com__dzackgarza__lean-categories/references/folland-real-analysis-definition-catalogue
# Folland real analysis definition catalogue

``` markdown #projects/github.com__dzackgarza__lean-categories/references/folland-real-analysis-definition-catalogue

# Folland real analysis definition catalogue

``` markdown #projects/github.com__dzackgarza__lean-categories/references/folland-real-analysis-definition-catalogue

# Folland real analysis definition catalogue

# Folland real analysis definition catalogue

# Folland real analysis definition catalogue

# Real Analysis: definition catalogue

Title: *Real Analysis: Modern Techniques and Their Applications*, second edition

Author: Gerald B. Folland

Zotero key: `FAE4HS67`

Citekey: `Fol13`

Source attachment: ``local-write-api-1783336781793-FAE4HS67_extracted.md``

## Chapter 0: Prologue

- [x] Set — §0.1, The Language of Set Theory, p. 1
  - `Set` — `Mathlib/Data/Set/Defs.lean`
- [x] Relation — §0.1, The Language of Set Theory, p. 1
  - `Relation` — `Mathlib/Logic/Relation.lean`
- [x] Equivalence relation — §0.1, The Language of Set Theory, p. 1
  - `Setoid` — `Mathlib/Data/Setoid/Basic.lean`
- [x] Mapping — §0.1, The Language of Set Theory, p. 1
  - `Function` — `Mathlib/Logic/Function/Basic.lean`
- [x] Sequence — §0.1, The Language of Set Theory, p. 1
  - `Function` — `Mathlib/Logic/Function/Basic.lean`
- [x] Cartesian product — §0.1, The Language of Set Theory, p. 1
  - `Prod` — `Mathlib/Data/Prod/Basic.lean`
- [x] Partial order — §0.2, Orderings, p. 4
  - `PartialOrder` — `Mathlib/Order/Defs/PartialOrder.lean`
- [x] Linear order — §0.2, Orderings, p. 4
  - `LinearOrder` — `Mathlib/Order/Defs/LinearOrder.lean`
- [x] Well ordering — §0.2, Orderings, p. 4
  - `IsWellOrder` — `Mathlib/Order/RelClasses.lean`
- [x] Cardinality — §0.3, Cardinality, p. 6
  - `Cardinal` — `Mathlib/SetTheory/Cardinal/Defs.lean`
- [x] Countable set — §0.3, Cardinality, p. 6
  - `Set.Countable` — `Mathlib/Data/Set/Countable.lean`
- [x] Ordinal number — §0.4, More about Well Ordered Sets, p. 9
  - `Ordinal` — `Mathlib/SetTheory/Ordinal/Basic.lean`
- [x] Extended real number system — §0.5, The Extended Real Number System, p. 10
  - `EReal` — `Mathlib/Data/EReal/Basic.lean`
- [x] Metric space — §0.6, Metric Spaces, p. 13
  - `MetricSpace` — `Mathlib/Topology/MetricSpace/Defs.lean`
- [x] Open ball — §0.6, Metric Spaces, p. 13
  - `Metric.ball` — `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- [x] Open set — §0.6, Metric Spaces, p. 13
  - `IsOpen` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Closed set — §0.6, Metric Spaces, p. 13
  - `IsClosed` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Interior — §0.6, Metric Spaces, p. 13
  - `interior` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Closure — §0.6, Metric Spaces, p. 13
  - `closure` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Dense subset — §0.6, Metric Spaces, p. 13
  - `Dense` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Separable metric space — §0.6, Metric Spaces, p. 13
  - `SeparableSpace` — `Mathlib/Topology/Bases.lean`
- [x] Cauchy sequence — §0.6, Metric Spaces, p. 13
  - `CauchySeq` — `Mathlib/Topology/UniformSpace/Cauchy.lean`
- [x] Complete metric space — §0.6, Metric Spaces, p. 13
  - `CompleteSpace` — `Mathlib/Topology/UniformSpace/Cauchy.lean`
- [x] Totally bounded set — §0.6, Metric Spaces, p. 13
  - `TotallyBounded` — `Mathlib/Topology/UniformSpace/Cauchy.lean`
- [x] Compact set — §0.6, Metric Spaces, p. 13
  - `IsCompact` — `Mathlib/Topology/Defs/Filter.lean`

## Chapter 1: Measures

- [x] Algebra of sets — §1.2, Sigma-algebras, p. 21
  - Mathlib: `MeasureTheory.IsSetAlgebra` — `Mathlib/MeasureTheory/SetAlgebra.lean`
- [x] Sigma-algebra — §1.2, Sigma-algebras, p. 21
  - `MeasurableSpace` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Generated sigma-algebra — §1.2, Sigma-algebras, p. 21
  - `MeasurableSpace.generateFrom` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Borel sigma-algebra — §1.2, Sigma-algebras, p. 21
  - `borel` — `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- [x] Measurable space — §1.2, Sigma-algebras, p. 21
  - `MeasurableSpace` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Measure — §1.3, Measures, p. 24
  - `Measure` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- [x] Measure space — §1.3, Measures, p. 24
  - `MeasureSpace` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- [x] Finite measure — §1.3, Measures, p. 24
  - `IsFiniteMeasure` — `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- [x] Sigma-finite measure — §1.3, Measures, p. 24
  - `SigmaFinite` — `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- [ ] Semifinite measure — §1.3, Measures, p. 24
- [x] Complete measure — §1.3, Measures, p. 24
  - `Measure.IsComplete` — `Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- [x] Outer measure — §1.4, Outer Measures, p. 28
  - `OuterMeasure` — `Mathlib/MeasureTheory/OuterMeasure/Defs.lean`
- [x] Caratheodory measurable set — §1.4, Outer Measures, p. 28
  - `OuterMeasure.caratheodory` — `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- [x] Lebesgue measure — §1.5, Borel Measures on the Real Line, p. 33
  - `volume` — `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- [x] Lebesgue measurable set — §1.5, Borel Measures on the Real Line, p. 33
  - `MeasurableSet` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Lebesgue-Stieltjes measure — §1.5, Borel Measures on the Real Line, p. 33
  - `StieltjesFunction.measure` — `Mathlib/MeasureTheory/Measure/Stieltjes.lean`

## Chapter 2: Integration

- [x] Measurable function — §2.1, Measurable Functions, p. 43
  - `Measurable` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Borel measurable function — §2.1, Measurable Functions, p. 43
  - `Measurable` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Simple function — §2.1, Measurable Functions, p. 43
  - `MeasureTheory.SimpleFunc` — `Mathlib/MeasureTheory/Function/SimpleFunc.lean`
- [x] Integral of a nonnegative simple function — §2.2, Integration of Nonnegative Functions, p. 49
  - `MeasureTheory.SimpleFunc.lintegral` — `Mathlib/MeasureTheory/Function/SimpleFunc.lean`
- [x] Integral of a nonnegative measurable function — §2.2, Integration of Nonnegative Functions, p. 49
  - `MeasureTheory.lintegral` — `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- [x] Integrable complex function — §2.3, Integration of Complex Functions, p. 52
  - `MeasureTheory.Integrable` — `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- [x] Integral of a complex function — §2.3, Integration of Complex Functions, p. 52
  - `MeasureTheory.integral` — `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- [x] Almost everywhere — §2.3, Integration of Complex Functions, p. 52
  - `ae` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- [x] Convergence almost everywhere — §2.4, Modes of Convergence, p. 60
  - `Filter.Tendsto` — `Mathlib/Order/Filter/Defs.lean`
- [x] Convergence in measure — §2.4, Modes of Convergence, p. 60
  - `MeasureTheory.TendstoInMeasure` — `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- [x] Convergence in L1 — §2.4, Modes of Convergence, p. 60
  - `MeasureTheory.L1` — `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
- [x] Product sigma-algebra — §2.5, Product Measures, p. 64
  - `MeasurableSpace.prod` — `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- [x] Product measure — §2.5, Product Measures, p. 64
  - `Measure.prod` — `Mathlib/MeasureTheory/Measure/Prod.lean:171`
- [ ] Section of a measurable set — §2.5, Product Measures, p. 64
- [x] Lebesgue integral on Euclidean space — §2.6, The n-dimensional Lebesgue Integral, p. 70
  - `MeasureTheory.integral` — `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- [x] Polar coordinates — §2.7, Integration in Polar Coordinates, p. 77
  - `Complex.polarCoord` — `Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`

## Chapter 3: Signed Measures and Differentiation

- [x] Signed measure — §3.1, Signed Measures, p. 85
  - `SignedMeasure` — `Mathlib/MeasureTheory/VectorMeasure/Basic.lean`
- [ ] Positive set for a signed measure — §3.1, Signed Measures, p. 85
- [ ] Negative set for a signed measure — §3.1, Signed Measures, p. 85
- [x] Mutually singular measures — §3.1, Signed Measures, p. 85
  - `Measure.MutuallySingular` — `Mathlib/MeasureTheory/Measure/MutuallySingular.lean`
- [x] Total variation measure — §3.1, Signed Measures, p. 85
  - `SignedMeasure.totalVariation` — `Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`
- [x] Absolute continuity of measures — §3.2, The Lebesgue-Radon-Nikodym Theorem, p. 88
  - `Measure.AbsolutelyContinuous` — `Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- [x] Radon-Nikodym derivative — §3.2, The Lebesgue-Radon-Nikodym Theorem, p. 88
  - `Measure.rnDeriv` — `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- [x] Complex measure — §3.3, Complex Measures, p. 93
  - `ComplexMeasure` — `Mathlib/MeasureTheory/Measure/Complex.lean`
- [ ] Lebesgue point — §3.4, Differentiation on Euclidean Space, p. 95
- [x] Function of bounded variation — §3.5, Functions of Bounded Variation, p. 100
  - `BoundedVariationOn` — `Mathlib/Topology/EMetricSpace/BoundedVariation.lean`
- [x] Total variation function — §3.5, Functions of Bounded Variation, p. 100
  - `variationOnFromTo` — `Mathlib/Topology/EMetricSpace/VariationOnFromTo.lean`
- [x] Absolutely continuous function — §3.5, Functions of Bounded Variation, p. 100
  - `AbsolutelyContinuousOnInterval` — `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`

## Chapter 4: Point Set Topology

- [x] Topological space — §4.1, Topological Spaces, p. 113
  - `TopologicalSpace` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Neighborhood — §4.1, Topological Spaces, p. 113
  - `nhds` — `Mathlib/Topology/Defs/Filter.lean`
- [x] Base for a topology — §4.1, Topological Spaces, p. 113
  - `IsTopologicalBasis` — `Mathlib/Topology/Bases.lean`
- [x] Subbase for a topology — §4.1, Topological Spaces, p. 113
  - `TopologicalSpace.generateFrom` — `Mathlib/Topology/Order.lean`
- [x] Subspace topology — §4.1, Topological Spaces, p. 113
  - `TopologicalSpace.induced` — `Mathlib/Topology/Defs/Induced.lean`
- [x] Product topology — §4.1, Topological Spaces, p. 113
  - `instTopologicalSpaceProd` — `Mathlib/Topology/Constructions.lean`
- [x] Hausdorff space — §4.1, Topological Spaces, p. 113
  - `T2Space` — `Mathlib/Topology/Separation/Hausdorff.lean`
- [x] Continuous map — §4.2, Continuous Maps, p. 119
  - `Continuous` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Homeomorphism — §4.2, Continuous Maps, p. 119
  - `Homeomorph` — `Mathlib/Topology/Homeomorph/Defs.lean`
- [x] Quotient topology — §4.2, Continuous Maps, p. 119
  - `TopologicalSpace.coinduced` — `Mathlib/Topology/Defs/Induced.lean`
- [x] Net — §4.3, Nets, p. 125
  - Mathlib: `Filter` — `Mathlib/Order/Filter/Defs.lean`
- [x] Subnet — §4.3, Nets, p. 125
  - Mathlib: `Filter.Tendsto` — `Mathlib/Order/Filter/Defs.lean`
- [x] Compact space — §4.4, Compact Spaces, p. 128
  - `CompactSpace` — `Mathlib/Topology/Defs/Filter.lean`
- [x] Relatively compact set — §4.4, Compact Spaces, p. 128
  - Mathlib: `IsCompact (closure s)` — `Mathlib/Topology/Separation/Basic.lean`
- [x] Locally compact space — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - `LocallyCompactSpace` — `Mathlib/Topology/Defs/Filter.lean`
- [x] One-point compactification — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - `OnePoint` — `Mathlib/Topology/Compactification/OnePoint/Basic.lean`
- [x] Compact-open topology — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - `ContinuousMap.compactOpen` — `Mathlib/Topology/CompactOpen.lean`
- [ ] Uniform algebra — §4.7, The Stone-Weierstrass Theorem, p. 138
- [x] Completely regular space — §4.8, Embeddings in Cubes, p. 143
  - `CompletelyRegularSpace` — `Mathlib/Topology/Separation/CompletelyRegular.lean`
- [x] Normal space — §4.8, Embeddings in Cubes, p. 143
  - `NormalSpace` — `Mathlib/Topology/Separation/Regular.lean`

## Chapter 5: Elements of Functional Analysis

- [x] Normed vector space — §5.1, Normed Vector Spaces, p. 151
  - `NormedSpace` — `Mathlib/Analysis/Normed/Module/Basic.lean`
- [x] Banach space — §5.1, Normed Vector Spaces, p. 151
  - `CompleteSpace` — `Mathlib/Topology/UniformSpace/Cauchy.lean`
- [x] Bounded linear map — §5.1, Normed Vector Spaces, p. 151
  - `ContinuousLinearMap` — `Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- [x] Operator norm — §5.1, Normed Vector Spaces, p. 151
  - `ContinuousLinearMap.opNorm` — `Mathlib/Analysis/Normed/Operator/Basic.lean`
- [x] Linear functional — §5.2, Linear Functionals, p. 157
  - `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Dual space — §5.2, Linear Functionals, p. 157
  - `NormedSpace.Dual` — `Mathlib/Analysis/Normed/Module/Dual.lean`
- [x] Weak topology — §5.2, Linear Functionals, p. 157
  - `WeakBilin` — `Mathlib/Topology/Algebra/Module/Spaces/WeakBilin.lean:64`
- [x] Weak-star topology — §5.2, Linear Functionals, p. 157
  - `WeakDual` — `Mathlib/Topology/Algebra/Module/WeakDual.lean`
- [x] Meager set — §5.3, The Baire Category Theorem and its Consequences, p. 161
  - `IsMeagre` — `Mathlib/Topology/GDelta/Basic.lean`
- [x] Baire space — §5.3, The Baire Category Theorem and its Consequences, p. 161
  - `BaireSpace` — `Mathlib/Topology/Defs/Basic.lean`
- [x] Topological vector space — §5.4, Topological Vector Spaces, p. 165
  - `ContinuousSMul` — `Mathlib/Topology/Algebra/Module/Basic.lean`
- [x] Locally convex space — §5.4, Topological Vector Spaces, p. 165
  - `LocallyConvexSpace` — `Mathlib/Topology/Algebra/Module/LocallyConvex.lean`
- [x] Seminorm — §5.4, Topological Vector Spaces, p. 165
  - `Seminorm` — `Mathlib/Analysis/Seminorm.lean`
- [x] Inner product space — §5.5, Hilbert Spaces, p. 171
  - `InnerProductSpace` — `Mathlib/Analysis/InnerProductSpace/Defs.lean`
- [x] Hilbert space — §5.5, Hilbert Spaces, p. 171
  - `CompleteSpace` — `Mathlib/Topology/UniformSpace/Cauchy.lean`
- [x] Orthogonal complement — §5.5, Hilbert Spaces, p. 171
  - `Submodule.orthogonal` — `Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- [x] Orthonormal set — §5.5, Hilbert Spaces, p. 171
  - `Orthonormal` — `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- [x] Complete orthonormal set — §5.5, Hilbert Spaces, p. 171
  - `OrthonormalBasis` — `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`

## Chapter 6: Lp Spaces

- [x] Lp space — §6.1, Basic Theory of Lp Spaces, p. 181
  - `MeasureTheory.Lp` — `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
- [x] Essential supremum — §6.1, Basic Theory of Lp Spaces, p. 181
  - `MeasureTheory.essSup` — `Mathlib/MeasureTheory/Function/EssSup.lean`
- [x] L-infinity space — §6.1, Basic Theory of Lp Spaces, p. 181
  - `MeasureTheory.Lp` — `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
- [x] Conjugate exponents — §6.1, Basic Theory of Lp Spaces, p. 181
  - `IsConjExponent` — `Mathlib/Analysis/MeanInequalities.lean`
- [x] Dual of an Lp space — §6.2, The Dual of Lp, p. 188
  - `NormedSpace.Dual` — `Mathlib/Analysis/Normed/Module/Dual.lean`
- [x] Distribution function — §6.4, Distribution Functions and Weak Lp, p. 197
  - `MeasureTheory.distribution` — `fpvandoorn/BonnAnalysis:BonnAnalysis/LorentzSpace.lean`
- [x] Weak Lp space — §6.4, Distribution Functions and Weak Lp, p. 197
  - `MeasureTheory.Lorentz` (q = ∞) — `fpvandoorn/BonnAnalysis:BonnAnalysis/LorentzSpace.lean`
- [ ] Analytic family of operators — §6.5, Interpolation of Lp Spaces, p. 200

## Chapter 7: Radon Measures

- [x] Positive linear functional on Cc(X) — §7.1, Positive Linear Functionals on Cc(X), p. 211
  - `PositiveLinearMap` — `Mathlib/Algebra/Order/Module/PositiveLinearMap.lean`
- [x] Radon measure — §7.2, Regularity and Approximation Theorems, p. 216
  - `Measure.IsRadon` — `Mathlib/MeasureTheory/Measure/Regular.lean`
- [x] Outer regular measure — §7.2, Regularity and Approximation Theorems, p. 216
  - `Measure.OuterRegular` — `Mathlib/MeasureTheory/Measure/Regular.lean`
- [x] Inner regular measure — §7.2, Regularity and Approximation Theorems, p. 216
  - `Measure.InnerRegular` — `Mathlib/MeasureTheory/Measure/Regular.lean`
- [x] C0(X) — §7.3, The Dual of C0(X), p. 221
  - `CocompactMap` — `Mathlib/Topology/ContinuousMap/CocompactMap.lean`
- [x] Product of Radon measures — §7.4, Products of Radon Measures, p. 226
  - `Measure.prod` — `Mathlib/MeasureTheory/Measure/Prod.lean:171`

## Chapter 8: Elements of Fourier Analysis

- [x] Translation operator — §8.1, Preliminaries, p. 235
  - `translate` — `Mathlib/Algebra/Group/Translate.lean`
- [ ] Dilation operator — §8.1, Preliminaries, p. 235
- [x] Convolution — §8.2, Convolutions, p. 239
  - `MeasureTheory.convolution` — `Mathlib/Analysis/Convolution.lean`
- [x] Approximate identity — §8.2, Convolutions, p. 239
  - `TauCeti.IsMollifier` — `TauCetiProject/TauCeti:TauCeti/RepresentationTheory/Compact/ApproximateIdentity.lean`
- [x] Fourier transform — §8.3, The Fourier Transform, p. 247
  - `FourierTransform` — `Mathlib/Analysis/Fourier/Notation.lean`
- [x] Inverse Fourier transform — §8.3, The Fourier Transform, p. 247
  - `FourierTransformInv` — `Mathlib/Analysis/Fourier/Notation.lean`
- [x] Fourier series — §8.4, Summation of Fourier Integrals and Series, p. 257
  - `fourierCoeff` — `Mathlib/Analysis/Fourier/AddCircle.lean`
- [ ] Summability kernel — §8.4, Summation of Fourier Integrals and Series, p. 257
- [x] Fourier-Stieltjes transform — §8.6, Fourier Analysis of Measures, p. 270
  - `MeasureTheory.charFun` — `Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`
- [x] Fundamental solution of a differential operator — §8.7, Applications to Partial Differential Equations, p. 273
  - `DifferentialOperators.IsTemperedFundamentalSolution` — `facebookresearch/atlas-lean:Atlas/DifferentialAnalysis/code/DifferentialOperators.lean`

## Chapter 9: Elements of Distribution Theory

- [x] Test function — §9.1, Distributions, p. 281
  - `TestFunction` — `Mathlib/Analysis/Distribution/TestFunction.lean`
- [x] Distribution — §9.1, Distributions, p. 281
  - `Distribution` — `Mathlib/Analysis/Distribution/Distribution.lean`
- [x] Distributional derivative — §9.1, Distributions, p. 281
  - `Distribution.lineDerivCLM` — `Mathlib/Analysis/Distribution/Distribution.lean`
- [x] Support of a distribution — §9.1, Distributions, p. 281
  - `dsupport` — `Mathlib/Analysis/Distribution/Support.lean`
- [x] Compactly supported distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - `IsCompactlySupportedDistribution` — `facebookresearch/atlas-lean:Atlas/DifferentialAnalysis/code/WavefrontSet.lean`
- [x] Tempered distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - `TemperedDistribution` — `Mathlib/Analysis/Distribution/TemperedDistribution.lean`
- [ ] Periodic distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
- [x] Fourier transform of a tempered distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - `FourierTransform.fourierCLM` — `Mathlib/Analysis/Fourier/Notation.lean:181` (was `TemperedDistribution.fourierTransformCLM`, a deprecated alias)
- [x] Sobolev space — §9.3, Sobolev Spaces, p. 301
  - `TemperedDistribution.MemSobolev` — `Mathlib/Analysis/Distribution/Sobolev.lean`
- [x] Weak derivative — §9.3, Sobolev Spaces, p. 301
  - `Distribution.lineDerivCLM` — `Mathlib/Analysis/Distribution/Distribution.lean`

## Chapter 10: Topics in Probability Theory

- [x] Probability space — §10.1, Basic Concepts, p. 313
  - `Measure.IsProbabilityMeasure` — `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`
- [x] Random variable — §10.1, Basic Concepts, p. 313
  - `Measurable` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- [x] Distribution of a random variable — §10.1, Basic Concepts, p. 313
  - `Measure.map` — `Mathlib/MeasureTheory/Measure/Map.lean`
- [x] Expectation — §10.1, Basic Concepts, p. 313
  - `MeasureTheory.integral` — `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- [x] Independence — §10.1, Basic Concepts, p. 313
  - `ProbabilityTheory.Indep` — `Mathlib/Probability/Independence/Basic.lean`
- [x] Identically distributed random variables — §10.1, Basic Concepts, p. 313
  - `ProbabilityTheory.IdentDistrib` — `Mathlib/Probability/IdentDistrib.lean`
- [x] Convergence in probability — §10.1, Basic Concepts, p. 313
  - `MeasureTheory.TendstoInMeasure` — `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- [x] Convergence in distribution — §10.1, Basic Concepts, p. 313
  - `MeasureTheory.TendstoInDistribution` — `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`
- [x] Characteristic function — §10.3, The Central Limit Theorem, p. 325
  - `Measure.charFun` — `Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`
- [x] Product probability space — §10.4, Construction of Sample Spaces, p. 328
  - `Measure.prod` — `Mathlib/MeasureTheory/Measure/Prod.lean:171`
- [x] Wiener process — §10.5, The Wiener Process, p. 330
  - `ProbabilityTheory.IsBrownianReal` — `Mathlib/Probability/BrownianMotion/Basic.lean`

## Chapter 11: More Measures and Integrals

- [x] Topological group — §11.1, Topological Groups and Haar Measure, p. 339
  - `IsTopologicalGroup` — `Mathlib/Topology/Algebra/Group/Defs.lean`
- [x] Left Haar measure — §11.1, Topological Groups and Haar Measure, p. 339
  - `MeasureTheory.IsHaarMeasure` — `Mathlib/MeasureTheory/Group/Measure.lean`
- [x] Right Haar measure — §11.1, Topological Groups and Haar Measure, p. 339
  - `MeasureTheory.IsMulRightInvariant` — `Mathlib/MeasureTheory/Group/Defs.lean`
- [x] Modular function — §11.1, Topological Groups and Haar Measure, p. 339
  - `MeasureTheory.modularCharacter` — `Mathlib/MeasureTheory/Group/ModularCharacter.lean`
- [x] Hausdorff measure — §11.2, Hausdorff Measure, p. 348
  - `MeasureTheory.hausdorffMeasure` — `Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- [x] Hausdorff dimension — §11.2, Hausdorff Measure, p. 348
  - `MeasureTheory.dimH` — `Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- [x] Similarity — §11.3, Self-similarity and Hausdorff Dimension, p. 355
  - `Dilation` — `Mathlib/Topology/MetricSpace/Dilation.lean`
- [ ] Self-similar set — §11.3, Self-similarity and Hausdorff Dimension, p. 355
- [x] Differential form — §11.4, Integration on Manifolds, p. 361
  - `DifferentialForm` — (no Mathlib declaration)
- [x] Integral of a differential form — §11.4, Integration on Manifolds, p. 361
  - `curveIntegral`, `CurveIntegrable` — `Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`
```

```

```
