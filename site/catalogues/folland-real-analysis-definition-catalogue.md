---
title: "Folland real analysis definition catalogue"
---

Title: *Real Analysis: Modern Techniques and Their Applications*, second edition

Author: Gerald B. Folland

Zotero key: `FAE4HS67`

Citekey: `Fol13`

Source attachment: ``local-write-api-1783336781793-FAE4HS67_extracted.md``

## Chapter 0: Prologue

- [x] Set — §0.1, The Language of Set Theory, p. 1
  - `Set` — [`Mathlib/Data/Set/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html)
- [x] Relation — §0.1, The Language of Set Theory, p. 1
  - `Relation` — [`Mathlib/Logic/Relation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html)
- [x] Equivalence relation — §0.1, The Language of Set Theory, p. 1
  - `Setoid` — [`Mathlib/Data/Setoid/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Setoid/Basic.html)
- [x] Mapping — §0.1, The Language of Set Theory, p. 1
  - `Function` — [`Mathlib/Logic/Function/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html)
- [x] Sequence — §0.1, The Language of Set Theory, p. 1
  - `Function` — [`Mathlib/Logic/Function/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html)
- [x] Cartesian product — §0.1, The Language of Set Theory, p. 1
  - `Prod` — [`Mathlib/Data/Prod/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Prod/Basic.html)
- [x] Partial order — §0.2, Orderings, p. 4
  - `PartialOrder` — [`Mathlib/Order/Defs/PartialOrder.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/PartialOrder.html)
- [x] Linear order — §0.2, Orderings, p. 4
  - `LinearOrder` — [`Mathlib/Order/Defs/LinearOrder.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/LinearOrder.html)
- [x] Well ordering — §0.2, Orderings, p. 4
  - `IsWellOrder` — [`Mathlib/Order/RelClasses.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/RelClasses.html)
- [x] Cardinality — §0.3, Cardinality, p. 6
  - `Cardinal` — [`Mathlib/SetTheory/Cardinal/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Defs.html)
- [x] Countable set — §0.3, Cardinality, p. 6
  - [`Set.Countable`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Set.Countable#doc) — [`Mathlib/Data/Set/Countable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Countable.html)
- [x] Ordinal number — §0.4, More about Well Ordered Sets, p. 9
  - `Ordinal` — [`Mathlib/SetTheory/Ordinal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Basic.html)
- [x] Extended real number system — §0.5, The Extended Real Number System, p. 10
  - `EReal` — [`Mathlib/Data/EReal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/EReal/Basic.html)
- [x] Metric space — §0.6, Metric Spaces, p. 13
  - `MetricSpace` — [`Mathlib/Topology/MetricSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Defs.html)
- [x] Open ball — §0.6, Metric Spaces, p. 13
  - [`Metric.ball`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Metric.ball#doc) — [`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Defs.html)
- [x] Open set — §0.6, Metric Spaces, p. 13
  - `IsOpen` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Closed set — §0.6, Metric Spaces, p. 13
  - `IsClosed` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Interior — §0.6, Metric Spaces, p. 13
  - `interior` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Closure — §0.6, Metric Spaces, p. 13
  - `closure` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Dense subset — §0.6, Metric Spaces, p. 13
  - `Dense` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Separable metric space — §0.6, Metric Spaces, p. 13
  - `SeparableSpace` — [`Mathlib/Topology/Bases.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html)
- [x] Cauchy sequence — §0.6, Metric Spaces, p. 13
  - `CauchySeq` — [`Mathlib/Topology/UniformSpace/Cauchy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
- [x] Complete metric space — §0.6, Metric Spaces, p. 13
  - `CompleteSpace` — [`Mathlib/Topology/UniformSpace/Cauchy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
- [x] Totally bounded set — §0.6, Metric Spaces, p. 13
  - `TotallyBounded` — [`Mathlib/Topology/UniformSpace/Cauchy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
- [x] Compact set — §0.6, Metric Spaces, p. 13
  - `IsCompact` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)

## Chapter 1: Measures

- [x] Algebra of sets — §1.2, Sigma-algebras, p. 21
  - Mathlib: [`MeasureTheory.IsSetAlgebra`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.IsSetAlgebra#doc) — [`Mathlib/MeasureTheory/SetAlgebra.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/SetAlgebra.html)
- [x] Sigma-algebra — §1.2, Sigma-algebras, p. 21
  - `MeasurableSpace` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Generated sigma-algebra — §1.2, Sigma-algebras, p. 21
  - [`MeasurableSpace.generateFrom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasurableSpace.generateFrom#doc) — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Borel sigma-algebra — §1.2, Sigma-algebras, p. 21
  - `borel` — [`Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.html)
- [x] Measurable space — §1.2, Sigma-algebras, p. 21
  - `MeasurableSpace` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Measure — §1.3, Measures, p. 24
  - `Measure` — [`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.html)
- [x] Measure space — §1.3, Measures, p. 24
  - `MeasureSpace` — [`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.html)
- [x] Finite measure — §1.3, Measures, p. 24
  - `IsFiniteMeasure` — [`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.html)
- [x] Sigma-finite measure — §1.3, Measures, p. 24
  - `SigmaFinite` — [`Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.html)
- [ ] Semifinite measure — §1.3, Measures, p. 24
- [x] Complete measure — §1.3, Measures, p. 24
  - [`Measure.IsComplete`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.IsComplete#doc) — [`Mathlib/MeasureTheory/Measure/NullMeasurable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/NullMeasurable.html)
- [x] Outer measure — §1.4, Outer Measures, p. 28
  - `OuterMeasure` — [`Mathlib/MeasureTheory/OuterMeasure/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Defs.html)
- [x] Caratheodory measurable set — §1.4, Outer Measures, p. 28
  - [`OuterMeasure.caratheodory`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=OuterMeasure.caratheodory#doc) — [`Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.html)
- [x] Lebesgue measure — §1.5, Borel Measures on the Real Line, p. 33
  - `volume` — [`Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.html)
- [x] Lebesgue measurable set — §1.5, Borel Measures on the Real Line, p. 33
  - `MeasurableSet` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Lebesgue-Stieltjes measure — §1.5, Borel Measures on the Real Line, p. 33
  - [`StieltjesFunction.measure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=StieltjesFunction.measure#doc) — [`Mathlib/MeasureTheory/Measure/Stieltjes.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Stieltjes.html)

## Chapter 2: Integration

- [x] Measurable function — §2.1, Measurable Functions, p. 43
  - `Measurable` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Borel measurable function — §2.1, Measurable Functions, p. 43
  - `Measurable` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Simple function — §2.1, Measurable Functions, p. 43
  - [`MeasureTheory.SimpleFunc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.SimpleFunc#doc) — [`Mathlib/MeasureTheory/Function/SimpleFunc.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/SimpleFunc.html)
- [x] Integral of a nonnegative simple function — §2.2, Integration of Nonnegative Functions, p. 49
  - [`MeasureTheory.SimpleFunc.lintegral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.SimpleFunc.lintegral#doc) — [`Mathlib/MeasureTheory/Function/SimpleFunc.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/SimpleFunc.html)
- [x] Integral of a nonnegative measurable function — §2.2, Integration of Nonnegative Functions, p. 49
  - [`MeasureTheory.lintegral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.lintegral#doc) — [`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.html)
- [x] Integrable complex function — §2.3, Integration of Complex Functions, p. 52
  - [`MeasureTheory.Integrable`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.Integrable#doc) — [`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/L1Space/Integrable.html)
- [x] Integral of a complex function — §2.3, Integration of Complex Functions, p. 52
  - [`MeasureTheory.integral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.integral#doc) — [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- [x] Almost everywhere — §2.3, Integration of Complex Functions, p. 52
  - `ae` — [`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.html)
- [x] Convergence almost everywhere — §2.4, Modes of Convergence, p. 60
  - [`Filter.Tendsto`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Filter.Tendsto#doc) — [`Mathlib/Order/Filter/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)
- [x] Convergence in measure — §2.4, Modes of Convergence, p. 60
  - [`MeasureTheory.TendstoInMeasure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.TendstoInMeasure#doc) — [`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.html)
- [x] Convergence in L1 — §2.4, Modes of Convergence, p. 60
  - [`MeasureTheory.L1`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.L1#doc) — [`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Basic.html)
- [x] Product sigma-algebra — §2.5, Product Measures, p. 64
  - [`MeasurableSpace.prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasurableSpace.prod#doc) — [`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html)
- [x] Product measure — §2.5, Product Measures, p. 64
  - [`Measure.prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.prod#doc) — `Mathlib/MeasureTheory/Measure/Prod.lean:171`
- [ ] Section of a measurable set — §2.5, Product Measures, p. 64
- [x] Lebesgue integral on Euclidean space — §2.6, The n-dimensional Lebesgue Integral, p. 70
  - [`MeasureTheory.integral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.integral#doc) — [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- [x] Polar coordinates — §2.7, Integration in Polar Coordinates, p. 77
  - [`Complex.polarCoord`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.polarCoord#doc) — [`Mathlib/Analysis/SpecialFunctions/PolarCoord.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/PolarCoord.html)

## Chapter 3: Signed Measures and Differentiation

- [x] Signed measure — §3.1, Signed Measures, p. 85
  - `SignedMeasure` — [`Mathlib/MeasureTheory/VectorMeasure/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/VectorMeasure/Basic.html)
- [ ] Positive set for a signed measure — §3.1, Signed Measures, p. 85
- [ ] Negative set for a signed measure — §3.1, Signed Measures, p. 85
- [x] Mutually singular measures — §3.1, Signed Measures, p. 85
  - [`Measure.MutuallySingular`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.MutuallySingular#doc) — [`Mathlib/MeasureTheory/Measure/MutuallySingular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MutuallySingular.html)
- [x] Total variation measure — §3.1, Signed Measures, p. 85
  - [`SignedMeasure.totalVariation`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SignedMeasure.totalVariation#doc) — [`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.html)
- [x] Absolute continuity of measures — §3.2, The Lebesgue-Radon-Nikodym Theorem, p. 88
  - [`Measure.AbsolutelyContinuous`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.AbsolutelyContinuous#doc) — [`Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.html)
- [x] Radon-Nikodym derivative — §3.2, The Lebesgue-Radon-Nikodym Theorem, p. 88
  - [`Measure.rnDeriv`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.rnDeriv#doc) — [`Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.html)
- [x] Complex measure — §3.3, Complex Measures, p. 93
  - `ComplexMeasure` — [`Mathlib/MeasureTheory/Measure/Complex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Complex.html)
- [ ] Lebesgue point — §3.4, Differentiation on Euclidean Space, p. 95
- [x] Function of bounded variation — §3.5, Functions of Bounded Variation, p. 100
  - `BoundedVariationOn` — [`Mathlib/Topology/EMetricSpace/BoundedVariation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/EMetricSpace/BoundedVariation.html)
- [x] Total variation function — §3.5, Functions of Bounded Variation, p. 100
  - `variationOnFromTo` — [`Mathlib/Topology/EMetricSpace/VariationOnFromTo.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/EMetricSpace/VariationOnFromTo.html)
- [x] Absolutely continuous function — §3.5, Functions of Bounded Variation, p. 100
  - `AbsolutelyContinuousOnInterval` — [`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.html)

## Chapter 4: Point Set Topology

- [x] Topological space — §4.1, Topological Spaces, p. 113
  - `TopologicalSpace` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Neighborhood — §4.1, Topological Spaces, p. 113
  - `nhds` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] Base for a topology — §4.1, Topological Spaces, p. 113
  - `IsTopologicalBasis` — [`Mathlib/Topology/Bases.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html)
- [x] Subbase for a topology — §4.1, Topological Spaces, p. 113
  - [`TopologicalSpace.generateFrom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.generateFrom#doc) — [`Mathlib/Topology/Order.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order.html)
- [x] Subspace topology — §4.1, Topological Spaces, p. 113
  - [`TopologicalSpace.induced`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.induced#doc) — [`Mathlib/Topology/Defs/Induced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Induced.html)
- [x] Product topology — §4.1, Topological Spaces, p. 113
  - `instTopologicalSpaceProd` — [`Mathlib/Topology/Constructions.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Constructions.html)
- [x] Hausdorff space — §4.1, Topological Spaces, p. 113
  - `T2Space` — [`Mathlib/Topology/Separation/Hausdorff.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Hausdorff.html)
- [x] Continuous map — §4.2, Continuous Maps, p. 119
  - `Continuous` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Homeomorphism — §4.2, Continuous Maps, p. 119
  - `Homeomorph` — [`Mathlib/Topology/Homeomorph/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homeomorph/Defs.html)
- [x] Quotient topology — §4.2, Continuous Maps, p. 119
  - [`TopologicalSpace.coinduced`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.coinduced#doc) — [`Mathlib/Topology/Defs/Induced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Induced.html)
- [x] Net — §4.3, Nets, p. 125
  - Mathlib: `Filter` — [`Mathlib/Order/Filter/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)
- [x] Subnet — §4.3, Nets, p. 125
  - Mathlib: [`Filter.Tendsto`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Filter.Tendsto#doc) — [`Mathlib/Order/Filter/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)
- [x] Compact space — §4.4, Compact Spaces, p. 128
  - `CompactSpace` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] Relatively compact set — §4.4, Compact Spaces, p. 128
  - Mathlib: `IsCompact (closure s)` — [`Mathlib/Topology/Separation/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Basic.html)
- [x] Locally compact space — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - `LocallyCompactSpace` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] One-point compactification — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - `OnePoint` — [`Mathlib/Topology/Compactification/OnePoint/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactification/OnePoint/Basic.html)
- [x] Compact-open topology — §4.5, Locally Compact Hausdorff Spaces, p. 131
  - [`ContinuousMap.compactOpen`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousMap.compactOpen#doc) — [`Mathlib/Topology/CompactOpen.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html)
- [ ] Uniform algebra — §4.7, The Stone-Weierstrass Theorem, p. 138
- [x] Completely regular space — §4.8, Embeddings in Cubes, p. 143
  - `CompletelyRegularSpace` — [`Mathlib/Topology/Separation/CompletelyRegular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/CompletelyRegular.html)
- [x] Normal space — §4.8, Embeddings in Cubes, p. 143
  - `NormalSpace` — [`Mathlib/Topology/Separation/Regular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Regular.html)

## Chapter 5: Elements of Functional Analysis

- [x] Normed vector space — §5.1, Normed Vector Spaces, p. 151
  - `NormedSpace` — [`Mathlib/Analysis/Normed/Module/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Basic.html)
- [x] Banach space — §5.1, Normed Vector Spaces, p. 151
  - `CompleteSpace` — [`Mathlib/Topology/UniformSpace/Cauchy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
- [x] Bounded linear map — §5.1, Normed Vector Spaces, p. 151
  - `ContinuousLinearMap` — [`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.html)
- [x] Operator norm — §5.1, Normed Vector Spaces, p. 151
  - [`ContinuousLinearMap.opNorm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousLinearMap.opNorm#doc) — [`Mathlib/Analysis/Normed/Operator/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Basic.html)
- [x] Linear functional — §5.2, Linear Functionals, p. 157
  - `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Dual space — §5.2, Linear Functionals, p. 157
  - [`NormedSpace.Dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=NormedSpace.Dual#doc) — [`Mathlib/Analysis/Normed/Module/Dual.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Dual.html)
- [x] Weak topology — §5.2, Linear Functionals, p. 157
  - `WeakBilin` — `Mathlib/Topology/Algebra/Module/Spaces/WeakBilin.lean:64`
- [x] Weak-star topology — §5.2, Linear Functionals, p. 157
  - `WeakDual` — [`Mathlib/Topology/Algebra/Module/WeakDual.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/WeakDual.html)
- [x] Meager set — §5.3, The Baire Category Theorem and its Consequences, p. 161
  - `IsMeagre` — [`Mathlib/Topology/GDelta/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/GDelta/Basic.html)
- [x] Baire space — §5.3, The Baire Category Theorem and its Consequences, p. 161
  - `BaireSpace` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Topological vector space — §5.4, Topological Vector Spaces, p. 165
  - `ContinuousSMul` — [`Mathlib/Topology/Algebra/Module/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/Basic.html)
- [x] Locally convex space — §5.4, Topological Vector Spaces, p. 165
  - `LocallyConvexSpace` — [`Mathlib/Topology/Algebra/Module/LocallyConvex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Module/LocallyConvex.html)
- [x] Seminorm — §5.4, Topological Vector Spaces, p. 165
  - `Seminorm` — [`Mathlib/Analysis/Seminorm.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Seminorm.html)
- [x] Inner product space — §5.5, Hilbert Spaces, p. 171
  - `InnerProductSpace` — [`Mathlib/Analysis/InnerProductSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Defs.html)
- [x] Hilbert space — §5.5, Hilbert Spaces, p. 171
  - `CompleteSpace` — [`Mathlib/Topology/UniformSpace/Cauchy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html)
- [x] Orthogonal complement — §5.5, Hilbert Spaces, p. 171
  - [`Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.orthogonal#doc) — [`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthogonal.html)
- [x] Orthonormal set — §5.5, Hilbert Spaces, p. 171
  - `Orthonormal` — [`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthonormal.html)
- [x] Complete orthonormal set — §5.5, Hilbert Spaces, p. 171
  - `OrthonormalBasis` — [`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthonormal.html)

## Chapter 6: Lp Spaces

- [x] Lp space — §6.1, Basic Theory of Lp Spaces, p. 181
  - [`MeasureTheory.Lp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.Lp#doc) — [`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Basic.html)
- [x] Essential supremum — §6.1, Basic Theory of Lp Spaces, p. 181
  - [`MeasureTheory.essSup`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.essSup#doc) — [`Mathlib/MeasureTheory/Function/EssSup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/EssSup.html)
- [x] L-infinity space — §6.1, Basic Theory of Lp Spaces, p. 181
  - [`MeasureTheory.Lp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.Lp#doc) — [`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Basic.html)
- [x] Conjugate exponents — §6.1, Basic Theory of Lp Spaces, p. 181
  - `IsConjExponent` — [`Mathlib/Analysis/MeanInequalities.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/MeanInequalities.html)
- [x] Dual of an Lp space — §6.2, The Dual of Lp, p. 188
  - [`NormedSpace.Dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=NormedSpace.Dual#doc) — [`Mathlib/Analysis/Normed/Module/Dual.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Dual.html)
- [x] Distribution function — §6.4, Distribution Functions and Weak Lp, p. 197
  - [`MeasureTheory.distribution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.distribution#doc) — `fpvandoorn/BonnAnalysis:BonnAnalysis/LorentzSpace.lean`
- [x] Weak Lp space — §6.4, Distribution Functions and Weak Lp, p. 197
  - [`MeasureTheory.Lorentz`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.Lorentz#doc) (q = ∞) — `fpvandoorn/BonnAnalysis:BonnAnalysis/LorentzSpace.lean`
- [ ] Analytic family of operators — §6.5, Interpolation of Lp Spaces, p. 200

## Chapter 7: Radon Measures

- [x] Positive linear functional on Cc(X) — §7.1, Positive Linear Functionals on Cc(X), p. 211
  - `PositiveLinearMap` — [`Mathlib/Algebra/Order/Module/PositiveLinearMap.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Module/PositiveLinearMap.html)
- [x] Radon measure — §7.2, Regularity and Approximation Theorems, p. 216
  - [`Measure.IsRadon`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.IsRadon#doc) — [`Mathlib/MeasureTheory/Measure/Regular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html)
- [x] Outer regular measure — §7.2, Regularity and Approximation Theorems, p. 216
  - [`Measure.OuterRegular`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.OuterRegular#doc) — [`Mathlib/MeasureTheory/Measure/Regular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html)
- [x] Inner regular measure — §7.2, Regularity and Approximation Theorems, p. 216
  - [`Measure.InnerRegular`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.InnerRegular#doc) — [`Mathlib/MeasureTheory/Measure/Regular.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html)
- [x] C0(X) — §7.3, The Dual of C0(X), p. 221
  - `CocompactMap` — [`Mathlib/Topology/ContinuousMap/CocompactMap.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousMap/CocompactMap.html)
- [x] Product of Radon measures — §7.4, Products of Radon Measures, p. 226
  - [`Measure.prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.prod#doc) — `Mathlib/MeasureTheory/Measure/Prod.lean:171`

## Chapter 8: Elements of Fourier Analysis

- [x] Translation operator — §8.1, Preliminaries, p. 235
  - `translate` — [`Mathlib/Algebra/Group/Translate.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Translate.html)
- [ ] Dilation operator — §8.1, Preliminaries, p. 235
- [x] Convolution — §8.2, Convolutions, p. 239
  - [`MeasureTheory.convolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.convolution#doc) — [`Mathlib/Analysis/Convolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convolution.html)
- [x] Approximate identity — §8.2, Convolutions, p. 239
  - [`TauCeti.IsMollifier`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.IsMollifier#doc) — `TauCetiProject/TauCeti:TauCeti/RepresentationTheory/Compact/ApproximateIdentity.lean`
- [x] Fourier transform — §8.3, The Fourier Transform, p. 247
  - `FourierTransform` — [`Mathlib/Analysis/Fourier/Notation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Notation.html)
- [x] Inverse Fourier transform — §8.3, The Fourier Transform, p. 247
  - `FourierTransformInv` — [`Mathlib/Analysis/Fourier/Notation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Notation.html)
- [x] Fourier series — §8.4, Summation of Fourier Integrals and Series, p. 257
  - `fourierCoeff` — [`Mathlib/Analysis/Fourier/AddCircle.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/AddCircle.html)
- [ ] Summability kernel — §8.4, Summation of Fourier Integrals and Series, p. 257
- [x] Fourier-Stieltjes transform — §8.6, Fourier Analysis of Measures, p. 270
  - [`MeasureTheory.charFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.charFun#doc) — [`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.html)
- [x] Fundamental solution of a differential operator — §8.7, Applications to Partial Differential Equations, p. 273
  - [`DifferentialOperators.IsTemperedFundamentalSolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DifferentialOperators.IsTemperedFundamentalSolution#doc) — `facebookresearch/atlas-lean:Atlas/DifferentialAnalysis/code/DifferentialOperators.lean`

## Chapter 9: Elements of Distribution Theory

- [x] Test function — §9.1, Distributions, p. 281
  - `TestFunction` — [`Mathlib/Analysis/Distribution/TestFunction.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/TestFunction.html)
- [x] Distribution — §9.1, Distributions, p. 281
  - `Distribution` — [`Mathlib/Analysis/Distribution/Distribution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/Distribution.html)
- [x] Distributional derivative — §9.1, Distributions, p. 281
  - [`Distribution.lineDerivCLM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Distribution.lineDerivCLM#doc) — [`Mathlib/Analysis/Distribution/Distribution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/Distribution.html)
- [x] Support of a distribution — §9.1, Distributions, p. 281
  - `dsupport` — [`Mathlib/Analysis/Distribution/Support.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/Support.html)
- [x] Compactly supported distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - `IsCompactlySupportedDistribution` — `facebookresearch/atlas-lean:Atlas/DifferentialAnalysis/code/WavefrontSet.lean`
- [x] Tempered distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - `TemperedDistribution` — [`Mathlib/Analysis/Distribution/TemperedDistribution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/TemperedDistribution.html)
- [ ] Periodic distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
- [x] Fourier transform of a tempered distribution — §9.2, Compactly Supported, Tempered, and Periodic Distributions, p. 291
  - [`FourierTransform.fourierCLM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FourierTransform.fourierCLM#doc) — `Mathlib/Analysis/Fourier/Notation.lean:181` (was [`TemperedDistribution.fourierTransformCLM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TemperedDistribution.fourierTransformCLM#doc), a deprecated alias)
- [x] Sobolev space — §9.3, Sobolev Spaces, p. 301
  - [`TemperedDistribution.MemSobolev`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TemperedDistribution.MemSobolev#doc) — [`Mathlib/Analysis/Distribution/Sobolev.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/Sobolev.html)
- [x] Weak derivative — §9.3, Sobolev Spaces, p. 301
  - [`Distribution.lineDerivCLM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Distribution.lineDerivCLM#doc) — [`Mathlib/Analysis/Distribution/Distribution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/Distribution.html)

## Chapter 10: Topics in Probability Theory

- [x] Probability space — §10.1, Basic Concepts, p. 313
  - [`Measure.IsProbabilityMeasure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.IsProbabilityMeasure#doc) — [`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.html)
- [x] Random variable — §10.1, Basic Concepts, p. 313
  - `Measurable` — [`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)
- [x] Distribution of a random variable — §10.1, Basic Concepts, p. 313
  - [`Measure.map`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.map#doc) — [`Mathlib/MeasureTheory/Measure/Map.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Map.html)
- [x] Expectation — §10.1, Basic Concepts, p. 313
  - [`MeasureTheory.integral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.integral#doc) — [`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html)
- [x] Independence — §10.1, Basic Concepts, p. 313
  - [`ProbabilityTheory.Indep`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProbabilityTheory.Indep#doc) — [`Mathlib/Probability/Independence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html)
- [x] Identically distributed random variables — §10.1, Basic Concepts, p. 313
  - [`ProbabilityTheory.IdentDistrib`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProbabilityTheory.IdentDistrib#doc) — [`Mathlib/Probability/IdentDistrib.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/IdentDistrib.html)
- [x] Convergence in probability — §10.1, Basic Concepts, p. 313
  - [`MeasureTheory.TendstoInMeasure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.TendstoInMeasure#doc) — [`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.html)
- [x] Convergence in distribution — §10.1, Basic Concepts, p. 313
  - [`MeasureTheory.TendstoInDistribution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.TendstoInDistribution#doc) — [`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.html)
- [x] Characteristic function — §10.3, The Central Limit Theorem, p. 325
  - [`Measure.charFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.charFun#doc) — [`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.html)
- [x] Product probability space — §10.4, Construction of Sample Spaces, p. 328
  - [`Measure.prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Measure.prod#doc) — `Mathlib/MeasureTheory/Measure/Prod.lean:171`
- [x] Wiener process — §10.5, The Wiener Process, p. 330
  - [`ProbabilityTheory.IsBrownianReal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProbabilityTheory.IsBrownianReal#doc) — [`Mathlib/Probability/BrownianMotion/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/BrownianMotion/Basic.html)

## Chapter 11: More Measures and Integrals

- [x] Topological group — §11.1, Topological Groups and Haar Measure, p. 339
  - `IsTopologicalGroup` — [`Mathlib/Topology/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Group/Defs.html)
- [x] Left Haar measure — §11.1, Topological Groups and Haar Measure, p. 339
  - [`MeasureTheory.IsHaarMeasure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.IsHaarMeasure#doc) — [`Mathlib/MeasureTheory/Group/Measure.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/Measure.html)
- [x] Right Haar measure — §11.1, Topological Groups and Haar Measure, p. 339
  - [`MeasureTheory.IsMulRightInvariant`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.IsMulRightInvariant#doc) — [`Mathlib/MeasureTheory/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/Defs.html)
- [x] Modular function — §11.1, Topological Groups and Haar Measure, p. 339
  - [`MeasureTheory.modularCharacter`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.modularCharacter#doc) — [`Mathlib/MeasureTheory/Group/ModularCharacter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/ModularCharacter.html)
- [x] Hausdorff measure — §11.2, Hausdorff Measure, p. 348
  - [`MeasureTheory.hausdorffMeasure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.hausdorffMeasure#doc) — [`Mathlib/MeasureTheory/Measure/Hausdorff.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Hausdorff.html)
- [x] Hausdorff dimension — §11.2, Hausdorff Measure, p. 348
  - [`MeasureTheory.dimH`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MeasureTheory.dimH#doc) — [`Mathlib/Topology/MetricSpace/HausdorffDimension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/HausdorffDimension.html)
- [x] Similarity — §11.3, Self-similarity and Hausdorff Dimension, p. 355
  - `Dilation` — [`Mathlib/Topology/MetricSpace/Dilation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Dilation.html)
- [ ] Self-similar set — §11.3, Self-similarity and Hausdorff Dimension, p. 355
- [x] Differential form — §11.4, Integration on Manifolds, p. 361
  - `DifferentialForm` — (no Mathlib declaration)
- [x] Integral of a differential form — §11.4, Integration on Manifolds, p. 361
  - `curveIntegral`, `CurveIntegrable` — [`Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.html)
```

```
