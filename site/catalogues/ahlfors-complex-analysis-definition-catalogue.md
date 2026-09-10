---
title: "Ahlfors complex analysis definition catalogue"
---

Title: *Complex Analysis*, third edition

Author: Lars V. Ahlfors

Zotero key: `RYTA2YNJ`

Citekey: `Mar68`

Source attachment: ``local-write-api-1783129264316-RYTA2YNJ_extracted.md``

## Chapter 1: Complex Numbers

- [x] Complex number — §1.1, Arithmetic Operations, p. 1
  - `Complex` — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Real part — §1.1, Arithmetic Operations, p. 1
  - [`Complex.re`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.re#doc) — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Imaginary part — §1.1, Arithmetic Operations, p. 1
  - [`Complex.im`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.im#doc) — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Purely imaginary number — §1.1, Arithmetic Operations, p. 1
  - Mathlib: `Complex.re z = 0` — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Complex conjugate — §1.4, Conjugation, Absolute Value, p. 6
  - `starRingEnd` — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Absolute value of a complex number — §1.4, Conjugation, Absolute Value, p. 6
  - [`Complex.normSq`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.normSq#doc) — [`Mathlib/Data/Complex/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html)
- [x] Argument of a complex number — §2.1, Geometric Addition and Multiplication, p. 12
  - [`Complex.arg`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.arg#doc) — [`Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/Arg.html)
- [x] Riemann sphere — §2.4, The Spherical Representation, p. 18
  - `OnePoint` — [`Mathlib/Topology/Compactification/OnePoint/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactification/OnePoint/Basic.html)
- [x] Stereographic projection — §2.4, The Spherical Representation, p. 18
  - `stereographic` — [`Mathlib/Geometry/Manifold/Instances/Sphere.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Instances/Sphere.html)

## Chapter 2: Complex Functions

- [x] Limit of a complex function — §1.1, Limits and Continuity, p. 22
  - [`Filter.Tendsto`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Filter.Tendsto#doc) — [`Mathlib/Order/Filter/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html)
- [x] Continuous complex function — §1.1, Limits and Continuity, p. 22
  - `Continuous` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Derivative of a complex function — §1.2, Analytic Functions, p. 24
  - `HasDerivAt` — [`Mathlib/Analysis/Calculus/Deriv/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html)
- [x] Analytic function — §1.2, Analytic Functions, p. 24
  - `AnalyticAt` — [`Mathlib/Analysis/Analytic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html)
- [x] Entire function — §1.2, Analytic Functions, p. 24
  - `AnalyticOnNhd` — [`Mathlib/Analysis/Analytic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html)
- [x] Polynomial — §1.3, Polynomials, p. 28
  - `Polynomial` — [`Mathlib/Algebra/Polynomial/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Basic.html)
- [x] Rational function — §1.4, Rational Functions, p. 30
  - `RatFunc` — [`Mathlib/FieldTheory/RatFunc/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/RatFunc/Defs.html)
- [x] Sequence — §2.1, Sequences, p. 34
  - `Function` — [`Mathlib/Logic/Function/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html)
- [x] Series — §2.2, Series, p. 35
  - `Summable` — [`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html)
- [x] Uniform convergence — §2.3, Uniform Convergence, p. 36
  - `TendstoUniformly` — [`Mathlib/Topology/UniformSpace/UniformConvergence.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/UniformConvergence.html)
- [x] Power series — §2.4, Power Series, p. 38
  - `FormalMultilinearSeries` — [`Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/FormalMultilinearSeries.html)
- [x] Radius of convergence — §2.4, Power Series, p. 38
  - [`FormalMultilinearSeries.radius`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FormalMultilinearSeries.radius#doc) — [`Mathlib/Analysis/Analytic/ConvergenceRadius.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/ConvergenceRadius.html)
- [x] Exponential function — §3.1, The Exponential, p. 43
  - [`Complex.exp`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.exp#doc) — [`Mathlib/Analysis/SpecialFunctions/Exp.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Exp.html)
- [x] Trigonometric functions — §3.2, The Trigonometric Functions, p. 44
  - [`Complex.sin`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.sin#doc) — [`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.html)
- [x] Complex logarithm — §3.4, The Logarithm, p. 46
  - [`Complex.log`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.log#doc) — [`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html)

## Chapter 3: Analytic Functions as Mappings

- [x] Metric space — §1.2, Metric Spaces, p. 51
  - `MetricSpace` — [`Mathlib/Topology/MetricSpace/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Defs.html)
- [x] Open set — §1.2, Metric Spaces, p. 51
  - `IsOpen` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Closed set — §1.2, Metric Spaces, p. 51
  - `IsClosed` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Neighborhood — §1.2, Metric Spaces, p. 51
  - `nhds` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] Region — §1.3, Connectedness, p. 54
  - Mathlib: `IsOpen U ∧ IsConnected U` — [`Mathlib/Topology/Connected/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/Basic.html)
- [x] Connected set — §1.3, Connectedness, p. 54
  - `IsConnected` — [`Mathlib/Topology/Connected/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/Basic.html)
- [x] Compact set — §1.4, Compactness, p. 59
  - `IsCompact` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] Continuous mapping — §1.5, Continuous Functions, p. 64
  - `Continuous` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Topological space — §1.6, Topological Spaces, p. 67
  - `TopologicalSpace` — [`Mathlib/Topology/Defs/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html)
- [x] Arc — §2.1, Arcs and Closed Curves, p. 68
  - `Path` — [`Mathlib/Topology/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Path.html)
- [x] Closed curve — §2.1, Arcs and Closed Curves, p. 68
  - [`Path.IsClosed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.IsClosed#doc) — [`Mathlib/Topology/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Path.html)
- [x] Analytic function in a region — §2.2, Analytic Functions in Regions, p. 69
  - `AnalyticOnNhd` — [`Mathlib/Analysis/Analytic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html)
- [x] Conformal mapping — §2.3, Conformal Mapping, p. 73
  - `ConformalAt` — [`Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Conformal/NormedSpace.html)
- [x] Linear transformation — §3.1, The Linear Group, p. 76
  - [`UpperHalfPlane.smulAux'`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=UpperHalfPlane.smulAux'#doc), [`UpperHalfPlane.smulAux`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=UpperHalfPlane.smulAux#doc) — [`Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.html)
- [ ] Cross ratio — §3.2, The Cross Ratio, p. 78
- [ ] Symmetric points — §3.3, Symmetry, p. 80
- [ ] Oriented circle — §3.4, Oriented Circles, p. 83
- [ ] Elementary Riemann surface — §4.3, Elementary Riemann Surfaces, p. 97

## Chapter 4: Complex Integration

- [x] Line integral — §1.1, Line Integrals, p. 101
  - `curveIntegral`, `CurveIntegrable` — [`Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.html)
- [ ] Rectifiable arc — §1.2, Rectifiable Arcs, p. 104
- [x] Index of a point with respect to a closed curve — §2.1, The Index of a Point with Respect to a Closed Curve, p. 114
  - [`TauCeti.Contour.windingNumber`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.Contour.windingNumber#doc) — `TauCetiProject__TauCeti/TauCeti/Analysis/Contour/Winding/Number/Basic.lean`
- [ ] Removable singularity — §3.1, Removable Singularities, p. 124
- [x] Zero of an analytic function — §3.2, Zeros and Poles, p. 126
  - `meromorphicOrderAt` — [`Mathlib/Analysis/Meromorphic/Order.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Order.html)
- [x] Pole — §3.2, Zeros and Poles, p. 126
  - `meromorphicOrderAt` — [`Mathlib/Analysis/Meromorphic/Order.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Order.html)
- [x] Order of a zero — §3.2, Zeros and Poles, p. 126
  - `meromorphicOrderAt` — [`Mathlib/Analysis/Meromorphic/Order.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Order.html)
- [x] Order of a pole — §3.2, Zeros and Poles, p. 126
  - `meromorphicOrderAt` — [`Mathlib/Analysis/Meromorphic/Order.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Order.html)
- [ ] Chain — §4.1, Chains and Cycles, p. 137
- [x] Cycle — §4.1, Chains and Cycles, p. 137
  - [`TauCeti.Contour.Cycle`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.Contour.Cycle#doc) — `TauCetiProject__TauCeti/TauCeti/Analysis/Contour/Cycle/Basic.lean`
- [x] Simply connected region — §4.2, Simple Connectivity, p. 139
  - `SimplyConnectedSpace` — [`Mathlib/Topology/Homotopy/Contractible.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Contractible.html)
- [x] Exact differential — §4.3, Exact Differentials in Simply Connected Regions, p. 141
  - [`Complex.IsExactOn`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.IsExactOn#doc) — [`Mathlib/Analysis/Complex/HasPrimitives.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/HasPrimitives.html)
- [x] Residue — §5.1, The Residue Theorem, p. 147
  - [`LaurentSeries.residue`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LaurentSeries.residue#doc) — `facebookresearch/atlas-lean:Atlas/AlgebraicGeometryI/code/ResidueMap.lean`
- [x] Harmonic function — §6.1, Definition and Basic Properties, p. 160
  - `HarmonicAt` — [`Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.html)
- [ ] Harmonic conjugate — §6.1, Definition and Basic Properties, p. 160

## Chapter 5: Series and Product Developments

- [x] Taylor series — §1.2, The Taylor Series, p. 177
  - `HasFPowerSeriesAt` — [`Mathlib/Analysis/Analytic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Basic.html)
- [x] Laurent series — §1.3, The Laurent Series, p. 182
  - `LaurentSeries` — [`Mathlib/RingTheory/LaurentSeries.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LaurentSeries.html)
- [x] Principal part of a Laurent series — §1.3, The Laurent Series, p. 182
  - [`GeneralizedResidueTheory.meromorphicPrincipalPart`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GeneralizedResidueTheory.meromorphicPrincipalPart#doc) — `reservoir-sources/Vilin97__lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicPrincipalPart.lean`
- [ ] Isolated singularity — §1.3, The Laurent Series, p. 182
- [x] Essential singularity — §1.3, The Laurent Series, p. 182
  - `EssentialSingularity` — `reservoir-sources/project-numina__LeanTriathlon/LiveLeanTriathlonSorry/CasoratiWeierstrass/All.lean`
- [x] Meromorphic function — §1.3, The Laurent Series, p. 182
  - `MeromorphicAt` — [`Mathlib/Analysis/Meromorphic/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Basic.html)
- [x] Infinite product — §2.2, Infinite Products, p. 189
  - `Multipliable` — [`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Defs.html)
- [x] Canonical product — §2.3, Canonical Products, p. 192
  - [`Complex.canonicalProduct`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.canonicalProduct#doc) — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CanonicalProduct.lean:33`
- [x] Gamma function — §2.4, The Gamma Function, p. 196
  - [`Complex.Gamma`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.Gamma#doc) — [`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.html)
- [x] Order of an entire function — §3.2, Hadamard's Theorem, p. 206
  - [`Complex.Hadamard.EntireOfOrderAtMost`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.Hadamard.EntireOfOrderAtMost#doc) — `AlexKontorovich__PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Order.lean`
- [x] Equicontinuous family — §4.1, Equicontinuity, p. 210
  - `Equicontinuous` — [`Mathlib/Topology/UniformSpace/Equicontinuity.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Equicontinuity.html)
- [ ] Normal family — §4.2, Normality and Compactness, p. 211

## Chapter 6: Conformal Mapping and Dirichlet's Problem

- [ ] Analytic arc — §1.4, Analytic Arcs, p. 226
- [ ] Schwarz-Christoffel transformation — §2.2, The Schwarz-Christoffel Formula, p. 228
- [x] Mean-value property — §3.1, Functions with the Mean-value Property, p. 234
  - [`DiffContOnCl.circleAverage`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DiffContOnCl.circleAverage#doc), `circleAverage_of_differentiable_on_off_countable` — [`Mathlib/Analysis/Complex/MeanValue.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/MeanValue.html)
- [x] Subharmonic function — §4.1, Subharmonic Functions, p. 237
  - `SubharmonicOn` — `girving__ray/Ray/Hartogs/Subharmonic.lean`
- [x] Dirichlet problem — §4.2, Solution of Dirichlet's Problem, p. 240
  - [`Rado.exists_harmonic_extension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Rado.exists_harmonic_extension#doc) — `reservoir-sources/rkirov__jordan_pick/Rado/Complex/Poisson.lean`
- [ ] Harmonic measure — §5.1, Harmonic Measures, p. 244
- [ ] Green's function — §5.2, Green's Function, p. 249
- [ ] Parallel slit region — §5.3, Parallel Slit Regions, p. 251

## Chapter 7: Elliptic Functions

- [x] Simply periodic function — §1, Simply Periodic Functions, p. 255
  - [`Function.Periodic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Function.Periodic#doc) — [`Mathlib/Algebra/Ring/Periodic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Periodic.html)
- [x] Function of finite order — §1.3, Functions of Finite Order, p. 256
  - [`Complex.Hadamard.EntireOfOrderAtMost`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.Hadamard.EntireOfOrderAtMost#doc) — `AlexKontorovich/PrimeNumberTheoremAnd:PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Order.lean:78`
- [x] Doubly periodic function — §2, Doubly Periodic Functions, p. 257
  - [`ComplexLattice.IsLatticePeriodic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ComplexLattice.IsLatticePeriodic#doc) — `facebookresearch__atlas-lean/Atlas/EllipticCurves/code/EllipticFunction.lean`
- [x] Period module — §2.1, The Period Module, p. 257
  - [`Complex.PeriodPair.lattice`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.PeriodPair.lattice#doc) — [`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html)
- [x] Unimodular transformation — §2.2, Unimodular Transformations, p. 258
  - `SpecialLinearGroup` — [`Mathlib/LinearAlgebra/SpecialLinearGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpecialLinearGroup.html)
- [x] Canonical basis of a period module — §2.3, The Canonical Basis, p. 260
  - [`Complex.PeriodPair.latticeBasis`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.PeriodPair.latticeBasis#doc) — [`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html)
- [x] Elliptic function — §2.4, General Properties of Elliptic Functions, p. 262
  - [`ComplexLattice.IsEllipticFunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ComplexLattice.IsEllipticFunction#doc) — `facebookresearch__atlas-lean/Atlas/EllipticCurves/code/EllipticFunction.lean`
- [x] Weierstrass elliptic function — §3.1, The Weierstrass wp-function, p. 264
  - [`Complex.PeriodPair.weierstrassP`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Complex.PeriodPair.weierstrassP#doc) — [`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.html)
- [x] Weierstrass zeta function — §3.2, The Functions zeta(z) and sigma(z), p. 265
  - [`PeriodPair.weierstrassZeta`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PeriodPair.weierstrassZeta#doc) — `reservoir-sources/Vilin97__lean-pool/LeanPool/Chudnovsky/SigmaZeta.lean`
- [x] Weierstrass sigma function — §3.2, The Functions zeta(z) and sigma(z), p. 265
  - [`PeriodPair.weierstrassSigma`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PeriodPair.weierstrassSigma#doc) — `reservoir-sources/Vilin97__lean-pool/LeanPool/Chudnovsky/SigmaZeta.lean`
- [x] Modular lambda function — §3.4, The Modular Function lambda(tau), p. 269
  - `modularLambdaFn` — `reservoir-sources/mrdouglasny__seiberg-witten/SeibergWitten/Physics/ThetaLambda.lean`

## Chapter 8: Global Analytic Functions

- [ ] Function element — §1.1, General Analytic Functions, p. 275
- [ ] Direct analytic continuation — §1.1, General Analytic Functions, p. 275
- [ ] Complete analytic function — §1.1, General Analytic Functions, p. 275
- [ ] Riemann surface of a function — §1.2, The Riemann Surface of a Function, p. 277
- [ ] Analytic continuation along an arc — §1.3, Analytic Continuation along Arcs, p. 278
- [x] Homotopy of curves — §1.4, Homotopic Curves, p. 281
  - [`Path.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.Homotopy#doc) — [`Mathlib/Topology/Homotopy/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html)
- [ ] Branch point — §1.6, Branch Points, p. 287
- [x] Resultant of two polynomials — §2.1, The Resultant of Two Polynomials, p. 291
  - [`Polynomial.resultant`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.resultant#doc) — [`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Resultant/Basic.html)
- [ ] Algebraic function — §2.2, Definition and Properties of Algebraic Functions, p. 292
- [ ] Critical point of an algebraic function — §2.3, Behavior at the Critical Points, p. 294
- [ ] Lacunary value — §3.1, Lacunary Values, p. 297
- [ ] Ordinary point of a linear differential equation — §4.1, Ordinary Points, p. 300
- [ ] Regular singular point — §4.2, Regular Singular Points, p. 302
- [ ] Hypergeometric differential equation — §4.4, The Hypergeometric Differential Equation, p. 305
```

```
