---
title: "Shafarevich varieties definition catalogue"
---

Title: *Basic Algebraic Geometry 1*

Author: Igor R. Shafarevich

Zotero key: `GYU94DB4`

Citekey: `Sha94`

Source attachment: ``local-write-api-1783244375935-GYU94DB4_extracted.md``

## Chapter I. Basic Notions

- [x] Plane algebraic curve — §1.1, Plane Curves, p. 1
  - [`Lec5BezoutPascal.PlaneCurve`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lec5BezoutPascal.PlaneCurve#doc) — `Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`
- [x] Degree of a plane curve — §1.1, Plane Curves, p. 1
  - [`PlaneCurve.deg`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PlaneCurve.deg#doc) — `Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`
- [ ] Rational curve — §1.2, Rational Curves, p. 4
- [ ] Parametrisation of a curve — §1.2, Rational Curves, p. 4
- [x] Rational function on a curve — §1.3, Relation with Field Theory, p. 8
  - [`Scheme.functionField`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.functionField#doc) — [`Mathlib/AlgebraicGeometry/FunctionField.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/FunctionField.html)
- [x] Rational map — §1.4, Rational Maps, p. 10
  - [`AlgebraicGeometry.Scheme.RationalMap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Scheme.RationalMap#doc) — [`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Birational/RationalMap.html)
- [x] Birational map — §1.4, Rational Maps, p. 10
  - [`AlgebraicGeometry.Birational`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Birational#doc) — [`Mathlib/AlgebraicGeometry/Birational/Birational.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Birational/Birational.html)
- [ ] Singular point — §1.5, Singular and Nonsingular Points, p. 12
  - Partial reference: [`SingularPoints.IsSingularPoint`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularPoints.IsSingularPoint#doc) is a finite affine Jacobian criterion — `Atlas/ArithmeticGeometry/code/CoordinateRingSingular.lean`
- [x] Nonsingular point — §1.5, Singular and Nonsingular Points, p. 12
  - Partial reference: [`SingularPoints.IsNonsingularPoint`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularPoints.IsNonsingularPoint#doc) is a finite affine Jacobian criterion — `Atlas/ArithmeticGeometry/code/CoordinateRingSingular.lean`
  - `IsRegularLocalRing` — [`Mathlib/RingTheory/RegularLocalRing/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RegularLocalRing/Defs.html)
- [ ] Multiplicity of a point — §1.5, Singular and Nonsingular Points, p. 13
  - Partial reference: [`Lec5BezoutPascal.hypersurfaceMultiplicity`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lec5BezoutPascal.hypersurfaceMultiplicity#doc) treats polynomial hypersurfaces only — `Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`
- [x] Projective plane — §1.6, The Projective Plane, p. 16
  - LeanCategories: `LeanCategories.Schemes.ProjectiveSpace k 2` — [`LeanCategories/Schemes/Varieties.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Schemes/Varieties.lean)
- [x] Homogeneous coordinates — §1.6, The Projective Plane, p. 16
  - `Projectivization` — [`Mathlib/LinearAlgebra/Projectivization/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projectivization/Basic.html)
- [x] Projective algebraic plane curve — §1.6, The Projective Plane, p. 17
  - [`ProjectiveSpectrum.zeroLocus`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProjectiveSpectrum.zeroLocus#doc) — [`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.html)
- [x] Closed subset of affine space — §2.1, Definition of Closed Subsets, p. 22
  - [`PrimeSpectrum.zeroLocus`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PrimeSpectrum.zeroLocus#doc) — [`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Basic.html)
- [x] Affine algebraic set — §2.1, Definition of Closed Subsets, pp. 22–23
  - [`PrimeSpectrum.zeroLocus`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PrimeSpectrum.zeroLocus#doc) — [`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Basic.html)
- [x] Zariski topology on affine space — §2.1, Definition of Closed Subsets, p. 23
  - [`PrimeSpectrum.zariskiTopology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PrimeSpectrum.zariskiTopology#doc) — [`Mathlib/RingTheory/Spectrum/Prime/Topology.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Topology.html)
- [x] Closure of a subset — §2.1, Definition of Closed Subsets, p. 23
  - `closure` — [`Mathlib/Topology/Defs/Filter.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html)
- [x] Regular function on a closed subset — §2.2, Regular Functions on a Closed Subset, p. 24
  - `Scheme.Γ` — [`Mathlib/AlgebraicGeometry/Scheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html)
- [x] Germ of a regular function — §2.2, Regular Functions on a Closed Subset, p. 24
  - [`TopCat.Presheaf.germ`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.Presheaf.germ#doc) — [`Mathlib/Topology/Sheaves/Stalks.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Stalks.html)
- [x] Coordinate ring — §2.2, Regular Functions on a Closed Subset, p. 25
  - `Scheme.Γ` — [`Mathlib/AlgebraicGeometry/Scheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html)
- [x] Regular map — §2.3, Regular Maps, p. 27
  - [`Scheme.Hom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.Hom#doc) — [`Mathlib/AlgebraicGeometry/Scheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html)
- [x] Graph of a regular map — §2.3, Regular Maps, pp. 27–31
  - [`AlgebraicGeometry.graphMorphism`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.graphMorphism#doc) — `Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean`
- [x] Irreducible algebraic subset — §3.1, Irreducible Algebraic Subsets, p. 34
  - `IsIrreducible` — [`Mathlib/Topology/Irreducible.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Irreducible.html)
- [x] Irreducible component — §3.1, Irreducible Algebraic Subsets, p. 34
  - `irreducibleComponents` — [`Mathlib/Topology/Irreducible.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Irreducible.html)
- [x] Rational function field — §3.2, Rational Functions, p. 35
  - [`Scheme.functionField`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.functionField#doc) — [`Mathlib/AlgebraicGeometry/FunctionField.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/FunctionField.html)
- [x] Domain of definition of a rational function — §3.2, Rational Functions, p. 36
  - [`RationalMap.domain`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RationalMap.domain#doc) — [`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Birational/RationalMap.html)
- [x] Rational map of algebraic subsets — §3.3, Rational Maps, p. 37
  - [`AlgebraicGeometry.Scheme.RationalMap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Scheme.RationalMap#doc) — [`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Birational/RationalMap.html)
- [x] Closed subset of projective space — §4.1, Closed Subsets of Projective Space, p. 41
  - [`ProjectiveSpectrum.zeroLocus`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProjectiveSpectrum.zeroLocus#doc) — [`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.html)
- [x] Quasiprojective variety — §4.2, Regular Functions, p. 46
  - [`ProjectiveDefinitions.IsQuasiProjectiveVariety`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ProjectiveDefinitions.IsQuasiProjectiveVariety#doc) — `Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean`
- [x] Regular function on a quasiprojective variety — §4.2, Regular Functions, p. 46
  - `Scheme.Γ` — [`Mathlib/AlgebraicGeometry/Scheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html)
- [x] Regular map of quasiprojective varieties — §4.4, Examples of Regular Maps, p. 52
  - [`Scheme.Hom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.Hom#doc) — [`Mathlib/AlgebraicGeometry/Scheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Scheme.html)
- [ ] Product of quasiprojective varieties — §5.1, Products, p. 54
- [x] Finite map — §5.3, Finite Maps, p. 61
  - [`AlgebraicGeometry.IsFinite`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.IsFinite#doc) — [`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Morphisms/Finite.html)
- [x] Dimension of a variety — §6.1, Definition of Dimension, p. 67
  - `topologicalKrullDim` — [`Mathlib/Topology/KrullDimension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/KrullDimension.html)
- [x] Codimension — §6.1, Definition of Dimension, p. 67
  - [`Order.coheight`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Order.coheight#doc) — [`Mathlib/Order/KrullDimension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/KrullDimension.html)

## Chapter II. Local Properties

- [x] Local ring of a point — §1.1, The Local Ring of a Point, p. 83
  - [`TopCat.Presheaf.stalk`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.Presheaf.stalk#doc) — [`Mathlib/Topology/Sheaves/Stalks.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Stalks.html)
- [ ] Local ring along a subvariety — §1.1, The Local Ring of a Point, pp. 83–84
- [x] Tangent space — §1.2, The Tangent Space, p. 85
  - [`TauCeti.AlgebraicGeometry.ZariskiTangentSpace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.AlgebraicGeometry.ZariskiTangentSpace#doc) — `TauCeti/AlgebraicGeometry/TangentSpace/Basic.lean` (TauCeti)
- [x] Cotangent space — §1.2, The Tangent Space, pp. 85–86
  - [`Algebra.CotangentSpace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.CotangentSpace#doc) — [`Mathlib/RingTheory/Extension/Cotangent/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Extension/Cotangent/Basic.html)
- [x] Differential of a regular map — §1.3, Intrinsic Nature of the Tangent Space, pp. 86–91
  - `KaehlerDifferential` — [`Mathlib/RingTheory/Kaehler/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Kaehler/Basic.html)
- [x] Singular point of a variety — §1.4, Singular Points, p. 92
  - [`Scheme.IsSingularAtPoint`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.IsSingularAtPoint#doc) — `Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean`
  - Partial reference: [`SingularPoints.IsSingularPointIntrinsic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularPoints.IsSingularPointIntrinsic#doc) still uses finite affine Jacobian generators — `Atlas/ArithmeticGeometry/code/CoordinateRingSingular.lean`
- [x] Nonsingular point of a variety — §1.4, Singular Points, pp. 92–94
  - Partial reference: [`SingularPoints.IsNonsingularPointIntrinsic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularPoints.IsNonsingularPointIntrinsic#doc) still uses finite affine Jacobian generators — `Atlas/ArithmeticGeometry/code/CoordinateRingSingular.lean`
  - `IsRegularLocalRing` — [`Mathlib/RingTheory/RegularLocalRing/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/RegularLocalRing/Defs.html)
- [x] Tangent cone — §1.5, The Tangent Cone, p. 95
  - [`Definition38.tangentCone`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Definition38.tangentCone#doc) — `Atlas/AlgebraicGeometryI/code/GradedRingProjDef38.lean`
- [ ] Multiplicity of a singular point — §1.5, The Tangent Cone, p. 95
  - Partial reference: [`MvPolynomial.multiplicityAt`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MvPolynomial.multiplicityAt#doc) is a translated-polynomial multiplicity — `Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean`
- [ ] Local parameters — §2.1, Local Parameters at a Point, p. 98
- [x] Completion of a local ring — §2.2, Power Series Expansions, p. 104
  - `AdicCompletion` — [`Mathlib/RingTheory/AdicCompletion/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdicCompletion/Basic.html)
- [ ] Codimension-one subvariety — §3.1, Codimension 1 Subvarieties, p. 107
- [ ] Nonsingular subvariety — §3.2, Nonsingular Subvarieties, p. 111
- [ ] Blowup — §4.1, Blowup in Projective Space, p. 114
  - Partial reference: [`Blowup.blowupAlong`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Blowup.blowupAlong#doc) constructs the blowup of an affine scheme `Spec R` — `Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean`
- [ ] Centre of a blowup — §4.1, Blowup in Projective Space, p. 114
  - Partial reference: [`Blowup.blowupAtCenter`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Blowup.blowupAtCenter#doc) is tied to that affine Rees-algebra model — `Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean`
- [ ] Local blowup — §4.2, Local Blowup, p. 115
  - Partial reference: [`BlowupAtPoint.blowupAtPoint`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=BlowupAtPoint.blowupAtPoint#doc) is tied to a chosen affine Rees algebra — `Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean`
- [ ] Birational transform — §4.3, Behaviour of a Subvariety under a Blowup, p. 118
  - Partial reference: [`Blowup.properTransformSet`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Blowup.properTransformSet#doc) is a closure of subsets, not a scheme-theoretic transform — `Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean`
- [ ] Exceptional subvariety — §4.4, Exceptional Subvarieties, p. 119
  - Partial reference: [`Blowup.exceptionalLocusSet`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Blowup.exceptionalLocusSet#doc) is a preimage of closed subsets — `Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean`
- [x] Birational equivalence — §4.5, Isomorphism and Birational Equivalence, p. 121
  - [`AlgebraicGeometry.Birational`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Birational#doc) — [`Mathlib/AlgebraicGeometry/Birational/Birational.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Birational/Birational.html)
- [x] Normal variety — §5.1, Normal Varieties, pp. 125–128
  - `IsNormalScheme` — `reservoir-sources/leanprover__lean-eval/LeanEval/AlgebraicGeometry/TopologicalReconstruction.lean`
  - Partial reference: `IsNormalVariety` only defines normality for affine coordinate domains — `Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean`
- [x] Normalisation of an affine variety — §5.2, Normalisation of an Affine Variety, p. 129
  - [`Scheme.Hom.normalization`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.Hom.normalization#doc) — [`Mathlib/AlgebraicGeometry/Normalization.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Normalization.html)
- [x] Normalisation of a curve — §5.3, Normalisation of a Curve, p. 131
  - [`Scheme.Hom.normalization`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.Hom.normalization#doc) — [`Mathlib/AlgebraicGeometry/Normalization.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Normalization.html)
- [ ] Irreducible map — §6.1, Irreducibility, p. 139
- [x] Nonsingular map — §6.2, Nonsingularity, p. 141
  - [`AlgebraicGeometry.Smooth`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Smooth#doc) — [`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Morphisms/Smooth.html)
- [ ] Ramification point — §6.3, Ramification, p. 142
  - Partial reference: [`CurveMorphismData.IsRamifiedAt`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CurveMorphismData.IsRamifiedAt#doc) uses a height-one Dedekind-spectrum model — `Atlas/AlgebraicGeometryI/code/RamificationDivisor.lean`
- [ ] Branch point — §6.3, Ramification, p. 144
- [ ] Inseparable map — §6.3, Ramification, p. 144

## Chapter III. Divisors and Differential Forms

- [x] Prime divisor — §1.1, The Divisor of a Function, p. 151
  - [`IsDedekindDomain.HeightOneSpectrum`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IsDedekindDomain.HeightOneSpectrum#doc) — [`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Ideal/Basic.html)
- [x] Divisor — §1.1, The Divisor of a Function, p. 151
  - [`FunctionField.Chart.DivisorA`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.DivisorA#doc) — `RiemannRoch/Place.lean` (riemann-roch-function-fields)
- [x] Effective divisor — §1.1, The Divisor of a Function, p. 151
  - [`FunctionField.Chart.IsEffective`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.IsEffective#doc) — `RiemannRoch/FunctionField/Divisor.lean` (riemann-roch-function-fields)
- [ ] Divisor of zeros — §1.1, The Divisor of a Function, p. 153
  - Partial reference: [`CurveDivisor.divZeros`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CurveDivisor.divZeros#doc) splits an already-given divisor and does not attach it to a function — `Atlas/ArithmeticGeometry/code/Divisors.lean`
- [ ] Divisor of poles — §1.1, The Divisor of a Function, p. 153
  - Partial reference: [`CurveDivisor.divPoles`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CurveDivisor.divPoles#doc) splits an already-given divisor and does not attach it to a function — `Atlas/ArithmeticGeometry/code/Divisors.lean`
- [x] Principal divisor — §1.1, The Divisor of a Function, p. 153
  - [`FunctionField.Chart.principalDivisorA`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.principalDivisorA#doc) — `RiemannRoch/Place.lean` (riemann-roch-function-fields)
- [x] Linear equivalence of divisors — §1.2, Locally Principal Divisors, p. 155
  - Partial reference: [`LinearEquivDivisors.WeilLinearlyEquivalent`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearEquivDivisors.WeilLinearlyEquivalent#doc) is a relation modulo an arbitrary chosen subgroup — `Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean`
  - [`TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.LinearlyEquivalent`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.LinearlyEquivalent#doc) — `TauCeti/AlgebraicGeometry/WeilDivisor/Principal/Basic.lean` (TauCeti)
- [x] Divisor class group — §1.2, Locally Principal Divisors, p. 155
  - `ClassGroup` — [`Mathlib/RingTheory/ClassGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/ClassGroup.html)
- [x] Locally principal divisor — §1.2, Locally Principal Divisors, p. 155
  - `CartierDivisorGroupScheme` — `Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean`
  - `CartierDivisorDatum` — `Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean`
- [x] Linear system of a divisor — §1.5, The Linear System of a Divisor, p. 161
  - [`FunctionField.Chart.RRspace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.RRspace#doc) — `RiemannRoch/RRspace/Basic.lean` (riemann-roch-function-fields)
- [x] Complete linear system — §1.5, The Linear System of a Divisor, pp. 161–163
  - [`FunctionField.Chart.RRspace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.RRspace#doc) — `RiemannRoch/RRspace/Basic.lean` (riemann-roch-function-fields)
- [ ] Pencil of divisors — §1.6, Pencil of Conics, p. 164
- [x] Degree of a divisor on a curve — §2.1, The Degree of a Divisor of a Curve, p. 168
  - [`FunctionField.Chart.deg`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.deg#doc) — `RiemannRoch/FunctionField/Divisor.lean` (riemann-roch-function-fields)
- [x] Class group of a plane cubic — §3.1, The Class Group, p. 175
  - `ClassGroup` — [`Mathlib/RingTheory/ClassGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/ClassGroup.html)
- [x] Algebraic group — §4.1, Algebraic Groups, p. 188
  - `IsAlgebraicGroup` — `Atlas/ArithmeticGeometry/code/EllipticCurves.lean` (atlas-lean)
- [ ] Quotient algebraic group — §4.2, Quotient Groups and Chevalley’s Theorem, pp. 188–194
- [x] Differential 1-form — Chapter III, p. 195
  - [`FunctionField.Chart.WeilDifferential`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.WeilDifferential#doc) — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Rational differential form — Chapter III, p. 203
  - [`FunctionField.Chart.WeilDifferential`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.WeilDifferential#doc) — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Regular differential form — Chapter III, pp. 202–203
  - [`FunctionField.Chart.WeilDifferential`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.WeilDifferential#doc) — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Invariant differential form — Chapter III, p. 207
  - [`FunctionField.Chart.WeilDifferential`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.WeilDifferential#doc) — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Canonical differential — Chapter III, p. 209
  - [`FunctionField.Chart.WeilDifferential`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.WeilDifferential#doc) — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Genus of a curve — Chapter III, p. 210
  - [`FunctionField.Chart.genus`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FunctionField.Chart.genus#doc) — `RiemannRoch/Genus/Basic.lean` (riemann-roch-function-fields)

## Chapter IV. Intersection Theory

- [ ] Proper intersection — Chapter IV, p. 223
- [x] Intersection multiplicity — Chapter IV, pp. 223–225
  - `intersectionMultiplicity` — `reservoir-sources/leanprover__lean-eval/LeanEval/AlgebraicGeometry/Bezout.lean`
  - Partial reference: [`Lec5BezoutPascal.intersectionMultiplicity`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lec5BezoutPascal.intersectionMultiplicity#doc) treats affine plane curves only — `Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`
- [x] Local intersection number — Chapter IV, p. 224
  - `intersectionMultiplicity` — `reservoir-sources/leanprover__lean-eval/LeanEval/AlgebraicGeometry/Bezout.lean`
  - Partial reference: [`LocalIntersection.localIntersectionMultiplicity`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LocalIntersection.localIntersectionMultiplicity#doc) treats affine plane curves only — `Atlas/AlgebraicGeometryI/code/LocalIntersectionMultiplicity.lean`
- [ ] Order of tangency — Chapter IV, p. 225
- [x] Cycle — Chapter IV, p. 249
  - [`AlgebraicGeometry.AlgebraicCycle`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.AlgebraicCycle#doc) — [`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.html)
- [ ] Rational equivalence of cycles — Chapter IV, p. 249
- [ ] Numerical equivalence — Chapter IV, p. 238
- [ ] Néron–Severi group — Chapter IV, p. 238
- [ ] Intersection form on a surface — Chapter IV, p. 245
