---
title: "Hatcher algebraic topology definition catalogue"
---

- Author — Allen Hatcher
- Zotero key — `5UPFWXXF`
- Citekey — `Hat02`
- Source attachment — ``Hatcher - 2002 - Algebraic Topology.md``

## Chapter 0. Some Underlying Geometric Notions

- [x] Deformation retraction — “Homotopy and Homotopy Type,” p. 1
  - [`DeformationRetract.IsDeformationRetract`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DeformationRetract.IsDeformationRetract#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section5.lean`
- [x] Mapping cylinder
  - [`HomotopicalAlgebra.Cylinder`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomotopicalAlgebra.Cylinder#doc) — [`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/ModelCategory/Cylinder.html) — “Homotopy and Homotopy Type,” p. 1
- [x] Homotopy — “Homotopy and Homotopy Type,” p. 1
  - [`ContinuousMap.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousMap.Homotopy#doc) — [`Mathlib/Topology/Homotopy/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Basic.html)
- [x] Retraction — “Homotopy and Homotopy Type,” p. 1
  - [`CategoryTheory.IsSplitEpi`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.IsSplitEpi#doc) — [`Mathlib/CategoryTheory/EpiMono.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/EpiMono.html)
- [x] Homotopy equivalence — “Homotopy and Homotopy Type,” p. 1
  - [`ContinuousMap.HomotopyEquiv`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousMap.HomotopyEquiv#doc) — [`Mathlib/Topology/Homotopy/Equiv.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Equiv.html)
- [x] Contractible space — “Homotopy and Homotopy Type,” p. 1
  - `ContractibleSpace` — [`Mathlib/Topology/Homotopy/Contractible.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Contractible.html)
- [x] Cell complex
  - [`TopCat.RelativeCWComplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.RelativeCWComplex#doc) — [`Mathlib/Topology/CWComplex/Abstract/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Abstract/Basic.html) — “Cell Complexes,” p. 5
- [x] CW complex — “Cell Complexes,” p. 5
  - [`TopCat.CWComplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.CWComplex#doc) — [`Mathlib/Topology/CWComplex/Abstract/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Abstract/Basic.html)
- [x] Skeleton
  - [`RelCWComplex.skeleton`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RelCWComplex.skeleton#doc) — [`Mathlib/Topology/CWComplex/Classical/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html) — “Cell Complexes,” p. 5
- [x] Characteristic map — “Cell Complexes,” p. 5
  - `rpnCharMap` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section17.lean`
- [x] Subcomplex
  - [`RelCWComplex.Subcomplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=RelCWComplex.Subcomplex#doc) — [`Mathlib/Topology/CWComplex/Classical/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html) — “Cell Complexes,” p. 5
- [ ] Wedge sum — “Operations on Spaces,” p. 8
  - Partial reference: [`GroundZero.HITs.Wedge`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GroundZero.HITs.Wedge#doc) — `rzrn/ground_zero/GroundZero/HITs/Wedge.lean`
- [ ] Smash product — “Operations on Spaces,” p. 8
- [ ] Join — “Operations on Spaces,” p. 8
  - Partial reference: [`GroundZero.HITs.Join`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GroundZero.HITs.Join#doc) — `rzrn/ground_zero/GroundZero/HITs/Join.lean`
- [ ] Suspension — “Operations on Spaces,” p. 8
  - Partial reference: [`GroundZero.HITs.Suspension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GroundZero.HITs.Suspension#doc) — `rzrn/ground_zero/GroundZero/HITs/Suspension.lean`
- [x] Homotopy extension property — “The Homotopy Extension Property,” p. 14
  - `HasHomotopyExtensionProperty` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/HEP/Cofibration.lean`

## Chapter 1. The Fundamental Group

- [x] Path — §1.1, “Paths and Homotopy,” p. 25
  - `Path` — [`Mathlib/Topology/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Path.html)
- [x] Homotopy of paths — §1.1, “Paths and Homotopy,” p. 25
  - [`Path.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.Homotopy#doc) — [`Mathlib/Topology/Homotopy/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html)
- [x] Homotopy class of a path
  - [`Path.Homotopic.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.Homotopic.Quotient#doc) — [`Mathlib/Topology/Homotopy/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html) — §1.1, “Paths and Homotopy,” p. 25
- [x] Loop — §1.1, “Paths and Homotopy,” p. 25
  - `LoopSpace` — [`Mathlib/Topology/Homotopy/HomotopyGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/HomotopyGroup.html)
- [x] Fundamental group — §1.1, “Paths and Homotopy,” p. 25
  - `FundamentalGroup` — [`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html)
- [x] Reparametrization of a path — §1.1, “Paths and Homotopy,” p. 25
  - [`Path.reparam`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.reparam#doc) — [`Mathlib/Topology/Homotopy/Path.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html)
- [x] Induced homomorphism on fundamental groups — §1.1, “Induced Homomorphisms,” p. 34
  - [`FundamentalGroup.map`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=FundamentalGroup.map#doc) — [`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html)
- [x] Free product of groups — §1.2, “Free Products of Groups,” p. 41
  - Mathlib: [`Monoid.Coprod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Monoid.Coprod#doc) — [`Mathlib/GroupTheory/Coprod/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coprod/Basic.html)
- [x] Covering space
  - `IsCoveringMap` — [`Mathlib/Topology/Covering/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Covering/Basic.html) — §1.3, “Covering Spaces,” p. 56
- [x] Lift
  - [`IsCoveringMap.liftPath`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IsCoveringMap.liftPath#doc) — [`Mathlib/Topology/Homotopy/Lifting.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Lifting.html) — §1.3, “Lifting Properties,” p. 60
- [x] Deck transformation — §1.3, “Deck Transformations and Group Actions,” p. 70
  - [`TauCeti.Deck`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.Deck#doc) — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/UniversalCover/Deck/Basic.lean`
- [ ] Graph — §1.A, “Graphs and Free Groups,” p. 83
- [x] K(G,1) space — §1.B, “K(G,1) Spaces and Graphs of Groups,” p. 87
  - [`TauCeti.IsEilenbergMacLaneSpaceOne`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.IsEilenbergMacLaneSpaceOne#doc) — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [ ] Graph of groups — §1.B, “K(G,1) Spaces and Graphs of Groups,” p. 87

## Chapter 2. Homology

- [ ] Δ-complex — §2.1, “Δ-Complexes,” p. 102
- [x] Simplicial chain group — §2.1, “Simplicial Homology,” p. 104
  - [`SSet.chainComplexFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.chainComplexFunctor#doc) — [`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.html)
- [x] Simplicial homology — §2.1, “Simplicial Homology,” p. 104
  - [`SSet.homologyFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.homologyFunctor#doc) — [`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.html)
- [x] Singular simplex
  - [`TopCat.toSSetObjEquiv`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.toSSetObjEquiv#doc) — [`Mathlib/AlgebraicTopology/SingularSet.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularSet.html) — §2.1, “Singular Homology,” p. 108
- [x] Singular chain group — §2.1, “Singular Homology,” p. 108
  - [`AlgebraicTopology.singularChainComplexFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicTopology.singularChainComplexFunctor#doc) — [`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularHomology/Basic.html)
- [x] Singular homology — §2.1, “Singular Homology,” p. 108
  - [`AlgebraicTopology.singularHomologyFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicTopology.singularHomologyFunctor#doc) — [`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularHomology/Basic.html)
- [x] Relative homology group
  - `TopPair.HomologyPretheory.Hₚ` — [`Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/EilenbergSteenrod.html) — §2.1, “Relative Homology Groups,” p. 113
- [x] Degree of a map — §2.2, “Degree,” p. 134
  - [`DegreeTheory.degreeHom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DegreeTheory.degreeHom#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section10.lean`
- [x] Cellular homology — §2.2, “Cellular Homology,” p. 137
  - [`CWHomology.cellularHomologyGroup`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWHomology.cellularHomologyGroup#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section16.lean`
- [x] Euler characteristic — §2.2, “Cellular Homology,” p. 137
  - [`HomologicalComplex.homologyEulerChar`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.homologyEulerChar#doc) — [`Mathlib/Algebra/Homology/EulerCharacteristic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/EulerCharacteristic.html)
- [x] Mayer–Vietoris sequence — §2.2, “Mayer–Vietoris Sequences,” p. 149
  - [`MayerVietoris.MayerVietorisSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MayerVietoris.MayerVietorisSequence#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean`
- [x] Homology with coefficients — §2.2, “Homology with Coefficients,” p. 153
  - [`AlgebraicTopology.singularHomologyFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicTopology.singularHomologyFunctor#doc) — [`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularHomology/Basic.html)
- [x] Homology theory — §2.3, “Axioms for Homology,” p. 160
  - [`TopPair.HomologyPretheory`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopPair.HomologyPretheory#doc) — [`Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/EilenbergSteenrod.html)
- [x] Category — §2.3, “Categories and Functors,” p. 162
  - [`CategoryTheory.Category`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Category#doc) — [`Mathlib/CategoryTheory/Category/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- [x] Functor — §2.3, “Categories and Functors,” p. 162
  - [`CategoryTheory.Functor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor#doc) — [`Mathlib/CategoryTheory/Functor/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Basic.html)
- [ ] Simplicial approximation — §2.C, “Simplicial Approximation,” p. 177
- [ ] Lefschetz number — §2.C, “The Lefschetz Fixed Point Theorem,” p. 177

## Chapter 3. Cohomology

- [x] Cohomology group — §3.1, “Cohomology Groups,” p. 190
  - [`SingularCohomology.singularCohomology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularCohomology.singularCohomology#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cohomology with coefficients — §3.1, “Cohomology of Spaces,” p. 197
  - [`SingularCohomology.singularCohomology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularCohomology.singularCohomology#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cup product — §3.2, “Cup Product,” p. 206
  - [`SingularCohomology.cupProduct`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularCohomology.cupProduct#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cohomology ring — §3.2, “The Cohomology Ring,” p. 212
  - [`SingularCohomology.instGRingCohomologyFamily`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularCohomology.instGRingCohomologyFamily#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section29.lean`
- [x] Orientation of a manifold — §3.3, “Orientations and Homology,” p. 233
  - [`OrientationHomology.ROrientation`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=OrientationHomology.ROrientation#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section31.lean`
- [x] Fundamental class — §3.3, “Orientations and Homology,” p. 233
  - [`PoincareDuality.fundamentalClass`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PoincareDuality.fundamentalClass#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section38.lean`
- [ ] Cohomology with compact supports — §3.3, “Cohomology with Compact Supports,” p. 230
- [x] Cross product in homology — §3.B, “The Cross Product in Homology,” p. 268
  - [`SingularCohomology.homologyCross`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SingularCohomology.homologyCross#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section33.lean`
- [x] H-space — §3.C, “H-Spaces and Hopf Algebras,” p. 281
  - `HSpace` — [`Mathlib/Topology/Homotopy/HSpaces.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/HSpaces.html)
- [x] Hopf algebra — §3.C, “Hopf Algebras,” p. 281
  - `HopfAlgebra` — [`Mathlib/RingTheory/HopfAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/HopfAlgebra/Basic.html)
- [ ] Pontryagin product — §3.C, “Pontryagin Product,” p. 281
- [x] Direct limit — §3.F, “Direct and Inverse Limits,” p. 311
  - [`CategoryTheory.Limits.colimit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.colimit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Inverse limit — §3.F, “Direct and Inverse Limits,” p. 311
  - [`CategoryTheory.Limits.limit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.limit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Local coefficient system — §3.H, “Local Coefficients,” p. 327
  - [`LocalCoefficientSystems.LocalCoefficientSystem`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LocalCoefficientSystems.LocalCoefficientSystem#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section31.lean`

## Chapter 4. Homotopy Theory

- [x] Homotopy group — §4.1, “Definitions and Basic Constructions,” p. 340
  - `HomotopyGroup` — [`Mathlib/Topology/Homotopy/HomotopyGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/HomotopyGroup.html)
- [ ] Relative homotopy group — §4.1, “Definitions and Basic Constructions,” p. 340
- [x] Weak homotopy equivalence
  - [`HomotopicalAlgebra.WeakEquivalence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomotopicalAlgebra.WeakEquivalence#doc) — [`Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.html) — §4.1, “Whitehead's Theorem,” p. 346
- [ ] CW approximation — §4.1, “CW Approximation,” p. 352
- [x] Eilenberg–Mac Lane space — §4.2, “Eilenberg–Mac Lane Spaces,” p. 360
  - [`TauCeti.IsEilenbergMacLaneSpaceOne`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TauCeti.IsEilenbergMacLaneSpaceOne#doc) — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [x] Fiber bundle — §4.2, “Fiber Bundles,” p. 375
  - `FiberBundle` — [`Mathlib/Topology/FiberBundle/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FiberBundle/Basic.html)
- [ ] Stable homotopy group — §4.2, “Stable Homotopy Groups,” p. 384
- [x] Fibration
  - [`HomotopicalAlgebra.Fibration`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomotopicalAlgebra.Fibration#doc) — [`Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.html) — §4.3, “Fibrations,” p. 405
- [x] Pathspace — §4.3, “Pathspace Constructions,” p. 405
  - [`HomotopicalAlgebra.PathObject`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomotopicalAlgebra.PathObject#doc) — [`Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/ModelCategory/PathObject.html)
- [ ] Postnikov tower — §4.3, “Postnikov Towers,” p. 410
- [ ] Obstruction cocycle — §4.3, “Obstruction Theory,” p. 415
- [ ] Hopf invariant — §4.B, “The Hopf Invariant,” p. 427
- [ ] Spectrum — §4.F, “Spectra and Homology Theories,” p. 452
- [x] Generalized homology theory — §4.F, “Spectra and Homology Theories,” p. 452
  - Mathlib: `HomologyPretheory` and its Eilenberg–Steenrod axiom classes — [`Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/EilenbergSteenrod.html)
- [ ] Homotopy group with coefficients — §4.H, “Homotopy Groups with Coefficients,” p. 460
- [ ] Quasifibration — §4.K, “Quasifibrations,” p. 475
- [ ] Symmetric product — §4.K, “Symmetric Products,” p. 475
- [ ] Steenrod square — §4.L, “Steenrod Squares and Powers,” p. 487
- [ ] Steenrod power — §4.L, “Steenrod Squares and Powers,” p. 487
- [ ] Steenrod algebra — §4.L, “Adem Relations and the Steenrod Algebra,” p. 487

## Appendix. Topology of Cell Complexes

- [x] Weak topology on a CW complex — “Topology of Cell Complexes,” p. 519
  - [`CWComplex.closed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWComplex.closed#doc) — [`Mathlib/Topology/CWComplex/Classical/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html)
- [x] Compact-open topology — “The Compact-Open Topology,” p. 529
  - [`ContinuousMap.compactOpen`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousMap.compactOpen#doc) — [`Mathlib/Topology/CompactOpen.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html)
- [x] Euclidean neighborhood retract — “Euclidean Neighborhood Retracts,” p. 519
  - `IsNeighborhoodRetract` — `facebookresearch__atlas-lean/Atlas/AlgebraicTopologyI/code/Section34.lean`
- [ ] Space dominated by a CW complex — “Spaces Dominated by CW Complexes,” p. 519
