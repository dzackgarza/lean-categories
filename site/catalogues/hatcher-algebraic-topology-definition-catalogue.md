---
title: "Hatcher algebraic topology definition catalogue"
---

# *Algebraic Topology*: definition catalogue

- Author — Allen Hatcher
- Zotero key — `5UPFWXXF`
- Citekey — `Hat02`
- Source attachment — ``Hatcher - 2002 - Algebraic Topology.md``

## Chapter 0. Some Underlying Geometric Notions

- [x] Deformation retraction — “Homotopy and Homotopy Type,” p. 1
  - `DeformationRetract.IsDeformationRetract` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section5.lean`
- [x] Mapping cylinder
  - `HomotopicalAlgebra.Cylinder` — `Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean` — “Homotopy and Homotopy Type,” p. 1
- [x] Homotopy — “Homotopy and Homotopy Type,” p. 1
  - `ContinuousMap.Homotopy` — `Mathlib/Topology/Homotopy/Basic.lean`
- [x] Retraction — “Homotopy and Homotopy Type,” p. 1
  - `CategoryTheory.IsSplitEpi` — `Mathlib/CategoryTheory/EpiMono.lean`
- [x] Homotopy equivalence — “Homotopy and Homotopy Type,” p. 1
  - `ContinuousMap.HomotopyEquiv` — `Mathlib/Topology/Homotopy/Equiv.lean`
- [x] Contractible space — “Homotopy and Homotopy Type,” p. 1
  - `ContractibleSpace` — `Mathlib/Topology/Homotopy/Contractible.lean`
- [x] Cell complex
  - `TopCat.RelativeCWComplex` — `Mathlib/Topology/CWComplex/Abstract/Basic.lean` — “Cell Complexes,” p. 5
- [x] CW complex — “Cell Complexes,” p. 5
  - `TopCat.CWComplex` — `Mathlib/Topology/CWComplex/Abstract/Basic.lean`
- [x] Skeleton
  - `RelCWComplex.skeleton` — `Mathlib/Topology/CWComplex/Classical/Basic.lean` — “Cell Complexes,” p. 5
- [x] Characteristic map — “Cell Complexes,” p. 5
  - `rpnCharMap` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section17.lean`
- [x] Subcomplex
  - `RelCWComplex.Subcomplex` — `Mathlib/Topology/CWComplex/Classical/Basic.lean` — “Cell Complexes,” p. 5
- [ ] Wedge sum — “Operations on Spaces,” p. 8
  - Partial reference: `GroundZero.HITs.Wedge` — `rzrn/ground_zero/GroundZero/HITs/Wedge.lean`
- [ ] Smash product — “Operations on Spaces,” p. 8
- [ ] Join — “Operations on Spaces,” p. 8
  - Partial reference: `GroundZero.HITs.Join` — `rzrn/ground_zero/GroundZero/HITs/Join.lean`
- [ ] Suspension — “Operations on Spaces,” p. 8
  - Partial reference: `GroundZero.HITs.Suspension` — `rzrn/ground_zero/GroundZero/HITs/Suspension.lean`
- [x] Homotopy extension property — “The Homotopy Extension Property,” p. 14
  - `HasHomotopyExtensionProperty` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/HEP/Cofibration.lean`

## Chapter 1. The Fundamental Group

- [x] Path — §1.1, “Paths and Homotopy,” p. 25
  - `Path` — `Mathlib/Topology/Path.lean`
- [x] Homotopy of paths — §1.1, “Paths and Homotopy,” p. 25
  - `Path.Homotopy` — `Mathlib/Topology/Homotopy/Path.lean`
- [x] Homotopy class of a path
  - `Path.Homotopic.Quotient` — `Mathlib/Topology/Homotopy/Path.lean` — §1.1, “Paths and Homotopy,” p. 25
- [x] Loop — §1.1, “Paths and Homotopy,” p. 25
  - `LoopSpace` — `Mathlib/Topology/Homotopy/HomotopyGroup.lean`
- [x] Fundamental group — §1.1, “Paths and Homotopy,” p. 25
  - `FundamentalGroup` — `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`
- [x] Reparametrization of a path — §1.1, “Paths and Homotopy,” p. 25
  - `Path.reparam` — `Mathlib/Topology/Homotopy/Path.lean`
- [x] Induced homomorphism on fundamental groups — §1.1, “Induced Homomorphisms,” p. 34
  - `FundamentalGroup.map` — `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`
- [x] Free product of groups — §1.2, “Free Products of Groups,” p. 41
  - Mathlib: `Monoid.Coprod` — `Mathlib/GroupTheory/Coprod/Basic.lean`
- [x] Covering space
  - `IsCoveringMap` — `Mathlib/Topology/Covering/Basic.lean` — §1.3, “Covering Spaces,” p. 56
- [x] Lift
  - `IsCoveringMap.liftPath` — `Mathlib/Topology/Homotopy/Lifting.lean` — §1.3, “Lifting Properties,” p. 60
- [x] Deck transformation — §1.3, “Deck Transformations and Group Actions,” p. 70
  - `TauCeti.Deck` — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/UniversalCover/Deck/Basic.lean`
- [ ] Graph — §1.A, “Graphs and Free Groups,” p. 83
- [x] K(G,1) space — §1.B, “K(G,1) Spaces and Graphs of Groups,” p. 87
  - `TauCeti.IsEilenbergMacLaneSpaceOne` — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [ ] Graph of groups — §1.B, “K(G,1) Spaces and Graphs of Groups,” p. 87

## Chapter 2. Homology

- [ ] Δ-complex — §2.1, “Δ-Complexes,” p. 102
- [x] Simplicial chain group — §2.1, “Simplicial Homology,” p. 104
  - `SSet.chainComplexFunctor` — `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`
- [x] Simplicial homology — §2.1, “Simplicial Homology,” p. 104
  - `SSet.homologyFunctor` — `Mathlib/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`
- [x] Singular simplex
  - `TopCat.toSSetObjEquiv` — `Mathlib/AlgebraicTopology/SingularSet.lean` — §2.1, “Singular Homology,” p. 108
- [x] Singular chain group — §2.1, “Singular Homology,” p. 108
  - `AlgebraicTopology.singularChainComplexFunctor` — `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
- [x] Singular homology — §2.1, “Singular Homology,” p. 108
  - `AlgebraicTopology.singularHomologyFunctor` — `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
- [x] Relative homology group
  - `TopPair.HomologyPretheory.Hₚ` — `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean` — §2.1, “Relative Homology Groups,” p. 113
- [x] Degree of a map — §2.2, “Degree,” p. 134
  - `DegreeTheory.degreeHom` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section10.lean`
- [x] Cellular homology — §2.2, “Cellular Homology,” p. 137
  - `CWHomology.cellularHomologyGroup` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section16.lean`
- [x] Euler characteristic — §2.2, “Cellular Homology,” p. 137
  - `HomologicalComplex.homologyEulerChar` — `Mathlib/Algebra/Homology/EulerCharacteristic.lean`
- [x] Mayer–Vietoris sequence — §2.2, “Mayer–Vietoris Sequences,” p. 149
  - `MayerVietoris.MayerVietorisSequence` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean`
- [x] Homology with coefficients — §2.2, “Homology with Coefficients,” p. 153
  - `AlgebraicTopology.singularHomologyFunctor` — `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
- [x] Homology theory — §2.3, “Axioms for Homology,” p. 160
  - `TopPair.HomologyPretheory` — `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`
- [x] Category — §2.3, “Categories and Functors,” p. 162
  - `CategoryTheory.Category` — `Mathlib/CategoryTheory/Category/Basic.lean`
- [x] Functor — §2.3, “Categories and Functors,” p. 162
  - `CategoryTheory.Functor` — `Mathlib/CategoryTheory/Functor/Basic.lean`
- [ ] Simplicial approximation — §2.C, “Simplicial Approximation,” p. 177
- [ ] Lefschetz number — §2.C, “The Lefschetz Fixed Point Theorem,” p. 177

## Chapter 3. Cohomology

- [x] Cohomology group — §3.1, “Cohomology Groups,” p. 190
  - `SingularCohomology.singularCohomology` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cohomology with coefficients — §3.1, “Cohomology of Spaces,” p. 197
  - `SingularCohomology.singularCohomology` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cup product — §3.2, “Cup Product,” p. 206
  - `SingularCohomology.cupProduct` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section26.lean`
- [x] Cohomology ring — §3.2, “The Cohomology Ring,” p. 212
  - `SingularCohomology.instGRingCohomologyFamily` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section29.lean`
- [x] Orientation of a manifold — §3.3, “Orientations and Homology,” p. 233
  - `OrientationHomology.ROrientation` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section31.lean`
- [x] Fundamental class — §3.3, “Orientations and Homology,” p. 233
  - `PoincareDuality.fundamentalClass` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section38.lean`
- [ ] Cohomology with compact supports — §3.3, “Cohomology with Compact Supports,” p. 230
- [x] Cross product in homology — §3.B, “The Cross Product in Homology,” p. 268
  - `SingularCohomology.homologyCross` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section33.lean`
- [x] H-space — §3.C, “H-Spaces and Hopf Algebras,” p. 281
  - `HSpace` — `Mathlib/Topology/Homotopy/HSpaces.lean`
- [x] Hopf algebra — §3.C, “Hopf Algebras,” p. 281
  - `HopfAlgebra` — `Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- [ ] Pontryagin product — §3.C, “Pontryagin Product,” p. 281
- [x] Direct limit — §3.F, “Direct and Inverse Limits,” p. 311
  - `CategoryTheory.Limits.colimit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Inverse limit — §3.F, “Direct and Inverse Limits,” p. 311
  - `CategoryTheory.Limits.limit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Local coefficient system — §3.H, “Local Coefficients,” p. 327
  - `LocalCoefficientSystems.LocalCoefficientSystem` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section31.lean`

## Chapter 4. Homotopy Theory

- [x] Homotopy group — §4.1, “Definitions and Basic Constructions,” p. 340
  - `HomotopyGroup` — `Mathlib/Topology/Homotopy/HomotopyGroup.lean`
- [ ] Relative homotopy group — §4.1, “Definitions and Basic Constructions,” p. 340
- [x] Weak homotopy equivalence
  - `HomotopicalAlgebra.WeakEquivalence` — `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean` — §4.1, “Whitehead's Theorem,” p. 346
- [ ] CW approximation — §4.1, “CW Approximation,” p. 352
- [x] Eilenberg–Mac Lane space — §4.2, “Eilenberg–Mac Lane Spaces,” p. 360
  - `TauCeti.IsEilenbergMacLaneSpaceOne` — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [x] Fiber bundle — §4.2, “Fiber Bundles,” p. 375
  - `FiberBundle` — `Mathlib/Topology/FiberBundle/Basic.lean`
- [ ] Stable homotopy group — §4.2, “Stable Homotopy Groups,” p. 384
- [x] Fibration
  - `HomotopicalAlgebra.Fibration` — `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean` — §4.3, “Fibrations,” p. 405
- [x] Pathspace — §4.3, “Pathspace Constructions,” p. 405
  - `HomotopicalAlgebra.PathObject` — `Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean`
- [ ] Postnikov tower — §4.3, “Postnikov Towers,” p. 410
- [ ] Obstruction cocycle — §4.3, “Obstruction Theory,” p. 415
- [ ] Hopf invariant — §4.B, “The Hopf Invariant,” p. 427
- [ ] Spectrum — §4.F, “Spectra and Homology Theories,” p. 452
- [x] Generalized homology theory — §4.F, “Spectra and Homology Theories,” p. 452
  - Mathlib: `HomologyPretheory` and its Eilenberg–Steenrod axiom classes — `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`
- [ ] Homotopy group with coefficients — §4.H, “Homotopy Groups with Coefficients,” p. 460
- [ ] Quasifibration — §4.K, “Quasifibrations,” p. 475
- [ ] Symmetric product — §4.K, “Symmetric Products,” p. 475
- [ ] Steenrod square — §4.L, “Steenrod Squares and Powers,” p. 487
- [ ] Steenrod power — §4.L, “Steenrod Squares and Powers,” p. 487
- [ ] Steenrod algebra — §4.L, “Adem Relations and the Steenrod Algebra,” p. 487

## Appendix. Topology of Cell Complexes

- [x] Weak topology on a CW complex — “Topology of Cell Complexes,” p. 519
  - `CWComplex.closed` — `Mathlib/Topology/CWComplex/Classical/Basic.lean`
- [x] Compact-open topology — “The Compact-Open Topology,” p. 529
  - `ContinuousMap.compactOpen` — `Mathlib/Topology/CompactOpen.lean`
- [x] Euclidean neighborhood retract — “Euclidean Neighborhood Retracts,” p. 519
  - `IsNeighborhoodRetract` — `facebookresearch__atlas-lean/Atlas/AlgebraicTopologyI/code/Section34.lean`
- [ ] Space dominated by a CW complex — “Spaces Dominated by CW Complexes,” p. 519
