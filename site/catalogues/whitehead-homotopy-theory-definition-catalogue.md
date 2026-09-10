---
title: "Whitehead homotopy theory definition catalogue"
---

# *Elements of Homotopy Theory*: definition catalogue

- Author — George W. Whitehead
- Zotero key — `IAQXVT6W`
- Citekey — `Whi78`
- Source attachment — ``local-write-api-1783392216311-IAQXVT6W_extracted.md``

## Chapter I. Introductory Notions

- [ ] Extension problem — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [x] Homotopy extension problem — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
  - `HasHomotopyExtensionProperty` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/HEP/Cofibration.lean`
- [x] Cofibration
  - `HomotopicalAlgebra.Cofibration` — `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean` — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [x] Lifting problem
  - `CategoryTheory.HasLiftingProperty` — `Mathlib/CategoryTheory/LiftingProperties/Basic.lean` — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [x] Fibration
  - `HomotopicalAlgebra.Fibration` — `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean` — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3; §7, “Fibrations,” p. 29
- [x] Homotopy of maps of pairs — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
  - `TopPair.Homotopy` — `Mathlib/Topology/Category/TopPair.lean`
- [ ] Λ-space — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [ ] Λ-map — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [ ] Λ-homotopy — §1, “The Fundamental Problems: Extension, Homotopy, and Classification,” p. 3
- [x] Singular simplex
  - `TopCat.toSSetObjEquiv` — `Mathlib/AlgebraicTopology/SingularSet.lean` — §2, “Standard Notations and Conventions,” p. 9
- [x] Total singular complex — §2, “Standard Notations and Conventions,” p. 9
  - `TopCat.toSSet` — `Mathlib/AlgebraicTopology/SingularSet.lean`
- [x] Compactly generated space — §4, “Compactly Generated Spaces,” p. 17
  - `CompactlyGeneratedSpace` — `Mathlib/Topology/Compactness/CompactlyGeneratedSpace.lean`
- [ ] NDR-pair — §5, “NDR-pairs,” p. 21
- [ ] Filtered space — §6, “Filtered Spaces,” p. 27

## Chapter II. CW-complexes

- [x] Relative CW-complex — §1, “Construction of CW-complexes,” p. 48
  - `TopCat.RelativeCWComplex` — `Mathlib/Topology/CWComplex/Abstract/Basic.lean`
- [x] CW-complex — §1, “Construction of CW-complexes,” p. 48
  - `TopCat.CWComplex` — `Mathlib/Topology/CWComplex/Abstract/Basic.lean`
- [x] Cellular map — §4, “Cellular Maps,” p. 76
  - `CWHomology.IsCellularMap` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section16.lean`
- [ ] Regular cell complex — §6, “Regular Cell Complexes,” p. 81
- [x] Cohomology ring — §7, “Products and the Cohomology Ring,” p. 88
  - `SingularCohomology.instGRingCohomologyFamily` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section29.lean`

## Chapter III. Generalities on Homotopy Classes of Mappings

- [x] Based space
  - `Pointed` — `Mathlib/CategoryTheory/Category/Pointed.lean` — §2, “Spaces with Base Points,” p. 102
- [x] Based map
  - `Pointed.Hom` — `Mathlib/CategoryTheory/Category/Pointed.lean` — §2, “Spaces with Base Points,” p. 102
- [ ] Reduced suspension — §2, “Spaces with Base Points,” p. 102
  - Partial reference: `GroundZero.HITs.Suspension` — `rzrn/ground_zero/GroundZero/HITs/Suspension.lean`
- [ ] Smash product — §2, “Spaces with Base Points,” p. 102
- [x] H-space — §4, “H-spaces,” p. 116
  - `HSpace` — `Mathlib/Topology/Homotopy/HSpaces.lean`
- [ ] H′-space — §5, “H′-spaces,” p. 121
- [ ] Exact sequence of mapping functors — §6, “Exact Sequences of Mapping Functors,” p. 127
- [x] Hopf algebra — §8, “Hopf Algebras,” p. 149
  - `HopfAlgebra` — `Mathlib/RingTheory/HopfAlgebra/Basic.lean`

## Chapter IV. Homotopy Groups

- [x] Relative homotopy group — §1, “Relative Homotopy Groups,” p. 158
  - `RelHomotopyGroup` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/RelHomotopyGroup/Defs.lean`
- [x] Homotopy sequence — §2, “The Homotopy Sequence,” p. 161
  - `isExactAt_iStar_jStar`, `isExactAt_jStar_bd`, `isExactAt_bd_iStar` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/RelHomotopyGroup/LongExactSeq.lean`
- [x] Action of the fundamental group on higher homotopy groups — §3, “The Operations of the Fundamental Group on the Homotopy Sequence,” p. 164
  - `HomotopyGroup.changeBasePt`, `FundamentalGroupoid.changeBasePt` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/HomotopyGroup/ChangeBasePt.lean`
- [ ] Hurewicz map — §4, “The Hurewicz Map,” p. 166
  - Partial reference: `Model.UnstructuredUniverse.Cylinder.Hurewicz` — `sinhp/HoTTLean/HoTTLean/Model/Unstructured/Hurewicz.lean`
- [ ] Eilenberg homology group — §5, “The Eilenberg and Blakers Homology Groups,” p. 170
- [ ] Blakers homology group — §5, “The Eilenberg and Blakers Homology Groups,” p. 170

## Chapter V. Homotopy Theory of CW-complexes

- [x] Weak homotopy equivalence
  - `HomotopicalAlgebra.WeakEquivalence` — `Mathlib/AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean` — §3, “Weak Homotopy Equivalence and CW-approximation,” p. 219
- [x] CW-approximation — §3, “Weak Homotopy Equivalence and CW-approximation,” p. 219
  - `TopCat.IsCompressible.relCWComplex_of_isWeakHomotopyEquiv` — `reservoir-sources/Vilin97__lean-pool/LeanPool/WhiteheadTheorem/Compressible/WeakEquiv.lean`
- [x] Aspherical space — §4, “Aspherical Spaces,” p. 224
  - `TauCeti.IsAspherical` — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [ ] Obstruction cocycle — §5, “Obstruction Theory,” p. 228
- [x] Eilenberg–Mac Lane space — §7, “Eilenberg–Mac Lane Spaces,” p. 244
  - `TauCeti.IsEilenbergMacLaneSpaceOne` — `TauCetiProject/TauCeti/TauCeti/AlgebraicTopology/EilenbergMacLane/Basic.lean`
- [ ] Cohomology operation — §8, “Cohomology Operations,” p. 250

## Chapter VI. Homology with Local Coefficients

- [ ] Bundle of groups — §1, “Bundles of Groups,” p. 257
- [x] Local coefficient system — §1, “Bundles of Groups,” p. 257
  - `LocalCoefficientSystems.LocalCoefficientSystem` — `facebookresearch/atlas-lean/Atlas/AlgebraicTopologyI/code/Section31.lean`
- [ ] Homology with local coefficients — §2, “Homology with Local Coefficients,” p. 265
- [ ] Primary obstruction to a lifting — §6, “The Primary Obstruction to a Lifting,” p. 297
- [ ] Characteristic class of a vector bundle — §7, “Characteristic Classes of Vector Bundles,” p. 305

## Chapter VII. Homology of Fibre Spaces: Elementary Theory

- [ ] James reduced product — §2, “The James Reduced Products,” p. 326
- [ ] Wang sequence — §3, “Further Properties of the Wang Sequence,” p. 336
- [ ] Homology sequence of a fibration — §6, “The Homology Sequence of a Fibration,” p. 363

## Chapter VIII. The Homology Suspension

- [ ] Homology suspension — §1, “The Homology Suspension,” p. 373
- [ ] Stable cohomology operation — §5, “Stable Operations,” p. 390
- [ ] Mod 2 Steenrod algebra — §6, “The mod 2 Steenrod Algebra,” p. 394
- [ ] Cartan product — §7, “The Cartan Product Formula,” p. 397
- [ ] Steenrod square — §8, “Some Relations among the Steenrod Squares,” p. 403

## Chapter IX. Postnikov Systems

- [ ] Connective fibration — §1, “Connective Fibrations,” p. 417
- [ ] Postnikov system — §2, “The Postnikov Invariants of a Space,” p. 421
- [ ] Postnikov invariant — §2, “The Postnikov Invariants of a Space,” p. 421
- [ ] Relative Postnikov system — §6, “Relative Postnikov Systems,” p. 443

## Chapter X. On Mappings into Group-like Spaces

- [ ] Category of a space — §1, “The Category of a Space,” p. 457
- [ ] H₀-space — §2, “H₀-spaces,” p. 461
- [ ] Nilpotency of [X,G] — §3, “Nilpotency of [X,G],” p. 462
- [ ] Samelson product — §5, “The Samelson Product,” p. 467
- [ ] Whitehead product — §7, “The Whitehead Product,” p. 472
- [ ] Composition product in homotopy groups — §8, “Operations in Homotopy Groups,” p. 478
- [ ] Reduced join — §8, “Operations in Homotopy Groups,” p. 478
  - Partial reference: `GroundZero.HITs.Join` — `rzrn/ground_zero/GroundZero/HITs/Join.lean`

## Chapter XI. Homotopy Operations

- [ ] Homotopy operation — §1, “Homotopy Operations,” p. 490
- [ ] Hopf invariant — §2, “The Hopf Invariant,” p. 494
- [ ] Functional cup product — §3, “The Functional Cup Product,” p. 496
- [ ] Hopf construction — §4, “The Hopf Construction,” p. 502
- [ ] Hopf-Hilton invariant — §8, “The Hopf-Hilton Invariants,” p. 533

## Chapter XII. Stable Homotopy and Homology

- [ ] Suspension category — §3, “The Suspension Category,” p. 550
- [ ] S-map — §3, “The Suspension Category,” p. 550
- [ ] Stable homotopy group — §3, “The Suspension Category,” p. 550
- [ ] Stable homotopy theory — §5, “Stable Homotopy as a Homology Theory,” p. 571
- [x] Generalized homology theory — §6, “Comparison with the Eilenberg-Steenrod Axioms,” p. 578
  - `TopPair.HomologyPretheory` — `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`
- [x] Generalized cohomology theory — §7, “Cohomology Theories,” p. 594
  - Mathlib: the dual of `HomologyPretheory` — `Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`

## Chapter XIII. Homology of Fibre Spaces

- [ ] Exact couple — §2, “Exact Couples,” p. 609
- [ ] Spectral sequence of a filtered space — §3, “The Exact Couples of a Filtered Space,” p. 613
- [ ] Spectral sequence of a fibration — §4, “The Spectral Sequence of a Fibration,” p. 623
- [ ] Atiyah-Hirzebruch spectral sequence — §6, “The Atiyah-Hirzebruch Spectral Sequence,” p. 640
- [ ] Leray–Serre spectral sequence — §7, “The Leray–Serre Spectral Sequence,” p. 645
