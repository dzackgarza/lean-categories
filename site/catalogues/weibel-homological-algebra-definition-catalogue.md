---
title: "Weibel homological algebra definition catalogue"
---

# *An Introduction to Homological Algebra*: definition catalogue

- Author — Charles A. Weibel
- Zotero key — `8XN9IJSP`
- Citekey — `Wei94`
- Source attachment — ``Weibel - 1994 - An Introduction to Homological Algebra.md``

## Chapter 1. Chain Complexes

- [x] Chain complex — §1.1, “Complexes of R-Modules,” p. 1; Definition 1.1.1
  - `ChainComplex` — `Mathlib/Algebra/Homology/HomologicalComplex.lean`
- [x] Quasi-isomorphism — §1.1, “Complexes of R-Modules,” p. 1; Definition 1.1.2
  - `QuasiIso` — `Mathlib/Algebra/Homology/QuasiIso.lean`
- [x] Kernel — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.1
  - `CategoryTheory.Limits.kernel` — `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`
- [x] Cokernel — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.1
  - `CategoryTheory.Limits.cokernel` — `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`
- [x] Abelian category — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.2
  - `CategoryTheory.Abelian` — `Mathlib/CategoryTheory/Abelian/Basic.lean`
- [x] Split complex — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.1
  - `Homotopy (1_C) 0` via `HomologicalComplex.Homotopy` — `Mathlib/Algebra/Homology/Homotopy.lean`
- [x] Split exact complex — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.1
  - `Homotopy (1_C) 0` implies acyclicity (homotopic identity → zero on homology) — `Mathlib/Algebra/Homology/Homotopy.lean`
- [x] Null-homotopic chain map — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.3
  - `HomologicalComplex.Homotopy` — `Mathlib/Algebra/Homology/Homotopy.lean`
- [x] Chain homotopy — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.4
  - `HomologicalComplex.Homotopy` — `Mathlib/Algebra/Homology/Homotopy.lean`
- [x] Mapping cone — §1.5, “Mapping Cones and Cylinders,” p. 18
  - `HomologicalComplex.mappingCone` — `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`
- [x] Mapping cylinder
  - `HomologicalComplex.cylinder` — `Mathlib/Algebra/Homology/HomotopyCofiber.lean` — §1.5, “Mapping Cones and Cylinders,” p. 18
- [x] Sheaf — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.5
  - `TopCat.Sheaf` — `Mathlib/Topology/Sheaves/Sheaf.lean`
- [x] Left exact functor — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.6
  - `CategoryTheory.LeftExactFunctor` — `Mathlib/CategoryTheory/Limits/ExactFunctor.lean`
- [x] Right exact functor — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.6
  - `CategoryTheory.RightExactFunctor` — `Mathlib/CategoryTheory/Limits/ExactFunctor.lean`

## Chapter 2. Derived Functors

- [x] Homological δ-functor — §2.1, “δ-Functors,” p. 30; Definition 2.1.1
  - `category_theory.delta_functor` — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Cohomological δ-functor — §2.1, “δ-Functors,” p. 30; Definition 2.1.1
  - `category_theory.delta_functor` — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Morphism of δ-functors — §2.1, “δ-Functors,” p. 30; Definition 2.1.4
  - `category_theory.delta_functor.hom` — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Left resolution — §2.2, “Projective Resolutions,” p. 33; Definition 2.2.4
  - `CategoryTheory.ProjectiveResolution` — `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`
- [x] Projective resolution — §2.2, “Projective Resolutions,” p. 33
  - `CategoryTheory.ProjectiveResolution` — `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`
- [x] Right resolution — §2.3, “Injective Resolutions,” p. 38; Definition 2.3.5
  - `CategoryTheory.InjectiveResolution` — `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`
- [x] Injective resolution — §2.3, “Injective Resolutions,” p. 38
  - `CategoryTheory.InjectiveResolution` — `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`
- [x] Adjoint functors — §2.3, “Injective Resolutions,” p. 38; Definition 2.3.9
  - `CategoryTheory.Adjunction` — `Mathlib/CategoryTheory/Adjunction/Basic.lean`
- [x] Left derived functor — §2.4, “Left Derived Functors,” p. 43
  - `CategoryTheory.Functor.leftDerived` — `Mathlib/CategoryTheory/Abelian/LeftDerived.lean`
- [x] Right derived functor — §2.5, “Right Derived Functors,” p. 49
  - `CategoryTheory.Functor.rightDerived` — `Mathlib/CategoryTheory/Abelian/RightDerived.lean`
- [x] Ext groups — §2.5, “Right Derived Functors,” p. 49; Definition 2.5.2
  - `CategoryTheory.Ext` — `Mathlib/CategoryTheory/Abelian/Ext.lean`
- [x] Tor groups — §2.6, “Adjoint Functors and Left/Right Exactness,” p. 51; Definition 2.6.4
  - `CategoryTheory.Tor` — `Mathlib/CategoryTheory/Monoidal/Tor.lean`
- [x] Filtered category — §2.6, “Adjoint Functors and Left/Right Exactness,” p. 51; Definition 2.6.13
  - `CategoryTheory.IsFiltered` — `Mathlib/CategoryTheory/Filtered/Basic.lean`
- [x] Balanced functor — §2.7, “Balancing Tor and Ext,” p. 58; Definition 2.7.7
  - `CategoryTheory.Functor.ReflectsIsomorphisms` — `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean:38`

## Chapter 3. Tor and Ext

- [x] Flat module — §3.2, “Tor and Flatness,” p. 68; Definition 3.2.1
  - `Module.Flat` — `Mathlib/RingTheory/Flat/Basic.lean`
- [x] Pontryagin dual of a module — §3.2, “Tor and Flatness,” p. 68; Definition 3.2.3
  - `PontryaginDual` — `Mathlib/Topology/Algebra/PontryaginDual.lean`
- [x] Noetherian ring — §3.3, “Ext for Nice Rings,” p. 73; Definition 3.3.9
  - `IsNoetherianRing` — `Mathlib/RingTheory/Noetherian/Defs.lean`
- [x] Extension of modules — §3.4, “Ext and Extensions,” p. 76
  - `LeanCategories.Homological.Extension` — `LeanCategories/Homological/Extensions.lean`
- [ ] Baer sum — §3.4, “Ext and Extensions,” p. 76; Definition 3.4.4
- [x] Inverse limit of a tower — §3.5, “Derived Functors of the Inverse Limit,” p. 80; Definition 3.5.1
  - `CategoryTheory.Limits.limit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Mittag-Leffler condition — §3.5, “Derived Functors of the Inverse Limit,” p. 80; Definition 3.5.6
  - `Functor.IsMittagLeffler` — `Mathlib/CategoryTheory/CofilteredSystem.lean`

## Chapter 4. Homological Dimension

- [x] Projective dimension — §4.1, “Dimensions,” p. 91
  - `CategoryTheory.projectiveDimension` — `Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean`
- [x] Injective dimension — §4.1, “Dimensions,” p. 91
  - `CategoryTheory.injectiveDimension` — `Mathlib/CategoryTheory/Abelian/Injective/Dimension.lean`
- [x] Global dimension — §4.1, “Dimensions,” p. 91; Definition 4.1.1
  - LeanCategories: `LeanCategories.Homological.GlobalDimension` — `LeanCategories/Homological/GlobalDimension.lean`
  - Also defines `injectiveGlobalDimension` (Thm. 4.1.2) and proves `of_divisionRing` (Example 4.1.4)
- [ ] Weak dimension — §4.1, “Dimensions,” p. 91
- [x] Semisimple ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.1
  - `IsSemisimpleRing` — `Mathlib/RingTheory/SimpleModule/Basic.lean`
- [x] Quasi-Frobenius ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.3
  - LeanCategories: `LeanCategories.Homological.IsQuasiFrobenius` — `LeanCategories/Homological/IsQuasiFrobenius.lean`
- [x] Frobenius algebra — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.5
  - monlib4: `FrobeniusAlgebra` — `Monlib/LinearAlgebra/Coalgebra/Lemmas.lean`
- [x] Hereditary ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.10
  - LeanCategories: `LeanCategories.Homological.IsRightHereditary` — `LeanCategories/Homological/IsHereditary.lean`
- [x] Koszul complex — §4.5, “Koszul Complexes,” p. 111
  - `KoszulComplex` — `facebookresearch/atlas-lean/Atlas/LieGroups/code/SyzygiesKoszul.lean`
- [x] Local cohomology — §4.6, “Local Cohomology,” p. 115; Definitions 4.6.1 and 4.6.5
  - `localCohomology` — `Mathlib/Algebra/Homology/LocalCohomology.lean`

## Chapter 5. Spectral Sequences

- [x] Homology spectral sequence
  - `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean` — §5.2, “Terminology,” p. 122; Definition 5.2.1
- [x] Cohomology spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.3
  - `CategoryTheory.CohomologicalSpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Collapse of a spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.7
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Bounded-below spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.9
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Regular spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.10
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Serre fibration — §5.3, “The Leray-Serre Spectral Sequence,” p. 127; Definition 5.3.1
- [ ] Bounded filtration of a chain complex — §5.4, “Spectral Sequence of a Filtration,” p. 131; Definition 5.4.2
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Hausdorff filtration — §5.4, “Spectral Sequence of a Filtration,” p. 131; Definition 5.4.4
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Column filtration of a double complex — §5.6, “Spectral Sequences of a Double Complex,” p. 141; Definition 5.6.1
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Row filtration of a double complex — §5.6, “Spectral Sequences of a Double Complex,” p. 141; Definition 5.6.2
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`
- [ ] Cartan-Eilenberg resolution — §5.7, “Hyperhomology,” p. 145; Definition 5.7.1
- [ ] Chain homotopy of double-complex maps — §5.7, “Hyperhomology,” p. 145; Definition 5.7.3
- [ ] Hyperderived functor — §5.7, “Hyperhomology,” p. 145; Definition 5.7.4
  - Partial reference: `Hypercohomology.hypercohomologyFunctor` — `facebookresearch/atlas-lean/Atlas/AlgebraicGeometryI/code/HypercohomologyDef.lean`
- [x] Acyclic object for a functor — §5.8, “Grothendieck Spectral Sequences,” p. 150; Definition 5.8.2
  - `LeanCategories.Homological.IsAcyclicFor` — `LeanCategories/Homological/DerivedDimension.lean`
- [ ] Derived exact couple — §5.9, “Exact Couples,” p. 153; Definition 5.9.1
  - Partial reference: `CategoryTheory.SpectralSequence` — `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`

## Chapter 6. Group Homology and Cohomology

- [x] Group homology with coefficients — §6.1, “Definitions and First Properties,” p. 160; Definition 6.1.2
  - `Rep.groupHomology.groupHomology` — `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`
- [x] Group cohomology with coefficients — §6.1, “Definitions and First Properties,” p. 160
  - `groupCohomology.groupCohomology` — `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`
- [x] Augmentation ideal — §6.1, “Definitions and First Properties,” p. 160; Definition 6.1.5
  - `Ideal.IsAugmentation` — `Mathlib/RingTheory/Ideal/IsAugmentation.lean`
- [x] Tate cohomology
  - `TateCohomology.tateCohomologyFunctor` — `Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean` — §6.2, “Cyclic and Free Groups,” p. 167; Definition 6.2.4
- [x] Induced module
  - `Rep.ind` — `Mathlib/RepresentationTheory/Induced.lean` — §6.3, “Shapiro's Lemma,” p. 171; Definition 6.3.1
- [x] Coinduced module
  - `Rep.coind` — `Mathlib/RepresentationTheory/Coinduced.lean` — §6.3, “Shapiro's Lemma,” p. 171; Definition 6.3.1
- [x] Derivation of a group in a module
  - `groupCohomology.IsCocycle₁` — `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` — §6.4, “Crossed Homomorphisms and H¹,” p. 174; Definition 6.4.1
- [x] Crossed homomorphism
  - `groupCohomology.IsCocycle₁` — `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` — §6.4, “Crossed Homomorphisms and H¹,” p. 174; Definition 6.4.1
- [x] Bar resolution
  - `Rep.barResolution` — `Mathlib/RepresentationTheory/Homological/Resolution.lean` — §6.5, “The Bar Resolution,” p. 177; Definition 6.5.1
- [x] Group extension
  - `GroupExtension` — `Mathlib/GroupTheory/GroupExtension/Defs.lean` — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.1
- [x] Factor set
  - `groupCohomology.IsCocycle₂` — `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.4
- [x] Relative Brauer group — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.11
- `RelativeBrGroup` — `reservoir-sources/Whysoserioushah__BrauerGroup/BrauerGroup/RelativeBrauer.lean`
- [ ] Restriction, corestriction, inflation, and transfer — §6.7, “Restriction, Corestriction, Inflation, and Transfer,” p. 189; Definition 6.7.1
- [x] Bialgebra — §6.7.1, “Cup Product,” p. 189; Definition 6.7.15
  - `Bialgebra` — `Mathlib/RingTheory/Bialgebra/Basic.lean`
- [x] Hopf algebra — §6.7.1, “Cup Product,” p. 189; Definition 6.7.15
  - `HopfAlgebra` — `Mathlib/RingTheory/HopfAlgebra/Basic.lean`
- [ ] Steinberg group — §6.9, “Universal Central Extensions,” p. 198; Definition 6.9.13
- [ ] Classifying space BG — §6.10, “Covering Spaces in Topology,” p. 203; Definition 6.10.4
  - Partial reference: `classifyingSpaceUniversalCover` — `Mathlib/RepresentationTheory/Homological/Resolution.lean`
- [x] Profinite group — §6.11, “Galois Cohomology and Profinite Groups,” p. 206; Definition 6.11.5
  - `ProfiniteGrp` — `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean`
- [ ] Discrete module over a profinite group — §6.11, “Galois Cohomology and Profinite Groups,” p. 206; Definition 6.11.8

## Chapter 7. Lie Algebra Homology and Cohomology

- [x] Lie algebra — §7.1, “Lie Algebras,” p. 216
  - `LieAlgebra` — `Mathlib/Algebra/Lie/Basic.lean`
- [x] Module over a Lie algebra — §7.2, “g-Modules,” p. 219
  - `LieModule` — `Mathlib/Algebra/Lie/Basic.lean`
- [ ] Lie algebra homology — §7.2, “g-Modules,” p. 219; Definition 7.2.2
- [x] Lie algebra cohomology — §7.2, “g-Modules,” p. 219; Definition 7.2.2
  - `LieModule.Cohomology.oneCochain` — `Mathlib/Algebra/Lie/Cochain.lean`
- [x] Tensor algebra — §7.3, “Universal Enveloping Algebras,” p. 223; Definition 7.3.1
  - `TensorAlgebra` — `Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`
- [x] Universal enveloping algebra — §7.3, “Universal Enveloping Algebras,” p. 223; Definition 7.3.2
  - `UniversalEnvelopingAlgebra` — `Mathlib/Algebra/Lie/UniversalEnveloping.lean`
- [x] Derivation from a Lie algebra into a module — §7.4, “H¹ and H₁,” p. 228; Definition 7.4.3
  - Mathlib: `LieDerivation` — `Mathlib/Algebra/Lie/Derivation/Basic.lean`
- [x] Extension of Lie algebras — §7.6, “H² and Extensions,” p. 234; Definition 7.6.1
  - `LieAlgebra.Extension` — `Mathlib/Algebra/Lie/Extension.lean`
- [ ] Chevalley-Eilenberg complex — §7.7, “The Chevalley-Eilenberg Complex,” p. 238; Definition 7.7.1
- [x] Killing form — §7.8, “Semisimple Lie Algebras,” p. 242; Definition 7.8.3
  - `killingForm` — `Mathlib/Algebra/Lie/TraceForm.lean`

## Chapter 8. Simplicial Methods in Homological Algebra

- [x] Simplicial object — §8.1, “Simplicial Objects,” p. 254
  - `CategoryTheory.SimplicialObject` — `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`
- [x] Semisimplicial object — §8.1, “Simplicial Objects,” p. 254; Definition 8.1.9
  - Mathlib: `SemiSimplexCategoryᵒᵖ ⥤ C` — `Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean`
- [x] Associated unnormalized chain complex — §8.2, “Operations on Simplicial Objects,” p. 259; Definition 8.2.1
  - `AlgebraicTopology.alternatingFaceMapComplex` — `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`
- [ ] Simplicial homotopy group — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.1
- [ ] Eilenberg-Mac Lane space — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.4
  - Partial reference: `GroundZero.Algebra.K` — `rzrn/ground_zero/GroundZero/Algebra/EilenbergMacLane.lean`
- [x] Moore normalized chain complex — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.6
  - `AlgebraicTopology.normalizedMooreComplex` — `Mathlib/AlgebraicTopology/MooreComplex.lean`
- [x] Triple — §8.6, “Canonical Resolutions,” p. 278; Definition 8.6.1
  - `CategoryTheory.Monad` — `Mathlib/CategoryTheory/Monad/Basic.lean`
- [ ] Cotriple-projective object — §8.6, “Canonical Resolutions,” p. 278; Definition 8.6.5
- [ ] Cotriple homology — §8.7, “Cotriple Homology,” p. 286; Definition 8.7.1
- [ ] Relative derived functor — §8.7, “Cotriple Homology,” p. 286; Definition 8.7.3
- [ ] k-split chain complex — §8.7.1, “Relative Tor and Ext,” p. 286; Definition 8.7.7
- [ ] André-Quillen homology — §8.8, “André-Quillen Homology and Cohomology,” p. 294
- [ ] André-Quillen cohomology — §8.8, “André-Quillen Homology and Cohomology,” p. 294

## Chapter 9. Hochschild and Cyclic Homology

- [ ] Hochschild homology — §9.1, “Hochschild Homology and Cohomology of Algebras,” p. 300
- [ ] Hochschild cohomology — §9.1, “Hochschild Homology and Cohomology of Algebras,” p. 300
- [x] Derivation of an algebra — §9.2, “Derivations, Differentials, and Separable Algebras,” p. 306
  - Mathlib: `Derivation` — `Mathlib/RingTheory/Derivation/Basic.lean`
- [x] Kähler differentials
  - `KaehlerDifferential` — `Mathlib/RingTheory/Kaehler/Basic.lean` — §9.2, “Derivations, Differentials, and Separable Algebras,” p. 306
- [x] Separable algebra — §9.2, “Derivations, Differentials, and Separable Algebras,” p. 306
  - Mathlib: `Algebra.IsSeparable` — `Mathlib/FieldTheory/Separable.lean`
- [x] Smooth algebra
  - `Algebra.Smooth` — `Mathlib/RingTheory/Smooth/Basic.lean` — §9.3.1, “Smooth Algebras,” p. 311
- [x] Essentially finite-type algebra — §9.4.2, “The Exterior Algebra Ω*R/k,” p. 319; Definition 9.4.5
  - Mathlib: `Algebra.EssFiniteType` — `Mathlib/RingTheory/EssentialFiniteness.lean`
- [ ] Hodge decomposition of Hochschild homology — §9.4.3, “Hodge Decomposition,” p. 319; Definition 9.4.15
- [x] Morita equivalence
  - `MoritaEquivalence` — `Mathlib/RingTheory/Morita/Basic.lean` — §9.5, “Morita Invariance,” p. 326; Definition 9.5.1
- [x] Trace on matrix algebras and bimodules — §9.5, “Morita Invariance,” p. 326; Definition 9.5.7
- `Matrix.trace` — `Mathlib/LinearAlgebra/Matrix/Trace.lean`
- [ ] Cyclic object — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.1
- [ ] Cyclic category — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.3
- [ ] Tsygan double complex — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.6
- [ ] Cyclic homology — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.7
- [ ] Mixed complex — §9.8, “Mixed Complexes,” p. 344; Definition 9.8.1
- [ ] Connes double complex — §9.8, “Mixed Complexes,” p. 344; Definition 9.8.2
- [ ] Hodge decomposition of cyclic homology — §9.8.2, “Hodge Decomposition,” p. 344; Definition 9.8.14
- [x] Graded algebra — §9.9, “Graded Algebras,” p. 354
  - `GradedAlgebra` — `Mathlib/RingTheory/GradedAlgebra/Basic.lean`
- [ ] Differential graded algebra — §9.9.1, “Homology of DG-Algebras,” p. 354

## Chapter 10. The Derived Category

- [x] Triangle in K(A) — §10.1, “The Category K(A),” p. 369; Definition 10.1.3
  - Mathlib: `Triangle (HomotopyCategory C (ComplexShape.up ℤ))` — `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`
- [x] Triangulated category — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.1
  - `CategoryTheory.IsTriangulated` — `Mathlib/CategoryTheory/Triangulated/Triangulated.lean`
- [x] Morphism of triangulated categories — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.6
  - Mathlib: `Functor.IsTriangulated` — `Mathlib/CategoryTheory/Triangulated/Functor.lean`
- [x] Triangulated subcategory — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.6
  - Mathlib: `ObjectProperty.IsTriangulated` — `Mathlib/CategoryTheory/Triangulated/Subcategory.lean`
- [x] Cohomological functor on a triangulated category — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.7
  - Mathlib: `Functor.IsHomological` — `Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean`
- [x] Localization of a category — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.1
  - `CategoryTheory.MorphismProperty.Localization` — `Mathlib/CategoryTheory/Localization/Construction.lean`
- [x] Multiplicative system — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.4
  - Mathlib: `MorphismProperty` — `Mathlib/CategoryTheory/MorphismProperty/Basic.lean`
- [ ] Localizing subcategory — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.12
- [x] Derived category — §10.4, “The Derived Category,” p. 385
  - `DerivedCategory` — `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`
- [x] Total right derived functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.1
  - `CategoryTheory.Functor.totalRightDerived` — `Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean`
- [x] Acyclic complex for a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.4
  - Mathlib: `HomologicalComplex.Acyclic` — `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`
- [x] Cohomological dimension of a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.10
  - `LeanCategories.Homological.cohomologicalDimension` — `LeanCategories/Homological/DerivedDimension.lean`
- [x] Homological dimension of a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.10
  - `LeanCategories.Homological.homologicalDimension` — `LeanCategories/Homological/DerivedDimension.lean`
- [x] Total tensor product — §10.6, “The Total Tensor Product,” p. 394; Definition 10.6.1
  - Mathlib: `HomologicalComplex.tensorObj` — `Mathlib/Algebra/Homology/Monoidal.lean`
- [ ] Hyperext — §10.7, “Ext and RHom,” p. 398; Definition 10.7.1
- [ ] Derived Hom object RHom — §10.7, “Ext and RHom,” p. 398; Definition 10.7.2
- [ ] Spectrum — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.1
- [ ] Stable category — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.4
- [ ] Prespectrum — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.5
- [ ] Homotopy category of spectra — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.10

## Appendix A. Category Theory Language

- [x] Category — §A.1, “Categories,” p. 417; Definition A.1.1
  - `CategoryTheory.Category` — `Mathlib/CategoryTheory/Category/Basic.lean`
- [x] Functor — §A.2, “Functors,” p. 421
  - `CategoryTheory.Functor` — `Mathlib/CategoryTheory/Functor/Basic.lean`
- [x] Natural transformation — §A.3, “Natural Transformations,” p. 423
  - `CategoryTheory.NatTrans` — `Mathlib/CategoryTheory/NatTrans.lean`
- [x] Abelian category — §A.4, “Abelian Categories,” p. 424; Definition A.4.2
  - `CategoryTheory.Abelian` — `Mathlib/CategoryTheory/Abelian/Basic.lean`
- [x] Limit — §A.5, “Limits and Colimits,” p. 427
  - `CategoryTheory.Limits.limit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Colimit — §A.5, “Limits and Colimits,” p. 427
  - `CategoryTheory.Limits.colimit` — `Mathlib/CategoryTheory/Limits/HasLimits.lean`
- [x] Adjoint functors — §A.6, “Adjoint Functors,” p. 429
  - `CategoryTheory.Adjunction` — `Mathlib/CategoryTheory/Adjunction/Basic.lean`
