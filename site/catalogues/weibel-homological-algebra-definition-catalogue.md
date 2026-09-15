---
title: "Weibel homological algebra definition catalogue"
---

- Author — Charles A. Weibel
- Zotero key — `8XN9IJSP`
- Citekey — `Wei94`
- Source attachment — ``Weibel - 1994 - An Introduction to Homological Algebra.md``

## Chapter 1. Chain Complexes

- [x] Chain complex — §1.1, “Complexes of R-Modules,” p. 1; Definition 1.1.1
  - `ChainComplex` — [`Mathlib/Algebra/Homology/HomologicalComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomologicalComplex.html)
- [x] Quasi-isomorphism — §1.1, “Complexes of R-Modules,” p. 1; Definition 1.1.2
  - `QuasiIso` — [`Mathlib/Algebra/Homology/QuasiIso.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/QuasiIso.html)
- [x] Kernel — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.1
  - [`CategoryTheory.Limits.kernel`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.kernel#doc) — [`Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Kernels.html)
- [x] Cokernel — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.1
  - [`CategoryTheory.Limits.cokernel`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.cokernel#doc) — [`Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Kernels.html)
- [x] Abelian category — §1.2, “Operations on Chain Complexes,” p. 5; Definition 1.2.2
  - [`CategoryTheory.Abelian`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Abelian#doc) — [`Mathlib/CategoryTheory/Abelian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Basic.html)
- [x] Split complex — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.1
  - `Homotopy (1_C) 0` via [`HomologicalComplex.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.Homotopy#doc) — [`Mathlib/Algebra/Homology/Homotopy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Homotopy.html)
- [x] Split exact complex — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.1
  - `Homotopy (1_C) 0` implies acyclicity (homotopic identity → zero on homology) — [`Mathlib/Algebra/Homology/Homotopy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Homotopy.html)
- [x] Null-homotopic chain map — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.3
  - [`HomologicalComplex.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.Homotopy#doc) — [`Mathlib/Algebra/Homology/Homotopy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Homotopy.html)
- [x] Chain homotopy — §1.4, “Chain Homotopies,” p. 15; Definition 1.4.4
  - [`HomologicalComplex.Homotopy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.Homotopy#doc) — [`Mathlib/Algebra/Homology/Homotopy.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Homotopy.html)
- [x] Mapping cone — §1.5, “Mapping Cones and Cylinders,” p. 18
  - [`HomologicalComplex.mappingCone`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.mappingCone#doc) — [`Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.html)
- [x] Mapping cylinder
  - [`HomologicalComplex.cylinder`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.cylinder#doc) — [`Mathlib/Algebra/Homology/HomotopyCofiber.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomotopyCofiber.html) — §1.5, “Mapping Cones and Cylinders,” p. 18
- [x] Sheaf — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.5
  - [`TopCat.Sheaf`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.Sheaf#doc) — [`Mathlib/Topology/Sheaves/Sheaf.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Sheaf.html)
- [x] Left exact functor — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.6
  - [`CategoryTheory.LeftExactFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.LeftExactFunctor#doc) — [`Mathlib/CategoryTheory/Limits/ExactFunctor.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/ExactFunctor.html)
- [x] Right exact functor — §1.6, “More on Abelian Categories,” p. 25; Definition 1.6.6
  - [`CategoryTheory.RightExactFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.RightExactFunctor#doc) — [`Mathlib/CategoryTheory/Limits/ExactFunctor.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/ExactFunctor.html)

## Chapter 2. Derived Functors

- [x] Homological δ-functor — §2.1, “δ-Functors,” p. 30; Definition 2.1.1
  - [`category_theory.delta_functor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=category_theory.delta_functor#doc) — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Cohomological δ-functor — §2.1, “δ-Functors,” p. 30; Definition 2.1.1
  - [`category_theory.delta_functor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=category_theory.delta_functor#doc) — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Morphism of δ-functors — §2.1, “δ-Functors,” p. 30; Definition 2.1.4
  - [`category_theory.delta_functor.hom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=category_theory.delta_functor.hom#doc) — `lean-liquid/src/for_mathlib/universal_delta_functor/basic.lean`
- [x] Left resolution — §2.2, “Projective Resolutions,” p. 33; Definition 2.2.4
  - [`CategoryTheory.ProjectiveResolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.ProjectiveResolution#doc) — [`Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Projective/Resolution.html)
- [x] Projective resolution — §2.2, “Projective Resolutions,” p. 33
  - [`CategoryTheory.ProjectiveResolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.ProjectiveResolution#doc) — [`Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Projective/Resolution.html)
- [x] Right resolution — §2.3, “Injective Resolutions,” p. 38; Definition 2.3.5
  - [`CategoryTheory.InjectiveResolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.InjectiveResolution#doc) — [`Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Injective/Resolution.html)
- [x] Injective resolution — §2.3, “Injective Resolutions,” p. 38
  - [`CategoryTheory.InjectiveResolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.InjectiveResolution#doc) — [`Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Injective/Resolution.html)
- [x] Adjoint functors — §2.3, “Injective Resolutions,” p. 38; Definition 2.3.9
  - [`CategoryTheory.Adjunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Adjunction#doc) — [`Mathlib/CategoryTheory/Adjunction/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Basic.html)
- [x] Left derived functor — §2.4, “Left Derived Functors,” p. 43
  - [`CategoryTheory.Functor.leftDerived`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor.leftDerived#doc) — [`Mathlib/CategoryTheory/Abelian/LeftDerived.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/LeftDerived.html)
- [x] Right derived functor — §2.5, “Right Derived Functors,” p. 49
  - [`CategoryTheory.Functor.rightDerived`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor.rightDerived#doc) — [`Mathlib/CategoryTheory/Abelian/RightDerived.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/RightDerived.html)
- [x] Ext groups — §2.5, “Right Derived Functors,” p. 49; Definition 2.5.2
  - [`CategoryTheory.Ext`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Ext#doc) — [`Mathlib/CategoryTheory/Abelian/Ext.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Ext.html)
- [x] Tor groups — §2.6, “Adjoint Functors and Left/Right Exactness,” p. 51; Definition 2.6.4
  - [`CategoryTheory.Tor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Tor#doc) — [`Mathlib/CategoryTheory/Monoidal/Tor.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monoidal/Tor.html)
- [x] Filtered category — §2.6, “Adjoint Functors and Left/Right Exactness,” p. 51; Definition 2.6.13
  - [`CategoryTheory.IsFiltered`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.IsFiltered#doc) — [`Mathlib/CategoryTheory/Filtered/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Filtered/Basic.html)
- [x] Balanced functor — §2.7, “Balancing Tor and Ext,” p. 58; Definition 2.7.7
  - [`CategoryTheory.Functor.ReflectsIsomorphisms`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor.ReflectsIsomorphisms#doc) — `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean:38`

## Chapter 3. Tor and Ext

- [x] Flat module — §3.2, “Tor and Flatness,” p. 68; Definition 3.2.1
  - [`Module.Flat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Flat#doc) — [`Mathlib/RingTheory/Flat/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Flat/Basic.html)
- [x] Pontryagin dual of a module — §3.2, “Tor and Flatness,” p. 68; Definition 3.2.3
  - `PontryaginDual` — [`Mathlib/Topology/Algebra/PontryaginDual.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/PontryaginDual.html)
- [x] Noetherian ring — §3.3, “Ext for Nice Rings,” p. 73; Definition 3.3.9
  - `IsNoetherianRing` — [`Mathlib/RingTheory/Noetherian/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Defs.html)
- [x] Extension of modules — §3.4, “Ext and Extensions,” p. 76
  - [`LeanCategories.Homological.Extension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.Extension#doc) — [`LeanCategories/Homological/Extensions.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/Extensions.lean)
- [ ] Baer sum — §3.4, “Ext and Extensions,” p. 76; Definition 3.4.4
- [x] Inverse limit of a tower — §3.5, “Derived Functors of the Inverse Limit,” p. 80; Definition 3.5.1
  - [`CategoryTheory.Limits.limit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.limit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Mittag-Leffler condition — §3.5, “Derived Functors of the Inverse Limit,” p. 80; Definition 3.5.6
  - [`Functor.IsMittagLeffler`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.IsMittagLeffler#doc) — [`Mathlib/CategoryTheory/CofilteredSystem.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/CofilteredSystem.html)

## Chapter 4. Homological Dimension

- [x] Projective dimension — §4.1, “Dimensions,” p. 91
  - [`CategoryTheory.projectiveDimension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.projectiveDimension#doc) — [`Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Projective/Dimension.html)
- [x] Injective dimension — §4.1, “Dimensions,” p. 91
  - [`CategoryTheory.injectiveDimension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.injectiveDimension#doc) — [`Mathlib/CategoryTheory/Abelian/Injective/Dimension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Injective/Dimension.html)
- [x] Global dimension — §4.1, “Dimensions,” p. 91; Definition 4.1.1
  - LeanCategories: [`LeanCategories.Homological.GlobalDimension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.GlobalDimension#doc) — [`LeanCategories/Homological/GlobalDimension.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/GlobalDimension.lean)
  - Also defines `injectiveGlobalDimension` (Thm. 4.1.2) and proves `of_divisionRing` (Example 4.1.4)
- [ ] Weak dimension — §4.1, “Dimensions,” p. 91
- [x] Semisimple ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.1
  - `IsSemisimpleRing` — [`Mathlib/RingTheory/SimpleModule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/SimpleModule/Basic.html)
- [x] Quasi-Frobenius ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.3
  - LeanCategories: [`LeanCategories.Homological.IsQuasiFrobenius`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.IsQuasiFrobenius#doc) — [`LeanCategories/Homological/IsQuasiFrobenius.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/IsQuasiFrobenius.lean)
- [x] Frobenius algebra — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.5
  - monlib4: `FrobeniusAlgebra` — `Monlib/LinearAlgebra/Coalgebra/Lemmas.lean`
- [x] Hereditary ring — §4.2, “Rings of Small Dimension,” p. 95; Definition 4.2.10
  - LeanCategories: [`LeanCategories.Homological.IsRightHereditary`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.IsRightHereditary#doc) — [`LeanCategories/Homological/IsHereditary.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/IsHereditary.lean)
- [x] Koszul complex — §4.5, “Koszul Complexes,” p. 111
  - `KoszulComplex` — `facebookresearch/atlas-lean/Atlas/LieGroups/code/SyzygiesKoszul.lean`
- [x] Local cohomology — §4.6, “Local Cohomology,” p. 115; Definitions 4.6.1 and 4.6.5
  - `localCohomology` — [`Mathlib/Algebra/Homology/LocalCohomology.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/LocalCohomology.html)

## Chapter 5. Spectral Sequences

- [x] Homology spectral sequence
  - [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html) — §5.2, “Terminology,” p. 122; Definition 5.2.1
- [x] Cohomology spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.3
  - [`CategoryTheory.CohomologicalSpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.CohomologicalSpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Collapse of a spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.7
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Bounded-below spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.9
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Regular spectral sequence — §5.2, “Terminology,” p. 122; Definition 5.2.10
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Serre fibration — §5.3, “The Leray-Serre Spectral Sequence,” p. 127; Definition 5.3.1
- [ ] Bounded filtration of a chain complex — §5.4, “Spectral Sequence of a Filtration,” p. 131; Definition 5.4.2
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Hausdorff filtration — §5.4, “Spectral Sequence of a Filtration,” p. 131; Definition 5.4.4
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Column filtration of a double complex — §5.6, “Spectral Sequences of a Double Complex,” p. 141; Definition 5.6.1
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Row filtration of a double complex — §5.6, “Spectral Sequences of a Double Complex,” p. 141; Definition 5.6.2
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)
- [ ] Cartan-Eilenberg resolution — §5.7, “Hyperhomology,” p. 145; Definition 5.7.1
- [ ] Chain homotopy of double-complex maps — §5.7, “Hyperhomology,” p. 145; Definition 5.7.3
- [ ] Hyperderived functor — §5.7, “Hyperhomology,” p. 145; Definition 5.7.4
  - Partial reference: [`Hypercohomology.hypercohomologyFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Hypercohomology.hypercohomologyFunctor#doc) — `facebookresearch/atlas-lean/Atlas/AlgebraicGeometryI/code/HypercohomologyDef.lean`
- [x] Acyclic object for a functor — §5.8, “Grothendieck Spectral Sequences,” p. 150; Definition 5.8.2
  - [`LeanCategories.Homological.IsAcyclicFor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.IsAcyclicFor#doc) — [`LeanCategories/Homological/DerivedDimension.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/DerivedDimension.lean)
- [ ] Derived exact couple — §5.9, “Exact Couples,” p. 153; Definition 5.9.1
  - Partial reference: [`CategoryTheory.SpectralSequence`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SpectralSequence#doc) — [`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/SpectralSequence/Basic.html)

## Chapter 6. Group Homology and Cohomology

- [x] Group homology with coefficients — §6.1, “Definitions and First Properties,” p. 160; Definition 6.1.2
  - [`Rep.groupHomology.groupHomology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Rep.groupHomology.groupHomology#doc) — [`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.html)
- [x] Group cohomology with coefficients — §6.1, “Definitions and First Properties,” p. 160
  - [`groupCohomology.groupCohomology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=groupCohomology.groupCohomology#doc) — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.html)
- [x] Augmentation ideal — §6.1, “Definitions and First Properties,” p. 160; Definition 6.1.5
  - [`Ideal.IsAugmentation`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsAugmentation#doc) — [`Mathlib/RingTheory/Ideal/IsAugmentation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/IsAugmentation.html)
- [x] Tate cohomology
  - [`TateCohomology.tateCohomologyFunctor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TateCohomology.tateCohomologyFunctor#doc) — [`Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/TateCohomology/Basic.html) — §6.2, “Cyclic and Free Groups,” p. 167; Definition 6.2.4
- [x] Induced module
  - [`Rep.ind`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Rep.ind#doc) — [`Mathlib/RepresentationTheory/Induced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Induced.html) — §6.3, “Shapiro's Lemma,” p. 171; Definition 6.3.1
- [x] Coinduced module
  - [`Rep.coind`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Rep.coind#doc) — [`Mathlib/RepresentationTheory/Coinduced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Coinduced.html) — §6.3, “Shapiro's Lemma,” p. 171; Definition 6.3.1
- [x] Derivation of a group in a module
  - `groupCohomology.IsCocycle₁` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html) — §6.4, “Crossed Homomorphisms and H¹,” p. 174; Definition 6.4.1
- [x] Crossed homomorphism
  - `groupCohomology.IsCocycle₁` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html) — §6.4, “Crossed Homomorphisms and H¹,” p. 174; Definition 6.4.1
- [x] Bar resolution
  - [`Rep.barResolution`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Rep.barResolution#doc) — [`Mathlib/RepresentationTheory/Homological/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/Resolution.html) — §6.5, “The Bar Resolution,” p. 177; Definition 6.5.1
- [x] Group extension
  - `GroupExtension` — [`Mathlib/GroupTheory/GroupExtension/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupExtension/Defs.html) — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.1
- [x] Factor set
  - `groupCohomology.IsCocycle₂` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html) — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.4
- [x] Relative Brauer group — §6.6, “Factor Sets and H²,” p. 182; Definition 6.6.11
- `RelativeBrGroup` — `reservoir-sources/Whysoserioushah__BrauerGroup/BrauerGroup/RelativeBrauer.lean`
- [ ] Restriction, corestriction, inflation, and transfer — §6.7, “Restriction, Corestriction, Inflation, and Transfer,” p. 189; Definition 6.7.1
- [x] Bialgebra — §6.7.1, “Cup Product,” p. 189; Definition 6.7.15
  - `Bialgebra` — [`Mathlib/RingTheory/Bialgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Bialgebra/Basic.html)
- [x] Hopf algebra — §6.7.1, “Cup Product,” p. 189; Definition 6.7.15
  - `HopfAlgebra` — [`Mathlib/RingTheory/HopfAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/HopfAlgebra/Basic.html)
- [ ] Steinberg group — §6.9, “Universal Central Extensions,” p. 198; Definition 6.9.13
- [ ] Classifying space BG — §6.10, “Covering Spaces in Topology,” p. 203; Definition 6.10.4
  - Partial reference: `classifyingSpaceUniversalCover` — [`Mathlib/RepresentationTheory/Homological/Resolution.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/Resolution.html)
- [x] Profinite group — §6.11, “Galois Cohomology and Profinite Groups,” p. 206; Definition 6.11.5
  - `ProfiniteGrp` — [`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.html)
- [ ] Discrete module over a profinite group — §6.11, “Galois Cohomology and Profinite Groups,” p. 206; Definition 6.11.8

## Chapter 7. Lie Algebra Homology and Cohomology

- [x] Lie algebra — §7.1, “Lie Algebras,” p. 216
  - `LieAlgebra` — [`Mathlib/Algebra/Lie/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Basic.html)
- [x] Module over a Lie algebra — §7.2, “g-Modules,” p. 219
  - `LieModule` — [`Mathlib/Algebra/Lie/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Basic.html)
- [ ] Lie algebra homology — §7.2, “g-Modules,” p. 219; Definition 7.2.2
- [x] Lie algebra cohomology — §7.2, “g-Modules,” p. 219; Definition 7.2.2
  - [`LieModule.Cohomology.oneCochain`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LieModule.Cohomology.oneCochain#doc) — [`Mathlib/Algebra/Lie/Cochain.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Cochain.html)
- [x] Tensor algebra — §7.3, “Universal Enveloping Algebras,” p. 223; Definition 7.3.1
  - `TensorAlgebra` — [`Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorAlgebra/Basic.html)
- [x] Universal enveloping algebra — §7.3, “Universal Enveloping Algebras,” p. 223; Definition 7.3.2
  - `UniversalEnvelopingAlgebra` — [`Mathlib/Algebra/Lie/UniversalEnveloping.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/UniversalEnveloping.html)
- [x] Derivation from a Lie algebra into a module — §7.4, “H¹ and H₁,” p. 228; Definition 7.4.3
  - Mathlib: `LieDerivation` — [`Mathlib/Algebra/Lie/Derivation/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Derivation/Basic.html)
- [x] Extension of Lie algebras — §7.6, “H² and Extensions,” p. 234; Definition 7.6.1
  - [`LieAlgebra.Extension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LieAlgebra.Extension#doc) — [`Mathlib/Algebra/Lie/Extension.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/Extension.html)
- [ ] Chevalley-Eilenberg complex — §7.7, “The Chevalley-Eilenberg Complex,” p. 238; Definition 7.7.1
- [x] Killing form — §7.8, “Semisimple Lie Algebras,” p. 242; Definition 7.8.3
  - `killingForm` — [`Mathlib/Algebra/Lie/TraceForm.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/TraceForm.html)

## Chapter 8. Simplicial Methods in Homological Algebra

- [x] Simplicial object — §8.1, “Simplicial Objects,” p. 254
  - [`CategoryTheory.SimplicialObject`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.SimplicialObject#doc) — [`Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialObject/Basic.html)
- [x] Semisimplicial object — §8.1, “Simplicial Objects,” p. 254; Definition 8.1.9
  - Mathlib: `SemiSimplexCategoryᵒᵖ ⥤ C` — [`Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.html)
- [x] Associated unnormalized chain complex — §8.2, “Operations on Simplicial Objects,” p. 259; Definition 8.2.1
  - [`AlgebraicTopology.alternatingFaceMapComplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicTopology.alternatingFaceMapComplex#doc) — [`Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.html)
- [ ] Simplicial homotopy group — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.1
- [ ] Eilenberg-Mac Lane space — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.4
  - Partial reference: [`GroundZero.Algebra.K`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GroundZero.Algebra.K#doc) — `rzrn/ground_zero/GroundZero/Algebra/EilenbergMacLane.lean`
- [x] Moore normalized chain complex — §8.3, “Simplicial Homotopy Groups,” p. 263; Definition 8.3.6
  - [`AlgebraicTopology.normalizedMooreComplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicTopology.normalizedMooreComplex#doc) — [`Mathlib/AlgebraicTopology/MooreComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/MooreComplex.html)
- [x] Triple — §8.6, “Canonical Resolutions,” p. 278; Definition 8.6.1
  - [`CategoryTheory.Monad`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Monad#doc) — [`Mathlib/CategoryTheory/Monad/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Basic.html)
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
  - Mathlib: `Derivation` — [`Mathlib/RingTheory/Derivation/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Derivation/Basic.html)
- [x] Kähler differentials
  - `KaehlerDifferential` — [`Mathlib/RingTheory/Kaehler/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Kaehler/Basic.html) — §9.2, “Derivations, Differentials, and Separable Algebras,” p. 306
- [x] Separable algebra — §9.2, “Derivations, Differentials, and Separable Algebras,” p. 306
  - Mathlib: [`Algebra.IsSeparable`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.IsSeparable#doc) — [`Mathlib/FieldTheory/Separable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Separable.html)
- [x] Smooth algebra
  - [`Algebra.Smooth`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.Smooth#doc) — [`Mathlib/RingTheory/Smooth/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Smooth/Basic.html) — §9.3.1, “Smooth Algebras,” p. 311
- [x] Essentially finite-type algebra — §9.4.2, “The Exterior Algebra Ω*R/k,” p. 319; Definition 9.4.5
  - Mathlib: [`Algebra.EssFiniteType`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.EssFiniteType#doc) — [`Mathlib/RingTheory/EssentialFiniteness.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/EssentialFiniteness.html)
- [ ] Hodge decomposition of Hochschild homology — §9.4.3, “Hodge Decomposition,” p. 319; Definition 9.4.15
- [x] Morita equivalence
  - `MoritaEquivalence` — [`Mathlib/RingTheory/Morita/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Morita/Basic.html) — §9.5, “Morita Invariance,” p. 326; Definition 9.5.1
- [x] Trace on matrix algebras and bimodules — §9.5, “Morita Invariance,” p. 326; Definition 9.5.7
- [`Matrix.trace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.trace#doc) — [`Mathlib/LinearAlgebra/Matrix/Trace.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Trace.html)
- [ ] Cyclic object — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.1
- [ ] Cyclic category — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.3
- [ ] Tsygan double complex — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.6
- [ ] Cyclic homology — §9.6, “Cyclic Homology,” p. 330; Definition 9.6.7
- [ ] Mixed complex — §9.8, “Mixed Complexes,” p. 344; Definition 9.8.1
- [ ] Connes double complex — §9.8, “Mixed Complexes,” p. 344; Definition 9.8.2
- [ ] Hodge decomposition of cyclic homology — §9.8.2, “Hodge Decomposition,” p. 344; Definition 9.8.14
- [x] Graded algebra — §9.9, “Graded Algebras,” p. 354
  - `GradedAlgebra` — [`Mathlib/RingTheory/GradedAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/GradedAlgebra/Basic.html)
- [ ] Differential graded algebra — §9.9.1, “Homology of DG-Algebras,” p. 354

## Chapter 10. The Derived Category

- [x] Triangle in K(A) — §10.1, “The Category K(A),” p. 369; Definition 10.1.3
  - Mathlib: `Triangle (HomotopyCategory C (ComplexShape.up ℤ))` — [`Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.html)
- [x] Triangulated category — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.1
  - [`CategoryTheory.IsTriangulated`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.IsTriangulated#doc) — [`Mathlib/CategoryTheory/Triangulated/Triangulated.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Triangulated/Triangulated.html)
- [x] Morphism of triangulated categories — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.6
  - Mathlib: [`Functor.IsTriangulated`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.IsTriangulated#doc) — [`Mathlib/CategoryTheory/Triangulated/Functor.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Triangulated/Functor.html)
- [x] Triangulated subcategory — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.6
  - Mathlib: [`ObjectProperty.IsTriangulated`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ObjectProperty.IsTriangulated#doc) — [`Mathlib/CategoryTheory/Triangulated/Subcategory.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Triangulated/Subcategory.html)
- [x] Cohomological functor on a triangulated category — §10.2, “Triangulated Categories,” p. 373; Definition 10.2.7
  - Mathlib: [`Functor.IsHomological`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.IsHomological#doc) — [`Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Triangulated/HomologicalFunctor.html)
- [x] Localization of a category — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.1
  - [`CategoryTheory.MorphismProperty.Localization`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.MorphismProperty.Localization#doc) — [`Mathlib/CategoryTheory/Localization/Construction.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Localization/Construction.html)
- [x] Multiplicative system — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.4
  - Mathlib: `MorphismProperty` — [`Mathlib/CategoryTheory/MorphismProperty/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/MorphismProperty/Basic.html)
- [ ] Localizing subcategory — §10.3, “Localization and the Calculus of Fractions,” p. 379; Definition 10.3.12
- [x] Derived category — §10.4, “The Derived Category,” p. 385
  - `DerivedCategory` — [`Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/DerivedCategory/Basic.html)
- [x] Total right derived functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.1
  - [`CategoryTheory.Functor.totalRightDerived`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor.totalRightDerived#doc) — [`Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Derived/RightDerived.html)
- [x] Acyclic complex for a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.4
  - Mathlib: [`HomologicalComplex.Acyclic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.Acyclic#doc) — [`Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.html)
- [x] Cohomological dimension of a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.10
  - [`LeanCategories.Homological.cohomologicalDimension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.cohomologicalDimension#doc) — [`LeanCategories/Homological/DerivedDimension.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/DerivedDimension.lean)
- [x] Homological dimension of a functor — §10.5, “Derived Functors,” p. 390; Definition 10.5.10
  - [`LeanCategories.Homological.homologicalDimension`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Homological.homologicalDimension#doc) — [`LeanCategories/Homological/DerivedDimension.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Homological/DerivedDimension.lean)
- [x] Total tensor product — §10.6, “The Total Tensor Product,” p. 394; Definition 10.6.1
  - Mathlib: [`HomologicalComplex.tensorObj`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.tensorObj#doc) — [`Mathlib/Algebra/Homology/Monoidal.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Monoidal.html)
- [ ] Hyperext — §10.7, “Ext and RHom,” p. 398; Definition 10.7.1
- [ ] Derived Hom object RHom — §10.7, “Ext and RHom,” p. 398; Definition 10.7.2
- [ ] Spectrum — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.1
- [ ] Stable category — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.4
- [ ] Prespectrum — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.5
- [ ] Homotopy category of spectra — §10.9, “The Topological Derived Category,” p. 407; Definition 10.9.10

## Appendix A. Category Theory Language

- [x] Category — §A.1, “Categories,” p. 417; Definition A.1.1
  - [`CategoryTheory.Category`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Category#doc) — [`Mathlib/CategoryTheory/Category/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- [x] Functor — §A.2, “Functors,” p. 421
  - [`CategoryTheory.Functor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Functor#doc) — [`Mathlib/CategoryTheory/Functor/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Basic.html)
- [x] Natural transformation — §A.3, “Natural Transformations,” p. 423
  - [`CategoryTheory.NatTrans`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.NatTrans#doc) — [`Mathlib/CategoryTheory/NatTrans.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/NatTrans.html)
- [x] Abelian category — §A.4, “Abelian Categories,” p. 424; Definition A.4.2
  - [`CategoryTheory.Abelian`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Abelian#doc) — [`Mathlib/CategoryTheory/Abelian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Basic.html)
- [x] Limit — §A.5, “Limits and Colimits,” p. 427
  - [`CategoryTheory.Limits.limit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.limit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Colimit — §A.5, “Limits and Colimits,” p. 427
  - [`CategoryTheory.Limits.colimit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Limits.colimit#doc) — [`Mathlib/CategoryTheory/Limits/HasLimits.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html)
- [x] Adjoint functors — §A.6, “Adjoint Functors,” p. 429
  - [`CategoryTheory.Adjunction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Adjunction#doc) — [`Mathlib/CategoryTheory/Adjunction/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Basic.html)
