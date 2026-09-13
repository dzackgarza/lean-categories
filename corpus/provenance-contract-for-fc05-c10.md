---
type: reference
title: Provenance contract for FC05 C10
description: '# Provenance contract for FC05 C10'
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC05 C10

# Provenance contract for FC05 C10

## Provenance contract for FC05 C10

- Project-first search was performed at repository HEAD `f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`. No project declaration owns a complete C10 source row under strict bundle semantics.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. The checked P interfaces cover the homotopy-category quotient and homology descent, mapping-cone and Verdier triangulated structures, categorical localization and fraction calculus, K-injective/K-projective Hom comparison, short-exact-sequence triangles, additive functors on homotopy categories, and generic localized shifted Hom. Every P target promoted in the C10 table was inspected at this exact revision.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`, Apache-2.0, Lean 4.34.0-rc2. H adds `Mathlib/CategoryTheory/Functor/Derived/RightDerivedTriangulated.lean::Functor.isTriangulated_of_leftExtension` and its left-derived dual, but these are conditional generic criteria rather than an instantiation of Weibel's total derived-functor bundles U055/U057. H still has no completed derived tensor/RHom, Grothendieck spectral sequence, derived sheaf direct-image/Leray, or stable-homotopy-spectrum package realizing the missing C10 bundles.
- The bounded-derived support at P is asymmetric for the source's bundled statements: `HomotopyCategory.Plus` and `DerivedCategory.Plus` are developed explicitly, together with injective derivability and `rightDerivedFunctorPlus`, but the checked pin has no corresponding `HomotopyCategory.Minus`/`DerivedCategory.Minus` or `Bounded` chapter files. Therefore rows such as U004, U019, U040, U045, U050, and U062 that simultaneously assert the bounded, bounded-above, bounded-below, or both injective/projective halves are not partially credited.
- P's localization calculus has exact left/right fraction structures, equivalence relations, composition, map-equality criteria, and additive localization. However, U026 bundles the two-sided Ore and two-sided cancellation axioms as one multiplicative-system interface, while the checked API separates left and right calculus assumptions and does not package that whole source definition; U026 therefore remains unmatched. The local-smallness/filtered-colimit theorems U029–U032 likewise exceed the checked fraction infrastructure.
- P's derived category gives exact K-injective and K-projective Hom-comparison interfaces (`CochainComplex.IsKInjective.Qh_map_bijective` and the projective dual), so U049 is direct. `ShortComplex.ShortExact.triangleOfSES` with `triangleOfSES_distinguished` directly owns U051. By contrast, the stronger bundled equivalence/existence statements U048/U050 and the zero-map criterion U052 are not inferred from adjacent localization machinery without a checked declaration of the whole source row.
- `Mathlib/Algebra/Homology/Monoidal.lean` and `Mathlib/Algebra/Homology/BifunctorHomotopy.lean` provide the ordinary total tensor/bifunctor and homotopy infrastructure, and `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean` provides the total Hom complex. These are not promoted for U068–U099 when the source row additionally asserts total-derived tensor/RHom, hypertor/hyperext recovery, change of rings, projection formula, derived composition, or spectral-sequence conclusions that the checked P/H API does not instantiate.
- U079 is routed through `Mathlib/CategoryTheory/Localization/SmallShiftedHom.lean::Localization.SmallShiftedHom` and `SmallShiftedHom.equiv`: for arbitrary complexes this is exactly a small representative of the shifted Hom type in the localization, i.e. the source definition of hyperext. This is not conflated with the later object-level `CategoryTheory.Abelian.Ext` API.
- `LC=50500fadbbfa205092dd7fb07a59a05eea23ce66` is the audited 2026-09-06 HEAD of `dagurtomas/LeanCondensed`, Apache-2.0, Lean 4.32.0-rc1. Its `LeanCondensed/Mathlib/Algebra/Homology/DerivedCategory/TwoVariable.lean` contains substantial two-variable K-projective/K-injective/K-flat derived-functor work, but the audited file still has five `sorry` obligations, including a key enough-K-projectives equivalence. It is therefore incomplete reference evidence, not a route for the total-derived tensor/RHom rows.
- `SP=3b078f5f1de251637decf04bd3fc8aa01930a6b3` is the audited HEAD of the historical Apache-2.0 HLean repository `cmu-phil/Spectral`. It contains prespectrum/spectrum, stable homotopy-group, suspension, and spectrification constructions in `spectrum/basic.hlean` and `spectrum/spectrification.hlean`, but the development contains unfinished `sorry` proofs and does not supply the complete category/CW-localization/triangulation/HZ-module bundles U100–U121. No such row is upgraded from this partial historical development.
- Indexed GitHub code search and open Mathlib PR search on 2026-09-06 found no completed Lean implementation closing the total-derived tensor/RHom or stable-spectrum gaps. TauCeti at its refreshed C09 baseline `T=0857cbca8b6a91dd22680eba45ecc284c14d8325` likewise supplied no complete C10 row beyond the Mathlib interfaces already audited.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, TauCeti, LeanCondensed, the historical Spectral development, open Mathlib work, indexed GitHub search, and relevant external Lean repositories. A prerequisite, generic construction not instantiated to the source theorem, mathematically derivable consequence, incomplete development, differently scoped theorem, or proper subset of a bundled row is not credited as that row's route.
