---
type: reference
title: Foundational corpus mapping FC05 Weibel
description: '# Foundational corpus mapping FC05 Weibel'
tags:
- project
- reference
timestamp: '2026-09-11T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# Foundational corpus mapping FC05 Weibel

# FC05 — Weibel, *An Introduction to Homological Algebra* mapping

Status: **Sweep II complete.** C01–C10 and Appendix A are complete.

## Sweep III execution — FC05

Active source: FC05. Delivered Sweep III C01 owners include U027 (`8d9923d35465caa0c0b848d6daffc1df37db7326`, exact-sequence categories), U031 (`3a54724`, split/split-exact complexes), U043 (`88f8c7695cd68068b15add1e23c974fa904f06b2`, mapping cylinder), U046 (`e1a8d1079d908f80b77d42f265f4b8330d296e4f`, cylinder/cone comparison construction), U064 (`fef625b60b66a7af727251771d1b6035be748a30`, Yoneda defect and weak effaceability), U030 (`2dc447cb7d803555cbcec2a6bc2ac84062a197cb`, vector-space splitting and decomposition), and U057 (`105a2ea8eca5f75ba4f230286eb416fff82810d2`, sheaf-versus-presheaf exponential counterexample). Sweep III C02 owners include U001 (`887d412db1b999d3aade31af067c37027f8eb6d9`, homological/cohomological δ-functors), U006 (`f5249475bfb718a27deef032b467792703ebb265`, morphisms and universal δ-functors), U008 (`77cbedf932c2ff494f68fba80d8df70cad34c4ff`, left/right satellite terminology), U045 (`2cb95566c780301276a432387277e67f900cb021`, projective-resolution syzygy kernels), and U080 (`6275e09dd58df3f335c45442205790ddd4f5f1dc`, right-balanced multivariable functors); U030 is also closed directly by pinned Mathlib's generic right action. Sweep III C03 now includes U033 (`8ea3f3cdf2b1a6100cf6e12deecb1392d80f16d7`, right-Noetherian finite-presentation convention and noncanonical degreewise finite-rank free resolutions with exactness proved), U040 (`46fe0d30487afad2f793f1a139e6ae1627884a3b`, literal Baer sum via fibre product and skew-diagonal quotient), U045 (`1391d0a`, the AB4* convention with positive Ab/module/chain-complex examples and an explicit shrinking-fibre sheaf counterexample showing products of epis need not be epi), U046 (`502d89e`, the Eilenberg countable-tower difference-map model with coherent kernel, `lim¹` cokernel, and zero higher terms), and U052 (`b71d575`, Mathlib’s image-stabilization condition plus the project-owned trivial Mittag–Leffler condition and its implication to ordinary Mittag–Leffler). C01-U048, C02-U047, C02-U056, and C02-U081 remain dependency-blocked. The source-local `fc05-remap` gate was closed on 2026-09-14 under clause-wise semantics; the live generated frontier, not this handoff prose, selects the next definition. At closure the first ready row is C03-U031. The old untracked `LeanCategories/Homological/RoosComplex.lean` is pre-existing residue and is not an authoritative handoff or an active claim.

Sweep III C03-U031 is now realized by `LeanCategories/Homological/CentralHomLocalization.lean::centralOreSet`, `centralSubmonoid`, `localizedLinearMapFraction`, and `centralHomLocalizationComparison`, with `centralHomLocalizationComparison_fraction` proving Weibel's `(f/s)(a/t)=f(a)/(st)` formula at arbitrary-associative-ring generality. The implementation was checked by building its module and by temporary intended/separating probes (commutative submonoids are central; powers of an explicit noncentral `2×2` integer matrix are not). The regenerated frontier selects C04-U050 next. `RoosComplex.lean` remains preserved old residue, not the active frontier.

Sweep III C04-U050 is realized by the provenance-preserving port in `LeanCategories/ForMathlib/LocalGradeCohenMacaulay.lean`: `IsLocalRing.IsGradeSequence`, `IsLocalRing.grade`, and `IsCohenMacaulayLocalRing`. The 2026-09-14 source-convention audit repaired the class so Cohen–Macaulay local rings carry U047's Noetherian hypothesis explicitly; the existing `isGradeSequence_nil` and `not_isGradeSequence_one` checks witness the intended and excluded regular-sequence cases. The owner and its build target elaborate successfully. The regenerated frontier selects C04-U068 next.

Sweep III C04-U068 is now realized by `LeanCategories/Homological/KoszulComplex.lean::koszulComplex` and `canonicalKoszulComplexRealization`. The owner constructs the arbitrary-associative-ring Koszul complex for a finite central sequence, proves the alternating boundary squares to zero via the deletion-pair involution, and records the exact free-degree/basis differential formula. `lake build LeanCategories.Homological.KoszulComplex` succeeds; temporary probes accept arbitrary sequences over commutative rings and reject an explicit noncentral `2×2` integer-matrix singleton. The earlier exhaustive search evidence and commutative/field external implementations remain recorded as prior art rather than substituted for the source-general owner.

Sweep III C04-U069 now uses that canonical owner directly in `LeanCategories/Homological/KoszulHomology.lean`. `koszulHomology` and `koszulCohomology` take only the central sequence and coefficient module, exactly as Notation 4.5.1 does; the realization-parametrized `…Of` helpers are retained solely for comparison maps. Focused builds of `KoszulHomology` and the dependent `KoszulTransition` module both succeed.

Sweep III C04-U070 is realized by `LeanCategories/Homological/KoszulExteriorDescription.lean::canonicalKoszulExteriorDescription`: at arbitrary-ring generality it uses the source's free module on ordered wedge symbols and proves the U068 differential is contraction by the central sequence. In the commutative specialization, `koszulExteriorPowerEquiv` and `koszulExteriorPowerEquiv_wedgeSymbol` compare that model to Mathlib's actual exterior power and standard exterior basis. The focused module build succeeds; the earlier exhaustive external-search evidence remains provenance/prior art rather than a narrower substitute.

Sweep III C04-U080 is realized by `LeanCategories/Homological/KoszulTransition.lean::koszulPowerTransitionMap` and `canonicalKoszulPowerTransition`. A direct source recheck corrected the stale mapping description: Weibel's one-variable map is identity in degree zero and multiplication by `x` in degree one, so after tensoring the wedge `e_I` is multiplied by `∏_{j∈I} x_j`, not by the complementary product. The owner constructs that degreewise map, proves it commutes with the Koszul differential, and induces the homology/cohomology transitions. The focused module elaborates successfully; temporary `x=2` probes verify the degree-zero and degree-one coefficients and separate the former complementary-product misdescription.

Sweep III C05-U045 is realized by `LeanCategories/Homological/DoubleComplexFiltrations.lean::columnFiltration`. The owner first proves the direct-sum totalization exists for every first-quadrant double complex by finiteness of the fibers `i+j=n`, then realizes `F_p Tot` as the totalization of the horizontal stupid truncation to columns `i≤p`; the inclusion is proved degreewise split mono, so it defines an actual subcomplex of `Tot K`, and negative filtration degrees are `⊥`. The tracked module elaborates successfully. Temporary intended/separating probes verify that `p=0` retains column `0` by an isomorphism, kills column `1`, and that filtration degree `-1` is bottom. Page/associated-graded identifications and convergence remain theorem work.

Sweep III C05-U046 is realized in the same owner by `firstQuadrantTotalComplexShapeSymmetry` and `rowFiltration`. The standard sign `(-1)^(pq)` gives Mathlib’s total-complex flip isomorphism for first-quadrant chain bicomplexes; `rowFiltration` is the image of `columnFiltration (flip K)` under the induced order isomorphism on subobjects. Focused elaboration succeeds, and temporary probes verify the `p=0` row cutoff retains row `0`, kills row `1`, and has bottom in negative filtration degree.

Sweep III C06-U007 accepts the already-integrated TauCeti port in `LeanCategories/Algebra/MonoidAlgebra.lean`: `augmentation` is the coefficient-sum ring hom and `augmentationIdeal` its kernel, with `augmentationGenerators` recording the source elements `g-1`. The module builds successfully; temporary group-ring probes verify coefficient summation, `g-1 ∈ I`, and `1 ∉ I`. The TauCeti commit/license remain the implementation provenance, while the generator-spans-kernel statement stays in the theorem layer.

Canonical catalogue: [[foundational-corpus-units-fc05-weibel|FC05 — Weibel, An Introduction to Homological Algebra]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib was refreshed 2026-09-14 to `2ff8073df352b7cb74638403c464ed5cd3f97ce2`; declarations first appearing after the project pin are revision-specific reference-port routes unless an importable package route is independently justified.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, indexed search services, and relevant external Lean repositories. Route acceptance is clause-wise: checked owners are recorded for every supplied clause, and `unmatched` records only the residual mathematical statement after those owners are exhausted. The FC05 source-local exact-route gate was refreshed and closed on 2026-09-14; later-source remaps are independent prior work under the live DAG.

[Provenance contract for FC05 C01](provenance-contract-for-fc05-c01)

[Chapter 1. Chain Complexes FC05](chapter-1-chain-complexes-fc05)

[Provenance contract for FC05 C02](provenance-contract-for-fc05-c02)

[Chapter 2. Derived Functors FC05](chapter-2-derived-functors-fc05)

[Provenance contract for FC05 C03](provenance-contract-for-fc05-c03)

[Chapter 3. Tor and Ext FC05](chapter-3-tor-and-ext-fc05)

[Provenance contract for FC05 C04](provenance-contract-for-fc05-c04)

[Chapter 4. Homological Dimension FC05](chapter-4-homological-dimension-fc05)

[Provenance contract for FC05 C05](provenance-contract-for-fc05-c05)

[Chapter 5. Spectral Sequences FC05](chapter-5-spectral-sequences-fc05)

[Provenance contract for FC05 C06](provenance-contract-for-fc05-c06)

[Chapter 6. Group Homology and Cohomology FC05](chapter-6-group-homology-and-cohomology-fc05)

[Provenance contract for FC05 C07](provenance-contract-for-fc05-c07)

[Chapter 7. Lie Algebra Homology and Cohomology FC05](chapter-7-lie-algebra-homology-and-cohomology-fc05)

[Provenance contract for FC05 C08](provenance-contract-for-fc05-c08)

[Chapter 8. Simplicial Methods in Homological Algebra FC05](chapter-8-simplicial-methods-in-homological-algebra-fc05)

[Provenance contract for FC05 C09](provenance-contract-for-fc05-c09)

[Chapter 9. Hochschild and Cyclic Homology FC05](chapter-9-hochschild-and-cyclic-homology-fc05)

[Provenance contract for FC05 C10](provenance-contract-for-fc05-c10)

[Chapter 10. The Derived Category FC05](chapter-10-the-derived-category-fc05)

[Provenance contract for FC05 CA](provenance-contract-for-fc05-ca)

[Appendix A. Category Theory Language FC05](appendix-a-category-theory-language-fc05)
