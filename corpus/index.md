---
okf_version: '0.1'
---

# References

# Concepts

- [Ambiguity resolution source map for issues 1 and 4](ambiguity-resolution-source-map-for-issues-1-and-4) - Survey date: 2026-07-22. Epistemic status: reference record of a three-agent source survey (two transcript explorers, one Downloads explorer) mapping the mathematically underspecified items in lean-lattices issues #1 and #4 to resolving sources. Rulings quoted below are the *final* settled answers of adversarial ChatGPT threads (earlier answers in those threads are frequently retracted); coverage caveats at the end.
- [Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)](category-functor-coverage-audit-6-of-the-repo-is-an-actual-category-or-functor-2026-08-06-as-of-bb4ae16) - Full read-every-file audit (five parallel subagents, no sampling, no grep-only proxies) of every `.lean` file under `CategoryGraph/` and `LeanCategories/` as of commit `bb4ae16` (2026-08-06), classifying every top-level declaration as CATEGORY (a genuine `instance : Category X`, or the object-type of one), FUNCTOR (a genuine `C ⥤ D` term or its obj/map/map_id/map_comp bundle), or NEITHER (with what it actually is — predicate, data record, unbuilt morphism structure, axiom, theorem, tooling).
- The authored category catalogue: 93 categories with definitions and declared hierarchy - # The Authored Category Catalogue — 93 categories
- [root-generated does not imply integral: counterexample at W strictly containing R](root-generated-does-not-imply-integral-counterexample-at-w-strictly-containing-r) - **The statement is false (found 2026-08-08).** The catalogue plan had this row in its implications table: `root-generated ⟹ integral`. The proof in the cell was: "`b(x,x) = 2 ∈ R` on a generating family forces `𝔰(b) ≤ R`". That proof assumes a root norm. Roots have no fixed norm. The statement fails on `BilinMod(R, W)` when `W` is larger than `R`.
- [Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)](category-functor-coverage-audit-6-of-the-repo-is-an-actual-category-or-functor-2026-08-06-as-of-bb4ae16) - # Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)
- 2026-08-09T15:46:59+0800 Definition-first audit of lean-categories plans - ## Verdict
- [Lean formalization source atlas and research log](lean-formalization-source-atlas-and-research-log) - ## Audited sources
- [Lean formalization source atlas and research log](lean-formalization-source-atlas-and-research-log) - # Lean formalization reuse research log
- [Lean formalization source atlas and research log](lean-formalization-source-atlas-and-research-log) - # Lean formalization source atlas and research log
- [Recursive mathematical decomposition and compressed insight](recursive-mathematical-decomposition-and-compressed-insight) - This record supplements [[global/references/mathematical-inquiry-under-artifact-pressure]]. It preserves two later episodes from Codex transcripts.
- TODO-ALGEBRA Mathlib and Lean source reuse audit - Most of `TODO-ALGEBRA.md` is not new foundational work. Mathlib already supplies the first six layers’ basic objects and machinery.
- [Duplication audit of formed-module arithmetic branch](duplication-audit-of-formed-module-arithmetic-branch) - # Duplication audit of formed-module arithmetic branch
- [Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)](category-functor-coverage-audit-6-of-the-repo-is-an-actual-category-or-functor-2026-08-06-as-of-bb4ae16) - # Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)
- [Lean formalization source atlas and research log](lean-formalization-source-atlas-and-research-log) - # Lean formalization source atlas and research log
- 2026-08-09T15:46:59+0800 Definition-first audit of lean-categories plans - # 2026-08-09T15:46:59+0800 Definition-first audit of lean-categories plans
- [Ambiguity resolution source map for issues 1 and 4](ambiguity-resolution-source-map-for-issues-1-and-4) - # Ambiguity resolution source map for issues 1 and 4
- TODO-ALGEBRA Mathlib and Lean source reuse audit - # TODO-ALGEBRA Mathlib and Lean source reuse audit
- The authored category catalogue: 93 categories with definitions and declared hierarchy - # The authored category catalogue: 93 categories with definitions and declared hierarchy
- [2026-08-09T15:46:59+0800 Definition-first audit of lean-categories plans](2026-08-09t15-46-59-0800-definition-first-audit-of-lean-categories-plans) - ## Verdict
- [TODO-ALGEBRA Mathlib and Lean source reuse audit](todo-algebra-mathlib-and-lean-source-reuse-audit) - # TODO-ALGEBRA Mathlib and Lean source reuse audit
- [The authored category catalogue: 93 categories with definitions and declared hierarchy](the-authored-category-catalogue-93-categories-with-definitions-and-declared-hierarchy) - # The authored category catalogue: 93 categories with definitions and declared hierarchy
- [Initial Zotero textbook checklist shortlist preserved verbatim](initial-zotero-textbook-checklist-shortlist-preserved-verbatim) - Yes. The live Zotero library contains several strong checklist sources. All items below have PDFs and Markdown extractions.
- [Foundational source corpus](foundational-source-corpus) - # Curriculum-based textbook checklist sources
- [Foundational source corpus](foundational-source-corpus) - # Standard graduate textbook checklist sources
- [Definition catalogue - Dummit and Foote Abstract Algebra](definition-catalogue-dummit-and-foote-abstract-algebra) - # Abstract Algebra: definition catalogue
- [Definition catalogue - Folland Real Analysis](definition-catalogue-folland-real-analysis) - # Real Analysis: definition catalogue
- [Definition catalogue - Ahlfors Complex Analysis](definition-catalogue-ahlfors-complex-analysis) - # Complex Analysis: definition catalogue
- [Definition catalogue - Atiyah and Macdonald Commutative Algebra](definition-catalogue-atiyah-and-macdonald-commutative-algebra) - # Introduction to Commutative Algebra
- [Definition catalogue - Shafarevich Basic Algebraic Geometry 1](definition-catalogue-shafarevich-basic-algebraic-geometry-1) - # Basic Algebraic Geometry 1
- [Definition catalogue - Hartshorne Algebraic Geometry](definition-catalogue-hartshorne-algebraic-geometry) - # Algebraic Geometry
- [Definition catalogue - Weibel Homological Algebra](definition-catalogue-weibel-homological-algebra) - # *An Introduction to Homological Algebra*: definition catalogue
- [Definition catalogue - Hatcher Algebraic Topology](definition-catalogue-hatcher-algebraic-topology) - # *Algebraic Topology*: definition catalogue
- [Definition catalogue - Whitehead Homotopy Theory](definition-catalogue-whitehead-homotopy-theory) - # *Elements of Homotopy Theory*: definition catalogue
- [Definition catalogue - Apostol Analytic Number Theory](definition-catalogue-apostol-analytic-number-theory) - # *Introduction to Analytic Number Theory*: definition catalogue
- [Dummit and Foote definition catalogue](dummit-and-foote-definition-catalogue) - # Abstract Algebra: definition catalogue
- [Folland real analysis definition catalogue](folland-real-analysis-definition-catalogue) - # Real Analysis: definition catalogue
- [Ahlfors complex analysis definition catalogue](ahlfors-complex-analysis-definition-catalogue) - # Complex Analysis: definition catalogue
- [Atiyah and Macdonald definition catalogue](atiyah-and-macdonald-definition-catalogue) - # Introduction to Commutative Algebra
- [Shafarevich varieties definition catalogue](shafarevich-varieties-definition-catalogue) - # Basic Algebraic Geometry 1
- [Hartshorne schemes definition catalogue](hartshorne-schemes-definition-catalogue) - # Algebraic Geometry
- [Weibel homological algebra definition catalogue](weibel-homological-algebra-definition-catalogue) - # *An Introduction to Homological Algebra*: definition catalogue
- [Hatcher algebraic topology definition catalogue](hatcher-algebraic-topology-definition-catalogue) - # *Algebraic Topology*: definition catalogue
- [Whitehead homotopy theory definition catalogue](whitehead-homotopy-theory-definition-catalogue) - # *Elements of Homotopy Theory*: definition catalogue
- [Apostol analytic number theory definition catalogue](apostol-analytic-number-theory-definition-catalogue) - # *Introduction to Analytic Number Theory*: definition catalogue
- [Sage preamble definition catalogue](sage-preamble-definition-catalogue) - # Sage preamble: definition catalogue
- Foundation 0.1 unmatched-definition reference search - Search scope before new authorship: pinned Mathlib at 81a5d257c8e410db227a6665ed08f64fea08e997; current lean-categories; current Mathlib pull requests; facebookresearch/atlas-lean; google-deepmind/formal-conjectures; leanprover-community/LeanProject reference repositories; Lean Reservoir packages; and targeted GitHub searches. Results: WuProver/groebner_proj supplied a mature Apache-2.0 Groebner-basis definition and was adapted with attribution. No reusable Lean implementation was found for associated graded rings or modules, Zariski rings, outer automorphism groups, rational canonical forms, or Jordan canonical forms. Related objects were rejected as substitutes: Rees algebras are not associated graded objects; Zariski topology and Zariski-local morphism properties are not Zariski rings; Smith normal form is not rational canonical form; lattice Jordan decomposition is not matrix Jordan canonical form. User approved beginning new implementation after this search was recorded.
- Atiyah-Macdonald Chapter 11 dimension-theory reuse search - Search recorded for LeanCategories/Algebra/DimensionTheory.lean on 2026-08-15. Consulted the pinned Mathlib source and declarations: Mathlib/Order/KrullDimension.lean for Order.LTSeries, Order.height, Order.coheight, and Order.krullDim; Mathlib/RingTheory/Spectrum/Prime/Defs.lean for the prime-spectrum order; Mathlib/RingTheory/Ideal/Height.lean for Ideal.height; Mathlib/RingTheory/KrullDimension/Basic.lean for ringKrullDim; Mathlib/RingTheory/KrullDimension/Module.lean for Module.supportDim; Mathlib/RingTheory/AlgebraicIndependent/Basic.lean for Algebra.trdeg; Mathlib/RingTheory/RegularLocalRing/Defs.lean for IsRegularLocalRing. Consulted Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean documentation for the standard codimension route through Order.coheight. Consulted corpus/atiyah-and-macdonald-definition-catalogue.md, Chapter 11, pp. 116-124. Existing Mathlib definitions route prime chains, ideal height, ring and module Krull dimension, codimension weight, transcendence degree, and regular local rings. No exact Mathlib declaration was found for systems of parameters, so the file adds only the standard predicate from Atiyah-Macdonald p. 122 using Ideal.span, Ideal.radical, and IsLocalRing.maximalIdeal. No dimension theorem, principal ideal theorem, or Noether normalization was authored.
- Dummit-Foote Chapter 16 reuse search - Searched the pinned Mathlib checkout under .lake/packages/mathlib/Mathlib, including RingTheory/Artinian/Ring.lean, RingTheory/Length.lean, RingTheory/FiniteLength.lean, RingTheory/DiscreteValuationRing/Basic.lean, RingTheory/DedekindDomain/Basic.lean, RingTheory/DedekindDomain/Dvr.lean, RingTheory/FractionalIdeal/Basic.lean, RingTheory/FractionalIdeal/Operations.lean, RingTheory/ClassGroup/Basic.lean, RingTheory/Valuation, and RingTheory/AdicCompletion. Searched in-repo owners LeanCategories/Algebra/Concrete/Rings.lean, Algebra/IntegralDependence.lean, Algebra/FractionalIdeals.lean, Algebra/Local.lean, Algebra/IdealProfiniteCompletion*.lean, ForMathlib/AdicCompletion*.lean, plus the Dummit-Foote and Atiyah-Macdonald catalogues and project source atlas. Chapter 16 catalogue terms are Artinian ring, discrete valuation, discrete valuation ring, Dedekind domain, fractional ideal, and ideal class group. Mathlib and existing LeanCategories owners already provide these: IsArtinianRing/ArtinianRingCat, Valuation/ValuationSubring, IsDiscreteValuationRing/DiscreteValuationRingCat, IsDedekindDomain/DedekindDomainCat, FractionalIdeal, and ClassGroup. No new mathematical definitions or theorems are needed; implementation should expose precise route aliases only.
- shafarevich-chapter-i-affine-route-search - Search note for Shafarevich Basic Algebraic Geometry I, Chapter I affine algebraic sets and affine varieties.
- Shafarevich projective varieties reuse search - # Shafarevich projective varieties reuse search
- [Dummit and Foote definition catalogue](dummit-and-foote-definition-catalogue) - # Dummit and Foote definition catalogue
- [Atiyah and Macdonald definition catalogue](atiyah-and-macdonald-definition-catalogue) - # Atiyah and Macdonald definition catalogue
- [Folland real analysis definition catalogue](folland-real-analysis-definition-catalogue) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/folland-real-analysis-definition-catalogue
- [Ahlfors complex analysis definition catalogue](ahlfors-complex-analysis-definition-catalogue) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/ahlfors-complex-analysis-definition-catalogue
- [Apostol analytic number theory definition catalogue](apostol-analytic-number-theory-definition-catalogue) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/apostol-analytic-number-theory-definition-catalogue
- [Weibel homological algebra definition catalogue](weibel-homological-algebra-definition-catalogue) - # Weibel homological algebra definition catalogue
- [Hatcher algebraic topology definition catalogue](hatcher-algebraic-topology-definition-catalogue) - # Hatcher algebraic topology definition catalogue
- [Whitehead homotopy theory definition catalogue](whitehead-homotopy-theory-definition-catalogue) - # Whitehead homotopy theory definition catalogue
- [Hartshorne schemes definition catalogue](hartshorne-schemes-definition-catalogue) - # Hartshorne schemes definition catalogue
- [Shafarevich varieties definition catalogue](shafarevich-varieties-definition-catalogue) - # Shafarevich varieties definition catalogue
- [Foundational source corpus](foundational-source-corpus) - # Foundational source corpus v1
- [Sage preamble definition catalogue](sage-preamble-definition-catalogue) - # Sage preamble definition catalogue
- [Foundational source corpus](foundational-source-corpus) - # Foundational source corpus v1 (frozen)
- [Foundational source corpus](foundational-source-corpus) - # Foundational source corpus
- [Foundational corpus status](foundational-corpus-status) - ---
- [Foundational source corpus](foundational-source-corpus) - # Foundational source corpus
- [Foundational corpus units FC01 Dummit–Foote](foundational-corpus-units-fc01-dummit-foote) - # FC01 — Dummit–Foote, *Abstract Algebra*
- [FC02 — Munkres, Topology](foundational-corpus-units-fc02-munkres) - # FC02 — Munkres, *Topology*
- [Foundational corpus units FC04 Atiyah Macdonald](foundational-corpus-units-fc04-atiyah-macdonald) - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra*
- [Foundational corpus units FC05 Weibel](foundational-corpus-units-fc05-weibel) - Canonical Sweep-I source-unit catalogue for Weibel, 1,059 units across Chapters 1–10 and Appendix A; exercises excluded.
- [Foundational corpus units FC06 Hartshorne](foundational-corpus-units-fc06-hartshorne) - Canonical Sweep-I source-unit catalogue for Hartshorne, 969 units across Chapters I–V; exercises and Appendices A–C excluded.
- [Foundational corpus mapping FC01 Dummit Foote](foundational-corpus-mapping-fc01-dummit-foote) - ---
- [Foundational corpus units FC01 Dummit–Foote](foundational-corpus-units-fc01-dummit-foote) - ---
- [Foundational corpus mapping FC02 Munkres](foundational-corpus-mapping-fc02-munkres) - ---
- [Foundational corpus mapping FC03 Riehl Category Theory in Context](foundational-corpus-mapping-fc03-riehl-category-theory-in-context) - ---
- Chapter 2. Modules - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping
- [Provenance contract for C01](provenance-contract-for-c01) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
- [Chapter 1. Rings and ideals](chapter-1-rings-and-ideals) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
- [Provenance contract for C02](provenance-contract-for-c02) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
- Chapter 2. Modules - # Chapter 2. Modules
- [Provenance contract for C03](provenance-contract-for-c03) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
- [Chapter 3. Rings and Modules of Fractions; Local Properties](chapter-3-rings-and-modules-of-fractions-local-properties) - Extracted from Chapter 2. Modules.
- [Provenance contract for C04](provenance-contract-for-c04) - Extracted from Chapter 2. Modules.
- [Chapter 4. Primary Decomposition](chapter-4-primary-decomposition) - Extracted from Chapter 2. Modules.
- [Provenance contract for C05](provenance-contract-for-c05) - Extracted from Chapter 2. Modules.
- [Chapter 5. Integral Dependence and Valuations](chapter-5-integral-dependence-and-valuations) - Extracted from Chapter 2. Modules.
- [Provenance contract for C06](provenance-contract-for-c06) - Extracted from Chapter 2. Modules.
- [Chapter 6. Chain Conditions](chapter-6-chain-conditions) - Extracted from Chapter 2. Modules.

- Chapter 2. Modules - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping
- [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald) - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping
* [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald.md) - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping

* [Provenance contract for C07](provenance-contract-for-c07.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.

* [Chapter 7. Noetherian Rings](chapter-7-noetherian-rings.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
* [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald.md) - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping

* [Provenance contract for C08](provenance-contract-for-c08.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.

* [Chapter 8. Artin Rings](chapter-8-artin-rings.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
* [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald.md) - # FC04 — Atiyah–Macdonald, *Introduction to Commutative Algebra* mapping

* [Provenance contract for C09](provenance-contract-for-c09.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.

* [Chapter 9. Discrete Valuation Rings and Dedekind Domains](chapter-9-discrete-valuation-rings-and-dedekind-domains.md) - Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.

* [Provenance contract for C10](provenance-contract-for-c10.md) - # Provenance contract for C10

* [Chapter 10. Completions](chapter-10-completions.md) - # Chapter 10. Completions
* [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald.md) - # Foundational corpus mapping FC04 Atiyah Macdonald

* [Provenance contract for C11](provenance-contract-for-c11.md) - # Provenance contract for C11

* [Chapter 11. Dimension Theory](chapter-11-dimension-theory.md) - # Chapter 11. Dimension Theory
* [Foundational corpus mapping FC04 Atiyah Macdonald](foundational-corpus-mapping-fc04-atiyah-macdonald.md) - # Foundational corpus mapping FC04 Atiyah Macdonald
* [Foundational corpus status](foundational-corpus-status.md) - # Foundational corpus status

* [Provenance contract for FC05 C01](provenance-contract-for-fc05-c01.md) - # Provenance contract for FC05 C01

* [Chapter 1. Chain Complexes FC05](chapter-1-chain-complexes-fc05.md) - ## Chapter 1. Chain Complexes

* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C02](provenance-contract-for-fc05-c02.md) - # Provenance contract for FC05 C02

* [Chapter 2. Derived Functors FC05](chapter-2-derived-functors-fc05.md) - # Chapter 2. Derived Functors FC05
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C03](provenance-contract-for-fc05-c03.md) - # Provenance contract for FC05 C03

* [Chapter 3. Tor and Ext FC05](chapter-3-tor-and-ext-fc05.md) - # Chapter 3. Tor and Ext FC05
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C04](provenance-contract-for-fc05-c04.md) - # Provenance contract for FC05 C04

* [Chapter 4. Homological Dimension FC05](chapter-4-homological-dimension-fc05.md) - ## Chapter 4. Homological Dimension
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C05](provenance-contract-for-fc05-c05.md) - # Provenance contract for FC05 C05

* [Chapter 5. Spectral Sequences FC05](chapter-5-spectral-sequences-fc05.md) - ## Chapter 5. Spectral Sequences
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C06](provenance-contract-for-fc05-c06.md) - # Provenance contract for FC05 C06

* [Chapter 6. Group Homology and Cohomology FC05](chapter-6-group-homology-and-cohomology-fc05.md) - ## Chapter 6. Group Homology and Cohomology
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C07](provenance-contract-for-fc05-c07.md) - # Provenance contract for FC05 C07

* [Chapter 7. Lie Algebra Homology and Cohomology FC05](chapter-7-lie-algebra-homology-and-cohomology-fc05.md) - ## Chapter 7. Lie Algebra Homology and Cohomology
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # FC05 — Weibel, *An Introduction to Homological Algebra* mapping

* [Provenance contract for FC05 C08](provenance-contract-for-fc05-c08.md) - ## Provenance contract for FC05 C08

* [Chapter 8. Simplicial Methods in Homological Algebra FC05](chapter-8-simplicial-methods-in-homological-algebra-fc05.md) - ## Chapter 8. Simplicial Methods in Homological Algebra
* [Foundational corpus mapping FC05 Weibel](foundational-corpus-mapping-fc05-weibel.md) - # Foundational corpus mapping FC05 Weibel
* [Provenance contract for FC05 C08](provenance-contract-for-fc05-c08.md) - ## Provenance contract for FC05 C08

* [Provenance contract for FC05 C09](provenance-contract-for-fc05-c09.md) - ## Provenance contract for FC05 C09

* [Chapter 9. Hochschild and Cyclic Homology FC05](chapter-9-hochschild-and-cyclic-homology-fc05.md) - ## Chapter 9. Hochschild and Cyclic Homology
* [Provenance contract for FC05 C09](provenance-contract-for-fc05-c09.md) - ## Provenance contract for FC05 C09

* [Provenance contract for FC05 C10](provenance-contract-for-fc05-c10.md) - # Provenance contract for FC05 C10

* [Chapter 10. The Derived Category FC05](chapter-10-the-derived-category-fc05.md) - # Chapter 10. The Derived Category FC05

* [Provenance contract for FC05 CA](provenance-contract-for-fc05-ca.md) - # Provenance contract for FC05 CA

* [Appendix A. Category Theory Language FC05](appendix-a-category-theory-language-fc05.md) - # Appendix A. Category Theory Language FC05
* [Foundational corpus status](foundational-corpus-status.md) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/foundational-corpus-status

* [Provenance contract for FC06 C01](provenance-contract-for-fc06-c01.md) - # Provenance contract for FC06 C01

* [Chapter 1. Varieties FC06](chapter-1-varieties-fc06.md) - # Chapter 1. Varieties FC06

* [Foundational corpus mapping FC06 Hartshorne](foundational-corpus-mapping-fc06-hartshorne.md) - # Foundational corpus mapping FC06 Hartshorne

* [Chapter 2. Schemes FC06](chapter-2-schemes-fc06.md) - # Chapter 2. Schemes FC06

* [Provenance contract for FC06 C02](provenance-contract-for-fc06-c02.md) - # Provenance contract for FC06 C02
* [Foundational corpus mapping FC06 Hartshorne](foundational-corpus-mapping-fc06-hartshorne.md) - # Foundational corpus mapping FC06 Hartshorne

* [Chapter 3. Cohomology FC06](chapter-3-cohomology-fc06.md) - # Chapter 3. Cohomology FC06

* [Provenance contract for FC06 C03](provenance-contract-for-fc06-c03.md) - # Provenance contract for FC06 C03
* [Foundational corpus mapping FC06 Hartshorne](foundational-corpus-mapping-fc06-hartshorne.md) - # Foundational corpus mapping FC06 Hartshorne
* [Chapter 2. Schemes FC06](chapter-2-schemes-fc06.md) - # Chapter 2. Schemes FC06

* [Chapter 4. Curves FC06](chapter-4-curves-fc06.md) - # Chapter 4. Curves FC06

* [Provenance contract for FC06 C04](provenance-contract-for-fc06-c04.md) - # Provenance contract for FC06 C04

* [Chapter 5. Surfaces FC06](chapter-5-surfaces-fc06.md) - # Chapter 5. Surfaces FC06

* [Provenance contract for FC06 C05](provenance-contract-for-fc06-c05.md) - # Provenance contract for FC06 C05
* [Foundational corpus status](foundational-corpus-status.md) - # Foundational corpus status
* [Foundational source corpus](foundational-source-corpus.md) - # Foundational source corpus v1

* [Chapter 0. Some Underlying Geometric Notions FC07](chapter-0-some-underlying-geometric-notions-fc07.md) - # Chapter 0. Some Underlying Geometric Notions FC07

* [Provenance contract for FC07 C00](provenance-contract-for-fc07-c00.md) - # Provenance contract for FC07 C00

* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # FC07 — Hatcher, *Algebraic Topology* mapping

* [Foundational corpus units FC13 Matsumura](foundational-corpus-units-fc13-matsumura.md) - Pinned source: Hideyuki Matsumura, *Commutative Ring Theory*, Cambridge Studies in Advanced Mathematics 8, translated by Miles Reid; local pinned PDF `/home/dzack/Zotero/storage/JHZDICNF/local-write-api-1781955283942-TSA7KUJB_matsumura.pdf`.
* [Foundational source corpus](foundational-source-corpus.md) - # Foundational source corpus v1

* [Foundational corpus units FC14 Humphreys](foundational-corpus-units-fc14-humphreys.md) - Pinned source: J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in Mathematics 9, third printing revised (1980).
* [Foundational source corpus](foundational-source-corpus.md) - # Foundational source corpus v1

* [Chapter 1. The Fundamental Group FC07](chapter-1-the-fundamental-group-fc07.md) - # Chapter 1. The Fundamental Group FC07

* [Provenance contract for FC07 C01](provenance-contract-for-fc07-c01.md) - # Provenance contract for FC07 C01
* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # FC07 — Hatcher, *Algebraic Topology* mapping

* [Foundational corpus units FC15 Humphreys Reflection Groups and Coxeter Groups](foundational-corpus-units-fc15-humphreys-reflection-groups-and-coxeter-groups.md) - # Foundational corpus units FC15 Humphreys Reflection Groups and Coxeter Groups
* [Foundational source corpus](foundational-source-corpus.md) - # Foundational source corpus

* [Foundational corpus units FC16 Humphreys Linear Algebraic Groups](foundational-corpus-units-fc16-humphreys-linear-algebraic-groups.md) - # Foundational corpus units FC16 Humphreys Linear Algebraic Groups

* [Chapter 0. Conventions and terminology FC13](chapter-0-conventions-and-terminology-fc13.md) - # Chapter 0. Conventions and terminology FC13

* [Provenance contract for FC13 C00](provenance-contract-for-fc13-c00.md) - # Provenance contract for FC13 C00

* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - # Foundational corpus mapping FC13 Matsumura

* [Chapter 2. Homology FC07](chapter-2-homology-fc07.md) - # Chapter 2. Homology FC07

* [Provenance contract for FC07 C02](provenance-contract-for-fc07-c02.md) - # Provenance contract for FC07 C02
* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # Foundational corpus mapping FC07 Hatcher

* [Chapter 1. Commutative rings and modules FC13](chapter-1-commutative-rings-and-modules-fc13.md) - # Chapter 1. Commutative rings and modules FC13

* [Provenance contract for FC13 C01](provenance-contract-for-fc13-c01.md) - # Provenance contract for FC13 C01
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - # Foundational corpus mapping FC13 Matsumura

* [Chapter 2. Prime ideals FC13](chapter-2-prime-ideals-fc13.md) - # Chapter 2. Prime ideals FC13

* [Provenance contract for FC13 C02](provenance-contract-for-fc13-c02.md) - # Provenance contract for FC13 C02
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - # Foundational corpus mapping FC13 Matsumura

* [Chapter 3. Properties of extension rings FC13](chapter-3-properties-of-extension-rings-fc13.md) - # Chapter 3. Properties of extension rings FC13

* [Provenance contract for FC13 C03](provenance-contract-for-fc13-c03.md) - # Provenance contract for FC13 C03
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - # Foundational corpus mapping FC13 Matsumura

* [Chapter 4. Valuation rings, DVRs, Dedekind rings and Krull rings FC13](chapter-4-valuation-rings-dvrs-dedekind-rings-and-krull-rings-fc13.md) - # Chapter 4. Valuation rings, DVRs, Dedekind rings and Krull rings FC13

* [Provenance contract for FC13 C04](provenance-contract-for-fc13-c04.md) - # Provenance contract for FC13 C04
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/foundational-corpus-mapping-fc13-matsumura

* [Chapter 3. Cohomology FC07](chapter-3-cohomology-fc07.md) - # Chapter 3. Cohomology FC07

* [Provenance contract for FC07 C03](provenance-contract-for-fc07-c03.md) - # Provenance contract for FC07 C03
* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # Foundational corpus mapping FC07 Hatcher

* [Chapter 5. Dimension theory FC13](chapter-5-dimension-theory-fc13.md) - # Chapter 5. Dimension theory FC13

* [Provenance contract for FC13 C05](provenance-contract-for-fc13-c05.md) - # Provenance contract for FC13 C05
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - ````markdown #projects/github.com__dzackgarza__lean-categories/references/foundational-corpus-mapping-fc13-matsumura

* [Chapter 6. Regular sequences, Cohen–Macaulay and Gorenstein rings FC13](chapter-6-regular-sequences-cohen-macaulay-and-gorenstein-rings-fc13.md) - # Chapter 6. Regular sequences, Cohen–Macaulay and Gorenstein rings FC13

* [Provenance contract for FC13 C06](provenance-contract-for-fc13-c06.md) - # Provenance contract for FC13 C06
* [Foundational corpus mapping FC13 Matsumura](foundational-corpus-mapping-fc13-matsumura.md) - # FC13 — Matsumura, *Commutative Ring Theory* mapping
* [Chapter 6. Regular sequences, Cohen–Macaulay and Gorenstein rings FC13](chapter-6-regular-sequences-cohen-macaulay-and-gorenstein-rings-fc13.md) - # Chapter 6. Regular sequences, Cohen–Macaulay and Gorenstein rings FC13

* [Chapter 7. Regular rings, UFDs and complete intersections FC13](chapter-7-regular-rings-ufds-and-complete-intersections-fc13.md) - # Chapter 7. Regular rings, UFDs and complete intersections FC13

* [Provenance contract for FC13 C07](provenance-contract-for-fc13-c07.md) - # Provenance contract for FC13 C07

* [Chapter 8. Local flatness and openness loci FC13](chapter-8-local-flatness-and-openness-loci-fc13.md) - # Chapter 8. Local flatness and openness loci FC13

* [Provenance contract for FC13 C08](provenance-contract-for-fc13-c08.md) - # Provenance contract for FC13 C08

* [Chapter 4. Homotopy Theory FC07](chapter-4-homotopy-theory-fc07.md) - # Chapter 4. Homotopy Theory FC07

* [Provenance contract for FC07 C04](provenance-contract-for-fc07-c04.md) - # Provenance contract for FC07 C04
* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # Foundational corpus mapping FC07 Hatcher

* [Chapter 9. Differentials, separability and higher derivations FC13](chapter-9-differentials-separability-and-higher-derivations-fc13.md) - # Chapter 9. Differentials, separability and higher derivations FC13

* [Provenance contract for FC13 C09](provenance-contract-for-fc13-c09.md) - # Provenance contract for FC13 C09

* [Appendix. Topology of Cell Complexes FC07](appendix-topology-of-cell-complexes-fc07.md) - # Appendix. Topology of Cell Complexes FC07

* [Provenance contract for FC07 CA](provenance-contract-for-fc07-ca.md) - # Provenance contract for FC07 CA
* [Foundational corpus mapping FC07 Hatcher](foundational-corpus-mapping-fc07-hatcher.md) - # Foundational corpus mapping FC07 Hatcher

* [Chapter 10. Adic smoothness, Cohen structure and Jacobian criteria FC13](chapter-10-adic-smoothness-cohen-structure-and-jacobian-criteria-fc13.md) - # Chapter 10. Adic smoothness, Cohen structure and Jacobian criteria FC13

* [Provenance contract for FC13 C10](provenance-contract-for-fc13-c10.md) - # Provenance contract for FC13 C10

* [Chapter 11. Catenarity, formal fibres and normalization FC13](chapter-11-catenarity-formal-fibres-and-normalization-fc13.md) - # Chapter 11. Catenarity, formal fibres and normalization FC13

* [Provenance contract for FC13 C11](provenance-contract-for-fc13-c11.md) - # Provenance contract for FC13 C11

* [Chapter 1. Smooth Manifolds FC08](chapter-1-smooth-manifolds-fc08.md) - # Chapter 1. Smooth Manifolds FC08

* [Provenance contract for FC08 C01](provenance-contract-for-fc08-c01.md) - # Provenance contract for FC08 C01

* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 2. Smooth Maps FC08](chapter-2-smooth-maps-fc08.md) - # Chapter 2. Smooth Maps FC08

* [Provenance contract for FC08 C02](provenance-contract-for-fc08-c02.md) - # Provenance contract for FC08 C02
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 3. Tangent Vectors FC08](chapter-3-tangent-vectors-fc08.md) - # Chapter 3. Tangent Vectors FC08

* [Provenance contract for FC08 C03](provenance-contract-for-fc08-c03.md) - # Provenance contract for FC08 C03
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 4. Submersions, Immersions, and Embeddings FC08](chapter-4-submersions-immersions-and-embeddings-fc08.md) - # Chapter 4. Submersions, Immersions, and Embeddings FC08

* [Provenance contract for FC08 C04](provenance-contract-for-fc08-c04.md) - # Provenance contract for FC08 C04
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # Foundational corpus mapping FC09 Neukirch

* [Provenance contract for FC09 C01](provenance-contract-for-fc09-c01.md) - # Provenance contract for FC09 C01

* [Chapter 1. Algebraic Integers FC09](chapter-1-algebraic-integers-fc09.md) - # Chapter 1. Algebraic Integers FC09
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 5. Submanifolds FC08](chapter-5-submanifolds-fc08.md) - # Chapter 5. Submanifolds FC08

* [Provenance contract for FC08 C05](provenance-contract-for-fc08-c05.md) - # Provenance contract for FC08 C05
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 6. Sard’s Theorem FC08](chapter-6-sards-theorem-fc08.md) - # Chapter 6. Sard’s Theorem FC08

* [Provenance contract for FC08 C06](provenance-contract-for-fc08-c06.md) - # Provenance contract for FC08 C06
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 7. Lie Groups FC08](chapter-7-lie-groups-fc08.md) - # Chapter 7. Lie Groups FC08

* [Provenance contract for FC08 C07](provenance-contract-for-fc08-c07.md) - # Provenance contract for FC08 C07
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 2. Valuations FC09](chapter-2-valuations-fc09.md) - # Chapter 2. Valuations FC09

* [Provenance contract for FC09 C02](provenance-contract-for-fc09-c02.md) - # Provenance contract for FC09 C02
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 8. Vector Fields FC08](chapter-8-vector-fields-fc08.md) - # Chapter 8. Vector Fields FC08

* [Provenance contract for FC08 C08](provenance-contract-for-fc08-c08.md) - # Provenance contract for FC08 C08
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 9. Integral Curves and Flows FC08](chapter-9-integral-curves-and-flows-fc08.md) - # Chapter 9. Integral Curves and Flows FC08

* [Provenance contract for FC08 C09](provenance-contract-for-fc08-c09.md) - # Provenance contract for FC08 C09
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 3. Riemann-Roch Theory FC09](chapter-3-riemann-roch-theory-fc09.md) - # Chapter 3. Riemann-Roch Theory FC09

* [Provenance contract for FC09 C03](provenance-contract-for-fc09-c03.md) - # Provenance contract for FC09 C03
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 10. Vector Bundles FC08](chapter-10-vector-bundles-fc08.md) - # Chapter 10. Vector Bundles FC08

* [Provenance contract for FC08 C10](provenance-contract-for-fc08-c10.md) - # Provenance contract for FC08 C10
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 4. Abstract Class Field Theory FC09](chapter-4-abstract-class-field-theory-fc09.md) - # Chapter 4. Abstract Class Field Theory FC09

* [Provenance contract for FC09 C04](provenance-contract-for-fc09-c04.md) - # Provenance contract for FC09 C04
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 11. Covectors and Covector Fields FC08](chapter-11-covectors-and-covector-fields-fc08.md) - # Chapter 11. Covectors and Covector Fields FC08

* [Provenance contract for FC08 C11](provenance-contract-for-fc08-c11.md) - # Provenance contract for FC08 C11
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 5. Local Class Field Theory FC09](chapter-5-local-class-field-theory-fc09.md) - # Chapter 5. Local Class Field Theory FC09

* [Provenance contract for FC09 C05](provenance-contract-for-fc09-c05.md) - # Provenance contract for FC09 C05
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 12. Tensors FC08](chapter-12-tensors-fc08.md) - # Chapter 12. Tensors FC08

* [Provenance contract for FC08 C12](provenance-contract-for-fc08-c12.md) - # Provenance contract for FC08 C12
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - ---

* [Chapter 6. Global Class Field Theory FC09](chapter-6-global-class-field-theory-fc09.md) - # Chapter 6. Global Class Field Theory FC09

* [Provenance contract for FC09 C06](provenance-contract-for-fc09-c06.md) - # Provenance contract for FC09 C06
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 13. Riemannian Metrics FC08](chapter-13-riemannian-metrics-fc08.md) - # Chapter 13. Riemannian Metrics FC08

* [Provenance contract for FC08 C13](provenance-contract-for-fc08-c13.md) - # Provenance contract for FC08 C13
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 14. Differential Forms FC08](chapter-14-differential-forms-fc08.md) - # Chapter 14. Differential Forms FC08

* [Provenance contract for FC08 C14](provenance-contract-for-fc08-c14.md) - # Provenance contract for FC08 C14
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 7. Zeta Functions and L-series FC09](chapter-7-zeta-functions-and-l-series-fc09.md) - ## Chapter 7. Zeta Functions and L-series

* [Provenance contract for FC09 C07](provenance-contract-for-fc09-c07.md) - ## Provenance contract for FC09 C07
* [Foundational corpus mapping FC09 Neukirch](foundational-corpus-mapping-fc09-neukirch.md) - # FC09 — Neukirch, *Algebraic Number Theory* mapping

* [Chapter 15. Orientations FC08](chapter-15-orientations-fc08.md) - # Chapter 15. Orientations FC08

* [Provenance contract for FC08 C15](provenance-contract-for-fc08-c15.md) - # Provenance contract for FC08 C15
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Foundational corpus mapping FC10 Serre Local Fields](foundational-corpus-mapping-fc10-serre-local-fields.md) - # FC10 — Serre, *Local Fields* mapping

* [Chapter 16. Integration on Manifolds FC08](chapter-16-integration-on-manifolds-fc08.md) - # Chapter 16. Integration on Manifolds FC08

* [Provenance contract for FC08 C16](provenance-contract-for-fc08-c16.md) - # Provenance contract for FC08 C16
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 17. de Rham Cohomology FC08](chapter-17-de-rham-cohomology-fc08.md) - # Chapter 17. de Rham Cohomology FC08

* [Provenance contract for FC08 C17](provenance-contract-for-fc08-c17.md) - # Provenance contract for FC08 C17
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 18. The de Rham Theorem FC08](chapter-18-the-de-rham-theorem-fc08.md) - # Chapter 18. The de Rham Theorem FC08

* [Provenance contract for FC08 C18](provenance-contract-for-fc08-c18.md) - # Provenance contract for FC08 C18
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 19. Distributions and Foliations FC08](chapter-19-distributions-and-foliations-fc08.md) - # Chapter 19. Distributions and Foliations FC08

* [Provenance contract for FC08 C19](provenance-contract-for-fc08-c19.md) - # Provenance contract for FC08 C19
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 20. The Exponential Map FC08](chapter-20-the-exponential-map-fc08.md) - # Chapter 20. The Exponential Map FC08

* [Provenance contract for FC08 C20](provenance-contract-for-fc08-c20.md) - # Provenance contract for FC08 C20
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 1. Discrete Valuation Rings and Dedekind Domains FC10](chapter-1-discrete-valuation-rings-and-dedekind-domains-fc10.md) - # Chapter 1. Discrete Valuation Rings and Dedekind Domains FC10

* [Provenance contract for FC10 C01](provenance-contract-for-fc10-c01.md) - # Provenance contract for FC10 C01

* [Chapter 2. Completion FC10](chapter-2-completion-fc10.md) - # Chapter 2. Completion FC10

* [Provenance contract for FC10 C02](provenance-contract-for-fc10-c02.md) - # Provenance contract for FC10 C02

* [Chapter 3. Discriminant and Different FC10](chapter-3-discriminant-and-different-fc10.md) - # Chapter 3. Discriminant and Different FC10

* [Provenance contract for FC10 C03](provenance-contract-for-fc10-c03.md) - # Provenance contract for FC10 C03

* [Chapter 4. Ramification Groups FC10](chapter-4-ramification-groups-fc10.md) - # Chapter 4. Ramification Groups FC10

* [Provenance contract for FC10 C04](provenance-contract-for-fc10-c04.md) - # Provenance contract for FC10 C04

* [Chapter 5. The Norm FC10](chapter-5-the-norm-fc10.md) - # Chapter 5. The Norm FC10

* [Provenance contract for FC10 C05](provenance-contract-for-fc10-c05.md) - # Provenance contract for FC10 C05

* [Chapter 6. Artin Representation FC10](chapter-6-artin-representation-fc10.md) - # Chapter 6. Artin Representation FC10

* [Provenance contract for FC10 C06](provenance-contract-for-fc10-c06.md) - # Provenance contract for FC10 C06

* [Chapter 7. Basic Facts FC10](chapter-7-basic-facts-fc10.md) - # Chapter 7. Basic Facts FC10

* [Provenance contract for FC10 C07](provenance-contract-for-fc10-c07.md) - # Provenance contract for FC10 C07

* [Chapter 8. Cohomology of Finite Groups FC10](chapter-8-cohomology-of-finite-groups-fc10.md) - # Chapter 8. Cohomology of Finite Groups FC10

* [Provenance contract for FC10 C08](provenance-contract-for-fc10-c08.md) - # Provenance contract for FC10 C08

* [Chapter 9. Theorems of Tate and Nakayama FC10](chapter-9-theorems-of-tate-and-nakayama-fc10.md) - # Chapter 9. Theorems of Tate and Nakayama FC10

* [Provenance contract for FC10 C09](provenance-contract-for-fc10-c09.md) - # Provenance contract for FC10 C09

* [Chapter 10. Galois Cohomology FC10](chapter-10-galois-cohomology-fc10.md) - # Chapter 10. Galois Cohomology FC10

* [Provenance contract for FC10 C10](provenance-contract-for-fc10-c10.md) - # Provenance contract for FC10 C10

* [Chapter 11. Class Formations FC10](chapter-11-class-formations-fc10.md) - # Chapter 11. Class Formations FC10

* [Provenance contract for FC10 C11](provenance-contract-for-fc10-c11.md) - # Provenance contract for FC10 C11

* [Chapter 12. Brauer Group of a Local Field FC10](chapter-12-brauer-group-of-a-local-field-fc10.md) - # Chapter 12. Brauer Group of a Local Field FC10

* [Provenance contract for FC10 C12](provenance-contract-for-fc10-c12.md) - # Provenance contract for FC10 C12

* [Chapter 13. Local Class Field Theory FC10](chapter-13-local-class-field-theory-fc10.md) - # Chapter 13. Local Class Field Theory FC10

* [Provenance contract for FC10 C13](provenance-contract-for-fc10-c13.md) - # Provenance contract for FC10 C13

* [Chapter 14. Local Symbols and Existence Theorem FC10](chapter-14-local-symbols-and-existence-theorem-fc10.md) - # Chapter 14. Local Symbols and Existence Theorem FC10

* [Provenance contract for FC10 C14](provenance-contract-for-fc10-c14.md) - # Provenance contract for FC10 C14

* [Chapter 15. Ramification FC10](chapter-15-ramification-fc10.md) - # Chapter 15. Ramification FC10

* [Provenance contract for FC10 C15](provenance-contract-for-fc10-c15.md) - # Provenance contract for FC10 C15
* [Foundational corpus mapping FC10 Serre Local Fields](foundational-corpus-mapping-fc10-serre-local-fields.md) - # FC10 — Serre, *Local Fields* mapping

* [Chapter 21. Quotient Manifolds FC08](chapter-21-quotient-manifolds-fc08.md) - # Chapter 21. Quotient Manifolds FC08

* [Provenance contract for FC08 C21](provenance-contract-for-fc08-c21.md) - # Provenance contract for FC08 C21
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Chapter 22. Symplectic Manifolds FC08](chapter-22-symplectic-manifolds-fc08.md) - # Chapter 22. Symplectic Manifolds FC08

* [Provenance contract for FC08 C22](provenance-contract-for-fc08-c22.md) - # Provenance contract for FC08 C22
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Appendix A. Review of Topology FC08](appendix-a-review-of-topology-fc08.md) - # Appendix A. Review of Topology FC08

* [Provenance contract for FC08 CA](provenance-contract-for-fc08-ca.md) - # Provenance contract for FC08 Appendix A
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Foundational corpus mapping FC11 Peters Sterk](foundational-corpus-mapping-fc11-peters-sterk.md) - # FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping

* [Appendix B. Review of Linear Algebra FC08](appendix-b-review-of-linear-algebra-fc08.md) - # Appendix B. Review of Linear Algebra FC08

* [Provenance contract for FC08 CB](provenance-contract-for-fc08-cb.md) - # Provenance contract for FC08 Appendix B
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Appendix C. Review of Calculus FC08](appendix-c-review-of-calculus-fc08.md) - # Appendix C. Review of Calculus FC08

* [Provenance contract for FC08 CC](provenance-contract-for-fc08-cc.md) - # Provenance contract for FC08 Appendix C
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Appendix D. Ordinary Differential Equations FC08](appendix-d-ordinary-differential-equations-fc08.md) - # Appendix D. Ordinary Differential Equations FC08

* [Provenance contract for FC08 CD](provenance-contract-for-fc08-cd.md) - # Provenance contract for FC08 Appendix D
* [Foundational corpus mapping FC08 Lee](foundational-corpus-mapping-fc08-lee.md) - # Foundational corpus mapping FC08 Lee

* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # FC12 — Beauville, *Complex Algebraic Surfaces*, 2nd ed. mapping

* [Chapter I. Generalities on Algebraic Surfaces FC12](chapter-i-generalities-on-algebraic-surfaces-fc12.md) - # Chapter I. Generalities on Algebraic Surfaces FC12

* [Provenance contract for FC12 C01](provenance-contract-for-fc12-c01.md) - # Provenance contract for FC12 C01
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter II. Birational Maps and Blow-ups FC12](chapter-ii-birational-maps-and-blow-ups-fc12.md) - # Chapter II. Birational Maps and Blow-ups FC12

* [Provenance contract for FC12 C02](provenance-contract-for-fc12-c02.md) - # Provenance contract for FC12 C02
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter III. Ruled Surfaces FC12](chapter-iii-ruled-surfaces-fc12.md) - # Chapter III. Ruled Surfaces FC12

* [Provenance contract for FC12 C03](provenance-contract-for-fc12-c03.md) - # Provenance contract for FC12 C03
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter IV. Rational Surfaces FC12](chapter-iv-rational-surfaces-fc12.md) - # Chapter IV. Rational Surfaces FC12

* [Provenance contract for FC12 C04](provenance-contract-for-fc12-c04.md) - # Provenance contract for FC12 C04
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter V. The Albanese Map and Rationality FC12](chapter-v-the-albanese-map-and-rationality-fc12.md) - # Chapter V. The Albanese Map and Rationality FC12

* [Provenance contract for FC12 C05](provenance-contract-for-fc12-c05.md) - # Provenance contract for FC12 C05
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter VI FC12](chapter-vi-fc12.md) - # Chapter VI FC12

* [Provenance contract for FC12 C06](provenance-contract-for-fc12-c06.md) - # Provenance contract for FC12 C06
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter VII. Kodaira Dimension FC12](chapter-vii-kodaira-dimension-fc12.md) - # Chapter VII. Kodaira Dimension FC12

* [Provenance contract for FC12 C07](provenance-contract-for-fc12-c07.md) - # Provenance contract for FC12 C07
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter VIII. Surfaces of Kodaira Dimension Zero FC12](chapter-viii-surfaces-of-kodaira-dimension-zero-fc12.md) - # Chapter VIII. Surfaces of Kodaira Dimension Zero FC12

* [Provenance contract for FC12 C08](provenance-contract-for-fc12-c08.md) - # Provenance contract for FC12 C08
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter IX. Elliptic Surfaces FC12](chapter-ix-elliptic-surfaces-fc12.md) - # Chapter IX. Elliptic Surfaces FC12

* [Provenance contract for FC12 C09](provenance-contract-for-fc12-c09.md) - # Provenance contract for FC12 C09
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Chapter X. Surfaces of General Type FC12](chapter-x-surfaces-of-general-type-fc12.md) - # Chapter X. Surfaces of General Type FC12

* [Provenance contract for FC12 C10](provenance-contract-for-fc12-c10.md) - # Provenance contract for FC12 C10
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Appendix A. Surfaces in Positive Characteristic FC12](appendix-a-surfaces-in-positive-characteristic-fc12.md) - # Appendix A. Surfaces in Positive Characteristic FC12

* [Provenance contract for FC12 A](provenance-contract-for-fc12-a.md) - # Provenance contract for FC12 Appendix A
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Appendix B. Compact Complex Surfaces FC12](appendix-b-compact-complex-surfaces-fc12.md) - # Appendix B. Compact Complex Surfaces FC12

* [Provenance contract for FC12 B](provenance-contract-for-fc12-b.md) - # Provenance contract for FC12 Appendix B
* [Foundational corpus mapping FC12 Beauville](foundational-corpus-mapping-fc12-beauville.md) - # Foundational corpus mapping FC12 Beauville

* [Foundational corpus mapping FC14 Humphreys](foundational-corpus-mapping-fc14-humphreys.md) - # FC14 — Humphreys, *Introduction to Lie Algebras and Representation Theory* mapping

* [Chapter I. Basic Concepts FC14](chapter-i-basic-concepts-fc14.md) - # Chapter I. Basic Concepts FC14

* [Provenance contract for FC14 C01](provenance-contract-for-fc14-c01.md) - # Provenance contract for FC14 C01
* [Foundational corpus mapping FC14 Humphreys](foundational-corpus-mapping-fc14-humphreys.md) - # Foundational corpus mapping FC14 Humphreys
* [Foundational corpus mapping FC11 Peters Sterk](foundational-corpus-mapping-fc11-peters-sterk.md) - # FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping

* [Provenance contract for FC11 C01](provenance-contract-for-fc11-c01.md) - # Provenance contract for FC11 C01

* [Chapter 1. Symmetric and Quadratic Forms, an Overview FC11](chapter-1-symmetric-and-quadratic-forms-an-overview-fc11.md) - # Chapter 1. Symmetric and Quadratic Forms, an Overview FC11
* [Foundational corpus mapping FC11 Peters Sterk](foundational-corpus-mapping-fc11-peters-sterk.md) - # FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping

* [Provenance contract for FC11 C02](provenance-contract-for-fc11-c02.md) - # Provenance contract for FC11 C02

* [Chapter 2. Indefinite Unimodular Integral Lattices FC11](chapter-2-indefinite-unimodular-integral-lattices-fc11.md) - # Chapter 2. Indefinite Unimodular Integral Lattices FC11
* [Foundational corpus mapping FC11 Peters Sterk](foundational-corpus-mapping-fc11-peters-sterk.md) - # FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping

* [Provenance contract for FC11 C03](provenance-contract-for-fc11-c03.md) - # Provenance contract for FC11 C03

* [Chapter 3. Quadratic Forms over ℚ and ℚ_p FC11](chapter-3-quadratic-forms-over-q-and-q-p-fc11.md) - # Chapter 3. Quadratic Forms over ℚ and ℚ_p FC11
* [Foundational corpus mapping FC11 Peters Sterk](foundational-corpus-mapping-fc11-peters-sterk.md) - # FC11 — Peters–Sterk, *Symmetric and Quadratic Forms* mapping
* [Chapter 3. Rings and Modules of Fractions; Local Properties](chapter-3-rings-and-modules-of-fractions-local-properties.md) - | FC04 ID         | Verdict                                           | Route              | Lean target(s)                                                                                                                                                                                   | Provenance | Interface comparison                                                                                                                                                                                                                                          |
* [Chapter 5. Integral Dependence and Valuations](chapter-5-integral-dependence-and-valuations.md) - | FC04 ID         | Verdict                                            | Route              | Lean target(s)                                                                                                                                                                                           | Provenance    | Interface comparison                                                                                                                                                                                                                                                                                                   |
* [Chapter 1. Rings and ideals](chapter-1-rings-and-ideals.md) - ## Source and revision comparison
* [Provenance contract for C05](provenance-contract-for-c05.md) - - Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. Project HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966` owns the integrally-closed-domain and valuation-ring category wrappers used at U020 and U029; the remaining source-shaped results are delegated to Mathlib.
* [Foundational corpus units FC05 Weibel](foundational-corpus-units-fc05-weibel.md) - Corpus source: `FC05` in [[foundational-source-corpus|Foundational source corpus v1 (frozen)]].
* [Chapter 1. Chain Complexes FC05](chapter-1-chain-complexes-fc05.md) - # Chapter 1. Chain Complexes FC05
* [Provenance contract for FC05 C02](provenance-contract-for-fc05-c02.md) - # Provenance contract for FC05 C02
* [Provenance contract for FC05 C03](provenance-contract-for-fc05-c03.md) - # Provenance contract for FC05 C03
