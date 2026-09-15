---
type: reference
title: Foundational corpus mapping FC17 Kerodon
description: '# Foundational corpus mapping FC17 Kerodon'
tags:
- project
- reference
timestamp: '2026-09-14T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# FC17 — Kerodon mapping

Canonical catalogue: [[foundational-corpus-units-fc17-kerodon|FC17 — Kerodon]].

Status: **Sweep II open.** The catalogue is complete for the pinned FC17 Kerodon
snapshot, but no unit is cleared for new authorship merely by appearing here.

## Search contract

For every FC17 unit, read the authoritative source statement at its permanent
Kerodon tag before accepting a route. Search pinned/current Mathlib first, then
query the live [Formalization Corpus](https://dzackgarza.github.io/formalization-corpus/)
API as a first-class discovery source, using several mathematically distinct
formulations rather than one literal phrase. The repository client is:

```sh
python scripts/formalization_corpus.py search 'quasicategory inner horn'
python scripts/formalization_corpus.py search 'inner anodyne extension'
python scripts/formalization_corpus.py list 'repo:mathlib4'
```

The service contract is the live OpenAPI document linked by the
[API reference](https://dzackgarza.github.io/formalization-corpus/api.html); that
document, rather than this repository, owns paths, methods, and schemas. Search
results are discovery evidence, not final provenance: open the returned upstream declaration and record its exact
repository/revision/path/name/license/toolchain plus the mathematical comparison
to the full Kerodon obligation.

An `unmatched` route requires the complete negative-search stopping rule in
`AGENTS.md`, including the Formalization Corpus API under multiple source names,
standard synonyms, expected declaration/type fragments, and nearby constructions.
An API outage cannot support `unmatched`.

## Canonical row schema

Append one row per source-unit ID as Mapping proceeds. `Route` is exactly one of
`mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`.
The `Formalization Corpus queries` cell records the dated query batch actually
used; plausible hits are followed to their upstream source before a positive
route is accepted.

| ID | Verdict | Route | Lean target(s) | Provenance | Formalization Corpus queries | Interface comparison |
| --- | --- | --- | --- | --- | --- | --- |
| `FC17-KER-U00010` | exact pinned notation/object constructor for `[n]` | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean::SimplexCategory.mk`; scoped notation `⦋n⦌` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `0009` read 2026-09-15 | source-enriched batch: `[n] linearly ordered set`; pinned source inspection | Kerodon fixes `[n]={0<…<n}`. Mathlib's `SimplexCategory.mk n` has underlying ordered type `Fin (n+1)` and the project notation `⦋n⦌`; no new mathematical object is required. |
| `FC17-KER-U00011` | exact pinned simplex category | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean::SimplexCategory`; `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean::SimplexCategory.mkHom` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `000A` read 2026-09-15 | `Simplex Category`; live corpus also returned `emilyriehl/infinity-cosmos` and Mathlib consumers | Objects are finite ordinals `[n]`; morphisms are monotone maps, exactly Kerodon's `Δ`. `mkHom` exposes the same monotone-map presentation. |
| `FC17-KER-U00013` | exact pinned simplicial and cosimplicial object definitions | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean::CategoryTheory.SimplicialObject`, `CategoryTheory.CosimplicialObject` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `000C` read 2026-09-15 | source-enriched batch: `simplicial object cosimplicial object` | Mathlib defines these literally as functors `SimplexCategoryᵒᵖ ⥤ C` and `SimplexCategory ⥤ C`, matching the complete Kerodon definition. |
| `FC17-KER-U00014` | exact pinned evaluation notation | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`; scoped notations `X _⦋n⦌`, `X ^⦋n⦌` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `000D` read 2026-09-15 | source-enriched batch from the notation statement | Kerodon writes `C_n` and `C^n` for evaluation on `[n]`. Mathlib's scoped notations are exactly those evaluations for simplicial and cosimplicial objects. |
| `FC17-KER-U00018` | exact pinned simplicial-set definition | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean::SSet` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `000H` read 2026-09-15 | source-enriched batch: `simplicial set Sets`; live corpus returned UniMath and Lean hits | `SSet` is definitionally `SimplicialObject (Type u)`, hence a presheaf `Δᵒᵖ ⥤ Type`, exactly the source definition up to Lean's universe of sets. |
| `FC17-KER-U05752` | exact pinned category of simplicial sets | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean::SSet` with its functor-category `Category` instance | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `04Z5` read 2026-09-15 | source-enriched batch: `category simplicial sets` | Kerodon's `Set_Δ = Fun(Δᵒᵖ,Set)` is precisely Mathlib's functor-category abbreviation `SSet`; the ambient category structure is inherited from the functor category. |
| `FC17-KER-U05759` | exact pinned injective simplex category | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean::SemiSimplexCategory`, `SemiSimplexCategory.Hom`, `toSimplexCategory` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `04ZC` read 2026-09-15 | source-enriched batch: `strictly increasing Simplicial Sets` | Objects are `[n]` and morphisms are order embeddings `Fin(n+1) ↪o Fin(m+1)`, exactly Kerodon's `Δ_inj`; `toSimplexCategory` is its inclusion into `Δ`. |
| `FC17-KER-U05760` | exact pinned generic semisimplicial-object expression | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean::SemiSimplexCategory`; object type `SemiSimplexCategoryᵒᵖ ⥤ C` and set-valued specialization | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `04ZD` read 2026-09-15 | source-enriched batch: `semisimplicial object semisimplicial set` | Kerodon's definition contains no structure beyond a functor out of `Δ_injᵒᵖ`. Mathlib owns the indexing category and generic functor category, so the source object is the literal type expression; a project wrapper would add no mathematics. |
| `FC17-KER-U05761` | exact pinned face operators | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean::SimplexCategory.δ`; `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean::SimplicialObject.δ` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `04ZE` read 2026-09-15 | `Face Operators`; source-enriched `i-th face operator` | Mathlib's `δ i : ⦋n⦌ ⟶ ⦋n+1⦌` omits vertex `i`, and `X.δ i` is its contravariant image, exactly Kerodon's coface and face maps. |
| `FC17-KER-U05766` | exact pinned degeneracy operators | `mathlib` | `Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean::SimplexCategory.σ`; `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean::SimplicialObject.σ` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `04ZK` read 2026-09-15 | `Degeneracy Operators`; source-enriched `i-th degeneracy operator` | Mathlib's `σ i : ⦋n+1⦌ ⟶ ⦋n⦌` is the standard monotone surjection identifying `i,i+1`, and `X.σ i` is its simplicial image, exactly the source construction. |
| `FC17-KER-U00037` | exact pinned degenerate/nondegenerate simplex predicates | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean::SSet.degenerate`, `SSet.nonDegenerate`, `degenerate_eq_iUnion_range_σ` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `0012` read 2026-09-15 | source-enriched batch: `degenerate nondegenerate` | Mathlib defines degenerate simplices as precisely those in the union of degeneracy-map ranges and nondegenerate simplices as the complement; degree zero is proved nondegenerate, matching all definition clauses. |
| `FC17-KER-U00029` | exact pinned horn construction | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialSet/Horn.lean::SSet.horn`, scoped notation `Λ[n, i]`, `horn_eq_iSup` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; Kerodon tag `000U` read 2026-09-15 | source-enriched batch: `Horn Lambda`; live corpus also returned `emilyriehl/infinity-cosmos` | `SSet.horn n i` is the subcomplex of `Δ[n]` whose simplices miss a vertex other than `i`; `horn_eq_iSup` identifies it with the union of all codimension-one faces except the `i`th face. This is exactly Kerodon's `i`th horn, with the same `Λ[n,i]` notation. |
| `FC17-KER-U00113` | exact pinned quasicategory definition | `mathlib` | `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean::SSet.Quasicategory` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 003A]`; Kerodon tag `003A` read 2026-09-15 | source-enriched batch: `∞-category quasicategory inner horn`; pinned Kerodon cross-reference | Mathlib's horn-filling class requires fillers for every inner horn `Λ[n,i] → S`, exactly Kerodon's definition of an `∞`-category. The source tag is attached directly to the declaration. |
| `FC17-KER-U01541` | exact pinned inner-fibration definition | `mathlib` | `Mathlib/AlgebraicTopology/Quasicategory/InnerFibration.lean::SSet.innerFibrations`, `SSet.InnerFibration` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 01BA]`; Kerodon tag `01BA` read 2026-09-15 | source-enriched batch: `inner fibration`; pinned Kerodon cross-reference | `innerFibrations` is the right lifting property against inner horn inclusions, and `InnerFibration q` is membership in that morphism property. This is the source lifting condition verbatim. |
| `FC17-KER-U03043` | exact pinned nonsingular-simplicial-set definition | `mathlib` | `Mathlib/AlgebraicTopology/SimplicialSet/Nonsingular.lean::SSet.Nonsingular` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 02MG]`; Kerodon tag `02MG` read 2026-09-15 | source-enriched batch: `nonsingular simplicial set`; pinned Kerodon cross-reference | Mathlib requires the simplex map `Δ[n] ⟶ X` associated to every nondegenerate simplex to be mono, exactly Kerodon's nonsingularity condition. |
| `FC17-KER-U00331` | exact pinned locally-groupoidal bicategory / source `2`-category predicate | `mathlib` | `Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean::CategoryTheory.Bicategory.IsLocallyGroupoid` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 009Q]`; Kerodon tag `009Q` read 2026-09-15 | source-enriched batch from `2-category`; pinned Kerodon cross-reference | Kerodon calls a bicategory a `2`-category here when every 2-morphism is invertible. Mathlib's `IsLocallyGroupoid` says precisely that every hom-category is a groupoid, hence every 2-cell is invertible. |
| `FC17-KER-U00361` | exact pinned pith construction | `mathlib` | `Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean::CategoryTheory.Bicategory.Pith` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 00AL]`; Kerodon tag `00AL` read 2026-09-15 | source-enriched batch: `pith bicategory`; pinned Kerodon cross-reference | Mathlib's wrapper keeps the objects and 1-morphisms of the bicategory and replaces each hom-category by its core, exactly discarding noninvertible 2-cells as in Kerodon's pith. |
| `FC17-KER-U00290` | exact pinned strict-functor data for bicategories | `mathlib` | `Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean::CategoryTheory.StrictPseudofunctor` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 008H]`; Kerodon tag `008H` read 2026-09-15 | source-enriched batch: `strict functor bicategory`; pinned Kerodon cross-reference | Mathlib's structure is a pseudofunctor whose identity and composition constraints are definitional equality transports, i.e. the strict preservation data and laws in Kerodon's strict-functor definition. |
| `FC17-KER-U00298` | exact pinned strictly-unital lax-functor definition | `mathlib` | `Mathlib/CategoryTheory/Bicategory/Functor/StrictlyUnitary.lean::CategoryTheory.StrictlyUnitaryLaxFunctor` | P=`db584cd6d46c92f209a44c0f1c829460d327499d`; explicit `@[kerodon 008R]`; Kerodon tag `008R` read 2026-09-15 | source-enriched batch: `unital strictly unital lax functor`; pinned Kerodon cross-reference | Kerodon's condition is that every identity constraint is an identity 2-morphism. Mathlib imposes exactly `map (𝟙 X) = 𝟙 (obj X)` and identifies `mapId` with the corresponding equality morphism. |
