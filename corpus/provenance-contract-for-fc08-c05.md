---
type: reference
title: Provenance contract for FC08 C05
description: '# Provenance contract for FC08 C05'
tags:
- project
- reference
timestamp: '2026-09-07T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC08 C05

# Provenance contract for FC08 C05

- Canonical source block: FC08 Lee, Chapter 5, `FC08-C05-U001`–`FC08-C05-U070`, exactly 70 unique contiguous rows from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]].
- The 2026-09-13 `remap-strict-bundle` pass uses clause-wise exact-route semantics. A missing named `Submanifold` wrapper is not a negative result: subset topology/manifold structures, inclusion embeddings/immersions, codimension, slices, regular-value predicates, tangent data, and boundary models are assembled from their actual Mathlib/reference owners. A row remains `unmatched` only when a substantive theorem/example clause is still unresolved.
- Current route totals are regenerated from the table: `mathlib` 28, `project-existing` 0, `package-import` 0, `reference-port` 3, `unmatched` 39; total 70.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`. Current Mathlib supplies `IsImmersion.injective_mfderiv` and the restriction/initiality theorems used in the tangent/restriction block, but the derivative-surjective submersion equivalence and finite-dimensional constant-rank/inverse-function bridges remain unresolved as recorded in Chapter 4.
- TauCeti `C=0d1c1bf4d2762c45533c6840a6bd764507ecf784` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`) was inspected at declaration level. `Boundary/Charts.lean` proves the boundary manifold and smooth embedding; `DerivationBundle.lean` proves the tangent-vector/point-derivation evaluation and naturality formulas; `Analysis/Fredholm/LevelSet/Basic.lean` gives genuine surjective-derivative level-set charts. The cited target files contain no `sorry`, `axiom`, or `admit`.
- The level-set block distinguishes direct terminology from theorem content. Regular-point/value definitions are native, but openness of the raw surjective-`mfderiv` locus, the full finite-dimensional constant-rank/regular-level-set theorem, and properly-embedded conclusions remain genuine gaps. TauCeti's Fredholm level-set implementation is recorded as partial/reference evidence rather than silently generalized.
- The embedded/immersed blocks now route direct definitions through subtype/manifold and inclusion-map data. Image-structure uniqueness, local slice criteria, local embeddedness of arbitrary immersed subsets, extension of functions, tangent-kernel characterizations, and the concrete figure-eight/dense-torus assertions remain `unmatched` where no checked theorem closes the source clause.
- The boundary block uses the proof-complete TauCeti boundary manifold/embedding where exact. Global boundary defining functions, sign characterization of inward/outward tangent vectors, regular-domain global defining functions/exhaustions, and arbitrary half-slice converse theorems remain scoped residual gaps.
- U063 remains a catalogue-data defect: the tracked source statement stops after the hypotheses of Proposition 5.47. No conclusion is invented. U064 therefore records the regular-sublevel theorem it explicitly attributes to U063 as unresolved even though its terminology is native.
- Live formalization-corpus and public/reference searches recorded in the mapping rows were used as discovery surfaces. Search errors/timeouts are never treated as negative evidence; only successfully inspected revisions support an `unmatched` residual.
