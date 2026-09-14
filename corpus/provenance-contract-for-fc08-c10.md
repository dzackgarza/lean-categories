---
type: reference
title: Provenance contract for FC08 C10
description: '# Provenance contract for FC08 C10'
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
# Provenance contract for FC08 C10

- Canonical source block: FC08 Lee, Chapter 10, `FC08-C10-U001`–`FC08-C10-U055`, exactly 55 unique catalogue rows.
- The 2026-09-14 `remap-strict-bundle` pass uses clause-wise exact-route semantics. Missing names such as `BundleHom`, `Subbundle`, or `SmoothFiberBundle` are not negative evidence when Lee's definition is exactly a conjunction of existing bundle, smoothness, linearity, embedding, or trivialization predicates.
- Current route totals regenerated from the table are `mathlib` 39, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 16; total 55. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`.
- Current Mathlib has substantially more bundle infrastructure than the original 2026-09-07 audit credited. `VectorPrebundle.totalSpaceTopology`, `toFiberBundle`, `toVectorBundle`, `VectorPrebundle.IsContMDiff`, and `contMDiffVectorBundle` implement Lee's vector-bundle chart construction. Pullback smooth-vector-bundle instances implement restriction. `FiberBundle.isOpenMap_proj`, `surjective_proj`, and `isQuotientMap_proj` settle the base-map topology in bundle homomorphisms.
- Current `Geometry/Manifold/VectorBundle/Hom.lean` and `Topology/VectorBundle/Hom.lean` construct the bundle of continuous linear maps and provide smooth application lemmas for smoothly varying fiber maps. Together with `ContMDiffSection`, `ContMDiff.smul_section`, and the tangent-map API, this routes Lee's definitions and examples of bundle homomorphisms and their induced operators on sections without inventing a wrapper structure.
- `FiberBundle.exists_contMDiffOn_extend` and `contMDiffAt_extend` now give a smooth local section through every prescribed fiber vector. This is strong input for Lee's section-extension and section-operator characterization theorems, but no checked source performs the support-controlled relative gluing of U022 or reconstructs a smooth fiber map from an arbitrary `C∞(M)`-linear operator on global sections in U042; those remain substantive residuals.
- `LocalFrame.lean` provides frames arising from trivializations, coefficients/reconstruction, and the coefficient-to-section smoothness direction. Its current API still lacks the fully frame-intrinsic converse needed to turn an arbitrary smooth frame into a smooth trivialization and to prove the section-to-coefficient smoothness direction. Accordingly U028–U033 remain unmatched exactly where that bridge is used; U023 is only the native frame definition.
- Live formalization-corpus/API searches were refreshed for Möbius bundles, section extension, frame completion, frame/trivialization, smooth inverse bundle maps, section-operator characterizations, subbundles, constant-rank kernels/images, orthogonal complements, and smooth fiber bundles. No general checked owner was found for U007, U022, U024, U038, U042, U046, U049, or U050. The apparent `Moebius` hits were Möbius transformations; the apparent homomorphism hits were unrelated specialized files. Search failures/timeouts are not used as negative evidence.
- The subbundle block is separated similarly. The definition U045 is exactly a dependent family of linear subspaces equipped with vector/smooth-vector-bundle data and a smooth embedded inclusion, while the local-frame criterion U046, the general tangent-subbundle example U047(c), constant-rank kernel/image theorem U049, orthogonal-complement theorem U050, and normal-bundle corollary U051 remain theorem-level gaps. The live orthogonal-complement hit in Atlas merely postulates a tangent splitting and is not an implementation of Lee's theorem.
- U053–U054 are direct refinements of Mathlib's topological `FiberBundle`/`Trivialization` data by smooth-manifold and smooth-map predicates. U055 remains unmatched only on the explicit Möbius interval-bundle/nontriviality clause; product bundles, vector bundles, and covering maps already realize its other examples.
