---
type: reference
title: Provenance contract for FC08 C16
description: '# Provenance contract for FC08 C16'
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
# Provenance contract for FC08 C16

# Provenance contract for FC08 C16

- Canonical source block: FC08 Lee, Chapter 16, `FC08-C16-U001`–`FC08-C16-U066`, exactly 66 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/GitHub/external Lean searches. No `project-existing`, `package-import`, or `reference-port` owner survived strict whole-row checking.
- C16 has 1 pinned `mathlib` row and 65 dated `unmatched` rows. The sole positive row is U023.
- U023 is exact: `EuclideanQuadrant n` is the nonnegative coordinate orthant, `range_euclideanQuadrant` identifies its image with `∀ i, 0 ≤ y i`, and `modelWithCornersEuclideanQuadrant` supplies the standard corners model.
- P/H do contain strong adjacent analytic infrastructure: Lebesgue/Bochner integration, the Jacobian change-of-variables theorem (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`), Henstock–Kurzweil box integration and a box divergence theorem, Haar measures, and general `ModelWithCorners`. None supplies Lee’s smooth oriented-manifold differential-form integral, its Stokes theorem, or the smooth density-bundle interface, so these ingredients are not promoted across a missing bridge.
- C14 already established the central differential-form boundary: Mathlib has vector-space `AlternatingMap` forms and a continuous alternating-map bundle, but no smooth manifold `DifferentialForm` section/exterior-derivative layer. C15 additionally established the absence of a global smooth-manifold orientation API. C16 U001–U022 and U035–U046 depend essentially on those missing layers.
- Mathlib’s manifold framework can use Euclidean quadrants as models with corners, but targeted searches found no corner-depth/stratification API matching Lee’s “more than one vanishing coordinate” corner points, no chart-invariance theorem for that notion, and no integration/Stokes theorem over corner faces. Hence U024–U034 remain unmatched despite U023.
- Exact P/H searches for `Density` find only unrelated combinatorial/measure-theoretic uses; there is no linear determinant-density object, density bundle, or Riemannian density in Lee’s sense. `Measure.withDensity` is a Radon–Nikodym-style measure construction, not the source object. Thus U047–U066 are not identified with measure densities by terminology alone.
- Targeted current external search found no compatible Mathlib-based implementation of the missing manifold integration/density layer. A current pure-Lean mathematical-physics project advertises differential forms/de Rham theory but deliberately has no Mathlib dependency and axiomatizes substantial analytic scaffolding; it does not satisfy the evidence/compatibility floor for `package-import` or `reference-port` here.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

