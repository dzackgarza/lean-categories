---
type: reference
title: Provenance contract for FC08 C17
description: '# Provenance contract for FC08 C17'
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
# Provenance contract for FC08 C17

# Provenance contract for FC08 C17

- Canonical source block: FC08 Lee, Chapter 17, `FC08-C17-U001`–`FC08-C17-U056`, exactly 56 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/current/external Lean searches.
- C17 has 9 pinned `mathlib` rows and 47 dated `unmatched` rows. Positive rows are: U017, U026, U027, U047, U049, U052, U053, U054, U055.
- The geometric de Rham layer is absent at P/H. Current Mathlib documentation exposes manifold vector fields, Riemannian geometry, smooth sections, and algebraic homological/cohomological complexes but no manifold de Rham cohomology module. A targeted current GitHub search likewise did not identify a compatible Mathlib-based de Rham implementation meeting the evidence floor.
- U017 is independent of differential forms: `contractible_iff_id_nullhomotopic` is exactly Lee’s definition of contractibility as identity homotopic to a constant map.
- U026–U027 are algebraic exactness and are owned directly by `Function.Exact` / `moduleCat_exact_iff_range_eq_ker`.
- U047, U049, U052–U055 are generic homological algebra. Mathlib explicitly distinguishes `CochainComplex` (differentials increase degree) from `ChainComplex` (decrease degree), defines homology/cohomology as cycles modulo boundaries, gives induced homology maps, characterizes short exact complexes degreewise, and constructs the connecting morphism and long exact homology sequence. These rows therefore map without any de Rham bridge.
- U048 remains unmatched despite adjacent exactness/complex APIs because its complete source bundle includes the strict non-converse “complex need not be exact”; no checked single owner packages that assertion, and a new counterexample would be reconstruction rather than reuse.
- U046 was checked separately. P/H/current Mathlib contains Banach contraction fixed-point theory and one-dimensional interval fixed-point results, but no arbitrary-dimensional Brouwer closed-ball fixed-point theorem.
- All remaining geometric rows depend essentially on the missing manifold de Rham complex, integration layer, or orientation-covering/degree machinery established absent in C14–C16; generic topological homotopy or algebraic complex infrastructure is not promoted through that gap.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

