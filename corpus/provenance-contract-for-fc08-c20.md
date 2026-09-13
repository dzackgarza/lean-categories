---
type: reference
title: Provenance contract for FC08 C20
description: '# Provenance contract for FC08 C20'
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
# Provenance contract for FC08 C20

# Provenance contract for FC08 C20

- Canonical block: `FC08-C20-U001`–`FC08-C20-U034`, exactly 34 unique contiguous rows.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), then indexed/current/external Lean search.
- Result: 2 pinned `mathlib` rows (U029, U032) and 32 dated `unmatched` rows.
- U029 maps exactly to `LieIdeal` and its bracket-closure theorem. U032 maps exactly to the Lie algebra homomorphism `LieAlgebra.ad : g →ₗ⁅R⁆ End(g)` with `ad_apply`.
- P/H contain Lie groups, left-invariant vector fields, manifold Lie brackets, smooth actions, matrix exponentials, and abstract Lie algebra infrastructure, but targeted searches found no Lie-group exponential/one-parameter subgroup object, no closed subgroup theorem, no Lie correspondence/integration of Lie algebra actions, and no group adjoint representation differentiated to `ad`.
- Accordingly the matrix-exponential rows are not promoted through a missing identification with Lee’s Lie-group exponential, and group-level adjoint/normal-subgroup rows are not inferred from the algebraic `ad`/`LieIdeal` objects.
- `N=2026-09-07` marks negative decisions; strict whole-row semantics apply uniformly.

