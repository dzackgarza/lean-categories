---
type: reference
title: Provenance contract for FC08 CB
description: '# Provenance contract for FC08 Appendix B'
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
# Provenance contract for FC08 CB

# Provenance contract for FC08 Appendix B

- Canonical source block: FC08 Lee, Appendix B, `FC08-CB-U001`–`FC08-CB-U090`, exactly 90 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then indexed/current/external Lean search surfaces. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix B has 81 pinned `mathlib` rows and 9 dated `unmatched` rows. Positive rows are: U001, U003, U004, U005, U006, U007, U008, U009, U010, U011, U012, U013, U015, U016, U017, U018, U019, U020, U021, U022, U023, U024, U025, U026, U027, U028, U029, U030, U031, U032, U033, U034, U035, U036, U037, U038, U040, U041, U042, U043, U044, U046, U047, U048, U049, U050, U051, U053, U054, U055, U056, U057, U058, U060, U061, U062, U063, U064, U065, U066, U068, U069, U070, U071, U072, U073, U074, U075, U076, U077, U079, U080, U081, U083, U084, U085, U086, U087, U088, U089, U090.
- `/tmp/fc08-cb-witness.lean` compiles at exact P and checks the principal declaration surface used here: modules/submodules, span, convexity, linear independence, bases/finrank, quotients/projections, matrices/rank/determinants, inner-product/Gram–Schmidt APIs, bounded linear maps, products, and direct sums.
- The finite-dimensional linear-algebra layer is especially complete. Mathlib’s `Basis`, `finrank`, `LinearMap`, `LinearEquiv`, `Basis.toMatrix`, rank-nullity, matrix rank/transpose, determinant, adjugate/nonsingular inverse, and triangular/block-triangular APIs give direct owners for the standard statements rather than requiring local rederivations.
- Gram–Schmidt is also exact: `gramSchmidtBasis`, `gramSchmidtNormed_orthonormal`, and `span_gramSchmidt_Iic` give an orthonormal basis while preserving every initial span, matching Lee Proposition B.40 at source generality.
- The direct-product/direct-sum section maps to `LinearMap.pi`, `DirectSum.lof`, `DirectSum.toModule`, its uniqueness theorem, and `DirectSum.IsInternal`. Mathlib uses a finite-support dependent-function representation (`DFinsupp`) for external direct sums, mathematically equivalent to Lee’s finite-support submodule of the product.
- The nine unmatched rows are deliberately narrow. U002 and U052 are terminology only; U014/U059/U078 lack canonical bundled owners for Lee’s exact naming/predicate; U039 and U045 miss the exact general theorem statement; U067 bundles angle terminology not found canonically; U082 bundles Pi construction with an AC nonemptiness assertion. Adjacent ingredients were not promoted under strict whole-row semantics.
- Broad current GitHub/indexed searches found additional executable Gram–Schmidt projects, but none improves on the pinned Mathlib owner or supplies a missing whole-row route. No external package import was justified.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

