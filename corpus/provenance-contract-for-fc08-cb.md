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
# Provenance contract for FC08 Appendix B

- Canonical source block: FC08 Lee, Appendix B, `FC08-CB-U001`–`FC08-CB-U090`, exactly 90 unique catalogue rows.
- The 2026-09-14 exact-route remap replaces the obsolete strict-whole-row audit. Current totals are `mathlib` 88, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 2.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was checked at `H=7f22e856c19eeabc38d75733b71d7e44167307f3`. The standard finite-dimensional linear algebra, determinant, inner-product, norm, product, and direct-sum layers are direct Mathlib routes.
- Seven former negatives were artifacts of demanding a named wrapper for textbook terminology. U002 is terminology on `Module`; U014 is quotient-finrank codimension; U052 is native row/column update/permutation operations; U059 is determinant of a deleted-row/deleted-column submatrix and its signed cofactor; U067 is exactly `InnerProductGeometry.angle`; U078 is the direct two-sided positive-bound predicate for norms, with finite-dimensional equivalence supplied by continuity of identity maps; U082 is the dependent Pi type together with `Classical.nonempty_pi`.
- Two theorem rows remain unmatched after pinned/current source search. U039 asks for the rectangular canonical rank form for an arbitrary linear map `V → W`; `Matrix.exists_rank_normal_form` is only square, and obtaining the source form requires authoring bases adapted to kernel/range. U045 asks for the iff between `rank A ≥ k` and existence of a nonsingular `k×k` minor; Mathlib has `Matrix.rank_submatrix_le` and the determinant/full-rank direction, but no checked converse producing the minor.
- No external route is needed for the positive rows, and no weaker/specialized external theorem was substituted for U039 or U045. Negative claims are scoped to the inspected pinned/current sources.
