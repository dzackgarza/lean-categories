---
type: reference
title: Provenance contract for FC08 C21
description: '# Provenance contract for FC08 C21'
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
# Provenance contract for FC08 C21

# Provenance contract for FC08 C21

- Canonical block: `FC08-C21-U001`–`FC08-C21-U042`, exactly 42 unique contiguous rows.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), then indexed/current/external Lean search.
- Result: 7 pinned `mathlib` rows and 35 dated `unmatched` rows. Positives: U001, U002, U005, U006, U021, U029, U030.
- The topological action layer is strong: `MulAction.orbitRel` gives orbit equivalence/classes; the orbit quotient has the quotient topology and an open quotient map; `ProperSMul` is exactly Lee’s proper-action definition; and proper actions have Hausdorff orbit quotient. These own U001, U002, U005, U006.
- U021 is the exact underlying coset-space convention: `G ⧸ H` is the left-coset quotient, `leftRel_apply` gives `g₁⁻¹g₂ ∈ H`, and the topology is quotient topology.
- U029–U030 are exact abstract group theory: quotient by a normal subgroup, canonical surjection/kernel, and the first isomorphism theorem.
- Mathlib also contains useful proper-action compact-set results and topological quotient-covering machinery, but not Lee’s smooth quotient-manifold theorem/unique smooth structure/submersion. These are not promoted into U007–U018.
- No homogeneous-space quotient-manifold construction, Lie-group quotient theorem/first-isomorphism theorem, or Lie-correspondence classification was found. Connectivity searches likewise did not locate the bundled SO/U/SU/GL component results.
- `N=2026-09-07` marks negative decisions; strict whole-row semantics apply uniformly.
