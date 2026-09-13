---
type: reference
title: Provenance contract for FC08 C18
description: '# Provenance contract for FC08 C18'
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
# Provenance contract for FC08 C18

# Provenance contract for FC08 C18

- Canonical source block: FC08 Lee, Chapter 18, `FC08-C18-U001`–`FC08-C18-U025`, exactly 25 unique contiguous rows from the canonical FC08 unit catalogue.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), then indexed/current/external Lean searches.
- C18 has 6 pinned `mathlib` rows and 19 dated `unmatched` rows. Positives: U003, U006, U007, U008, U009, U019.
- U003 and U006–U009 are owned by Mathlib’s singular-simplicial-set/singular-chain-complex implementation: continuous standard-simplex maps, free chain objects, alternating face differential, square-zero boundary, cycles, and homology.
- U001–U002 and U004–U005 were not promoted merely because adjacent standard-simplex/face APIs exist: Lee’s rows bundle explicit affine Euclidean simplex geometry and uniqueness/face data not owned by one checked interface.
- U010 is deliberately not assembled from separate point-homology and homotopy-invariance results because its arbitrary coproduct clause lacks a checked complete theorem.
- No singular-homology Mayer–Vietoris theorem or singular-cohomology functor matching Lee’s real-coefficient convention was found at P/H/current external search, so U011–U014 remain unmatched.
- Smooth singular homology/smoothing of simplices (U015–U018) is not present. U019 is independent algebra and maps to Mathlib’s stronger categorical five lemma.
- U020–U025 require the missing manifold differential-form integration/de Rham comparison infrastructure identified in C14–C17 and remain unmatched.
- `N=2026-09-07` marks negative decisions; strict whole-row semantics apply uniformly.

