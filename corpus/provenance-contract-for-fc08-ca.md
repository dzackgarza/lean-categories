---
type: reference
title: Provenance contract for FC08 CA
description: '# Provenance contract for FC08 Appendix A'
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
# Provenance contract for FC08 CA

# Provenance contract for FC08 Appendix A

- Canonical source block: FC08 Lee, Appendix A, `FC08-CA-U001`–`FC08-CA-U101`, exactly 101 unique contiguous rows from the canonical FC08 unit catalogue.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), then indexed/current/external Lean search. Existing FC02/FC07 topology mappings were used only as search leads; every cited Mathlib file was revalidated at exact P before promotion.
- Result: 54 pinned `mathlib` rows and 47 dated `unmatched` rows. Positive IDs: U001, U002, U004, U005, U007, U008, U010, U011, U012, U014, U015, U016, U017, U018, U019, U020, U021, U022, U025, U029, U030, U031, U032, U033, U038, U039, U040, U042, U047, U049, U051, U056, U060, U061, U063, U065, U067, U069, U070, U075, U076, U077, U078, U080, U081, U082, U083, U084, U085, U088, U093, U096, U097, U101.
- The strongest direct matches are native topology/metric/basis/subspace/quotient definitions, the exact `CompactExhaustion` structure and construction, native homotopy/path-class/fundamental-group objects, and the pinned covering lifting criterion.
- Lee’s special “neighborhood = open neighborhood” convention is not conflated with Mathlib’s generic neighborhood-filter membership. `nhds_basis_opens` is used only where an open-neighborhood basis itself is the source object.
- Large bundled propositions (subspace/product/disjoint-union/quotient/connectedness/compactness properties) remain unmatched when Mathlib only supplies the clauses separately. Likewise Lee’s definition of a proper map allows discontinuous maps, whereas Mathlib `IsProperMap` includes continuity; U073 is therefore not identified with it. U077 is mapped only because the source assumes continuity and a locally compact Hausdorff target, so the compact-preimage characterization bridges to `IsProperMap`.
- FC07’s TauCeti reference-port evidence was reconsidered for U098–U100, but no short compatible bridge from Lee’s locally-simply-connected convention to the later package’s universal-cover hypotheses plus the full uniqueness statement was found; these rows remain unmatched rather than silently changing hypotheses.
- `N=2026-09-07` marks all negative decisions; strict whole-row semantics apply uniformly.
