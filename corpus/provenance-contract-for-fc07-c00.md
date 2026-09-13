---
type: reference
title: Provenance contract for FC07 C00
description: '# Provenance contract for FC07 C00'
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
# Provenance contract for FC07 C00

# Provenance contract for FC07 C00

- Canonical source block: FC07 Hatcher, Chapter 0, `FC07-C00-U001`–`FC07-C00-U041`, in canonical source-ID order, extracted from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`. The extraction contains exactly 41 contiguous rows. FC01–FC06 were left closed and no FC13 scratch or vault record was touched.
- Project-first inspection was refreshed at repository HEAD `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. No project-owned declaration in `LeanCategories/**` owns a complete C00 source row, so no `project-existing` route is promoted.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every `mathlib` declaration promoted in the table was inspected at that exact revision.
- Current upstream Mathlib was refreshed on 2026-09-06 at `H=633b366493a76df88a2bff099ed0cbf711a59ec9`, Lean 4.34.0-rc2, Apache-2.0. Searches at H and in current open Mathlib PRs found ongoing classical-CW infrastructure work but no post-pin route completing the missing suspension/smash/mapping-cone, product/quotient-CW, or HEP proposition bundles.
- `deancureton/sphere-six-complex@895c0a0661501581c34d42fea3c553d4f0ee43b1` is Apache-2.0 and uses Lean 4.34.0-rc1. It contains exact general-topology implementations of strong deformation retractions, mapping cylinders/pushout homotopies, HEP, and Hatcher Cor. 0.20. Because it is not the project pin and no direct package-compatibility import test against Lean 4.33.0 was established, all promoted uses are `reference-port`, not `package-import`.
- `Vilin97/lean-pool@3fc79f0a795f19fffcc59eee3efaf5faa52de3c3` was inspected as a Reservoir/local reference source. Its Whitehead/HEP development has a target-specific HEP interface and supplies adjacent evidence but no stricter route than the promoted sphere-six declarations. `facebookresearch/atlas-lean@34ffed396f376454c1a9b297f3fd74c5c801fb50` was also checked for its deformation-retract interface; it uses Lean 4.29.0 and a noncommercial/no-training license, and no C00 row depends on it.
- Indexed/search-service probes (Mathlib docs, Loogle/LeanSearch-oriented searches, Reservoir/package search, GitHub-wide Lean search, and local reference-corpus scans) were used for the remaining gaps. Generic category-theoretic cones, joins, pushouts, and homological mapping cones were not conflated with Hatcher’s topological constructions.
- Strict bundle semantics govern every row. A route must own the complete stable-ID statement. A theorem for only one clause, one example, a specialization, or a semantically adjacent object is retained as adjacent evidence but does not promote the row.
- U008 is deliberately unmatched despite Mathlib’s `CWComplex`/`RelCWComplex` characteristic-map interface, skeletons, and skeleton-union theorems: the source row specifically gives the inductive discrete-0-skeleton/successive-cell-attachment construction, and no checked theorem bridges the complete source construction to the current classical-CW presentation.
- U009 is likewise not inferred from `CWComplex.OneSkeletonGraph`: that declaration extracts a combinatorial graph from the 1-skeleton, but the checked API does not identify an arbitrary one-dimensional CW complex with a topological graph realization as the source example states.
- U015 and U016 are promoted because Mathlib’s characteristic-map and subcomplex interfaces are direct equivalent representations rather than weaker consequences: closed-ball characteristic maps restrict to homeomorphisms on open cells, and subcomplexes are closed unions of cells with an induced CW structure.
- U028 is represented exactly by the topological pushout: the underlying type pushout is explicitly the quotient of the disjoint union by the attachment relation, and `TopCat.colimit_topology` equips it with the final topology.
- U036 remains unmatched even though `hasHomotopyExtensionProperty_of_relativeCWComplex_proved` proves its HEP consequence. The external proof constructs an ordinary retraction of the L-shaped cylinder and explicitly does not establish the stronger deformation-retract clause bundled into Hatcher Prop. 0.16.
- U040 is the exact external Cor. 0.20 theorem and returns the stronger stationary (strong) deformation retraction. U037–U039 remain unmatched because no searched declaration owns their respective quotient-collapse, homotopic-attachment, or relative-homotopy-equivalence statements in full.
- U041 remains unmatched under whole-row semantics: the external mapping-cylinder/HEP/strong-deformation-retract API supplies ingredients and directions, but no checked declaration packages both Hatcher’s iff and the common-ambient-space characterization.
- `N=2026-09-06` marks a dated unmatched decision after project-first, P, H/current/open work, indexed search services, Reservoir/local reference sources and relevant external Lean repositories.

