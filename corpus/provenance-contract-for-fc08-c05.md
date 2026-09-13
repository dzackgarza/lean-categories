---
type: reference
title: Provenance contract for FC08 C05
description: '# Provenance contract for FC08 C05'
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
# Provenance contract for FC08 C05

# Provenance contract for FC08 C05

- Canonical source block: FC08 Lee, Chapter 5, `FC08-C05-U001`–`FC08-C05-U070`, exactly 70 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted current/indexed/external Lean searches and local reference probes. No `mathlib`, `project-existing`, `package-import`, or `reference-port` C05 row survived strict whole-row checking.
- C05 therefore has 0 promoted rows and 70 dated `unmatched` rows. This is not a failure to find nearby manifold machinery: it records a specific missing abstraction boundary. At P, `Mathlib/Geometry/Manifold/SmoothEmbedding.lean` says its `IsSmoothEmbedding` map predicate “will be useful to define embedded submanifolds”; no embedded-submanifold definition is present. `IsManifold/InteriorBoundary.lean` explicitly lists “`boundary M` is a submanifold ... this requires a definition of submanifolds” as TODO. Current H still has no `Submanifold`, regular-value, or level-set manifold file/interface.
- The same boundary controls the immersed rows. `Immersion.lean` and `Submersion.lean` define map predicates by local normal forms, not Lee’s finite-dimensional injective/surjective differential definitions. At P both files state the finite-dimensional equivalence as future work. H adds differential-immersion infrastructure and one implication toward injective `mfderiv`, but no complete equivalence to `IsImmersion` and no parallel differential-submersion package. Therefore C05’s image-of-immersion, immersed-submanifold, local-parametrization, level-set, and restriction theorems cannot be routed through those map predicates without an unproved bridge.
- Several ingredients were checked and deliberately not promoted as whole rows: `IsSmoothEmbedding.of_opens` for open inclusions; `Topology.isEmbedding_graph` plus `ContMDiff.prodMk` for graph maps; proper-map/closed-embedding results; `ContMDiff.subtypeVal_comp_iff` for open subtypes; smooth sphere APIs; `TangentSpace`/`mfderiv`; and generic models with corners. Each owns only a proper subset or specialization of the corresponding C05 statement and does not construct the required submanifold topology/smooth structure.
- The level-set block U017–U027 was searched separately. P/H have no manifold `RegularPoint`, `RegularValue`, `RegularLevelSet`, or regular-value/submersion-level-set theorem. Thus even where generic preimage/singleton or linear rank-nullity primitives exist, there is no checked owner for Lee’s manifold-level definitions and codimension/proper-embedded conclusions.
- The boundary block U055–U070 was also searched separately. P/H expose `IsBoundaryPoint`, `boundary`, `interior`, local-diffeomorphism boundary preservation, interval/half-space models, and related chart APIs, but no inward/outward tangent-vector predicate, boundary defining function, regular domain, half-slice criterion, or general submanifold-with-boundary package.
- U063 has a separate canonical-source defect: its Sweep-I statement is truncated to `Suppose M is a smooth manifold and f ∈ C^∞(M).` with no conclusion. Sweep II leaves that canonical row unmatched rather than reconstructing a proposition from an external edition and thereby mutating Sweep-I content implicitly.
- Project-first search found no C05 submanifold implementation. `LeanCategories/ForMathlib/QuotientManifold.lean` from the preceding covering audit is a specialized quotient-manifold construction, not a submanifold package and does not close any C05 row.
- Targeted indexed GitHub searches for Lean formalizations of embedded/immersed submanifolds, regular level sets, and boundary defining functions returned no compatible general owner. A current TauCeti roadmap result independently describes embedded-submanifold infrastructure as absent from Mathlib, consistent with the checked source-tree evidence; this secondary evidence was not used in place of direct revision inspection.
- `N=2026-09-07` marks a dated unmatched decision after the prescribed search layers. Strict whole-row semantics apply uniformly.
