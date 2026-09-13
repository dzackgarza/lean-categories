---
type: reference
title: Provenance contract for FC08 C04
description: '# Provenance contract for FC08 C04'
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
# Provenance contract for FC08 C04

# Provenance contract for FC08 C04

- Canonical source block: FC08 Lee, Chapter 4, `FC08-C04-U001`–`FC08-C04-U041`, exactly 41 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- The chapter title is *Submersions, Immersions, and Embeddings* in Lee’s second edition. Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted current/indexed/external Lean searches and local project/reference probes. No `project-existing`, `package-import`, or `reference-port` C04 owner survived strict whole-row checking.
- Every promoted Mathlib path exists at exact `P`. `/tmp/fc08-c04-witness.lean` compiled the strict form of Lee’s U021 Dirichlet bound from `exists_int_int_abs_mul_sub_le` and checked the exact Kronecker-delta formula used for U012. `/tmp/fc08-c04-sphere.lean` compiled U023’s smooth sphere inclusion, injective manifold derivative, topological embedding, and compactness ingredients. These witnesses are audit evidence only, not project source.
- C04 has 4 pinned `mathlib` rows and 37 dated `unmatched` rows. Positive rows are: U006, U012, U021, U023.
- The controlling semantic issue is explicit in pinned `Immersion.lean` and `Submersion.lean`: Mathlib defines immersions/submersions by local normal forms, while Lee C04 defines them by injectivity/surjectivity of the differential. At `P`, both files say the finite-dimensional equivalence is future work. Current `H` adds `ImmersionDiff.lean` and proves local-normal-form immersion implies injective `mfderiv`, plus that injectivity yields a split differential in finite dimensions, but it still does not prove the converse to `IsImmersion`; there is no parallel differential-submersion file/equivalence. Consequently none of U003–U005, U009, U015–U017, U022, U024, or U028–U033 is credited through an unproved bridge.
- The manifold inverse/rank theorems are also genuinely absent from the checked interface. `LocalDiffeomorph.lean` at both `P` and `H` leaves “invertible `mfderiv` implies local diffeomorphism” as TODO, so U007 cannot be inferred from the Banach-space inverse function theorem. No checked manifold constant-rank/rank theorem was found for U011–U014, and the boundary normal form U015 is likewise absent.
- U006 is direct from `IsLocalDiffeomorphAt`/`IsLocalDiffeomorph`: the witness is a smooth equivalence between open neighborhoods. U012 is Mathlib’s identity-matrix entry formula `Matrix.one_apply`. U021 is a strict corollary of the stronger pinned Dirichlet bound and was compiled. U023 is a specialized existing formalization: `Instances/Sphere.lean` proves both smoothness and injectivity of the sphere inclusion derivative, while generic topology/compactness APIs supply the topological embedding and compact domain.
- U008 is not promoted despite substantial local-diffeomorphism coverage: P has composition, local-homeomorphism/open-map consequences, diffeomorphisms as local diffeomorphisms, and bijective local diffeomorphisms as diffeomorphisms, but the complete seven-clause source bundle was not found. Similarly, U035–U041 are not inferred from topological covering APIs: Mathlib’s `IsCoveringMap` is topological and explicitly allows nonsurjective coverings, while Lee’s smooth-covering predicate additionally requires smooth/diffeomorphic sheets and connected/surjective hypotheses.
- Project-first search found only the specialized `LeanCategories/ForMathlib/QuotientManifold.lean`, where a discrete-subgroup quotient is given a manifold structure using local sections of a quotient covering. It is useful adjacent evidence for U038 but is a proper specialization, not the general covering-space smooth-structure theorem. The project source remained unmodified.
- Targeted indexed searches for Lean formalizations of the manifold rank theorem, smooth-submersion local sections/descent, smooth covering maps, and proper-local-diffeomorphism covering theorems found no compatible general owner beyond the checked Mathlib/topological ingredients. Current upstream was inspected by git object without changing the pinned worktree.
- `N=2026-09-07` denotes a dated unmatched decision after the prescribed search layers. Strict whole-row semantics apply uniformly.
