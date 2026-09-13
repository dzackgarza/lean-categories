---
type: reference
title: Provenance contract for FC07 CA
description: '# Provenance contract for FC07 CA'
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
# Provenance contract for FC07 CA

# Provenance contract for FC07 CA

- Canonical source block: FC07 Hatcher Appendix, `FC07-CA-U001`–`FC07-CA-U032`, exactly 32 unique contiguous rows retrieved from [[foundational-corpus-units-fc07-hatcher|FC07 — Hatcher, Algebraic Topology]] through `agent-memory`.
- Search order followed the established FC07 contract: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=80cbd0498ab39e21d24d6730b3f932cec672a702` (Apache-2.0, Lean 4.34.0-rc2), current/open and indexed search, Reservoir/packages, broad discoverable Lean repositories, and local reference mirrors. No `project-existing`, `package-import`, or admissible `reference-port` owner was found.
- Every promoted Mathlib path exists at exact P and every promoted declaration was compiled through the project toolchain. Two nontrivial exact consequences were also compiled as local audit witnesses: U001’s skeletonwise weak-topology iff from `CWComplex.closed`, and U023’s product-of-a-quotient-map theorem from `IsQuotientMap.continuous_lift_prod_left`. Audit witnesses are evidence only, not project source.
- CA has 10 pinned positive rows and 22 dated unmatched rows. The positives are U001 (weak topology), U003 (characteristic-map CW criterion packaged as `CWComplex`), U018 (compact-open topology), U019 (compact-domain sup metric), U020 (evaluation/exponential-law continuity), U023 (quotient map × locally compact identity), U027 (simplicial set), U028 (singular complex), U030 (degenerate simplex), and U031 (geometric realization).
- U002 is deliberately not promoted from `facebookresearch/atlas-lean::Atlas/AlgebraicTopologyI/code/Section15.lean::CWSubcomplex.compact_subset_finite_subcomplex`: the declaration’s proof is `by sorry`. U011 likewise is not routed through Atlas’s `IsNeighborhoodRetract`: that declaration covers an already embedded Euclidean subset rather than Hatcher’s arbitrary-space existence-of-embedding predicate, and the repository license is CC BY-NC 4.0 with an additional no-training rider, so it is not treated as a portable source route.
- U024 remains unmatched after checking the Apache-2.0 LeanPool HEP development at `Vilin97/lean-pool` revision `3fc79f0a795f19fffcc59eee3efaf5faa52de3c3`: it defines `HasHomotopyExtensionProperty`/`IsCofibration` and nearby retractions, but no checked iff identifies HEP with a retraction of `X × I` onto `X × {0} ∪ A × I`.
- U022 is not inferred from `Homeomorph.curry`: the pinned homeomorphism has stronger local-compactness assumptions than Hatcher’s exact Y-locally-compact, Z-Hausdorff theorem. U021 is not inferred from generic compactly-generated machinery without the stated product theorem.
- U031 is an equivalent categorical realization, not a name-only match: `SSet.toTop` is explicitly the geometric-realization functor, constructed as the left Kan extension of standard topological simplices along Yoneda, and `toTopSimplex` identifies representables with the corresponding topological simplices. This is the colimit presentation equivalent to the quotient by all simplex-structure identifications.
- U032 is deliberately not promoted. P and H have degreewise categorical products of simplicial sets, and current `TopAdj.lean` equips the right adjoint `TopCat.toSSet` with monoidal/product structure, but no checked declaration proves that geometric realization `SSet.toTop` preserves products. A TauCeti Lean source encountered in broad discovery explicitly leaves identifying realization with products for later work.
- Current upstream was refreshed on 2026-09-07; `H=80cbd0498ab39e21d24d6730b3f932cec672a702` remained the newest Mathlib HEAD observed and uses Lean 4.34.0-rc2. No new H endpoint closed the unmatched ENR/CW-local-contractibility/product-realization rows.
- This Appendix is the final canonical FC07 block: the catalogue contains no units after `FC07-CA-U032`. With CA promoted, FC07 Sweep II is complete.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are uniform: a proper subset of a multi-clause row, a hypothesis-mismatched theorem, an unproved declaration, or a licensing-incompatible external source is not credited as a route.
