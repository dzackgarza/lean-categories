---
type: reference
title: Provenance contract for FC08 C10
description: '# Provenance contract for FC08 C10'
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
# Provenance contract for FC08 C10

# Provenance contract for FC08 C10

- Canonical source block: FC08 Lee, Chapter 10, `FC08-C10-U001`–`FC08-C10-U055`, exactly 55 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` C10 owner survived strict whole-row checking.
- C10 has 18 pinned `mathlib` rows and 37 dated `unmatched` rows. Positive rows are: U001, U002, U004, U006, U009, U010, U012, U014, U015, U016, U017, U020, U021, U025, U026, U027, U031, U052.
- Mathlib’s basic bundle representation is equivalent to Lee’s after passing between a dependent family `E : B → Type*` and its sigma-type `Bundle.TotalSpace F E`. `FiberBundle` supplies local product trivializations, `VectorBundle` supplies fiberwise linearity, and `ContMDiffVectorBundle` supplies smooth transition functions. At the smooth level Mathlib proves the total space is a manifold, the projection is smooth, and atlas trivializations are smooth in both directions. These facts justify U001/U002 without reconstructing a new bundle formalism.
- The transition-function and Whitney-sum rows have direct owners. `Trivialization.coordChangeL` is invertible on overlaps and satisfies the exact change-of-trivialization formula; `contMDiffOn_coordChangeL` supplies smoothness. `Bundle.Prod` is the fiberwise direct sum and `coordChangeL_prod` gives the product/block transition map. Thus U009/U010/U012 are promoted at P.
- The section rows use the dependent-fiber presentation directly. A rough section is a dependent function `s : ∀ p, E p`; its total-space lift lies over the identity definitionally. `FiberBundle.continuousAt_section`/`continuousWithinAt_section` characterize continuous sections, while `ContMDiffSection` bundles smooth global sections. `/tmp/fc08-c10-witness.lean` compiled the projection identity and the continuity equivalence at P. U014–U017 and U020–U021 are promoted accordingly; U018 remains unmatched because no dependent-section support API was found.
- The local-frame API is strong but intentionally asymmetric. `Trivialization.localFrame` and `isLocalFrameOn_localFrame_baseSet` directly own the frame induced by a trivialization and give U025–U027; `IsLocalFrameOn.coeff` owns U031. However `LocalFrame.lean` explicitly states that a fully frame-intrinsic converse for smoothness is still future work, and no arbitrary-frame-to-trivialization construction was found at P or H. Therefore U023/U024/U028–U030/U032 are not inferred from the one-way infrastructure.
- U011 is deliberately unmatched despite `VectorPrebundle`/`VectorBundleCore`: those constructors produce the topology and smooth vector-bundle structure from compatible coordinate-change data, but no checked theorem supplies Lee’s full uniqueness of both topology and smooth structure. Strict whole-row semantics exclude the construction-only subset.
- U008/U013/U019/U033/U039 and tangent-dependent portions of later examples inherit the promoted C03 boundary: Mathlib’s mature tangent bundle uses standard `TangentSpace`, while Lee’s tangent vectors in this source were introduced as point derivations; no checked `PointDerivation ≃ TangentSpace` bridge exists at P or H. Submanifold-dependent portions also inherit C05’s absence of a general embedded/immersed submanifold package.
- The largest C10 gap is bundle maps/subbundles. Exact searches at P and H found no `BundleHom`/`VectorBundleHom` structure, no bundle-isomorphism structure of Lee’s form, and no `Subbundle`/`VectorSubbundle` abstraction. Consequently U034–U051 remain unmatched rather than being reconstructed from total-space maps, fiberwise linear maps, kernels/ranges, and Riemannian ingredients.
- General smooth fiber bundles are also not bundled at P/H. `FiberBundle` exactly owns U052, but there is no checked general `ContMDiffFiberBundle`/smooth-fiber-bundle predicate for arbitrary model fibers; smooth vector bundles are only a special case. U053–U055 therefore remain unmatched where their whole statements require the missing smooth/general or explicit Möbius components.
- Targeted indexed searches did not surface a compatible external Lean owner for the missing bundle-homomorphism, subbundle, arbitrary-frame converse, or general smooth-fiber-bundle rows. External results were used only as secondary evidence; route decisions are grounded in the exact checked revisions above.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.
