---
type: reference
title: Provenance contract for FC08 C13
description: '# Provenance contract for FC08 C13'
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
# Provenance contract for FC08 C13

# Provenance contract for FC08 C13

- Canonical source block: FC08 Lee, Chapter 13, `FC08-C13-U001`–`FC08-C13-U047`, exactly 47 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` owner survived strict whole-row checking.
- C13 has 3 pinned `mathlib` rows and 44 dated `unmatched` rows. Positive rows are: U037, U038, U046.
- The controlling boundary is inherited from C03 and used consistently in C08/C11/C12. Lee’s tangent spaces in FC08 are the point-derivation model. Mathlib’s mature Riemannian manifold files explicitly build on `TangentSpace I x`; exact P/H searches still find no checked `PointDerivation ≃ TangentSpace`. Therefore the otherwise strong standard-tangent Riemannian metric, path-length, distance, orthonormal-frame, pullback, musical, and gradient APIs are adjacency evidence only, not routes for U001–U036 or U039–U045.
- Submanifold and normal-bundle rows U022–U029 also inherit C05’s missing general immersed/embedded submanifold layer. Generic Riemannian vector-bundle infrastructure does not repair the absent source tangent/submanifold objects.
- U037 is independent of Riemannian tangent semantics: `TopologicalSpace.MetrizableSpace` is exactly Lee’s topological definition. U038 is directly proved by `Manifold.metrizableSpace`, so metrizability survives even though Lee derives it from Riemannian distance.
- U046 is likewise tangent-independent algebra. `LinearMap.BilinForm.Nondegenerate` and `toDual` supply the nondegenerate bilinear form and induced `V ≃ₗ V*`. For symmetric real forms, `QuadraticMap.associated_left_inverse` transports to quadratic-form language, `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` gives Sylvester diagonalization, and `sigPos`/`sigNeg` with their equivalence theorems give the basis-independent signature counts. `/tmp/fc08-c13-witness.lean` compiled the nondegenerate symmetric-form-to-±1 diagonalization bridge at exact P.
- U047 remains unmatched: neither P nor H contains a manifold-level pseudo-Riemannian/Lorentz metric structure with smoothness and constant signature. The algebraic signature package alone is only a proper subset.
- Targeted external/indexed searches did not surface a compatible Lean owner for the missing point-derivation Riemannian bridge or Lorentz/pseudo-Riemannian manifold layer.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

