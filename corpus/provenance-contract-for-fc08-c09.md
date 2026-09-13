---
type: reference
title: Provenance contract for FC08 C09
description: '# Provenance contract for FC08 C09'
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
# Provenance contract for FC08 C09

# Provenance contract for FC08 C09

- Canonical source block: FC08 Lee, Chapter 9, `FC08-C09-U001`–`FC08-C09-U081`, exactly 81 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` C09 owner survived strict whole-row checking.
- C09 has 2 pinned `mathlib` rows and 79 dated `unmatched` rows. Positive rows are: U010, U011.
- The controlling geometric boundary is inherited from promoted C03/C08. Lee’s tangent vectors are the point-derivation model; Mathlib’s manifold integral-curve theory (`IntegralCurve/Basic`, `Transform`, `ExistUnique`, `UniformTime`) is formulated with the separate standard `TangentSpace` model. Exact P/H searches again found no `PointDerivation ≃ TangentSpace` bridge. Consequently the otherwise-close integral-curve existence, uniqueness, translation/scaling, uniform-time, vector-field and Lie-bracket APIs cannot silently own Lee’s derivation-tangent rows.
- This exclusion is substantive: pinned Mathlib now has a strong manifold integral-curve package. `IsMIntegralCurveOn`/`At`, `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`, `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`, the transform lemmas, and `exists_isMIntegralCurve_of_isMIntegralCurveOn` are all nearby. They establish adjacency only, because using them here would reverse the already-promoted C03 model decision.
- U010 and U011 are independent of tangent vectors and do match exactly. `Mathlib/Dynamics/Flow.lean::Flow ℝ M` stores Lee’s global continuous ℝ-action. Its fixed-time continuity, group laws, `toHomeomorph`, and `orbit_eq_range` own U011’s topological clauses. For the smooth clause, after using `Flow.toAddAction`, `ContMDiffVAdd` and `Diffeomorph.vadd` give the fixed-time diffeomorphism. `/tmp/fc08-c09-flow-witness.lean` compiled the entire U010/U011 interface at P.
- P/H have no local/partial-flow structure with a flow domain `D ⊆ ℝ × M`, no maximal-flow object, and no fundamental theorem producing Lee’s maximal partial flow. `Dynamics.Flow` is global only. This is the separate blocker for U017–U027, U035–U037, U048–U050, U057–U061 even aside from tangent semantics.
- U017 and U018 are canonically truncated in the Sweep-I catalogue; U073 is also truncated before its coordinate formula. They were left unmatched from the canonical text and were not reconstructed from the book during Sweep II.
- Current H was checked specifically for `LocalFlow`, flow-domain/maximal-flow constructions, collar neighborhoods, Lie derivatives, manifold time-dependent vector fields, and first-order characteristics; it contains none. Its relevant flow/integral-curve file set is materially the same as P on these interfaces.
- Boundary geometry remains absent: P/H have no collar-neighborhood construction/theorem, boundary flowout theorem, smooth attachment-along-boundary theorem, connected-sum/double construction with Lee’s smooth properties, or boundary flow-box theorem. `Geometry/Manifold/Bordism.lean` only mentions the collar-neighborhood theorem in prose.
- The Lie-derivative/commuting-fields section also has no direct owner. Mathlib has the standard-tangent manifold Lie bracket and global flow/invariant-set APIs, but no Lie derivative of vector fields defined via flow, no vector-field invariance-under-flow predicate, and no local-flow commutation theorem. Replacing Lee’s flow definition by the bracket using his later theorem would reverse the source dependency and cross the tangent-model boundary.
- Time-dependent theory is presently Banach-space rather than manifold-level. `Mathlib/Analysis/ODE` formalizes time-dependent vector fields, integral curves, Picard–Lindelöf local flows, and uniqueness on normed spaces. No P/H theorem gives Lee’s arbitrary-manifold time-dependent flow with maximal domains, restart property, partial-time diffeomorphisms, and cocycle law.
- Targeted indexed search found no Lean implementation of the missing collar/local-flow/Lie-derivative/method-of-characteristics results. The only method-of-characteristics hits were non-Lean numerical/symbolic projects and were irrelevant to routing.
- No first-order linear/quasilinear Cauchy-problem or method-of-characteristics formalization matching U070–U081 was found in project source, P, H, or indexed Lean repositories.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.
