---
type: reference
title: Provenance contract for FC08 C11
description: '# Provenance contract for FC08 C11'
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
# Provenance contract for FC08 C11

# Provenance contract for FC08 C11

- Canonical source block: FC08 Lee, Chapter 11, `FC08-C11-U001`–`FC08-C11-U068`, exactly 68 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` C11 owner survived strict whole-row checking.
- C11 has 9 pinned `mathlib` rows and 59 dated `unmatched` rows. Positive rows are: U001, U002, U003, U004, U005, U007, U009, U035, U065.
- The pure finite-dimensional dual-space block has direct owners. `Module.Dual`, `Basis.dualBasis`, `LinearMap.dualMap`, the identity/composition laws, and `Module.evalEquiv` match U001–U005 and U007. `/tmp/fc08-c11-witness.lean` compiled these specializations at P. U006 remains unmatched because no contravariant dual functor on the category of real vector spaces/modules matching Lee’s categorical statement was found.
- C11 preserves the tangent-model contract established in promoted C03. Lee’s `TₚM` is the point-derivation model, so U009 can be represented exactly as `Module.Dual ℝ (PointDerivation I p)`. The same choice makes U035 a short exact assembly: dualize `fdifferential F p` with `LinearMap.dualMap`. The witness compiles `(dFₚ)⁎ ω v = ω (dFₚ v)` at the pin. This does not assert any unproved bridge to Mathlib’s standard `TangentSpace`.
- No general manifold cotangent bundle or bundled manifold 1-form/covector-field theory was found at P or H. `Analysis/Calculus/DifferentialForm` explicitly represents forms on normed vector spaces, and `Geometry/Manifold/MFDeriv/NormedSpace` represents scalar differentials using the separate standard `TangentSpace`. Exact P/H searches found no `CotangentBundle`/manifold 1-form layer. Therefore U011–U025 and the global pullback/smoothness rows U036–U042 are not inferred from vector-space or standard-tangent infrastructure.
- The differential-of-functions block U026–U033 is likewise not silently transferred. `mvfderiv` is excellent standard-tangent infrastructure, while `DerivationBundle.fdifferential` stays within point derivations and does not package `df` as a cotangent field. Without the missing `PointDerivation ≃ TangentSpace` theorem or a derivation-model cotangent bundle, the source rows remain unmatched.
- Pinned Mathlib does contain a substantial curve-integral theory: `MeasureTheory/Integral/CurveIntegral/Basic.lean` defines `curveIntegral` for 1-forms on normed vector spaces and proves reversal, concatenation, linearity, and the ordinary-integral formula. `CurveIntegral/Poincare.lean` proves homotopy invariance and a Poincaré lemma for convex subsets. These are recorded as adjacent evidence only: Lee’s U043–U064 are stated for cotangent fields and piecewise-smooth curves on arbitrary manifolds, an interface absent from P/H.
- U065 is independent and exact: `StarConvex ℝ c U` plus `c ∈ U` is precisely Lee’s star-shaped condition, with `starConvex_iff_segment_subset` giving the source formulation. The C11 witness compiles the equivalence.
- U066 is deliberately not promoted from the pinned Poincaré theorem. Mathlib assumes `Convex ℝ U`, while Lee assumes only star-shaped; convexity is strictly stronger. No star-shaped Poincaré theorem was found at P, current H, project source, or targeted indexed Lean searches. U067 then also lacks the manifold closed-1-form layer needed for Lee’s local-exactness corollary.
- Submanifold restriction U041–U042 additionally inherits the promoted C05 blocker: P/H still lack Lee’s general embedded/immersed submanifold abstraction. No reconstruction from inclusions and linear restrictions was used.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.
