---
type: reference
title: Provenance contract for FC08 C21
description: '# Provenance contract for FC08 C21'
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
# Provenance contract for FC08 C21

- Canonical source block: FC08 Lee, Chapter 21, `FC08-C21-U001`–`FC08-C21-U042`, exactly 42 unique catalogue rows.
- The 2026-09-14 exact-route remap replaces the obsolete strict-whole-row audit. Current totals are `mathlib` 17, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 25.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was checked at `H=7f22e856c19eeabc38d75733b71d7e44167307f3`. Current TauCeti was inspected at `C=fa4b768a0e9e221ec2c2f05d09fb4212f7c6d871`. Hosted-corpus and grep-style search endpoints returned access/rate-limit failures during this turn; those failures are not negative evidence, and negative rows are based on inspected pinned/current source trees plus successful public/source searches.
- The proper-action topology is substantially complete in Mathlib. `ProperSMul` is exactly Lee's definition; proper orbit quotients are Hausdorff; `MulAction.properSMul_iff_isCompact_setOfPred_inter_nonempty` gives Lee 21.5(c) exactly under manifold-appropriate compact-generation hypotheses; proper-map compactness plus the sequence API supplies the sequence clause. Compact-group properness, proper orbit maps, closed orbits and compact stabilizers are short assemblies from the same proper-map primitives. U005–U011 record the exact clause boundary; U009 alone remains unmatched because the smooth orbit-map immersion/embedding theorem is absent.
- Discrete free actions have a mature topological quotient-covering layer. `properlyDiscontinuousSMul_iff_properSMul`, `ProperlyDiscontinuousSMul.exists_nhds_disjoint_image`, `IsQuotientCoveringMap.disjoint`, and `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` account for U014–U015 and the topological parts of U016–U018. The current Mathlib file `Geometry/Manifold/Instances/Quotient.lean` still explicitly lists the smooth manifold structure and smooth quotient projection as TODOs, so U012/U017 and dependent smooth quotient statements are genuine residuals.
- `LeanCategories/ForMathlib/QuotientManifold.lean` was inspected but is not used as a general `project-existing` escape hatch. It proves a smooth structure only for a normed vector space modulo a discrete additive subgroup. This is relevant partial evidence for U018/U035, not an owner for arbitrary free proper Lie-group actions or arbitrary Lie-group quotients.
- Homogeneous-space definitions are native as `ContMDiffSMul` plus `MulAction.IsPretransitive`, and the underlying coset quotient `G ⧸ H` is native. The smooth closed-subgroup quotient construction, equivariant diffeomorphism `G/G_p ≃ M`, induced smooth structures on transitive G-sets, and the concrete Grassmann/flag/homogeneous quotient examples remain blocked by U012 and the still-missing closed-subgroup theorem. Current TauCeti's `Geometry/Lie` tree contains exponential, adjoint, functor and subgroup-Lie-algebra prerequisites but no closed-subgroup/quotient/homogeneous-space implementation.
- Abstract quotient groups and the first isomorphism theorem are exact Mathlib routes (U029–U030). Discrete subgroup topology is native and Mathlib proves `Subgroup.isClosed_of_discrete` (U033), but promoting arbitrary discrete/closed subgroups to embedded Lie subgroups and forming smooth quotient Lie groups remains unavailable; this is the precise residual in U031–U038.
- U039 is no longer a negative row: orbit fibers are connected as continuous images of connected `G`, and `Topology.IsCoinducing.isConnected_preimage_of_isClosed` lifts connectedness of the quotient to the total space. The classical analytic connectedness/component theorems for `SO(n)`, `U(n)`, `SU(n)`, `O(n)` and real `GL(n)` were not found in current checked Lean sources. TauCeti's similarly named algebraic-group connectedness files concern Zariski/geometric connectedness, not Lee's manifold topology. U041 itself is native because `Matrix.GLPos` is the positive-determinant subgroup and the negative piece is the determinant-negative subset.
- Negative findings are dated/scoped to the inspected sources. Search endpoint failures are never treated as evidence of absence.
