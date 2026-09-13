---
type: reference
title: Provenance contract for FC08 C02
description: '# Provenance contract for FC08 C02'
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
# Provenance contract for FC08 C02

# Provenance contract for FC08 C02

- Canonical source block: FC08 Lee, Chapter 2, `FC08-C02-U001`–`FC08-C02-U035`, exactly 35 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), current/open/indexed searches, Reservoir and broad discoverable Lean sources, then local reference mirrors. No `project-existing`, `package-import`, or `reference-port` C02 owner is required after the 2026-09-13 clause-wise remap; definitions/conventions assemble directly from native Mathlib predicates where appropriate.
- Every promoted path exists at exact `P`, and the promoted declaration set compiled through the project toolchain. `/tmp/fc08-c02-witness.lean` additionally compiled exact audit witnesses for U009 (smooth gluing over an arbitrary open cover), U022 (arbitrary two-threshold cutoff), U024 (radial Euclidean bump with the strict annular inequalities), U031 (closed-set bump with `tsupport` inside the prescribed open set), and U035 (closed set as an exact smooth zero locus). These witnesses only assemble pinned Mathlib declarations; they are audit evidence, not project source.
- C02 has 31 `mathlib` rows and 4 dated `unmatched` rows after the exact-route remap. The residual unmatched units are U015 (real-projective smooth quotient clauses), U019 (invariance of manifold dimension), U033 (support-controlled smooth extension from subset-local data), and U034 (smooth exhaustion functions).
- Smooth-map rows U002–U012 are mapped through Mathlib’s charted-manifold `ContMDiff` interface rather than by name analogy. Extended charts/model-with-corners encode Lee’s boundary convention; maximal-atlas lemmas give chart independence; open-subtype and open-union lemmas supply locality and the gluing assembly.
- U017 is exact in both parts: `OpenPartialHomeomorph.univUnitBall` uses Lee’s explicit inverse square-root formulas and is proved smooth in both directions, while `OpenPartialHomeomorph.toStructomorph` turns every smooth atlas chart into a smooth diffeomorphism between its open source and target.
- U018 and U020 now use clause-wise assembly: native diffeomorphism composition/product/homeomorphism operations, `Equiv.image`, open-subtype smoothness in source and target, and `Diffeomorph.image_boundary`/`image_interior` construct the restricted diffeomorphisms directly. A missing convenience constructor is not a missing mathematical route.
- U024 is not credited merely from `ContDiffBump`: that interface guarantees 1 on the inner closed ball and positivity in the outer ball but does not guarantee strict `< 1` throughout the annulus (its base file explicitly does not assume an iff characterization of the one-locus). The promoted route instead uses `Real.smoothTransition` composed with squared norm, and the audit witness checks all strict inequalities.
- U028 uses `PartitionOfUnity.IsSubordinate`, which is defined with `tsupport`, i.e. closure of nonzero support, exactly matching Lee’s support convention; `locallyFinite_tsupport` also proves local finiteness for those closed supports. U029 is then the direct smooth subordinate-partition existence theorem under the standard Lee manifold hypotheses.
- U031 is a short exact corollary of U029 using the two-set cover `U, Aᶜ`; the pinned witness verifies smoothness, `[0,1]` bounds, equality to 1 on `A`, and `tsupport ⊆ U`.
- U033 is not inferred from Tietze extension or `Continuous.exists_contMDiff_approx_and_eqOn`: the latter starts with an ambient continuous function already smooth on a neighborhood of the closed set, while Lee starts only with a map defined on the closed subset that is locally extendable. Turning those ingredients into Lee’s global support-controlled extension is the substantive theorem itself.
- U034 remains unmatched after pinned/current/external search: no checked positive smooth exhaustion-function theorem was found. U035 is direct from `exists_contMDiff_zero_iff_one_iff_of_isClosed` with the second closed set specialized to `∅`.
- Current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` was fetched as an object only (no checkout); its `lean-toolchain` is Lean 4.34.0-rc2, and the C02 gap probes did not reveal a current-only owner for U033 or U034. The pinned Mathlib worktree remained clean.
- The 2026-09-13 remap compares source clauses individually. Live formalization-corpus queries for the four residual families were attempted but timed out and are not treated as negative evidence; the residual claims use the successfully inspected pinned/current Mathlib, public Lean and reference/source-atlas surfaces recorded in their rows.
