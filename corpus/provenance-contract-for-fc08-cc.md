---
type: reference
title: Provenance contract for FC08 CC
description: '# Provenance contract for FC08 Appendix C'
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
# Provenance contract for FC08 CC

# Provenance contract for FC08 Appendix C

- Canonical source block: FC08 Lee, Appendix C, `FC08-CC-U001`–`FC08-CC-U050`, exactly 50 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then current/open/indexed services, Reservoir/package candidates, broad GitHub Lean repositories, and local reference sources. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix C has 23 pinned `mathlib` rows and 27 dated `unmatched` rows. Positive rows are: U001, U002, U003, U004, U005, U006, U007, U008, U011, U012, U014, U015, U016, U017, U027, U035, U041, U043, U044, U045, U046, U048, U050.
- `/tmp/fc08-cc-witness.lean` compiles at exact P and checks the principal calculus routes: Fréchet derivatives and chain rule, line derivatives, second-derivative symmetry, Taylor/parametric-integral adjacency, Fubini/Bochner integration adjacency, local Lipschitz results, uniform-series M-test, inverse function theorem, Banach contraction, and implicit function theorem.
- Mathlib’s Fréchet calculus provides exact coordinate-free owners for Lee’s total derivative, chain rule, `C^k` regularity, and local inverse/implicit-function results. `lineDeriv` supplies the exact one-variable derivative along a standard basis vector, so source partial derivatives and Jacobian entries are short canonical assemblies rather than new definitions.
- The main negative boundary is representational and deliberate. Lee builds multidimensional integration through Darboux sums and a Riemann integral on bounded domains; pinned/current Mathlib uses Lebesgue/Bochner integration. Mathlib has stronger Fubini, vector-integral, norm-integral, set-volume, and Jacobian change-of-variables results, but no checked Riemann–Lebesgue equivalence for Lee’s interface. Therefore U021–U026 and U028–U039 remain unmatched except for the representation-independent null-set theorem U027 and Corollary U035.
- `map_add_eq_sum_add_integral_iteratedFDeriv` gives a strong coordinate-free Taylor theorem, but Lee’s U019 is the explicit all-orders multi-index partial-derivative formula. Because the all-orders mixed-partial permutation bridge in U013 was not found, U019/U020 are not promoted by silently translating representations.
- The polar-coordinate example U048 has an unusually exact pinned owner: `polarCoord` is the open partial homeomorphism between the slit plane and `(0,∞)×(-π,π)`, its inverse is Lee’s `(r cos θ,r sin θ)`, and `det_fderivPolarCoordSymm` computes determinant `r`. No corresponding full spherical-coordinate owner was found for U049.
- Broad GitHub searches on 2026-09-07 did not surface a compatible Lean 4 implementation of Lee’s multidimensional Darboux/Riemann layer or a missing Jacobian/partial-derivative bundle. Current repositories found in the ODE/control direction either reuse Mathlib or explicitly axiomatize ODE existence results, so they do not improve Appendix C routes.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

