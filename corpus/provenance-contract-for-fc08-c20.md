---
type: reference
title: Provenance contract for FC08 C20
description: '# Provenance contract for FC08 C20'
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
# Provenance contract for FC08 C20

- Canonical source block: FC08 Lee, Chapter 20, `FC08-C20-U001`–`FC08-C20-U034`, exactly 34 unique catalogue rows.
- The 2026-09-14 exact-route remap replaces the obsolete near-total negative audit with the current Lie-group exponential layer. Current totals are `mathlib` 6, `project-existing` 0, `package-import` 0, `reference-port` 10, `unmatched` 18.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`. TauCeti is pinned at `C=35469bdd4baafcaf1da88fba1e6f6d66d623aaac` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`).
- TauCeti now gives a proof-complete finite-dimensional exponential package: invariant integral curves and their uniqueness, one-parameter-subgroup classification, the tangent/left-invariant-derivation Lie equivalence, `lieExp`, smoothness, fixed-line homomorphism laws, inversion/powers, `d exp_0 = id`, local diffeomorphism at zero, functoriality under smooth group homomorphisms, and the right-translation flow formula. These files were audited for `sorry`/`admit`/`axiom` before the routes were accepted.
- `Exponential/Matrix/Compatibility.lean` identifies the ambient `GL(n,ℝ)` exponential with `Matrix.exp`, and Mathlib's normed-algebra exponential gives the power-series formula. The corresponding claims for an arbitrary Lie subgroup of `GL(n)` are not promoted, because current Mathlib/TauCeti still has no general Lie-subgroup structure/restriction theorem; U004, U005, U008 and U011 record that precise residual.
- `Derivative/Log.lean` proves the local logarithm of `exp(tX)exp(tY)` has derivative `X+Y` at zero, and `Trotter.lean` proves the full Trotter product formula. It does not prove Lee's stronger smooth second-order factorization `t(X+Y)+t²Z(t)`, so U012 remains unmatched while U013 is an exact reference port.
- The closed-subgroup theorem is a concrete upstream frontier, not a search guess. TauCeti `Subgroup/LieAlgebra.lean` explicitly names promotion of a closed subgroup to an embedded Lie subgroup as the next target. Consequently U014–U015 and the connected-subgroup/ideal correspondence U028/U034 remain theorem-level residuals.
- Smooth action definitions are native, but no current theorem packages Lee's general infinitesimal-generator/flow, related-vector-field, or action-integration results. U016–U018 and U020–U025/U027 remain scoped to that missing Lie-action/Lie-III layer. U019, U022 and U026 are direct algebra/local-operation definitions and therefore no longer counted as missing abstractions.
- The adjoint layer is proof-complete in current TauCeti. `Adjoint/Basic.lean`/`Derivation.lean` implement `Ad` as the tangent map of conjugation, `Representation/Basic.lean` bundles the smooth group representation, and `Representation/Differential.lean` proves `d(Ad)_1 = ad`. U030, U031 and U033 are accepted reference ports; U032 is Mathlib's native `LieAlgebra.ad`.
- Live corpus/current-source searches found no proof-complete replacements for the residual closed-subgroup, BCH-remainder, action-integration, or Lie-III statements. Search failures/timeouts are never used as negative evidence.
