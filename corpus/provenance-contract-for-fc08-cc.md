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
# Provenance contract for FC08 Appendix C

- Canonical source block: FC08 Lee, Appendix C, `FC08-CC-U001`–`FC08-CC-U050`, exactly 50 unique catalogue rows.
- The 2026-09-14 exact-route remap replaces the obsolete strict-whole-row audit. Current totals are `mathlib` 42, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 8.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was checked at `H=7f22e856c19eeabc38d75733b71d7e44167307f3`.
- The old contract's central integration premise was false: pinned Mathlib has an explicit tagged multidimensional Riemann integral in `Analysis/BoxIntegral`, with `IntegrationParams.Riemann`, finite tagged box partitions, `BoxIntegral.HasIntegral`/`Integrable`, and Riemann sums. Moreover `MeasureTheory.ContinuousOn.hasBoxIntegral`, `MeasureTheory.AEContinuous.hasBoxIntegral`, and `BoxIntegral.integrable_of_bounded_and_ae_continuousWithinAt` identify the Riemann value of continuous/a.e.-continuous box functions with the corresponding Bochner/set integral. This checked bridge promotes U021-U023, U026, U028, U030-U034, and U036-U039 without asserting a nonexistent global Darboux-to-Bochner equivalence.
- Darboux sums themselves remain a real boundary. Mathlib's Riemann implementation is tagged-sum based, so U024 (lower/upper sums) and U025 (the lower-vs-upper comparison) remain unmatched. U029 also remains unmatched: no checked theorem was found proving, for an arbitrary bounded function on an arbitrary bounded set, that extension-by-zero Riemann integrability/value is independent of the chosen containing rectangle. Regular boundary-null continuous functions bypass U029 via the checked a.e.-continuity Riemann theorem and set-integral identification.
- Calculus rows U018 and U019 are positive: Mathlib has parametric differentiation under interval integrals and the higher-dimensional Taylor formula with integral remainder `map_add_eq_sum_add_integral_iteratedFDeriv`. U020 remains unmatched because Lee's exact coordinate remainder constant `n^(k+1) M/(k+1)!` from separate coordinate-partial bounds is not a checked theorem. U013 likewise remains the precise all-orders mixed-coordinate-partial permutation gap.
- U040 is a short native assembly of the convex mean-value theorem with continuity of `fderiv` on compact sets, giving the exact `sup_K ‖DF‖` Lipschitz constant. U042 is covered by Mathlib's uniform-limit continuity/completeness APIs, dominated convergence, and `hasFDerivAt_of_tendstoUniformlyOnFilter`; coordinate partials are handled by one-dimensional standard-basis slices.
- U047 is no longer a gap: nonzero Jacobian determinant gives an invertible derivative; the inverse function theorem gives local open partial homeomorphisms and smooth local inverses, hence openness, and injectivity makes the local inverses glue to the inverse on the image. U048 remains the exact native polar-coordinate example. U049 remains unmatched because no corresponding checked spherical-coordinate map/determinant/injectivity package was found.
- U009 remains unmatched for a different reason than the old audit: the frozen source statement is false as written when `U=V=∅` and the ambient dimensions differ. With a nonempty-domain hypothesis, the derivative inverse formula and equality of dimensions are a short chain-rule/linear-equivalence assembly, but the unqualified frozen theorem cannot be marked checked. U010 remains the local-ambient-extension smoothness notion on arbitrary subsets, for which no equivalence with Mathlib's intrinsic within-set `ContDiffOn` was found.
- Negative findings are scoped to the inspected pinned/current sources; they do not use failed search endpoints as evidence of absence.
