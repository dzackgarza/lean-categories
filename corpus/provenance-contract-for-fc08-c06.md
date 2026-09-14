---
type: reference
title: Provenance contract for FC08 C06
description: '# Provenance contract for FC08 C06'
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
# Provenance contract for FC08 C06

- Canonical source block: FC08 Lee, Chapter 6, `FC08-C06-U001`–`FC08-C06-U044`, exactly 44 unique contiguous catalogue rows.
- The 2026-09-14 `remap-strict-bundle` pass uses clause-wise exact-route semantics. Direct definitions such as manifold-null sets, epsilon-closeness, retractions, smooth homotopies, transversality, smooth families, and almost-everywhere parameter predicates are mapped through their actual Mathlib primitives rather than left greenfield for lack of named wrappers.
- Current route totals regenerated from the table are `mathlib` 19, `project-existing` 0, `package-import` 0, `reference-port` 3, `unmatched` 22; total 44. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`.
- U001–U008 were rechecked against Mathlib measure/product/chart infrastructure. `Measure.measure_prod_null_of_ae_null`, `Measure.volume_eq_prod`, `measurableSet_graph`, `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`, second-countable/Lindelof cover lemmas, and positivity of volume on open sets supply Lee's Euclidean null-slice/graph/null-image results and the chartwise manifold-nullity calculus.
- TauCeti `C=35469bdd4baafcaf1da88fba1e6f6d66d623aaac` (Apache-2.0, Lean 4.34.0-rc2, Mathlib `30a58f795ae8c95b8299fe3c9ded1e6498a9e9fe`) now contains a proof-complete finite-dimensional Morse–Sard development. `Analysis/Calculus/Sard/OutermostStratum.lean` proves nullity of critical values for arbitrary finite dimensions under a sufficient smoothness bound, and `LowDimension.lean` proves the lower-dimensional-source null-image theorem. The six cited Sard files were checked at this commit and contain no `sorry`, `admit`, or `axiom`. U009, U010 and U012 therefore carry `reference-port` routes; the remaining work is Lee's manifold/half-space chart transfer, not rederivation of Sard.
- External candidates were checked adversarially. `leanprover/lean-eval` `Geometry/SardTheorem.lean` states a different rank-deficient Sard problem and its theorem body is `sorry`, so it is not a route. `facebookresearch/atlas-lean` `WeinsteinNeighborhood.lean` contains useful tubular-neighborhood scaffolding but multiple admitted geometric steps, so U027 is not promoted from it. The older `fpvandoorn/sard` checkout likewise retains admitted obligations and is superseded as Sard evidence by the proof-complete TauCeti development.
- Current Mathlib's `WhitneyEmbedding.lean` still proves only a compact-manifold embedding into unspecified finite dimension and explicitly leaves the general `2m+1` theorem as TODO. TauCeti's current weak-Whitney files construct map-space topologies and smooth-family continuity, not the dimension-sharp Whitney embedding/immersion theorems. Hence U013–U020 remain scoped theorem gaps; U021 and U022 are terminology/direct predicates and are not invention work.
- U025's normal-space/normal-bundle definition is direct inner-product/subtype data. The smooth normal-bundle theorem and tubular-neighborhood theorem U026–U027 remain genuine gaps; TauCeti's locally-flat/bicollar notes explicitly leave positive-codimension normal/tubular theory open. U028 is the native continuity/identity retraction predicate, while U029 depends on the unresolved tubular construction.
- `SmoothApprox.lean` remains an exact owner for U023 and the U024 positive smooth minorant corollary, but does not smooth maps into arbitrary manifold codomains or return homotopies. Thus U030–U031 and U034 remain theorem-level residuals. U032 itself is only the direct smoothness predicate on a product-with-interval extension; U033 still needs a checked smooth-concatenation theorem.
- U035 transversality is a direct tangent-range span predicate. TauCeti current Fredholm/Sard–Smale files provide substantial parameter-projection and analytic transversality machinery, but no proof-complete finite-dimensional theorem matching Lee's transverse preimage/intersection, local graph, parametric transversality, or transversality-homotopy statements. U036–U039 and U043–U044 therefore remain unmatched with those exact gaps recorded. U040–U042 are native smooth-family/path-connectedness/null-complement constructions.
- Live formalization-corpus searches and public/reference searches were refreshed on 2026-09-14. Search errors are never negative evidence; every surviving unmatched claim above is supported by successful inspection of pinned/current Mathlib plus the named external revisions/candidates.
