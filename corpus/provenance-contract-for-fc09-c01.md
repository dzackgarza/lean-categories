---
type: reference
title: Provenance contract for FC09 C01
description: '# Provenance contract for FC09 C01'
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
# Provenance contract for FC09 C01

# Provenance contract for FC09 C01

## Provenance contract for FC09 C01

- Canonical source block: FC09 Neukirch Chapter I, `FC09-C01-U001`–`FC09-C01-U135`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 135 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). Project-owned arithmetic code was searched first, including `LeanCategories/Algebra/FractionalIdeals.lean`; that wrapper re-exposes the class-group map/kernel/surjectivity pieces but does not close a C01 bundle beyond the pinned Mathlib owners recorded here, so C01 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native coverage is extensive in Gaussian integers, number fields/integrality, trace/norm/discriminants, Dedekind and fractional ideals, Minkowski/class-number/Dirichlet-unit theory, ramification/Hilbert/cyclotomic theory, localization/DVRs, affine schemes, and rational-function valuations.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6` (2026-09-07 00:03:14 UTC). Targeted current-tree symbol/file searches and targeted open-PR searches were run for the unresolved bundles. Current H contains neither the #40848 localization declarations nor the #40791 S-unit theorem module. Open PR #40848 at `2c91fb2be280d3a396f0f7de2d7d0df5bf2a8243` proves that the valuation-defined S-integer ring is the required localization and a Dedekind domain; this changes U096 to a revision-specific `reference-port`. Open PR #40791 at `6c4013931e7a0c11d5696f2bcf76628d6fcdf565` proves finite generation and the rank formula for S-units, but no checked source-complete route here identifies its torsion factor with `μ(K)` and packages Neukirch U097's full direct-product isomorphism, so U097 remains unmatched.
- Strict bundle semantics was enforced throughout. In particular, the Gaussian infrastructure does not earn U006's complete prime classification or U007's `ℤ[i]=𝓞_{ℚ(i)}` identification; the pinned embedding formulas do not earn U015 without its characteristic-polynomial factorization; the standard mixed-space convention is not silently identified with Neukirch's all-embeddings metric/measure in U045–U048; the weaker exported Minkowski class bound does not earn U053's sharp `(2/π)^s` constant; the deleted-coordinate regulator convention does not earn U060's `√(r+s)` covolume statement; and partial Hilbert-theory APIs do not earn the full U081 inertia-field bundle.
- The late chapter is treated the same way: local/scheme order-of-vanishing APIs do not earn U115's global divisor/principal-divisor/rational-equivalence bundle; a generic presheaf does not earn U124 because Neukirch also imposes `F(∅)=0`; and the rational-function Ostrowski theorem does not earn U132 because that unit also asserts finiteness of the valuations outside the chosen affine model. Spec/Zariski/residue fields, sheaf/stalk/structure-sheaf, and full faithfulness of affine Spec are credited only where they close their complete source units.
- All pinned targets listed as `mathlib` were path/token validated against P. The U096 target was validated by `git show` at the exact #40848 head revision, and the cited #40791 finite-generation/rank declarations were likewise checked at its exact head.
- Route totals for C01: `mathlib` 64, `project-existing` 0, `package-import` 0, `reference-port` 1, `unmatched` 70.
