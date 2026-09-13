---
type: reference
title: Provenance contract for FC09 C02
description: '# Provenance contract for FC09 C02'
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
# Provenance contract for FC09 C02

# Provenance contract for FC09 C02

## Provenance contract for FC09 C02

- Canonical source block: FC09 Neukirch Chapter II, `FC09-C02-U001`–`FC09-C02-U135`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 135 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). `LeanCategories/ForMathlib/DenseIntegralCompletion.lean` is a material project-owned owner: its compatible quotient-power equivalences and inverse-limit/completed-valuation-ring comparison, specialized through the pinned rational height-one-prime/PadicInt equivalence, close U025 as `project-existing`. Other project p-adic/local-global wrappers do not close an additional C02 bundle beyond the pinned owners recorded here.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native coverage is strongest for the Cauchy construction of ℚ_p, p-adic valuations and ℤ_p ideals, absolute-value equivalence/weak approximation/Ostrowski, valuation rings and DVRs, generic completion, finite-dimensional topology and spectral norms, nonarchimedean local fields, the p-adic factorial formula, Krull topology/infinite Galois correspondence, fixed fields, and the valuation-subring inertia kernel.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Targeted current-tree and open-work searches were run for the unresolved Newton-polygon, henselian-extension, local-field classification, valuation-extension, ramification, and higher-ramification bundles. The current `Mathlib/RingTheory/Valuation/RamificationGroup.lean` still explicitly says `TODO: Define higher ramification groups in lower numbering`; no compatible current/open route was found for U125–U135.
- Strict bundle semantics was enforced. In particular, the infinity valuation on `k(t)` does not earn U015 without its product formula; p-adic residue maps do not earn formal digit/power-series presentations; principal-unit infrastructure does not earn the all-level quotients U041–U042; generic adic-completion infrastructure does not earn U049 because that row also asserts the units inverse limit; simple-root Hensel APIs do not earn the factorization and henselian-characterization rows; ideal-theoretic ramification APIs do not earn the henselian/unramified/tame valued-field bundles; and decomposition/inertia definitions do not earn any source row that also asserts a ramification group, exact sequence, completion isomorphism, or higher ramification theorem.
- Short derivations are credited only when all ingredients are exact pinned owners: U024 uses the kernel of `toZModPow` plus its elementary surjectivity by natural representatives; U033 converts a uniform integer bound to `|n|≤1` by applying the bound to powers; U054 combines the spectral-norm uniqueness/constant-term formula with field-norm transitivity. These are direct theorem-level derivations, not partial semantic matches.
- All `mathlib` targets were path/token validated against P, every `project-existing` target against project baseline A, and the higher-ramification negative check against H.
- Route totals for C02: `mathlib` 31, `project-existing` 1, `package-import` 0, `reference-port` 0, `unmatched` 103.

