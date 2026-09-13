---
type: reference
title: Provenance contract for FC11 C01
description: '# Provenance contract for FC11 C01'
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
# Provenance contract for FC11 C01

# Provenance contract for FC11 C01

## Provenance contract for FC11 C01

- Canonical source block: FC11 Peters–Sterk Chapter 1, “Symmetric and Quadratic Forms, an Overview”, `FC11-C01-U001`–`FC11-C01-U155`, 155 units, in exact canonical order from [[foundational-corpus-units-fc11-peters-sterk]].
- Project code baseline: `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19` (Apache-2.0, Lean 4.33.0). No project Lean source changed while this chapter was audited.
- Pinned Mathlib: `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0). Current upstream Mathlib source was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Targeted Mathlib history was inspected from the local full Git checkout; open-PR searches included the form/lattice families and found, among others, PR #42719 on totally isotropic subspaces, which does not close the unmatched Witt/lattice bundles.
- Search services: dated LeanSearch query captures cover linear/symmetric/quadratic forms, integral lattices, primitivity, index/discriminant, parity, reflections, Witt theory, dual/discriminant forms, gluing, local/genus/Hasse theory, dyadic forms, finiteness/Hermite, Nikulin/Niemeier, mass and theta-series families. Loogle captures cover orthogonal, discriminant, primitive/saturated, reflective, Witt, unimodular, Hermite, genus and theta vocabulary.
- Package discovery: Reservoir application/search data were captured and inspected. The local formalization-source atlas was checked across all registered sources, including `formal-conjectures@b123bb89b5978ae6b648159e430c4e4dce161b97`. Broad GitHub Lean code search captures cover bilinear/quadratic forms, primitive lattices, reflections, discriminant forms, overlattices, dyadic forms, Nikulin, Witt decomposition, Niemeier and Hermite families.
- Reference-port source used by three rows: `TauCeti@98a6bfc9f3cb4ab3a159d83858ce546d1e543c1b` (Apache-2.0), Lean 4.34.0-rc2 with Mathlib `e21ec05048292b3de86d4cf1987e2208171a5642`. Its integral-lattice index, overlattice/isotropic-subgroup, orthogonal-quotient and naturality declarations are mathematically compatible but require a source port to the project toolchain, so they are `reference-port`, not `package-import`.
- 2026-09-13 `remap-strict-bundle` rule: source units are matched clause by clause; a row may assemble several checked declarations when that conjunction realizes the source statement. `unmatched` is retained only for the residual source clauses after the checked Mathlib/project/reference/search evidence recorded in the mapping row; `project-existing` is accepted only with an explicit route to mapped source units, Mathlib primitives, or a cited reference implementation.
- Route totals after the 2026-09-13 exact-route remap: `mathlib` 99, `project-existing` 14, `package-import` 0, `reference-port` 3, `unmatched` 39; total 155.
- Negative-result scope is the dated 2026-09-13 remap evidence in each current `unmatched` row. Search-service errors, rate limits, and timeouts are not negative evidence; only inspected revisions and successful search surfaces cited by the row support its residual gap.
