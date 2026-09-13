---
type: reference
title: Provenance contract for C05
description: '- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was
  searched first. Project HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966` owns the
  integrally-closed-domain and valuation-ring category wrappers used at U020 and U029;
  the remaining source-shaped results are delegated to Mathlib.'
tags:
- project
- reference
timestamp: '2026-09-10T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for C05

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. Project HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966` owns the integrally-closed-domain and valuation-ring category wrappers used at U020 and U029; the remaining source-shaped results are delegated to Mathlib.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains every `mathlib` route below. Critical declaration names were compile-checked against the project pin.
- Current/open Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was refreshed 2026-09-06. The only change from the immediately preceding checked `29ea5de9cb981cb62dfa7979aaff0851f50c603a` is `scripts/nolints.json`, so none of the C05 Lean-source positives or negatives changed; targeted open-PR searches did not resolve the strict gaps.
- Package-import route: `E` is `anthropics/fermats-last-theorem@aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` (Apache-2.0), path `P2M/Sol/S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean`. Its lakefile pins Mathlib `P` and toolchain v4.33.1; the module was independently built against this repository's Lean v4.33.0 and pin `P`. U032 uses its exported partial-homomorphism local-ring API. The U031 candidate is retained as a conditional reference, not an exact realization: `exists_maximal` requires an initial graph. The 2026-09-10 printed-source comparison and Lean counterexample in the C05 mapping refute the source's unconditional existence clause. Full namespace: `P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.ChevalleyHom`.
- External negative search: U003 was checked against current/open Mathlib, broad indexed/GitHub Lean search, and ATLAS `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6` (Apache-2.0) without an exact faithful-module criterion. U023–U025 have no checked external owner. For U033–U034, `E` reaches the valuation-ring endpoint for its chosen maximal graph internally but does not export the source theorems for an arbitrary supplied maximal pair; TauCeti `89947b89f080ff3ad6f83f6842fe23b6d07e2b9f` and CBirkbeck `2f45865e87d20dd460cc5a14d04850bf03be4570` likewise use Mathlib's alternative maximal-local-subring construction. No checked external owner was found for U036.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, P/H, open/current work, installed packages, and targeted external Lean search. Alternative proofs are not credited for source-specific construction rows, and partial theorem bundles are not promoted.

