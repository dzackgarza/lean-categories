---
type: reference
title: Provenance contract for C02
description: Extracted from Foundational corpus mapping FC04 Atiyah Macdonald.
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for C02

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first for module, exact-sequence, tensor, scalar-change, flatness, and algebra interfaces. The project consumes Mathlib's foundational algebra APIs downstream but does not own source-shaped replacements for these Chapter 2 units.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, was checked declaration-wise and compile-checked for the critical boundary interfaces.
- Current/open Mathlib: upstream `29ea5de9cb981cb62dfa7979aaff0851f50c603a` (Apache-2.0, Lean v4.34.0-rc2), denoted `H`, was refreshed 2026-09-06. Targeted current-tree and open-PR searches were used for the strict negative rows, including Hom-detection converses, arbitrary additive invariants, the concrete tensor counterexamples, and multi-tensor uniqueness.
- External positive route: `E` is `AxelDlv00/LeanAlgebraicGeometry@f48ddbf1eb13625e8c41acbd549cc4522fb8b79f` (Apache-2.0). Its Algebraic-Jacobian project pins Lean v4.31.0 and Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The U020 theorem's proof was independently compiled unchanged against project pin `P`, so the route is source-revision-specific but port-compatible with the repository baseline. The external repository's current `HEAD` was rechecked immediately before this candidate was assembled and is still exactly `f48ddbf1eb13625e8c41acbd549cc4522fb8b79f`.
- External negative search: targeted GitHub/indexed Lean searches found no complete owner for the seven strict negative bundles. Partial generic infrastructure is not credited when a concrete example, converse, positive-rank normalization, arbitrary invariant, or arbitrary-target uniqueness clause is missing.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, pinned/current Mathlib, relevant open work, installed packages, and external indexed search.
