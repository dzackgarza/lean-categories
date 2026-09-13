---
type: reference
title: Provenance contract for C06
description: Extracted from Chapter 2. Modules.
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
# Provenance contract for C06

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. Project HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966` explicitly reifies Noetherian modules, Artinian modules, simple modules, Noetherian rings, and Artinian rings as full subcategories; these definition rows are `project-existing`, with the source equivalences supplied by the pinned Mathlib predicates.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains the chain-condition, finite-length, composition-series, Jordan–Hölder, and length APIs cited below. Critical declarations were compile-checked against the project environment.
- Current/open Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was checked 2026-09-06. The C06 positive declarations persist there. U010, U016, and U030 were separately searched in current/open work rather than inferred from nearby general results.
- External negative search: targeted GitHub/indexed Lean searches found no strict owner for U010's six-example module bundle or U016's ring-example bundle; in particular the compact-Hausdorff function-ring and infinite-variable polynomial counterexamples remain absent. U030 is not negative: its source criterion compiles directly from pinned prime/product, Krull-dimension-zero, and Hopkins–Levitzki APIs.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, P/H, current/open work, installed packages, and targeted external search. Concrete comparison bundles are not credited piecemeal.
