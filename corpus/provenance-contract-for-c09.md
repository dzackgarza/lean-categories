---
type: reference
title: Provenance contract for C09
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
# Provenance contract for C09

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first. Project HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966` explicitly reifies discrete valuation rings and Dedekind domains in `LeanCategories/Algebra/Concrete/Rings.lean`; those definition rows are `project-existing`. `LeanCategories/Algebra/FractionalIdeals.lean` only wraps Mathlib's fractional-ideal/class-group APIs (`InvertibleFractionalIdeal`, `idealClass`, principal/trivial-class lemmas, integral-class surjectivity) and does not own a complete U016–U029 source row.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains the DVR TFAE, Dedekind local equivalence, adic valuations, fractional-ideal inversion, ideal factorization, class-group, class-number, and Dirichlet-unit interfaces below. The nontrivial U001 product conversion, U009 primary-power direction, and U024 finite-support/reconstruction bundles were compile-checked against P.
- Current/open Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was refreshed 2026-09-06 and preserves the checked interfaces. Targeted current/open and indexed external searches were used for U013, U020, U021, U028, and U029.
- Source defect: the frozen Proposition 9.7 row U021 is false as printed at the field edge under the chapter's preceding DVR definition: a field is a local domain whose only nonzero fractional ideal is invertible, but a field does not admit the source's surjective discrete valuation `Kˣ→ℤ`. The mapping therefore records the row as unmatched rather than silently adding a nonfield hypothesis.
- `N` denotes dated 2026-09-06 negative evidence after project-first search, P/H, open/current work, installed packages, and targeted external Lean search. A concrete number-ring example is not credited from separate abstract number-field and Gaussian/Pell infrastructure without the required bridge.
