---
type: reference
title: Provenance contract for FC08 CD
description: '# Provenance contract for FC08 Appendix D'
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
# Provenance contract for FC08 CD

# Provenance contract for FC08 Appendix D

- Canonical source block: FC08 Lee, Appendix D, `FC08-CD-U001`–`FC08-CD-U011`, exactly 11 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then indexed/current/open Mathlib work, packages/Reservoir, broad GitHub Lean repositories, and local reference sources. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix D has 3 pinned `mathlib` rows and 8 dated `unmatched` rows. Positive rows are: U001, U002, U006.
- `/tmp/fc08-cd-witness.lean` compiles at exact P and checks Mathlib’s public ODE surface: integral-curve predicates, the Picard operator, Picard–Lindelöf existence families, interval/open-set uniqueness theorems, solution regularity in time, and generalized eigenspaces.
- U001/U002 map directly to `ODE.IsIntegralCurveOn` and its time-independent specialization. U006 is exact: `ODE.picard_apply` is Lee’s integral operator, including the initial-value constant and interval integral.
- Mathlib’s current Picard–Lindelöf development is substantial but stops short of Lee’s strongest bundled regularity claims. It gives local solution families with continuous/Lipschitz dependence on initial points and `C^n` regularity of each solution curve in time; targeted P/H search found no smooth-dependence theorem for the flow as a function of initial data. This blocks U003, U008, and U009 under strict semantics.
- The public existence/uniqueness results use uniform Lipschitz bounds on a chosen region. Lee U005/U007 assume only local Lipschitz continuity and quantify over neighborhoods/common domains. Their localization/chaining argument is not inferred from the stronger local ingredients without a checked wrapper theorem.
- Broad GitHub search found a current Lean control-theory project that explicitly axiomatizes Picard–Lindelöf-style existence rather than proving a reusable replacement; it therefore supplies no acceptable import/reference route. No compatible external source was found for Lee’s nonlinear comparison theorem or the full `2×2` ODE solution classification.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

