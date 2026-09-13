---
type: reference
title: Provenance contract for FC13 C09
description: '# Provenance contract for FC13 C09'
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
# Provenance contract for FC13 C09

# Provenance contract for FC13 C09

## Provenance contract for FC13 C09

- Canonical source block: FC13 Matsumura Chapter 9, `FC13-C09-U001`–`FC13-C09-U048`, §§25–27, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. All 48 IDs are retrieved through `agent-memory`, asserted once/in-order, and assigned exactly one route.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. No project-owned derivation/Kähler/separability wrapper closes a C09 source unit more completely than pinned Mathlib, so C09 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native C09 coverage is concentrated in derivations, trivial square-zero extensions, Kähler differentials and cotangent/Jacobi–Zariski sequences, formal smooth/unramified/étale maps, separable algebraic field extensions, linear disjointness, relative perfect closure, and the generic differential-basis universal property.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493` (Lean 4.34.0-rc2). Targeted current/open searches for p-bases, differential ideals/Harper/Kimura–Niitsuma, and Hasse–Schmidt/iterative higher derivations found no compatible completed owner. GitHub-wide Lean-code searches likewise found no reusable source-level interfaces.
- Strict bundle semantics were enforced. U002 is not credited from the Lie bracket without D^p being a derivation; U015 is not credited from `IsGeometricallyReduced` because its own pinned TODO records missing arbitrary field-extension stability; U016 is not downgraded from arbitrary finite-dimensional algebras to finite field extensions; and the partial equivalence program in `SeparablyGenerated.lean` does not earn U018–U021/U024.
- The Kähler exact-sequence rows U009–U010 are native assemblies, not textual-name matches: pinned Jacobi–Zariski/conormal exactness plus formal-smooth H₁-vanishing and projectivity supply the stated injectivity and splitting clauses. For U010, `h1CotangentEquivCotangent` identifies the quotient cotangent module with H₁(B/A). U011 uses the presentation-level cotangent complex whose matrix entries are the evaluated partial derivatives. The U006 generator-spanning, U009/U010 injectivity, and U023 perfect-closure minimality assemblies were compile-checked against P in isolated Lean files before promotion.
- Route totals for C09: `mathlib` 13, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 35.
