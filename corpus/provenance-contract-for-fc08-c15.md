---
type: reference
title: Provenance contract for FC08 C15
description: '# Provenance contract for FC08 C15'
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
# Provenance contract for FC08 C15

# Provenance contract for FC08 C15

- Canonical source block: FC08 Lee, Chapter 15, `FC08-C15-U001`–`FC08-C15-U056`, exactly 56 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. No `project-existing`, `package-import`, or `reference-port` owner survived strict whole-row checking.
- C15 has 5 pinned `mathlib` rows and 51 dated `unmatched` rows. Positive rows are: U003, U004, U006, U007, U048.
- Linear orientation algebra is mature at P. `Orientation` is a positive ray of top alternating forms; `Basis.orientation`, `orientation_eq_iff_det_pos`, and the negation lemmas make it equivalent to Lee’s ordered-basis equivalence classes. The zero-dimensional case is represented by `positiveOrientation` and `Orientation.eq_or_eq_neg_of_isEmpty`.
- `/tmp/fc08-c15-witness.lean` compiled at exact P. Its central bridge proves `rayOfNeZero ℝ ω hω = e.orientation ↔ 0 < ω e`, so Mathlib’s ray representation exactly realizes Lee Proposition 15.3; it also verifies that the determinant form of a basis lies in that basis orientation.
- U002 is deliberately unmatched because the canonical catalogue row is truncated after the transition-matrix formula and omits the determinant-sign condition. The adjacent Mathlib theorem is not used to repair source text silently.
- P and current H have no global smooth-manifold orientation/orientability API. Exact searches find no `Orientable`/`IsOrientable` manifold structure, orientation-preserving smooth-map predicate, orientation covering, or smooth manifold volume-form layer. Therefore U008–U047 and U050–U056 remain unmatched even when linear orientation, standard-tangent Riemannian, or generic covering ingredients are present.
- Tangent-based manifold rows also inherit the C03 boundary: Lee’s FC08 tangent spaces are point derivations, while Mathlib manifold tangent geometry uses standard `TangentSpace`; no checked bridge exists at P/H. Hypersurface/submanifold rows additionally inherit C05’s absent general submanifold API.
- U048 is independent of manifold orientation. Mathlib’s `IsCoveringMap` already permits disconnected total spaces and supplies the evenly-covered/continuity part, while Lee additionally requires local path connectedness and surjectivity. The exact conjunction was compiled in the witness. U049 is not inferred: no checked theorem provides Lee’s componentwise restriction result, and proving it would be substantive.
- Targeted current GitHub/indexed searches did not surface a compatible external Lean owner for manifold orientability or the orientation-covering theorems.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

