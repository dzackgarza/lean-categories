---
type: reference
title: Provenance contract for FC08 C06
description: '# Provenance contract for FC08 C06'
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
# Provenance contract for FC08 C06

# Provenance contract for FC08 C06

- Canonical source block: FC08 Lee, Chapter 6, `FC08-C06-U001`–`FC08-C06-U044`, exactly 44 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Chapter title: *Sard’s Theorem*. Search order followed the Sweep-II plan: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then current/indexed/external Lean searches and local reference probes. No `project-existing`, `package-import`, or completed `reference-port` C06 owner survived strict checking.
- C06 has 3 pinned `mathlib` rows and 41 dated `unmatched` rows. Positive rows are U003, U023, U024. Every cited positive file exists at exact P. `/tmp/fc08-c06-witness.lean` compiles U003’s Euclidean specialization of `addHaar_affineSubspace` and derives U024 exactly from `Continuous.exists_contMDiff_approx`; it also confirms the relevant smooth-approximation interface at the project pin. The witness is audit evidence only, not project source.
- U003 is direct measure theory: `addHaar_affineSubspace` proves every proper affine subspace of a finite-dimensional real normed space is null for any additive Haar measure, hence for Euclidean `volume`. U023 is the pinned `SmoothApprox` theorem: variable positive continuous error, smooth approximation of a continuous vector-valued function on a real finite-dimensional manifold, with equality on a closed set where the original map is already smooth on a neighborhood. U024 is the immediate positive smooth minorant corollary, compiled from U023.
- P/H do not have Lee’s manifold measure-zero abstraction. An external indexed search found `fpvandoorn/sard`, inspected at `R=77da83ff581fc9bf8af67e18ba8949cf555cc41c` (Lean 4.12.0). Its completed `Sard/MeasureZero.lean` defines a preferred-chart `MeasureZero`, but the file explicitly notes that equivalence with all charts is still missing; `measure_zero_image_iff_chart_domains` itself contains `sorry`. Therefore U005–U008 are not promoted from that repository.
- The same external repository is not used as a Sard `reference-port`: its README states the hard Morse–Sard case remains open, and the exact checkout contains 41 `sorry`/`admit` occurrences. `Sard/MainTheorem.lean` states manifold Sard results but their proofs depend on those unfinished obligations. P/H only provide partial Euclidean/Hausdorff-dimension Sard consequences, so U009–U010 remain unmatched.
- `Mathlib/Geometry/Manifold/WhitneyEmbedding.lean` is deliberately not over-credited. At P and H it proves a compact-manifold embedding into some finite-dimensional Euclidean space and explicitly lists the general weak `ℝ^(2m+1)` theorem as TODO pending stronger Sard machinery. Thus none of U013–U021 has the dimension-sharp/general owner demanded by Lee’s rows.
- `Mathlib/Geometry/Manifold/SmoothApprox.lean` is a direct owner only for U023 and the compiled U024 corollary. It does not approximate maps into arbitrary manifold codomains and does not produce homotopies, so U030–U034 remain unmatched. U022 is only terminology: Mathlib uses the same pointwise distance formula but exposes no named ε-close predicate.
- Targeted P/H searches found no tubular-neighborhood implementation, no normal-bundle construction for arbitrary embedded submanifolds, and no smooth transversality API. The latter appears only in comments in `Bordism.lean`; there is no checked `Transverse` predicate or parametric/transversality-homotopy theorem. Consequently U025–U029 and U035–U044 remain unmatched. These blocks also depend on the general submanifold abstraction already established missing in C05.
- Current upstream H was inspected by git object without changing the pinned worktree. H still contains only `SmoothApprox.lean` and `WhitneyEmbedding.lean` among the relevant manifold files, and targeted searches found no Sard-manifold, tubular, transversality, or smooth-homotopy implementation.
- `N=2026-09-07` marks dated unmatched decisions after the prescribed search layers. Strict whole-row semantics apply uniformly.

