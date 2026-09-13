---
type: reference
title: Provenance contract for FC08 C01
description: '# Provenance contract for FC08 C01'
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
# Provenance contract for FC08 C01

# Provenance contract for FC08 C01

- Canonical source block: FC08 Lee, Chapter 1, `FC08-C01-U001`–`FC08-C01-U061`, exactly 61 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order followed the Sweep-II contract: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, then pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), current/open work, indexed searches, Reservoir/package material and broad/local Lean reference mirrors.  No `project-existing`, importable package, or admissible external reference-port owner was found for a C01 row.
- Every promoted Mathlib declaration/path was checked through the project toolchain at the exact pin `P`; cited source files were verified with `git cat-file`.  The compiled audit witness `/tmp/fc08-c01-checks.lean` also checked the structural real-manifold assemblies and synthesized countability of connected components from `SecondCountableTopology` plus local path-connectedness.  C01 therefore has 18 `mathlib` rows and 43 dated `unmatched` rows.
- Positive rows are: U001 (topological-manifold structural interface/Hausdorffness), U010 (product topological manifolds and dimension-sum bridge), U013 (local path connectedness, components, countability, open component manifolds), U014 (local compactness), U015 (local finiteness/refinement/paracompactness), U016 (closures of locally finite families), U019 (smooth maps/diffeomorphisms), U020 (transition maps and smooth compatibility), U021 (smooth atlases), U022 (maximal-atlas presentation of smooth structures), U024 (`C^k`/real-analytic/complex-analytic variants), U030 (standard smooth Euclidean space), U036–U037 (open submanifolds), U046 (smooth products), U049 (half-space interior/frontier), U060 (product boundary formula), and U061 (smooth invariance of boundary).
- U003 is not promoted: no topological invariance-of-dimension theorem was found.  U012/U017/U018 are likewise not inferred from second-countability/paracompactness: the exact precompact-coordinate-ball basis, countable arbitrary-basis refinement, and countable-`π₁` statements were not found as checked owners.
- U008/U042 are deliberately not routed to `EuclideanSpace.instIsManifoldSphere`: Mathlib’s sphere atlas is stereographic, while Lee’s rows specify graph-coordinate atlases, and no checked atlas-equivalence bridge was found.  The same strict representation rule leaves the real-projective and Grassmann rows unmatched.
- The boundary distinction is material.  `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas` proves chart-independence for `C¹` and higher, so it exactly supports smooth U061.  The file explicitly explains that the analogous finite-dimensional *topological* result requires singular homology and is not proved there; therefore U051–U052 and the topological boundary-manifold assertions of U055 are not promoted from preferred-chart definitions or smooth theorems.
- U057 is not equated with Mathlib’s `ContDiffWithinAt`: Mathlib uses local Taylor-series/derivative data on a set, whereas Lee defines smoothness on arbitrary subsets by local extension to an ambient open set and additionally records the boundary-derivative/Borel characterization.  No checked equivalence of these complete interfaces was found.
- Broad external discovery found no admissible complete owner for the missing dimension-invariance, precompact-chart, countable-`π₁`, real-projective/Grassmann, full-rank-matrix, regular-level-set, or topological-boundary-invariance rows.  `facebookresearch/atlas-lean` was not credited: the locally mirrored source is research-only CC BY-NC with a no-training rider and contains `sorry`-backed material, so it is not an admissible portable route under the corpus provenance policy.
- Current upstream was refreshed on 2026-09-07: `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` was the Mathlib `master` head at audit time and uses Lean 4.34.0-rc2.  Current-tree searches for the named missing theorem families did not add a complete owner beyond the pinned interfaces above.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers.  Strict whole-row semantics apply uniformly: a row is not promoted from a proper subset of its clauses or from a nearby representation lacking the required bridge.
