---
type: reference
title: Provenance contract for FC08 C14
description: '# Provenance contract for FC08 C14'
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
# Provenance contract for FC08 C14

# Provenance contract for FC08 C14

- Canonical source block: FC08 Lee, Chapter 14, `FC08-C14-U001`–`FC08-C14-U045`, exactly 45 unique contiguous rows retrieved from [[foundational-corpus-units-fc08-lee|FC08 — John M. Lee, Introduction to Smooth Manifolds]] through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then targeted indexed/external Lean searches. Project search found exterior-algebra consumers/contraction lemmas but no source-row owner; no `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- C14 has 10 pinned `mathlib` rows and 35 dated `unmatched` rows. Positive rows are: U001, U002, U003, U005, U007, U012, U013, U014, U019, U021.
- The algebraic alternating-map layer is strong. `AlternatingMap` directly represents scalar exterior forms; `map_linearDependent` and the defining repeated-input axiom give Lee’s equivalent alternating criteria. `MultilinearMap.alternatization` is the unnormalized signed permutation sum and `AlternatingMap.coe_alternatization` supplies the exact `k!` factor, so Lee’s normalized `Alt` and its projection property are short checked assemblies. `/tmp/fc08-c14-witness.lean` compiles U002/U003/U005 at exact P.
- Elementary forms and top-degree determinant behavior also have direct checked realizations. `Matrix.detRowAlternating` composed with selected coordinate covectors gives Lee’s determinant elementary form (U007). `AlternatingMap.eq_smul_basis_det` plus `Basis.det_comp` gives the top-degree transformation law (U012). Both assemblies compile in the witness.
- `AlternatingMap.domCoprod` is explicitly Mathlib’s exterior product and uses the signed shuffle formula. For scalar forms, composing with `TensorProduct.lid` and reindexing along `finSumFinEquiv` gives Lee’s determinant-convention wedge; `MultilinearMap.domCoprod_alternization_eq` verifies the factorial normalization. U013/U014 are therefore promoted. Lee’s alternate convention U019 is the corresponding normalized alternation of `MultilinearMap.domCoprod`, also compiled in the witness.
- `AlternatingMap.curryLeft` is exactly interior multiplication by fixing the first argument, so U021 is promoted. `curryLeft_same` proves U022(a), but no checked Leibniz rule against the scalar specialized wedge was found; strict whole-row semantics keep U022 unmatched.
- A deliberate representation boundary blocks several tempting algebraic promotions. Mathlib has `ExteriorAlgebra`, `Module.Basis.exteriorPower`, `exteriorPower.finrank_eq`, and grading machinery, but targeted P/H searches found no checked finite-dimensional equivalence identifying the abstract exterior powers of `V*` with the scalar-valued `AlternatingMap` realization used by Lee. U011/U018 and dependent coordinate/algebra laws are not inferred across that missing bridge.
- The manifold half remains absent. P and H have `Topology/VectorBundle/ContinuousAlternatingMap.lean`, which constructs a topological bundle of continuous alternating maps between vector-bundle fibers, but no smooth `ContMDiff` alternating-map bundle or manifold `DifferentialForm` section API. Moreover, Lee’s FC08 tangent/cotangent spaces remain the point-derivation model from C03/C11 with no checked bridge to Mathlib’s standard `TangentSpace`. Thus U023–U031 are unmatched.
- Exact P/H searches also find no manifold exterior-derivative layer: no smooth differential-form `d`, invariant exterior-derivative formula, Cartan magic formula, or Lie-derivative/exterior-derivative package. U032–U045 remain unmatched rather than being reconstructed from vector-space calculus and Lie-bracket ingredients.
- Current-H file search shows the same relevant manifold surface: `Topology/VectorBundle/ContinuousAlternatingMap.lean` but no geometry/manifold differential-form implementation. Targeted external indexed search did not surface a compatible Lean owner; one current categorical-differential-geometry project describes de Rham cohomology only as a long-term goal rather than a replacement implementation.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.

