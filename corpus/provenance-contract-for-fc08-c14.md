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

- Canonical source block: FC08 Lee, Chapter 14, `FC08-C14-U001`–`FC08-C14-U045`, exactly 45 unique catalogue rows.
- The 2026-09-14 `remap-strict-bundle` pass uses clause-wise exact-route semantics. Multi-index notation, concrete alternating-form bases, wedge/pullback constructions, differential-form sections, and Euclidean exterior calculus are mapped through their actual algebra/calculus owners rather than rejected for lack of Lee-specific wrappers.
- Current route totals regenerated from the table are `mathlib` 30, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 15; total 45. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`; current upstream was inspected at `H=87befc843c2b3a1be12f7fe9ba274d212b544348`.
- The algebraic alternating-form layer is substantially complete. `AlternatingMap`, `alternatization`, determinant alternating maps, `Module.Basis.ext_alternating`, ordered finite-index combinatorics, `AlternatingMap.domCoprod`, and `curryLeft` route Lee's alternation, elementary forms, basis/dimension, wedge definition, decomposable forms, and contraction definitions. The increasing elementary forms are recognized by their Kronecker evaluation matrix; `Nat.choose` supplies the dimension count.
- Two concrete algebraic theorem packages remain residual rather than inferred: U016 asks for the complete associative/graded-commutative determinant-convention wedge laws on the scalar `AlternatingMap` realization, and U022(b) asks for the graded contraction Leibniz rule. Mathlib has the abstract `ExteriorAlgebra`, the universal `exteriorPower.alternatingMapLinearEquiv`, and the pairing `exteriorPower.pairingDual`, but no checked algebra equivalence transporting Lee's concrete scalar alternating-map wedge into the abstract exterior algebra. Exact live searches found no separate proof-complete owner. U018 therefore remains blocked by the same concrete compatibility.
- The manifold differential-form layer no longer has the old tensor-bundle obstruction. FC08 C12's recursive smooth hom-bundles give covariant tensor bundles and smooth tensor fields, so U023 is the alternating fiberwise subspace/section predicate; pointwise wedge and pullback are finite smooth operations on those sections. U024–U031 are therefore routed through the C12 tensor bundle/pullback machinery plus the alternating-map wedge and top-degree determinant law.
- Current Mathlib has a genuine exterior derivative implementation on normed vector spaces in `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`: `extDeriv`, `extDerivWithin`, linearity, the 0-form formula, explicit evaluation, `extDeriv_extDeriv`, and `extDeriv_pullback`. `DifferentialForm/VectorField.lean` proves the invariant formula with Lie brackets. These route U033 and U039 and provide strong local-model evidence for U034/U040/U042.
- The Euclidean proposition U034 is not fully promoted because Mathlib does not presently state/prove the graded wedge Leibniz rule for `extDeriv` against `AlternatingMap.domCoprod`; its other three clauses (linearity, `d²=0`, pullback naturality) are exact native theorems. Live search found only Atlas's manifold differential-form file for the missing Leibniz implementation.
- There is still no proof-complete global exterior derivative on arbitrary manifolds in current Mathlib or TauCeti. TauCeti current `Geometry/Manifold/TwoForm.lean` explicitly records this limitation while providing a smooth rank-two form specialization. Atlas `v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean` defines a candidate manifold `d`, Cartan machinery, and related formulas, but the inspected file contains 15 `sorry` obligations, including obligations in the global exterior-derivative development, so it is not an admissible route.
- Consequently U032, U035–U038 and U040–U045 remain theorem/object-level residuals exactly at the global manifold differential/Lie-derivative boundary. Mathlib's vector-space invariant formula is recorded in U040/U042 as partial evidence rather than being silently generalized through charts. Search errors/timeouts are never negative evidence.
