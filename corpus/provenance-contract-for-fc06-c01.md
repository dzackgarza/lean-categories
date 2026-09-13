---
type: reference
title: Provenance contract for FC06 C01
description: '# Provenance contract for FC06 C01'
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
# Provenance contract for FC06 C01

# Provenance contract for FC06 C01

## Provenance contract for FC06 C01

- Canonical source block: FC06 Hartshorne, Chapter I, `FC06-C01-U001`–`FC06-C01-U147`, in canonical source-ID order. The canonical unit extraction was preserved; no completed FC05 block was touched.
- Project-first inspection was refreshed at repository HEAD `A=cd74b69e97f743cd7318a9fe130ed2a749860b3f`. The only complete project-owned C01 row promoted here is U138, `LeanCategories/Algebra/DimensionTheory.lean::LeanCategories.Algebra.HilbertFunction`. Project-local reuse crosses no external import/license boundary; no standalone repository license file was present in the checked tree.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every P declaration promoted in the table was inspected at that exact revision.
- Current Mathlib was refreshed again on 2026-09-13 at `H=87befc843c2b3a1be12f7fe9ba274d212b544348` (after the 2026-09-06 check at `5aedf732...`). Current-master searches remain negative for a classical `Projectivization` ↔ `ProjectiveSpectrum` closed-point/topology bridge and for graded-module shift/annihilator bundling. Post-pin declarations are recorded only as reference evidence, never silently credited as pinned Mathlib.
- The substantial FC06-C01 probes already recorded by the concurrent lean-categories audit were reused rather than rerun. Fresh searches in this pass were restricted to gaps left by those recordings (notably exact pinned declaration boundaries for Nullstellensatz, separable generation, DVR/Dedekind, cotangent dimension, and the numerical-polynomial/binomial-basis family).
- Strict bundle semantics govern every row. A route must own the complete stable-ID statement. A theorem for one clause, one example, a specialization, an unbridged classical/scheme analogue, or a result with stronger hypotheses than the source is recorded as adjacent evidence but is not promoted as the row.
- In particular, scheme-theoretic affine/projective/rational-map infrastructure is not used indiscriminately as a replacement for Hartshorne's classical point-set variety interfaces. U071, U072 and U074 are credited because the pinned scheme interfaces are the direct general constructions/theorems and specialize to the integral schemes attached to varieties; broader bundled classical dictionaries (U057–U068, U075–U077) remain unmatched without the missing bridge/equivalence theorem.
- U019 remains unmatched even though `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` proves existence of a representing affine point: the audited pinned interface does not package the source's full unique-point correspondence as the row states it.
- U034 is credited from the pinned principal-ideal-height theorems under precisely the source noetherian/non-zero-divisor hypotheses. U035 is the exact pinned height-one-prime characterization of UFDs.
- U078 remains unmatched despite `Field.exists_primitive_element`: the source additionally requires the primitive element to be chosen as a linear combination of an arbitrary finite generating set. `primitive_element_inf_aux` constructs `α+cβ` internally but does not expose the full finite-set strengthening as a stable declaration. U079 is represented exactly by `IsTranscendenceBasis` plus `Algebra.IsSeparable`, and U081 is the direct perfect-field theorem in `SeparablyGenerated.lean`.
- U099 is the direct `AdicCompletion` construction, but U100 remains unmatched because the source bundles locality/injectivity, finite-module tensor completion, dimension preservation and regularity preservation/reflection; only a proper subset is present in the checked pinned completion API. Indexed Lean search on 2026-09-06 found no Cohen structure theorem for U101; the only relevant FLT search hit explicitly stated its absence.
- U109–U116 are covered by pinned valuation/DVR/Dedekind interfaces. Mathlib uses an equivalent multiplicative/cyclic-value-group presentation in parts of the API and includes fields in `IsDedekindDomain` via dimension ≤ 1; the source's additive valuation convention and dimension-one/nonfield hypotheses identify the intended special cases. U117 is deliberately not promoted because the pinned integral-closure Dedekind theorem requires separability while Hartshorne states arbitrary finite extension.
- U133–U134 were searched separately in P, H and indexed GitHub Lean sources on 2026-09-06. P/H contain binomial-ring material and bibliographic references to integer-valued polynomials but no Hartshorne numerical-polynomial predicate or its binomial-basis/discrete-integration theorem. Indexed exact-phrase Lean search returned no match.
- U138 is project-existing. U139–U140 are not inferred from `Mathlib/RingTheory/Polynomial/HilbertPoly.lean`: that file's object is rational-power-series data and its documentation leaves graded-module Hilbert polynomials for future work. U141–U147 therefore remain unmatched as complete Hartshorne projective-degree/intersection bundles. Historical Atlas/TauCeti analogues found by the recorded audit are not promoted because the required exact semantics/package compatibility/license/toolchain route was not established; narrower plane-curve material also does not own U143–U144.
- Open Mathlib PR searches recorded on 2026-09-06 for Hilbert polynomial graded module, Hartshorne variety, Bézout/intersection multiplicity, function-field curves and separating transcendence bases returned no route completing the missing rows. Targeted indexed Lean searches likewise found no algebraic-geometric blowup implementation matching U083–U091; Mathlib's Rees-algebra source only contains a future-facing blowup comment.
- `N=2026-09-06` marks a dated unmatched decision after project-first, P, H/current, recorded open/current work, indexed search services and relevant external Lean checks. Each unmatched row records the exact A/P/H revisions checked and `none` as its Lean target because no complete path/declaration exists.

- 2026-09-13 remap note: public GitHub/Reservoir discovery was refreshed for the classical projective-space bridge. Hits included general projectivization topology/incidence projects and scheme formalizations, but no checked compatible Lean development identifying Mathlib `Projectivization` with the closed-point subspace of `ProjectiveSpectrum` or computing `Proj.basicOpenIsoSpec` as Hartshorne’s homogeneous-coordinate ratio chart. Rows U042–U048 now record that missing comparison explicitly rather than rejecting partial clauses under the former strict-bundle rule.
