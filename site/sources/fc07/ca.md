---
title: "Appendix. Topology of Cell Complexes"
---

FC07 — Hatcher, *Algebraic Topology* — block `FC07-CA`.

32 units. 10 have a Lean owner; 22 do not.

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`unmatched`]{.route-unmatched} | 22 | 69% | No checked Lean owner was found. |
| [`mathlib`]{.route-mathlib} | 10 | 31% | Mathlib owns the unit outright. |
| **total** | **32** | | |

::: {.callout-note collapse="true"}
## How this chapter was searched

- Canonical source block: FC07 Hatcher Appendix, `FC07-CA-U001`–`FC07-CA-U032`, exactly 32 unique contiguous rows retrieved from [FC07 — Hatcher, Algebraic Topology](/sources/fc07/) through `agent-memory`.
- Search order followed the established FC07 contract: project source first at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream Mathlib `H=80cbd0498ab39e21d24d6730b3f932cec672a702` (Apache-2.0, Lean 4.34.0-rc2), current/open and indexed search, Reservoir/packages, broad discoverable Lean repositories, and local reference mirrors. No `project-existing`, `package-import`, or admissible `reference-port` owner was found.
- Every promoted Mathlib path exists at exact P and every promoted declaration was compiled through the project toolchain. Two nontrivial exact consequences were also compiled as local audit witnesses: U001’s skeletonwise weak-topology iff from [`CWComplex.closed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWComplex.closed#doc), and U023’s product-of-a-quotient-map theorem from [`IsQuotientMap.continuous_lift_prod_left`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IsQuotientMap.continuous_lift_prod_left#doc). Audit witnesses are evidence only, not project source.
- CA has 10 pinned positive rows and 22 dated unmatched rows. The positives are U001 (weak topology), U003 (characteristic-map CW criterion packaged as `CWComplex`), U018 (compact-open topology), U019 (compact-domain sup metric), U020 (evaluation/exponential-law continuity), U023 (quotient map × locally compact identity), U027 (simplicial set), U028 (singular complex), U030 (degenerate simplex), and U031 (geometric realization).
- U002 is deliberately not promoted from `facebookresearch/atlas-lean::Atlas/AlgebraicTopologyI/code/Section15.lean::CWSubcomplex.compact_subset_finite_subcomplex`: the declaration’s proof is `by sorry`. U011 likewise is not routed through Atlas’s `IsNeighborhoodRetract`: that declaration covers an already embedded Euclidean subset rather than Hatcher’s arbitrary-space existence-of-embedding predicate, and the repository license is CC BY-NC 4.0 with an additional no-training rider, so it is not treated as a portable source route.
- U024 remains unmatched after checking the Apache-2.0 LeanPool HEP development at `Vilin97/lean-pool` revision [`3fc79f0a795f19fffcc59eee3efaf5faa52de3c3`](https://github.com/leanprover-community/mathlib4/commit/3fc79f0a795f19fffcc59eee3efaf5faa52de3c3): it defines `HasHomotopyExtensionProperty`/`IsCofibration` and nearby retractions, but no checked iff identifies HEP with a retraction of `X × I` onto `X × {0} ∪ A × I`.
- U022 is not inferred from [`Homeomorph.curry`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Homeomorph.curry#doc): the pinned homeomorphism has stronger local-compactness assumptions than Hatcher’s exact Y-locally-compact, Z-Hausdorff theorem. U021 is not inferred from generic compactly-generated machinery without the stated product theorem.
- U031 is an equivalent categorical realization, not a name-only match: [`SSet.toTop`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.toTop#doc) is explicitly the geometric-realization functor, constructed as the left Kan extension of standard topological simplices along Yoneda, and `toTopSimplex` identifies representables with the corresponding topological simplices. This is the colimit presentation equivalent to the quotient by all simplex-structure identifications.
- U032 is deliberately not promoted. P and H have degreewise categorical products of simplicial sets, and current [`TopAdj.lean`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopAdj.lean#doc) equips the right adjoint [`TopCat.toSSet`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.toSSet#doc) with monoidal/product structure, but no checked declaration proves that geometric realization [`SSet.toTop`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.toTop#doc) preserves products. A TauCeti Lean source encountered in broad discovery explicitly leaves identifying realization with products for later work.
- Current upstream was refreshed on 2026-09-07; `H=80cbd0498ab39e21d24d6730b3f932cec672a702` remained the newest Mathlib HEAD observed and uses Lean 4.34.0-rc2. No new H endpoint closed the unmatched ENR/CW-local-contractibility/product-realization rows.
- This Appendix is the final canonical FC07 block: the catalogue contains no units after `FC07-CA-U032`. With CA promoted, FC07 Sweep II is complete.
- `N=2026-09-07` denotes a dated unmatched result after the prescribed search layers. Strict whole-row semantics are uniform: a proper subset of a multi-clause row, a hypothesis-mismatched theorem, an unproved declaration, or a licensing-incompatible external source is not credited as a route.
:::

### **Definition/convention — weak topology for CW complexes** {#fc07-ca-u001}

::: {.unit-meta}
`FC07-CA-U001` · Appendix — Topology of Cell Complexes; source L10136 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`mathlib`]{.route-mathlib}
:::

A CW complex X=⋃_nX^n has the weak topology: A⊂X is open (equivalently closed) iff A∩X^n is open (respectively closed) in each skeleton.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/CWComplex/Classical/Basic.lean::Topology.CWComplex.closed, Topology.RelCWComplex.skeleton, Topology.RelCWComplex.closedCell_subset_skeleton, Topology.RelCWComplex.isClosed_closedCell`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html) — [`CWComplex.closed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWComplex.closed#doc) is Mathlib’s cellwise weak-topology criterion. Together with the skeleton containment and closed-cell lemmas, it proves the equivalent Hatcher criterion that a subset is closed iff its intersection with every skeleton is relatively closed; that exact equivalence was compiled as an audit witness at P.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.1** {#fc07-ca-u002}

::: {.unit-meta}
`FC07-CA-U002` · Appendix — Topology of Cell Complexes; source L10150 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

A compact subspace of a CW complex is contained in a finite subcomplex.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A compact subspace of a CW complex is contained in a finite subcomplex. Atlas contains [`CWSubcomplex.compact_subset_finite_subcomplex`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWSubcomplex.compact_subset_finite_subcomplex#doc), but its body is `by sorry`; current Mathlib has only finite-indexed-subcomplex finiteness, not the compact-subset theorem. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.2** {#fc07-ca-u003}

::: {.unit-meta}
`FC07-CA-U003` · Appendix — Topology of Cell Complexes; source L10163 · [`mathlib`]{.route-mathlib}
:::

Let X be Hausdorff and Φ_α:D_α^n→X a family of maps. They are characteristic maps of a CW structure iff: (i) each Φ_α maps int D_α^n homeomorphically onto a cell, these cells are disjoint, and they cover X; (ii) each boundary image lies in a finite union of lower-dimensional cells; (iii) C⊂X is closed iff C meets the closure of every cell in a closed set.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/CWComplex/Classical/Basic.lean::Topology.CWComplex, Topology.CWComplex.pairwiseDisjoint, Topology.CWComplex.mapsTo, Topology.CWComplex.closed, Topology.CWComplex.union`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CWComplex/Classical/Basic.html) — `CWComplex` is precisely the characteristic-map presentation used in Proposition A.2: disk interiors map homeomorphically to pairwise-disjoint cells covering the complex, boundaries land in finitely many lower-dimensional cells, and [`CWComplex.closed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CWComplex.closed#doc) is the weak-topology closure criterion. This is the proposition’s data/axioms packaged as a structure rather than a separate iff theorem.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.3** {#fc07-ca-u004}

::: {.unit-meta}
`FC07-CA-U004` · Appendix — Topology of Cell Complexes; source L10181 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

CW complexes are normal, and in particular, Hausdorff.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: CW complexes are normal, and in particular, Hausdorff. Pinned/current CW APIs assume Hausdorffness for many closed-cell lemmas; no checked theorem derives normality or Hausdorffness for every CW complex. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.4** {#fc07-ca-u005}

::: {.unit-meta}
`FC07-CA-U005` · Appendix — Topology of Cell Complexes; source L10185 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

Each point in a CW complex has arbitrarily small contractible open neighborhoods, so CW complexes are locally contractible.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: Each point in a CW complex has arbitrarily small contractible open neighborhoods, so CW complexes are locally contractible. No checked theorem gives arbitrarily small contractible open neighborhoods or local contractibility for arbitrary CW complexes. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.5** {#fc07-ca-u006}

::: {.unit-meta}
`FC07-CA-U006` · Appendix — Topology of Cell Complexes; source L10191 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

For a subcomplex A of a CW complex X, the open neighborhood N_{ε} (A) deformation retracts onto A if ε_{α} < 1 for all α.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: For a subcomplex A of a CW complex X, the open neighborhood N_{ε} (A) deformation retracts onto A if ε_{α} < 1 for all α. Subcomplex and homotopy machinery exists, but no checked construction of Hatcher’s N_ε(A) and its deformation retraction was found. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — topology generated by subspaces** {#fc07-ca-u007}

::: {.unit-meta}
`FC07-CA-U007` · Appendix — Topology of Cell Complexes; source L10197 · [`unmatched`]{.route-unmatched}
:::

A space X is generated by subspaces X_α when X=⋃X_α and A⊂X is closed iff every A∩X_α is closed in X_α.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A space X is generated by subspaces X_α when X=⋃X_α and A⊂X is closed iff every A∩X_α is closed in X_α. [`TopologicalSpace.coinduced`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.coinduced#doc)/`generatedBy` provide generic final-topology machinery, but no checked named interface realizes the full specified-family-of-subspaces closure criterion. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Construction — compactly generated topology** {#fc07-ca-u008}

::: {.unit-meta}
`FC07-CA-U008` · Appendix — Products of CW Complexes; source L10205 · after [`FC07-CA-U007`](#fc07-ca-u007) · [`unmatched`]{.route-unmatched}
:::

For a space X, X_c is the topology generated by its compact subspaces; X and X_c have the same compact subsets, and locally compact spaces satisfy X=X_c.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: For a space X, X_c is the topology generated by its compact subspaces; X and X_c have the same compact subsets, and locally compact spaces satisfy X=X_c. [`TopologicalSpace.compactlyGenerated`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.compactlyGenerated#doc) and `CompactlyGeneratedSpace` formalize k-generation by compact Hausdorff probes, but no checked bundle proves Hatcher’s stated same-compact-subsets clause together with local-compact equality for X_c. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Theorem A.6** {#fc07-ca-u009}

::: {.unit-meta}
`FC07-CA-U009` · Appendix — Products of CW Complexes; source L10207 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

For CW complexes X and Y with characteristic maps Φ_{α} and Psi_{β}, the product maps Φ_{α} × Psi_{β} are the characteristic maps for a CW complex structure on (X × Y)_{c}. If either X or Y is compact or more generally locally compact, then (X × Y)_{c} = X × Y. Also, (X × Y)_{c} = X × Y if both X and Y have countably many cells.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: For CW complexes X and Y with characteristic maps Φ_{α} and Psi_{β}, the product maps Φ_{α} × Psi_{β} are the characteristic maps for a CW complex structure on (X × Y)*{c}. If either X or Y is compact or more generally locally compact, then (X × Y)*{c} = X × Y. Also, (X × Y)_{c} = X × Y if both X and Y have countably many cells. No checked product-CW theorem supplies Hatcher’s characteristic product cells together with the compactly-generated/product-topology coincidence clauses. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Theorem A.7** {#fc07-ca-u010}

::: {.unit-meta}
`FC07-CA-U010` · Appendix — Euclidean Neighborhood Retracts; source L10225 · [`unmatched`]{.route-unmatched}
:::

A compact subspace K of ℝ^{n} is a retract of some neighborhood iff K is locally contractible in the weak sense that for each x ∈ K and each neighborhood U of x in K there exists a neighborhood V ⊂ U of x such that the inclusion V ↪ U is nullhomotopic.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A compact subspace K of ℝ^{n} is a retract of some neighborhood iff K is locally contractible in the weak sense that for each x ∈ K and each neighborhood U of x in K there exists a neighborhood V ⊂ U of x such that the inclusion V ↪ U is nullhomotopic. No checked Lean theorem gives the compact-subset-of-Euclidean-space neighborhood-retract iff weak-local-contractibility criterion. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — Euclidean neighborhood retract** {#fc07-ca-u011}

::: {.unit-meta}
`FC07-CA-U011` · Appendix — Euclidean Neighborhood Retracts; source L10239 · after [`FC07-C00-U001`](c00.html#fc07-c00-u001) · [`unmatched`]{.route-unmatched}
:::

X is an ENR if it embeds in some ℝ^n as a retract of a neighborhood of its image.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: X is an ENR if it embeds in some ℝ^n as a retract of a neighborhood of its image. Atlas defines `IsNeighborhoodRetract` for an already embedded Euclidean subset, but it does not package Hatcher’s arbitrary-space embedding definition and its CC BY-NC/no-training license is not a portable project route. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Corollary A.8** {#fc07-ca-u012}

::: {.unit-meta}
`FC07-CA-U012` · Appendix — Euclidean Neighborhood Retracts; source L10241 · [`unmatched`]{.route-unmatched}
:::

A compact space is an ENR iff it can be embedded as a retract of a finite simplicial complex. Hence the homology groups and the fundamental group of a compact ENR are finitely generated.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A compact space is an ENR iff it can be embedded as a retract of a finite simplicial complex. Hence the homology groups and the fundamental group of a compact ENR are finitely generated. No checked theorem proves the stated ENR characterization/application. Atlas mentions nearby ENR facts but the relevant theorem bodies are `sorry`-backed or do not own this row. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Corollary A.9** {#fc07-ca-u013}

::: {.unit-meta}
`FC07-CA-U013` · Appendix — Euclidean Neighborhood Retracts; source L10245 · [`unmatched`]{.route-unmatched}
:::

Every compact manifold, with or without boundary, is an ENR.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: Every compact manifold, with or without boundary, is an ENR. No checked theorem proves the stated ENR characterization/application. Atlas mentions nearby ENR facts but the relevant theorem bodies are `sorry`-backed or do not own this row. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Corollary A.10** {#fc07-ca-u014}

::: {.unit-meta}
`FC07-CA-U014` · Appendix — Euclidean Neighborhood Retracts; source L10249 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

Every finite CW complex is an ENR.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: Every finite CW complex is an ENR. No checked theorem proves the stated ENR characterization/application. Atlas mentions nearby ENR facts but the relevant theorem bodies are `sorry`-backed or do not own this row. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — domination** {#fc07-ca-u015}

::: {.unit-meta}
`FC07-CA-U015` · Appendix — Spaces Dominated by CW Complexes; source L10255 · after [`FC07-C00-U003`](c00.html#fc07-c00-u003) · [`unmatched`]{.route-unmatched}
:::

Y is dominated by X if there are maps Y→^iX→^rY with ri≃id_Y.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: Y is dominated by X if there are maps Y→^iX→^rY with ri≃id_Y. Homotopy and homotopy equivalence are formalized, but no checked `dominated` predicate packages maps Y→X→Y with composite homotopic to id. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.11** {#fc07-ca-u016}

::: {.unit-meta}
`FC07-CA-U016` · Appendix — Spaces Dominated by CW Complexes; source L10257 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

A space dominated by a CW complex is homotopy equivalent to a CW complex.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A space dominated by a CW complex is homotopy equivalent to a CW complex. No checked domination-to-CW or compact-manifold-to-CW homotopy-equivalence theorem was found. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Corollary A.12** {#fc07-ca-u017}

::: {.unit-meta}
`FC07-CA-U017` · Appendix — Spaces Dominated by CW Complexes; source L10271 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008) · [`unmatched`]{.route-unmatched}
:::

A compact manifold is homotopy equivalent to a CW complex.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A compact manifold is homotopy equivalent to a CW complex. No checked domination-to-CW or compact-manifold-to-CW homotopy-equivalence theorem was found. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — compact-open topology** {#fc07-ca-u018}

::: {.unit-meta}
`FC07-CA-U018` · Appendix — The Compact-Open Topology; source L10289 · [`mathlib`]{.route-mathlib}
:::

On the mapping space X^Y, the compact-open topology has subbasis M(K,U)={f:f(K)⊂U} for compact K⊂Y and open U⊂X.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/CompactOpen.lean::ContinuousMap.compactOpen, ContinuousMap.compactOpen_eq, ContinuousMap.isOpen_setOfPred_mapsTo`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html) — [`ContinuousMap.compactOpen`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ContinuousMap.compactOpen#doc) is generated by the subbasic sets of continuous maps carrying a compact K into an open U; `compactOpen_eq` and `isOpen_setOfPred_mapsTo` expose exactly Hatcher’s M(K,U) definition.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.13** {#fc07-ca-u019}

::: {.unit-meta}
`FC07-CA-U019` · Appendix — The Compact-Open Topology; source L10293 · [`mathlib`]{.route-mathlib}
:::

If X is a metric space and Y is compact, then the compact-open topology on X^{Y} is the same as the metric topology defined by the metric d (f, g) = {s u p }_{y ∈ Y} d (f (y), g (y)).

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/UniformSpace/CompactConvergence.lean::ContinuousMap.compactConvergenceUniformSpace, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/CompactConvergence.html); [`Mathlib/Topology/ContinuousMap/Compact.lean::ContinuousMap.instMetricSpace, ContinuousMap.dist_eq_iSup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousMap/Compact.html) — Pinned Mathlib identifies compact convergence on continuous maps with the compact-open topology; for compact domain and metric codomain the induced metric on `C(Y,X)` satisfies `dist f g = ⨆ y, dist (f y) (g y)`. Thus the compact-open topology is exactly Hatcher’s sup-metric topology.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.14** {#fc07-ca-u020}

::: {.unit-meta}
`FC07-CA-U020` · Appendix — The Compact-Open Topology; source L10301 · [`mathlib`]{.route-mathlib}
:::

For the compact-open topology: (a) evaluation e:X^Y×Y→X, e(f,y)=f(y), is continuous when Y is locally compact; (b) if f:Y×Z→X is continuous then its adjoint hat(f):Z→X^Y is continuous; (c) the converse to (b) holds when Y is locally compact.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/CompactOpen.lean::ContinuousEval, continuous_eval, ContinuousMap.curry, ContinuousMap.continuous_of_continuous_uncurry, ContinuousMap.continuous_uncurry_of_continuous`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html) — `ContinuousEval`/`continuous_eval` give joint evaluation continuity under the locally-compact-pair hypothesis (hence for locally compact Y). `continuous_of_continuous_uncurry` gives the adjoint direction without local compactness, while `continuous_uncurry_of_continuous` gives the converse when Y is locally compact. These are exactly parts (a)–(c), up to product-coordinate order.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.15** {#fc07-ca-u021}

::: {.unit-meta}
`FC07-CA-U021` · Appendix — The Compact-Open Topology; source L10318 · [`unmatched`]{.route-unmatched}
:::

If X is a compactly generated Hausdorff space and Y is locally compact, then the product topology on X × Y is compactly generated.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: If X is a compactly generated Hausdorff space and Y is locally compact, then the product topology on X × Y is compactly generated. `CompactlyGeneratedSpace` and locally compact instances exist, but no checked theorem proves the product of a compactly generated Hausdorff space with an arbitrary locally compact space is compactly generated. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.16** {#fc07-ca-u022}

::: {.unit-meta}
`FC07-CA-U022` · Appendix — The Compact-Open Topology; source L10326 · [`unmatched`]{.route-unmatched}
:::

The map X^{Y × Z} {→ } (X^{Y})^{Z}, f ↦ {hat(f) }, is a homeomorphism if Y is locally compact Hausdorff and Z is Hausdorff.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: The map X^{Y × Z} {→ } (X^{Y})^{Z}, f ↦ {hat(f) }, is a homeomorphism if Y is locally compact Hausdorff and Z is Hausdorff. [`Homeomorph.curry`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Homeomorph.curry#doc) gives an exponential-law homeomorphism only under stronger local-compactness hypotheses on both factors; no checked theorem matches Hatcher’s Y-locally-compact, Z-Hausdorff hypothesis bundle. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Proposition A.17** {#fc07-ca-u023}

::: {.unit-meta}
`FC07-CA-U023` · Appendix — The Compact-Open Topology; source L10336 · [`mathlib`]{.route-mathlib}
:::

If f: X {→ } Y is a quotient map then so is f × 1: X × Z → Y × Z whenever Z is locally compact.

::: {.unit-lean}
**In Lean.** [`Mathlib/Topology/CompactOpen.lean::Topology.IsQuotientMap.continuous_lift_prod_left`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/CompactOpen.html#Topology.IsQuotientMap.continuous_lift_prod_left); [`Mathlib/Topology/Maps/Basic.lean::isQuotientMap_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Maps/Basic.html); [`Mathlib/Topology/Order.lean::isOpen_iff_continuous_mem`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order.html) — `continuous_lift_prod_left` is the locally-compact product lifting property for a quotient map. Combining it with the Sierpiński-space characterization of open sets and the quotient-map criterion gives exactly that `f × id_Z` is quotient for locally compact Z; the complete theorem was compiled as an audit witness at P.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.18** {#fc07-ca-u024}

::: {.unit-meta}
`FC07-CA-U024` · Appendix — The Homotopy Extension Property; source L10354 · [`unmatched`]{.route-unmatched}
:::

A pair (X, A) has the homotopy extension property if and only if X × {0 } ∪ A × I is a retract of X × I.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A pair (X, A) has the homotopy extension property if and only if X × {0 } ∪ A × I is a retract of X × I. LeanPool formalizes topological HEP/cofibration predicates, but no checked theorem proves HEP iff X×{0}∪A×I is a retract of X×I. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — regular CW complex and simplicial complex** {#fc07-ca-u025}

::: {.unit-meta}
`FC07-CA-U025` · Appendix — Simplicial CW Structures; source L10376 · after [`FC07-C00-U008`](c00.html#fc07-c00-u008), [`FC07-C00-U015`](c00.html#fc07-c00-u015) · [`unmatched`]{.route-unmatched}
:::

A CW complex is regular if characteristic maps can be chosen embeddings. A simplicial complex is a regular unordered Δ-complex in which each simplex is uniquely determined by its vertices.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A CW complex is regular if characteristic maps can be chosen embeddings. A simplicial complex is a regular unordered Δ-complex in which each simplex is uniquely determined by its vertices. Simplicial complexes and CW complexes exist separately, but no checked regular-CW predicate plus Hatcher’s unique-vertex-determined characterization owns the entire row. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition/construction — singular Δ-complex** {#fc07-ca-u026}

::: {.unit-meta}
`FC07-CA-U026` · Appendix — Simplicial CW Structures; source L10378 · [`unmatched`]{.route-unmatched}
:::

A singular Δ-complex (sΔ-complex) broadens a Δ-complex by allowing simplices to be attached along arbitrary simplicial maps, hence supports quotient and attachment constructions.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: A singular Δ-complex (sΔ-complex) broadens a Δ-complex by allowing simplices to be attached along arbitrary simplicial maps, hence supports quotient and attachment constructions. No checked singular-Δ-complex interface allowing arbitrary simplicial attaching maps was found. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — simplicial set** {#fc07-ca-u027}

::: {.unit-meta}
`FC07-CA-U027` · Appendix — Simplicial CW Structures; source L10394 · after [`FC07-C02-U078`](c02.html#fc07-c02-u078), [`FC07-C02-U079`](c02.html#fc07-c02-u079) · [`mathlib`]{.route-mathlib}
:::

Let Δ_* be the category of finite ordered simplices with order-preserving maps. A simplicial set is a contravariant functor Δ_*→Sets.

::: {.unit-lean}
**In Lean.** [`Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean::SSet`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Basic.html) — `SSet` abbreviates simplicial objects in `Type`, i.e. functors `SimplexCategoryᵒᵖ ⥤ Type`, exactly contravariant functors from finite ordered simplices to sets.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Construction — singular complex** {#fc07-ca-u028}

::: {.unit-meta}
`FC07-CA-U028` · Appendix — Simplicial CW Structures; source L10396 · after [`FC07-CA-U027`](#fc07-ca-u027), [`FC07-C02-U010`](c02.html#fc07-c02-u010) · [`mathlib`]{.route-mathlib}
:::

For a space X, the singular complex S(X) is the simplicial set whose n-simplices are all continuous maps Δ^n→X, with structure maps by precomposition.

::: {.unit-lean}
**In Lean.** [`Mathlib/AlgebraicTopology/SingularSet.lean::TopCat.toSSet, TopCat.toSSetObjEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularSet.html) — [`TopCat.toSSet`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.toSSet#doc) is the singular simplicial set. `toSSetObjEquiv` identifies its n-simplices with continuous maps from the standard topological n-simplex to X, and functoriality is precomposition by simplex maps.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Proposition A.19** {#fc07-ca-u029}

::: {.unit-meta}
`FC07-CA-U029` · Appendix — Simplicial CW Structures; source L10400 · after [`FC07-CA-U027`](#fc07-ca-u027) · [`unmatched`]{.route-unmatched}
:::

Every simplicial set is isomorphic to one of the form Δ (X) for some s complex X which is unique up to isomorphism.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: Every simplicial set is isomorphic to one of the form Δ (X) for some s complex X which is unique up to isomorphism. Pinned Mathlib realizes simplicial sets as presheaves and has geometric realization, but no checked sΔ-complex reconstruction/uniqueness theorem realizes Proposition A.19. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

### **Definition — degenerate simplex** {#fc07-ca-u030}

::: {.unit-meta}
`FC07-CA-U030` · Appendix — Simplicial CW Structures; source L10404 · after [`FC07-CA-U027`](#fc07-ca-u027) · [`mathlib`]{.route-mathlib}
:::

An n-simplex of a simplicial set is degenerate if it lies in the image of a structure map induced by a noninjective (equivalently surjective after factorization) simplex map.

::: {.unit-lean}
**In Lean.** [`Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.lean::SSet.degenerate, SSet.mem_degenerate_iff, SSet.degenerate_eq_iUnion_range_σ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Degenerate.html) — [`SSet.degenerate`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.degenerate#doc) defines an n-simplex to lie in the range of a structure map to lower dimension; `mem_degenerate_iff` factors through an epi/surjective simplex map, and `degenerate_eq_iUnion_range_σ` gives the usual degeneracy-map formulation.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Construction — geometric realization** {#fc07-ca-u031}

::: {.unit-meta}
`FC07-CA-U031` · Appendix — Simplicial CW Structures; source L10408 · [`mathlib`]{.route-mathlib}
:::

For a simplicial set Y, its geometric realization \

::: {.unit-lean}
**In Lean.** [`Mathlib/AlgebraicTopology/SingularSet.lean::SSet.toTop, SSet.toTopSimplex, sSetTopAdj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SingularSet.html) — [`SSet.toTop`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.toTop#doc) is explicitly Mathlib’s geometric-realization functor, defined as the left Kan extension of the standard topological simplex along Yoneda; `toTopSimplex` identifies representables with standard simplices. This is the categorical colimit form of Hatcher’s quotient of all Y_n × Δ^n by the structure-map identifications.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### **Construction — product of simplicial sets** {#fc07-ca-u032}

::: {.unit-meta}
`FC07-CA-U032` · Appendix — Simplicial CW Structures; source L10420 · after [`FC07-CA-U027`](#fc07-ca-u027), [`FC07-CA-U031`](#fc07-ca-u031) · [`unmatched`]{.route-unmatched}
:::

The product simplicial set has (X×Y)_n=X_n×Y_n with structure maps acting componentwise, and geometric realization preserves this product (with the compactly generated CW topology).

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No checked project/P/H/open/external/indexed Lean declaration realizes the whole source row: The product simplicial set has (X×Y)_n=X_n×Y_n with structure maps acting componentwise, and geometric realization preserves this product (with the compactly generated CW topology). Degreewise products of simplicial sets are available categorically, but neither P nor current H proves that [`SSet.toTop`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=SSet.toTop#doc) preserves products; current `TopAdj` equips the right adjoint [`TopCat.toSSet`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopCat.toSSet#doc), not realization, with monoidal/product structure. Strict bundle semantics reject specializations, stronger/weaker hypothesis substitutions, adjacent constructions, isolated clauses/examples, `sorry`-backed results, and nonportable source-only near-matches.
:::

