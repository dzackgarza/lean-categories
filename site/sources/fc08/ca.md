---
title: "FC08 — John M. Lee, Introduction to Smooth Manifolds, 2nd ed. (2013)"
---

FC08 — Lee, *Introduction to Smooth Manifolds*.

This chapter contains 55 definitions, 7 theorems, 21 propositions, 4 lemmas, 1 corollary, 5 examples, 5 constructions and 3 conventions.

Of the 101 statements checked against Lean, 54 are formalized somewhere and 47 are not.

| Status | Statements | Share | What it means |
| --- | ---: | ---: | --- |
| [in Mathlib]{.route-mathlib} | 54 | 53% | Mathlib states and proves it. |
| [not formalized]{.route-unmatched} | 47 | 47% | A documented search found no Lean statement of it anywhere. |
| **checked in total** | **101** | | |

::: {.callout-note collapse="true"}
## Which versions of Lean and Mathlib were searched

- Canonical source block: FC08 Lee, Appendix A, `FC08-CA-U001`–`FC08-CA-U101`, exactly 101 unique contiguous rows from the canonical FC08 unit catalogue.
- Search order: project `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0; Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0; Lean 4.34.0-rc2), then indexed/current/external Lean search. Existing FC02/FC07 topology mappings were used only as search leads; every cited Mathlib file was revalidated at exact P before promotion.
- Result: 54 pinned `mathlib` rows and 47 dated `unmatched` rows. Positive IDs: U001, U002, U004, U005, U007, U008, U010, U011, U012, U014, U015, U016, U017, U018, U019, U020, U021, U022, U025, U029, U030, U031, U032, U033, U038, U039, U040, U042, U047, U049, U051, U056, U060, U061, U063, U065, U067, U069, U070, U075, U076, U077, U078, U080, U081, U082, U083, U084, U085, U088, U093, U096, U097, U101.
- The strongest direct matches are native topology/metric/basis/subspace/quotient definitions, the exact `CompactExhaustion` structure and construction, native homotopy/path-class/fundamental-group objects, and the pinned covering lifting criterion.
- Lee’s special “neighborhood = open neighborhood” convention is not conflated with Mathlib’s generic neighborhood-filter membership. `nhds_basis_opens` is used only where an open-neighborhood basis itself is the source object.
- Large bundled propositions (subspace/product/disjoint-union/quotient/connectedness/compactness properties) remain unmatched when Mathlib only supplies the clauses separately. Likewise Lee’s definition of a proper map allows discontinuous maps, whereas Mathlib `IsProperMap` includes continuity; U073 is therefore not identified with it. U077 is mapped only because the source assumes continuity and a locally compact Hausdorff target, so the compact-preimage characterization bridges to `IsProperMap`.
- FC07’s TauCeti reference-port evidence was reconsidered for U098–U100, but no short compatible bridge from Lee’s locally-simply-connected convention to the later package’s universal-cover hypotheses plus the full uniqueness statement was found; these rows remain unmatched rather than silently changing hypotheses.
- `N=2026-09-07` marks all negative decisions; strict whole-row semantics apply uniformly.
:::

### Definition/convention — open subsets {#fc08-ca-u001}

::: {.unit-meta}
`FC08-CA-U001` · Appendix A, § Topological Spaces; source L17896 · [in Mathlib]{.route-mathlib}
:::

Let $X$ be a set. A topology on $X$ is a collection $\mathcal{T}$ of subsets of $X$, called open subsets, such that (i) $X$ and $\emptyset$ are open; (ii) the union of any family of open subsets is open; and (iii) the intersection of any finite family of open subsets is open. A pair $(X,\mathcal{T})$ is called a topological space.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::TopologicalSpace, IsOpen`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — `TopologicalSpace` is exactly a family of open sets closed under arbitrary unions and finite intersections; `IsOpen` names membership in it.
:::

### Definition/convention — topological space {#fc08-ca-u002}

::: {.unit-meta}
`FC08-CA-U002` · Appendix A, § Topological Spaces; source L17904 · [in Mathlib]{.route-mathlib}
:::

A pair .X; T / consisting of a set X together with a topology T on X is called a topological space. Ordinarily, when the topology is understood, one omits mention of it and simply says “X is a topological space.”

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::TopologicalSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — A `TopologicalSpace X` is precisely Lee’s topology datum on the underlying type.
:::

### Definition/convention — neighborhood of p {#fc08-ca-u003}

::: {.unit-meta}
`FC08-CA-U003` · Appendix A, § Topological Spaces; source L17910 · [not formalized]{.route-unmatched}
:::

A neighborhood of p is an open subset containing p. Similarly, a neighborhood of the set S is an open subset containing S. (Be warned that some authors use the word “neighborhood” in the more general sense of a subset containing an open subset containing p or S.)

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Lee intentionally reserves “neighborhood” for an open set containing the point/set; Mathlib’s generic neighborhood notion is filter membership and includes nonopen supersets. `nhds_basis_opens` gives the canonical open basis but does not identify the two terminology conventions. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — closed {#fc08-ca-u004}

::: {.unit-meta}
`FC08-CA-U004` · Appendix A, § Topological Spaces; source L17912 · [in Mathlib]{.route-mathlib}
:::

S is said to be closed if X setminus S is open (where X setminus S denotes the set difference x ∈ X : x not ∈ S ) .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::IsClosed`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — `IsClosed s` is defined by openness of the complement, exactly Lee’s convention.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u005}

::: {.unit-meta}
`FC08-CA-U005` · Appendix A, § Topological Spaces; source L17914 · [in Mathlib]{.route-mathlib}
:::

The interior of S , denoted by Int S, is the union of all open subsets of X contained in S.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::interior`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — `interior s` is the greatest open subset of `s`, equivalently the union of all open subsets contained in `s`.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u006}

::: {.unit-meta}
`FC08-CA-U006` · Appendix A, § Topological Spaces; source L17916 · [not formalized]{.route-unmatched}
:::

The exterior of S , denoted by Ext S, is the union of all open subsets of X contained in $X \setminus S$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The source packages a named relative/exterior construction in a convention not represented by one checked declaration with the same interface; it is expressible from interior/complement or subtype topology, but that expression would be reconstruction. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — source terminology/construction {#fc08-ca-u007}

::: {.unit-meta}
`FC08-CA-U007` · Appendix A, § Topological Spaces; source L17918 · [in Mathlib]{.route-mathlib}
:::

The closure of S , denoted by bar(S) , , is the intersection of all closed subsets of X containing S.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::closure`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — `closure s` is the least closed superset of `s`, equivalent to Lee’s intersection-of-all-closed-supersets definition.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u008}

::: {.unit-meta}
`FC08-CA-U008` · Appendix A, § Topological Spaces; source L17920 · [in Mathlib]{.route-mathlib}
:::

The boundary of S , denoted by @S, is the set of all points of X that are in neither Int S nor Ext S.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::frontier`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html); [`Mathlib/Topology/Closure.lean::frontier_eq_inter_compl_interior`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Closure.html) — `frontier` is Lee’s boundary; `frontier_eq_inter_compl_interior` identifies it exactly with points in neither the interior nor the exterior.
:::

### Definition/convention — an isolated point of S {#fc08-ca-u009}

::: {.unit-meta}
`FC08-CA-U009` · Appendix A, § Topological Spaces; source L17922 · [not formalized]{.route-unmatched}
:::

A point p ∈ S is said to be an isolated point of S if p has a neighborhood U ⊆ X such that U ∩ S = p

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The source packages a named relative/exterior construction in a convention not represented by one checked declaration with the same interface; it is expressible from interior/complement or subtype topology, but that expression would be reconstruction. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — a limit point of S {#fc08-ca-u010}

::: {.unit-meta}
`FC08-CA-U010` · Appendix A, § Topological Spaces; source L17924 · [in Mathlib]{.route-mathlib}
:::

point $p \in X$ (not necessarily in S ) is said to be a limit point of S if every neighborhood of p contains at least one point of S other than p.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/ClusterPt.lean::accPt_iff_nhds`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ClusterPt.html) — For the principal filter of `S`, `accPt_iff_nhds` says every neighborhood contains a distinct point of `S`, exactly Lee’s limit-point condition.
:::

### Definition/convention — dense in X {#fc08-ca-u011}

::: {.unit-meta}
`FC08-CA-U011` · Appendix A, § Topological Spaces; source L17926 · [in Mathlib]{.route-mathlib}
:::

S is said to be dense in X if ${ \overline { { S } } } = X$ , or equivalently if every nonempty open subset of X contains at least one point

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Closure.lean::Dense, dense_iff_closure_eq, dense_iff_inter_open`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Closure.html) — Mathlib gives both source characterizations: closure equal to the whole space and intersection with every nonempty open set.
:::

### Definition/convention — nowhere dense in X {#fc08-ca-u012}

::: {.unit-meta}
`FC08-CA-U012` · Appendix A, § Topological Spaces; source L17928 · [in Mathlib]{.route-mathlib}
:::

S is said to be nowhere dense in X if Sx contains no nonempty open subset.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/GDelta/Basic.lean::IsNowhereDense`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/GDelta/Basic.html) — `IsNowhereDense s` is defined by `interior (closure s) = ∅`, exactly the source convention.
:::

### Definition/convention — next {#fc08-ca-u013}

::: {.unit-meta}
`FC08-CA-U013` · Appendix A, § Topological Spaces; source L17930 · [not formalized]{.route-unmatched}
:::

The most important concepts of topology are continuous maps and convergent sequences, which we define next. Let X and Y be topological spaces.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — This is transitional prose rather than a mathematical theorem/construction with an independent checked owner. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — continuous {#fc08-ca-u014}

::: {.unit-meta}
`FC08-CA-U014` · Appendix A, § Topological Spaces; source L17932 · [in Mathlib]{.route-mathlib}
:::

map $F \colon X \to Y$ is said to be continuous if for every open subset $U \subseteq Y$ , the preimage $F ^ { - 1 } ( U )$ is open

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Basic.lean::Continuous`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html) — `Continuous f` is the open-preimage condition.
:::

### Definition/convention — homeomorphism {#fc08-ca-u015}

::: {.unit-meta}
`FC08-CA-U015` · Appendix A, § Topological Spaces; source L17934 · [in Mathlib]{.route-mathlib}
:::

. A continuous bijective map $F \colon X \to Y$ with continuous inverse is called a homeomorphism. If there exists a homeomorphism from X to Y , we say that X and Y are homeomorph

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Homeomorph/Defs.lean::Homeomorph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homeomorph/Defs.html) — `Homeomorph X Y` is a bijection with continuous forward and inverse maps, exactly the source object.
:::

### Definition/convention — a local homeomorphism {#fc08-ca-u016}

::: {.unit-meta}
`FC08-CA-U016` · Appendix A, § Topological Spaces; source L17936 · [in Mathlib]{.route-mathlib}
:::

continuous map $F \colon X \to Y$ is said to be a local homeomorphism if every point $p \in X$ has a neighborhood $U \subseteq X$ such that $F ( U )$ is open in Y and F restricts to a homeomorphism from U

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/IsLocalHomeomorph.lean::IsLocalHomeomorph, isLocalHomeomorph_iff_isOpenEmbedding_restrict`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/IsLocalHomeomorph.html) — The pointwise open-restriction characterization is exactly Lee’s local-homeomorphism definition.
:::

### Convention/notation — source terminology/construction {#fc08-ca-u017}

::: {.unit-meta}
`FC08-CA-U017` · Appendix A, § Topological Spaces; source L17938 · [in Mathlib]{.route-mathlib}
:::

Given a sequence ( p _i ) _i = 1 ^∞ of points in X and a point p ∈ X , the sequence is said to converge to p if for every neighborhood U of p _: , there exists a positive integer N such that p _i ∈ U for all i ≥ N . In this case, we write p _i → p or scriptstyle operatorname* l i m _i → ∞ p _i = p

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Filter.lean::Tendsto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html); [`Mathlib/Topology/Neighborhoods.lean::nhds_basis_opens`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Neighborhoods.html) — Convergence of a sequence is `Tendsto u atTop (𝓝 p)`; the open-neighborhood basis expands this to Lee’s eventual-membership formulation.
:::

### Example A.4 {#fc08-ca-u018}

::: {.unit-meta}
`FC08-CA-U018` · Appendix A, § Topological Spaces; source L17958 · [in Mathlib]{.route-mathlib}
:::

Example A.4 (Discrete Spaces). If X is an arbitrary set, the discrete topology on X is the topology defined by declaring every subset of X to be open. Any space that has the discrete topology is called a discrete space.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Order.lean::DiscreteTopology`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order.html) — `DiscreteTopology X` is exactly the topology in which every subset is open.
:::

### Example A.5 {#fc08-ca-u019}

::: {.unit-meta}
`FC08-CA-U019` · Appendix A, § Topological Spaces; source L17960 · [in Mathlib]{.route-mathlib}
:::

Example A.5 (Metric Spaces). A metric space is a set M endowed with a distance function (also called a metric) d $M \times M \to \mathbb { R }$ (where R denotes the set of rea numbers) satisfying the following properties for all $x , y , z \in M$ (i) POSITIVITY: $d ( x , y ) \geq 0$ , with equality if and only if $x = y$ (ii) SYMMETRY: $d ( x , y ) = d ( y , x )$ (iii) TRIANGLE INEQUALITY: $d ( x , z ) \leq d ( x , y ) + d ( y , z )$ If M is a metric space, $x \in M$ ; and $r > 0$ , the open ball of radius r around x is the set $$ B _ {r} (x) = \left\{y \in M: d (x, y) < r \right\}, $$ and the closed ball of radius r is $$ \bar {B} _ {r} (x) = \left\{y \in M: d (x, y) \leq r \right\}. $$ The metric topology on M is defined by declaring a subset $S \subseteq M$ to be open if for every point $x \in S$ , there is some $r > 0$ such

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/MetricSpace/Defs.lean::MetricSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Defs.html); [`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean::Metric.ball, Metric.closedBall, Metric.nhds_basis_ball`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Defs.html) — The metric axioms, open/closed balls, and the ball basis for the induced metric topology directly realize the full example.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u020}

::: {.unit-meta}
`FC08-CA-U020` · Appendix A, § Topological Spaces; source L17986 · [in Mathlib]{.route-mathlib}
:::

If S is a nonempty bounded subset of M; the diameter of S is the number diam S = operatorname* s u p d ( x , y ) : x , y ∈ S

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/MetricSpace/Bounded.lean::Metric.diam`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Bounded.html#Metric.diam) — [`Metric.diam`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Metric.diam#doc) is the supremum of pairwise distances on a set, with Lee’s bounded nonempty regime as its ordinary finite-valued case.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u021}

::: {.unit-meta}
`FC08-CA-U021` · Appendix A, § Topological Spaces; source L17988 · [in Mathlib]{.route-mathlib}
:::

A sequence of points ( x _i ) _i = 1 ^∞ in M is a Cauchy sequence if for every ε > 0 , there exists an integer N such that i , j ≥ N implies d ( x _i , x _j ) < ε

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/UniformSpace/Cauchy.lean::CauchySeq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html) — For metric spaces, `CauchySeq` unfolds to the usual ε-eventual pairwise-distance definition.
:::

### Definition/convention — complete {#fc08-ca-u022}

::: {.unit-meta}
`FC08-CA-U022` · Appendix A, § Topological Spaces; source L17990 · [in Mathlib]{.route-mathlib}
:::

A metric space M is said to be complete if every Cauchy sequence in M converges to a point of M .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/UniformSpace/Cauchy.lean::CompleteSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Cauchy.html) — `CompleteSpace` asserts that every Cauchy filter/sequence converges; in metric spaces it is equivalent to Lee’s sequence definition.
:::

### Example A.6 {#fc08-ca-u023}

::: {.unit-meta}
`FC08-CA-U023` · Appendix A, § Topological Spaces; source L17992 · [not formalized]{.route-unmatched}
:::

Example A.6 (Euclidean Spaces). For each integer n ≥ 1 , the set ℝ ^n of ordered n-tuples of real numbers is called n-dimensional Euclidean space. We denote a point in ℝ ^n by ( x ^1 , … , x ^n ) , ( x ^i ) , or x; the numbers x ^i are called the components or coordinates of x. (When n is small, we often use more traditional names such as ( x , y , z ) for the coordinates.) Notice that we write the coordinates of a point ( x ^1 , … , x ^n ) ∈ ℝ ^n with superscripts, not subscripts as is usually done in linear algebra and calculus books, so as to be consistent with the Einstein summation convention, explained in Chapter 1. By convention, ℝ ^0 is the one-element set 0 .

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has Euclidean/normed-space instances and many of the listed facts separately, but this source row bundles Lee’s coordinate conventions or several Euclidean identifications/examples; no single checked interface owns the whole bundle. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — Euclidean norm {#fc08-ca-u024}

::: {.unit-meta}
`FC08-CA-U024` · Appendix A, § Topological Spaces; source L17994 · [not formalized]{.route-unmatched}
:::

For each $x \in \mathbb{R}^{n}$, the Euclidean norm of $x$ is the nonnegative real number $$ |x| = \sqrt{(x^{1})^{2} + \cdots + (x^{n})^{2}}, $$ and for $x, y \in \mathbb{R}^{n}$ the Euclidean distance function is $d(x,y) = |x-y|$.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has Euclidean/normed-space instances and many of the listed facts separately, but this source row bundles Lee’s coordinate conventions or several Euclidean identifications/examples; no single checked interface owns the whole bundle. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — Euclidean distance {#fc08-ca-u025}

::: {.unit-meta}
`FC08-CA-U025` · Appendix A, § Topological Spaces; source L18000 · [in Mathlib]{.route-mathlib}
:::

{n}\right) ^ {2}}, $$ and for x; $y \in \mathbb { R } ^ { n }$ , the Euclidean distance function is defined by $$ d (x, y) = |

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Normed/Group/Basic.lean::dist_eq_norm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/Basic.html) — `dist_eq_norm` is exactly `d(x,y)=‖x-y‖` in the norm-induced Euclidean metric.
:::

### Convention/notation — Euclidean topology {#fc08-ca-u026}

::: {.unit-meta}
`FC08-CA-U026` · Appendix A, § Topological Spaces; source L18006 · [not formalized]{.route-unmatched}
:::

This distance function turns $\mathbb { R } ^ { n }$ into a complete metric space. The resulting metric topology on $\mathbb { R } ^ { n }$ is called the Euclidean

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has Euclidean/normed-space instances and many of the listed facts separately, but this source row bundles Lee’s coordinate conventions or several Euclidean identifications/examples; no single checked interface owns the whole bundle. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Example A.7 {#fc08-ca-u027}

::: {.unit-meta}
`FC08-CA-U027` · Appendix A, § Topological Spaces; source L18008 · [not formalized]{.route-unmatched}
:::

Example A.7 (Complex Euclidean Spaces). We also sometimes have occasion to work with complex Euclidean spaces. We consider the set C of complex numbers, as a set, to be simply $\mathbb { R } ^ { 2 }$ , with the complex number $x + i y$ corresponding to $( x , y ) \in \mathbb { R } ^ { 2 }$ . For any positive integer n, the n-dimensional complex Euclidean space is the set $\mathbb { C } ^ { n }$ of ordered n-tuples of complex numbers. It becomes a topological space when identified with $\mathbb { R } ^ { 2 { \bar { n } } }$ via the correspondence $$ \left(x ^ {1} + i y ^ {1}, \dots , x ^ {n} + i y ^ {n}\right) \leftrightarrow \left(x ^ {1}, y ^ {1}, \dots , x ^ {n}, y ^ {n}\right).\tag{//} $$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has Euclidean/normed-space instances and many of the listed facts separately, but this source row bundles Lee’s coordinate conventions or several Euclidean identifications/examples; no single checked interface owns the whole bundle. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Example A.8 {#fc08-ca-u028}

::: {.unit-meta}
`FC08-CA-U028` · Appendix A, § Topological Spaces; source L18014 · [not formalized]{.route-unmatched}
:::

(Subsets of Euclidean Spaces). Every subset of ℝ ^n or ℂ ^n becomes a metric space, and thus a topological space, when endowed with the Euclidean metric. Whenever we mention such a subset, it is always assumed to have this metric topology unless otherwise specified. It is a complete metric space if and only if it is a closed subset of ℝ ^n . Here are some standard subsets of Euclidean spaces that we work with frequently: The unit interval is the subset I ⊆ ℝ defined by I = [ 0, 1 ] = x ∈ ℝ: 0 ≤ x ≤ 1 . The (open) unit ball of dimension n is the subset mathbb B ^n ⊆ ℝ ^n defined by mathbb B ^n = x ∈ ℝ ^n: ∣ x ∣ < 1 . The closed unit ball of dimension n is the subset overline mathbb B ^n ⊆ ℝ ^n defined by overline mathbb B ^n = x ∈ ℝ ^n: ∣ x ∣ ≤ 1 . The terms (open) unit disk and closed unit disk are commonly used for mathbb B ^2 and overline mathbb B ^2 , respectively. For n ≥ 0 , the (unit) n-sphere is the subset mathbb S ^n ⊆ ℝ ^n + 1 defined by mathbb S ^n = x ∈ ℝ ^n + 1: ∣ x ∣ = 1 . Sometimes it is useful to think of an odd-dimensional sphere mathbb S ^2 n + 1 as a subset of ℂ ^n + 1 , by means of the usual identification of ℂ ^n + 1 with ℝ ^2 n + 2 The (unit) circle is the 1-sphere mathbb S ^1 , considered either as a subset of ℝ ^2 or as a subset of C.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has Euclidean/normed-space instances and many of the listed facts separately, but this source row bundles Lee’s coordinate conventions or several Euclidean identifications/examples; no single checked interface owns the whole bundle. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — a Hausdorff space {#fc08-ca-u029}

::: {.unit-meta}
`FC08-CA-U029` · Appendix A, § Hausdorff Spaces; source L18052 · [in Mathlib]{.route-mathlib}
:::

To avoid pathological cases like this, which result when X does not have sufficiently many open subsets, we often restrict our attention to topological spaces satisfying the following special condition. A topological space X is said to be a Hausdorff space if for every pair of distinct points $p , q \in X$ , there exist disjoint open subsets $U , V \subseteq X$ such that $p \in U$ and $q \in V .$

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Separation/Hausdorff.lean::T2Space`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Hausdorff.html) — `T2Space` is exactly pairwise separation of distinct points by disjoint neighborhoods/open sets.
:::

### Definition/convention — a basis for the topology of X {#fc08-ca-u030}

::: {.unit-meta}
`FC08-CA-U030` · Appendix A, § Bases and Countability; source L18060 · [in Mathlib]{.route-mathlib}
:::

Suppose X is a topological space. A collection of open subsets of X is said to be a basis for the topology of X (plural: bases) if every open subset of X is the union of some collection of elements of .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Bases.lean::IsTopologicalBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html) — `IsTopologicalBasis B` is precisely the source condition that open sets are unions of basis elements.
:::

### Definition/convention — topology generated by B {#fc08-ca-u031}

::: {.unit-meta}
`FC08-CA-U031` · Appendix A, § Bases and Countability; source L18062 · [in Mathlib]{.route-mathlib}
:::

More generally, suppose X is merely a set, and B is a collection of subsets of X satisfying the following conditions: (i) beginarray r X = bigcup _B ∈ B B . endarray (ii) I f ~ B _1 , B _2 ∈ B and x ∈ B _1 ∩ B _2 , then there exists B _3 ∈ B such that x ∈ B _3 ⊆ B _1 ∩ B _2 . Then the collection of all unions of elements of B is a topology on X, called the topology generated by B , and B is a basis for this topology.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Bases.lean::IsTopologicalBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html) — Mathlib’s basis-generation API formalizes the cover/refinement criterion and identifies the resulting topology as the topology generated by the basis.
:::

### Definition/convention — topology generated by B {#fc08-ca-u032}

::: {.unit-meta}
`FC08-CA-U032` · Appendix A, § Bases and Countability; source L18068 · [in Mathlib]{.route-mathlib}
:::

Then the collection of all unions of elements of B is a topology on X, called the topology generated by B , and B is a basis for this topology.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Bases.lean::IsTopologicalBasis.eq_generateFrom`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html#IsTopologicalBasis.eq_generateFrom) — A topological basis generates exactly the ambient topology; this is Lee’s generated-topology convention.
:::

### Definition/convention — neighborhood basis at p {#fc08-ca-u033}

::: {.unit-meta}
`FC08-CA-U033` · Appendix A, § Bases and Countability; source L18070 · [in Mathlib]{.route-mathlib}
:::

If X is a topological space and $p \in X$ a neighborhood basis at p is a collection $\mathcal { B } _ { p }$ of neighborhoods of p such that every neighborhood of p contains at least one $B \in { \mathcal { B } } _ { p } .$

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Neighborhoods.lean::nhds_basis_opens`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Neighborhoods.html); [`Mathlib/Order/Filter/Bases/Basic.lean::Filter.HasBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Bases/Basic.html#Filter.HasBasis) — `nhds_basis_opens` says open sets containing `p` form a basis of `𝓝 p`; [`Filter.HasBasis`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Filter.HasBasis#doc) is exactly the refinement property Lee calls a neighborhood basis.
:::

### Definition/convention — countably infinite {#fc08-ca-u034}

::: {.unit-meta}
`FC08-CA-U034` · Appendix A, § Bases and Countability; source L18072 · [not formalized]{.route-unmatched}
:::

A set is said to be countably infinite if it admits a bijection with the set of positive integers, and countable if it is finite or countably infinite. A topological space X is said to be first-countable if there is a countable neighborhood basis at each point, and second-countable if there is a countable basis for its topology. Since a countable basis for X contains a countable neighborhood basis at each point, secondcountability implies first-countability.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has the constituent countability/filter/sequence/cover notions, but this source row bundles several definitions or several sequential characterizations. No one declaration or short checked assembly owns all clauses under strict whole-row semantics. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — sequence {#fc08-ca-u035}

::: {.unit-meta}
`FC08-CA-U035` · Appendix A, § Bases and Countability; source L18074 · [not formalized]{.route-unmatched}
:::

The next lemma expresses the most important properties of first-countable spaces. To say that a sequence is eventually in a subset means that all but finitely many terms of the sequence are in the subset.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has the constituent countability/filter/sequence/cover notions, but this source row bundles several definitions or several sequential characterizations. No one declaration or short checked assembly owns all clauses under strict whole-row semantics. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Lemma A.12 {#fc08-ca-u036}

::: {.unit-meta}
`FC08-CA-U036` · Appendix A, § Bases and Countability; source L18076 · [not formalized]{.route-unmatched}
:::

Lemma A.12 (Sequence Lemma). Let X be a first-countable space, let $A \subseteq X$ be any subset, and let $x \in X$ (a) $x \in { \overline { { A } } }$ if and only if x is a limit of a sequence of points in A. (b) $x \in$ Int A if and only if every sequence in X converging to x is eventually in A. (c) A is closed in X if and only if A contains every limit of every convergent sequence of points in A. (d) A is open in X if and only if every sequence in X converging to a point of A is eventua

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has the constituent countability/filter/sequence/cover notions, but this source row bundles several definitions or several sequential characterizations. No one declaration or short checked assembly owns all clauses under strict whole-row semantics. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — open cover {#fc08-ca-u037}

::: {.unit-meta}
`FC08-CA-U037` · Appendix A, § Bases and Countability; source L18092 · [not formalized]{.route-unmatched}
:::

One of the most important properties of second-countable spaces is expressed in the following proposition. Let X be a topological space. A cover of X is a collection of subsets of X whose union is X; it is called an open cover if each of the sets in is open. A subcover of is a subcollection of that is still a cover.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has the constituent countability/filter/sequence/cover notions, but this source row bundles several definitions or several sequential characterizations. No one declaration or short checked assembly owns all clauses under strict whole-row semantics. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.16 {#fc08-ca-u038}

::: {.unit-meta}
`FC08-CA-U038` · Appendix A, § Bases and Countability; source L18094 · [in Mathlib]{.route-mathlib}
:::

Proposition A.16. Let X be a second-countable topological space. Every open cover of X has a countable subcover.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Compactness/Lindelof.lean::SecondCountableTopology.toHereditarilyLindelof, IsLindelof.elim_countable_subcover`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Lindelof.html) — Second-countability supplies Lindelöfness, whose elimination theorem gives a countable subcover of every open cover.
:::

### Definition/convention — relative topology) by declaring a subset U {#fc08-ca-u039}

::: {.unit-meta}
`FC08-CA-U039` · Appendix A, § Subspaces; source L18102 · [in Mathlib]{.route-mathlib}
:::

Probably the simplest way to obtain new topological spaces from old ones is by taking subsets of other spaces. If X is a topological space and $S \subseteq X$ is an arbitrary subset, we define the subspace topology on S (sometimes called the relative topology) by declaring a subset $U \subseteq S$ to be open in S if and only if there exists an open subset V X such that $U = V \cap S$ A subset of S that is open or closed in the subspace topology is sometimes said to be relatively open or relatively closed in S , to make it clear that we do not mean open or closed as a subset of X. Any subset of X endowed with the subspace topology is said to be a subspace of X . Whenever we treat a subset of a topological space as a space in its own right, we always assume that it has the subspace topology unless otherwise specified.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Induced.lean::TopologicalSpace.induced`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Induced.html#TopologicalSpace.induced); [`Mathlib/Topology/Constructions.lean::isOpen_induced_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Constructions.html) — The subtype topology is the induced topology and `isOpen_induced_iff` gives exactly the intersection-with-an-ambient-open-set characterization.
:::

### Definition/convention — topological embedding {#fc08-ca-u040}

::: {.unit-meta}
`FC08-CA-U040` · Appendix A, § Subspaces; source L18104 · [in Mathlib]{.route-mathlib}
:::

If X and Y are topological spaces, a continuous injective map $F \colon X \to Y$ is called a topological embedding if it is a homeomorphism onto its image $F ( X ) \subseteq Y$ in the subspace topolo

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Induced.lean::Topology.IsEmbedding`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Induced.html#Topology.IsEmbedding) — `IsEmbedding f` is injective and inducing; equivalently a continuous injection that is a homeomorphism onto its range with the subspace topology.
:::

### Proposition A.17 {#fc08-ca-u041}

::: {.unit-meta}
`FC08-CA-U041` · Appendix A, § Subspaces; source L18108 · [not formalized]{.route-unmatched}
:::

Proposition A.17 (Properties of the Subspace Topology). Let X be a topological space and let S be a subspace of X. (a) CHARACTERISTIC PROPERTY: If Y is a topological space, a map F Y S is continuous if and only if the composition $\iota _ { S } \circ F \colon Y \to X$ is continuous, where $\iota _ { S } \colon S \hookrightarrow$ X is the inclusion map (the restriction of the identity map of X to S ). (b) The subspace topology is the unique topology on S for which the characteristic property holds. (c) A subset $K \subseteq S$ is closed in S if and only if there exists a closed subset $L \subseteq X$ such that $K = L \cap S$ (d) The inclusion map $\iota _ { S } \colon S \hookrightarrow X$ is a topological embedding. (e) If Y is a topological space and $F \colon X \to Y$ is continuous, then $F | _ { S } \colon S \to Y$ (the restriction of F to S ) is continuous. (f) If is a basis for the topology of X , then $\mathcal { B } _ { S } = \{ B \cap S : B \in \mathcal { B } \}$ is a basis for the subspace topology on S. (g) If X is Hausdorff, then so is S . (h) If X is first-countable, then so is S . (i)

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Lemma A.19 {#fc08-ca-u042}

::: {.unit-meta}
`FC08-CA-U042` · Appendix A, § Subspaces; source L18132 · [in Mathlib]{.route-mathlib}
:::

Lemma A.19 (Continuity Is Local). Continuity is a local property, in the following sense: if F X Y is a map between topological spaces such that every poin $p \in X$ has a neighborhood U on which the restriction $F | _ { U }$ is continuous, then F is continuous.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/ContinuousOn.lean::continuous_of_cover_nhds`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousOn.html) — `continuous_of_cover_nhds` is the local-to-global continuity theorem on a neighborhood cover, exactly Lee’s lemma.
:::

### Lemma A.20 {#fc08-ca-u043}

::: {.unit-meta}
`FC08-CA-U043` · Appendix A, § Subspaces; source L18134 · [not formalized]{.route-unmatched}
:::

Lemma A.20 (Gluing Lemma for Continuous Maps). Let X and Y be topological spaces, and suppose one of the following conditions holds: (a) $B _ { 1 } , \ldots , B _ { n }$ are finitely many closed subsets of X whose union is X. (b) $\{ B _ { i } \} _ { i \in A }$ is a collection of open subsets of X whose union is X. Suppose that for all i we are given continuous maps $F _ { i } \colon B _ { i } \to Y$ that agree on overlaps: $F _ { i } | _ { B _ { i } \cap B _ { j } } = F _ { j } | _ { B _ { i } \cap B _ { j } }$ . Then there exists a unique continuous map $F \colon X \to Y$ whose restriction to each $B _ { i }$ is equal

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — source terminology/construction {#fc08-ca-u044}

::: {.unit-meta}
`FC08-CA-U044` · Appendix A, § Product Spaces; source L18148 · [not formalized]{.route-unmatched}
:::

Next we consider finite products of topological spaces. If X _1 , … , X _k are (finitely many) sets, their Cartesian product is the set X _1 × ·s × X _k consisting of all ordered k-tuples of the form ( x _1 , … , x _k ) with x _i ∈ X _i for each i. The i th projection map is the map π _i : X _1 × ·s × X _k → X _i defined by π _i ( x _1 , … , x _k ) = x _i

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — product topology {#fc08-ca-u045}

::: {.unit-meta}
`FC08-CA-U045` · Appendix A, § Product Spaces; source L18150 · [not formalized]{.route-unmatched}
:::

Suppose X _1 , … , X _k are topological spaces. The collection of all subsets of X _1 × ·s × X _k of the form U _1 × ·s × U _k , where each U _i is open in X _i , , forms a basis for a topology on X _1 × ·s × X _k , called the product topology. Endowed with this topology, a finite product of topological spaces is called a product space. Any open subset of the form U _1 × ·s × U _k ⊆ X _1 × ·s × X _k , where each U _i is open in X _i , , is called a product open subset. (A slightly different definition is required for products of infinitely many spaces, but we need only the finite case. See [LeeTM] for more about infinite product spaces.)

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.23 {#fc08-ca-u046}

::: {.unit-meta}
`FC08-CA-U046` · Appendix A, § Product Spaces; source L18152 · [not formalized]{.route-unmatched}
:::

(Properties of the Product Topology). Suppose X _1 , … , X _k are topological spaces, and let X _1 × ·s × X _k be their product space. (a) CHARACTERISTIC PROPERTY: If B is a topological space, a map F : B → X _1 × ·s × X _k is continuous if and only if each of its component functions F _i = π _i ∘ F : B X _i is continuous. (b) The product topology is the unique topology on X _1 × ·s × X _k for which the characteristic property holds. (c) Each projection map π i X _1 × ·s × X _k X _i is continuous. (d) Given any continuous maps F _i : X _i Y _i for i = 1 , … , k , the product map F _1 × ·s × F _k : X _1 × ·s × X _k → Y _1 × ·s × Y _k is continuous, where F _1 × … × F _k (x _1, … , x _k) = (F _1 (x _1), … , F _k (x _k) ). (e) I f S _i is a subspace of X for i = 1 , … , n , the product topology and the subspace topology on S _1 × ·s × S _n ⊆ X _1 × ·s × X _n coincide. (f) For any i ∈ 1 , … , k and any choices of points a _j ∈ X _j for j ≠ i , the map x ↦ ( a _1 , … , a _i - 1 , x , a _i + 1 , … , a _k ) is a topological embedding of X _i into the product space X _1 × ·s × X _k . (g) cal I f B _i is a basis for the topology of X _i f o r i = 1 , … , k , then the collection B = B _1 × … × B _k: B _i ∈ B _i is a basis for the topology of X _1 × ·s × X _k . (h) Every finite product of Hausdorff spaces is Hausdorff. (i) Every finite product of first-countable spaces is first-countable. (j) Every finite product of second-countable spaces is second-countable.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — source terminology/construction {#fc08-ca-u047}

::: {.unit-meta}
`FC08-CA-U047` · Appendix A, § Disjoint Union Spaces; source L18188 · [in Mathlib]{.route-mathlib}
:::

Another simple way of building new topological spaces is by taking disjoint unions of other spaces. From a set-theoretic point of view, the disjoint union is defined as follows. If ( X _α ) _α ∈ A is an indexed family of sets, their disjoint union is the set $$ \coprod_{\alpha \in A} X_{\alpha} = \{(x,\alpha) : \alpha \in A,\ x \in X_{\alpha}\}, $$ with canonical injections $\iota_{\alpha} \colon X_{\alpha} \to \coprod_{\alpha \in A} X_{\alpha}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/Data/Sigma/Basic.lean::Sigma`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Sigma/Basic.html) — The dependent sum `Σ a, X a` is exactly the tagged disjoint union of an indexed family.
:::

### Convention/notation — source terminology/construction {#fc08-ca-u048}

::: {.unit-meta}
`FC08-CA-U048` · Appendix A, § Disjoint Union Spaces; source L18194 · [not formalized]{.route-unmatched}
:::

For each α , there is a canonical injective map iota _α : X _α → coprod _α ∈ A X _α given by iota _α ( x ) = ( x , α ) , and the images of these maps for different values of ˛ are disjoint. Typically, we implicitly identify X _α with its image in the disjoint union, thereby viewing X _α as a subset of I I _α ∈ A X _α . The ˛ in the notation ( x , α ) should be thought of as mathbf a Sigma ^ mathrm t a g ^prime to indicate which set x comes from, so that the subsets corresponding to different values of ˛ are disjoint, even if some or all of the original sets X _α were identical.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — disjoint union topology {#fc08-ca-u049}

::: {.unit-meta}
`FC08-CA-U049` · Appendix A, § Disjoint Union Spaces; source L18196 · [in Mathlib]{.route-mathlib}
:::

Given an indexed family of topological spaces ( X _α ) _α ∈ A , we define the disjoint union topology on U _α ∈ A X _α by declaring a subset of H _α ∈ A X _α to be open if and only if its intersection with each overline X _α is open in overline X _α .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Constructions.lean::isOpen_sigma_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Constructions.html) — `isOpen_sigma_iff` says a set in a dependent sum is open iff every tagged component preimage is open, exactly the disjoint-union topology.
:::

### Proposition A.25 {#fc08-ca-u050}

::: {.unit-meta}
`FC08-CA-U050` · Appendix A, § Disjoint Union Spaces; source L18198 · [not formalized]{.route-unmatched}
:::

(Properties of the Disjoint Union Topology). Suppose ( X _α ) _α ∈ A is an indexed family of topological spaces, and textstyle I _α ∈ A X _α is endowed with the disjoint union topology. (a) CHARACTERISTIC PROPERTY: If Y is a topological space, a map F : coprod_α ∈ A X _α → Y is continuous if and only if F iota _α : X _α → Y is continuous for each ˛ ∈ A (b) The disjoint union topology is the unique topology on textstyle I I _α ∈ A X _α for which the characteristic property holds. (c) A subset of textstyle I _α ∈ A X _α is closed if and only if its intersection with each X _α is closed. (d) Each injection beginarray r iota _α : X _α → big L _α ∈ A X _α endarray is a topological embedding. (e) Every disjoint union of Hausdorff spaces is Hausdorff. (f) Every disjoint union of first-countable spaces is first-countable. (g) Every disjoint union of countably many second-countable spaces is secondcountable.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The underlying subspace/product/disjoint-union infrastructure is formalized, but this row is a multi-clause construction/properties bundle (or tagged-image convention) not owned in full by one declaration or a short assembly. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — quotient map {#fc08-ca-u051}

::: {.unit-meta}
`FC08-CA-U051` · Appendix A, § Quotient Spaces and Quotient Maps; source L18224 · [in Mathlib]{.route-mathlib}
:::

If X is a topological space, Y is a set, and $\pi \colon X \to Y$ is a surjective map, the quotient topology on Y determined by  is defined by declaring a subset $U \subseteq Y$ to be open if and only if $\pi ^ { - 1 } ( U )$ is open in X. If X and Y are topological spaces, a map $\pi \colon X \to Y$ is called a quotient map if it is surjective and continuous and Y has the quotient topology determi

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Induced.lean::Topology.IsQuotientMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Induced.html#Topology.IsQuotientMap) — `IsQuotientMap` is surjectivity plus the coinduced/quotient topology, hence exactly Lee’s quotient-map package.
:::

### Definition/convention — equivalence relation {#fc08-ca-u052}

::: {.unit-meta}
`FC08-CA-U052` · Appendix A, § Quotient Spaces and Quotient Maps; source L18226 · [not formalized]{.route-unmatched}
:::

The following construction is the most common way of producing quotient maps. A relation on a set X is called an equivalence relation if it is reflexive $( x \sim x$ for all $x \in X )$ , symmetric $( x \sim y$ implies $y \sim x )$ , and transitive $( x \sim y$ and $y \sim z$ imply $x \sim z )$ . If $R \subseteq X \times X$ is any relation on X, then the intersection of all equivalence relations on $X$ containing R is an equivalence relation, called the equivalence relation generated by R. If is an equivalence relation on $X$ , then for each $x \in X$ , the equivalence class of x, denoted by Œx, is the set of all $y \in X$ such that $y \sim x$ . The set of all equivalence classes is a partition of X : a collection of disjoint nonempty subsets whose union is

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — quotient space ( {#fc08-ca-u053}

::: {.unit-meta}
`FC08-CA-U053` · Appendix A, § Quotient Spaces and Quotient Maps; source L18228 · [not formalized]{.route-unmatched}
:::

Suppose X is a topological space and is an equivalence relation on X. Let $X / \sim$ denote the set of equivalence classes in X, and let $\pi \colon X \to X / \sim$ be the natural projection sending each point to its equivalence class. Endowed with the quotient topology determined by , the space $X / \sim$ is called the quotient space (or identification space) of X determined by . For example, suppose X and Y are topological spaces, $A \subseteq Y$ is a closed subset, and $f \colon A \to X$ is a continuous map. The relation $a \sim f ( a )$ for all $a \in A$ generates an equivalence relation on X Y , whose quotient space is denoted by $X \cup _ { f } Y$ and called an adjunction space. It is said to be formed by attaching Y to X

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — saturated {#fc08-ca-u054}

::: {.unit-meta}
`FC08-CA-U054` · Appendix A, § Quotient Spaces and Quotient Maps; source L18230 · [not formalized]{.route-unmatched}
:::

If π : X → Y is a map, a subset U ⊆ X is said to be saturated with respect to π if U is the entire preimage of its image: U = π ^- 1 ( π ( U ) ) . Given y ∈ Y , the fiber of π over y is the set π ^- 1 ( y ) Thus, a subset of X is saturated if and only if it is a union of fibers.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Theorem A.27 {#fc08-ca-u055}

::: {.unit-meta}
`FC08-CA-U055` · Appendix A, § Quotient Spaces and Quotient Maps; source L18232 · [not formalized]{.route-unmatched}
:::

(Properties of Quotient Maps). Let π : X → Y be a quotient map. (a) CHARACTERISTIC PROPERTY: If B is a topological space, a map F : Y B is continuous if and only if F π : X → B is continuous. (b) The quotient topology is the unique topology on Y for which the characteristic property holds. (c) A subset K ⊆ Y is closed if and only i f π ^- 1 ( K ) is closed in X . (d) If π is injective, then it is a homeomorphism. (e) I f U ⊆ X is a saturated open or closed subset, then the restriction π ∣ _U : U → π.U / is a quotient map. (f) Any composition of π with another quotient map is again a quotient map.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Theorem A.30 {#fc08-ca-u056}

::: {.unit-meta}
`FC08-CA-U056` · Appendix A, § Quotient Spaces and Quotient Maps; source L18258 · [in Mathlib]{.route-mathlib}
:::

(Passing to the Quotient). Suppose π : X → Y is a quotient map, B is a topological space, and F : X → B is a continuous map that is constant on the fibers of π ( i . e . , π ( p ) = π ( q ) implies F ( p ) = F ( q ) ) . Then there exists a unique continuous map tilde(F) : Y → B such that F = tilde(F) ∘ π

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/ContinuousMap/Basic.lean::Topology.IsQuotientMap.lift, Topology.IsQuotientMap.lift_comp, Topology.IsQuotientMap.liftEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousMap/Basic.html) — For a continuous map constant on fibers, `lift` descends it uniquely through a quotient map and `lift_comp` gives the required factorization; `liftEquiv` packages uniqueness.
:::

### Theorem A.31 {#fc08-ca-u057}

::: {.unit-meta}
`FC08-CA-U057` · Appendix A, § Quotient Spaces and Quotient Maps; source L18262 · [not formalized]{.route-unmatched}
:::

(Uniqueness of Quotient Spaces). I f π _1 : X → Y _1 and π _2 : X → Y _2 are quotient maps that are constant on each other’s fibers ( i . e . , π _1 ( p ) = π _1 ( q ) if and only if dot π _2 ( p ) = π _2 ( q ) ) , then there exists a unique homeomorphism φ : Y _1 Y _2 such that φ ∘ π _1 = π _2

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — an open map {#fc08-ca-u058}

::: {.unit-meta}
`FC08-CA-U058` · Appendix A, § Open and Closed Maps; source L18268 · [not formalized]{.route-unmatched}
:::

A map F : X → Y (continuous or not) is said to be an open map if for every open subset U ⊆ X , the image set F ( U ) is open in Y , and a closed map if for every closed subset K ⊆ X , the image F ( K ) is closed in Y . Continuous maps may be open, closed, both, or neither, as can be seen by examining simple examples involving subsets of the plane.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Theorem A.38 {#fc08-ca-u059}

::: {.unit-meta}
`FC08-CA-U059` · Appendix A, § Open and Closed Maps; source L18288 · [not formalized]{.route-unmatched}
:::

Theorem A.38. Suppose X and Y are topological spaces, and $F \colon X \to Y$ is a continuous map that is either open or closed. (a) If F is surjective, then it is a quotient map. (b) If F is injective, then it is a topological embedding. (c) If F is bijective, then it is a homeomor

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient/setoid/open/closed-map infrastructure, but this row bundles generated equivalence relations, adjunction examples, saturation, several quotient properties, or quotient-space uniqueness beyond the single directly mapped universal property. No complete owner was found. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — disconnected {#fc08-ca-u060}

::: {.unit-meta}
`FC08-CA-U060` · Appendix A, § Connectedness and Compactness; source L18302 · [in Mathlib]{.route-mathlib}
:::

A topological space X is said to be disconnected if it has two disjoint nonempty open subsets whose union is X, and it is connected otherwise. Equivalently, X is connected if and only if the only subsets of X that are both open and closed are ¿ and X itself. If X is any topological space, a connected subset of X is a subset that is a connected space when endowed with the subspace topology. For example, the nonempty connected subsets of R are the singletons (one-element sets) and the intervals, which are the subsets J ⊆ ℝ containing more than one point and having the property that whenever a , b ∈ J and a < c < b , it follows that c ∈ J as well.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Connected/Basic.lean::IsPreconnected, IsConnected`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/Basic.html); [`Mathlib/Topology/Order/IntermediateValue.lean::isPreconnected_iff_ordConnected`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/IntermediateValue.html) — Mathlib’s connectedness is the no-open-separation condition; on the real line, `isPreconnected_iff_ordConnected` identifies connected subsets with order-convex intervals, with singletons included.
:::

### Definition/convention — component ( {#fc08-ca-u061}

::: {.unit-meta}
`FC08-CA-U061` · Appendix A, § Connectedness and Compactness; source L18304 · [in Mathlib]{.route-mathlib}
:::

A maximal connected subset of X (i.e., a connected subset that is not properly contained in any larger connected subset) is called a component (or connected component) of X.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Connected/Basic.lean::connectedComponent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/Basic.html) — `connectedComponent x` is the maximal connected subset through `x`, exactly the source component.
:::

### Proposition A.39 {#fc08-ca-u062}

::: {.unit-meta}
`FC08-CA-U062` · Appendix A, § Connectedness and Compactness; source L18306 · [not formalized]{.route-unmatched}
:::

Proposition A.39 (Properties of Connected Spaces). Let X and Y be topological spaces. (a) $I f F \colon X \to Y$ is continuous and X is connected, then $F ( X )$ is connected. (b) Every connected subset of X is contained in a single component of X. (c) A union of connected subspaces of X with a point in common is connected. (d) The components of X are disjoint nonempty closed subsets whose union is X, and thus they form a partition of X . (e) If S is a subset of X that is both open and closed, then S is a union of components of X . (f) Every finite product of connected spaces is connected. (g) Every quotient space of a connected space is conn

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — path-connected {#fc08-ca-u063}

::: {.unit-meta}
`FC08-CA-U063` · Appendix A, § Connectedness and Compactness; source L18324 · [in Mathlib]{.route-mathlib}
:::

Closely related to connectedness is path connectedness. If X is a topological space and $p , q \in X$ , a path in X from p to q is a continuous map $f \colon I \to X$ (where $I = [ 0 , 1 ] )$ such that $f ( 0 ) = p$ and $f ( 1 ) = q$ . If for every pair of points $p , q \in X$ there exists a path in X from p to q, then X is said to be path-connected. The path components of X are its maximal path-connected subse

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Path.lean::Path`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Path.html); [`Mathlib/Topology/Connected/PathConnected.lean::IsPathConnected, pathComponent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/PathConnected.html) — Mathlib directly formalizes paths on `[0,1]`, path-connected subsets, and maximal path components.
:::

### Proposition A.41 {#fc08-ca-u064}

::: {.unit-meta}
`FC08-CA-U064` · Appendix A, § Connectedness and Compactness; source L18326 · after [`FC08-CA-U062`](#fc08-ca-u062) · [not formalized]{.route-unmatched}
:::

Proposition A.41 (Properties of Path-Connected Spaces). (a) Proposition A.39 holds with “connected” replaced by “path-connected” and “component” by “path component” throughout. (b) Every path-connected space is connected.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — locally path-connected {#fc08-ca-u065}

::: {.unit-meta}
`FC08-CA-U065` · Appendix A, § Connectedness and Compactness; source L18334 · [in Mathlib]{.route-mathlib}
:::

For most topological spaces we treat in this book, including all manifolds, connectedness and path connectedness turn out to be equivalent. The link between the two concepts is provided by the following notion. A topological space is said to be locally path-connected if it admits a basis of path-connected open subsets.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Connected/LocallyPathConnected.lean::LocallyPathConnectedSpace, isOpen_isPathConnected_basis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Connected/LocallyPathConnected.html) — The class is characterized by an open path-connected neighborhood basis, exactly Lee’s definition.
:::

### Proposition A.43 {#fc08-ca-u066}

::: {.unit-meta}
`FC08-CA-U066` · Appendix A, § Connectedness and Compactness; source L18336 · [not formalized]{.route-unmatched}
:::

Proposition A.43 (Properties of Locally Path-Connected Spaces). Let X be a locally path-connected topological space. (a) The components of X are open in X. (b) The path components of X are equal to its components. (c) X is connected if and only if it is path-connected. (d) Every open subset of X is locally path-connected.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — compact {#fc08-ca-u067}

::: {.unit-meta}
`FC08-CA-U067` · Appendix A, § Connectedness and Compactness; source L18348 · [in Mathlib]{.route-mathlib}
:::

A topological space X is said to be compact if every open cover of X has a finite subcover. A compact subset of a topological space is one that is a compact space in the subspace topology. For example, it is a consequence of the Heine–Borel theorem that a subset of R is compact if and only if it is closed and bounded.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Filter.lean::IsCompact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html); [`Mathlib/Topology/Compactness/Compact.lean::isCompact_iff_finite_subcover`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html); [`Mathlib/Topology/MetricSpace/Bounded.lean::isCompact_iff_isClosed_bounded`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Bounded.html) — Mathlib’s finite-subcover characterization is the source compactness definition, and its Heine–Borel theorem gives the stated closed-and-bounded criterion in Euclidean proper metric spaces.
:::

### Proposition A.45 {#fc08-ca-u068}

::: {.unit-meta}
`FC08-CA-U068` · Appendix A, § Connectedness and Compactness; source L18350 · [not formalized]{.route-unmatched}
:::

Proposition A.45 (Properties of Compact Spaces). Let X and Y be topological spaces. (a) If $F \colon X \to Y$ is continuous and X is compact, then F .X / is compact. (b) If X is compact and f X R is continuous, then f is bounded and attains its maximum and minimum values on X. (c) Any union of finitely many compact subspaces of X is compact. (d) If X is Hausdorff and K and L are disjoint compact subsets of X, then there exist disjoint open subsets U; $V \subseteq X$ such that $K \subseteq U$ and $L \subseteq V$ (e) Every closed subset of a compact space is compact. (f) Every compact subset of a Hausdorff space is closed. (g) Every compact subset of a metric space is bounded. (h) Every finite product of compact spaces is compact. (i) Every quotient of a compact space is compa

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — Lipschitz constant for F {#fc08-ca-u069}

::: {.unit-meta}
`FC08-CA-U069` · Appendix A, § Connectedness and Compactness; source L18372 · [in Mathlib]{.route-mathlib}
:::

For maps between metric spaces, there are several variants of continuity that are useful, especially in the context of compact spaces. Suppose ( M _1 , d _1 ) and ( M _2 , d _2 ) are metric spaces, and F : M _1 → M _2 is a map. Then F is said to be uniformly continuous if for every ε > 0 . , there exists delta > 0 such that for all x; y ∈ M _1 , d _1 ( x , y ) < delta implies d _2 big ( F ( x ) , F ( y ) big ) < ε . . It is said to be Lipschitz continuous if there is a constant C such that d _2 ( F ( x ) , F ( y ) ) ≤ C d _1 ( x , y ) for all x , y ∈ M _1 . Any such C is called a Lipschitz constant for F . We say that F is locally Lipschitz continuous if every point x ∈ M _1 has a neighborhood on which F is Lipschitz continuous. (To emphasize the distinction, Lipschitz continuous functions are sometimes called uniformly or globally Lipschitz continuous.)

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/UniformSpace/Defs.lean::UniformContinuous`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/Defs.html); [`Mathlib/Topology/EMetricSpace/Lipschitz.lean::LipschitzWith, LocallyLipschitz`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/EMetricSpace/Lipschitz.html) — These are exactly the uniform-continuity, global Lipschitz, and local Lipschitz predicates in Lee’s metric-space formulation.
:::

### Proposition A.48 {#fc08-ca-u070}

::: {.unit-meta}
`FC08-CA-U070` · Appendix A, § Connectedness and Compactness; source L18376 · [in Mathlib]{.route-mathlib}
:::

Proposition A.48. Suppose $( M _ { 1 } , d _ { 1 } )$ and $( M _ { 2 } , d _ { 2 } )$ are metric spaces and $F \colon M _ { 1 } \to$ $M _ { 2 }$ is a map. Let K be any compact subset of $M _ { 1 }$ (a) If F is continuous, then $F | _ { K }$ is uniformly continuous. (b) If F is locally Lipschitz continuous, then $F | _ { K }$ is Lipschitz conti

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/UniformSpace/HeineCantor.lean::IsCompact.uniformContinuousOn_of_continuous`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/HeineCantor.html#IsCompact.uniformContinuousOn_of_continuous); [`Mathlib/Topology/Algebra/MetricSpace/Lipschitz.lean::LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/MetricSpace/Lipschitz.html#LocallyLipschitzOn.exists_lipschitzOnWith_of_compact) — The first theorem is Heine–Cantor on a compact set; the second states exactly that locally Lipschitz on a compact set admits one global Lipschitz constant there.
:::

### Proposition A.50 {#fc08-ca-u071}

::: {.unit-meta}
`FC08-CA-U071` · Appendix A, § Connectedness and Compactness; source L18396 · [not formalized]{.route-unmatched}
:::

Proposition A.50 (Equivalent Formulations of Compactness). Suppose M is a second-countable Hausdorff space or a metric space. The following are equivalent. (a) M is compact. (b) Every infinite subset of M has a limit point in M . (c) Every sequence in M has a convergent subsequence in M .

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Lemma A.52 {#fc08-ca-u072}

::: {.unit-meta}
`FC08-CA-U072` · Appendix A, § Connectedness and Compactness; source L18408 · [not formalized]{.route-unmatched}
:::

Lemma A.52 (Closed Map Lemma). Suppose X is a compact space, Y is a Hausdorff space, and F X Y is a continuous map. (a) F is a closed map. (b) If F is surjective, it is a quotient map. (c) If F is injective, it is a topological embedding. (d) If F is bijective, it is a homeomorphism.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — proper {#fc08-ca-u073}

::: {.unit-meta}
`FC08-CA-U073` · Appendix A, § Connectedness and Compactness; source L18420 · [not formalized]{.route-unmatched}
:::

If X and Y are topological spaces, a map F X Y (continuous or not) is said to be proper if for every compact set K Y , the preimage F .K/ is compact. Here are some useful sufficient conditions for a map to be proper.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.53 {#fc08-ca-u074}

::: {.unit-meta}
`FC08-CA-U074` · Appendix A, § Connectedness and Compactness; source L18422 · [not formalized]{.route-unmatched}
:::

(Sufficient Conditions for Properness). Suppose X and Y are topological spaces, and F X Y is a continuous map. (a) If X is compact and Y is Hausdorff, then F is proper. (b) If F is a closed map with compact fibers, then F is proper. (c) If F is a topological embedding with closed image, then F is proper. (d) If Y is Hausdorff and F has a continuous left inverse (i.e., a continuous map G : Y → X such that G ∘ F = I d _X ) , then F is proper. (e) If F is proper and A ⊆ X is a subset that is saturated with respect to F , then F ∣ _A : A → F ( A ) is proper.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — metrizable {#fc08-ca-u075}

::: {.unit-meta}
`FC08-CA-U075` · Appendix A, § Locally Compact Hausdorff Spaces; source L18438 · [in Mathlib]{.route-mathlib}
:::

In general, the topological spaces whose properties are most familiar are those whose topologies are induced by metrics; such a topological space is said to be metrizable. However, when studying manifolds, it is often quite inconvenient to exhibit a metric that generates a manifold’s topology. Fortunately, as shown in Chapter 1, manifolds belong to another class of spaces with similarly nice properties, the locally compact Hausdorff spaces. In this section, we review some of the properties of these spaces.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Metrizable/Basic.lean::MetrizableSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Metrizable/Basic.html) — `MetrizableSpace` is exactly existence of a metric inducing the given topology.
:::

### Definition/convention — locally compact {#fc08-ca-u076}

::: {.unit-meta}
`FC08-CA-U076` · Appendix A, § Locally Compact Hausdorff Spaces; source L18440 · [in Mathlib]{.route-mathlib}
:::

A topological space X is said to be locally compact if every point has a neighborhood contained in a compact subset of X. If X is Hausdorff, this property has two equivalent formulations that are often more useful, as the next exercise shows. A subset of X is said to be precompact in X if its closure in X is compact.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Defs/Filter.lean::LocallyCompactSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Filter.html); [`Mathlib/Topology/Separation/Basic.lean::Bornology.relativelyCompact, Bornology.relativelyCompact.isBounded_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Separation/Basic.html) — `LocallyCompactSpace` is the compact-neighborhood condition; the relatively-compact bornology identifies precompact sets exactly by compact closure.
:::

### Theorem A.57 {#fc08-ca-u077}

::: {.unit-meta}
`FC08-CA-U077` · Appendix A, § Locally Compact Hausdorff Spaces; source L18454 · [in Mathlib]{.route-mathlib}
:::

Theorem A.57 (Proper Continuous Maps Are Closed). Suppose X is a topological space and Y is a locally compact Hausdorff space. Then every proper continuous map $F \colon X \to Y$ is clos

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Maps/Proper/CompactlyGenerated.lean::isProperMap_iff_isCompact_preimage`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Maps/Proper/CompactlyGenerated.html); [`Mathlib/Topology/Maps/Proper/Basic.lean::IsProperMap.isClosedMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Maps/Proper/Basic.html#IsProperMap.isClosedMap) — For a locally compact Hausdorff target, the compact-preimage criterion is equivalent to Mathlib properness, whose `isClosedMap` theorem gives Lee’s conclusion.
:::

### Theorem A.58 {#fc08-ca-u078}

::: {.unit-meta}
`FC08-CA-U078` · Appendix A, § Locally Compact Hausdorff Spaces; source L18460 · [in Mathlib]{.route-mathlib}
:::

Theorem A.58 (Baire Category Theorem). In a locally compact Hausdorff space or a complete metric space, every countable union of nowhere dense sets has empty interior.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Baire/CompleteMetrizable.lean::BaireSpace.of_completelyPseudoMetrizable`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Baire/CompleteMetrizable.html#BaireSpace.of_completelyPseudoMetrizable); [`Mathlib/Topology/Baire/LocallyCompactRegular.lean::BaireSpace.of_t2Space_locallyCompactSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Baire/LocallyCompactRegular.html#BaireSpace.of_t2Space_locallyCompactSpace) — Mathlib supplies Baire-space instances for complete metrizable and locally compact Hausdorff spaces; its Baire-space axiom is equivalent to the source nowhere-dense-union formulation.
:::

### Corollary A.59 {#fc08-ca-u079}

::: {.unit-meta}
`FC08-CA-U079` · Appendix A, § Locally Compact Hausdorff Spaces; source L18462 · [not formalized]{.route-unmatched}
:::

Corollary A.59. In a locally compact Hausdorff space or a complete metric space, every nonempty countable closed subset contains at least one isolated point.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib contains many constituent connectedness/compactness/properness facts, but the source row is a substantial multi-clause theorem or uses Lee’s compact-preimage definition of properness for maps not assumed continuous. No one checked owner matches the complete row. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — exhaustion of X by compact sets {#fc08-ca-u080}

::: {.unit-meta}
`FC08-CA-U080` · Appendix A, § Locally Compact Hausdorff Spaces; source L18466 · [in Mathlib]{.route-mathlib}
:::

If we add the hypothesis of second-countability to a locally compact Hausdorff space, we can prove even more. A sequence ( K _i ) _i = 1 ^∞ of compact subsets of a topological space X is called an exhaustion of X by compact sets if textstyle X = bigcup _i K _i and K _i ⊆ I n t K _i + 1 for each i .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Compactness/SigmaCompact.lean::CompactExhaustion`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/SigmaCompact.html) — `CompactExhaustion` has exactly Lee’s fields: compact `K n`, `K n ⊆ interior (K (n+1))`, and union equal to the whole space.
:::

### Proposition A.60 {#fc08-ca-u081}

::: {.unit-meta}
`FC08-CA-U081` · Appendix A, § Locally Compact Hausdorff Spaces; source L18468 · [in Mathlib]{.route-mathlib}
:::

A second-countable, locally compact Hausdorff space admits an exhaustion by compact sets.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Compactness/SigmaCompact.lean::sigmaCompactSpace_of_locallyCompact_secondCountable, CompactExhaustion.choice`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/SigmaCompact.html#CompactExhaustion.choice) — Second-countable locally compact spaces are σ-compact, and [`CompactExhaustion.choice`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CompactExhaustion.choice#doc) constructs exactly the exhaustion defined in U080.
:::

### Definition/convention — homotopic relative to A {#fc08-ca-u082}

::: {.unit-meta}
`FC08-CA-U082` · Appendix A, § Homotopy and the Fundamental Group; source L18474 · [in Mathlib]{.route-mathlib}
:::

If X and Y are topological spaces and F _0 , F _1 : X Y are continuous maps, a homotopy from ±b F _0 to cal F _1 is a continuous map H : X × I → Y satisfying beginarrayl H (x, 0) = F _0 (x), H (x, 1) = F _1 (x), endarray for all x ∈ X . If there exists a homotopy from F _0 to F _1 , we say that ±b F _0 and cal F _1 are homotopic, and write F _0 simeq F _1 . If the homotopy satisfies H ( x , t ) = F _0 ( x ) = F _1 ( x ) for all t ∈ I and all x in some subset A ⊆ X , the maps F _0 and F _1 are said to be homotopic relative to A. Both “homotopic” and “homotopic relative to A ^ast are equivalence relations on the set of all continuous maps from X to Y

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Homotopy/Basic.lean::ContinuousMap.Homotopic, ContinuousMap.Homotopic.refl, ContinuousMap.Homotopic.symm, ContinuousMap.Homotopic.trans, ContinuousMap.HomotopicRel`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Basic.html) — `Homotopic` and `HomotopicRel` are the interval-homotopy and relative-homotopy relations; the displayed refl/symm/trans theorems prove the source equivalence-relation clause.
:::

### Definition/convention — path-homotopic {#fc08-ca-u083}

::: {.unit-meta}
`FC08-CA-U083` · Appendix A, § Homotopy and the Fundamental Group; source L18482 · [in Mathlib]{.route-mathlib}
:::

Two paths $f_{0}, f_{1} \colon I \to X$ are path-homotopic, written $f_{0} \sim f_{1}$, if they are homotopic relative to $\{0,1\}$; explicitly, there is a continuous map $H \colon I \times I \to X$ with $$ H(s,0) = f_{0}(s), \quad H(s,1) = f_{1}(s) \quad (s \in I), \qquad H(0,t) = f_{0}(0) = f_{1}(0), \quad H(1,t) = f_{0}(1) = f_{1}(1) \quad (t \in I). $$ For fixed $p, q \in X$, path homotopy is an equivalence relation on the paths from $p$ to $q$; the class of $f$ is its path class $[f]$.

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Homotopy/Path.lean::Path.Homotopic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html#Path.Homotopic) — [`Path.Homotopic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Path.Homotopic#doc) is homotopy relative to the two endpoints, exactly Lee’s path-homotopy relation.
:::

### Definition/convention — its path class {#fc08-ca-u084}

::: {.unit-meta}
`FC08-CA-U084` · Appendix A, § Homotopy and the Fundamental Group; source L18488 · [in Mathlib]{.route-mathlib}
:::

For any given points $p , q \in X$ , path homotopy is an equivalence relation on the set of all paths from $p$ to $q$ . The equivalence class of a path $f$ is called its path class, and is denoted by Œf .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Homotopy/Path.lean::Path.Homotopic.Quotient`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Path.html#Path.Homotopic.Quotient) — The quotient by path homotopy is exactly the set of path classes between fixed endpoints.
:::

### Definition/convention — fundamental group of X based at {#fc08-ca-u085}

::: {.unit-meta}
`FC08-CA-U085` · Appendix A, § Homotopy and the Fundamental Group; source L18498 · [in Mathlib]{.route-mathlib}
:::

If X is a topological space and $q$ is a point in X, a loop in X based at q is a path in X from $q$ to $q$ , that is, a continuous map $f \colon I \to X$ such that $f ( 0 ) = f ( 1 ) = q$ The set of path classes of loops based at q is denoted by $\pi _ { 1 } ( X , q )$ . Equipped with the product described above, it is a group, called the fundamental group of X based at $\pmb q$ . The identity element of this group is the path class of the constant path $c _ { q } ( s ) \equiv q$ , and the inverse of $[ f ]$ is the path class of the reverse path ${ \overline { { f } } } ( s ) =$ $f ( 1 - s )$ It can

::: {.unit-lean}
**Formalized.** [`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean::FundamentalGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html) — `FundamentalGroup X q` is the automorphism group at `q` in the path-homotopy fundamental groupoid, i.e. path classes of based loops with concatenation, constant identity, and reversal inverse.
:::

### Definition/convention — source terminology/construction {#fc08-ca-u086}

::: {.unit-meta}
`FC08-CA-U086` · Appendix A, § Homotopy and the Fundamental Group; source L18500 · [not formalized]{.route-unmatched}
:::

$f ( 1 - s )$ It can be shown that for path-connected spaces, the fundamental groups based at different points are isomorphic. If X is path-connected and for some (hence every) $q \in X$ , the fundamental group $\pi _ { 1 } ( X , q )$ is the trivial group consisting of $[ c _ { q } ]$ alone, we say that X is simply connected. This means that every loop is path-homotopic to a constant path.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.62 {#fc08-ca-u087}

::: {.unit-meta}
`FC08-CA-U087` · Appendix A, § Homotopy and the Fundamental Group; source L18506 · [not formalized]{.route-unmatched}
:::

$F _ { 0 } , F _ { 1 } \colon X Y$ and $G _ { 0 } , G _ { 1 } \colon Y \to Z$ are continuous maps with $F _ { 0 } \simeq F _ { 1 }$ and $G _ { 0 } \simeq G _ { 1 }$ , then $G _ { 0 } \circ F _ { 0 } \simeq G _ { 1 } \circ F _ { 1 }$ . Similarly, $i f f _ { 0 } , f _ { 1 } \colon I \to X$ are path-homotopic and $F \colon X \to Y$ is a continuous map, then

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.64 {#fc08-ca-u088}

::: {.unit-meta}
`FC08-CA-U088` · Appendix A, § Homotopy and the Fundamental Group; source L18516 · [in Mathlib]{.route-mathlib}
:::

Proposition A.64. If X and Y are topological spaces and $F \colon X \to Y$ is a continuous map, then $F _ { * } \colon \pi _ { 1 } ( X , q ) \to \pi _ { 1 } ( Y , F ( q ) )$ is a group homomorphism, known as the homomorphism induce

::: {.unit-lean}
**Formalized.** [`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean::FundamentalGroup.map`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html#FundamentalGroup.map) — A continuous map induces exactly the stated group homomorphism on based fundamental groups.
:::

### Proposition A.65 {#fc08-ca-u089}

::: {.unit-meta}
`FC08-CA-U089` · Appendix A, § Homotopy and the Fundamental Group; source L18518 · [not formalized]{.route-unmatched}
:::

(Properties of the Induced Homomorphism). (a) Let F : X → Y and G : Y → Z be continuous maps. Then for each q ∈ X ( G ∘ F ) _* = G _* ∘ F _* : π _1 ( X , q ) → π _1 ( Z , G ( F ( q ) ) ) (b) For each space X and each q ∈ X , the homomorphism induced by the identity map Id X X X is the identity map of π _1 ( X , q ) (c) If F : X → Y is a homeomorphism, then F _* : π _1 ( X , q ) → π _1 ( Y , F ( q ) ) is an isomorphism. Thus, homeomorphic spaces have isomorphic fundamental groups.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.68 {#fc08-ca-u090}

::: {.unit-meta}
`FC08-CA-U090` · Appendix A, § Homotopy and the Fundamental Group; source L18530 · [not formalized]{.route-unmatched}
:::

(Fundamental Groups of Spheres). (a) π _1 big ( mathbb S ^1 , ( 1 , 0 ) big ) is the infinite cyclic group generated by the path class of the loop ! dot I → mathbb S ^1 given by ω ( s ) = ( cos 2 π s , sin 2 π s ) (b) I f n > 1 , mathbb S ^n is simply connected.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.69 {#fc08-ca-u091}

::: {.unit-meta}
`FC08-CA-U091` · Appendix A, § Homotopy and the Fundamental Group; source L18536 · [not formalized]{.route-unmatched}
:::

(Fundamental Groups of Product Spaces). Suppose X _1 , … , X _k are topological spaces, and let p _i : X _1 × ·s × X _k → X _i denote the ith projection map. For any points q _i ∈ X _i , i = 1 , … , k , define a map P : pi_1 (X _1 × … × X _k, (q _1, … , q _k) ) → pi_1 (X _1, q _1) × … × pi_1 (X _k, q _k) b P [ f ] = (p _1 * [ f ], … , p _k * [ f ] ). Then P is an isomorphism.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — homotopy inverse for F {#fc08-ca-u092}

::: {.unit-meta}
`FC08-CA-U092` · Appendix A, § Homotopy and the Fundamental Group; source L18552 · [not formalized]{.route-unmatched}
:::

A continuous map F : X → Y between topological spaces is said to be a homotopy equivalence if there is a continuous map G : Y → X such that F ∘ G simeq I d _Y and G ∘ F simeq I d _X . Such a map G is called a homotopy inverse for F . If there exists a homotopy equivalence between X and Y , the two spaces are said to be homotopy equivalent. For example, the inclusion map iota : mathbb S ^n - 1 ↪ ℝ ^n setminus 0 is a homotopy equivalence with homotopy inverse r ( x ) = x / ∣ x ∣ , because r ∘ iota = I d _ mathbb S ^n - 1 and iota ∘ r is homotopic to the identity map of ℝ ^n setminus 0 via the straight-line homotopy H ( x , t ) = t x + ( 1 - t ) x / ∣ x ∣

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib/TauCeti contain substantial fundamental-group and homotopy infrastructure, but this row bundles basepoint transport, composition/functoriality clauses, sphere/product computations, or a concrete deformation example without one complete checked owner at the required interface. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Theorem A.71 {#fc08-ca-u093}

::: {.unit-meta}
`FC08-CA-U093` · Appendix A, § Homotopy and the Fundamental Group; source L18554 · [in Mathlib]{.route-mathlib}
:::

(Homotopy Invariance). I f F : X → Y is a homotopy equivalence, then for each p ∈ X , F _* : π _1 ( X , p ) → π _1 ( Y , F ( p ) ) is an isomorphism.

::: {.unit-lean}
**Formalized.** [`Mathlib/AlgebraicTopology/FundamentalGroupoid/InducedMaps.lean::FundamentalGroupoidFunctor.equivOfHomotopyEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/InducedMaps.html#FundamentalGroupoidFunctor.equivOfHomotopyEquiv); [`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean::FundamentalGroup.map`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.html#FundamentalGroup.map) — The equivalence of fundamental groupoids induced by a homotopy equivalence restricts at each basepoint to the source induced fundamental-group isomorphism.
:::

### Definition/convention — covering map {#fc08-ca-u094}

::: {.unit-meta}
`FC08-CA-U094` · Appendix A, § Covering Maps; source L18560 · [not formalized]{.route-unmatched}
:::

Suppose E and X are topological spaces. A map π : E → X is called a covering map if E and X are connected and locally path-connected, π is surjective and continuous, and each point p ∈ X has a neighborhood U that is evenly covered by π, meaning that each component of π ^- 1 ( U ) is mapped homeomorphically onto U by π. In this case, X is called the base of the covering, and E is called a covering space of X . If U is an evenly covered subset of X, the components of π ^- 1 ( U ) are called the sheets of the covering over U .

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has covering and lifting infrastructure and TauCeti has later universal-cover classification results, but Lee’s row uses an augmented covering-map convention or a locally-simply-connected/universal-cover statement whose full hypotheses and uniqueness conclusion are not owned by one compatible checked declaration without a nontrivial bridge. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — lift of F {#fc08-ca-u095}

::: {.unit-meta}
`FC08-CA-U095` · Appendix A, § Covering Maps; source L18576 · [not formalized]{.route-unmatched}
:::

$\pi \colon E \to X$ is a covering map and $F \colon B \to X$ is a continuous map, a lift of F is a continuous map $\widetilde { F } \colon B \to E$ such that $\pi \circ { \tilde { F } } = F$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has covering and lifting infrastructure and TauCeti has later universal-cover classification results, but Lee’s row uses an augmented covering-map convention or a locally-simply-connected/universal-cover statement whose full hypotheses and uniqueness conclusion are not owned by one compatible checked declaration without a nontrivial bridge. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.77 {#fc08-ca-u096}

::: {.unit-meta}
`FC08-CA-U096` · Appendix A, § Covering Maps; source L18580 · [in Mathlib]{.route-mathlib}
:::

(Lifting Properties of Covering Maps). Suppose π E X is a covering map. (a) UNIQUE LIFTING PROPERTY: If B is a connected space and F : B → X is a continuous map, then any two lifts of F that agree at one point are identical. (b) PATH LIFTING PROPERTY: If f : I → X is a path, then for any point e ∈ E such that π ( e ) = f ( 0 ) , there exists a unique lift tilde(f) _e : I E of f such that widetilde f ( 0 ) = e (c) MONODROMY THEOREM: If f; g I X are path-homotopic paths and tilde(f) _e , tilde(g) _e : I E are their lifts starting at the same point e ∈ E , then tilde(f) _e and tilde(g) _e are path-homotopic and widetilde f _e ( 1 ) = widetilde g _e ( 1 )

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Covering/Basic.lean::IsCoveringMap.eq_of_comp_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Covering/Basic.html#IsCoveringMap.eq_of_comp_eq); [`Mathlib/Topology/Homotopy/Lifting.lean::IsCoveringMap.exists_path_lifts, IsCoveringMap.liftPath, IsCoveringMap.homotopicRel_liftPath`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Lifting.html) — `eq_of_comp_eq` is unique lifting from one agreed point on a connected source; path lifting gives the unique lifted path, and `homotopicRel_liftPath` gives homotopic lifts and hence equal lifted endpoints.
:::

### Proposition A.78 {#fc08-ca-u097}

::: {.unit-meta}
`FC08-CA-U097` · Appendix A, § Covering Maps; source L18588 · [in Mathlib]{.route-mathlib}
:::

(Lifting Criterion). Suppose π : E → X is a covering map, Y is a connected and locally path-connected space, and F Y X is a continuous map. Let y ∈ Y and e ∈ E be such that π ( e ) = F ( y ) . Then there exists a lift tilde(F) : Y → dot E of F satisfying widetilde F ( y ) = e if and only if F _* ( π _1 ( Y , y ) ) ⊆ π _* ( π _1 ( E , e ) )

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Homotopy/Lifting.lean::IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Homotopy/Lifting.html#IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le) — This is the fundamental-group image containment criterion for existence and uniqueness of a lift with prescribed basepoint, exactly Lee’s lifting criterion.
:::

### Proposition A.79 {#fc08-ca-u098}

::: {.unit-meta}
`FC08-CA-U098` · Appendix A, § Covering Maps; source L18590 · [not formalized]{.route-unmatched}
:::

(Coverings of Simply Connected Spaces). If X is a simply connected space, then every covering map π : E → X is a homeomorphism.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has covering and lifting infrastructure and TauCeti has later universal-cover classification results, but Lee’s row uses an augmented covering-map convention or a locally-simply-connected/universal-cover statement whose full hypotheses and uniqueness conclusion are not owned by one compatible checked declaration without a nontrivial bridge. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — locally simply connected {#fc08-ca-u099}

::: {.unit-meta}
`FC08-CA-U099` · Appendix A, § Covering Maps; source L18592 · [not formalized]{.route-unmatched}
:::

A topological space is said to be locally simply connected if it admits a basis of simply connected open subsets.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has covering and lifting infrastructure and TauCeti has later universal-cover classification results, but Lee’s row uses an augmented covering-map convention or a locally-simply-connected/universal-cover statement whose full hypotheses and uniqueness conclusion are not owned by one compatible checked declaration without a nontrivial bridge. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition A.80 {#fc08-ca-u100}

::: {.unit-meta}
`FC08-CA-U100` · Appendix A, § Covering Maps; source L18594 · [not formalized]{.route-unmatched}
:::

Proposition A.80 (Existence of a Universal Covering Space). If X is a connected and locally simply connected topological space, there exists a simply connected topological space $\widetilde { X }$ and a covering map  ${ \tilde { X } } \to X . \ I f { \widehat { \pi } } \colon { \hat { X } } \to { \bar { X } }$ is any other simply connected covering of X, there is a homeomorphism $\varphi \colon { \tilde { X } } { \hat { X } }$ such that ${ \hat { \pi } } \circ \varphi = \pi$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has covering and lifting infrastructure and TauCeti has later universal-cover classification results, but Lee’s row uses an augmented covering-map convention or a locally-simply-connected/universal-cover statement whose full hypotheses and uniqueness conclusion are not owned by one compatible checked declaration without a nontrivial bridge. Strict whole-row semantics reject partial clause coverage and unbridged reconstruction.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — universal covering space of X {#fc08-ca-u101}

::: {.unit-meta}
`FC08-CA-U101` · Appendix A, § Covering Maps; source L18596 · [in Mathlib]{.route-mathlib}
:::

The simply connected covering space tilde(X) whose existence and uniqueness (up to homeomorphism) are guaranteed by this proposition is called the universal covering space of X .

::: {.unit-lean}
**Formalized.** [`Mathlib/Topology/Covering/Basic.lean::IsCoveringMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Covering/Basic.html); [`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean::SimplyConnectedSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.html) — A universal covering space is exactly a covering map whose total space is simply connected; these two checked interfaces encode the source definition.
:::

