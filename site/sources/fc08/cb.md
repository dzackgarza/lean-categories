---
title: "FC08 — John M. Lee, Introduction to Smooth Manifolds, 2nd ed. (2013)"
---

FC08 — Lee, *Introduction to Smooth Manifolds*.

This chapter contains 50 definitions, 2 theorems, 13 propositions, 1 lemma, 4 corollaries, 5 examples, 8 constructions and 7 conventions.

Of the 90 statements checked against Lean, 81 are formalized somewhere and 9 are not.

| Status | Statements | Share | What it means |
| --- | ---: | ---: | --- |
| [in Mathlib]{.route-mathlib} | 81 | 90% | Mathlib states and proves it. |
| [not formalized]{.route-unmatched} | 9 | 10% | A documented search found no Lean statement of it anywhere. |
| **checked in total** | **90** | | |

::: {.callout-note collapse="true"}
## Which versions of Lean and Mathlib were searched

- Canonical source block: FC08 Lee, Appendix B, `FC08-CB-U001`–`FC08-CB-U090`, exactly 90 unique contiguous rows retrieved from [FC08 — John M. Lee, Introduction to Smooth Manifolds](/sources/fc08/) through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then indexed/current/external Lean search surfaces. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix B has 81 pinned `mathlib` rows and 9 dated `unmatched` rows. Positive rows are: U001, U003, U004, U005, U006, U007, U008, U009, U010, U011, U012, U013, U015, U016, U017, U018, U019, U020, U021, U022, U023, U024, U025, U026, U027, U028, U029, U030, U031, U032, U033, U034, U035, U036, U037, U038, U040, U041, U042, U043, U044, U046, U047, U048, U049, U050, U051, U053, U054, U055, U056, U057, U058, U060, U061, U062, U063, U064, U065, U066, U068, U069, U070, U071, U072, U073, U074, U075, U076, U077, U079, U080, U081, U083, U084, U085, U086, U087, U088, U089, U090.
- `/tmp/fc08-cb-witness.lean` compiles at exact P and checks the principal declaration surface used here: modules/submodules, span, convexity, linear independence, bases/finrank, quotients/projections, matrices/rank/determinants, inner-product/Gram–Schmidt APIs, bounded linear maps, products, and direct sums.
- The finite-dimensional linear-algebra layer is especially complete. Mathlib’s `Basis`, `finrank`, `LinearMap`, `LinearEquiv`, [`Basis.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.toMatrix#doc), rank-nullity, matrix rank/transpose, determinant, adjugate/nonsingular inverse, and triangular/block-triangular APIs give direct owners for the standard statements rather than requiring local rederivations.
- Gram–Schmidt is also exact: `gramSchmidtBasis`, `gramSchmidtNormed_orthonormal`, and `span_gramSchmidt_Iic` give an orthonormal basis while preserving every initial span, matching Lee Proposition B.40 at source generality.
- The direct-product/direct-sum section maps to [`LinearMap.pi`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.pi#doc), [`DirectSum.lof`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirectSum.lof#doc), [`DirectSum.toModule`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirectSum.toModule#doc), its uniqueness theorem, and [`DirectSum.IsInternal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirectSum.IsInternal#doc). Mathlib uses a finite-support dependent-function representation (`DFinsupp`) for external direct sums, mathematically equivalent to Lee’s finite-support submodule of the product.
- The nine unmatched rows are deliberately narrow. U002 and U052 are terminology only; U014/U059/U078 lack canonical bundled owners for Lee’s exact naming/predicate; U039 and U045 miss the exact general theorem statement; U067 bundles angle terminology not found canonically; U082 bundles Pi construction with an AC nonemptiness assertion. Adjacent ingredients were not promoted under strict whole-row semantics.
- Broad current GitHub/indexed searches found additional executable Gram–Schmidt projects, but none improves on the pinned Mathlib owner or supplies a missing whole-row route. No external package import was justified.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u001}

::: {.unit-meta}
`FC08-CB-U001` · Appendix B, § Vector Spaces; source L18604 · [in Mathlib]{.route-mathlib}
:::

Let R denote the field of real numbers. A vector space over (or real vector space) is a set V endowed with two operations: vector addition $V \times V \to V$ , denoted by $( v , w ) \mapsto v + w$ , and scalar multiplication $\mathbb { R } \times V V$ , denoted by $( a , v ) \mapsto a v$ satisfying the following properties: (i) V is an abelian group under vector addition.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Defs.lean::Module`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html) — `Module ℝ V` is Mathlib’s canonical real-vector-space structure, with addition supplied by the additive-group structure and scalar multiplication/laws by `Module`.
:::

### Definition/convention — vectors {#fc08-cb-u002}

::: {.unit-meta}
`FC08-CB-U002` · Appendix B, § Vector Spaces; source L18632 · [not formalized]{.route-unmatched}
:::

The elements of a vector space are usually called vectors. When it is necessary to distinguish them from vectors, elements of the underlying field (which is R unless otherwise specified) are called scalars. L

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — This row is solely source terminology (“vectors” versus “scalars”), not a mathematical structure or theorem with a canonical Lean declaration; the underlying `Module` is mapped in U001.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — subspace of V {#fc08-cb-u003}

::: {.unit-meta}
`FC08-CB-U003` · Appendix B, § Vector Spaces; source L18634 · [in Mathlib]{.route-mathlib}
:::

Let V be a vector space. A subset $W \subseteq V$ that is closed under vector addition and scalar multiplication is itself a vector space with the same operations, and is called a subspace of V . To avoid confusion with the use of the word “subspace” in topology, we sometimes use the term linear subspace for a subspace of a vector space in this sense, and topological subspace for a subset of a topological space endowed with the subspace topology.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Span/Defs.lean::Submodule, Submodule.span, subset_span, span_le`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Span/Defs.html#Submodule.span) — `Submodule ℝ V` is a linear subspace and [`Submodule.span`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.span#doc) is the least submodule containing a set; `subset_span`/`span_le` give precisely Lee’s closure/minimality characterization.
:::

### Convention/notation — linear combination of the vectors v {#fc08-cb-u004}

::: {.unit-meta}
`FC08-CB-U004` · Appendix B, § Vector Spaces; source L18636 · [in Mathlib]{.route-mathlib}
:::

A finite sum of the form $\textstyle \sum _ { i = 1 } ^ { k } a ^ { i } v _ { i }$ , where $a ^ { i }$ are scalars and $v _ { i } \in V$ , is called a linear combination of the vectors $\pmb { v } _ { 1 } , \ldots , \pmb { v } _ { k }$ . (The reason we write the coefficients $a ^ { i }$ with superscripts instead of subscripts is to be consistent with the Einstein summation convention, explained in Chapter 1.) If S is an arbitrary subset of V , the set of all linear combinations of elements of S is called the span of S and is denoted by span.S /; it is easily seen to be the smallest subspace of V containing S. If $V = \operatorname { s p a n } ( S )$ , we say that S spans $V$ . By convention, a linear combination of no elements is considered to sum to zero, and the span of the empty set whose fiber at $x \in M$ is $\mathbb { R } \times T _ { x } ^ { * } M$ .

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Span/Defs.lean::Submodule, Submodule.span, subset_span, span_le`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Span/Defs.html#Submodule.span) — `Submodule ℝ V` is a linear subspace and [`Submodule.span`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.span#doc) is the least submodule containing a set; `subset_span`/`span_le` give precisely Lee’s closure/minimality characterization.
:::

### Definition/convention — convex {#fc08-cb-u005}

::: {.unit-meta}
`FC08-CB-U005` · Appendix B, § Vector Spaces; source L18638 · [in Mathlib]{.route-mathlib}
:::

If p and q are points of V , the line segment from p to q is the set $\{ ( 1 - t ) p + t q :$ $0 \leq t \leq 1 \}$ . A subset $B \subseteq V$ is said to be convex if for every two points $p , q \in B$ the line segment from $p$ to q is contained in B. ##

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Convex/Basic.lean::Convex`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html) — `Convex ℝ B` is exactly closure of `B` under real line segments/convex combinations, equivalent to Lee’s segment definition.
:::

### Convention/notation — linearly dependent {#fc08-cb-u006}

::: {.unit-meta}
`FC08-CB-U006` · Appendix B, § Bases and Dimension; source L18642 · [in Mathlib]{.route-mathlib}
:::

Suppose V is a vector space. A subset $S \subseteq V$ is said to be linearly dependent if there exists a linear relation of the form $\textstyle \sum _ { i = 1 } ^ { k } a ^ { i } v _ { i } = 0$ , where $v _ { 1 } , \ldots , v _ { k }$ are distinct elements of S and at least one of the coefficients $a ^ { i }$ is nonzero; S is said to be linearly independent otherwise. In other words, S is linearly independent if and only if the only linear combination of distinct elements of S that sums to zero is the one in which all the scalar coefficients are zero. Note that every set containing the zero vector is linearly dependent. By convention, the empty set is considered to be linearly independent.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/LinearIndependent/Defs.lean::LinearIndepOn, LinearIndependent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent/Defs.html) — `LinearIndepOn` handles a set of vectors and `LinearIndependent` an indexed family; these are exactly Lee’s set and ordered-tuple notions, including repeated vectors through noninjectivity.
:::

### Definition/convention — k-tuple {#fc08-cb-u007}

::: {.unit-meta}
`FC08-CB-U007` · Appendix B, § Bases and Dimension; source L18644 · [in Mathlib]{.route-mathlib}
:::

It is frequently important to work with ordered k-tuples of vectors in $V :$ ; such a k-tuple is denoted by $( v _ { 1 } , \ldots , v _ { k } )$ or $( v _ { i } )$ , with parentheses instead of braces to distinguish it from the (unordered) set of elements $\{ v _ { 1 } , \ldots , v _ { k } \}$ . When we consider ordered k-tuples, linear dependence takes on a slightly different meaning. We say that $( v _ { 1 } , \ldots , v _ { k } )$ is a linearly dependent k-tuple if there are scalars $( a ^ { 1 } , \ldots , a ^ { k } )$ not all zero, such that $\textstyle \sum _ { i = 1 } ^ { k } a ^ { i } v _ { i } = 0$ ; it is a linearly independent k-tuple otherwise. The only difference between a linearly independent set and a linearly independent $k { - } t u p l e$ is that the latter cannot have repeated vectors. For example if $v \in V$ is a nonzero vector, the ordered pair $( v , v )$ is linearly dependent, while the set $\{ v , v \} = \{ v \}$ is linearly independent. On the other hand, if $( v _ { 1 } , \ldots , v _ { k } )$ is any linearly independent k-tuple, then the set $\{ v _ { 1 } , \ldots , v _ { k } \}$ is also linearly independent.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/LinearIndependent/Defs.lean::LinearIndepOn, LinearIndependent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/LinearIndependent/Defs.html) — `LinearIndepOn` handles a set of vectors and `LinearIndependent` an indexed family; these are exactly Lee’s set and ordered-tuple notions, including repeated vectors through noninjectivity.
:::

### Definition/convention — finite-dimensional {#fc08-cb-u008}

::: {.unit-meta}
`FC08-CB-U008` · Appendix B, § Bases and Dimension; source L18656 · [in Mathlib]{.route-mathlib}
:::

A basis for V (plural: bases) is a subset $S \subseteq V$ that is linearly independent and spans V . If S is a basis for V , every element of V has a unique expression as a linear combination of elements of S. If V has a finite basis, then $V$ is said to be finite-dimensional, and otherwise it is infinite-dimensional. The trivial vector space $\{ 0 \}$ is finite-dimensional, because it has the empty set as a basis.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Basis/Defs.lean::Basis, Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html#Basis.repr); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — A `Basis ι ℝ V` is a linearly independent spanning indexed family, [`Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.repr#doc) gives unique coordinates, and finite index types together with [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) encode finite dimension and ordered bases.
:::

### Definition/convention — ordered basis for V {#fc08-cb-u009}

::: {.unit-meta}
`FC08-CB-U009` · Appendix B, § Bases and Dimension; source L18658 · [in Mathlib]{.route-mathlib}
:::

If V is finite-dimensional, an ordered basis for V is a basis endowed with a specific ordering of the basis vectors, or equivalently a linearly independent n-tuple $\left( E _ { i } \right)$ that spans $V$ . For most purposes, ordered bases are more useful than unordered bases, so we always assume, often without comment, that each basis comes with a given ordering.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Basis/Defs.lean::Basis, Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html#Basis.repr); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — A `Basis ι ℝ V` is a linearly independent spanning indexed family, [`Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.repr#doc) gives unique coordinates, and finite index types together with [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) encode finite dimension and ordered bases.
:::

### Definition/convention — components of v {#fc08-cb-u010}

::: {.unit-meta}
`FC08-CB-U010` · Appendix B, § Bases and Dimension; source L18666 · [in Mathlib]{.route-mathlib}
:::

The numbers $v ^ { i }$ are called the components of v with respect to this basis, and the ordered n-tuple $\left( v ^ { 1 } , \ldots , v ^ { n } \right)$ is called its basis representation. (Here is an example of a definition that requires an ordered basis.)

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Basis/Defs.lean::Basis, Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html#Basis.repr); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — A `Basis ι ℝ V` is a linearly independent spanning indexed family, [`Basis.repr`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.repr#doc) gives unique coordinates, and finite index types together with [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) encode finite dimension and ordered bases.
:::

### Lemma B.2 {#fc08-cb-u011}

::: {.unit-meta}
`FC08-CB-U011` · Appendix B, § Bases and Dimension; source L18668 · [in Mathlib]{.route-mathlib}
:::

requires an ordered basis.) Lemma B.2. Let V be a vector space. If V is spanned by a set of n vectors, then every subset of V containing more than n vectors is linearly dependent.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Dimension/Constructions.lean::finrank_span_le_card, finrank_span_eq_card`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Constructions.html); [`Mathlib/LinearAlgebra/Dimension/OrzechProperty.lean::linearIndependent_iff_card_le_finrank_span`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/OrzechProperty.html) — For a finite family, Mathlib identifies the cardinality of an independent family with the finrank of its span and bounds span finrank by the number of generators. Applied to an `n`-element spanning family, this gives Lee Lemma B.2 exactly.
:::

### Proposition B.3 {#fc08-cb-u012}

::: {.unit-meta}
`FC08-CB-U012` · Appendix B, § Bases and Dimension; source L18674 · [in Mathlib]{.route-mathlib}
:::

n + 1 } \}$ is linearly dependent by Exercise B.1(b).  Proposition B.3. If V is a finite-dimensional vector space, all bases for V contain the same number of elements. Proof. If $

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean::Module.finrank_eq_card_basis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.html#Module.finrank_eq_card_basis); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — [`Module.finrank_eq_card_basis`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank_eq_card_basis#doc) proves all finite bases have the same cardinality; [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) is therefore exactly Lee’s dimension.
:::

### Definition/convention — dimension of V {#fc08-cb-u013}

::: {.unit-meta}
`FC08-CB-U013` · Appendix B, § Bases and Dimension; source L18678 · [in Mathlib]{.route-mathlib}
:::

Because of the preceding proposition, if V is a finite-dimensional vector space, it makes sense to define the dimension of V , denoted by dim V , to be the number of elements in any basis.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean::Module.finrank_eq_card_basis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.html#Module.finrank_eq_card_basis); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — [`Module.finrank_eq_card_basis`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank_eq_card_basis#doc) proves all finite bases have the same cardinality; [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) is therefore exactly Lee’s dimension.
:::

### Definition/convention — codimension of S in V to be dim V dim S {#fc08-cb-u014}

::: {.unit-meta}
`FC08-CB-U014` · Appendix B, § Bases and Dimension; source L18694 · [not formalized]{.route-unmatched}
:::

If S is a subspace of a finite-dimensional vector space V , we define the codimension of S in V to be dim V dim S. By virtue of Exercise B.4(b), the codimension of S is always nonnegative, and is zero if and only if S V . A (linear) hyperplane is a linear subspace of codimension 1.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has quotient dimensions and [`Submodule.finrank_quotient_add_finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.finrank_quotient_add_finrank#doc), so Lee’s numerical codimension is easy to express, but no canonical `codimension`/linear-hyperplane owner matching the entire terminology row was found. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Example B.6 {#fc08-cb-u015}

::: {.unit-meta}
`FC08-CB-U015` · Appendix B, § Bases and Dimension; source L18696 · [in Mathlib]{.route-mathlib}
:::

vector space under the usual operations of vector addition and scalar multiplication: $$ \begin{array}{c} (x ^ {1}, \ldots , x ^ {n}) + (y ^ {1}, \ldots , y ^ {n}) = (x ^ {1} + y ^ {1}, \ldots , x ^ {n} + y ^ {n}), \\ a (x ^ {1}, \ldots , x ^ {n}) = (a x ^ {1}, \ldots , a x ^ {n}). \end{array} $$ There is a natural basis $( e _ { 1 } , \ldots , e _ { n } )$ for $\mathbb { R } ^ { n }$ , called the standard basis, where $e _ { i } =$ $( 0 , \ldots , 1 , \ldots , 0 )$ is the vector with a 1 in the ith place and zeros elsewhere; thus R has dimension n, as one would expect. Any element $x \in \mathbb { R } ^ { n }$ can be written $\begin{array} { r } { \left( x ^ { 1 } , . . . , x ^ { n } \right) = \sum _ { i = 1 } ^ { n } x ^ { i } e _ { i } } \end{array}$ , so its components with respect to the standard basis are just its coordina t there is no 1-form  on M such that the tautological form $\tau \in \Omega ^ { 1 } ( T ^ { * } M )$ is equal to the pullback $\pi ^ { * } \sigma$ 22-13.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/StdBasis.lean::Pi.basisFun`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/StdBasis.html#Pi.basisFun); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — [`Pi.basisFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Pi.basisFun#doc) is the standard coordinate basis of finite function spaces; specializing the scalar field to `ℝ` or `ℂ` gives the standard bases of `ℝ^n` and `ℂ^n`, with finrank `n`.
:::

### Example B.7 {#fc08-cb-u016}

::: {.unit-meta}
`FC08-CB-U016` · Appendix B, § Bases and Dimension; source L18706 · [in Mathlib]{.route-mathlib}
:::

(Complex Euclidean Spaces). With scalar multiplication and vector addition defined as in the real case, $n$-dimensional complex Euclidean space $\mathbb{C}^{n}$ is a complex vector space; the vectors $(e_{1},\dots,e_{n})$ form a basis over $\mathbb{C}$, so $\mathbb{C}^{n}$ has complex dimension $n$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/StdBasis.lean::Pi.basisFun`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/StdBasis.html#Pi.basisFun); [`Mathlib/LinearAlgebra/Dimension/Finrank.lean::Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html#Module.finrank) — [`Pi.basisFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Pi.basisFun#doc) is the standard coordinate basis of finite function spaces; specializing the scalar field to `ℝ` or `ℂ` gives the standard bases of `ℝ^n` and `ℂ^n`, with finrank `n`.
:::

### Convention/notation — the {#fc08-cb-u017}

::: {.unit-meta}
`FC08-CB-U017` · Appendix B, § Bases and Dimension; source L18710 · [in Mathlib]{.route-mathlib}
:::

If S and T are subspaces of a vector space V , the notation $S + T$ denotes the set of all vectors of the form $v + w$ , where $v \in S$ and $w \in T$ . It is easily seen to be a subspace of V , and in fact is the subspace spanned by $S \cup T$ . If $S + T = V$ and $S \cap T = \{ 0 \}$ , then V is said to be the (internal) direct sum of S and T , and we write $V = S \oplus T$ . Two linear subspaces $S , T \subseteq V$ are said to be complementary subspaces if $V = S \oplus T$ . In this case, every vector in V has a unique expression as a sum of an element of S plus an element of $T$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Projection.lean::IsCompl, Submodule.prodEquivOfIsCompl`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projection.html#Submodule.prodEquivOfIsCompl) — For submodules, lattice supremum is the sum and `IsCompl S T` is exactly `S ⊓ T = ⊥` together with `S ⊔ T = ⊤`; `prodEquivOfIsCompl` gives the unique decomposition.
:::

### Definition/convention — affine subspace of V parallel to S {#fc08-cb-u018}

::: {.unit-meta}
`FC08-CB-U018` · Appendix B, § Bases and Dimension; source L18722 · [in Mathlib]{.route-mathlib}
:::

Any subset of V of the form $$ v + S = \{v + w: w \in S \} $$ for some fixed $v \in V$ is called an affine subspace of V parallel to S . If S is a linear hyperplane, then any affine subspace parallel to S is called an affine hyperplane.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean::AffineSubspace, affineSpan`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.html) — `AffineSubspace ℝ V` canonically represents translates of linear subspaces; its direction submodule gives the parallel linear space, including affine hyperplanes by codimension one.
:::

### Definition/convention — coset of S determined by v {#fc08-cb-u019}

::: {.unit-meta}
`FC08-CB-U019` · Appendix B, § Bases and Dimension; source L18738 · [in Mathlib]{.route-mathlib}
:::

For each vector $v \in V$, the affine subspace $v + S$ is called the coset of $S$ determined by $v$, and the set $V/S$ of cosets is the quotient of $V$ by $S$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Quotient/Defs.lean::Submodule.Quotient, Submodule.mkQ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Quotient/Defs.html) — `V ⧸ S` is Mathlib’s quotient module by the coset relation and [`Submodule.mkQ`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.mkQ#doc) is the quotient projection, exactly Lee’s `V/S`.
:::

### Definition/convention — linear functional {#fc08-cb-u020}

::: {.unit-meta}
`FC08-CB-U020` · Appendix B, § Linear Maps; source L18756 · [in Mathlib]{.route-mathlib}
:::

Let V and W be real vector spaces. A map $T \colon V \to W$ \boldsymbol { w }$ for all vectors $v , w \in V$ and all scalars a; b. (Because of the close connection between linear maps and matrix multiplication described below, we generally write the action of a linear map T on a vector v as T v without parentheses, unless parentheses are needed for grouping.) In the special case $W = \mathbb { R }$ , a linear map from V to R is usually called a linear functional on V . If $

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html); [`Mathlib/LinearAlgebra/Dual/Defs.lean::Module.Dual`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Defs.html#Module.Dual); [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap.ker, LinearMap.range`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html) — `LinearMap` is the canonical linear-map object; [`Module.Dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Dual#doc) is the scalar-valued special case, and [`LinearMap.ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.ker#doc)/`range` are exactly Lee’s kernel and image subspaces.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u021}

::: {.unit-meta}
`FC08-CB-U021` · Appendix B, § Linear Maps; source L18758 · [in Mathlib]{.route-mathlib}
:::

a linear map from V to R is usually called a linear functional on V . If $T \colon V \to W$ is a linear map, the kernel or null space of T , denoted by Ker T or $T ^ { - 1 } ( 0 )$ , is the set $\{ v \in V : T v = 0 \}$ , and the image of T , denoted by Im T or $T ( V )$ , is the set $\{ w \in W : w = T \ i$ for some and find the flow of the corresponding infinitesimal symmetry.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html); [`Mathlib/LinearAlgebra/Dual/Defs.lean::Module.Dual`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Defs.html#Module.Dual); [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap.ker, LinearMap.range`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html) — `LinearMap` is the canonical linear-map object; [`Module.Dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Dual#doc) is the scalar-valued special case, and [`LinearMap.ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.ker#doc)/`range` are exactly Lee’s kernel and image subspaces.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u022}

::: {.unit-meta}
`FC08-CB-U022` · Appendix B, § Linear Maps; source L18760 · [in Mathlib]{.route-mathlib}
:::

Given a subspace $S \subseteq V$ and a complementary subspace $T$, there is a unique linear map $\pi \colon V \to S$ defined by $$ \pi(v+w) = v \quad \text{for } v \in S,\ w \in T. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Projection.lean::Submodule.projectionOnto, Submodule.ker_projectionOnto, Submodule.range_projectionOnto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projection.html) — Given complementary submodules, `projectionOnto` is the unique linear projection onto the first summand and Mathlib proves its kernel is the second summand and its range is all of the target subtype.
:::

### Construction/definition — projection onto S {#fc08-cb-u023}

::: {.unit-meta}
`FC08-CB-U023` · Appendix B, § Linear Maps; source L18766 · [in Mathlib]{.route-mathlib}
:::

This map is called the projection onto S with kernel T .

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Projection.lean::Submodule.projectionOnto, Submodule.ker_projectionOnto, Submodule.range_projectionOnto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projection.html) — Given complementary submodules, `projectionOnto` is the unique linear projection onto the first summand and Mathlib proves its kernel is the second summand and its range is all of the target subtype.
:::

### Definition/convention — isomorphism {#fc08-cb-u024}

::: {.unit-meta}
`FC08-CB-U024` · Appendix B, § Linear Maps; source L18768 · [in Mathlib]{.route-mathlib}
:::

If V and W are vector spaces, a bijective linear map $T \colon V \to W$ is called an isomorphism. In this case, there is a unique inverse map $T ^ { - 1 } \colon W \to V$ , and the following computation shows that $T ^ { - 1 }$ is also linear: $$ \begin{array}{l} a T ^ {- 1} v + b T ^ {- 1} w = T ^ {- 1} T \left(a T ^ {- 1} v + b T ^ {- 1} w\right) \\ \qquad = T ^ {- 1} \left(a T T ^ {- 1} v + b T T ^ {- 1} w\right) \quad \text {(by linearity of T)} \\ \qquad = T ^ {- 1} (a v + b w). \end{array} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Equiv/Defs.lean::LinearEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Equiv/Defs.html) — `LinearEquiv` is a bijective linear map with a linear inverse, exactly Lee’s isomorphism/invertibility notion for vector spaces.
:::

### Definition/convention — invertible {#fc08-cb-u025}

::: {.unit-meta}
`FC08-CB-U025` · Appendix B, § Linear Maps; source L18774 · [in Mathlib]{.route-mathlib}
:::

A bijective linear map is also said to be invertible, and if there exists an isomorphism $T \colon V \to W$ then $V$ and $W$ are isomorphic.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Equiv/Defs.lean::LinearEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Equiv/Defs.html) — `LinearEquiv` is a bijective linear map with a linear inverse, exactly Lee’s isomorphism/invertibility notion for vector spaces.
:::

### Example B.12 {#fc08-cb-u026}

::: {.unit-meta}
`FC08-CB-U026` · Appendix B, § Linear Maps; source L18776 · [in Mathlib]{.route-mathlib}
:::

Example B.12. Let V be an n-dimensional real vector space, and $( E _ { 1 } , \ldots , E _ { n } )$ be an ordered basis for V . Define a map $E \colon \mathbb { R } ^ { n } \to V$ by $$ E \left(x ^ {1}, \dots , x ^ {n}\right) = x ^ {1} E _ {1} + \dots + x ^ {n} E _ {n}. $$ Then E is linear and bijective, so it is an isomorphism, called the basis isomorphism determined by this basis. Thus, every n-dimensional real vector space is isomorphic to R.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Basis/Defs.lean::Basis.equivFun`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Defs.html#Basis.equivFun) — [`Basis.equivFun`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.equivFun#doc) is the coordinate linear equivalence `V ≃ₗ[ℝ] (ι → ℝ)`; its inverse is Lee’s basis isomorphism from coordinate space to `V`.
:::

### Definition/convention — affine map {#fc08-cb-u027}

::: {.unit-meta}
`FC08-CB-U027` · Appendix B, § Linear Maps; source L18806 · [in Mathlib]{.route-mathlib}
:::

If $V$ and $W$ are vector spaces, a map $F \colon V \to W$ is an affine map if it can be written $F(v) = w + Tv$ for some linear map $T \colon V \to W$ and some fixed $w \in W$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean::AffineMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineMap.html) — An `AffineMap ℝ V W` is a map with a linear part preserving affine combinations; for vector spaces it is exactly a translation plus a linear map, Lee’s `w + T v`.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u028}

::: {.unit-meta}
`FC08-CB-U028` · Appendix B, § Linear Maps; source L18812 · [in Mathlib]{.route-mathlib}
:::

Now suppose V and W are finite-dimensional vector spaces with ordered bases ( E _1 , … , E _n ) and ( F _1 , … , F _m ) , respectively. If T : V → W is a linear map, the matrix of T with respect to these bases is the m × n matrix $$ A = (A^{i}_{j}) = \begin{pmatrix} A^{1}_{1} & \cdots & A^{1}_{n} \\ \vdots & \ddots & \vdots \\ A^{m}_{1} & \cdots & A^{m}_{n} \end{pmatrix}, $$ whose $j$th column consists of the components of $TE_{j}$ with respect to the basis $(F_{i})$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_comp, LinearMap.toMatrix_id`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html); [`Mathlib/Data/Matrix/Basic.lean::Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.mul_apply) — [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) is the matrix in chosen bases; `toMatrix_mulVec_repr` is coordinate matrix-vector multiplication, [`Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.mul_apply#doc) is the entry formula, and `toMatrix_comp`/`toMatrix_id` give composition and identity matrices.
:::

### Convention/notation — source terminology/construction {#fc08-cb-u029}

::: {.unit-meta}
`FC08-CB-U029` · Appendix B, § Linear Maps; source L18830 · [in Mathlib]{.route-mathlib}
:::

Writing the components of a vector with respect to a basis as a column matrix, the matrix representation of $w = Tv$ is given by matrix multiplication, $$ \begin{pmatrix} w^{1} \\ \vdots \\ w^{m} \end{pmatrix} = \begin{pmatrix} A^{1}_{1} & \cdots & A^{1}_{n} \\ \vdots & \ddots & \vdots \\ A^{m}_{1} & \cdots & A^{m}_{n} \end{pmatrix} \begin{pmatrix} v^{1} \\ \vdots \\ v^{n} \end{pmatrix}, $$ or more succinctly $w^{i} = \sum_{j=1}^{n} A^{i}_{j}v^{j}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_comp, LinearMap.toMatrix_id`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html); [`Mathlib/Data/Matrix/Basic.lean::Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.mul_apply) — [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) is the matrix in chosen bases; `toMatrix_mulVec_repr` is coordinate matrix-vector multiplication, [`Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.mul_apply#doc) is the entry formula, and `toMatrix_comp`/`toMatrix_id` give composition and identity matrices.
:::

### Convention/notation — matrix product AB {#fc08-cb-u030}

::: {.unit-meta}
`FC08-CB-U030` · Appendix B, § Linear Maps; source L18842 · [in Mathlib]{.route-mathlib}
:::

Insofar as possible, we denote the row index of a matrix by a superscript and the column index by a subscript, so that $A _ { j } ^ { i }$ represents the element in the ith row and j th column. Thus the entry in the ith row and $j$ th column of a matrix product AB is given by $$ (A B) _ {j} ^ {i} = \sum_ {k = 1} ^ {n} A _ {k} ^ {i} B _ {j} ^ {k}. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_comp, LinearMap.toMatrix_id`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html); [`Mathlib/Data/Matrix/Basic.lean::Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.mul_apply) — [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) is the matrix in chosen bases; `toMatrix_mulVec_repr` is coordinate matrix-vector multiplication, [`Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.mul_apply#doc) is the entry formula, and `toMatrix_comp`/`toMatrix_id` give composition and identity matrices.
:::

### Convention/notation — n-dimensional vector space {#fc08-cb-u031}

::: {.unit-meta}
`FC08-CB-U031` · Appendix B, § Linear Maps; source L18848 · [in Mathlib]{.route-mathlib}
:::

The composition of two linear maps is represented by the product of their matrices. Provided we use the same basis for both the domain and the codomain, the identity map on an n-dimensional vector space is represented by the n - n identity matrix, which we denote by $I _ { n }$ ; it is the matrix with ones on the main diagona (where the row number equals the column number) and zeros elsewhere.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_comp, LinearMap.toMatrix_id`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html); [`Mathlib/Data/Matrix/Basic.lean::Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.mul_apply) — [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) is the matrix in chosen bases; `toMatrix_mulVec_repr` is coordinate matrix-vector multiplication, [`Matrix.mul_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.mul_apply#doc) is the entry formula, and `toMatrix_comp`/`toMatrix_id` give composition and identity matrices.
:::

### Definition/convention — bilinear {#fc08-cb-u032}

::: {.unit-meta}
`FC08-CB-U032` · Appendix B, § Linear Maps; source L18850 · [in Mathlib]{.route-mathlib}
:::

A map $B \colon V \times W \to \mathbb{R}$ is bilinear if it is linear in each variable separately: $$ B(a_{1}v_{1} + a_{2}v_{2}, w) = a_{1}B(v_{1},w) + a_{2}B(v_{2},w), \qquad B(v, a_{1}w_{1} + a_{2}w_{2}) = a_{1}B(v,w_{1}) + a_{2}B(v,w_{2}). $$ An algebra over $\mathbb{R}$ is a real vector space $V$ with a bilinear product $V \times V \to V$; it is commutative or associative when that product is.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/BilinearMap.lean::LinearMap.BilinMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/BilinearMap.html#LinearMap.BilinMap); [`Mathlib/LinearAlgebra/Matrix/ToLin.lean::LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html#LinearMap.toMatrix) — [`LinearMap.BilinMap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.BilinMap#doc) is a map linear in each argument; matrices are finite function spaces and inherit the componentwise real-vector-space structure.
:::

### Definition/convention — commutative {#fc08-cb-u033}

::: {.unit-meta}
`FC08-CB-U033` · Appendix B, § Linear Maps; source L18856 · [in Mathlib]{.route-mathlib}
:::

An algebra (over R) is a real vector space V endowed with a bilinear product map $V \times V \to V$ . The algebra is said to be commutative or associative if the bilinear product has that property.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Algebra/Basic.lean::Algebra`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html) — Mathlib’s `Algebra ℝ A` packages a real module with compatible multiplication; commutativity/associativity are the corresponding multiplication typeclasses, matching Lee’s algebra terminology.
:::

### Definition/convention — invertible {#fc08-cb-u034}

::: {.unit-meta}
`FC08-CB-U034` · Appendix B, § Linear Maps; source L18860 · [in Mathlib]{.route-mathlib}
:::

Show that they are noncommutative unless $n = 1$ Suppose A is an $n \times n$ matrix. If there is a matrix B such that A $B = B A = I _ { n } $ ， then A is said to be invertible or nonsingular; it is singular otherwise.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.isUnit_iff_isUnit_det`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.isUnit_iff_isUnit_det) — For a square matrix over `ℝ`, being a unit in the matrix ring is exactly existence of a two-sided inverse; `isUnit_iff_isUnit_det` characterizes this by nonzero determinant.
:::

### Definition/convention — transition matrix between the two bases {#fc08-cb-u035}

::: {.unit-meta}
`FC08-CB-U035` · Appendix B, § Change of Basis; source L18874 · [in Mathlib]{.route-mathlib}
:::

Suppose $(E_{i})$ and $(\widetilde{E}_{j})$ are two bases for a finite-dimensional real vector space $V$. Each can be written uniquely in terms of the other, so there is an invertible matrix $B$, the transition matrix between the bases, with $$ E_{i} = \sum_{j=1}^{n} B^{j}_{i}\widetilde{E}_{j}, \qquad \widetilde{E}_{j} = \sum_{i=1}^{n} (B^{-1})^{i}_{j}E_{i}. \tag{B.1} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Basis.lean::Basis.toMatrix, Basis.toMatrix_mul_toMatrix_flip, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Basis.html) — [`Basis.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.toMatrix#doc) is the transition matrix. Mathlib proves opposite transition matrices are inverses and gives the two-sided change-of-basis multiplication formula, which specializes to Lee’s `C A B⁻¹` and conjugation formulas.
:::

### Convention/notation — source terminology/construction {#fc08-cb-u036}

::: {.unit-meta}
`FC08-CB-U036` · Appendix B, § Change of Basis; source L18880 · [in Mathlib]{.route-mathlib}
:::

E _ {i} = \sum_ {j = 1} ^ {n} B _ {i} ^ {j} \widetilde {E} _ {j}, \quad \widetilde {E} _ {j} = \sum_ {i = 1} ^ {n} \left(B ^ {- 1}\right) _ {j} ^ {i} E _ {i}.\tag{B.1} $$ Now suppose V and W are finite-dimensional vector spaces and $T \colon V \to W$ is a linear map. With respect to bases $( E _ { i } )$ for the domain V and $( F _ { j } )$ for the codomain $W$ , the map $T$ is represented by some matrix $A = \left( A _ { j } ^ { i } \right)$ . If $\left( \widetilde { E } _ { i } \right)$ and $\left( \widetilde { F } _ { j } \right)$ are any other choices of bases for V and $W$ , respectively, let B and C denote the transition matrices satisfying (B.1) and $$ F _ {i} = \sum_ {j = 1} ^ {m} C _ {i} ^ {j} \widetilde {F} _ {j}, \quad \widetilde {F} _ {j} = \sum_ {i = 1} ^ {m} \left(C ^ {- 1}\right) _ {j} ^ {i} F _ {i}. $$ Then a straightforward computation shows that the matrix $\widetilde { A }$ representing $T$ with respect to the new bases is related to A by $$ \widetilde {A} _ {j} ^ {i} = \sum_ {k, l} C _ {l} ^ {i} A _ {k} ^ {l} (B ^ {- 1}) _ {j} ^ {k}, $$ or, in matrix notation, $$ \widetilde {A} = C A B ^ {- 1}. $$ In particular, if $T$ is a map from V to itself, we usually use the same basis for the domain and the codomain. In this case, if A denotes the matrix of $T$ with respect to $( E _ { i } )$ , and $\tilde { A }$ is its matrix with respect to $\left( \widetilde { E } _ { i } \right)$ , we have $$ \widetilde {A}

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Basis.lean::Basis.toMatrix, Basis.toMatrix_mul_toMatrix_flip, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Basis.html) — [`Basis.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.toMatrix#doc) is the transition matrix. Mathlib proves opposite transition matrices are inverses and gives the two-sided change-of-basis multiplication formula, which specializes to Lee’s `C A B⁻¹` and conjugation formulas.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u037}

::: {.unit-meta}
`FC08-CB-U037` · Appendix B, § Change of Basis; source L18904 · [in Mathlib]{.route-mathlib}
:::

If V and W are real vector spaces, the set L ( V ; W ) of linear maps from V to W is a real vector space under the operations $$ (S+T)v = Sv + Tv, \qquad (cT)v = c(Tv). $$ If $\dim V = n$ and $\dim W = m$, a choice of bases identifies $\operatorname{L}(V;W)$ with the $m \times n$ matrices.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html) — `V →ₗ[ℝ] W` carries the pointwise module structure, exactly Lee’s vector space `L(V,W)` of linear maps.
:::

### Definition/convention — rank of T {#fc08-cb-u038}

::: {.unit-meta}
`FC08-CB-U038` · Appendix B, § Change of Basis; source L18912 · [in Mathlib]{.route-mathlib}
:::

If $T \colon V \to W$ is a linear map between finite-dimensional spaces, the dimension of $\operatorname{Im} T$ is the rank of $T$ and the dimension of $\operatorname{Ker} T$ is its nullity. Up to choices of bases, a linear map is determined by its rank together with the dimensions of its domain and codomain.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Dimension/RankNullity.lean::LinearMap.finrank_range_add_finrank_ker`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/RankNullity.html#LinearMap.finrank_range_add_finrank_ker) — Mathlib defines rank/nullity as finranks of `range`/`ker`; [`LinearMap.finrank_range_add_finrank_ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.finrank_range_add_finrank_ker#doc) is exactly the finite-dimensional rank-nullity law.
:::

### Theorem B.20 {#fc08-cb-u039}

::: {.unit-meta}
`FC08-CB-U039` · Appendix B, § Change of Basis; source L18914 · [not formalized]{.route-unmatched}
:::

(Canonical Form for a Linear Map). Suppose $V$ and $W$ are finite-dimensional vector spaces and $T \colon V \to W$ is a linear map of rank $r$. Then there are bases for $V$ and $W$ with respect to which $T$ has the block matrix representation $$ \begin{pmatrix} I_{r} & 0 \\ 0 & 0 \end{pmatrix}. $$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib has [`Matrix.exists_rank_normal_form`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.exists_rank_normal_form#doc) for square matrices, but Lee’s theorem is the rectangular linear-map canonical form with independently chosen domain/codomain bases. No checked declaration owning that full generality was found. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Corollary B.21 {#fc08-cb-u040}

::: {.unit-meta}
`FC08-CB-U040` · Appendix B, § Change of Basis; source L18942 · [in Mathlib]{.route-mathlib}
:::

Corollary B.21 (Rank-Nullity Law). Suppose $T \colon V \to W$ is a linear map between finite-dimensional vector spaces. Then $$ \dim V = \operatorname{rank} T + \text { nullity } T = \dim (\operatorname{Im} T) + \dim (\operatorname{Ker} T). $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Dimension/RankNullity.lean::LinearMap.finrank_range_add_finrank_ker`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/RankNullity.html#LinearMap.finrank_range_add_finrank_ker) — Mathlib defines rank/nullity as finranks of `range`/`ker`; [`LinearMap.finrank_range_add_finrank_ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.finrank_range_add_finrank_ker#doc) is exactly the finite-dimensional rank-nullity law.
:::

### Definition/convention — symmetric {#fc08-cb-u041}

::: {.unit-meta}
`FC08-CB-U041` · Appendix B, § Change of Basis; source L18966 · [in Mathlib]{.route-mathlib}
:::

Let $A$ be an $m \times n$ matrix. Its transpose is the $n \times m$ matrix $A^{T}$ obtained by interchanging rows and columns, $(A^{T})^{j}_{i} = A^{i}_{j}$. A square matrix $A$ is symmetric if $A = A^{T}$ and skew-symmetric if $A = -A^{T}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Symmetric.lean::Matrix.transpose, Matrix.IsSymm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Symmetric.html) — [`Matrix.transpose`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.transpose#doc) is row/column interchange; [`Matrix.IsSymm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.IsSymm#doc) is `Aᵀ=A`, while skew-symmetry is the directly expressible equation `Aᵀ=-A`.
:::

### Definition/convention — its column rank {#fc08-cb-u042}

::: {.unit-meta}
`FC08-CB-U042` · Appendix B, § Change of Basis; source L18970 · [in Mathlib]{.route-mathlib}
:::

The rank of an $m \times n$ matrix $A$ is the rank of the corresponding linear map $\mathbb{R}^{n} \to \mathbb{R}^{m}$. Since the columns of $A$, as vectors in $\mathbb{R}^{m}$, are the images of the standard basis vectors, the rank is also the dimension of the span of the columns, sometimes called the column rank; the row rank is the dimension of the span of the rows, viewed as vectors in $\mathbb{R}^{n}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Rank.lean::Matrix.rank, Matrix.rank_eq_finrank_span_cols, Matrix.rank_transpose`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Rank.html) — [`Matrix.rank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.rank#doc) is the finrank of the matrix linear map/column span, and `rank_transpose` proves row rank equals column rank.
:::

### Proposition B.24 {#fc08-cb-u043}

::: {.unit-meta}
`FC08-CB-U043` · Appendix B, § Change of Basis; source L18972 · [in Mathlib]{.route-mathlib}
:::

The row rank of a matrix is equal to its column rank.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Rank.lean::Matrix.rank, Matrix.rank_eq_finrank_span_cols, Matrix.rank_transpose`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Rank.html) — [`Matrix.rank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.rank#doc) is the finrank of the matrix linear map/column span, and `rank_transpose` proves row rank equals column rank.
:::

### Definition/convention — submatrix of A {#fc08-cb-u044}

::: {.unit-meta}
`FC08-CB-U044` · Appendix B, § Change of Basis; source L18988 · [in Mathlib]{.route-mathlib}
:::

Such a matrix is called a submatrix of A. Looking at submatrices gives a convenien criterion for checking the rank of a matrix. P

::: {.unit-lean}
**Formalized.** [`Mathlib/Data/Matrix/Basic.lean::Matrix.submatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.submatrix) — [`Matrix.submatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.submatrix#doc) is exactly restriction to selected row and column index maps, the canonical formalization of a submatrix.
:::

### Proposition B.25 {#fc08-cb-u045}

::: {.unit-meta}
`FC08-CB-U045` · Appendix B, § Change of Basis; source L18990 · [not formalized]{.route-unmatched}
:::

Proposition B.25. Suppose A is an m n matrix. Then rank $A \geq k$ if and only if some $k \times k$ submatrix of A is nonsingular.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib proves rank monotonicity under submatrices and determinant criteria for full rank, but targeted P/H searches did not find the exact iff “rank ≥ k iff some k×k submatrix is nonsingular.” Reconstructing the converse via row/column selections is substantive. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — permutation of X {#fc08-cb-u046}

::: {.unit-meta}
`FC08-CB-U046` · Appendix B, § The Determinant; source L18998 · [in Mathlib]{.route-mathlib}
:::

If X is a set, a permutation of X is a bijective map from X to itself. The set of all permutations of X is a group under composition. A transposition is a permutation that interchanges two elements and leaves all the others fixed.

::: {.unit-lean}
**Formalized.** [`Mathlib/Logic/Equiv/Defs.lean::Equiv, Equiv.Perm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html#Equiv.Perm); [`Mathlib/GroupTheory/Perm/Basic.lean::Equiv.swap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Basic.html#Equiv.swap) — `Equiv.Perm X` is the permutation group of `X`; [`Equiv.swap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Equiv.swap#doc) is a transposition, so the symmetric group and transpositions are represented directly.
:::

### Definition/convention — symmetric group {#fc08-cb-u047}

::: {.unit-meta}
`FC08-CB-U047` · Appendix B, § The Determinant; source L19000 · [in Mathlib]{.route-mathlib}
:::

We let $S _ { n }$ denote the group of permutations of the set $\{ 1 , \ldots , n \}$ , called the symmetric group on n elements. The properties of $S _ { n }$ that we need are summarized in the following proposition; proofs can be found in any good undergraduate algebra text such as [Hun97] or [Her75].

::: {.unit-lean}
**Formalized.** [`Mathlib/Logic/Equiv/Defs.lean::Equiv, Equiv.Perm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html#Equiv.Perm); [`Mathlib/GroupTheory/Perm/Basic.lean::Equiv.swap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Basic.html#Equiv.swap) — `Equiv.Perm X` is the permutation group of `X`; [`Equiv.swap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Equiv.swap#doc) is a transposition, so the symmetric group and transpositions are represented directly.
:::

### Proposition B.26 {#fc08-cb-u048}

::: {.unit-meta}
`FC08-CB-U048` · Appendix B, § The Determinant; source L19002 · [in Mathlib]{.route-mathlib}
:::

Proposition B.26 (Properties of the Symmetric Group). (a) Every element of $S _ { n }$ can be expressed as a composition of finitely many transpositions. (b) For each $\sigma \in S _ { n }$ , the parity (evenness or oddness) of the number of factors in any decomposition of  as a product of transpositions is independent of the choice of decomposition. We say that  is an even permutation if every such decomposition has an even number of factors, and an odd permutation otherwise. (c) For each $\sigma \in S _ { n }$ , define the sign of  to be the number $$ \operatorname{sgn} \sigma = \left\{ \begin{array}{l l} + 1 & \text { if } \sigma \text { is even }, \\ - 1 & \text { if } \sigma \text { is odd }. \end{array} \right. $$ $H n \geq 2$ , sgn $S _ { n } \{ \pm 1 \}$ is a surjective group homomorphism, where we consider $\{ \pm 1 \}$ as a group under multiplication. Exercise B.27. Prove (or look up) Proposition B.26. If $A = \left( A _ { j } ^ { i } \right)$ is an $n \times n$ (real or complex) matrix, the determinant of A is defined by the expression $$ \det A = \sum_ {\sigma \in S _ {n}} (\operatorname{sgn} \sigma) A _ {1} ^ {\sigma (1)} \dots A _ {n} ^ {\sigma (n)}.\tag{B.3} $$ For simplicity, we assume throughout this section ogy on S (sometimes called the relative topology) by declaring a subset $U \subseteq S$ to be open in S if and only if there exists an open subset V X such that $U = V \cap S$ A subset of S that is open or closed in the subspace topology is sometimes said to be relatively open or relatively closed in S , to make it clear that we do not mean open or closed as a subset of X.

::: {.unit-lean}
**Formalized.** [`Mathlib/GroupTheory/Perm/Sign.lean::Equiv.Perm.sign, Equiv.Perm.sign_swap, mclosure_swap_castSucc_succ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Sign.html) — Mathlib’s permutation sign is a multiplicative homomorphism to `ℤˣ`, sends swaps to `-1`, and the adjacent swaps generate the finite symmetric group. These statements exactly encode existence of transposition decompositions and parity-independence.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u049}

::: {.unit-meta}
`FC08-CB-U049` · Appendix B, § The Determinant; source L19018 · [in Mathlib]{.route-mathlib}
:::

If A = ( A _j ^i ) is an n × n (real or complex) matrix, the determinant of A is defined by the expression $$ \det A = \sum_{\sigma \in S_{n}} (\operatorname{sgn}\sigma)\, A^{\sigma(1)}_{1} \cdots A^{\sigma(n)}_{n}. \tag{B.3} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det, Matrix.det_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html) — [`Matrix.det`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.det#doc) is the signed permutation sum. A matrix is a family of column vectors, so this is exactly Lee’s determinant both as a matrix function and as a function of its columns.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u050}

::: {.unit-meta}
`FC08-CB-U050` · Appendix B, § The Determinant; source L19026 · [in Mathlib]{.route-mathlib}
:::

Although the determinant is defined as a function of matrices, it is also useful to think of it as a function of n vectors in $\mathbb { R } ^ { n }$ : if $A _ { 1 } , \ldots , A _ { n } \in \mathbb { R } ^ { n }$ , we interpret $\operatorname* { d e t } ( A _ { 1 } , \ldots , A _ { n } )$ to mean the determinant of the matrix whose columns are $( A _ { 1 } , \ldots , A _ { n } )$ : $$ \det (A _ {1}, \ldots , A _ {n}) = \det \left( \begin{array}{c c c} A _ {1} ^ {1} & \ldots & A _ {n} ^ {1} \\ \vdots & \ddots & \vdots \\ A _ {1} ^ {n} & \ldots & A _ {n} ^ {n} \end{array} \right). $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det, Matrix.det_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html) — [`Matrix.det`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.det#doc) is the signed permutation sum. A matrix is a family of column vectors, so this is exactly Lee’s determinant both as a matrix function and as a function of its columns.
:::

### Proposition B.28 {#fc08-cb-u051}

::: {.unit-meta}
`FC08-CB-U051` · Appendix B, § The Determinant; source L19034 · [in Mathlib]{.route-mathlib}
:::

(a) If one column of A is multiplied by a scalar c, the determinant is multiplied by the same scalar: $$ \det (A _ {1}, \dots , c A _ {i}, \dots , A _ {n}) = c \det (A _ {1}, \dots , A _ {i}, \dots , A _ {n}). $$ (b) The determinant changes sign when two columns are interchanged: $$ \det (A _ {1}, \dots , A _ {q}, \dots , A _ {p}, \dots , A _ {n}) = - \det (A _ {1}, \dots , A _ {p}, \dots , A _ {q}, \dots , A _ {n}).\tag{B.4} $$ (c) The determinant is unchanged by adding a scalar multiple of one column to any other column: $$ \det (A _ {1}, \dots , A _ {i}, \dots , A _ {j} + c A _ {i}, \dots , A _ {n}) = \det (A _ {1}, \dots , A _ {i}, \dots , A _ {j} \dots , A _ {n}). $$ (d) For every scalar c, de $\operatorname { t } ( c A ) = c ^ { n }$ det A. (e) If any two columns of A are identical, then det $A = 0$ (f) If A has a column of zeros, then det $A = 0$ (g) det $A ^ { T } = \operatorname* { d e t } A .$ (h) det $I _ { n } = 1$ (i) If A is sing s S .

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_updateCol_smul, Matrix.det_permute, Matrix.det_updateCol_add_smul_self, Matrix.det_smul, Matrix.det_transpose, Matrix.det_one, Matrix.det_eq_zero_of_column_eq_zero, Matrix.det_zero_of_column_eq`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html) — Pinned Mathlib has the exact determinant laws for scaling/swapping/adding columns, scalar multiplication of a matrix, transpose, identity, repeated/zero columns, and singularity consequences; together they match every clause of Proposition B.28.
:::

### Definition/convention — elementary column operations {#fc08-cb-u052}

::: {.unit-meta}
`FC08-CB-U052` · Appendix B, § The Determinant; source L19088 · [not formalized]{.route-unmatched}
:::

Multiplying one column by a scalar, interchanging two columns and adding a multiple of one column to another are the elementary column operations, and parts (a)–(c) of the preceding proposition describe exactly how the determinant is affected by them. Defining elementary row operations analogously, $\det A^{T} = \det A$ implies the determinant behaves the same way under row operations.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has the actual row/column update and swap operations and their determinant laws, but no canonical object corresponding to Lee’s source-specific collective terminology “elementary row/column operations.”
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Theorem B.31 {#fc08-cb-u053}

::: {.unit-meta}
`FC08-CB-U053` · Appendix B, § The Determinant; source L19106 · [in Mathlib]{.route-mathlib}
:::

and B are $n \times n$ matrices, then $$ \det (A B) = (\det A) (\det B). $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_mul, Matrix.det_units_conj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html); [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.det_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_nonsing_inv); [`Mathlib/LinearAlgebra/Matrix/Nonsingular.lean::Matrix.nonsingular_iff_det_ne_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Nonsingular.html#Matrix.nonsingular_iff_det_ne_zero) — `det_mul` is multiplicativity; `det_nonsing_inv` gives the determinant of the inverse; `nonsingular_iff_det_ne_zero` is Lee’s singularity criterion over `ℝ`; determinant conjugation invariance follows directly and is also packaged for units.
:::

### Corollary B.32 {#fc08-cb-u054}

::: {.unit-meta}
`FC08-CB-U054` · Appendix B, § The Determinant; source L19114 · [in Mathlib]{.route-mathlib}
:::

If $A$ is a nonsingular $n \times n$ matrix, then $\det A \neq 0$ and $\det(A^{-1}) = (\det A)^{-1}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_mul, Matrix.det_units_conj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html); [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.det_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_nonsing_inv); [`Mathlib/LinearAlgebra/Matrix/Nonsingular.lean::Matrix.nonsingular_iff_det_ne_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Nonsingular.html#Matrix.nonsingular_iff_det_ne_zero) — `det_mul` is multiplicativity; `det_nonsing_inv` gives the determinant of the inverse; `nonsingular_iff_det_ne_zero` is Lee’s singularity criterion over `ℝ`; determinant conjugation invariance follows directly and is also packaged for units.
:::

### Corollary B.33 {#fc08-cb-u055}

::: {.unit-meta}
`FC08-CB-U055` · Appendix B, § The Determinant; source L19120 · [in Mathlib]{.route-mathlib}
:::

Corollary B.33. A square matrix is singular if and only if its determinant is zero.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_mul, Matrix.det_units_conj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html); [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.det_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_nonsing_inv); [`Mathlib/LinearAlgebra/Matrix/Nonsingular.lean::Matrix.nonsingular_iff_det_ne_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Nonsingular.html#Matrix.nonsingular_iff_det_ne_zero) — `det_mul` is multiplicativity; `det_nonsing_inv` gives the determinant of the inverse; `nonsingular_iff_det_ne_zero` is Lee’s singularity criterion over `ℝ`; determinant conjugation invariance follows directly and is also packaged for units.
:::

### Corollary B.34 {#fc08-cb-u056}

::: {.unit-meta}
`FC08-CB-U056` · Appendix B, § The Determinant; source L19124 · [in Mathlib]{.route-mathlib}
:::

Suppose $A$ and $B$ are $n \times n$ matrices with $B$ nonsingular. Then $\det(BAB^{-1}) = \det A$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_mul, Matrix.det_units_conj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html); [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.det_nonsing_inv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.det_nonsing_inv); [`Mathlib/LinearAlgebra/Matrix/Nonsingular.lean::Matrix.nonsingular_iff_det_ne_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Nonsingular.html#Matrix.nonsingular_iff_det_ne_zero) — `det_mul` is multiplicativity; `det_nonsing_inv` gives the determinant of the inverse; `nonsingular_iff_det_ne_zero` is Lee’s singularity criterion over `ℝ`; determinant conjugation invariance follows directly and is also packaged for units.
:::

### Definition/convention — determinant of T to be the determinant of any matrix represen {#fc08-cb-u057}

::: {.unit-meta}
`FC08-CB-U057` · Appendix B, § The Determinant; source L19134 · after [`FC08-CB-U056`](#fc08-cb-u056) · [in Mathlib]{.route-mathlib}
:::

Two matrices $A$ and $\widetilde{A}$ representing $T$ with respect to different bases are related by $\widetilde{A} = BAB^{-1}$ for a nonsingular $B$, so by Corollary B.34 $\det\widetilde{A} = \det A$. Hence for a linear map $T \colon V \to V$ of a finite-dimensional vector space to itself, the determinant of $T$ is defined to be the determinant of any matrix representation of $T$, using the same basis for domain and codomain.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Determinant.lean::LinearMap.det`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Determinant.html#LinearMap.det) — [`LinearMap.det`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.det#doc) is the basis-independent determinant of a finite-dimensional endomorphism, with its matrix representation theorem, exactly Lee’s definition.
:::

### Proposition B.35 {#fc08-cb-u058}

::: {.unit-meta}
`FC08-CB-U058` · Appendix B, § The Determinant; source L19138 · [in Mathlib]{.route-mathlib}
:::

Proposition B.35 (Expansion by Minors). Let A be an $n \times n$ matrix, and for each $i , j$ let $M _ { i } ^ { j }$ denote the $( n - 1 ) \times ( n - 1 )$ submatrix obtained by deleting the ith column and j th row of A. For any fixed i between 1 and n inclusive, $$ \det A = \sum_ {j = 1} ^ {n} (- 1) ^ {i + j} A _ {i} ^ {j} \det M _ {i} ^ {j}.\tag{B.5} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean::Matrix.det_succ_row, Matrix.det_succ_column`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html) — `det_succ_row`/`det_succ_column` give Laplace expansion by signed determinants of the deleted-row/deleted-column submatrices, exactly expansion by minors.
:::

### Definition/convention — minor of A {#fc08-cb-u059}

::: {.unit-meta}
`FC08-CB-U059` · Appendix B, § The Determinant; source L19172 · [not formalized]{.route-unmatched}
:::

Each determinant det $M _ { i } ^ { j }$ is called a minor of A, and (B.5) is called the expansion of det A by minors along the i th column. Since det A det $A ^ { T }$ , there is an analogous expansion along any row. The factor $( - 1 ) ^ { i + j }$ det $M _ { i } ^ { j }$ multiplying $A _ { i } ^ { j }$ in (B.5) is called the cofactor of $A _ { i } ^ { j }$ , and is denoted by co $\mathbf { \Sigma } _ { i } ^ { : j }$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib represents signed minors through submatrices and adjugate entries, but does not expose Lee’s exact `M_i^j` / cofactor terminology as a canonical standalone construction for this row. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Proposition B.36 {#fc08-cb-u060}

::: {.unit-meta}
`FC08-CB-U060` · Appendix B, § The Determinant; source L19174 · [in Mathlib]{.route-mathlib}
:::

Proposition B.36 (Cramer’s Rule). If A is a nonsingular $n \times n$ matrix, then $A ^ { - 1 }$ is equal to $1 / ( \operatorname* { d e t } A )$ times the transposed cofactor matrix of A. Thus, the entry in the ith row and j th column of $A ^ { - 1 }$ is $$ \left(A ^ {- 1}\right) _ {j} ^ {i} = \frac {1}{\det A} \mathrm{cof} _ {i} ^ {j} = \frac {1}{\det A} (- 1) ^ {i + j} \det M _ {i} ^ {j}.\tag{B.8} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Adjugate.lean::Matrix.adjugate_fin_succ_eq_det_submatrix`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Adjugate.html#Matrix.adjugate_fin_succ_eq_det_submatrix); [`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean::Matrix.nonsing_inv_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html#Matrix.nonsing_inv_apply) — Mathlib identifies adjugate entries with signed minors and defines the inverse of an invertible matrix as determinant inverse times the adjugate, which is exactly Lee’s Cramer-rule formula for `A⁻¹`.
:::

### Definition/convention — upper triangular {#fc08-cb-u061}

::: {.unit-meta}
`FC08-CB-U061` · Appendix B, § The Determinant; source L19188 · [in Mathlib]{.route-mathlib}
:::

A square matrix $A = \left( A _ { j } ^ { i } \right)$ is said to be upper triangular if $A _ { j } ^ { i } = 0$ for $i > j$ (i.e., the only nonzero entries are on and above the main diagonal). Determinants of upper triangular matrices are particularly easy to c

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Block.lean::Matrix.IsUpperTriangular, Matrix.det_of_isUpperTriangular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html) — [`Matrix.IsUpperTriangular`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.IsUpperTriangular#doc) is the zero-below-diagonal predicate and `det_of_isUpperTriangular` gives the product of diagonal entries exactly.
:::

### Proposition B.37 {#fc08-cb-u062}

::: {.unit-meta}
`FC08-CB-U062` · Appendix B, § The Determinant; source L19190 · [in Mathlib]{.route-mathlib}
:::

Proposition B.37. If A is an upper triangular $n \times n$ matrix, then the determinant of A is the product of its diagonal entries: $$ \det A = A _ {1} ^ {1} \dots A _ {n} ^ {n}. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Block.lean::Matrix.IsUpperTriangular, Matrix.det_of_isUpperTriangular`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html) — [`Matrix.IsUpperTriangular`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.IsUpperTriangular#doc) is the zero-below-diagonal predicate and `det_of_isUpperTriangular` gives the product of diagonal entries exactly.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u063}

::: {.unit-meta}
`FC08-CB-U063` · Appendix B, § The Determinant; source L19198 · [in Mathlib]{.route-mathlib}
:::

Suppose X is an ( m + k ) × ( m + k ) matrix. We say that X is block upper triangular if X has the form $$ X = \begin{pmatrix} A & B \\ 0 & C \end{pmatrix} \tag{B.10} $$ for matrices $A$, $B$, $C$ of sizes $m \times m$, $m \times k$ and $k \times k$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Block.lean::Matrix.BlockTriangular, Matrix.upper_two_blockTriangular, Matrix.det_fromBlocks_zero₂₁`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html) — Mathlib’s two-block triangular construction is the matrix `[[A,B],[0,C]]`; `det_fromBlocks_zero₂₁` proves its determinant is `det A * det C`.
:::

### Proposition B.38 {#fc08-cb-u064}

::: {.unit-meta}
`FC08-CB-U064` · Appendix B, § The Determinant; source L19206 · [in Mathlib]{.route-mathlib}
:::

If X is the block upper triangular matrix given by (B.10), then det X = ( operatorname* d e t A ) ( operatorname* d e t C )

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Matrix/Block.lean::Matrix.BlockTriangular, Matrix.upper_two_blockTriangular, Matrix.det_fromBlocks_zero₂₁`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Block.html) — Mathlib’s two-block triangular construction is the matrix `[[A,B],[0,C]]`; `det_fromBlocks_zero₂₁` proves its determinant is `det A * det C`.
:::

### Definition/convention — inner product {#fc08-cb-u065}

::: {.unit-meta}
`FC08-CB-U065` · Appendix B, § Inner Products and Norms; source L19232 · [in Mathlib]{.route-mathlib}
:::

If V is a real vector space, an inner product on V is a map $V \times V \to \mathbb { R }$ , usually written $( v , w ) \mapsto \langle v , w \rangle$ , that satisfies the following conditions: (i) SYMMETRY: $$ \langle v, w \rangle = \langle w, v \rangle ; $$ (ii) BILINEARITY: $$ \begin{array}{r} \langle a v + a ^ {\prime} v ^ {\prime}, w \rangle = a \langle v, w \rangle + a ^ {\prime} \langle v ^ {\prime}, w \rangle , \\ \langle v, b w + b ^ {\prime} w ^ {\prime} \rangle = b \langle v, w \rangle + b ^ {\prime} \langle v, w ^ {\prime} \rangle ; \end{array} $$ (iii) POSITIVE DEFINITENESS: $$ \langle v, v \rangle \geq 0, \quad \text { with equality if and only if } v = 0. $$ A vector d only if for every $A \subseteq X , F ( { \overline { { A } } } ) \supseteq { \overline { { F ( A ) } } }$ (b) F is open if and only if for every $B \subseteq Y , F ^ { - 1 } ( \operatorname { I n t } B ) \supseteq \operatorname { I n t } F ^ { - 1 } ( B )$ The most important classes of continuous maps in topology are the homeomorphisms, quotient maps, and topological embeddings.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Defs.lean::InnerProductSpace.Core, InnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Defs.html#InnerProductSpace.Core); [`Mathlib/Analysis/InnerProductSpace/PiL2.lean::Pi.instInnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#Pi.instInnerProductSpace) — `InnerProductSpace.Core ℝ V` packages a symmetric bilinear positive-definite real inner product, and Mathlib’s finite coordinate spaces have the standard dot-product instance.
:::

### Definition/convention — inner product space {#fc08-cb-u066}

::: {.unit-meta}
`FC08-CB-U066` · Appendix B, § Inner Products and Norms; source L19252 · [in Mathlib]{.route-mathlib}
:::

$$ A vector space endowed with a specific inner product is called an inner product space. The standard example is, of course, $\mathbb { R } ^ { n }$ with its Euclidean dot product: $$ \langle x, y \rangle = x \cdot y = \sum_ {i = 1} ^ {n} x ^ {i} y ^ {i}.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Defs.lean::InnerProductSpace.Core, InnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Defs.html#InnerProductSpace.Core); [`Mathlib/Analysis/InnerProductSpace/PiL2.lean::Pi.instInnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#Pi.instInnerProductSpace) — `InnerProductSpace.Core ℝ V` packages a symmetric bilinear positive-definite real inner product, and Mathlib’s finite coordinate spaces have the standard dot-product instance.
:::

### Definition/convention — unit vector {#fc08-cb-u067}

::: {.unit-meta}
`FC08-CB-U067` · Appendix B, § Inner Products and Norms; source L19258 · [not formalized]{.route-unmatched}
:::

Let $V$ be an inner product space. For $v \in V$, the length of $v$ is $|v| = \sqrt{\langle v,v \rangle}$, and a unit vector is a vector of length $1$. For nonzero $v, w \in V$, the angle between $v$ and $w$ is the unique $\theta \in [0,\pi]$ satisfying $$ \cos\theta = \frac{\langle v,w \rangle}{|v|\,|w|}. $$ Vectors are orthogonal if $\langle v,w \rangle = 0$, which means one of them is zero or the angle between them is $\pi/2$.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has norm and inner-product APIs, but targeted P/H search found no single canonical “angle between vectors” definition with Lee’s exact arccos characterization bundled together with the unit-vector terminology. The norm component alone is a proper subset. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — orthogonal {#fc08-cb-u068}

::: {.unit-meta}
`FC08-CB-U068` · Appendix B, § Inner Products and Norms; source L19264 · [in Mathlib]{.route-mathlib}
:::

Two vectors v; $w \in V$ are said to be orthogonal if $\langle v , w \rangle = 0 $ ; this means that either one of the vectors is zero, or the angle between them is $\pi / 2$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean::Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthogonal.html#Submodule.orthogonal); [`Mathlib/Analysis/InnerProductSpace/PiL2.lean::Orthonormal, OrthonormalBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html) — Orthogonality is zero inner product and `Orthonormal`/`OrthonormalBasis` impose pairwise orthogonality with unit norm, exactly Lee’s definitions.
:::

### Definition/convention — orthonormal {#fc08-cb-u069}

::: {.unit-meta}
`FC08-CB-U069` · Appendix B, § Inner Products and Norms; source L19278 · [in Mathlib]{.route-mathlib}
:::

Suppose $V$ is a finite-dimensional inner product space. A basis $(E_{1},\dots,E_{n})$ for $V$ is orthonormal if each $E_{i}$ is a unit vector and $E_{i}$ is orthogonal to $E_{j}$ whenever $i \neq j$.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean::Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthogonal.html#Submodule.orthogonal); [`Mathlib/Analysis/InnerProductSpace/PiL2.lean::Orthonormal, OrthonormalBasis`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html) — Orthogonality is zero inner product and `Orthonormal`/`OrthonormalBasis` impose pairwise orthogonality with unit norm, exactly Lee’s definitions.
:::

### Proposition B.40 {#fc08-cb-u070}

::: {.unit-meta}
`FC08-CB-U070` · Appendix B, § Inner Products and Norms; source L19280 · [in Mathlib]{.route-mathlib}
:::

Proposition B.40 (The Gram–Schmidt Algorithm). Let V be an inner product space of dimension $n \geq 1$ . Then V has an orthonormal basis. In fact, $i f ( E _ { 1 } , \dots , E _ { n } )$ is an arbitrary basis for V , there is an orthonormal basis $\big ( \breve { E } _ { 1 } , \dots , \breve { E } _ { n } \big )$ with the property that $$ \operatorname{span} \left(\widetilde {E} _ {1}, \dots , \widetilde {E} _ {k}\right) = \operatorname{span} \left(E _ {1}, \dots , E _ {k}\right) \quad f o r k = 1, \dots , n.\tag{B.12} $$ Proof. The proof is by induction on $n = \dim V$ . If $n = 1$ , there is only one basis element $E _ { 1 }$ , and then $\widetilde { E } _ { 1 } = E _ { 1 } / | E _ { 1 } |$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean::gramSchmidtBasis, span_gramSchmidt_Iic, gramSchmidtNormed_orthonormal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.html) — Mathlib’s Gram–Schmidt construction turns a basis into an orthogonal/orthonormal one and `span_gramSchmidt_Iic` proves equality of every initial-span prefix, exactly Proposition B.40.
:::

### Definition/convention — linear isometry {#fc08-cb-u071}

::: {.unit-meta}
`FC08-CB-U071` · Appendix B, § Inner Products and Norms; source L19298 · [in Mathlib]{.route-mathlib}
:::

An isomorphism $T \colon V \to W$ between inner product spaces is a linear isometry if it carries the inner product of $V$ to that of $W$: $$ \langle Tv, Tw \rangle = \langle v, w \rangle \quad \text{for all } v, w \in V. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Normed/Operator/LinearIsometry.lean::LinearIsometry, LinearIsometryEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/LinearIsometry.html) — A `LinearIsometry` preserves norm, and over real inner-product spaces this is equivalent to preserving the inner product; the bijective version `LinearIsometryEquiv` is Lee’s linear isometry.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u072}

::: {.unit-meta}
`FC08-CB-U072` · Appendix B, § Inner Products and Norms; source L19312 · [in Mathlib]{.route-mathlib}
:::

If V is a finite-dimensional inner product space and S ⊆ V is a subspace, the orthogonal complement of S in V is the set $$ S^{\perp} = \{v \in V : \langle v,w \rangle = 0 \text{ for all } w \in S\}. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean::Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthogonal.html#Submodule.orthogonal); [`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean::Submodule.orthogonalProjectionOnto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html#Submodule.orthogonalProjectionOnto) — [`Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.orthogonal#doc) is the orthogonal complement and `orthogonalProjectionOnto` is the canonical projection onto a subspace with orthogonal kernel; finite-dimensional real inner-product spaces have the required projection instance.
:::

### Construction/definition — orthogonal projection of V onto S {#fc08-cb-u073}

::: {.unit-meta}
`FC08-CB-U073` · Appendix B, § Inner Products and Norms; source L19320 · [in Mathlib]{.route-mathlib}
:::

Thanks to the result of the preceding exercise, for any subspace S of an inner product space V , there is a natural projection $\pi \colon V \to S$ with kernel $S ^ { \perp }$ . This is called the orthogonal projection of V onto S . ##

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean::Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Orthogonal.html#Submodule.orthogonal); [`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean::Submodule.orthogonalProjectionOnto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html#Submodule.orthogonalProjectionOnto) — [`Submodule.orthogonal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.orthogonal#doc) is the orthogonal complement and `orthogonalProjectionOnto` is the canonical projection onto a subspace with orthogonal kernel; finite-dimensional real inner-product spaces have the required projection instance.
:::

### Definition/convention — norm {#fc08-cb-u074}

::: {.unit-meta}
`FC08-CB-U074` · Appendix B, § Norms; source L19324 · [in Mathlib]{.route-mathlib}
:::

Norms If V is a real vector space, a norm on V is a function from V to R, written $v \mapsto | v |$ satisfying the following properties. (i)

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Normed/Group/Basic.lean::Norm, NormedAddCommGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/Basic.html); [`Mathlib/Analysis/Normed/Module/Basic.lean::NormedSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Basic.html) — `Norm` together with the normed additive-group axioms is Mathlib’s norm; `NormedSpace ℝ V` combines it with the vector-space scalar action and its metric topology.
:::

### Definition/convention — normed linear space {#fc08-cb-u075}

::: {.unit-meta}
`FC08-CB-U075` · Appendix B, § Norms; source L19332 · [in Mathlib]{.route-mathlib}
:::

A vector space together with a specific choice of norm is called a normed linear space. Exercise B.39 shows that the length function associated with any inner product is a norm; thus, in particular, every finite-dimensional vector space possesses many norms. Given a norm on V , the distance function d ( v , w ) = ∣ v - w ∣ turns V into a metric space, yielding a topology on V called the norm topology.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Normed/Group/Basic.lean::Norm, NormedAddCommGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/Basic.html); [`Mathlib/Analysis/Normed/Module/Basic.lean::NormedSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/Basic.html) — `Norm` together with the normed additive-group axioms is Mathlib’s norm; `NormedSpace ℝ V` combines it with the vector-space scalar action and its metric topology.
:::

### Example B.46 {#fc08-cb-u076}

::: {.unit-meta}
`FC08-CB-U076` · Appendix B, § Norms; source L19334 · [in Mathlib]{.route-mathlib}
:::

Example B.46 (Euclidean Spaces). Endowed with the Euclidean norm defined by $$ | x | = \sqrt {x \cdot x},\tag{B.14} $$ R is a normed linear space, whose norm topology is exactly the Euclidean topology described in Appendix A.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/InnerProductSpace/PiL2.lean::EuclideanSpace, Pi.instInnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html#Pi.instInnerProductSpace) — Mathlib’s finite `EuclideanSpace ℝ (Fin n)` has the Euclidean inner product and induced square-root-sum-of-squares norm, whose topology is the standard finite-product Euclidean topology.
:::

### Example B.47 {#fc08-cb-u077}

::: {.unit-meta}
`FC08-CB-U077` · Appendix B, § Norms; source L19342 · [in Mathlib]{.route-mathlib}
:::

(The Frobenius Norm on Matrices). The vector space $M(m \times n,\mathbb{R})$ of real $m \times n$ matrices has a natural Euclidean inner product, obtained by identifying a matrix with a point of $\mathbb{R}^{mn}$: $A \cdot B = \sum_{i,j} A^{i}_{j}B^{i}_{j}$. The resulting norm is the Frobenius norm $$ |A| = \sqrt{\sum_{i,j} (A^{i}_{j})^{2}}, \tag{B.15} $$ which is the norm always used on matrices here.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Matrix/Normed.lean::Matrix.frobeniusNorm, Matrix.frobeniusNormedAddCommGroup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Normed.html) — Mathlib defines the Frobenius norm of a finite matrix by the square root of the sum of squared entry norms, exactly Lee’s matrix norm.
:::

### Definition/convention — equivalent {#fc08-cb-u078}

::: {.unit-meta}
`FC08-CB-U078` · Appendix B, § Norms; source L19364 · [not formalized]{.route-unmatched}
:::

Two norms $|\cdot|_{1}$ and $|\cdot|_{2}$ on a vector space $V$ are equivalent if there are positive constants $c, C$ with $$ c\,|v|_{1} \leq |v|_{2} \leq C\,|v|_{1} \quad \text{for all } v \in V. $$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib’s finite-dimensional theory proves continuity of all linear maps and thereby equivalence of norms, but its own source notes that norm equivalence is not packaged explicitly as Lee’s two-constant predicate. No canonical owner for the definition row was found. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Definition/convention — bounded {#fc08-cb-u079}

::: {.unit-meta}
`FC08-CB-U079` · Appendix B, § Norms; source L19376 · [in Mathlib]{.route-mathlib}
:::

If V and W are normed linear spaces, a linear map $T \colon V \to W$ is said to be bounded if there exists a positive constant C such that $$ | T v | \leq C | v | \quad \text { for all } v \in V. $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean::IsBoundedLinearMap, isBoundedLinearMap_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.html) — `IsBoundedLinearMap` is explicitly the unbundled predicate that a linear map has a constant `C>0` with `‖Tv‖ ≤ C‖v‖`, exactly Lee’s bounded linear map.
:::

### Construction/definition — source terminology/construction {#fc08-cb-u080}

::: {.unit-meta}
`FC08-CB-U080` · Appendix B, § Direct Products and Direct Sums; source L19388 · [in Mathlib]{.route-mathlib}
:::

If $V_{1},\dots,V_{k}$ are real vector spaces, their direct product is the vector space whose underlying set is the Cartesian product $V_{1} \times \cdots \times V_{k}$, with addition and scalar multiplication defined componentwise, $$ (v_{1},\dots,v_{k}) + (v_{1}',\dots,v_{k}') = (v_{1}+v_{1}',\dots,v_{k}+v_{k}'), \qquad c(v_{1},\dots,v_{k}) = (cv_{1},\dots,cv_{k}). $$ The basic example is Euclidean space $\mathbb{R}^{n} = \mathbb{R} \times \cdots \times \mathbb{R}$.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Pi.lean::Pi.instModule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Pi.html#Pi.instModule); [`Mathlib/Algebra/Module/Defs.lean::Module`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html); [`Mathlib/Algebra/Module/Submodule/Defs.lean::Submodule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Defs.html) — Products of modules carry pointwise operations; `Module` and `Submodule` are exactly Lee’s module/submodule notions. For a finite family, product and direct-sum representations are linearly equivalent.
:::

### Definition/convention — submodule of V {#fc08-cb-u081}

::: {.unit-meta}
`FC08-CB-U081` · Appendix B, § Direct Products and Direct Sums; source L19400 · [in Mathlib]{.route-mathlib}
:::

For infinitely many vector spaces the setting is modules over a commutative ring $R$. Linear maps are defined as for vector spaces: $F \colon V \to W$ is $R$-linear if $F(av+bw) = aF(v) + bF(w)$ for all $a, b \in R$ and $v, w \in V$. A subset $S \subseteq V$ is a submodule if it is closed under addition and scalar multiplication, hence itself an $R$-module. In the applications $R$ is either $\mathbb{R}$, where the modules are real vector spaces and the maps the usual linear ones, or $\mathbb{Z}$, where the modules are abelian groups and the maps group homomorphisms.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Pi.lean::Pi.instModule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Pi.html#Pi.instModule); [`Mathlib/Algebra/Module/Defs.lean::Module`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html); [`Mathlib/Algebra/Module/Submodule/Defs.lean::Submodule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Defs.html) — Products of modules carry pointwise operations; `Module` and `Submodule` are exactly Lee’s module/submodule notions. For a finite family, product and direct-sum representations are linearly equivalent.
:::

### Construction/definition — nonempty indexed family of nonempty sets {#fc08-cb-u082}

::: {.unit-meta}
`FC08-CB-U082` · Appendix B, § Direct Products and Direct Sums; source L19402 · [not formalized]{.route-unmatched}
:::

If $( V _ { \alpha } ) _ { \alpha \in A }$ is an arbitrary indexed family of sets, their Cartesian product, denoted by $\Pi _ { \alpha \in A } V _ { \alpha }$ , is defined as the set of functions v $A \textstyle \bigcup _ { \alpha \in A } V _ { \alpha }$ with the property that $v ( \alpha ) \in V _ { \alpha }$ for each ˛. Thanks to the axiom of choice, the Cartesian product of a nonempty indexed family of nonempty sets is nonempty. If v is an element of the Cartesian product, we usually denote the value of v at $\alpha \in A$ by $v _ { \alpha }$ instead of $v ( \alpha )$ ; the element v itself is usually denoted by $( v _ { \alpha } ) _ { \alpha \in A }$ , or just $( v _ { \alpha } )$ if the index set is understood. This can be thought of as an indexed family of elements of the sets $V _ { \alpha } .$ , or an $\mathrm { \bf \ddot { \Delta } A - t u p l e . \mathrm { \bf 7 } }$ For each $\beta \in A$ , we have a canonical projection map $\textstyle \pi _ { \beta } \colon \prod _ { \alpha \in A } V _ { \alpha } \to V _ { \beta }$ , defined by $$ \pi_ {\beta} \left((v _ {\alpha}) _ {\alpha \in A}\right) = v _ {\beta}. $$

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pi types and coordinate projections are canonical Lean structures, but the row also asserts the axiom-of-choice nonemptiness theorem for arbitrary nonempty indexed families. No single checked declaration owns that whole set-theoretic bundle. Strict whole-row semantics reject proper subsets and substantive reconstruction from adjacent generic ingredients.
:::

[Searched: N=2026-09-07; A=3b2239e161592472b34e02ad3b7da308f9ce7280; P=db584cd6d46c92f209a44c0f1c829460d327499d; H=5315eef9e4ffb98e0f89f278b765c50a149f66ca]{.unit-provenance}

### Construction/definition — source terminology/construction {#fc08-cb-u083}

::: {.unit-meta}
`FC08-CB-U083` · Appendix B, § Direct Products and Direct Sums; source L19408 · [in Mathlib]{.route-mathlib}
:::

Now suppose that $( V _ { \alpha } ) _ { \alpha \in A }$ is an indexed family of -modules. The direct product of the family is the set $\Pi _ { \alpha \in A } V _ { \alpha }$ , made into an -module by defining addition and scalar multiplication as follows: $$ \begin{array}{c} (v _ {\alpha}) + \big (v _ {\alpha} ^ {\prime} \big) = \big (v _ {\alpha} + v _ {\alpha} ^ {\prime} \big), \\ c (v _ {\alpha}) = (c v _ {\alpha}). \end{array} $$ The zero tue of Theorem A.38, the last three assertions follow from the first, so we need only prove that F is closed.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/Pi.lean::Pi.instModule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Pi.html#Pi.instModule); [`Mathlib/Algebra/Module/Defs.lean::Module`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html); [`Mathlib/Algebra/Module/Submodule/Defs.lean::Submodule`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Defs.html) — Products of modules carry pointwise operations; `Module` and `Submodule` are exactly Lee’s module/submodule notions. For a finite family, product and direct-sum representations are linearly equivalent.
:::

### Proposition B.53 {#fc08-cb-u084}

::: {.unit-meta}
`FC08-CB-U084` · Appendix B, § Direct Products and Direct Sums; source L19416 · [in Mathlib]{.route-mathlib}
:::

(Characteristic Property of the Direct Product). Let $(V_{\alpha})_{\alpha \in A}$ be an indexed family of $R$-modules. For any $R$-module $W$ and any family of $R$-linear maps $G_{\alpha} \colon W \to V_{\alpha}$, there is a unique $R$-linear map $G \colon W \to \prod_{\alpha \in A} V_{\alpha}$ such that $\pi_{\alpha} \circ G = G_{\alpha}$ for each $\alpha$.

::: {.unit-lean}
**Formalized.** [`Mathlib/LinearAlgebra/Pi.lean::LinearMap.pi, LinearMap.proj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Pi.html) — [`LinearMap.pi`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.pi#doc) is the unique linear map into an indexed product with prescribed coordinate maps, with coordinate projections and extensionality giving exactly the product universal property.
:::

### Construction/definition — direct sum of the family to be the submodule of their direct {#fc08-cb-u085}

::: {.unit-meta}
`FC08-CB-U085` · Appendix B, § Direct Products and Direct Sums; source L19420 · [in Mathlib]{.route-mathlib}
:::

Complementary to direct products is the notion of direct sums. Given an indexed family $( V _ { \alpha } ) _ { \alpha \in A }$ as above, we define the direct sum of the family to be the submodule of their direct product consisting of A-tuples $( v _ { \alpha } ) _ { \alpha \in A }$ with the property that $v _ { \alpha } = 0$ for all but finitely many ˛. The direct sum is denoted by $\oplus _ { \alpha \in A } V _ { \alpha }$ , or in the case of a finite family by $V _ { 1 } \oplus \cdots \oplus V _ { k }$ . For finite families of modules, the direct product and the direct sum are identical.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/DirectSum/Basic.lean::DirectSum`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.lof, DirectSum.toModule, DirectSum.toModule_lof, DirectSum.toModule.unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — Mathlib’s `DirectSum` is the finite-support dependent family (`DFinsupp`) representation; `lof` is the canonical injection and `toModule` with its uniqueness theorem is exactly Lee’s direct-sum universal property.
:::

### Construction/definition — source terminology/construction {#fc08-cb-u086}

::: {.unit-meta}
`FC08-CB-U086` · Appendix B, § Direct Products and Direct Sums; source L19422 · [in Mathlib]{.route-mathlib}
:::

For each $\beta \in A$ , there is a canonical -linear injection $\iota _ { \beta } \colon V _ { \beta } \to \bigoplus _ { \alpha \in A } V _ { \alpha } .$ defined by letting $\iota _ { \beta } ( v )$ be the A-tuple $( v _ { \alpha } ) _ { \alpha \in A }$ with $v _ { \beta } = v$ and $v _ { \alpha } = 0$ for ˛ $\neq \beta$ In the case of a finite direct sum, this just means $\iota _ { \beta } ( v ) = ( 0 , \dots , 0 , v , 0 , \dots , 0 )$ , with v in position the properties of these spaces.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/DirectSum/Basic.lean::DirectSum`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.lof, DirectSum.toModule, DirectSum.toModule_lof, DirectSum.toModule.unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — Mathlib’s `DirectSum` is the finite-support dependent family (`DFinsupp`) representation; `lof` is the canonical injection and `toModule` with its uniqueness theorem is exactly Lee’s direct-sum universal property.
:::

### Proposition B.55 {#fc08-cb-u087}

::: {.unit-meta}
`FC08-CB-U087` · Appendix B, § Direct Products and Direct Sums; source L19424 · [in Mathlib]{.route-mathlib}
:::

Proposition B.55 (Characteristic Property of the Direct Sum). Let $( V _ { \alpha } ) _ { \alpha \in A }$ be an indexed family of -modules. Given an -module W and a family of -linear maps $G _ { \alpha } \colon V _ { \alpha } \to W$ , there exists a unique -linear map $G \colon \bigoplus _ { \alpha \in A } V _ { \alpha } \to W$ such that $G \circ \iota _ { \alpha } = G _ { \alpha }$ for ea equivalent: (a) X is locally compact.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/DirectSum/Basic.lean::DirectSum`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.lof, DirectSum.toModule, DirectSum.toModule_lof, DirectSum.toModule.unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — Mathlib’s `DirectSum` is the finite-support dependent family (`DFinsupp`) representation; `lof` is the canonical injection and `toModule` with its uniqueness theorem is exactly Lee’s direct-sum universal property.
:::

### Construction/definition — their external direct sum to distinguish it {#fc08-cb-u088}

::: {.unit-meta}
`FC08-CB-U088` · Appendix B, § Direct Products and Direct Sums; source L19428 · [in Mathlib]{.route-mathlib}
:::

If $W$ is an $R$-module and $(V_{\alpha})_{\alpha \in A}$ is a family of submodules, the characteristic property applied to the inclusions $\iota_{\alpha} \colon V_{\alpha} \hookrightarrow W$ gives a canonical $R$-linear map $\bigoplus_{\alpha} V_{\alpha} \to W$ restricting to the inclusion on each $V_{\alpha}$. It is an isomorphism exactly when every element of $W$ has a unique expression as a finite linear combination $\sum_{\alpha} c_{\alpha}v_{\alpha}$ with $v_{\alpha} \in V_{\alpha}$; then $W$ is identified with $\bigoplus_{\alpha} V_{\alpha}$ and called the internal direct sum of the $V_{\alpha}$. A direct sum of an abstract family is sometimes called their external direct sum by contrast.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/DirectSum/Basic.lean::DirectSum.IsInternal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html#DirectSum.IsInternal); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.IsInternal.submodule_iSup_eq_top, DirectSum.IsInternal.submodule_iSupIndep`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — [`DirectSum.IsInternal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DirectSum.IsInternal#doc) says the canonical map from the external direct sum of submodules to the ambient module is an isomorphism; its characterization is precisely spanning plus uniqueness of finite decomposition.
:::

### Definition/convention — source terminology/construction {#fc08-cb-u089}

::: {.unit-meta}
`FC08-CB-U089` · Appendix B, § Direct Products and Direct Sums; source L19430 · [in Mathlib]{.route-mathlib}
:::

For $\mathcal{R}$-modules $V$ and $W$, the set $\operatorname{Hom}_{\mathcal{R}}(V,W)$ of $\mathcal{R}$-linear maps is an $\mathcal{R}$-module under pointwise addition and scalar multiplication, $$ (F+G)(v) = F(v) + G(v), \qquad (aF)(v) = a\,F(v). $$ For real vector spaces this is the space $\operatorname{L}(V;W)$ of linear maps.

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.toModule, DirectSum.toModule.unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — Linear maps form the pointwise `R`-module `V →ₗ[R] W`. The direct-sum universal property gives the canonical linear equivalence between maps out of `⨁ Vα` and families of maps `Vα →ₗ[R] W`, i.e. Lee’s Hom/direct-product isomorphism.
:::

### Proposition B.57 {#fc08-cb-u090}

::: {.unit-meta}
`FC08-CB-U090` · Appendix B, § Direct Products and Direct Sums; source L19438 · [in Mathlib]{.route-mathlib}
:::

Let $(V_{\alpha})_{\alpha \in A}$ be an indexed family of $R$-modules. For each $R$-module $W$ there is a canonical isomorphism $$ \operatorname{Hom}_{R}\left(\bigoplus_{\alpha \in A} V_{\alpha},\ W\right) \cong \prod_{\alpha \in A} \operatorname{Hom}_{R}(V_{\alpha},W). $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Algebra/Module/LinearMap/Defs.lean::LinearMap`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/LinearMap/Defs.html); [`Mathlib/Algebra/DirectSum/Module.lean::DirectSum.toModule, DirectSum.toModule.unique`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Module.html) — Linear maps form the pointwise `R`-module `V →ₗ[R] W`. The direct-sum universal property gives the canonical linear equivalence between maps out of `⨁ Vα` and families of maps `Vα →ₗ[R] W`, i.e. Lee’s Hom/direct-product isomorphism.
:::

