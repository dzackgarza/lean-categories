---
title: "FC01 Appendix I — Cartesian Products and Zorn's Lemma"
---

FC01 — Dummit & Foote, *Abstract Algebra*.

This chapter contains 6 definitions, 4 theorems, 1 proposition, 1 convention and 1 other statements.

Nobody has checked this chapter against Lean yet, so the statements below
say nothing about whether they are formalized.

### convention: An indexing set is a set whose elements index a family ({Ai\mid i\in I}). {#fc01-ai-u001}

::: {.unit-meta}
`FC01-AI-U001` · Appendix I §1, p.905; extraction l.31695 · after `FC01-C00-U005`
:::

An **indexing set** is a set whose elements index a family ({A_i\mid i\in I}).

### definition: For a family ({Ai}{i\in I}), a choice function is (f:I\to\bigcupi Ai) with… {#fc01-ai-u002}

::: {.unit-meta}
`FC01-AI-U002` · Appendix I §1, p.905; extraction l.31697ff · after [`FC01-AI-U001`](#fc01-ai-u001)
:::

For a family ({A_i}_{i\in I}), a **choice function** is (f:I\to\bigcup_i A_i) with (f(i)\in A_i) for every (i).

### definition: The Cartesian product (\prod{i\in I}Ai) is the set of all choice functions {#fc01-ai-u003}

::: {.unit-meta}
`FC01-AI-U003` · Appendix I §1, p.905; extraction l.31700ff · after [`FC01-AI-U002`](#fc01-ai-u002)
:::

The **Cartesian product** (\prod_{i\in I}A_i) is the set of all choice functions; it is empty if (I) or any component is empty.

### definition: For (j\in I), (Aj) is the (j)-th component, (aj) the (j)-th coordinate, and… {#fc01-ai-u004}

::: {.unit-meta}
`FC01-AI-U004` · Appendix I §1, p.905; extraction l.31700ff · after [`FC01-AI-U003`](#fc01-ai-u003)
:::

For (j\in I), (A_j) is the (j)-th **component**, (a_j) the (j)-th **coordinate**, and the (j)-th **projection** sends ((a_i)_i\mapsto a_j).

### comparison {#fc01-ai-u005}

::: {.unit-meta}
`FC01-AI-U005` · Appendix I §1, pp.905–906; extraction l.31710ff · after [`FC01-AI-U003`](#fc01-ai-u003)
:::

For (I={1,\dots,n}), choice functions are canonically bijective with ordered (n)-tuples; for (I=\mathbb Z^+), they are infinite sequences.

### proposition {#fc01-ai-u006}

::: {.unit-meta}
`FC01-AI-U006` · Appendix I §1, p.906; Proposition 1, extraction l.31753 · after [`FC01-AI-U001`](#fc01-ai-u001), [`FC01-AI-U003`](#fc01-ai-u003)
:::

For nonempty countable $I$, $\lvert\prod_{i\in I}A_i\rvert=\prod_{i\in I}\lvert A_i\rvert$; in particular finite Cartesian-product cardinalities multiply.

### definition: A partial order on nonempty (A) is a reflexive, antisymmetric, transitive… {#fc01-ai-u007}

::: {.unit-meta}
`FC01-AI-U007` · Appendix I §2, p.907; extraction l.31791 · after `FC01-C00-U013`
:::

A **partial order** on nonempty (A) is a reflexive, antisymmetric, transitive relation; (A) with such a relation is a partially ordered set.

### definition: In a poset {#fc01-ai-u008}

::: {.unit-meta}
`FC01-AI-U008` · Appendix I §2, p.907; extraction l.31801 · after [`FC01-AI-U007`](#fc01-ai-u007)
:::

In a poset: a **chain** is a pairwise comparable subset; an **upper bound** of (B\subseteq A) is (u) with (b\le u) for all (b\in B); a **maximal element** (m) satisfies (m\le x\Rightarrow m=x).

### theorem: Zorn's Lemma: if a nonempty poset has an upper bound for every chain, then… {#fc01-ai-u009}

::: {.unit-meta}
`FC01-AI-U009` · Appendix I §2, p.908; Zorn's Lemma, l.31839ff · after [`FC01-AI-U007`](#fc01-ai-u007), [`FC01-AI-U008`](#fc01-ai-u008)
:::

**Zorn's Lemma:** if a nonempty poset has an upper bound for every chain, then it has a maximal element.

### theorem: Axiom of Choice: the Cartesian product of any nonempty family of nonempty… {#fc01-ai-u010}

::: {.unit-meta}
`FC01-AI-U010` · Appendix I §2, p.908; Axiom of Choice, l.31843ff · after [`FC01-AI-U002`](#fc01-ai-u002), [`FC01-AI-U003`](#fc01-ai-u003)
:::

**Axiom of Choice:** the Cartesian product of any nonempty family of nonempty sets is nonempty, equivalently a choice function exists.

### definition: A well ordering is a total order in which every nonempty subset has a minimum. {#fc01-ai-u011}

::: {.unit-meta}
`FC01-AI-U011` · Appendix I §2, p.908; extraction l.31849 · after [`FC01-AI-U007`](#fc01-ai-u007)
:::

A **well ordering** is a total order in which every nonempty subset has a minimum.

### theorem: Well Ordering Principle: every nonempty set admits a well ordering. {#fc01-ai-u012}

::: {.unit-meta}
`FC01-AI-U012` · Appendix I §2, p.908; Well Ordering Principle, l.31851ff · after [`FC01-AI-U011`](#fc01-ai-u011)
:::

**Well Ordering Principle:** every nonempty set admits a well ordering.

### theorem: Under Zermelo–Fraenkel set theory, Zorn's Lemma, the Axiom of Choice, and… {#fc01-ai-u013}

::: {.unit-meta}
`FC01-AI-U013` · Appendix I §2, p.908; Theorem 2, l.31853 · after [`FC01-AI-U009`](#fc01-ai-u009), [`FC01-AI-U010`](#fc01-ai-u010), [`FC01-AI-U012`](#fc01-ai-u012)
:::

Under Zermelo–Fraenkel set theory, Zorn's Lemma, the Axiom of Choice, and the Well Ordering Principle are equivalent.

