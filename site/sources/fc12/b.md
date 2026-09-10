---
title: "FC12 — Beauville, Complex Algebraic Surfaces, 2nd ed."
---

FC12 — Beauville, *Complex Algebraic Surfaces* — block `FC12-B`.

7 units. 0 have a Lean owner; 7 do not.

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`unmatched`]{.route-unmatched} | 7 | 100% | No checked Lean owner was found. |
| **total** | **7** | | |

::: {.callout-note collapse="true"}
## How this chapter was searched

- Canonical block `FC12-B-U001`–`FC12-B-U007`, exactly 7 contiguous units.
- Search order: project `A=12618f8abc2b4852b3da9ab65c3bc547ac4c1f19`, P=[`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/commit/db584cd6d46c92f209a44c0f1c829460d327499d), H=[`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`](https://github.com/leanprover-community/mathlib4/commit/71a80585ee495fc24472fd0eaffc89d94e4fd8d6), current/open/indexed, Reservoir/packages, broad GitHub Lean, and local references/mappings.
- Result: 0 positive routes and 7 dated `unmatched` rows.
- Targeted searches found no compatible Lean implementation of the appendix's algebraic/compact-complex surface classification layer. Generic algebra, topology, Frobenius, group-action, manifold, or bilinear-form infrastructure is only partial.
- `N=2026-09-07` marks dated unmatched decisions; strict whole-row semantics apply uniformly.
:::

### Convention / notation {#fc12-b-u001}

::: {.unit-meta}
`FC12-B-U001` · Appendix B, source L2962 · [`unmatched`]{.route-unmatched}
:::

For a compact complex surface, set $h=\dim H^0(X,\Omega_X^1)$ and let $b^+,b^-$ be the positive and negative indices of the intersection form on $H^2(X,\mathbf R)$.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Proposition B.1 {#fc12-b-u002}

::: {.unit-meta}
`FC12-B-U002` · Appendix B, source L2964 · after [`FC12-C03-U020`](c03.html#fc12-c03-u020), [`FC12-B-U001`](#fc12-b-u001) · [`unmatched`]{.route-unmatched}
:::

Proposition B.1 Let $X$ be a compact compler surface. Then either $b _ { 1 } ( X )$ is even, $b ^ { + } = 2 p _ { g } + 1$ and $\begin{array} { r } { q ( X ) = h ( X ) = \frac { 1 } { 2 } b _ { 1 } ( X ) } \end{array}$ ： or $b _ { 1 } ( X )$ is odd, $b ^ { + } = 2 p _ { g }$ ， $h ( X ) = q ( X ) - 1$ and $b _ { 1 } ( X ) = 2 q ( X ) - 1$

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Classification / comparison {#fc12-b-u003}

::: {.unit-meta}
`FC12-B-U003` · Appendix B, source L3012-L3021 · after [`FC12-C03-U001`](c03.html#fc12-c03-u001), [`FC12-C05-U009`](c05.html#fc12-c05-u009), [`FC12-C06-U023`](c06.html#fc12-c06-u023), [`FC12-C07-U001`](c07.html#fc12-c07-u001), [`FC12-C08-U003`](c08.html#fc12-c08-u003), [`FC12-C08-U004`](c08.html#fc12-c08-u004), [`FC12-C09-U003`](c09.html#fc12-c09-u003), [`FC12-C10-U001`](c10.html#fc12-c10-u001) · [`unmatched`]{.route-unmatched}
:::

If $b_1$ is even, a compact complex surface is Kähler and the algebraic-style Kodaira classification applies: ruled/rational for $\kappa=-\infty$, tori/K3/Enriques/bielliptic for $\kappa=0$, elliptic for $\kappa=1$, and algebraic general type for $\kappa=2$.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Proposition B.2 {#fc12-b-u004}

::: {.unit-meta}
`FC12-B-U004` · Appendix B, source L3014-L3021 · [`unmatched`]{.route-unmatched}
:::

Proposition B.2. A compact complex surface admitting a line bundle $L$ with $c_1(L)^2>0$ is projective.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Classification / definition {#fc12-b-u005}

::: {.unit-meta}
`FC12-B-U005` · Appendix B, source L3025-L3027 · after [`FC12-C03-U020`](c03.html#fc12-c03-u020), [`FC12-C07-U001`](c07.html#fc12-c07-u001) · [`unmatched`]{.route-unmatched}
:::

If $b_1$ is odd, $\kappa=2$ is impossible; for $\kappa=-\infty$ one obtains class $\mathrm{VII}_0$, with $b_1=q=1$, and the $b_2=0$ cases are Hopf or Inoue surfaces.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Definition / construction {#fc12-b-u006}

::: {.unit-meta}
`FC12-B-U006` · Appendix B, source L3029 · [`unmatched`]{.route-unmatched}
:::

A primary Kodaira surface is obtained as $L^*/q^{\mathbf Z}$ from a nonzero-degree line bundle over an elliptic curve; it is a principal elliptic bundle with $K\equiv0$, $q=2$, and $b_1=3$.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

### Definition: A secondary Kodaira surface is a finite free quotient of a primary Kodaira… {#fc12-b-u007}

::: {.unit-meta}
`FC12-B-U007` · Appendix B, source L3031 · after [`FC12-B-U006`](#fc12-b-u006) · [`unmatched`]{.route-unmatched}
:::

A secondary Kodaira surface is a finite free quotient of a primary Kodaira surface; it has $q=b_1=1$ and nontrivial torsion canonical class of order $2,3,4,$ or $6$.

::: {.unit-lean}
**Not in Lean.** none; no complete checked declaration under strict bundle semantics — No complete Lean owner was found for this compact-complex-surface Hodge/intersection/Kodaira statement. P/H lacks compact complex surface objects with Hodge numbers/intersection-form indices, the Kähler/projectivity/classification theorems used here, and Hopf/Inoue/Kodaira surface constructions; strict whole-row semantics reject generic complex-manifold, bilinear-form, line-bundle, or quotient ingredients as proper subsets.
:::

