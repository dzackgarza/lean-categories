---
title: "FC08 — John M. Lee, Introduction to Smooth Manifolds, 2nd ed. (2013)"
---

FC08 — Lee, *Introduction to Smooth Manifolds*.

This chapter contains 4 definitions, 6 theorems and 1 convention.

Of the 11 statements checked against Lean, 3 are formalized somewhere and 8 are not.

| Status | Statements | Share | What it means |
| --- | ---: | ---: | --- |
| [not formalized]{.route-unmatched} | 8 | 73% | A documented search found no Lean statement of it anywhere. |
| [in Mathlib]{.route-mathlib} | 3 | 27% | Mathlib states and proves it. |
| **checked in total** | **11** | | |

::: {.callout-note collapse="true"}
## Which versions of Lean and Mathlib were searched

- Canonical source block: FC08 Lee, Appendix D, `FC08-CD-U001`–`FC08-CD-U011`, exactly 11 unique contiguous rows retrieved from [FC08 — John M. Lee, Introduction to Smooth Manifolds](/sources/fc08/) through `agent-memory`.
- Search order: project at `A=3b2239e161592472b34e02ad3b7da308f9ce7280`, pinned Mathlib `P=db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean 4.33.0), current upstream `H=5315eef9e4ffb98e0f89f278b765c50a149f66ca` (Apache-2.0, Lean 4.34.0-rc2), then indexed/current/open Mathlib work, packages/Reservoir, broad GitHub Lean repositories, and local reference sources. No `project-existing`, `package-import`, or `reference-port` route survived strict whole-row checking.
- Appendix D has 3 pinned `mathlib` rows and 8 dated `unmatched` rows. Positive rows are: U001, U002, U006.
- `/tmp/fc08-cd-witness.lean` compiles at exact P and checks Mathlib’s public ODE surface: integral-curve predicates, the Picard operator, Picard–Lindelöf existence families, interval/open-set uniqueness theorems, solution regularity in time, and generalized eigenspaces.
- U001/U002 map directly to [`ODE.IsIntegralCurveOn`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ODE.IsIntegralCurveOn#doc) and its time-independent specialization. U006 is exact: [`ODE.picard_apply`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ODE.picard_apply#doc) is Lee’s integral operator, including the initial-value constant and interval integral.
- Mathlib’s current Picard–Lindelöf development is substantial but stops short of Lee’s strongest bundled regularity claims. It gives local solution families with continuous/Lipschitz dependence on initial points and `C^n` regularity of each solution curve in time; targeted P/H search found no smooth-dependence theorem for the flow as a function of initial data. This blocks U003, U008, and U009 under strict semantics.
- The public existence/uniqueness results use uniform Lipschitz bounds on a chosen region. Lee U005/U007 assume only local Lipschitz continuity and quantify over neighborhoods/common domains. Their localization/chaining argument is not inferred from the stronger local ingredients without a checked wrapper theorem.
- Broad GitHub search found a current Lean control-theory project that explicitly axiomatizes Picard–Lindelöf-style existence rather than proving a reusable replacement; it therefore supplies no acceptable import/reference route. No compatible external source was found for Lee’s nonlinear comparison theorem or the full `2×2` ODE solution classification.
- `N=2026-09-07` marks dated unmatched decisions. Strict whole-row semantics apply uniformly.
:::

### Convention/notation — source terminology/construction {#fc08-cd-u001}

::: {.unit-meta}
`FC08-CD-U001` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20228 · [in Mathlib]{.route-mathlib}
:::

Here is the general setting in which ODEs appear in this book: we are given n realvalued continuous functions $V ^ { 1 } , \ldots , V ^ { n }$ defined on some open subset $W \subseteq \mathbb { R } ^ { n + 1 }$ and the goal is to find differentiable real-valued functions ${ \bar { y } } ^ { 1 } , \ldots , y ^ { n }$ solving the following initial value problem: $$ \dot {y} ^ {i} (t) = V ^ {i} \big (t, y ^ {1} (t), \ldots , y ^ {n} (t) \big), i = 1, \ldots , n,\tag{D.1} $$ $$ y ^ {i} (t _ {0}) = c ^ {i}, $$ $$ i = 1, \ldots , n,\tag{D.2} $$ where $( t _ { 0 } , c ^ { 1 } , \ldots , c ^ { n } )$ is an arbitrary point in $W$ . (Here and elsewhere in the book, we use a dot to denote an ordinary derivative with respect to t whenever convenient, primarily when there are superscripts that would make the prime notation cu {c c c} 1 \ldots 0 \ldots 0 \\ \ddots \\ c \\ \ddots \\ 0 \ldots 0 \ldots 1 \end{array} \right) = \left( \begin{array}{c c c} A _ {1} ^ {1} \ldots c A _ {i} ^ {1} \ldots A _ {n} ^ {1} \\ \vdots & \vdots & \vdots \\ A _ {1} ^ {j} \ldots c A _ {i} ^ {j} \ldots A _ {n} ^ {j} \\ \vdots & \vdots & \vdots \\ A _ {1} ^ {n} \ldots c A _ {i} ^ {n} \ldots A _ {n} ^ {n} \end{array} \right).

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/ODE/Basic.lean::ODE.IsIntegralCurveOn, ODE.IsIntegralCurveAt, ODE.IsIntegralCurve`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/Basic.html); [`Mathlib/Analysis/Calculus/Deriv/Basic.lean::HasDerivAt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html) — Mathlib’s `IsIntegralCurveOn γ v J` is exactly the coordinate-free system `γ' (t)=v t (γ t)` on a time set; the initial condition is the equality `γ t₀ = c`. Taking `E=ℝ^n` realizes Lee’s full nonautonomous IVP notation componentwise.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### Definition/convention — autonomous {#fc08-cd-u002}

::: {.unit-meta}
`FC08-CD-U002` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20246 · [in Mathlib]{.route-mathlib}
:::

Most of our applications of the theory are confined to the following special case: if the functions $V ^ { i }$ on the right-hand side of (D.1) do not depend explicitly on t, the system is said to be autonomous; otherwise, it is nonautonomous. We begin by stating and proving our main theorem in the autonomous case. Afterwards, we show how the general case follows from this one.

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/ODE/Basic.lean::ODE.IsIntegralCurveOn`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/Basic.html#ODE.IsIntegralCurveOn) — An autonomous system is exactly the specialization of Mathlib’s time-dependent vector field to `fun _ => V`; nonautonomous means no such time-independent factorization is assumed. This is a direct specialization of the canonical ODE object.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### Theorem D.1 {#fc08-cd-u003}

::: {.unit-meta}
`FC08-CD-U003` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20248 · [not formalized]{.route-unmatched}
:::

(Fundamental Theorem for Autonomous ODEs). Suppose $U \subseteq \mathbb{R}^{n}$ is open and $V \colon U \to \mathbb{R}^{n}$ is smooth. Consider the initial value problem $$ \dot{y}^{i}(t) = V^{i}\big(y^{1}(t),\dots,y^{n}(t)\big), \quad i = 1,\dots,n, \tag{D.3} $$ $$ y^{i}(t_{0}) = c^{i}, \quad i = 1,\dots,n, \tag{D.4} $$ for $t_{0} \in \mathbb{R}$ and $c = (c^{1},\dots,c^{n}) \in U$. (a) Existence: for any $t_{0} \in \mathbb{R}$ and $x_{0} \in U$ there are an open interval $J_{0}$ containing $t_{0}$ and an open subset $U_{0} \subseteq U$ containing $x_{0}$ such that for each $c \in U_{0}$ there is a $C^{1}$ map $y \colon J_{0} \to U$ solving (D.3)–(D.4). (b) Uniqueness: any two differentiable solutions agree on their common domain. (c) Smoothness: with $J_{0}$ and $U_{0}$ as in (a), the map $\theta \colon J_{0} \times U_{0} \to U$ given by $\theta(t,x) = y(t)$, where $y$ solves (D.3) with $y(t_{0}) = x$, is smooth.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Pinned Mathlib proves local existence for `C¹` autonomous vector fields and constructs local families of solutions, and separately proves regularity of each solution in time. However Lee D.1(c) requires smooth dependence of the local flow `θ(t,x)` on both time and initial condition. Targeted P/H search found only continuous/Lipschitz dependence on initial data, not the required smooth dependence theorem, so the bundled theorem is not complete. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Theorem D.2 {#fc08-cd-u004}

::: {.unit-meta}
`FC08-CD-U004` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20268 · [not formalized]{.route-unmatched}
:::

(ODE Comparison Theorem). Let $J \subseteq \mathbb{R}$ be an open interval and suppose the differentiable function $u \colon J \to \mathbb{R}^{n}$ satisfies $|u'(t)| \leq f(|u(t)|)$ for all $t \in J$, where $f \colon [0,\infty) \to [0,\infty)$ is Lipschitz continuous. If for some $t_{0} \in J$ a differentiable $v \colon [0,\infty) \to [0,\infty)$ satisfies $v'(t) = f(v(t))$ and $v(0) = |u(t_{0})|$, then $$ |u(t)| \leq v(|t - t_{0}|) \tag{D.5} $$ for all $t \in J$.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib’s ODE library contains Grönwall comparison estimates, but Lee D.2 is a nonlinear scalar comparison theorem with bound `‖u(t)‖ ≤ v(|t-t₀|)` for a general Lipschitz `f`. No checked theorem with these hypotheses and conclusion was found. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Theorem D.3 {#fc08-cd-u005}

::: {.unit-meta}
`FC08-CD-U005` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20320 · [not formalized]{.route-unmatched}
:::

(Existence of ODE Solutions). Let $U \subseteq \mathbb{R}^{n}$ be open and suppose $V \colon U \to \mathbb{R}^{n}$ is locally Lipschitz continuous. For any $(t_{0},x_{0}) \in \mathbb{R} \times U$ there are an open interval $J_{0} \subseteq \mathbb{R}$ containing $t_{0}$, an open subset $U_{0} \subseteq U$ containing $x_{0}$, and for each $c \in U_{0}$ a $C^{1}$ map $y \colon J_{0} \to U$ satisfying the initial value problem (D.3)–(D.4).

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Picard–Lindelöf gives local existence after packaging a uniform Lipschitz constant and boundedness on a spacetime box. Lee D.3 assumes only local Lipschitz continuity of an autonomous vector field and concludes a uniform neighborhood of initial points. No public theorem at P/H was found that performs this localization at exactly the source interface; constructing the Picard parameters from local Lipschitz data would be substantive. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Definition/convention — new map I y {#fc08-cd-u006}

::: {.unit-meta}
`FC08-CD-U006` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20330 · [in Mathlib]{.route-mathlib}
:::

Suppose $J_{0}$ is an open interval containing $t_{0}$. For any continuous map $y \colon J_{0} \to U$, define a new map $Iy \colon J_{0} \to \mathbb{R}^{n}$ by $$ Iy(t) = c + \int_{t_{0}}^{t} V(y(s))\,ds. \tag{D.7} $$

::: {.unit-lean}
**Formalized.** [`Mathlib/Analysis/ODE/PicardLindelof.lean::ODE.picard, ODE.picard_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/PicardLindelof.html) — Mathlib’s Picard operator is defined by `x₀ + ∫ τ in t₀..t, f τ (α τ)`. Specializing the vector field to the autonomous `fun _ => V` gives Lee’s `I y(t)=c+∫_{t₀}^t V(y(s)) ds` exactly.
:::

[Searched: P=db584cd6d46c92f209a44c0f1c829460d327499d; Apache-2.0; Lean 4.33.0]{.unit-provenance}

### Theorem D.4 {#fc08-cd-u007}

::: {.unit-meta}
`FC08-CD-U007` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20378 · [not formalized]{.route-unmatched}
:::

Theorem D.4 (Uniqueness of ODE Solutions). Let $U \subseteq \mathbb { R } ^ { n }$ be an open subset, and suppose V $U \to \mathbb { R } ^ { n }$ is locally Lipschitz continuous. For any $t _ { 0 } \in \mathbb { R }$ and $c \in U$ any two differentiable solutions to (D.3)–(D.4) are equal on thei v + a ^ {\prime} v ^ {\prime}, w \rangle = a \langle v, w \rangle + a ^ {\prime} \langle v ^ {\prime}, w \rangle , \\ \langle v, b w + b ^ {\prime} w ^ {\prime} \rangle = b \langle v, w \rangle + b ^ {\prime} \langle v, w ^ {\prime} \rangle ; \end{array} $$ (iii) POSITIVE DEFINITENESS: $$ \langle v, v \rangle \geq 0, \quad \text { with equality if and only if } v = 0.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has exact uniqueness theorems for ODEs under a uniform `LipschitzOnWith K` hypothesis on the relevant region. Lee D.4 assumes only local Lipschitz continuity on `U` and uniqueness on arbitrary common domains. No checked theorem bridges those hypotheses globally without a localization/chaining argument. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Theorem D.5 {#fc08-cd-u008}

::: {.unit-meta}
`FC08-CD-U008` · Appendix D, § Existence, Uniqueness, and Smoothness; source L20394 · [not formalized]{.route-unmatched}
:::

(Smoothness of ODE Solutions). Suppose $U \subseteq \mathbb{R}^{n}$ is open and $V \colon U \to \mathbb{R}^{n}$ is locally Lipschitz continuous. Suppose $U_{0} \subseteq U$ is open, $J_{0} \subseteq \mathbb{R}$ is an open interval containing $t_{0}$, and $\theta \colon J_{0} \times U_{0} \to U$ is a map such that for each $x \in U_{0}$ the function $y(t) = \theta(t,x)$ solves the initial value problem (D.3)–(D.4) with $c = x$. If $V$ is of class $C^{k}$ for some $k \geq 0$, then so is $\theta$.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — [`ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt#doc) proves that each solution curve has the same time-regularity as the vector field, but Lee D.5 asserts `C^k` dependence of the whole solution map `θ(t,x)` on initial conditions. No pinned/current theorem supplies that parameter-smoothness statement. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Theorem D.6 {#fc08-cd-u009}

::: {.unit-meta}
`FC08-CD-U009` · Appendix D, § Nonautonomous Systems; source L20548 · [not formalized]{.route-unmatched}
:::

$J \subseteq \mathbb { R }$ be an open interval and $U \subseteq \mathbb { R } ^ { n }$ be an open subset, and let V $J \times U \to \mathbb { R } ^ { n }$ be a smooth vector-valued function. (a) EXISTENCE: For any $s _ { 0 } \in J$ and $x _ { 0 } \in U$ , there exist an open interval $J _ { 0 } \subseteq J$ containing $s _ { 0 }$ and an open subset $U _ { 0 } \subseteq U$ containing $x _ { 0 } .$ , such that for each $t _ { 0 } \in J _ { 0 }$ and $c = ( c ^ { 1 } , \ldots , c ^ { n } ) \in U _ { 0 }$ , there is a $C ^ { 1 }$ map $y \colon J _ { 0 } \to U$ that solves $( \mathrm { D } . 1 ) { - } ( \mathrm { D } . 2 )$ (b) UNIQUENESS: Any two differentiable solutions to (D.1)–(D.2) agree on their common domain. (c) SMOOTHNESS: Let $J _ { 0 }$ and $U _ { 0 }$ be as in (a), and define a map  $J _ { 0 } \times J _ { 0 } \times$ $U _ { 0 } \to U$ by letting $\theta ( t , t _ { 0 } , c ) = y ( t )$ , where y $J _ { 0 } \to U$ is the unique solution _ {\mathcal {R}} (V _ {\alpha}, W).

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — The time-dependent Picard–Lindelöf API supplies local existence and uniqueness ingredients, but Lee D.6 additionally requires smooth dependence jointly on `(t,t₀,c)`. P/H search found no theorem packaging this full nonautonomous flow regularity. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Definition/convention — separable {#fc08-cd-u010}

::: {.unit-meta}
`FC08-CD-U010` · Appendix D, § Separable Equations; source L20570 · [not formalized]{.route-unmatched}
:::

A first-order differential equation for a single function $y ( t )$ that can be written in the form $$ y ^ {\prime} (t) = f \big (y (t) \big) g (t), $$ where $f$ and g are continuous functions with $f$ nonvanishing, is said to be separable. Any separable equation can be solved (at least in principle) by dividing through by $f \left( y ( t ) \right)$ , integrating both sides, and using substitution to transform the left-hand integral: $$ \frac {y ^ {\prime} (t)}{f (y (t))} = g (t), $$ $$ \int \frac {y ^ {\prime} (t) d t}{f (y (t))} = \int g (t) d t, $$ $$ \int {\frac {d y}{f (y)}} = \int g (t) d t. $$ If the resulting indefinite integrals can be computed explicitly, the result is a relation involving y and t that can (again, in principle) be solved for y. The constant of integration can then be adjusted to achieve the desired initial condition for y. Separable equations include those of the form $y ^ { \prime } ( t ) = g ( t )$ as a trivial special case, which can be solved by direct int ed the total derivative of F at a.

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — No canonical Lean owner was found for the source-specific class of separable first-order equations together with the division/substitution solution recipe. Interval-integration and chain-rule ingredients are only proper subsets. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

### Definition/convention — generalized eigenvector) {#fc08-cd-u011}

::: {.unit-meta}
`FC08-CD-U011` · Appendix D, § 2 × 2 Constant-Coefficient Linear Systems; source L20608 · [not formalized]{.route-unmatched}
:::

It is always possible to find at least one (perhaps complex-valued) solution of the form $Z ( t ) = e ^ { \lambda t } Z _ { 0 }$ , where  is an eigenvalue of A and $Z _ { 0 }$ is a corresponding eigenvector. If A has two distinct eigenvalues, then there are two such solutions, and they span the solution space. (If the initial conditions are real, then the corresponding solution is real.) On the other hand, if A has only one eigenvalue, there are two cases. If $A - \lambda I _ { 2 } \neq 0$ , then there is a vector $Z _ { 1 }$ (called a generalized eigenvector) such that $( A - \lambda I _ { 2 } ) Z _ { 1 } = Z _ { 0 }$ , and a second linearly independent solution is given by $Z ( t ) = e ^ { \lambda t } ( t Z _ { 0 } + Z _ { 1 } )$ . Otherwise, $A = \lambda I _ { 2 }$ , and the two equations in (D.21) are uncoupled and can be solved independently. ##

::: {.unit-lean}
**Not formalized.** none; no complete checked declaration under strict bundle semantics — Mathlib has `genEigenspace`/`HasGenEigenvector`, so the generalized-eigenvector notion is formalized, but the row bundles the complete solution classification of complexified `2×2` constant-coefficient ODEs, including distinct/repeated eigenvalue cases and the explicit `e^{λt}(tZ₀+Z₁)` solution. No checked whole-row theorem was found. Strict whole-row semantics reject proper subsets, stronger/weaker hypotheses without a checked bridge, and substantive reconstruction.
:::

