---
title: "Epilogue: Theorems in Category Theory"
---

FC03 — Riehl, *Category Theory in Context*.

This chapter contains 7 definitions, 4 theorems, 2 constructions and 1 other statements.

Nobody has checked this chapter against Lean yet, so the statements below
say nothing about whether they are formalized.

### Definition: A symmetric monoidal category has a bifunctor ⊗, unit object, and natural… {#fc03-ce-u001}

::: {.unit-meta}
`FC03-CE-U001` · §E.2, pp. 219–220; L7337 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

A symmetric monoidal category has a bifunctor ⊗, unit object, and natural symmetry, associativity, and unit isomorphisms satisfying coherence; a monoidal category omits symmetry.

### Named comparison {#fc03-ce-u002}

::: {.unit-meta}
`FC03-CE-U002` · §E.2, pp. 219–220; L7343 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

Finite-product and finite-coproduct categories are symmetric monoidal; Mod_R has ⊕ and, for commutative R, ⊗_R; chain complexes have the graded tensor product.

### Theorem E.2.2 {#fc03-ce-u003}

::: {.unit-meta}
`FC03-CE-U003` · §E.2, pp. 219–220; L7357 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

Mac Lane–Kelly coherence: every formal diagram in a symmetric monoidal category built from associators, unitors, and symmetries commutes.

### Construction: The unit interval I=[0,1] defines paths {#fc03-ce-u004}

::: {.unit-meta}
`FC03-CE-U004` · §E.3, p. 221; L7363 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

The unit interval I=[0,1] defines paths; composable paths p,q compose through the homeomorphism δ:I≅I∨I followed by p∨q.

### Definition: A bipointed space is a space with two distinct closed designated endpoints {#fc03-ce-u005}

::: {.unit-meta}
`FC03-CE-U005` · §E.3, p. 221; L7379 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

A bipointed space is a space with two distinct closed designated endpoints; morphisms preserve the two endpoints, and X∨X is formed by gluing the right point of one copy to the left point of the other.

### Theorem E.3.1 {#fc03-ce-u006}

::: {.unit-meta}
`FC03-CE-U006` · §E.3, p. 221; L7381 · after [`FC03-C01-U049`](c01.html#fc03-c01-u049), [`FC03-C03-U008`](c03.html#fc03-c03-u008), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

Freyd–Leinster: the unit interval (I,0,1) is the terminal bipointed space equipped with a bipointed map X→X∨X; equivalently it is the terminal coalgebra for X↦X∨X.

### Definition: A Grothendieck topos is a reflective full subcategory of a presheaf category… {#fc03-ce-u007}

::: {.unit-meta}
`FC03-CE-U007` · §E.4, p. 222; L7393 · after [`FC03-C03-U040`](c03.html#fc03-c03-u040)
:::

A Grothendieck topos is a reflective full subcategory of a presheaf category whose reflector preserves finite limits; equivalently it is a category of sheaves on a small site.

### Theorem E.4.1 {#fc03-ce-u008}

::: {.unit-meta}
`FC03-CE-U008` · §E.4, p. 222; L7407 · after [`FC03-C03-U040`](c03.html#fc03-c03-u040)
:::

Giraud: E is a Grothendieck topos iff it is locally small; has finite limits; has all small coproducts, disjoint and universal; equivalence relations have universal coequalizers; every equivalence relation is effective and every epi a coequalizer; and E has a separating set.

### Definitions/comparisons {#fc03-ce-u009}

::: {.unit-meta}
`FC03-CE-U009` · §E.4, p. 222; L7417 · after [`FC03-C03-U040`](c03.html#fc03-c03-u040)
:::

A coproduct is disjoint when its injections are monic with pairwise-initial pullbacks; a colimit is universal when stable under pullback; an effective equivalence relation is a kernel pair.

### Definition E.5.1 {#fc03-ce-u010}

::: {.unit-meta}
`FC03-CE-U010` · §E.5, pp. 223–224; L7437 · after [`FC03-C03-U012`](c03.html#fc03-c03-u012), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

A category is abelian if it has a zero object 0, that is both initial and terminal, it has all binary products and binary coproducts, it has all kernels and cokernels, defined respectively to be the equalizer and coequalizer of a map $f \colon A \to B$ with the zero map $A 0 B ,$ and all monomorphisms and epimorphisms arise as kernels or cokernels, respectively.

### Construction/terminology {#fc03-ce-u011}

::: {.unit-meta}
`FC03-CE-U011` · §E.5, pp. 223–224; L7447 · after [`FC03-C03-U012`](c03.html#fc03-c03-u012), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

In an abelian category finite products and coproducts coincide as biproducts/direct sums; hom-sets are canonically abelian groups and composition is bilinear.

### Definition: The image of f is ker(coker f), equivalently coker(ker f) {#fc03-ce-u012}

::: {.unit-meta}
`FC03-CE-U012` · §E.5, pp. 223–224; L7451 · after [`FC03-C03-U012`](c03.html#fc03-c03-u012), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

The image of f is ker(coker f), equivalently coker(ker f); a composable sequence is exact when ker f_n = im f_{n+1}.

### Definition: A functor between abelian categories is exact when it preserves exact… {#fc03-ce-u013}

::: {.unit-meta}
`FC03-CE-U013` · §E.5, pp. 223–224; L7457 · after [`FC03-C03-U012`](c03.html#fc03-c03-u012), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

A functor between abelian categories is exact when it preserves exact sequences, equivalently when it is both left and right exact.

### Theorem E.5.2 {#fc03-ce-u014}

::: {.unit-meta}
`FC03-CE-U014` · §E.5, pp. 223–224; L7459 · after [`FC03-C03-U012`](c03.html#fc03-c03-u012), [`FC03-C03-U019`](c03.html#fc03-c03-u019)
:::

Freyd–Mitchell: every small abelian category A admits an exact fully faithful functor A↪Mod_R for some ring R, embedding A as a full subcategory.

