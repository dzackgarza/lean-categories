---
title: "Appendix B. Some homological algebra"
---

FC13 — Matsumura, *Commutative Ring Theory* — block `FC13-CB`.

This chapter is enumerated but not yet swept against Lean: the statements
below carry no routing verdict.

### Definition: complex, homology and cohomology {#fc13-cb-u001}

::: {.unit-meta}
`FC13-CB-U001` · Appendix B, pp. 274–275
:::

A chain complex K has d²=0 and homology H_n=ker d_n/im d_{n+1}; a cochain complex has cohomology H^n=ker d^n/im d^{n−1}. Exactness means all homology vanishes.

### Definition: morphism of complexes {#fc13-cb-u002}

::: {.unit-meta}
`FC13-CB-U002` · Appendix B, pp. 274–275 · after [`FC13-CB-U001`](#fc13-cb-u001)
:::

A morphism f:K→K′ is a degreewise family commuting with differentials and therefore induces maps on homology.

### Definition: chain homotopy and homotopy equivalence {#fc13-cb-u003}

::: {.unit-meta}
`FC13-CB-U003` · Appendix B, pp. 274–275 · after [`FC13-CB-U002`](#fc13-cb-u002)
:::

Morphisms f,g are homotopic if f−g=dh+hd. Homotopic maps induce the same homology map; homotopy-equivalent complexes have isomorphic homology.

### Theorem/construction: long exact homology sequence {#fc13-cb-u004}

::: {.unit-meta}
`FC13-CB-U004` · Appendix B, p. 275 · after [`FC13-CB-U001`](#fc13-cb-u001)
:::

A short exact sequence of complexes 0→K′→K→K″→0 has connecting maps H_n(K″)→H_{n−1}(K′) and yields the standard long exact homology sequence.

### Definition: double complex and total complex {#fc13-cb-u005}

::: {.unit-meta}
`FC13-CB-U005` · Appendix B, pp. 275–276 · after [`FC13-CB-U001`](#fc13-cb-u001)
:::

A double complex has commuting horizontal and vertical differentials squaring to zero. Its total complex uses total degree p+q and differential d=d′+(−1)^p d″.

### Theorem: Theorem B1 {#fc13-cb-u006}

::: {.unit-meta}
`FC13-CB-U006` · Appendix B, p. 276 · after [`FC13-CB-U005`](#fc13-cb-u005)
:::

For a first-quadrant double complex whose vertical homology vanishes above degree zero, total homology is the homology of the degree-zero vertical homology complex; with the symmetric horizontal vanishing, both edge complexes compute the same total homology.

### Theorem: Theorem B2 {#fc13-cb-u007}

::: {.unit-meta}
`FC13-CB-U007` · Appendix B, pp. 276–277 · after [`FC13-CB-U005`](#fc13-cb-u005)
:::

The cohomological analogue of Theorem B1 identifies total cohomology with the appropriate edge cohomology under the corresponding first-quadrant acyclicity hypotheses.

### Definition: projective module {#fc13-cb-u008}

::: {.unit-meta}
`FC13-CB-U008` · Appendix B, p. 277
:::

P is projective if maps P→N lift across every surjection M→N. Projective modules are exactly direct summands of free modules.

### Definition: injective module {#fc13-cb-u009}

::: {.unit-meta}
`FC13-CB-U009` · Appendix B, p. 277
:::

I is injective if maps from submodules extend across injections, the arrow-dual lifting condition to projectivity.

### Theorem: Theorem B3 (Baer criterion) {#fc13-cb-u010}

::: {.unit-meta}
`FC13-CB-U010` · Appendix B, p. 277 · after [`FC13-CB-U009`](#fc13-cb-u009)
:::

An A-module I is injective iff every A-linear map from an ideal a⊆A to I extends to a map A→I.

### Definition/construction: projective resolution {#fc13-cb-u011}

::: {.unit-meta}
`FC13-CB-U011` · Appendix B, pp. 277–278 · after [`FC13-CB-U008`](#fc13-cb-u008)
:::

Every module M has a projective resolution ⋯→P_1→P_0→M→0 built by successive projective surjections; its positive homology vanishes and H_0≅M.

### Corollary: finite free resolutions exist termwise for finite modules over Noetherian rings {#fc13-cb-u012}

::: {.unit-meta}
`FC13-CB-U012` · Appendix B, p. 278 · after [`FC13-C01-U054`](c01.html#fc13-c01-u054), [`FC13-CB-U011`](#fc13-cb-u011)
:::

If A is Noetherian and M finite, one may choose a projective resolution whose terms are finite free modules.

### Definition/construction: injective resolution {#fc13-cb-u013}

::: {.unit-meta}
`FC13-CB-U013` · Appendix B, p. 278 · after [`FC13-CB-U009`](#fc13-cb-u009)
:::

Every module M embeds into an injective resolution 0→M→Q^0→Q^1→⋯ with H^0≅M and H^n=0 for n>0.

### Theorem: comparison theorem for resolutions {#fc13-cb-u014}

::: {.unit-meta}
`FC13-CB-U014` · Appendix B, p. 278 · after [`FC13-CB-U003`](#fc13-cb-u003), [`FC13-CB-U011`](#fc13-cb-u011), [`FC13-CB-U013`](#fc13-cb-u013)
:::

A module map M→N lifts to a chain map between projective resolutions; the lift is unique up to homotopy. Consequently any two projective resolutions are homotopy equivalent, and dually for injective resolutions.

### Definition: Tor functors {#fc13-cb-u015}

::: {.unit-meta}
`FC13-CB-U015` · Appendix B, pp. 278–279 · after [`FC13-CB-U006`](#fc13-cb-u006), [`FC13-CB-U011`](#fc13-cb-u011)
:::

For projective resolutions P of M and Q of N, Tor_n^A(M,N) is the common homology of P⊗N, M⊗Q, and the associated double complex; it is independent of the chosen resolutions.

### Theorem: basic properties of Tor {#fc13-cb-u016}

::: {.unit-meta}
`FC13-CB-U016` · Appendix B, p. 279 · after [`FC13-CA-U009`](ca.html#fc13-ca-u009), [`FC13-CA-U021`](ca.html#fc13-ca-u021), [`FC13-CB-U015`](#fc13-cb-u015)
:::

Tor_0(M,N)=M⊗N; Tor_n vanishes for n>0 when one entry is flat; Tor is symmetric and covariant in both entries, sends short exact sequences to long exact sequences, and commutes with direct limits in the second entry.

### Definition: Ext functors {#fc13-cb-u017}

::: {.unit-meta}
`FC13-CB-U017` · Appendix B, pp. 279–280 · after [`FC13-CB-U007`](#fc13-cb-u007), [`FC13-CB-U011`](#fc13-cb-u011), [`FC13-CB-U013`](#fc13-cb-u013)
:::

Using a projective resolution of M or injective resolution of N, Ext_A^n(M,N) is the common cohomology computed from Hom(P,N) or Hom(M,Q); it is independent of resolutions.

### Theorem: basic properties of Ext {#fc13-cb-u018}

::: {.unit-meta}
`FC13-CB-U018` · Appendix B, pp. 279–280 · after [`FC13-CB-U017`](#fc13-cb-u017)
:::

Ext^0(M,N)=Hom(M,N); higher Ext vanishes for projective first or injective second arguments; Ext is contravariant in the first and covariant in the second, with long exact sequences in either variable; projectivity/injectivity are characterized by Ext^1 vanishing against all modules.

### Definition: projective and injective dimension {#fc13-cb-u019}

::: {.unit-meta}
`FC13-CB-U019` · Appendix B, p. 280 · after [`FC13-CB-U011`](#fc13-cb-u011), [`FC13-CB-U013`](#fc13-cb-u013)
:::

projdim M is the least length of a projective resolution, or ∞; injdim is defined dually. Dimension zero is equivalent to projectivity/injectivity.

### Theorem: Ext characterization of homological dimension {#fc13-cb-u020}

::: {.unit-meta}
`FC13-CB-U020` · Appendix B, p. 280 · after [`FC13-CB-U018`](#fc13-cb-u018), [`FC13-CB-U019`](#fc13-cb-u019)
:::

projdim M≤d iff Ext_A^{d+1}(M,N)=0 for every N; dually injdim N≤d iff Ext_A^{d+1}(M,N)=0 for every M.

### Definition/theorem: derived functors {#fc13-cb-u021}

::: {.unit-meta}
`FC13-CB-U021` · Appendix B, pp. 280–281 · after [`FC13-CB-U011`](#fc13-cb-u011), [`FC13-CB-U013`](#fc13-cb-u013), [`FC13-CB-U017`](#fc13-cb-u017)
:::

Right derived functors of a left-exact functor are obtained from resolutions and are characterized by degree-zero recovery, vanishing on projectives/injectives as appropriate, and natural long exact sequences; left derived functors are defined dually for right-exact functors.

### Definition: essential extension {#fc13-cb-u022}

::: {.unit-meta}
`FC13-CB-U022` · Appendix B, p. 281
:::

An extension M⊆L is essential if every nonzero submodule of L meets M nontrivially; equivalently every nonzero x∈L has a nonzero scalar multiple in M.

### Theorem: Theorem B4 {#fc13-cb-u023}

::: {.unit-meta}
`FC13-CB-U023` · Appendix B, p. 281 · after [`FC13-CB-U009`](#fc13-cb-u009), [`FC13-CB-U022`](#fc13-cb-u022)
:::

An A-module M is injective iff it has no proper essential extension.

### Definition/construction: injective hull {#fc13-cb-u024}

::: {.unit-meta}
`FC13-CB-U024` · Appendix B, p. 281 · after [`FC13-CB-U023`](#fc13-cb-u023)
:::

An injective hull E(M) is an injective essential extension of M. It exists by taking a maximal essential extension inside an injective overmodule and is unique up to an isomorphism fixing M.

### Definition/construction: minimal injective resolution {#fc13-cb-u025}

::: {.unit-meta}
`FC13-CB-U025` · Appendix B, p. 281 · after [`FC13-CB-U024`](#fc13-cb-u024)
:::

Iteratively taking injective hulls of successive cokernels gives the minimal injective resolution of a module.

### Theorem: five lemma {#fc13-cb-u026}

::: {.unit-meta}
`FC13-CB-U026` · Appendix B, pp. 281–282 · after [`FC13-CB-U004`](#fc13-cb-u004)
:::

In a commutative diagram of exact five-term rows, the standard injectivity and surjectivity hypotheses on the surrounding vertical maps imply injectivity or surjectivity of the middle map.

### Theorem: snake lemma {#fc13-cb-u027}

::: {.unit-meta}
`FC13-CB-U027` · Appendix B, p. 282 · after [`FC13-CB-U004`](#fc13-cb-u004)
:::

A commutative diagram with exact rows 0→A→B→C→0 and 0→A′→B′→C′→0 induces the standard exact sequence from kernels through cokernels with a connecting map Ker γ→Coker α.

### Construction: tensor product of complexes {#fc13-cb-u028}

::: {.unit-meta}
`FC13-CB-U028` · Appendix B, p. 282 · after [`FC13-CA-U004`](ca.html#fc13-ca-u004), [`FC13-CB-U005`](#fc13-cb-u005)
:::

For complexes K,L, (K⊗L)_n=⊕_{p+q=n}K_p⊗L_q with d(x⊗y)=dx⊗y+(−1)^p x⊗dy. There are graded-symmetry and associativity isomorphisms; finite iterated tensor products are therefore well-defined.

