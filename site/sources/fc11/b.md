---
title: "FC11 — Peters–Sterk, Symmetric and Quadratic Forms (June 2024)"
---

FC11 — Peters & Sterk, *Symmetric and Quadratic Forms*.

This chapter contains 27 definitions, 4 theorems, 1 proposition, 3 lemmas, 5 examples, 5 constructions, 1 remark and 1 criterion.

Nobody has checked this chapter against Lean yet, so the statements below
say nothing about whether they are formalized.

### Definition / construction {#fc11-b-u001}

::: {.unit-meta}
`FC11-B-U001` · Appendix B, source L11478
:::

A Hermitian metric on a complex manifold is equivalently encoded by its real $(1,1)$-form; it is Kähler when this form is closed.

### Definition / construction / notation {#fc11-b-u002}

::: {.unit-meta}
`FC11-B-U002` · Appendix B, source L11484-L11488
:::

The metric is K¨ahler if $\kappa$ is a closed form, which then is called the associated K¨ahler form. So its class is a (real) cohomology class of type $( 1 , 1 )$ . A manifold admitting a K¨ahler metric is called a K¨ahler manifold . Prominent examples are smooth complex projective varieties, and complex tori. Using the K¨ahler form $\kappa$ , we shall make use of a general positivity condition related to complex submanifolds $Y \subset X$ , namely the inequality $$ \int _ { Y } \underbrace { \kappa \wedge \cdot \cdot \cdot \wedge \kappa } _ { k } > 0 , \quad k = \dim Y . $$

### Definition / construction / notation {#fc11-b-u003}

::: {.unit-meta}
`FC11-B-U003` · Appendix B, source L11490-L11494
:::

We shall also be using numerical invariants defined for any compact complex manifold $X$ by way of the sheaf $\Omega _ { X } ^ { p }$ of holomorphic $p$ -forms on $X$ : $$ H ^ { p , q } ( X ) = H ^ { q } ( X , \Omega _ { X } ^ { p } ) , \quad h ^ { p , q } ( X ) = \dim H ^ { q } ( X , \Omega _ { X } ^ { p } ) \mathrm { ~ ( t h e ~ H o d g e ~ n u m b e r s ) } . $$

### Definition / construction {#fc11-b-u004}

::: {.unit-meta}
`FC11-B-U004` · Appendix B, source L11496-L11500 · after [`FC11-B-U002`](#fc11-b-u002)
:::

For a compact Kähler manifold, $H^{p,q}(X)$ is the subspace of complex de Rham cohomology represented by closed forms of type $(p,q)$, and the Hodge decomposition is $H^k(X,\mathbf C)=\bigoplus_{p+q=k}H^{p,q}(X)$ with $\overline{H^{p,q}(X)}=H^{q,p}(X)$.

### Definition / construction {#fc11-b-u005}

::: {.unit-meta}
`FC11-B-U005` · Appendix B, source L11516
:::

The intersection form of a compact complex surface is the cup-product form on $H^2(X,\mathbf Z)/\mathrm{tors}$; its signature is $(b^+,b^-)$ and its index is $b^+-b^-$.

### Theorem B.2.1 {#fc11-b-u006}

::: {.unit-meta}
`FC11-B-U006` · Appendix B, source L11524-L11528
:::

Theorem B.2.1 (Index theorem – special case). For a compact differentiable 4- manifold $X$ admitting a complex structure, the index $\tau ( X )$ satisfies $$ \tau ( X ) = { \frac { 1 } { 3 } } ( c _ { 1 } ^ { 2 } ( X ) - 2 c _ { 2 } ( X ) ) . $$

### Remark B.2.2 {#fc11-b-u007}

::: {.unit-meta}
`FC11-B-U007` · Appendix B, source L11530
:::

Remark B.2.2. The Chern class $c _ { 1 } ( X ) \in H ^ { 2 } ( X , \mathbb { Z } )$ is also represented by the class of the inverse of the canonical line bundle2 $K _ { X }$ . In particular, for a compact complex surface $X$ one has $c _ { 1 } ^ { 2 } ( X ) = K _ { X } \cdot K _ { X }$ .

### Construction / comparison {#fc11-b-u008}

::: {.unit-meta}
`FC11-B-U008` · Appendix B, source L11532-L11536 · after [`FC11-B-U004`](#fc11-b-u004)
:::

For a compact Kähler surface, the Hodge decompositions are $H^1(X,\mathbf C)=H^{1,0}\oplus H^{0,1}$ and $H^2(X,\mathbf C)=H^{2,0}\oplus H^{1,1}\oplus H^{0,2}$, with complex conjugation interchanging $H^{p,q}$ and $H^{q,p}$.

### Theorem B.2.3 {#fc11-b-u009}

::: {.unit-meta}
`FC11-B-U009` · Appendix B, source L11540 · after [`FC11-B-U005`](#fc11-b-u005)
:::

Theorem B.2.3 (Hodge Index Theorem). For a K¨ahler surface $X$ the intersection form gives the real vector space $H ^ { 1 , 1 } ( X ) _ { \mathbb { R } } = H ^ { 1 , 1 } ( X ) \cap H ^ { 2 } ( X , \mathbb { R } )$ the structure of $a$ hyperbolic space, i.e., the signature of the restriction of the intersection form on this space is $( 1 , h ^ { \scriptscriptstyle 1 , 1 } ( X ) - 1 )$ .

### Definition / construction / notation {#fc11-b-u010}

::: {.unit-meta}
`FC11-B-U010` · Appendix B, source L11542 · after [`FC11-B-U009`](#fc11-b-u009)
:::

The considerations of Example 16.1 apply to $H^{1,1}(X)_{\mathbb{R}}$: the light cone $\{x \in H^{1,1}(X)_{\mathbb{R}} \mid x \cdot x > 0\}$ has two connected components, and the positive cone is the one containing the Kähler classes, which form a convex cone and so lie in a single component. That component is denoted $$ \mathsf{C}_{X} = \text{the component of } \{x \in H^{1,1}(X)_{\mathbb{R}} \mid x \cdot x > 0\} \text{ containing the Kähler classes}, $$ and the Kähler classes span a subcone of it, the Kähler cone.

### Definition / construction {#fc11-b-u011}

::: {.unit-meta}
`FC11-B-U011` · Appendix B, source L11542-L11546
:::

The positive cone $C_X$ is the component of $\{x\in H^{1,1}(X)_\mathbf R:x^2>0\}$ containing the Kähler classes; those classes themselves span the Kähler cone inside $C_X$.

### Construction / comparison {#fc11-b-u012}

::: {.unit-meta}
`FC11-B-U012` · Appendix B, source L11548-L11552
:::

Noether's formula for a compact complex surface is $\chi(\mathcal O_X)=1-q(X)+p_g(X)=\frac1{12}(c_1^2(X)+c_2(X))$.

### Construction / comparison {#fc11-b-u013}

::: {.unit-meta}
`FC11-B-U013` · Appendix B, source L11554-L11558 · after [`FC11-B-U003`](#fc11-b-u003)
:::

For a compact Kähler surface, the Hodge numbers are topological invariants and the signature satisfies $b^+=2p_g+1$, $b^-=h^{1,1}-1$, hence $\tau=2p_g+2-h^{1,1}$.

### Lemma B.2.4 {#fc11-b-u014}

::: {.unit-meta}
`FC11-B-U014` · Appendix B, source L11568
:::

Lemma B.2.4. Let $X$ be a K¨ahler surface. If $S _ { X }$ is definite, $S _ { X } \simeq \langle 1 \rangle$ .

### Construction / comparison {#fc11-b-u015}

::: {.unit-meta}
`FC11-B-U015` · Appendix B, source L11570 · after [`FC11-B-U005`](#fc11-b-u005)
:::

For compact Kähler surfaces, the integral intersection form is determined by its parity and signature.

### Definition / construction / notation {#fc11-b-u016}

::: {.unit-meta}
`FC11-B-U016` · Appendix B, source L11572
:::

Invariants related to divisors. A divisor $D$ on a surface $X$ defines a cohomology class $[ D ] \in H ^ { 2 } ( X , \mathbb { Z } )$ . Divisors with the same class are said to be homologically equivalent and so the group of divisors on $X$ modulo homological equivalence, by definition the N´eron–Severi group $\mathsf { N S } ( X )$ , embeds in $H ^ { 2 } ( X , \mathbb { Z } )$ . Its rank is the Picard number $\rho ( X )$ of $X$ . We shall identify NS( $X$ ) with its image in $H ^ { 2 } ( X , \mathbb { Z } )$ . The resulting cohomology classes are the algebraic classes. By the Lefschetz $( 1 , 1 )$ - theorem these are precisely the classes of Hodge type $( 1 , 1 )$ :

### Proposition B.2.5 {#fc11-b-u017}

::: {.unit-meta}
`FC11-B-U017` · Appendix B, source L11574
:::

Proposition B.2.5. Let $X$ be a complex surface. Then $\mathsf { N S } ( X )$ is the subgroup of $H ^ { 2 } ( X , \mathbb { Z } )$ consisting of classes of type $( 1 , 1 )$ .

### Definition / construction {#fc11-b-u018}

::: {.unit-meta}
`FC11-B-U018` · Appendix B, source L11576 · after [`FC11-B-U005`](#fc11-b-u005)
:::

The intersection form gives $NS(X)/\mathrm{tors}$ its integral Néron--Severi (Picard) lattice structure; when a divisor class has positive square, the surface is projective and this lattice is Lorentzian.

### Theorem B.2.6 {#fc11-b-u019}

::: {.unit-meta}
`FC11-B-U019` · Appendix B, source L11578 · after [`FC11-B-U016`](#fc11-b-u016)
:::

Theorem B.2.6 (Algebraic Index Theorem [15, IV, Cor. 2.16], [19, p. 8]). Let $X$ be a smooth complex projective surface. The intersection pairing restricts non-degenerately to the N´eron–Severi group NS(??) and has signature $( 1 , \rho - 1 )$ . In particularly, if $D$ is a divisor with $D \cdot D > 0$ , any class in $\mathsf { N S } ( X )$ orthogonal to $D$ has negative self-intersection.

### Definition / construction {#fc11-b-u020}

::: {.unit-meta}
`FC11-B-U020` · Appendix B, source L11580-L11586
:::

For an irreducible curve $D$ on a smooth projective surface, the adjunction/genus formula is $2p_a(D)-2=K_X\cdot D+D^2$, with $p_a(D)=g(\widetilde D)+\delta$; $p_a(D)$ is the arithmetic genus and $\delta\ge0$ is the defect, vanishing exactly when $D$ is smooth.

### Definition / construction {#fc11-b-u021}

::: {.unit-meta}
`FC11-B-U021` · Appendix B, source L11588-L11592
:::

The Néron--Severi lattice is the largest primitive integral sublattice of $H^2(X,\mathbf Z)/\mathrm{tors}$ whose complexification lies in $H^{1,1}(X)$.

### Definition / construction {#fc11-b-u022}

::: {.unit-meta}
`FC11-B-U022` · Appendix B, source L11594-L11598
:::

The transcendental lattice $\operatorname{Trs}(X)$ is the smallest primitive sublattice $T\subset H^2(X,\mathbf Z)/\mathrm{tors}$ such that $H^{2,0}(X)\subset T\otimes\mathbf C$; it is a sub-Hodge structure.

### Lemma B.2.7 {#fc11-b-u023}

::: {.unit-meta}
`FC11-B-U023` · Appendix B, source L11602 · after [`FC11-B-U016`](#fc11-b-u016)
:::

Lemma B.2.7. Let $X$ be a compact K¨ahler surface such that its N´eron–Severi lattice is non-degenerate (e.g. if $X$ is projective), then Trs(??) and NS(??)/torsion are orthogonal complements of each other in $\mathsf { H } _ { X }$ .

### Definition / construction / notation {#fc11-b-u024}

::: {.unit-meta}
`FC11-B-U024` · Appendix B, source L11606
:::

1. The most basic examples of surfaces are $\mathbb { P } ^ { 2 }$ and $\mathbb { P } ^ { 1 } \times \mathbb { P } ^ { 1 }$ . These are birationally equivalent to each other (see e.g. Example B.5.1) and any surface birational to $\mathbb { P } ^ { 2 }$ is called a rational surface. Apart from the just mentioned surfaces also the Hirzebruch surfaces $F _ { n } , n \in \mathbb { N }$ , belong to this class. The surface $F _ { n }$ is the total space of the $\mathbb { P } ^ { 1 }$ -bundle over $\mathbb { P } ^ { 1 }$ possessing a unique section $C _ { n }$ with self-intersection $- n$ . The Hirzebruch surface $F _ { 0 }$ is just $\mathbb { P } ^ { 1 } \times \mathbb { P } ^ { 1 }$ and only $\pmb { F } _ { 1 }$ has an exceptional curve. These surfaces are all simply connected and $b _ { 2 } ( \mathbb { P } ^ { 2 } ) = h ^ { \scriptscriptstyle \mathrm { 1 , 1 } } ( \mathbb { P } ^ { \scriptscriptstyle 2 } ) = 1$ while $b _ { 2 } ( { \pmb F } _ { n } ) = h ^ { 1 , 1 } ( { \pmb F } _ { n } ) = 2$ .

### Example / comparison {#fc11-b-u025}

::: {.unit-meta}
`FC11-B-U025` · Appendix B, source L11614
:::

A ruled surface of genus $g$ is a $\mathbf P^1$-bundle over a curve of genus $g$; its rank-two intersection lattice is isometric to $U$ or to $\langle1\rangle\oplus\langle-1\rangle$.

### Example / comparison {#fc11-b-u026}

::: {.unit-meta}
`FC11-B-U026` · Appendix B, source L11616
:::

A smooth degree-$d$ surface in $\mathbf P^3$ is simply connected with $b_2=d^3-4d^2+6d-2$; degree $2$ gives a quadric and degree $4$ gives a K3 surface.

### Example / comparison {#fc11-b-u027}

::: {.unit-meta}
`FC11-B-U027` · Appendix B, source L11620-L11625
:::

A K3 surface is a simply connected surface with trivial canonical bundle; standard examples include Kummer surfaces, smooth quartics in $\mathbf P^3$, and smooth complete intersections of three quadrics in $\mathbf P^5$.

### Definition / construction {#fc11-b-u028}

::: {.unit-meta}
`FC11-B-U028` · Appendix B, source L11656
:::

An Enriques surface is a surface with $p_g=b_1=0$ and canonical bundle of order $2$.

### Example / comparison {#fc11-b-u029}

::: {.unit-meta}
`FC11-B-U029` · Appendix B, source L11658-L11664
:::

Example ( [19, 4.18]). Let $( x _ { 1 } : y _ { 1 } : z _ { 1 } : x _ { 2 } : y _ { 2 } : z _ { 2 } )$ be projective coordinates in $\mathbb { P } ^ { 5 }$ and define $$ \iota ( x _ { 1 } : y _ { 1 } : z _ { 1 } : x _ { 2 } : , y _ { 2 } : z _ { 2 } ) = ( x _ { 1 } : y _ { 1 } : z _ { 1 } : - x _ { 2 } : - y _ { 2 } ) $$ An invariant quadric is of the form $Q ^ { \prime } ( x _ { 1 } , y _ { 1 } , z _ { 1 } ) + Q ^ { \prime \prime } ( x _ { 2 } , y _ { 2 } , z _ { 2 } )$ . For a generic choice of three such quadrics, the intersection is a smooth surface and the calculation rules for complete intersections tell us that this is a K3 surface. Note that the fixed point set of $\iota$ consists of the two planes $x _ { i } = y _ { i } = z _ { i } = 0$ , $i = 1 , 2$ , and three invariant quadrics cut out three conics on each of these planes and so their intersection is empty for a generic choice of the quadrics. If this is the case, the involution acts on the intersection without fixed points. By what we just said, the quotient is an Enriques surface. All Enriques surfaces can be shown to either arise in this way or they are, in a technical sense, “limits” of such surfaces; in particular they are all algebraic.

### Definition / construction / notation {#fc11-b-u030}

::: {.unit-meta}
`FC11-B-U030` · Appendix B, source L11668-L11672 · after [`FC11-B-U005`](#fc11-b-u005)
:::

Since intersection form on a surface $X$ by definition comes from the wedge product of (closed) forms and taking the wedge of two type $( 2 , 0 )$ -classes is zero while for a single class $\omega \neq 0$ of type $( 2 , 0 )$ the product ${ \frac { 1 } { 4 } } \omega \wedge \bar { \omega }$ is the volume form, the Riemann bilinear relations result: $$ \begin{array} { l l } { { S _ { X } ( u , u ^ { \prime } ) = 0 , } } & { { u , u ^ { \prime } \in H ^ { 2 , 0 } ( X ) } } \\ { { S _ { X } ( u , \bar { u } ) > 0 , } } & { { u \in H ^ { 2 , 0 } ( X ) , u \not = 0 . } } \end{array} $$

### Definition B.4.1 {#fc11-b-u031}

::: {.unit-meta}
`FC11-B-U031` · Appendix B, source L11690-L11704
:::

Definition B.4.1. 1. A Hodge structure of weight 2 on a free $\mathbb { Z }$ -module $L$ of finite rank consists of a decomposition $$ { \cal L } _ { \mathbb { C } } = { \cal L } ^ { 2 , 0 } \oplus { \cal L } ^ { 1 , 1 } \oplus { \cal L } ^ { 0 , 2 } , $$ such that $L ^ { 2 , 0 }$ is the complex conjugate of $L ^ { 0 , 2 }$ and $L ^ { 1 , 1 }$ is self-conjugate. This implies that there exist subspaces $L$ and $L ^ { \prime \prime }$ of $L _ { \mathbb { R } }$ such that $$ { \cal L } _ { \mathbb { R } } = { \cal L } ^ { \prime } \oplus { \cal L } ^ { \prime \prime } , \quad { \cal L } _ { \mathbb { C } } ^ { \prime } = { \cal L } ^ { 1 , 1 } , { \cal L } _ { \mathbb { C } } ^ { \prime \prime } = { \cal L } ^ { 2 , 0 } + { \cal L } ^ { 0 , 2 } . $$ 2. If $^ { b }$ is a non-degenerate integral form on $L$ we say that $L$ is polarized by $b$ , if the two Riemann bilinear relations (B.8) and (B.9) hold. 5 3. A polarized weight 2 Hodge structure is said to be of $\kappa 3$ type if $\dim L ^ { 2 , 0 } = 1$ and $L ^ { \prime } \subset L _ { \mathbb { R } }$ is of Lorentzian type, that is, has signature $( 1 , \mathrm { d i m } L ^ { \prime } - 1 )$ .

### Definition / construction {#fc11-b-u032}

::: {.unit-meta}
`FC11-B-U032` · Appendix B, source L11706-L11716 · after [`FC11-B-U031`](#fc11-b-u031)
:::

Polarized weight-$2$ Hodge structures on $(L,b)$ with fixed $h^{2,0}$ are parametrized by the period domain of $b_\mathbf C$-isotropic $h^{2,0}$-planes $P$ satisfying $b_\mathbf C(u,\bar u)>0$ for $u\ne0$; for K3 type these are isotropic positive projective lines.

### Construction / comparison {#fc11-b-u033}

::: {.unit-meta}
`FC11-B-U033` · Appendix B, source L11718-L11724 · after [`FC11-B-U032`](#fc11-b-u032)
:::

The period domain is the homogeneous space $O(r_+,r_-)/(SO(r_+-1)\times O(1,r_-))$, equivalently the corresponding special-orthogonal quotient, and it is connected.

### Definition / construction {#fc11-b-u034}

::: {.unit-meta}
`FC11-B-U034` · Appendix B, source L11726 · after [`FC11-B-U031`](#fc11-b-u031)
:::

A marking $\varphi:H_X\xrightarrow{\sim}L$ transports the polarized Hodge structure to $L$ and determines its period point in $D(L)$ by the subspace $\varphi(H^{2,0}(X))\subset L_\mathbf C$.

### Definition / construction / notation {#fc11-b-u035}

::: {.unit-meta}
`FC11-B-U035` · Appendix B, source L11730-L11734
:::

Minimal models. Classification of surfaces begins with a reduction to minimal surfaces. To explain this, we need the concept of a $( - 1 )$ -curve6 $E$ on a complex algebraic surface; by definition $E$ is a smooth rational curve with $E \cdot E = - 1$ . Such a curve arises under the process of blowing up a surface at a point. To describe this, we assume that we have chosen coordinates $( u , v )$ in an open subset $U$ on the surface such that the point $p$ is the origin. Now consider $$ \widetilde { U } : = \{ ( ( u , v ) , ( U : V ) ) , \in U \times \mathbb { P } ^ { 1 } \mid ( u : v ) = ( U : V ) \} $$

### Example / comparison {#fc11-b-u036}

::: {.unit-meta}
`FC11-B-U036` · Appendix B, source L11738
:::

Example B.5.1. Let $p , q \in \mathbb { P } ^ { 2 }$ be two distinct points and let $L$ be the line connecting $p$ and $q$ . Blowing up $\mathbb { P } ^ { 2 }$ in $p$ and $q$ transforms the line $L$ in an exceptional curve.7 Blowing down this curve yields $\mathbb { P } ^ { 1 } \times \mathbb { P } ^ { 1 }$ and this procedure shows that $\mathbb { P } ^ { 2 }$ and $\mathbb { P } ^ { 1 } \times \mathbb { P } ^ { 1 }$ are two distinct minimal models within the same birationality class.

### Lemma B.5.2 {#fc11-b-u037}

::: {.unit-meta}
`FC11-B-U037` · Appendix B, source L11742-L11746
:::

Lemma B.5.2. Let $X$ be a compact complex surface, $\sigma : { \tilde { X } } X$ the blow-up in a point $p$ and $E = \sigma ^ { - 1 } p$ the exceptional curve. Recalling (B.2) for the notation, we have the following cohomological results: 1. $\sigma ^ { * } : H ^ { 2 } ( X , \mathbb { Z } ) \to H ^ { 2 } ( { \widetilde { X } } , \mathbb { Z } )$ is an injection; 2. ${ \mathsf { H } } _ { \widetilde { X } } \simeq { \mathsf { H } } _ { X } \oplus \langle - 1 \rangle$ , where the second summand is spanned by the class of $E$ .

### Definition / construction / notation {#fc11-b-u038}

::: {.unit-meta}
`FC11-B-U038` · Appendix B, source L11748-L11752
:::

Intermezzo on the Kodaira dimension. In this subsection we broaden our scope and change notation accordingly: $X$ stands for a compact K¨ahler variety and $L$ for a holomorphic line bundle on $X$ . Assuming $L$ has holomorphic sections, a choice of a basis $\{ s _ { 0 } , s _ { 1 } , \ldots , s _ { N } \}$ for the vector space of holomorphic sections defines the meromorphic map $$ \begin{array} { r l } & { f _ { L } : X \to \mathbb { P } ^ { N } } \\ & { \qquad x \mapsto ( s _ { 0 } ( x ) : s _ { 1 } ( x ) : \cdot \cdot \cdot : s _ { N } ( x s ) ) . } \end{array} $$

### Definition / construction / notation {#fc11-b-u039}

::: {.unit-meta}
`FC11-B-U039` · Appendix B, source L11754 · after [`FC11-B-U038`](#fc11-b-u038)
:::

This is not defined at points where all sections of $L$ vanish.

### Definition / construction / notation {#fc11-b-u040}

::: {.unit-meta}
`FC11-B-U040` · Appendix B, source L11756
:::

If $f _ { L }$ is everywhere defined and is an embedding, $L$ is called very ample and likewise for a divisor $D$ with $L = \odot _ { X } ( D )$ . Lastly, $L$ (or $D$ ) is called ample if for some positive $m$ the bundle $L ^ { \otimes m }$ (or the divisor $m D$ ) is very ample. This implies that $L \cdot C > 0$ for all curves $C \subset X$ , since $L \cdot ( m C )$ is the degree of the curve $c$ as embedded in $\mathbb { P } ^ { N }$ by means of $f _ { L ^ { \otimes m } }$ . Similarly, if $X$ has dimension $d$ , we have $L \cdots L > 0$ . We conclude that if $d = 2$ , for $D$ ample, we have $D \cdot C > 0$ and $D ^ { 2 } > 0$ . The converse is the Kleiman criterion: a divisor $D$ on a surface with $D^{2} > 0$ and $D \cdot C > 0$ for every curve $C$ is ample.

### Criterion / construction {#fc11-b-u041}

::: {.unit-meta}
`FC11-B-U041` · Appendix B, source L11758
:::

Kleiman's criterion in the stated surface form says that a divisor with positive self-intersection and positive intersection with every curve is ample.

### Definition / construction / notation {#fc11-b-u042}

::: {.unit-meta}
`FC11-B-U042` · Appendix B, source L11760-L11764
:::

The canonical bundle $K _ { X }$ of $X$ is the line bundle associated to the sheaf $\Omega _ { X } ^ { n }$ of holomorphic $n$ -forms where $n = \dim X$ . A divisor whose line bundle is $K _ { X }$ is called a canonical divisor, also denoted by $K _ { X }$ . The $m$ -th tensor power of $K _ { X }$ is the $m$ -th pluricanonical bundle and we set $$ P _ { m } ( X ) = h ^ { 0 } ( K _ { X } ^ { \otimes m } ) , \quad \mathrm { t h e } m { \cdot } \mathrm { t h p l u r i g e n u s ~ o f } X . $$

### Definition B.5.3 {#fc11-b-u043}

::: {.unit-meta}
`FC11-B-U043` · Appendix B, source L11768-L11772
:::

Definition B.5.3. Let $X$ be a compact complex variety. The Kodaira dimension of $X$ is the number $$ \begin{array} { r } { \kappa ( X ) = \left\{ \begin{array} { l l } { - \infty } & { \mathrm { ~ i f ~ } P _ { m } ( X ) = 0 \mathrm { ~ f o r ~ a l l ~ } m \in \mathbb N } \\ { \operatorname* { m a x } _ { m \in \mathbb Z _ { > 0 } } \dim f _ { K _ { X } ^ { \otimes m } } ( X ) } & { \mathrm { ~ o t h e r w i s e } . } \end{array} \right. } \end{array} $$

### Definition / construction {#fc11-b-u044}

::: {.unit-meta}
`FC11-B-U044` · Appendix B, source L11776
:::

A bielliptic surface is a surface with $b_2=2$ admitting a holomorphic locally trivial elliptic-curve bundle over an elliptic curve.

### Definition / construction {#fc11-b-u045}

::: {.unit-meta}
`FC11-B-U045` · Appendix B, source L11778 · after [`FC11-B-U043`](#fc11-b-u043)
:::

A properly elliptic surface is a surface of Kodaira dimension $1$ admitting an elliptic fibration over a curve.

### Definition / construction {#fc11-b-u046}

::: {.unit-meta}
`FC11-B-U046` · Appendix B, source L11780 · after [`FC11-B-U043`](#fc11-b-u043)
:::

A surface of general type is a surface with Kodaira dimension $2$; its minimal model is characterized here as non-rational with $c_1^2>0$.

### Theorem B.5.4 {#fc11-b-u047}

::: {.unit-meta}
`FC11-B-U047` · Appendix B, source L11784 · after [`FC11-B-U043`](#fc11-b-u043)
:::

Theorem B.5.4 (Enriques--Kodaira classification). Every minimal compact Kähler surface belongs to exactly one class, ordered by Kodaira dimension: minimal rational or ruled surfaces ($\kappa=-\infty$); two-dimensional tori, K3, Enriques, or bielliptic surfaces ($\kappa=0$); minimal properly elliptic surfaces ($\kappa=1$); or surfaces of general type ($\kappa=2$).

