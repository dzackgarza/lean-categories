---
title: "FC11 — Peters–Sterk, Symmetric and Quadratic Forms (June 2024)"
---

FC11 — Peters & Sterk, *Symmetric and Quadratic Forms* — block `FC11-C`.

This chapter is enumerated but not yet swept against Lean: the statements
below carry no routing verdict.

### Definition / construction / notation {#fc11-c-u001}

::: {.unit-meta}
`FC11-C-U001` · Appendix C, source L11798
:::

For a symmetric form $b$ on an $R$-module $V$, the correlation map $b_V:V\to V^*$ sends $x$ to $[y\mapsto b(x,y)]$; non-degeneracy means injectivity and unimodularity means bijectivity.

### Lemma C.1.1 {#fc11-c-u002}

::: {.unit-meta}
`FC11-C-U002` · Appendix C, source L11802
:::

Lemma C.1.1. Let $\{ w _ { 1 } , \ldots , w _ { r } \}$ be a basis of $W$ . Then $\beta _ { W }$ is surjective if and only if there exists vectors $v _ { 1 } , \dotsc , v _ { r } \in V$ with $b ( w _ { i } , v _ { j } ) = \delta _ { i j }$ . If $\beta _ { W } ( Z ) = W ^ { * }$ for some submodule $Z \subset W$ , then we may assume that the vectors $v _ { i }$ belong to $Z$ .

### Definition / construction / notation {#fc11-c-u003}

::: {.unit-meta}
`FC11-C-U003` · Appendix C, source L11804
:::

A quadratic form $q$ on $V$ is non-degenerate precisely if its polar form $b _ { q }$ is non-degenerate. Recall also that any vector $x \ \in \ V$ with $q ( x )$ a unit defines a reflection $\sigma _ { x } : V \to V$ given by $y \mapsto y - b _ { q } ( x , y ) q ( x ) ^ { - 1 } x$ . The quadratic form $q$ on an $R$ -module $V$ induces the $k$ -valued quadratic form $\overline { { q } }$ on ${ \overline { { V } } } = V \otimes _ { R } k = V / { \mathfrak { m } } V$ defined by $\overline { { { q } } } ( \overline { { { x } } } ) = q ( x )$ mod $\mathbf { m }$ and $q$ is unimodular if and only if the form $\overline { { q } }$ is unimodular (see $\ S$ 6.3.B, Example 6).

### Proposition C.1.2 {#fc11-c-u004}

::: {.unit-meta}
`FC11-C-U004` · Appendix C, source L11806-L11826 · after [`FC11-C07-U015`](c07.html#fc11-c07-u015)
:::

Proposition C.1.2. Let $( V , q )$ be a quadratic inner product space over $R$ of finite rank, and $W , W ^ { \prime } , Z$ submodules. Let $W , W ^ { \prime }$ be free and assume that $$ \beta _ { W } ( Z ) = W ^ { \ast } , \quad \beta _ { W ^ { \prime } } ( Z ) = W ^ { \prime \ast } . $$ Suppose $t : W \stackrel { \simeq } { \to } W ^ { \prime }$ is an isometry such that $$ t ( x ) - x \in Z \ f o r \ a l l \ x \in W . $$ Then ?? extends to an isometry $\tilde { t } : V \ \stackrel { \sim } { \to } \ V$ such that $\tilde { t } \ =$ id on the orthogonal complement of $Z$ . Moreover, $\tilde { t }$ is a product of reflections in vectors of $Z$ if we are in one of the following cases: $$ \begin{array} { r l } { k \neq \mathbb { F } _ { 2 } \quad } & { a n d \overline { { q } } ( \overline { { Z } } ) \neq 0 , } \\ { k = \mathbb { F } _ { 2 } \quad } & { a n d \overline { { q } } ( \overline { { Z } } ^ { \perp } ) \neq 0 . } \end{array} $$ Taking $Z = V$ gives an unconditional extension of $t$ to $V$ which generalizes Corollary 7.2.8:

### Corollary C.1.3 {#fc11-c-u005}

::: {.unit-meta}
`FC11-C-U005` · Appendix C, source L11828
:::

Corollary C.1.3 (Witt’s extension theorem over local rings). Let $( V , q )$ be a quadratic inner product space over $R$ of finite rank, ??, ??′ primitive free submodules such that $\beta _ { W }$ and $\beta _ { W ^ { \prime } }$ are surjective (this is in particular the case for unimodular submodules $W$ and $W ^ { \prime }$ ) and let $t : W \to W ^ { \prime }$ be an isometry. Then ?? extends to an isometry of $V$ . If $k \neq \mathbb { F } _ { 2 }$ , then this extension is a product of hyperplane reflections.

### Remark: Remark {#fc11-c-u006}

::: {.unit-meta}
`FC11-C-U006` · Appendix C, source L11830-L11833 · after [`FC11-C07-U013`](c07.html#fc11-c07-u013)
:::

Remark. 1. As we have observed (see Remark 7.2.9.1), Witt’s extension theorem is equivalent to Witt’s cancelation theorem 7.2.7. The proof of this does not depend on 2 being invertible or not, and so Witt’s cancelation theorem likewise holds over any local ring. 2. We may take $W \ = \ W ^ { \prime }$ which implies that in case $k \neq \mathbb { F } _ { 2 }$ , every isometry is a product of hyperplane reflections. Below we discuss the case $k = \mathbb { F } _ { 2 }$ . See Theorem C.1.4.

### Theorem C.1.4 {#fc11-c-u007}

::: {.unit-meta}
`FC11-C-U007` · Appendix C, source L11924-L11925
:::

Theorem C.1.4 (Cartan–Dieudonn´e over local rings). Every isometry of a quadratic inner product space $( V , q )$ over a local ring $( R , \mathfrak { m } )$ is a product of hyperplane reflections, except if $k = R / { \mathfrak { m } } = \mathbb { F } _ { 2 }$ , $\operatorname { r a n k } ( V ) = 4$ with quadratic form isometric to $x ^ { 2 } + x y + y ^ { 2 } + u ^ { 2 } + u v + v ^ { 2 }$ or if $k = R / { \mathfrak { m } } = \mathbb { F } _ { 2 }$ , $\operatorname { r a n k } ( V ) = 2$ .

### Definition / construction / notation {#fc11-c-u008}

::: {.unit-meta}
`FC11-C-U008` · Appendix C, source L11956-L11960
:::

For a non-degenerate quadratic torsion group $(G,q)$, the normalized Gauss sum is $\gamma_{(G,q)}=\

### Theorem C.2.1 {#fc11-c-u009}

::: {.unit-meta}
`FC11-C-U009` · Appendix C, source L11964
:::

Theorem C.2.1 (Milgram). Let $L$ be a non-degenerate integral quadratic lattice with discriminant form $( G , q )$ . Then $\gamma _ { ( G , q ) } = \rho _ { 8 } ^ { \tau _ { 8 } ( q ) } , \quad \rho _ { 8 } = \exp ( 2 \pi i / 8 )$ . 1

### Definition / construction {#fc11-c-u010}

::: {.unit-meta}
`FC11-C-U010` · Appendix C, source L11966-L11972
:::

For a possibly degenerate quadratic torsion form $q$ on $G$ and a homomorphism $f:\mathbf Q/\mathbf Z\to\mathbf Q/\mathbf Z$, the generalized Gauss sum is $\gamma_{(G,q)}(f)=\

### Proposition C.2.2 {#fc11-c-u011}

::: {.unit-meta}
`FC11-C-U011` · Appendix C, source L11976-L11980
:::

Proposition C.2.2. (1) If $\iota : ( G , q ) \simeq ( G ^ { \prime } , q ^ { \prime } )$ is an isometry of torsion quadratic forms and $f , f ^ { \prime } : \mathbb { Q } / \mathbb { Z } \to \mathbb { Q } / \mathbb { Z }$ homomorphisms for which $f ^ { \prime } { \circ } q ^ { \prime } { \circ } l ~ = ~ f { \circ } q$ , then $\gamma _ { ( G ^ { \prime } , q ^ { \prime } ) } ( f ^ { \prime } ) = \gamma _ { ( G , q ) } ( f )$ . (2) Let $\left( G , q \right) = \left( G ^ { \prime } , q ^ { \prime } \right) \oplus \left( G ^ { \prime \prime } , q ^ { \prime \prime } \right)$ , then for all homomorphisms $f : \mathbb { Q } / \mathbb { Z } \to \mathbb { Q } / \mathbb { Z }$ one has $\gamma _ { ( G , q ) } ( f ) = \gamma _ { ( G ^ { \prime } , q ^ { \prime } ) } ( f ) \cdot \gamma _ { ( G ^ { \prime \prime } , q ^ { \prime \prime } ) } ( f )$ . (3) If $H$ is a totally isotropic subgroup of $( G , q )$ then $\begin{array} { r } { \gamma _ { ( G , q ) } = \sqrt { \

### Proposition C.2.3 {#fc11-c-u012}

::: {.unit-meta}
`FC11-C-U012` · Appendix C, source L12009-L12020
:::

Proposition C.2.3. (1) Let $p$ be a prime and $G = \mathbb { Z } / p ^ { k } \mathbb { Z }$ , $k \geq 1$ . Then $$ \gamma _ { ( G , \langle u \cdot p ^ { - k } \rangle ) } ( p ^ { \ell } ) = { \left\{ \begin{array} { l l } { p ^ { k / 2 } } & { i f \ell > k } \\ { p ^ { \ell / 2 } } & { i f \ell = k , \quad p \neq 2 } \\ { 0 } & { i f \ell = k , \quad p = 2 } \\ { p ^ { \ell / 2 } \cdot \gamma _ { ( G , \langle u \cdot p ^ { - ( k - \ell ) } \rangle ) } } & { i f \ell < k } \end{array} \right. } $$ (2) For $u _ { k } , v _ { k }$ , $G = \mathbb { Z } / 2 ^ { k } \mathbb { Z } \oplus \mathbb { Z } / 2 ^ { k } \mathbb { Z }$ , we have $$ \gamma _ { ( G , u _ { k } ) } ( 2 ^ { \ell } ) = \left\{ \begin{array} { l l } { 2 ^ { k } } & { \mathrm { ~ } i f \ell \ge k } \\ { 2 ^ { \ell } \cdot \gamma _ { ( G , u _ { k - \ell } ) } } & { \mathrm { ~ } i f \ell < k } \end{array} \right. \mathrm { ~ } \mathrm { ~ } a n d \gamma _ { ( G , v _ { k } ) } ( 2 ^ { \ell } ) = \left\{ \begin{array} { l l } { 2 ^ { k } } & { \mathrm { ~ } i f \ell \ge k } \\ { 2 ^ { \ell } \cdot \gamma _ { ( G , v _ { k - \ell } ) } } & { \mathrm { ~ } i f \ell < k } \end{array} \right. $$

### Corollary C.2.5 {#fc11-c-u013}

::: {.unit-meta}
`FC11-C-U013` · Appendix C, source L12035-L12045
:::

Corollary C.2.5. (1). Let $p$ be a prime and $G = \mathbb { Z } / p ^ { k } \mathbb { Z }$ . Then $$ \sigma _ { \ell } ( G , \langle u \cdot p ^ { - k } \rangle ) = { \left\{ \begin{array} { l l } { 1 } & { \ i f \ \ell > k } \\ { 1 } & { \ i f \ \ell = k , \quad p \neq 2 } \\ { 0 } & { \ i f \ \ell = k , \quad p = 2 } \\ { \gamma _ { ( G , \langle u \cdot p ^ { - ( k - \ell ) } \rangle ) } } & { \ i f \ \ell < k . } \end{array} \right. } $$ (2) For $u _ { k } , v _ { k }$ , $G = \mathbb { Z } / 2 ^ { k } \mathbb { Z } \oplus \mathbb { Z } / 2 ^ { k } \mathbb { Z }$ , we have $$ \sigma _ { \ell } ( G , u _ { k } ) = \left\{ \begin{array} { l l } { 1 } & { \mathrm { ~ } i f \ell \geq k } \\ { \gamma _ { ( G , u _ { k - \ell } ) } } & { \mathrm { ~ } i f \ell < k } \end{array} \right. \quad a n d \sigma _ { \ell } ( G , v _ { k } ) = \left\{ \begin{array} { l l } { 1 } & { \mathrm { ~ } i f \ell \geq k } \\ { \gamma _ { ( G , v _ { k - \ell } ) } } & { \mathrm { ~ } i f \ell < k } \end{array} \right. $$

### Proposition C.3.1 {#fc11-c-u014}

::: {.unit-meta}
`FC11-C-U014` · Appendix C, source L12110-L12125
:::

Proposition C.3.1. Let $( G , q )$ be a homogeneous 2-primary quadratic torsion group of exponent $k$ and length $\ell ( G )$ . Then (1) $q \simeq w _ { k } \oplus ^ { b } v _ { k } \oplus ^ { c } u _ { k }$ , where $w _ { k }$ is an orthogonal direct sum of $a$ cyclic groups, $a \leq 2$ , $b \leq 1$ , $\begin{array} { r } { c = \frac { 1 } { 2 } ( \ell ( G ) - a ) - b } \end{array}$ , and where ?? is an isometry invariant of $q$ . (2) If $a = 2 , b = 0$ , then $w _ { k }$ is isometric to one of the following: $$ \langle 2 ^ { - k } \rangle \mathbb { \ O } \langle 2 ^ { - k } \rangle , \quad \langle - 2 ^ { - k } \rangle \mathbb { \ O } \langle - 2 ^ { - k } \rangle , \ w i t h \ \delta ( q ) = 1 $$ $$ \langle - 2 ^ { - k } \rangle \oplus \langle 3 \cdot 2 ^ { - k } \rangle , \quad \langle 2 ^ { - k } \rangle \oplus \langle - 3 \cdot 2 ^ { - k } \rangle \ w i t h \ \delta ( q ) = - $$ (3) If $a = 2 , b = 1$ , one may assume that $w _ { k } \oplus v _ { k }$ is one of the following: $$ \begin{array} { r l r } & { } & { \langle 2 ^ { - k } \rangle \oplus \langle 3 \cdot 2 ^ { - k } \rangle \oplus v _ { k } \ w i t h \ \delta ( q ) = 1 } \\ & { } & { \langle 2 ^ { - k } \rangle \oplus \langle - 2 ^ { - k } \rangle \oplus v _ { k } \ w i t h \ \delta ( q ) = - 3 . } \end{array} $$

### Definition / construction / notation {#fc11-c-u015}

::: {.unit-meta}
`FC11-C-U015` · Appendix C, source L12128 · after [`FC11-C-U014`](#fc11-c-u014)
:::

A normal form as in Proposition C.3.1 is called a reduced homogeneous normal form. Such normal forms are collected in the following table.

### Corollary C.3.2 {#fc11-c-u016}

::: {.unit-meta}
`FC11-C-U016` · Appendix C, source L12133-L12134
:::

Corollary C.3.2. Every 2-primary homogeneous quadratic form has a unique reduced normal form given in Table C.3.1. For $k \geq 2$ these forms are mutually non-isometric. For $k = 1$ the forms with $\delta = 1 , - 3$ with corresponding remaining invariants are isometric and the same holds for forms with $\delta = - 1 , 3$ .

### Lemma C.3.3 {#fc11-c-u017}

::: {.unit-meta}
`FC11-C-U017` · Appendix C, source L12145-L12172
:::

Lemma C.3.3. Let $u , u ^ { \prime } , u ^ { \prime \prime }$ be units in $\mathbb { Z } _ { 2 }$ . Then the following relations hold between non-homogeneous dyadic forms. $$ \langle u \cdot 2 ^ { k - 1 } \rangle \oplus U _ { k } \simeq \langle - 3 u \cdot 2 ^ { k - 1 } \rangle \oplus V _ { k } ~ f o r ~ k \geq 1 $$ $$ U _ { k - 1 } \oplus \langle u \cdot 2 ^ { k } \rangle \simeq \langle 3 u \cdot 2 ^ { k } \rangle \oplus V _ { k - 1 } ~ f o r ~ k \geq 1 $$ $$ \langle u \cdot 2 ^ { k - 1 } \rangle \mathbb { O } \langle u ^ { \prime } \cdot 2 ^ { k } \rangle \simeq \langle ( u + 2 u ^ { \prime } ) \cdot 2 ^ { k - 1 } \rangle \mathbb { O } \langle ( u ^ { \prime } + 2 u ) \cdot 2 ^ { k } \rangle f o r k \geq 1 $$ $$ ( \langle u \rangle \mathbb { O } \langle u ^ { \prime } \rangle ) ( 2 ^ { k - 1 } ) \mathbb { O } \langle 2 ^ { k } \rangle \simeq ( \langle u + 2 \rangle \mathbb { O } \langle u ^ { \prime } - 2 \rangle ) ( 2 ^ { k - 1 } ) \mathbb { O } \langle - 3 \cdot 2 ^ { k } \rangle $$ $$ \dot { u } \equiv u ^ { \prime } \bmod 4 , \quad k \geq 1 . $$ $$ \langle u \cdot 2 ^ { k - 2 } \rangle \mathbb { O } \langle u ^ { \prime } \cdot 2 ^ { k } \rangle \simeq \langle - 3 u \cdot 2 ^ { k - 2 } \rangle \mathbb { O } \langle - 3 u ^ { \prime } \cdot 2 ^ { k } \rangle , f o r k \geq 3 . $$ Similar relations hold for their quadratic torsion forms, that is, for the 2-primary quadratic torsion groups where the exponents $2 ^ { j }$ are replaced by $2 ^ { - j }$ , and for $u _ { k }$ and $v _ { k }$ instead of $U _ { k }$ and $V _ { k }$ , respectively.

### Remark C.3.4 {#fc11-c-u018}

::: {.unit-meta}
`FC11-C-U018` · Appendix C, source L12210 · after [`FC11-C-U017`](#fc11-c-u017)
:::

Remark C.3.4. The relations (V)–(IX) from Lemma C.3.3 involving different exponents give further reductions of non-homogeneous forms whose homogeneous summands are already in reduced normal form. These relations affect three consecutive exponents. Starting with the largest exponent and going down, this gives a new reduced normal form as is shown in [156, Ch.4.4]. Furthermore, as a consequence, every 2-primary quadratic torsion form and every quadratic dyadic lattice has a reduced normal form and no two such forms are isometric.

