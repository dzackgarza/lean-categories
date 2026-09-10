---
title: "FC02 — Munkres, *Topology*"
---

Corpus source: `FC02` in [Foundational source corpus v1 (frozen)](/corpus.html).

Pinned source: James R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000; complete book, exercises excluded.

Markdown extraction: ``local-write-api-1783249491889-EEDYK7RG_extracted.md``.

This is the canonical Sweep-I source-unit catalogue for FC02. Stable source-local IDs are consumed unchanged by Sweeps II–IV. Starred main-text sections are in scope; ordinary and supplementary exercise sections are excluded.

## Coverage

- Chapters 1–7: 530 units.
- Chapters 8–14: 314 units.
- Total: 844 stable source units.
- Explicit main-text Definition/Lemma/Theorem/Proposition/Corollary labels covered: 500.
- Every unit has section/page-span and exact extraction-line location; dependencies are source-unit IDs and point strictly backward.

## C01 — Set Theory and Logic

Units: 153.

### FC02-C01-U001

- **Kind:** Convention/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L277.
- **Statement/data:** Use $a\in A$ for membership and $a\notin A$ for nonmembership.
- **Dependencies:** —.

### FC02-C01-U002

- **Kind:** Convention/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L289.
- **Statement/data:** The equality sign means logical identity; $A=B$ means the two sets have exactly the same elements.
- **Dependencies:** —.

### FC02-C01-U003

- **Kind:** Definition/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L293.
- **Statement/data:** $A\subset B$ means every element of $A$ lies in $B$; $A\subsetneq B$ means proper inclusion; $B\supset A$ is reverse inclusion.
- **Dependencies:** —.

### FC02-C01-U004

- **Kind:** Convention/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L307.
- **Statement/data:** Finite sets may be listed inside braces; set-builder notation ${x\mid P(x)}$ denotes the set of objects satisfying the stated property.
- **Dependencies:** —.

### FC02-C01-U005

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L325.
- **Statement/data:** $A\cup B={x\mid x\in A\text{ or }x\in B}$ is the union.
- **Dependencies:** —.

### FC02-C01-U006

- **Kind:** Logical convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L339.
- **Statement/data:** Mathematical “or” is inclusive: $P$ or $Q$ allows both $P$ and $Q$.
- **Dependencies:** —.

### FC02-C01-U007

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L347.
- **Statement/data:** $A\cap B={x\mid x\in A\text{ and }x\in B}$ is the intersection.
- **Dependencies:** —.

### FC02-C01-U008

- **Kind:** Convention/definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L355.
- **Statement/data:** $\varnothing$ denotes the empty set, having no elements.
- **Dependencies:** —.

### FC02-C01-U009

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L363.
- **Statement/data:** Sets $A,B$ are disjoint when $A\cap B=\varnothing$.
- **Dependencies:** —.

### FC02-C01-U010

- **Kind:** Logical convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L393.
- **Statement/data:** “If $P$, then $Q$” asserts $Q$ whenever $P$ holds; when $P$ is false no condition on $Q$ is imposed.
- **Dependencies:** —.

### FC02-C01-U011

- **Kind:** Convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L407.
- **Statement/data:** An implication with impossible hypothesis is regarded as vacuously true.
- **Dependencies:** —.

### FC02-C01-U012

- **Kind:** Consequence/convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L411.
- **Statement/data:** $\varnothing\subset A$ for every set $A$, vacuously.
- **Dependencies:** FC02-C01-U008, FC02-C01-U010.

### FC02-C01-U013

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L417.
- **Statement/data:** The contrapositive of $P\Rightarrow Q$ is $(\neg Q)\Rightarrow(\neg P)$.
- **Dependencies:** FC02-C01-U010.

### FC02-C01-U014

- **Kind:** Logical equivalence.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L443.
- **Statement/data:** An implication and its contrapositive are logically equivalent.
- **Dependencies:** FC02-C01-U013.

### FC02-C01-U015

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L467.
- **Statement/data:** The converse of $P\Rightarrow Q$ is $Q\Rightarrow P$; it need not have the same truth value.
- **Dependencies:** FC02-C01-U010.

### FC02-C01-U016

- **Kind:** Convention/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L493.
- **Statement/data:** $P\Leftrightarrow Q$ means both $P\Rightarrow Q$ and $Q\Rightarrow P$ hold (“if and only if”).
- **Dependencies:** FC02-C01-U015.

### FC02-C01-U017

- **Kind:** Definition/logic.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L503.
- **Statement/data:** The negation of $P$ is “not $P$”; “for every” and “for at least one” are logical quantifiers.
- **Dependencies:** —.

### FC02-C01-U018

- **Kind:** Quantifier-negation rule.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L515.
- **Statement/data:** The negation of “for every $x\in A$, $P(x)$” is “for at least one $x\in A$, not $P(x)$,” and conversely.
- **Dependencies:** FC02-C01-U017.

### FC02-C01-U019

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L527.
- **Statement/data:** $A-B={x\mid x\in A, x\notin B}$ is the difference, also the complement of $B$ relative to $A$.
- **Dependencies:** —.

### FC02-C01-U020

- **Kind:** Identity.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L552.
- **Statement/data:** Set operations satisfy distributive laws, e.g. $A\cap(B\cup C)=(A\cap B)\cup(A\cap C)$ and its dual.
- **Dependencies:** FC02-C01-U005, FC02-C01-U007.

### FC02-C01-U021

- **Kind:** Identity.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L566.
- **Statement/data:** De Morgan laws: $A-(B\cup C)=(A-B)\cap(A-C)$ and $A-(B\cap C)=(A-B)\cup(A-C)$.
- **Dependencies:** FC02-C01-U005, FC02-C01-U007, FC02-C01-U019.

### FC02-C01-U022

- **Kind:** Definition/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L582.
- **Statement/data:** $\mathcal P(A)$ is the power set, the set of all subsets of $A$.
- **Dependencies:** FC02-C01-U003.

### FC02-C01-U023

- **Kind:** Convention/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L584.
- **Statement/data:** A set whose elements are sets is called a collection of sets and is typically denoted by a script letter.
- **Dependencies:** —.

### FC02-C01-U024

- **Kind:** Convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L586.
- **Statement/data:** Distinguish an element $a$, the singleton ${a}$, and membership ${a}\in\mathcal P(A)$.
- **Dependencies:** FC02-C01-U022.

### FC02-C01-U025

- **Kind:** Definition/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L598.
- **Statement/data:** $\bigcup_{A\in\mathcal A}A$ consists of points belonging to at least one member of the collection $\mathcal A$.
- **Dependencies:** FC02-C01-U005, FC02-C01-U023.

### FC02-C01-U026

- **Kind:** Definition/notation.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L604.
- **Statement/data:** $\bigcap_{A\in\mathcal A}A$ consists of points belonging to every member of the nonempty collection $\mathcal A$.
- **Dependencies:** FC02-C01-U007, FC02-C01-U023.

### FC02-C01-U027

- **Kind:** Convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L610.
- **Statement/data:** The union of the empty collection is $\varnothing$; Munkres leaves the intersection of the empty collection undefined unless a universe is separately fixed.
- **Dependencies:** FC02-C01-U008, FC02-C01-U025, FC02-C01-U026.

### FC02-C01-U028

- **Kind:** Definition.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L628.
- **Statement/data:** $A\times B={(a,b)\mid a\in A,b\in B}$ is the Cartesian product.
- **Dependencies:** —.

### FC02-C01-U029

- **Kind:** Construction.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L634.
- **Statement/data:** An ordered pair may be encoded set-theoretically as $(a,b)={{a},{a,b}}$.
- **Dependencies:** FC02-C01-U022.

### FC02-C01-U030

- **Kind:** Notation convention.
- **Locator:** §1 “Fundamental Concepts”; printed pp. 4–14; extraction L644.
- **Statement/data:** When $(a,b)$ as an ordered pair could be confused with interval notation, Munkres writes the ordered pair as $a\times b$.
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U031

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L762.
- **Statement/data:** A rule of assignment is a subset r of the cartesian product $C \times D$ of two sets, having the property that each element of C appears as the first coordinate of at most one ordered pair belonging to r.
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U032

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L772.
- **Statement/data:** For a rule of assignment, its domain is the set of first coordinates and its image set is the set of second coordinates.
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U033

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L782.
- **Statement/data:** A function $f$ is a rule of assignment $r$ , together with a set $B$ that contains the image set of $r$ . The domain $A$ of the rule $r$ is also called the domain of the function $f$ ; the image set of $r$ is also called the image set of $f$ ; and the set $B$ is called the range of $f$ . $^{\dagger}$ If $f$ is a function having domain $A$ and range $B$ , we express this fact by writing $$ f: A \longrightarrow B, $$ which is read “f is a function from A to B,” or “f is a mapping from A into B,” or simply “f maps A into B.” One sometimes visualizes f as a geometric transformation physically carrying the points of A to points of B. If $f: A \to B$ and if $a$ is an element of $A$ , we denote by $f(a)$ the unique element of $B$ that the rule determining $f$ assigns to $a$ ; it is called the value of $f$ at $a$ , or sometimes the image of $a$ under $f$ . Formally, if $r$ is the rule of the function $f$ , then $f(a)$ denotes the unique element of $B$ such that $(a, f(a)) \in r$ . Using this notation, one can go back to defining functions almost as one did before, with no lack of rigor. For instance, one can write (letting R denote the real numbers) "Let $f$ be the function whose rule is ${(x, x^3 + 1) \mid x \in \mathbb{R}}$ and whose range is $\mathbb{R}$ ,"
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U034

- **Kind:** Definition/notation.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L792.
- **Statement/data:** For $f:A\to B$, $f(a)$ is the unique value/image assigned to $a$.
- **Dependencies:** —.

### FC02-C01-U035

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L804.
- **Statement/data:** If $f: A \to B$ and if $A_0$ is a subset of $A$ , we define the restriction of $f$ to $A_0$ to be the function mapping $A_0$ into $B$ whose rule is $$ {(a, f (a)) \mid a \in A _ {0} }. $$ It is denoted by $f|A_{0}$ , which is read “f restricted to $A_{0}$ .”
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U036

- **Kind:** Example 1.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L812.
- **Statement/data:** Let $\mathbb{R}$ denote the real numbers and let $\bar{\mathbb{R}}_{+}$ denote the nonnegative reals. Consider the functions $$ f: \mathbb {R} \longrightarrow \mathbb {R} \quad \text { defined by } \quad f (x) = x ^ {2}, $$
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U037

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L837.
- **Statement/data:** Given functions $f: A \to B$ and $g: B \to C$ , we define the composite $g \circ f$ of $f$ and $g$ as the function $g \circ f: A \to C$ defined by the equation $(g \circ f)(a) = g(f(a))$ .
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U038

- **Kind:** Example 2.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L852.
- **Statement/data:** The composite of the function $f: \mathbb{R} \to \mathbb{R}$ given by $f(x) = 3x^2 + 2$ and the function $g: \mathbb{R} \to \mathbb{R}$ given by $g(x) = 5x$ is the function $g \circ f: \mathbb{R} \to \mathbb{R}$ given by $$ (g \circ f) (x) = g (f (x)) = g (3 x ^ {2} + 2) = 5 (3 x ^ {2} + 2). $$
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U039

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L864.
- **Statement/data:** A function $f: A \rightarrow B$ is said to be injective (or one-to-one) if for each pair of distinct points of A, their images under f are distinct. It is said to be surjective (or f is said to map A onto B) if every element of B is the image of some element of A under the function f. If f is both injective and surjective, it is said to be bijective (or is called a one-to-one correspondence).
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U040

- **Kind:** Definition/notation.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L880.
- **Statement/data:** For bijective $f:A\to B$, the inverse $f^{-1}:B\to A$ sends $b$ to the unique $a$ with $f(a)=b$.
- **Dependencies:** —.

### FC02-C01-U041

- **Kind:** Example 3.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L882.
- **Statement/data:** Consider again the functions $f, g, h$ , and $k$ of Figure 2.1. The function $f: \mathbb{R} \to \mathbb{R}$ given by $f(x) = x^2$ is neither injective nor surjective. Its restriction $g$ to the nonnegative reals is injective but not surjective. The function $h: \mathbb{R} \to \bar{\mathbb{R}}*+$ obtained from $f$ by changing the range is surjective but not injective. The function $k \cdot \bar{\mathbb{R}}*+ \to \bar{\mathbb{R}}_+$ obtained from $f$ by restricting the domain and changing the range is both injective and surjective, so it has an inverse. Its inverse is, of course, what we usually call the square-root function.
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U042

- **Kind:** Lemma 2.1.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L886.
- **Statement/data:** Let $f: A \to B$ . If there are functions $g: B \to A$ and $h: B \to A$ such that $g(f(a)) = a$ for every $a$ in $A$ and $f(h(b)) = b$ for every $b$ in $B$ , then $f$ is bijective and $g = h = f^{-1}$ .
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U043

- **Kind:** Definition.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L888.
- **Statement/data:** Let $f: A \to B$ . If $A_0$ is a subset of $A$ , we denote by $f(A_0)$ the set of all images of points of $A_0$ under the function $f$ ; this set is called the image of $A_0$ under $f$ . Formally, $$ f (A _ {0}) = {b \mid b = f (a) \text { for at least one } a \in A _ {0} }. $$ On the other hand, if $B_{0}$ is a subset of B, we denote by $f^{-1}(B_{0})$ the set of all elements of A whose images under f lie in $B_{0}$ ; it is called the preimage of $B_{0}$ under f (or the “counterimage,” or the “inverse image,” of $B_{0}$ ). Formally, $$ f ^ {- 1} (B _ {0}) = {a \mid f (a) \in B _ {0} }. $$ Of course, there may be no points $a$ of $A$ whose images lie in $B_0$ ; in that case, $f^{-1}(B_0)$ is empty.
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U044

- **Kind:** Definition/notation.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L894.
- **Statement/data:** For $B_0\subset B$, $f^{-1}(B_0)={a\in A\mid f(a)\in B_0}$ is the preimage/inverse image.
- **Dependencies:** —.

### FC02-C01-U045

- **Kind:** Example 4.
- **Locator:** §2 “Functions”; printed pp. 15–20; extraction L914.
- **Statement/data:** Consider the function $f: \mathbb{R} \to \mathbb{R}$ given by $f(x) = 3x^2 + 2$ (Figure 2.3). Let $[a, b]$ denote the closed interval $a \leq x \leq b$ . Then $$ f ^ {- 1} (f ([ 0, 1 ])) = f ^ {- 1} ([ 2, 5 ]) = [ - 1, 1 ], \quad \text { and } $$
- **Dependencies:** FC02-C01-U028.

### FC02-C01-U046

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L991.
- **Statement/data:** A relation on a set $A$ is a subset $C$ of the cartesian product $A \times A$ .
- **Dependencies:** —.

### FC02-C01-U047

- **Kind:** Example 1.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L997.
- **Statement/data:** Let $P$ denote the set of all people in the world, and define $D \subset P \times P$ by the equation $$ D = {(x, y) \mid x \text { is a descendant of } y }. $$
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U048

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1013.
- **Statement/data:** An equivalence relation is a reflexive, symmetric, transitive relation.
- **Dependencies:** —.

### FC02-C01-U049

- **Kind:** Example 2.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1021.
- **Statement/data:** Among the relations defined in Example 1, the descendant relation D is neither reflexive nor symmetric, while the blood relation B is not transitive (I am not a blood relation to my wife, although my children are!) The sibling relation S is, however, an equivalence relation, as you may check.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U050

- **Kind:** Convention/notation.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1023.
- **Statement/data:** The symbol $\sim$ is used generically for equivalence relations.
- **Dependencies:** FC02-C01-U048.

### FC02-C01-U051

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1033.
- **Statement/data:** For an equivalence relation $\sim$ on $A$, the class determined by $x$ is $[x]={y\mid y\sim x}$ (source writes $E$).
- **Dependencies:** FC02-C01-U048.

### FC02-C01-U052

- **Kind:** Lemma 3.1.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1041.
- **Statement/data:** Two equivalence classes $E$ and $E'$ are either disjoint or equal.
- **Dependencies:** FC02-C01-U046, FC02-C01-U048, FC02-C01-U051.

### FC02-C01-U053

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1054.
- **Statement/data:** A partition of a set $A$ is a collection of disjoint nonempty subsets of $A$ whose union is all of $A$ .
- **Dependencies:** FC02-C01-U046, FC02-C01-U048.

### FC02-C01-U054

- **Kind:** Construction/comparison.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1056.
- **Statement/data:** Equivalence relations on $A$ and partitions of $A$ determine one another: classes form a partition, and a partition induces $x\sim y$ iff they lie in the same part.
- **Dependencies:** FC02-C01-U048, FC02-C01-U053.

### FC02-C01-U055

- **Kind:** Example 3.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1062.
- **Statement/data:** Define two points in the plane to be equivalent if they lie at the same distance from the origin. Reflexivity, symmetry, and transitivity hold trivially. The collection $\mathcal{E}$ of equivalence classes consists of all circles centered at the origin, along with the set consisting of the origin alone.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U056

- **Kind:** Example 4.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1064.
- **Statement/data:** Define two points of the plane to be equivalent if they have the same y-coordinate. The collection of equivalence classes is the collection of all straight lines in the plane parallel to the x-axis.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U057

- **Kind:** Example 5.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1066.
- **Statement/data:** Let L be the collection of all straight lines in the plane parallel to the line y = -x. Then L is a partition of the plane, since each point lies on exactly one such line. The partition L comes from the equivalence relation on the plane that declares the points $(x_{0}, y_{0})$ and $(x_{1}, y_{1})$ to be equivalent if $x_{0} + y_{0} = x_{1} + y_{1}$ .
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U058

- **Kind:** Example 6.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1068.
- **Statement/data:** Let $\mathcal{L}'$ be the collection of all straight lines in the plane. Then $\mathcal{L}'$ is not a partition of the plane, for distinct elements of $\mathcal{L}'$ are not necessarily disjoint; two lines may intersect without being equal.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U059

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1072.
- **Statement/data:** A simple/linear order is a relation satisfying comparability of distinct elements, nonreflexivity, and transitivity.
- **Dependencies:** —.

### FC02-C01-U060

- **Kind:** Example 7.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1082.
- **Statement/data:** Consider the relation on the real line consisting of all pairs $(x, y)$ of real numbers such that $x < y$ . It is an order relation, called the "usual order relation," on the real line. A less familiar order relation on the real line is the following: Define $xCy$ if $x^2 < y^2$ , or if $x^2 = y^2$ and $x < y$ . You can check that this is an order relation.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U061

- **Kind:** Definition/comparison.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1084.
- **Statement/data:** A strict partial order satisfies nonreflexivity and transitivity but need not satisfy comparability.
- **Dependencies:** —.

### FC02-C01-U062

- **Kind:** Example 8.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1084.
- **Statement/data:** Consider again the relationships among people given in Example 1. The blood relation $B$ satisfies none of the properties of an order relation, and the sibling relation $S$ satisfies only (3). The descendant relation $D$ does somewhat better, for it satisfies both (2) and (3); however, comparability still fails. Relations that satisfy (2) and (3) occur often enough in mathematics to be given a special name. They are called strict partial order relations; we shall consider them later (see §11).
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U063

- **Kind:** Convention/notation.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1094.
- **Statement/data:** For a strict order, $x\le y$ means $x<y$ or $x=y$; $y>x$ means $x<y$; chains such as $x<y<z$ abbreviate conjunctions.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U064

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1096.
- **Statement/data:** If $X$ is a set and $<$ is an order relation on $X$ , and if $a < b$ , we use the notation $(a, b)$ to denote the set $$ {x \mid a < x < b }; $$ it is called an open interval in X. If this set is empty, we call a the immediate predecessor of b, and we call b the immediate successor of a.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U065

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1102.
- **Statement/data:** If the open interval $(a,b)$ is empty, $a$ is the immediate predecessor of $b$ and $b$ the immediate successor of $a$.
- **Dependencies:** —.

### FC02-C01-U066

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1104.
- **Statement/data:** Suppose that A and B are two sets with order relations $<*{A}$ and $<*{B}$ respectively. We say that A and B have the same order type if there is a bijective correspondence between them that preserves order; that is, if there exists a bijective function $f: A \rightarrow B$ such that $$ a _ {1} < _ {A} a _ {2} \Longrightarrow f (a _ {1}) < _ {B} f (a _ {2}). $$
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U067

- **Kind:** Example 9.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1110.
- **Statement/data:** The interval $(-1, 1)$ of real numbers has the same order type as the set $\mathbb{R}$ of real numbers itself, for the function $f \cdot (-1, 1) \to \mathbb{R}$ given by $$ f (x) = \frac {x}{1 - x ^ {2}} $$
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U068

- **Kind:** Example 10.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1118.
- **Statement/data:** The subset $A = {0} \cup (1,2)$ of $\mathbb{R}$ has the same order type as the subset $$ [ 0, 1) = {x \mid 0 \leq x < 1 } $$
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U069

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1137.
- **Statement/data:** Suppose that $A$ and $B$ are two sets with order relations $<*{A}$ and $<*{B}$ respectively. Define an order relation $<$ on $A \times B$ by defining $$ a _ {1} \times b _ {1} < a _ {2} \times b _ {2} $$ if $a_1 <*{A} a_2$ , or if $a_1 = a_2$ and $b_1 <*{B} b_2$ . It is called the dictionary order relation on $A \times B$ .
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U070

- **Kind:** Example 11.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1149.
- **Statement/data:** Consider the dictionary order on the plane $\mathbb{R} \times \mathbb{R}$ . In this order, the point $p$ is less than every point lying above it on the vertical line through $p$ , and $p$ is less than every point to the right of this vertical line.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U071

- **Kind:** Example 12.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1151.
- **Statement/data:** Consider the set $[0, 1)$ of real numbers and the set $\mathbb{Z}*{+}$ of positive integers, both in their usual orders; give $\mathbb{Z}*{+} \times [0, 1)$ the dictionary order. This set has the same order type as the set of nonnegative reals; the function $$ f (n \times t) = n + t - 1 $$
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U072

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1164.
- **Statement/data:** For $A_0$ in an ordered set: largest/smallest elements are members dominating/preceding all elements of $A_0$.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U073

- **Kind:** Definition/notation.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1166.
- **Statement/data:** Bounded above/below, upper/lower bounds, supremum $\sup A_0$, and infimum $\inf A_0$ are defined in the usual order-theoretic way.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U074

- **Kind:** Definition.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1172.
- **Statement/data:** An ordered set A is said to have the least upper bound property if every nonempty subset $A_{0}$ of A that is bounded above has a least upper bound. Analogously, the set A is said to have the greatest lower bound property if every nonempty subset $A_{0}$ of A that is bounded below has a greatest lower bound.
- **Dependencies:** FC02-C01-U046, FC02-C01-U073.

### FC02-C01-U075

- **Kind:** Example 13.
- **Locator:** §3 “Relations”; printed pp. 21–29; extraction L1176.
- **Statement/data:** Consider the set $A = (-1, 1)$ of real numbers in the usual order. Assuming the fact that the real numbers have the least upper bound property, it follows that the set A has the least upper bound property. For, given any subset of A having an upper bound in A, it follows that its least upper bound (in the real numbers) must be in A. For example, the subset ${-1/2n \mid n \in Z_{+}}$ of A, though it has no largest element, does have a least upper bound in A, the number 0.
- **Dependencies:** FC02-C01-U046.

### FC02-C01-U076

- **Kind:** Definition.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1282.
- **Statement/data:** A binary operation on a set A is a function f mapping $A \times A$ into A.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U077

- **Kind:** Assumption/construction.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1288.
- **Statement/data:** The real numbers are taken with addition, multiplication, and a linear order satisfying the field axioms, order compatibility, the least-upper-bound property, and the linear-continuum density property.
- **Dependencies:** FC02-C01-U059, FC02-C01-U074, FC02-C01-U076.

### FC02-C01-U078

- **Kind:** Construction/notation.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1326.
- **Statement/data:** From the field axioms define negatives, subtraction, reciprocals, and quotients in the standard way.
- **Dependencies:** FC02-C01-U077.

### FC02-C01-U079

- **Kind:** Definition/notation.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1336.
- **Statement/data:** $x>0$ means positive and $x<0$ negative; $\mathbb R_+$ denotes positive reals and $\bar{\mathbb R}_+$ nonnegative reals.
- **Dependencies:** FC02-C01-U077.

### FC02-C01-U080

- **Kind:** Comparison.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1338.
- **Statement/data:** An ordered set satisfying the two order axioms used for $\mathbb R$ (least-upper-bound plus density) is a linear continuum.
- **Dependencies:** FC02-C01-U074, FC02-C01-U077.

### FC02-C01-U081

- **Kind:** Definition.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1344.
- **Statement/data:** A subset $A$ of the real numbers is said to be inductive if it contains the number 1, and if for every $x$ in $A$ , the number $x+1$ is also in $A$ . Let $\mathcal{A}$ be the collection of all inductive subsets of $\mathbb{R}$ . Then the set $\mathbb{Z}*{+}$ of positive integers is defined by the equation $$ \mathbb {Z} _ {+} = \bigcap* {A \in \mathcal {A}} A. $$ Note that the set $R_{+}$ of positive real numbers is inductive, for it contains 1 and the statement x > 0 implies the statement $x + 1 > 0$ . Therefore, $Z_{+} \subset R_{+}$ , so the elements of $Z_{+}$ are indeed positive, as the choice of terminology suggests. Indeed, one sees readily that 1 is the smallest element of $Z_{+}$ , because the set of all real numbers x for which $x \geq 1$ is inductive. The basic properties of $\mathbb{Z}*{+}$ , which follow readily from the definition, are the following: (1) $\mathbb{Z}*{+}$ is inductive. (2) (Principle of induction). If $A$ is an inductive set of positive integers, then $A = \mathbb{Z}*+$ . We define the set Z of integers to be the set consisting of the positive integers $Z*{+}$ , the number 0, and the negatives of the elements of $Z_{+}$ . One proves that the sum, difference, and product of two integers are integers, but the quotient is not necessarily an integer. The set Q of quotients of integers is called the set of rational numbers.
- **Dependencies:** FC02-C01-U059, FC02-C01-U076.

### FC02-C01-U082

- **Kind:** Definition/construction.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1358.
- **Statement/data:** $\mathbb Z$ is the positive integers together with $0$ and their negatives; $\mathbb Q$ is the set of quotients of integers.
- **Dependencies:** —.

### FC02-C01-U083

- **Kind:** Theorem 4.1.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1372.
- **Statement/data:** (Well-ordering property). Every nonempty subset of $\mathbb{Z}_{+}$ has a smallest element.
- **Dependencies:** FC02-C01-U059, FC02-C01-U076, FC02-C01-U082.

### FC02-C01-U084

- **Kind:** Theorem 4.2.
- **Locator:** §4 “The Integers and the Real Numbers”; printed pp. 30–35; extraction L1380.
- **Statement/data:** (Strong induction principle). Let $A$ be a set of positive integers. Suppose that for each positive integer $n$ , the statement $S_{n} \subset A$ implies the statement $n \in A$ . Then $A = \mathbb{Z}_{+}$ .
- **Dependencies:** FC02-C01-U059, FC02-C01-U076, FC02-C01-U083.

### FC02-C01-U085

- **Kind:** Definition.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1544.
- **Statement/data:** Let A be a nonempty collection of sets. An indexing function for A is a surjective function f from some set J, called the index set, to A. The collection A, together with the indexing function f, is called an indexed family of sets. Given $\alpha \in J$ , we shall denote the set $f(\alpha)$ by the symbol $A_{\alpha}$ . And we shall denote the indexed family itself by the symbol $$ {A _ {\alpha} } _ {\alpha \in J}, $$ which is read "the family of all $A_{\alpha}$ , as $\alpha$ ranges over $J$ ." Sometimes we write merely ${A_{\alpha}}$ , if it is clear what the index set is. Note that although an indexing function is required to be surjective, it is not required to be injective. It is entirely possible for $A_{\alpha}$ and $A_{\beta}$ to be the same set of $\mathcal{A}$ , even though $\alpha \neq \beta$ . One way in which indexing functions are used is to give a new notation for arbitrary unions and intersections of sets. Suppose that $f: J \to A$ is an indexing function for A; let $A_{\alpha}$ denote $f(\alpha)$ . Then we define $$ \bigcup_ {\alpha \in J} A _ {\alpha} = {x \mid \text { for at least one } \alpha \in J, x \in A _ {\alpha} },
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U086

- **Kind:** Convention/notation.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1554.
- **Statement/data:** For indexed family ${A_\alpha}*{\alpha\in J}$, write $\bigcup*{\alpha\in J}A_\alpha$ and $\bigcap_{\alpha\in J}A_\alpha$ for its union/intersection.
- **Dependencies:** —.

### FC02-C01-U087

- **Kind:** Definition.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1580.
- **Statement/data:** Let $m$ be a positive integer. Given a set $X$ , we define an $m$ -tuple of elements of $X$ to be a function $$ \mathbf {x}: {1, \dots , m } \rightarrow X. $$ If x is an m-tuple, we often denote the value of x at i by the symbol $x_{i}$ rather than $\mathbf{x}(i)$ and call it the ith coordinate of x. And we often denote the function x itself by the symbol $$ (x _ {1}, \dots , x _ {m}). $$ Now let ${A_1, \ldots, A_m}$ be a family of sets indexed with the set ${1, \ldots, m}$ . Let $X = A_1 \cup \cdots \cup A_m$ . We define the cartesian product of this indexed family, denoted by
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U088

- **Kind:** Definition/construction.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1592.
- **Statement/data:** For a finite indexed family $A_1,\dots,A_m$, the Cartesian product is the set of $m$-tuples with $i$th coordinate in $A_i$.
- **Dependencies:** —.

### FC02-C01-U089

- **Kind:** Example 1.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1600.
- **Statement/data:** We now have two definitions for the symbol $A \times B$ . One definition is, of course, the one given earlier, under which $A \times B$ denotes the set of all ordered pairs $(a, b)$ such that $a \in A$ and $b \in B$ . The second definition, just given, defines $A \times B$ as the set of all functions $\mathbf{x} : {1, 2} \to A \cup B$ such that $\mathbf{x}(1) \in A$ and $\mathbf{x}(2) \in B$ . There is an obvious bijective correspondence between these two sets, under which the ordered pair $(a, b)$ corresponds to the function $\mathbf{x}$ defined by $\mathbf{x}(1) = a$ and $\mathbf{x}(2) = b$ . Since we commonly denote this function $\mathbf{x}$ in "tuple notation" by the symbol $(a, b)$ , the notation itself suggests the correspondence. Thus for the cartesian product of two sets, the general definition of cartesian product reduces essentially to the earlier one.
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U090

- **Kind:** Example 2.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1602.
- **Statement/data:** How does the cartesian product $A \times B \times C$ differ from the cartesian products $A \times (B \times C)$ and $(A \times B) \times C$ ? Very little. There are obvious bijective correspondences between these sets, indicated as follows $$ (a, b, c) \longleftrightarrow (a, (b, c)) \longleftrightarrow ((a, b), c). $$
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U091

- **Kind:** Definition.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1608.
- **Statement/data:** Given a set X, we define an $\omega$ -tuple of elements of X to be a function $$ \mathbf {x}: \mathbb {Z} _ {+} \longrightarrow X; $$ we also call such a function a sequence, or an infinite sequence, of elements of X. If x is an $\omega$ -tuple, we often denote the value of x at i by $x_{i}$ rather than $\mathbf{x}(i)$ , and call it the ith coordinate of x. We denote x itself by the symbol $$ (x _ {1}, x _ {2}, \dots) \quad \text { or } \quad (x _ {n}) _ {n \in \mathbb {Z} _ {+}}. $$ Now let ${A_{1}, A_{2}, \ldots}$ be a family of sets, indexed with the positive integers; let X be the union of the sets in this family. The cartesian product of this indexed family of sets, denoted by
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U092

- **Kind:** Definition/construction.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1620.
- **Statement/data:** For a sequence $A_1,A_2,\dots$, the Cartesian product is the set of $\omega$-tuples with $i$th coordinate in $A_i$.
- **Dependencies:** —.

### FC02-C01-U093

- **Kind:** Convention/notation.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1628.
- **Statement/data:** If all factors equal $X$, write $X^m$ for the finite product and $X^\omega$ for the countable product.
- **Dependencies:** —.

### FC02-C01-U094

- **Kind:** Example 3.
- **Locator:** §5 “Cartesian Products”; printed pp. 36–38; extraction L1632.
- **Statement/data:** If $\mathbb{R}$ is the set of real numbers, then $\mathbb{R}^m$ denotes the set of all $m$ -tuples of real numbers; it is often called euclidean $m$ -space (although Euclid would never recognize it). Analogously, $\mathbb{R}^\omega$ is sometimes called "infinite-dimensional euclidean space"; it is the set of all $\omega$ -tuples $(x_1, x_2, \ldots)$ of real numbers, that is, the set of all functions $\mathbf{x}: \mathbb{Z}_+ \to \mathbb{R}$ .
- **Dependencies:** FC02-C01-U028, FC02-C01-U033.

### FC02-C01-U095

- **Kind:** Definition/notation.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1684.
- **Statement/data:** $S_n={1,\dots,n-1}$ is the section of positive integers determined by $n$; finite sets are modeled on finite sections.
- **Dependencies:** —.

### FC02-C01-U096

- **Kind:** Definition.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1686.
- **Statement/data:** A set is said to be finite if there is a bijective correspondence of $A$ with some section of the positive integers. That is, $A$ is finite if it is empty or if there is a bijection $$ f: A \longrightarrow {1, \dots , n } $$ for some positive integer n. In the former case, we say that A has cardinality 0; in the latter case, we say that A has cardinality n. For instance, the set ${1, \ldots, n}$ itself has cardinality $n$ , for it is in bijective correspondence with itself under the identity function. Now note carefully: We have not yet shown that the cardinality of a finite set is uniquely determined by the set. It is of course clear that the empty set must have cardinality zero. But as far as we know, there might exist bijective correspondences of a given nonempty set A with two different sets ${1,\ldots,n}$ and ${1,\ldots,m}$ . The possibility may seem ridiculous, for it is like saying that it is possible for two people to count the marbles in a box and come out with two different answers, both correct. Our experience with counting in everyday life suggests that such is impossible, and in fact this is easy to prove when n is a small number such as 1, 2, or 3. But a direct proof when n is 5 million would be impossibly demanding. Even empirical demonstration would be difficult for such a large value of n. One might, for instance, construct an experiment by taking a freight car full of marbles and hiring 10 different people to count them independently. If one thinks of the physical problems involved, it seems likely that the counters would not all arrive at the same answer. Of course, the conclusion one could draw is that at least one person made a mistake. But that would mean assuming the correctness of the result one was trying to demonstrate empirically An alternative explanation could be that there do exist bijective correspondences between the given set of marbles and two different sections of the positive integers. In real life, we accept the first explanation. We simply take it on faith that our experience in counting comparatively small sets of objects demonstrates a truth that holds for arbitrarily large sets as well.
- **Dependencies:** FC02-C01-U033.

### FC02-C01-U097

- **Kind:** Definition/notation.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1698.
- **Statement/data:** If a finite nonempty set is bijective with ${1,\dots,n}$, its cardinality is $n$, written $|A|=n$; $|\varnothing|=0$.
- **Dependencies:** —.

### FC02-C01-U098

- **Kind:** Lemma 6.1.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1706.
- **Statement/data:** Let $n$ be a positive integer. Let $A$ be a set; let $a_0$ be an element of $A$ . Then there exists a bijective correspondence $f$ of the set $A$ with the set ${1, \ldots, n + 1}$ if and only if there exists a bijective correspondence $g$ of the set $A - {a_0}$ with the set ${1, \ldots, n}$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U096.

### FC02-C01-U099

- **Kind:** Theorem 6.2.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1748.
- **Statement/data:** Let $A$ be a set; suppose that there exists a bijection $f: A \to {1, \ldots, n}$ for some $n \in \mathbb{Z}_+$ . Let $B$ be a proper subset of $A$ . Then there exists no bijection $g: B \to {1, \ldots, n}$ ; but (provided $B \neq \emptyset$ ) there does exist a bijection $h: B \to {1, \ldots, m}$ for some $m < n$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U098.

### FC02-C01-U100

- **Kind:** Corollary 6.3.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1774.
- **Statement/data:** If $A$ is finite, there is no bijection of $A$ with a proper subset of itself.
- **Dependencies:** FC02-C01-U033, FC02-C01-U099.

### FC02-C01-U101

- **Kind:** Corollary 6.4.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1778.
- **Statement/data:** $\mathbb{Z}_{+}$ is not finite.
- **Dependencies:** FC02-C01-U033, FC02-C01-U100.

### FC02-C01-U102

- **Kind:** Corollary 6.5.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1782.
- **Statement/data:** The cardinality of a finite set A is uniquely determined by A.
- **Dependencies:** FC02-C01-U033, FC02-C01-U099.

### FC02-C01-U103

- **Kind:** Corollary 6.6.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1798.
- **Statement/data:** If B is a subset of the finite set A, then B is finite. If B is a proper subset of A, then the cardinality of B is less than the cardinality of A.
- **Dependencies:** FC02-C01-U033, FC02-C01-U099.

### FC02-C01-U104

- **Kind:** Corollary 6.7.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1800.
- **Statement/data:** Let B be a nonempty set. Then the following are equivalent: (1) $B$ is finite. (2) There is a surjective function from a section of the positive integers onto B. (3) There is an injective function from $B$ into a section of the positive integers.
- **Dependencies:** FC02-C01-U033, FC02-C01-U099.

### FC02-C01-U105

- **Kind:** Corollary 6.8.
- **Locator:** §6 “Finite Sets”; printed pp. 39–43; extraction L1820.
- **Statement/data:** Finite unions and finite cartesian products of finite sets are finite.
- **Dependencies:** FC02-C01-U033, FC02-C01-U103.

### FC02-C01-U106

- **Kind:** Definition.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1870.
- **Statement/data:** A set $A$ is said to be infinite if it is not finite. It is said to be countably infinite if there is a bijective correspondence $$ f: A \longrightarrow \mathbb {Z} _ {+}. $$
- **Dependencies:** FC02-C01-U096.

### FC02-C01-U107

- **Kind:** Definition/notation.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1872.
- **Statement/data:** Sets $A,B$ have the same cardinality if there is a bijection $A\to B$; for infinite sets cardinal comparisons are expressed via injections/bijections as developed here.
- **Dependencies:** —.

### FC02-C01-U108

- **Kind:** Example 1.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1876.
- **Statement/data:** The set $\mathbb{Z}$ of all integers is countably infinite. One checks easily that the function $f: \mathbb{Z} \to \mathbb{Z}_{+}$ defined by $$ f (n) = \left{ \begin{array}{l l} 2 n & \text {if} n > 0, \ - 2 n + 1 & \text {if} n \leq 0 \end{array} \right. $$
- **Dependencies:** FC02-C01-U096.

### FC02-C01-U109

- **Kind:** Example 2.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1884.
- **Statement/data:** The product $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ is countably infinite. If we represent the elements of the product $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ by the integer points in the first quadrant, then the left-hand portion of Figure 7.1 suggests how to "count" the points, that is, how to put them in bijective correspondence with the positive integers. A picture is not a proof, of course, but this picture suggests a proof. First, we define a bijection $f: \mathbb{Z}*{+} \times \mathbb{Z}*{+} \to A$ , where $A$ is the subset of $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ consisting of pairs $(x, y)$ for which $y \leq x$ , by the equation $$ f (x, y) = (x + y - 1, y). $$
- **Dependencies:** FC02-C01-U096.

### FC02-C01-U110

- **Kind:** Definition.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1903.
- **Statement/data:** A set is said to be countable if it is either finite or countably infinite. A set that is not countable is said to be uncountable.
- **Dependencies:** FC02-C01-U096.

### FC02-C01-U111

- **Kind:** Theorem 7.1.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1907.
- **Statement/data:** Let B be a nonempty set. Then the following are equivalent: (1) $B$ is countable. (2) There is a surjective function $f: \mathbb{Z}*+ \to B$ . (3) There is an injective function $g: B \to \mathbb{Z}*+$ .
- **Dependencies:** FC02-C01-U096, FC02-C01-U106, FC02-C01-U110.

### FC02-C01-U112

- **Kind:** Lemma 7.2.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1935.
- **Statement/data:** If $C$ is an infinite subset of $\mathbb{Z}_{+}$ , then $C$ is countably infinite.
- **Dependencies:** FC02-C01-U083, FC02-C01-U096.

### FC02-C01-U113

- **Kind:** Definition.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1965.
- **Statement/data:** A recursion formula defines a function in terms of earlier values; such a definition is a recursive definition.
- **Dependencies:** —.

### FC02-C01-U114

- **Kind:** Corollary 7.3.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1985.
- **Statement/data:** A subset of a countable set is countable.
- **Dependencies:** FC02-C01-U096, FC02-C01-U111, FC02-C01-U112.

### FC02-C01-U115

- **Kind:** Corollary 7.4.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1989.
- **Statement/data:** The set $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ is countably infinite.
- **Dependencies:** FC02-C01-U096, FC02-C01-U112.

### FC02-C01-U116

- **Kind:** Example 3.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L1999.
- **Statement/data:** The set $\mathbb{Q}*{+}$ of positive rational numbers is countably infinite. For we can define a surjection $g: \mathbb{Z}*{+} \times \mathbb{Z}*{+} \to \mathbb{Q}*{+}$ by the equation $$ g (n, m) = m / n. $$
- **Dependencies:** FC02-C01-U096.

### FC02-C01-U117

- **Kind:** Theorem 7.5.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L2009.
- **Statement/data:** A countable union of countable sets is countable.
- **Dependencies:** FC02-C01-U096, FC02-C01-U111, FC02-C01-U115.

### FC02-C01-U118

- **Kind:** Theorem 7.6.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L2027.
- **Statement/data:** A finite product of countable sets is countable.
- **Dependencies:** FC02-C01-U096, FC02-C01-U115.

### FC02-C01-U119

- **Kind:** Theorem 7.7.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L2047.
- **Statement/data:** Let $X$ denote the two element set ${0,1}$ . Then the set $X^{\omega}$ is uncountable.
- **Dependencies:** FC02-C01-U096, FC02-C01-U117.

### FC02-C01-U120

- **Kind:** Theorem 7.8.
- **Locator:** §7 “Countable and Uncountable Sets”; printed pp. 44–51; extraction L2073.
- **Statement/data:** Let $A$ be a set. There is no injective map $f: \mathcal{P}(A) \to A$ , and there is no surjective map $g: A \to \mathcal{P}(A)$ .
- **Dependencies:** FC02-C01-U022, FC02-C01-U039, FC02-C01-U096.

### FC02-C01-U121

- **Kind:** Lemma 8.1.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2189.
- **Statement/data:** Given $n \in \mathbb{Z}_{+}$ , there exists a function $$ f: {1, \dots , n } \rightarrow C $$ that satisfies (*) for all i in its domain.
- **Dependencies:** FC02-C01-U033, FC02-C01-U083, FC02-C01-U113.

### FC02-C01-U122

- **Kind:** Lemma 8.2.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2225.
- **Statement/data:** Suppose that $f: {1, \ldots, n} \to C$ and $g: {1, \ldots, m} \to C$ both satisfy (*) for all $i$ in their respective domains. Then $f(i) = g(i)$ for all $i$ in both domains.
- **Dependencies:** FC02-C01-U033, FC02-C01-U113, FC02-C01-U121.

### FC02-C01-U123

- **Kind:** Theorem 8.3.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2245.
- **Statement/data:** There exists a unique function $h: \mathbb{Z}*+ \to C$ satisfying (*) for all $i \in \mathbb{Z}*+$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U113, FC02-C01-U121, FC02-C01-U122.

### FC02-C01-U124

- **Kind:** Theorem 8.4.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2263.
- **Statement/data:** (Principle of recursive definition). Let A be a set; let $a_{0}$ be an element of A. Suppose $\rho$ is a function that assigns, to each function f mapping a nonempty section of the positive integers into A, an element of A. Then there exists a unique function $$ h: \mathbb {Z} _ {+} \rightarrow A $$ such that (*) $$ \begin{array}{l} h (1) = a _ {0}, \ h (i) = \rho (h | {1, \ldots , i - 1 }) \quad \text { for } i > 1. \end{array} $$ The formula (*) is called a recursion formula for h. It specifies $h(1)$ , and it expresses the value of h at i > 1 in terms of the values of h for positive integers less than i.
- **Dependencies:** FC02-C01-U033, FC02-C01-U113, FC02-C01-U123.

### FC02-C01-U125

- **Kind:** Definition.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2277.
- **Statement/data:** A recursion formula specifies the initial value and expresses each later value in terms of earlier values.
- **Dependencies:** —.

### FC02-C01-U126

- **Kind:** Example 1.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2279.
- **Statement/data:** Let us show that Theorem 8.3 is a special case of this theorem. Given the infinite subset $C$ of $\mathbb{Z}_{+}$ , let $a_0$ be the smallest element of $C$ , and define $\rho$ by the equation $$ \rho (f) = \text { smallest element of } [ C - (\text { image set of } f) ]. $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U113.

### FC02-C01-U127

- **Kind:** Example 2.
- **Locator:** *§8 “The Principle of Recursive Definition”; printed pp. 52–56; extraction L2293.
- **Statement/data:** Given $a \in \mathbb{R}$ , we "defined" $a^n$ , in the exercises of §4, by the recursion formula $$ \begin{array}{l} a ^ {1} = a, \ a ^ {n} = a ^ {n - 1} \cdot a. \end{array} $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U113.

### FC02-C01-U128

- **Kind:** Theorem 9.1.
- **Locator:** §9 “Infinite Sets and the Axiom of Choice”; printed pp. 57–61; extraction L2371.
- **Statement/data:** Let $A$ be a set. The following statements about $A$ are equivalent: (1) There exists an injective function $f: \mathbb{Z}_+ \to A$ . (2) There exists a bijection of $A$ with a proper subset of itself. (3) $A$ is infinite.
- **Dependencies:** FC02-C01-U100, FC02-C01-U106, FC02-C01-U124.

### FC02-C01-U129

- **Kind:** Axiom of choice.
- **Locator:** §9 “Infinite Sets and the Axiom of Choice”; printed pp. 57–61; extraction L2440.
- **Statement/data:** Given a collection of disjoint nonempty sets, there exists a set containing exactly one element from each member.
- **Dependencies:** —.

### FC02-C01-U130

- **Kind:** Lemma 9.2.
- **Locator:** §9 “Infinite Sets and the Axiom of Choice”; printed pp. 57–61; extraction L2446.
- **Statement/data:** (Existence of a choice function). Given a collection B of nonempty sets (not necessarily disjoint), there exists a function $$ c: \mathcal {B} \longrightarrow \bigcup_ {B \in \mathcal {B}} B $$ such that $c(B)$ is an element of $B$ , for each $B \in \mathcal{B}$ . The function $c$ is called a choice function for the collection $\mathcal{B}$ . The difference between this lemma and the axiom of choice is that in this lemma the sets of the collection B are not required to be disjoint. For example, one can allow B to be the collection of all nonempty subsets of a given set.
- **Dependencies:** FC02-C01-U106, FC02-C01-U124, FC02-C01-U129.

### FC02-C01-U131

- **Kind:** Definition.
- **Locator:** §9 “Infinite Sets and the Axiom of Choice”; printed pp. 57–61; extraction L2454.
- **Statement/data:** A function choosing one element $c(B)\in B$ for every nonempty set $B$ in a collection is a choice function.
- **Dependencies:** FC02-C01-U129.

### FC02-C01-U132

- **Kind:** Convention/comparison.
- **Locator:** §9 “Infinite Sets and the Axiom of Choice”; printed pp. 57–61; extraction L2514.
- **Statement/data:** Finite choice is the finite-family version; “the axiom of choice” refers to the unrestricted arbitrary-family form.
- **Dependencies:** FC02-C01-U129.

### FC02-C01-U133

- **Kind:** Definition.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2576.
- **Statement/data:** A set $A$ with an order relation $<$ is said to be well-ordered if every nonempty subset of $A$ has a smallest element.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U134

- **Kind:** Example 1.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2578.
- **Statement/data:** Consider the set ${1,2} \times \mathbb{Z}_{+}$ in the dictionary ordering. Schematically, it can be represented as one infinite sequence followed by another infinite sequence: $$ a _ {1}, a _ {2}, a _ {3}, \dots ; b _ {1}, b _ {2}, b _ {3}, \dots $$
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U135

- **Kind:** Example 2.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2586.
- **Statement/data:** Consider the set $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ in the dictionary order. Schematically, it can be represented as an infinite sequence of infinite sequences. We show that it is well-ordered. Let $X$ be a nonempty subset of $\mathbb{Z}*{+} \times \mathbb{Z}*{+}$ . Let $A$ be the subset of $\mathbb{Z}*{+}$ consisting of all first coordinates of elements of $X$ . Now $A$ has a smallest element; call it $a*{0}$ . Then the collection $$ {b \mid a _ {0} \times b \in X } $$
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U136

- **Kind:** Example 3.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2597.
- **Statement/data:** The set of integers is not well-ordered in the usual order; the subset consisting of the negative integers has no smallest element. Nor is the set of real numbers in the interval $0 \leq x \leq 1$ well-ordered; the subset consisting of those $x$ for which $0 < x < 1$ has no smallest element (although it has a greatest lower bound, of course).
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U137

- **Kind:** Theorem 10.1.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2617.
- **Statement/data:** Every nonempty finite ordered set has the order type of a section ${1, \ldots, n}$ of $\mathbb{Z}_+$ , so it is well-ordered.
- **Dependencies:** FC02-C01-U059, FC02-C01-U133.

### FC02-C01-U138

- **Kind:** Theorem (Well-ordering.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2671.
- **Statement/data:** theorem). If $A$ is a set, there exists an order relation on $A$ that is a well-ordering. This theorem was proved by Zermelo in 1904, and it startled the mathematical world. There was considerable debate as to the correctness of the proof; the lack of any constructive procedure for well-ordering an arbitrary uncountable set led many to be skeptical. When the proof was analyzed closely, the only point at which it was found that there might be some question was a construction involving an infinite number of arbitrary choices, that is, a construction involving—the choice axiom. Some mathematicians rejected the choice axiom as a result, and for many years a legitimate question about a new theorem was: Does its proof involve the choice axiom or not? A theorem was considered to be on somewhat shaky ground if one had to use the choice axiom in its proof. Present-day mathematicians, by and large, do not have such qualms. They accept the axiom of choice as a reasonable assumption about set theory, and they accept the well-ordering theorem along with it.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U139

- **Kind:** Corollary.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2681.
- **Statement/data:** There exists an uncountable well-ordered set. We now use this result to construct a particular well-ordered set that will prove to be very useful.
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U140

- **Kind:** Definition.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2685.
- **Statement/data:** Let $X$ be a well-ordered set Given $\alpha \in X$ , let $S_{\alpha}$ denote the set $$ S _ {\alpha} = {x \mid x \in X \text { and } x < \alpha }. $$ It is called the section of $X$ by $\alpha$ .
- **Dependencies:** FC02-C01-U059.

### FC02-C01-U141

- **Kind:** Definition/notation.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2691.
- **Statement/data:** For well-ordered $X$ and $\alpha\in X$, the section $S_\alpha$ is the set of elements preceding $\alpha$.
- **Dependencies:** —.

### FC02-C01-U142

- **Kind:** Lemma 10.2.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2693.
- **Statement/data:** There exists a well-ordered set $A$ having a largest element $\Omega$ , such that the section $S_{\Omega}$ of $A$ by $\Omega$ is uncountable but every other section of $A$ is countable.
- **Dependencies:** FC02-C01-U059, FC02-C01-U138, FC02-C01-U139.

### FC02-C01-U143

- **Kind:** Definition/notation.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2697.
- **Statement/data:** $S_\Omega$ denotes the minimal uncountable well-ordered set; $\bar S_\Omega=S_\Omega\cup{\Omega}$ (extraction glyph varies) denotes it with a largest point adjoined.
- **Dependencies:** —.

### FC02-C01-U144

- **Kind:** Theorem 10.3.
- **Locator:** §10 “Well-Ordered Sets”; printed pp. 62–67; extraction L2701.
- **Statement/data:** If $A$ is a countable subset of $S_{\Omega}$ , then $A$ has an upper bound in $S_{\Omega}$
- **Dependencies:** FC02-C01-U059, FC02-C01-U142.

### FC02-C01-U145

- **Kind:** Definition.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2779.
- **Statement/data:** A strict partial order is nonreflexive and transitive; comparability is not required.
- **Dependencies:** —.

### FC02-C01-U146

- **Kind:** Definition.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2787.
- **Statement/data:** A subset of a strictly partially ordered set is simply ordered when every pair of distinct elements is comparable; it is maximal if no strictly larger subset is simply ordered.
- **Dependencies:** FC02-C01-U145.

### FC02-C01-U147

- **Kind:** Theorem (The.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2791.
- **Statement/data:** maximum principle). Let $A$ be a set; let $\prec$ be a strict partial order on $A$ . Then there exists a maximal simply ordered subset $B$ of $A$ . Said differently, there exists a subset B of A such that B is simply ordered by $\prec$ and such that no subset of A that properly contains B is simply ordered by $\prec$ .
- **Dependencies:** FC02-C01-U138, FC02-C01-U145.

### FC02-C01-U148

- **Kind:** Example 1.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2795.
- **Statement/data:** If A is any collection of sets, the relation “is a proper subset of” is a strict partial order on A. Suppose that A is the collection of all circular regions (interiors of circles) in the plane. One maximal simply ordered subcollection of A consists of all circular regions with centers at the origin Another maximal simply ordered subcollection consists of all circular regions bounded by circles tangent from the right to the y-axis at the origin See Figure 11.
- **Dependencies:** FC02-C01-U138, FC02-C01-U145.

### FC02-C01-U149

- **Kind:** Example 2.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2803.
- **Statement/data:** If $(x_0, y_0)$ and $(x_1, y_1)$ are two points of the plane $\mathbb{R}^2$ , define $$ (x _ {0}, y _ {0}) \prec (x _ {1}, y _ {1}) $$
- **Dependencies:** FC02-C01-U138, FC02-C01-U145.

### FC02-C01-U150

- **Kind:** Definition.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2829.
- **Statement/data:** For a strict partial order, an upper bound of $B$ dominates every element of $B$; a maximal element has no strictly larger element.
- **Dependencies:** FC02-C01-U145.

### FC02-C01-U151

- **Kind:** Definition.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2829.
- **Statement/data:** Let A be a set and let $\prec$ be a strict partial order on A. If B is a subset of A, an upper bound on B is an element c of A such that for every b in B, either b = c or $b \prec c$ . A maximal element of A is an element m of A such that for no element a of A does the relation $m \prec a$ hold.
- **Dependencies:** FC02-C01-U138, FC02-C01-U145.

### FC02-C01-U152

- **Kind:** Zorn's Lemma.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2831.
- **Statement/data:** If every simply ordered subset of a strictly partially ordered set has an upper bound, then the set has a maximal element.
- **Dependencies:** FC02-C01-U147.

### FC02-C01-U153

- **Kind:** Definition.
- **Locator:** *§11 “The Maximum Principle”; printed pp. 68–71; extraction L2837.
- **Statement/data:** The reflexive relation $a\preceq b$ iff $a\prec b$ or $a=b$ associated to a strict partial order is called a partial order.
- **Dependencies:** FC02-C01-U145.

## C02 — Topological Spaces and Continuous Functions

Units: 151.

### FC02-C02-U001

- **Kind:** Definition.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L2991.
- **Statement/data:** A topology on a set $X$ is a collection $\mathcal{T}$ of subsets of $X$ having the following properties: (1) $\varnothing$ and $X$ are in $\mathcal{T}$ . (2) The union of the elements of any subcollection of $\mathcal{T}$ is in $\mathcal{T}$ . (3) The intersection of the elements of any finite subcollection of $\mathcal{T}$ is in $\mathcal{T}$ . A set X for which a topology T has been specified is called a topological space. Properly speaking, a topological space is an ordered pair $(X, \mathcal{T})$ consisting of a set X and a topology T on X, but we often omit specific mention of T if no confusion will arise. If X is a topological space with topology T, we say that a subset U of X is an open set of X if U belongs to the collection T. Using this terminology, one can say that a topological space is a set X together with a collection of subsets of X, called open sets, such that $\varnothing$ and X are both open, and such that arbitrary unions and finite intersections of open sets are open.
- **Dependencies:** —.

### FC02-C02-U002

- **Kind:** Definition.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L2999.
- **Statement/data:** A set with a specified topology is a topological space; members of the topology are its open sets.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U003

- **Kind:** Example 1.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L3005.
- **Statement/data:** Let $X$ be a three-element set, $X = {a, b, c}$ . There are many possible topologies on $X$ , some of which are indicated schematically in Figure 12.1. The diagram in the upper right-hand corner indicates the topology in which the open sets are $X, \varnothing, {a, b}, {b}$ , and ${b, c}$ . The topology in the upper left-hand corner contains only $X$ and $\varnothing$ , while the topology in the lower right-hand corner contains every subset of $X$ . You can get other topologies on $X$ by permuting $a, b$ , and $c$
- **Dependencies:** —.

### FC02-C02-U004

- **Kind:** Example 2.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L3031.
- **Statement/data:** If $X$ is any set, the collection of all subsets of $X$ is a topology on $X$ , it is called the discrete topology. The collection consisting of $X$ and $\varnothing$ only is also a topology on $X$ ; we shall call it the indiscrete topology, or the trivial topology
- **Dependencies:** —.

### FC02-C02-U005

- **Kind:** Example 3.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L3033.
- **Statement/data:** Let $X$ be a set; let $\mathcal{T}_f$ be the collection of all subsets $U$ of $X$ such that $X - U$ either is finite or is all of $X$ . Then $\mathcal{T}_f$ is a topology on $X$ , called the finite complement topology. Both $X$ and $\varnothing$ are in $\mathcal{T}*f$ , since $X - X$ is finite and $X - \varnothing$ is all of $X$ . If ${U*\alpha}$ is an indexed family of nonempty elements of $\mathcal{T}*f$ , to show that $\bigcup U*\alpha$ is in $\mathcal{T}_f$ , we compute $$ X - \bigcup U _ {\alpha} = \bigcap (X - U _ {\alpha}). $$
- **Dependencies:** —.

### FC02-C02-U006

- **Kind:** Example 4.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L3047.
- **Statement/data:** Let X be a set; let $T_{c}$ be the collection of all subsets U of X such that X - U either is countable or is all of X. Then $T_{c}$ is a topology on X, as you can check
- **Dependencies:** —.

### FC02-C02-U007

- **Kind:** Definition.
- **Locator:** §12 “Topological Spaces”; printed pp. 75–77; extraction L3049.
- **Statement/data:** Suppose that $\mathcal{T}$ and $\mathcal{T}'$ are two topologies on a given set $X$ . If $\mathcal{T}' \supset \mathcal{T}$ , we say that $\mathcal{T}'$ is finer than $\mathcal{T}$ ; if $\mathcal{T}'$ properly contains $\mathcal{T}$ , we say that $\mathcal{T}'$ is strictly finer than $\mathcal{T}$ . We also say that $\mathcal{T}$ is coarser than $\mathcal{T}'$ , or strictly coarser, in these two respective situations. We say $\mathcal{T}$ is comparable with $\mathcal{T}'$ if either $\mathcal{T}' \supset \mathcal{T}$ or $\mathcal{T} \supset \mathcal{T}'$ .
- **Dependencies:** —.

### FC02-C02-U008

- **Kind:** Definition.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3063.
- **Statement/data:** If $X$ is a set, a basis for a topology on $X$ is a collection $\mathcal{B}$ of subsets of $X$ (called basis elements) such that (1) For each $x \in X$ , there is at least one basis element $B$ containing $x$ . (2) If $x$ belongs to the intersection of two basis elements $B_{1}$ and $B_{2}$ , then there is a basis element $B_{3}$ containing $x$ such that $B_{3} \subset B_{1} \cap B_{2}$ . If $\mathcal{B}$ satisfies these two conditions, then we define the topology $\mathcal{T}$ generated by $\mathcal{B}$ as follows: A subset $U$ of $X$ is said to be open in $X$ (that is, to be an element of $\mathcal{T}$ ) if for each $x \in U$ , there is a basis element $B \in \mathcal{B}$ such that $x \in B$ and $B \subset U$ . Note that each basis element is itself an element of $\mathcal{T}$ . We will check shortly that the collection $\mathcal{T}$ is indeed a topology on $X$ . But first let us consider some examples.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U009

- **Kind:** Construction.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3069.
- **Statement/data:** A basis $\mathcal B$ generates the topology whose open sets $U$ satisfy: every $x\in U$ lies in some $B\in\mathcal B$ with $B\subset U$.
- **Dependencies:** FC02-C02-U008.

### FC02-C02-U010

- **Kind:** Example 1.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3073.
- **Statement/data:** Let B be the collection of all circular regions (internors of circles) in the plane. Then B satisfies both conditions for a basis. The second condition is illustrated in Figure 13 1. In the topology generated by B, a subset U of the plane is open if every x in U lies in some circular region contained in U
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U011

- **Kind:** Example 2.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3081.
- **Statement/data:** Let $\mathcal{B}'$ be the collection of all rectangular regions (internors of rectangles) in the plane, where the rectangles have sides parallel to the coordinate axes. Then $\mathcal{B}'$ satisfies both conditions for a basis. The second condition is illustrated in Figure 13 2; in this case, the condition is trivial, because the intersection of any two basis elements is itself a basis element (or empty). As we shall see later, the basis $\mathcal{B}'$ generates the same topology on the plane as the basis $\mathcal{B}$ given in the preceding example
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U012

- **Kind:** Example 3.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3083.
- **Statement/data:** If $X$ is any set, the collection of all one-point subsets of $X$ is a basis for the discrete topology on $X$ Let us check now that the collection $\mathcal{T}$ generated by the basis $\mathcal{B}$ is, in fact, a topology on $X$ . If $U$ is the empty set, it satisfies the defining condition of openness vacuously. Likewise, $X$ is in $\mathcal{T}$ , since for each $x \in X$ there is some basis element $B$ containing $x$ and contained in $X$ . Now let us take an indexed family ${U_{\alpha}}*{\alpha \in J}$ , of elements of $\mathcal{T}$ and show that $$ U = \bigcup* {\alpha \in J} U _ {\alpha} $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U013

- **Kind:** Lemma 13.1.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3110.
- **Statement/data:** Let X be a set; let B be a basis for a topology T on X. Then T equals the collection of all unions of elements of B.
- **Dependencies:** FC02-C02-U001, FC02-C02-U008.

### FC02-C02-U014

- **Kind:** Lemma 13.2.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3118.
- **Statement/data:** Let X be a topological space. Suppose that C is a collection of open sets of X such that for each open set U of X and each x in U, there is an element C of C such that $x \in C \subset U$ . Then C is a basis for the topology of X.
- **Dependencies:** FC02-C02-U001, FC02-C02-U008.

### FC02-C02-U015

- **Kind:** Lemma 13.3.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3126.
- **Statement/data:** Let $\mathcal{B}$ and $\mathcal{B}'$ be bases for the topologies $\mathcal{T}$ and $\mathcal{T}'$ , respectively, on $X$ . Then the following are equivalent: (1) $\mathcal{T}'$ is finer than $\mathcal{T}$ . (2) For each $x \in X$ and each basis element $B \in \mathcal{B}$ containing $x$ , there is a basis element $B' \in \mathcal{B}'$ such that $x \in B' \subset B$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U008.

### FC02-C02-U016

- **Kind:** Example 4.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3138.
- **Statement/data:** One can now see that the collection B of all circular regions in the plane generates the same topology as the collection $B'$ of all rectangular regions, Figure 13.4 illustrates the proof We shall treat this example more formally when we study metric spaces We now define three topologies on the real line R, all of which are of interest.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U017

- **Kind:** Definition.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3145.
- **Statement/data:** If B is the collection of all open intervals in the real line, $$ (a, b) = {x \mid a < x < b }, $$ the topology generated by B is called the standard topology on the real line. Whenever we consider R, we shall suppose it is given this topology unless we specifically state otherwise. If $B'$ is the collection of all half-open intervals of the form $$ [ a, b) = {x \mid a \leq x < b }, $$ where $a < b$ , the topology generated by $\mathcal{B}'$ is called the lower limit topology on $\mathbb{R}$ . When $\mathbb{R}$ is given the lower limit topology, we denote it by $\mathbb{R}*{\ell}$ . Finally let $K$ denote the set of all numbers of the form $1/n$ , for $n \in \mathbb{Z}*{+}$ , and let $\mathcal{B}''$ be the collection of all open intervals $(a, b)$ , along with all sets of the form $(a, b) - K$ . The topology generated by $\mathcal{B}''$ will be called the $K$ -topology on $\mathbb{R}$ . When $\mathbb{R}$ is given this topology, we denote it by $\mathbb{R}_{K}$ .
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U018

- **Kind:** Definition/notation.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3151.
- **Statement/data:** The basis of all open intervals generates the standard topology on $\mathbb R$.
- **Dependencies:** —.

### FC02-C02-U019

- **Kind:** Definition/notation.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3157.
- **Statement/data:** Half-open intervals $[a,b)$ generate the lower-limit topology; the resulting line is denoted $\mathbb R_\ell$.
- **Dependencies:** —.

### FC02-C02-U020

- **Kind:** Definition/notation.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3159.
- **Statement/data:** The basis of open intervals and sets $(a,b)-K$, $K={1/n}$, generates the $K$-topology on $\mathbb R$, denoted $\mathbb R_K$.
- **Dependencies:** —.

### FC02-C02-U021

- **Kind:** Lemma 13.4.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3161.
- **Statement/data:** The topologies of $\mathbb{R}_{\ell}$ and $\mathbb{R}_K$ are strictly finer than the standard topology on $\mathbb{R}$ , but are not comparable with one another.
- **Dependencies:** FC02-C02-U001, FC02-C02-U018, FC02-C02-U019, FC02-C02-U020.

### FC02-C02-U022

- **Kind:** Definition.
- **Locator:** §13 “Basis for a Topology”; printed pp. 78–83; extraction L3171.
- **Statement/data:** A subbasis S for a topology on X is a collection of subsets of X whose union equals X. The topology generated by the subbasis S is defined to be the collection T of all unions of finite intersections of elements of S.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U023

- **Kind:** Definition.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3251.
- **Statement/data:** In an ordered set, intervals determined by $a<b$ are $(a,b)$, $(a,b]$, $[a,b)$, and $[a,b]$.
- **Dependencies:** —.

### FC02-C02-U024

- **Kind:** Definition.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3259.
- **Statement/data:** For a simply ordered set X with more than one point, the basis consisting of all open intervals, together with half-open initial/final intervals when X has a smallest/largest element, generates the order topology.
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U025

- **Kind:** Example 1.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3271.
- **Statement/data:** The standard topology on $\mathbb{R}$ , as defined in the preceding section, is just the order topology derived from the usual order on $\mathbb{R}$ .
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U026

- **Kind:** Example 2.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3273.
- **Statement/data:** Consider the set $\mathbb{R} \times \mathbb{R}$ in the dictionary order; we shall denote the general element of $\mathbb{R} \times \mathbb{R}$ by $x \times y$ , to avoid difficulty with notation. The set $\mathbb{R} \times \mathbb{R}$ has neither a largest nor a smallest element, so the order topology on $\mathbb{R} \times \mathbb{R}$ has as basis the collection of all open intervals of the form $(a \times b, c \times d)$ for $a < c$ , and for $a = c$ and $b < d$ . These two types of intervals are indicated in Figure 14.1. The subcollection consisting of only intervals of the second type is also a basis for the order topology on $\mathbb{R} \times \mathbb{R}$ , as you can check
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U027

- **Kind:** Example 3.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3277.
- **Statement/data:** The positive integers $\mathbb{Z}*{+}$ form an ordered set with a smallest element. The order topology on $\mathbb{Z}*{+}$ is the discrete topology, for every one-point set is open If $n > 1$ , then the one-point set ${n} = (n - 1, n + 1)$ is a basis element; and if $n = 1$ , the one-point set ${1} = [1, 2)$ is a basis element.
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U028

- **Kind:** Example 4.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3279.
- **Statement/data:** The set $X = {1,2} \times \mathbb{Z}_+$ in the dictionary order is another example of an ordered set with a smallest element Denoting $1 \times n$ by $a_n$ and $2 \times n$ by $b_n$ , we can represent $X$ by $$ a _ {1}, a _ {2}, \dots ; b _ {1}, b _ {2}, \dots $$
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U029

- **Kind:** Definition.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3287.
- **Statement/data:** If X is an ordered set, and a is an element of X, there are four subsets of X that are called the rays determined by a. They are the following: $$ \begin{array}{l} (a, + \infty) = {x \mid x > a }, \ (- \infty , a) = {x \mid x < a }, \ [ a, + \infty) = {x \mid x \geq a }, \ (- \infty , a ] = {x \mid x \leq a }. \end{array} $$ Sets of the first two types are called open rays, and sets of the last two types are called closed rays. The use of the term “open” suggests that open rays in X are open sets in the order topology. And so they are. Consider, for example, the ray $(a, +\infty)$ . If X has a largest element $b_{0}$ , then $(a, +\infty)$ equals the basis element $(a, b_{0}]$ . If X has no largest element, then $(a, +\infty)$ equals the union of all basis elements of the form $(a, x)$ , for x > a. In either case, $(a, +\infty)$ is open. A similar argument applies to the ray $(-\infty, a)$ . The open rays, in fact, form a subbasis for the order topology on X, as we now show. Because the open rays are open in the order topology, the topology they generate is contained in the order topology. On the other hand, every basis element for the order topology equals a finite intersection of open rays; the interval $(a, b)$ equals the intersection of $(-\infty, b)$ and $(a, +\infty)$ , while $[a_{0}, b)$ and $(a, b_{0}]$ , if they exist, are themselves open rays. Hence the topology generated by the open rays contains the order topology
- **Dependencies:** FC02-C01-U059, FC02-C02-U008.

### FC02-C02-U030

- **Kind:** Definition.
- **Locator:** §14 “The Order Topology”; printed pp. 84–85; extraction L3293.
- **Statement/data:** The rays $(-\infty,a)$ and $(a,\infty)$ are open rays; $(-\infty,a]$ and $[a,\infty)$ are closed rays.
- **Dependencies:** FC02-C02-U029.

### FC02-C02-U031

- **Kind:** Definition.
- **Locator:** §15 “The Product Topology on $X \times Y$”; printed pp. 86–87; extraction L3303.
- **Statement/data:** Let X and Y be topological spaces. The product topology on $X \times Y$ is the topology having as basis the collection B of all sets of the form $U \times V$ , where U is an open subset of X and V is an open subset of Y.
- **Dependencies:** FC02-C01-U028, FC02-C02-U001.

### FC02-C02-U032

- **Kind:** Theorem 15.1.
- **Locator:** §15 “The Product Topology on $X \times Y$”; printed pp. 86–87; extraction L3317.
- **Statement/data:** If $\mathcal{B}$ is a basis for the topology of $X$ and $\mathcal{C}$ is a basis for the topology of $Y$ , then the collection $$ \mathcal {D} = {B \times C \mid B \in \mathcal {B} \text { and } C \in \mathcal {C} } $$ is a basis for the topology of $X \times Y$
- **Dependencies:** FC02-C01-U028, FC02-C02-U001, FC02-C02-U008, FC02-C02-U031.

### FC02-C02-U033

- **Kind:** Example 1.
- **Locator:** §15 “The Product Topology on $X \times Y$”; printed pp. 86–87; extraction L3329.
- **Statement/data:** We have a standard topology on $\mathbb{R}$ : the order topology The product of this topology with itself is called the standard topology on $\mathbb{R} \times \mathbb{R} = \mathbb{R}^2$ . It has as basis the collection of all products of open sets of $\mathbb{R}$ , but the theorem just proved tells us that the much smaller collection of all products $(a, b) \times (c, d)$ of open intervals in $\mathbb{R}$ will also serve as a basis for the topology of $\mathbb{R}^2$ . Each such set can be pictured as the interior of a rectangle in $\mathbb{R}^2$ . Thus the standard topology on $\mathbb{R}^2$ is just the one we considered in Example 2 of §13 It is sometimes useful to express the product topology in terms of a subbasis. To do this, we first define certain functions called projections.
- **Dependencies:** FC02-C01-U028, FC02-C02-U001.

### FC02-C02-U034

- **Kind:** Definition.
- **Locator:** §15 “The Product Topology on $X \times Y$”; printed pp. 86–87; extraction L3333.
- **Statement/data:** Let $\pi_1$ . $X \times Y \to X$ be defined by the equation $$ \pi_ {1} (x, y) = x; $$ let $\pi_2: X \times Y \to Y$ be defined by the equation $$ \pi_ {2} (x, y) = y. $$ The maps $\pi_1$ and $\pi_2$ are called the projections of $X \times Y$ onto its first and second factors, respectively.
- **Dependencies:** FC02-C01-U028, FC02-C02-U001.

### FC02-C02-U035

- **Kind:** Theorem 15.2.
- **Locator:** §15 “The Product Topology on $X \times Y$”; printed pp. 86–87; extraction L3357.
- **Statement/data:** The collection $$ \mathcal {S} = {\pi_ {1} ^ {- 1} (U) \mid U \text { open in } X } \cup {\pi_ {2} ^ {- 1} (V) \mid V \text { open in } Y } $$ is a subbasis for the product topology on $X \times Y$ .
- **Dependencies:** FC02-C01-U028, FC02-C02-U001, FC02-C02-U022, FC02-C02-U034.

### FC02-C02-U036

- **Kind:** Definition.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3377.
- **Statement/data:** Let $X$ be a topological space with topology $\mathcal{T}$ . If $Y$ is a subset of $X$ , the collection $$ \mathcal {T} _ {Y} = {Y \cap U \mid U \in \mathcal {T} } $$ is a topology on $Y$ , called the subspace topology. With this topology, $Y$ is called a subspace of $X$ ; its open sets consist of all intersections of open sets of $X$ with $Y$ .
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U037

- **Kind:** Lemma 16.1.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3397.
- **Statement/data:** If B is a basis for the topology of X then the collection $$ \mathcal {B} _ {Y} = {B \cap Y \mid B \in \mathcal {B} } $$ is a basis for the subspace topology on $Y$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U008, FC02-C02-U036.

### FC02-C02-U038

- **Kind:** Lemma 16.2.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3411.
- **Statement/data:** Let $Y$ be a subspace of $X$ . If $U$ is open in $Y$ and $Y$ is open in $X$ , then $U$ is open in $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U036.

### FC02-C02-U039

- **Kind:** Theorem 16.3.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3417.
- **Statement/data:** If $A$ is a subspace of $X$ and $B$ is a subspace of $Y$ , then the product topology on $A \times B$ is the same as the topology $A \times B$ inherits as a subspace of $X \times Y$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U031, FC02-C02-U036.

### FC02-C02-U040

- **Kind:** Example 1.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3431.
- **Statement/data:** Consider the subset $Y = [0,1]$ of the real line $\mathbb{R}$ , in the subspace topology. The subspace topology has as basis all sets of the form $(a,b) \cap Y$ , where $(a,b)$ is an open interval in $\mathbb{R}$ . Such a set is of one of the following types: $$ (a, b) \cap Y = \left{ \begin{array}{l l} (a, b) & \text { if } a \text { and } b \text { are in } Y, \ [ 0, b) & \text { if only } b \text { is in } Y, \ (a, 1 ] & \text { if only } a \text { is in } Y, \ Y \text { or } \varnothing & \text { if neither } a \text { nor } b \text { is in } Y. \end{array} \right. $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U041

- **Kind:** Example 2.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3441.
- **Statement/data:** Let Y be the subset $[0,1)\cup{2}$ of R. In the subspace topology on Y the one-point set ${2}$ is open, because it is the intersection of the open set $(\frac{3}{2},\frac{5}{2})$ with Y. But in the order topology on Y, the set ${2}$ is not open. Any basis element for the order topology on Y that contains 2 is of the form $$ {x \mid x \in Y \text { and } a < x \leq 2 } $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U042

- **Kind:** Example 3.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3449.
- **Statement/data:** Let $I = [0,1]$ . The dictionary order on $I \times I$ is just the restriction to $I \times I$ of the dictionary order on the plane $\mathbb{R} \times \mathbb{R}$ . However, the dictionary order topology on $I \times I$ is not the same as the subspace topology on $I \times I$ obtained from the dictionary order topology on $\mathbb{R} \times \mathbb{R}!$ . For example, the set ${1/2} \times (1/2,1]$ is open in $I \times I$ in the subspace topology, but not in the order topology, as you can check. See Figure 16.1.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U043

- **Kind:** Named construction.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3451.
- **Statement/data:** The set $I\times I$ with the dictionary order topology is the ordered square, denoted $I_o^2$.
- **Dependencies:** —.

### FC02-C02-U044

- **Kind:** Theorem 16.4.
- **Locator:** §16 “The Subspace Topology”; printed pp. 88–91; extraction L3462.
- **Statement/data:** Let $X$ be an ordered set in the order topology; let $Y$ be a subset of $X$ that is convex in $X$ . Then the order topology on $Y$ is the same as the topology $Y$ inherits as a subspace of $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U024, FC02-C02-U036.

### FC02-C02-U045

- **Kind:** Definition.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3536.
- **Statement/data:** A subset $A$ of a topological space $X$ is closed iff $X-A$ is open.
- **Dependencies:** —.

### FC02-C02-U046

- **Kind:** Example 1.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3538.
- **Statement/data:** The subset $[a, b]$ of $\mathbb{R}$ is closed because its complement $$ \mathbb {R} - [ a, b ] = (- \infty , a) \cup (b, + \infty), $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U047

- **Kind:** Example 2.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3546.
- **Statement/data:** In the plane $\mathbb{R}^2$ , the set $$ {x \times y \mid x \geq 0 \text { and } y \geq 0 } $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U048

- **Kind:** Example 3.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3560.
- **Statement/data:** In the finite complement topology on a set X, the closed sets consist of X itself and all finite subsets of X
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U049

- **Kind:** Example 4.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3562.
- **Statement/data:** In the discrete topology on the set X, every set is open; it follows that every set is closed as well.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U050

- **Kind:** Example 5.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3564.
- **Statement/data:** Consider the following subset of the real line: $$ Y = [ 0, 1 ] \cup (2, 3), $$
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U051

- **Kind:** Theorem 17.1.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3576.
- **Statement/data:** Let $X$ be a topological space. Then the following conditions hold: (1) $\varnothing$ and $X$ are closed. (2) Arbitrary intersections of closed sets are closed. (3) Finite unions of closed sets are closed.
- **Dependencies:** FC02-C02-U001, FC02-C02-U045.

### FC02-C02-U052

- **Kind:** Theorem 17.2.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3606.
- **Statement/data:** Let Y be a subspace of X. Then a set A is closed in Y if and only if it equals the intersection of a closed set of X with Y.
- **Dependencies:** FC02-C02-U001, FC02-C02-U036, FC02-C02-U045.

### FC02-C02-U053

- **Kind:** Theorem 17.3.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3615.
- **Statement/data:** Let $Y$ be a subspace of $X$ . If $A$ is closed in $Y$ and $Y$ is closed in $X$ , then $A$ is closed in $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U052.

### FC02-C02-U054

- **Kind:** Definition/notation.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3619.
- **Statement/data:** The interior of $A$ is the union of all open subsets of $A$; the closure is the intersection of all closed supersets. Write $\operatorname{Int}A$ and $\operatorname{Cl}A$ or $\bar A$.
- **Dependencies:** FC02-C02-U045.

### FC02-C02-U055

- **Kind:** Theorem 17.4.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3633.
- **Statement/data:** Let Y be a subspace of X, let A be a subset of Y, let $\tilde{A}$ denote the closure of A in X. Then the closure of A in Y equals $\tilde{A} \cap Y$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U052, FC02-C02-U054.

### FC02-C02-U056

- **Kind:** Terminology.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3641.
- **Statement/data:** Sets $A,B$ intersect iff $A\cap B\ne\varnothing$.
- **Dependencies:** —.

### FC02-C02-U057

- **Kind:** Theorem 17.5.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3643.
- **Statement/data:** Let $A$ be a subset of the topological space $X$ . (a) Then $x \in \tilde{A}$ if and only if every open set $U$ containing $x$ intersects $A$ . (b) Supposing the topology of $X$ is given by a basis, then $x \in A$ if and only if every basis element $B$ containing $x$ intersects $A$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U054.

### FC02-C02-U058

- **Kind:** Terminology.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3659.
- **Statement/data:** An open set containing $x$ is a neighborhood of $x$ (this is Munkres’s convention).
- **Dependencies:** —.

### FC02-C02-U059

- **Kind:** Example 6.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3665.
- **Statement/data:** Let $X$ be the real line $\mathbb{R}$ . If $A = (0,1]$ , then $\tilde{A} = [0,1]$ , for every neighborhood of 0 intersects $A$ , while every point outside $[0,1]$ has a neighborhood disjoint from $A$ . Similar arguments apply to the following subsets of $X$ If $B = {1 / n \mid n \in \mathbb{Z}*+}$ , then $\tilde{B} = {0} \cup B$ . If $C = {0} \cup (1, 2)$ , then $\tilde{C} = {0} \cup [1, 2]$ . If $\mathbb{Q}$ is the set of rational numbers, then $\tilde{\mathbb{Q}} = \mathbb{R}$ . If $\mathbb{Z}*+$ is the set of positive integers, then $\tilde{\mathbb{Z}}*+ = \mathbb{Z}*+$ . If $\mathbb{R}*+$ is the set of positive reals, then the closure of $\mathbb{R}*+$ is the set $\mathbb{R}*+ \cup {0}$ . (This is the reason we introduced the notation $\tilde{\mathbb{R}}*+$ for the set $\mathbb{R}_+ \cup {0}$ , back in §2)
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U060

- **Kind:** Example 7.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3669.
- **Statement/data:** Consider the subspace $Y = (0,1]$ of the real line $\mathbb{R}$ . The set $A = (0,\frac{1}{2})$ is a subset of $Y$ , its closure in $\mathbb{R}$ is the set $[0,\frac{1}{2}]$ , and its closure in $Y$ is the set $[0,\frac{1}{2}] \cap Y = (0,\frac{1}{2}]$ Some mathematicians use the term "neighborhood" differently. They say that $A$ is a neighborhood of $x$ if $A$ merely contains an open set containing $x$ . We shall not follow this practice.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U061

- **Kind:** Definition.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3677.
- **Statement/data:** $x$ is a limit/cluster/accumulation point of $A$ iff every neighborhood of $x$ meets $A$ in a point other than $x$; equivalently $x\in\overline{A-{x}}$.
- **Dependencies:** FC02-C02-U054, FC02-C02-U058.

### FC02-C02-U062

- **Kind:** Example 8.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3679.
- **Statement/data:** Consider the real line $\mathbb{R}$ . If $A = (0,1]$ , then the point $0$ is a limit point of $A$ and so is the point $\frac{1}{2}$ . In fact, every point of the interval $[0,1]$ is a limit point of $A$ , but no other point of $\mathbb{R}$ is a limit point of $A$ If $B = {1 / n \mid n \in \mathbb{Z}*+}$ , then 0 is the only limit point of $B$ . Every other point $x$ of $\mathbb{R}$ has a neighborhood that either does not intersect $B$ at all, or it intersects $B$ only in the point $x$ itself. If $C = {0} \cup (1,2)$ , then the limit points of $C$ are the points of the interval [1, 2]. If $\mathbb{Q}$ is the set of rational numbers, every point of $\mathbb{R}$ is a limit point of $\mathbb{Q}$ . If $\mathbb{Z}*+$ is the set of positive integers, no point of $\mathbb{R}$ is a limit point of $\mathbb{Z}*+$ . If $\mathbb{R}*+$ is the set of positive reals, then every point of ${0} \cup \mathbb{R}*+$ is a limit point of $\mathbb{R}*+$ Comparison of Examples 6 and 8 suggests a relationship between the closure of a set and the limit points of a set. That relationship is given in the following theorem:
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U063

- **Kind:** Comparison.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3683.
- **Statement/data:** Comparison of closure examples and limit-point examples motivates $\bar A=A\cup A'$, formalized in Theorem 17.6.
- **Dependencies:** FC02-C02-U054, FC02-C02-U061.

### FC02-C02-U064

- **Kind:** Theorem 17.6.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3685.
- **Statement/data:** Let $A$ be a subset of the topological space $X$ , let $A'$ be the set of all limit points of $A$ . Then $$ \bar {A} = A \cup A ^ {\prime}. $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U054, FC02-C02-U061.

### FC02-C02-U065

- **Kind:** Corollary 17.7.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3695.
- **Statement/data:** A subset of a topological space is closed if and only if it contains all its limit points.
- **Dependencies:** FC02-C02-U001, FC02-C02-U064.

### FC02-C02-U066

- **Kind:** Definition.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3706.
- **Statement/data:** A sequence $x_n$ converges to $x$ iff every neighborhood of $x$ contains all sufficiently large $x_n$.
- **Dependencies:** FC02-C02-U058.

### FC02-C02-U067

- **Kind:** Definition.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3710.
- **Statement/data:** A topological space $X$ is called a Hausdorff space if for each pair $x_{1}, x_{2}$ of distinct points of $X$ , there exist neighborhoods $U_{1}$ , and $U_{2}$ of $x_{1}$ and $x_{2}$ , respectively, that are disjoint.
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U068

- **Kind:** Theorem 17.8.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3712.
- **Statement/data:** Every finite point set in a Hausdorff space $X$ is closed.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C02-U069

- **Kind:** Definition.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3716.
- **Statement/data:** $T_1$ means every finite point set (equivalently every singleton) is closed.
- **Dependencies:** FC02-C02-U045.

### FC02-C02-U070

- **Kind:** Theorem 17.9.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3718.
- **Statement/data:** Let X be a space satisfying the $T_{1}$ axiom; let A be a subset of X. Then the point x is a limit point of A if and only if every neighborhood of x contains infinitely many points of A.
- **Dependencies:** FC02-C02-U001, FC02-C02-U061, FC02-C02-U069.

### FC02-C02-U071

- **Kind:** Theorem 17.10.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3732.
- **Statement/data:** If $X$ is a Hausdorff space, then a sequence of points of $X$ converges to at most one point of $X$
- **Dependencies:** FC02-C02-U001, FC02-C02-U066, FC02-C02-U067.

### FC02-C02-U072

- **Kind:** Notation.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3736.
- **Statement/data:** In a Hausdorff space, write $x_n\to x$ and call $x$ the limit of the sequence.
- **Dependencies:** FC02-C02-U066, FC02-C02-U067.

### FC02-C02-U073

- **Kind:** Theorem 17.11.
- **Locator:** §17 “Closed Sets and Limit Points”; printed pp. 92–101; extraction L3740.
- **Statement/data:** Every simply ordered set is a Hausdorff space in the order topology. The product of two Hausdorff spaces is a Hausdorff space. A subspace of a Hausdorff space is a Hausdorff space. The Hausdorff condition is generally considered to be a very mild extra condition to impose on a topological space. Indeed, in a first course in topology some mathematicians go so far as to impose this condition at the outset, refusing to consider spaces that are not Hausdorff spaces. We shall not go this far, but we shall certainly assume the Hausdorff condition whenever it is needed in a proof without having any qualms about limiting seriously the range of applications of the results. The Hausdorff condition is one of a number of extra conditions one can impose on a topological space. Each time one imposes such a condition, one can prove stronger theorems, but one limits the class of spaces to which the theorems apply. Much of the research that has been done in topology since its beginnings has centered on the problem of finding conditions that will be strong enough to enable one to prove interesting theorems about spaces satisfying those conditions, and yet not so strong that they limit severely the range of applications of the results. We shall study a number of such conditions in the next two chapters. The Hausdorff condition and the $T_{1}$ axiom are but two of a collection of conditions similar to one another that are called collectively the separation axioms. Other conditions include the countability axioms, and various compactness and connectedness conditions. Some of these are quite stringent requirements, as you will see.
- **Dependencies:** FC02-C02-U001, FC02-C02-U024, FC02-C02-U031, FC02-C02-U036, FC02-C02-U067.

### FC02-C02-U074

- **Kind:** Definition.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3872.
- **Statement/data:** $f:X\to Y$ is continuous iff $f^{-1}(V)$ is open in $X$ for every open $V\subset Y$.
- **Dependencies:** FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U075

- **Kind:** Example 1.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3900.
- **Statement/data:** Let us consider a function like those studied in analysis, a "real-valued function of a real variable," $$ f \quad \mathbb {R} \longrightarrow \mathbb {R}. $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U076

- **Kind:** Example 2.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3912.
- **Statement/data:** In calculus one considers the property of continuity for many kinds of functions. For example, one studies functions of the following types: $f$ . $\mathbb{R} \longrightarrow \mathbb{R}^2$ (curves in the plane) $f$ . $\mathbb{R} \longrightarrow \mathbb{R}^3$ (curves in space) $f\quad \mathbb{R}^2\longrightarrow \mathbb{R}$ (functions $f(x,y)$ of two real variables) $f$ . $\mathbb{R}^3 \longrightarrow \mathbb{R}$ (functions $f(x, y, z)$ of three real variables) $f$ . $\mathbb{R}^2 \longrightarrow \mathbb{R}^2$ (vector fields $\mathbf{v}(x, y)$ in the plane). Each of them has a notion of continuity defined for it. Our general definition of continuity includes all these as special cases; this fact will be a consequence of general theorems we shall prove concerning continuous functions on product spaces and on metric spaces.
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U077

- **Kind:** Example 3.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3926.
- **Statement/data:** Let $\mathbb{R}$ denote the set of real numbers in its usual topology, and let $\mathbb{R}_{\ell}$ denote the same set in the lower limit topology. Let $$ f \quad \mathbb {R} \longrightarrow \mathbb {R} _ {\ell} $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U078

- **Kind:** Theorem 18.1.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3942.
- **Statement/data:** Let $X$ and $Y$ be topological spaces; let $f: X \to Y$ . Then the following are equivalent: (1) $f$ is continuous. (2) For every subset $A$ of $X$ , one has $f(\bar{A}) \subset \overline{f(A)}$ . (3) For every closed set $B$ of $Y$ , the set $f^{-1}(B)$ is closed in $X$ (4) For each $x \in X$ and each neighborhood $V$ of $f(x)$ , there is a neighborhood $U$ of $x$ such that $f(U) \subset V$ . If the condition in (4) holds for the point $x$ of $X$ , we say that $f$ is continuous at the point $x$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001, FC02-C02-U054, FC02-C02-U074.

### FC02-C02-U079

- **Kind:** Definition.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3986.
- **Statement/data:** A bijection $f:X\to Y$ is a homeomorphism when both $f$ and $f^{-1}$ are continuous.
- **Dependencies:** FC02-C01-U040, FC02-C02-U074.

### FC02-C02-U080

- **Kind:** Definition.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3993.
- **Statement/data:** A property expressible entirely in terms of the topology and hence invariant under homeomorphism is a topological property.
- **Dependencies:** FC02-C02-U079.

### FC02-C02-U081

- **Kind:** Definition.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3997.
- **Statement/data:** An injective continuous $f:X\to Y$ is an imbedding if $X\to f(X)$ is a homeomorphism onto the image with its subspace topology.
- **Dependencies:** FC02-C02-U079.

### FC02-C02-U082

- **Kind:** Example 4.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L3999.
- **Statement/data:** The function $f \cdot \mathbb{R} \to \mathbb{R}$ given by $f(x) = 3x + 1$ is a homeomorphism. See Figure 18 2. If we define $g \cdot \mathbb{R} \to \mathbb{R}$ by the equation $$ g (y) = \frac {1}{3} (y - 1) $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U083

- **Kind:** Example 5.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4007.
- **Statement/data:** The function $F$ . $(-1, 1) \to \mathbb{R}$ defined by $$ F (x) = \frac {x}{1 - x ^ {2}} $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U084

- **Kind:** Example 6.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4028.
- **Statement/data:** A bijective function $f$ . $X \to Y$ can be continuous without being a homeomorphism. One such function is the identity map $g$ . $\mathbb{R}_{\ell} \to \mathbb{R}$ considered in Example 3. Another is the following Let $S^1$ denote the unit circle, $$ S ^ {1} = {x \times y \mid x ^ {2} + y ^ {2} = 1 }, $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U085

- **Kind:** Example 7.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4044.
- **Statement/data:** Consider the function $$ g: [ 0, 1) \longrightarrow \mathbb {R} ^ {2} $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U086

- **Kind:** Theorem 18.2.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4056.
- **Statement/data:** (Rules for constructing continuous functions). Let $X, Y$ , and $Z$ be topological spaces. (a) (Constant function) If $f \cdot X \to Y$ maps all of $X$ into the single point $y_0$ of $Y$ , then $f$ is continuous. (b) (Inclusion) If $A$ is a subspace of $X$ , the inclusion function $j: A \to X$ is continuous. (c) (Composites) If $f: X \to Y$ and $g: Y \to Z$ are continuous, then the map $g \circ f: X \to Z$ is continuous. (d) (Restricting the domain) If $f: X \to Y$ is continuous, and if $A$ is a subspace of $X$ , then the restricted function $f|A \cdot A \to Y$ is continuous. (e) (Restricting or expanding the range) Let $f \cdot X \to Y$ be continuous. If $Z$ is a subspace of $Y$ containing the image set $f(X)$ , then the function $g: X \to Z$ obtained by restricting the range of $f$ is continuous. If $Z$ is a space having $Y$ as a subspace, then the function $h: X \to Z$ obtained by expanding the range of $f$ is continuous. (f) (Local formulation of continuity) The map $f: X \to Y$ is continuous if $X$ can be written as the union of open sets $U_{\alpha}$ such that $f|U_{\alpha}$ is continuous for each $\alpha$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001, FC02-C02-U074.

### FC02-C02-U087

- **Kind:** Theorem 18.3.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4108.
- **Statement/data:** (The pasting lemma). Let $X = A \cup B$ , where $A$ and $B$ are closed in $X$ . Let $f: A \to Y$ and $g: B \to Y$ be continuous. If $f(x) = g(x)$ for every $x \in A \cap B$ , then $f$ and $g$ combine to give a continuous function $h: X \to Y$ , defined by setting $h(x) = f(x)$ if $x \in A$ , and $h(x) = g(x)$ if $x \in B$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001, FC02-C02-U086.

### FC02-C02-U088

- **Kind:** Example 8.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4120.
- **Statement/data:** Let us define a function $h: \mathbb{R} \to \mathbb{R}$ by setting $$ h (x) = \left{ \begin{array}{l l} x & \text { for } x \leq 0, \ x / 2 & \text { for } x \geq 0 \end{array} \right. $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U089

- **Kind:** Theorem 18.4.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4143.
- **Statement/data:** (Maps into products). Let $f: A \to X \times Y$ be given by the equation $$ f (a) = \left(f _ {1} (a), f _ {2} (a)\right). $$ Then $f$ is continuous if and only if the functions $$ f _ {1} \cdot A \longrightarrow X \quad \text { and } \quad f _ {2}: A \longrightarrow Y $$ are continuous. The maps $f_{1}$ and $f_{2}$ are called the coordinate functions of $f$ .
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001, FC02-C02-U074.

### FC02-C02-U090

- **Kind:** Definition/notation.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4157.
- **Statement/data:** For $f:A\to X\times Y$, the composites with the two projections are its coordinate functions.
- **Dependencies:** —.

### FC02-C02-U091

- **Kind:** Example 9.
- **Locator:** §18 “Continuous Functions”; printed pp. 102–111; extraction L4175.
- **Statement/data:** In calculus, a parametrized curve in the plane is defined to be a continuous map $f \quad [a, b] \to \mathbb{R}^2$ . It is often expressed in the form $f(t) = (x(t), y(t))$ ; and one frequently uses the fact that $f$ is a continuous function of $t$ if both $x$ and $y$ are. Similarly, a vector field in the plane $$ \begin{array}{r l} \mathbf {v} (x, y) & = P (x, y) \mathbf {i} + Q (x, y) \mathbf {j} \ & = (P (x, y), Q (x, y)) \end{array} $$
- **Dependencies:** FC02-C01-U033, FC02-C01-U044, FC02-C02-U001.

### FC02-C02-U092

- **Kind:** Construction/comparison.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4277.
- **Statement/data:** For finite/countable products one may use all products of open factor sets as a basis; this yields the box topology.
- **Dependencies:** —.

### FC02-C02-U093

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4287.
- **Statement/data:** Let $J$ be an index set. Given a set $X$ , we define a $J$ -tuple of elements of $X$ to be a function $\mathbf{x}: J \to X$ . If $\alpha$ is an element of $J$ , we often denote the value of $\mathbf{x}$ at $\alpha$ by $x_{\alpha}$ rather than $\mathbf{x}(\alpha)$ ; we call it the $\alpha$ th coordinate of $\mathbf{x}$ . And we often denote the function $\mathbf{x}$ itself by the symbol $$ (x _ {\alpha}) _ {\alpha \in J}, $$ which is as close as we can come to a "tuple notation" for an arbitrary index set $J$ . We denote the set of all $J$ -tuples of elements of $X$ by $X^J$ .
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U094

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4295.
- **Statement/data:** Let ${A_{\alpha}}*{\alpha \in J}$ be an indexed family of sets; let $X = \bigcup*{\alpha \in J} A_{\alpha}$ . The cartesian product of this indexed family, denoted by $$ \prod_ {\alpha \in J} A _ {\alpha}, $$ is defined to be the set of all $J$ -tuples $(x_{\alpha})*{\alpha \in J}$ of elements of $X$ such that $x*{\alpha} \in A_{\alpha}$ for each $\alpha \in J$ . That is, it is the set of all functions $$ \mathbf {x}: J \rightarrow \bigcup_ {\alpha \in J} A _ {\alpha} $$ such that $\mathbf{x}(\alpha) \in A_{\alpha}$ for each $\alpha \in J$ .
- **Dependencies:** FC02-C02-U001.

### FC02-C02-U095

- **Kind:** Definition/construction.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4301.
- **Statement/data:** For an arbitrary indexed family ${A_\alpha}$, $\prod A_\alpha$ is the set of functions/tuples with $x_\alpha\in A_\alpha$ for all $\alpha$.
- **Dependencies:** —.

### FC02-C02-U096

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4313.
- **Statement/data:** Let ${X_{\alpha}}*{\alpha \in J}$ be an indexed family of topological spaces. Let us take as a basis for a topology on the product space $$ \prod* {\alpha \in J} X _ {\alpha} $$ the collection of all sets of the form $$ \prod_ {\alpha \in J} U _ {\alpha}, $$ where $U_{\alpha}$ is open in $X_{\alpha}$ , for each $\alpha \in J$ . The topology generated by this basis is called the box topology
- **Dependencies:** FC02-C02-U001, FC02-C02-U094.

### FC02-C02-U097

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4325.
- **Statement/data:** The basis of all boxes $\prod U_\alpha$ with every $U_\alpha$ open generates the box topology.
- **Dependencies:** FC02-C02-U095.

### FC02-C02-U098

- **Kind:** Definition/notation.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4345.
- **Statement/data:** For each index $\beta$, $\pi_\beta( (x_\alpha))=x_\beta$ is the projection mapping.
- **Dependencies:** FC02-C02-U095.

### FC02-C02-U099

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4347.
- **Statement/data:** Let $S_{\beta}$ denote the collection $$ \mathcal {S} _ {\beta} = {\pi_ {\beta} ^ {- 1} (U _ {\beta}) \mid U _ {\beta} \text { open in } X _ {\beta} }, $$ and let S denote the union of these collections, $$ \mathcal {S} = \bigcup_ {\beta \in J} \mathcal {S} _ {\beta}. $$ The topology generated by the subbasis $S$ is called the product topology. In this topology $\prod_{\alpha\in J}X_{\alpha}$ is called a product space.
- **Dependencies:** FC02-C02-U001, FC02-C02-U094.

### FC02-C02-U100

- **Kind:** Definition.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4359.
- **Statement/data:** The topology generated by the subbasis of inverse images $\pi_\beta^{-1}(U_\beta)$ is the product topology on $\prod X_\alpha$.
- **Dependencies:** FC02-C02-U099.

### FC02-C02-U101

- **Kind:** Theorem 19.1.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4385.
- **Statement/data:** (Comparison of the box and product topologies). The box topology on $\prod X_{\alpha}$ has as basis all sets of the form $\prod U_{\alpha}$ , where $U_{\alpha}$ is open in $X_{\alpha}$ for each $\alpha$ . The product topology on $\prod X_{\alpha}$ has as basis all sets of the form $\prod U_{\alpha}$ , where $U_{\alpha}$ is open in $X_{\alpha}$ for each $\alpha$ and $U_{\alpha}$ equals $X_{\alpha}$ except for finitely many values of $\alpha$ . Two things are immediately clear First, for finite products $\prod_{\alpha=1}^{n} X_{\alpha}$ the two topologies are precisely the same. Second, the box topology is in general finer than the product topology. What is not so clear is why we prefer the product topology to the box topology. The answer will appear as we continue our study of topology. We shall find that a number of important theorems about finite products will also hold for arbitrary products if we use the product topology, but not if we use the box topology. As a result, the product topology is extremely important in mathematics. The box topology is not so important; we shall use it primarily for constructing counterexamples. Therefore, we make the following convention: Whenever we consider the product $\prod X_{\alpha}$ , we shall assume it is given the product topology unless we specifically state otherwise. Some of the theorems we proved for the product $X \times Y$ hold for the product $\prod X_{\alpha}$ no matter which topology we use. We list them here; most of the proofs are left to the exercises.
- **Dependencies:** FC02-C02-U001, FC02-C02-U094, FC02-C02-U097, FC02-C02-U100.

### FC02-C02-U102

- **Kind:** Theorem 19.2.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4395.
- **Statement/data:** Suppose the topology on each space $X_{\alpha}$ is given by a basis $\mathcal{B}*{\alpha}$ . The collection of all sets of the form $$ \prod* {\alpha \in J} B _ {\alpha}, $$ where $B_{\alpha} \in \mathcal{B}*{\alpha}$ for each $\alpha$ , will serve as a basis for the box topology on $\prod*{\alpha \in J} X_{\alpha}$ . The collection of all sets of the same form, where $B_{\alpha} \in B_{\alpha}$ for finitely many indices $\alpha$ and $B_{\alpha} = X_{\alpha}$ for all the remaining indices, will serve as a basis for the product topology $\prod_{\alpha \in J} X_{\alpha}$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U094, FC02-C02-U100.

### FC02-C02-U103

- **Kind:** Example 1.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4405.
- **Statement/data:** Consider euclidean $n$ -space $\mathbb{R}^n$ . A basis for $\mathbb{R}$ consists of all open intervals in $\mathbb{R}$ ; hence a basis for the topology of $\mathbb{R}^n$ consists of all products of the form $$ (a _ {1}, b _ {1}) \times (a _ {2}, b _ {2}) \times \cdot \quad \times (a _ {n}, b _ {n}). $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U094.

### FC02-C02-U104

- **Kind:** Theorem 19.3.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4413.
- **Statement/data:** Let $A_{\alpha}$ be a subspace of $X_{\alpha}$ , for each $\alpha \in J$ . Then $\prod A_{\alpha}$ is a subspace of $\prod X_{\alpha}$ if both products are given the box topology, or if both products are given the product topology.
- **Dependencies:** FC02-C02-U001, FC02-C02-U036, FC02-C02-U094, FC02-C02-U100.

### FC02-C02-U105

- **Kind:** Theorem 19.4.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4415.
- **Statement/data:** If each space $X_{\alpha}$ is a Hausdorff space, then $\prod X_{\alpha}$ is a Hausdorff space in both the box and product topologies.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C02-U094, FC02-C02-U100.

### FC02-C02-U106

- **Kind:** Theorem 19.5.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4417.
- **Statement/data:** Let ${X_{\alpha}}$ be an indexed family of spaces; let $A_{\alpha} \subset X_{\alpha}$ for each $\alpha$ . If $\prod X_{\alpha}$ is given either the product or the box topology, then $$ \prod \bar {A} _ {\alpha} = \overline {{\prod A _ {\alpha}}}. $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U054, FC02-C02-U094, FC02-C02-U100.

### FC02-C02-U107

- **Kind:** Theorem 19.6.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4429.
- **Statement/data:** Let $f: A \to \prod_{\alpha \in J} X_{\alpha}$ be given by the equation $$ f (a) = \left(f _ {\alpha} (a)\right) _ {\alpha \in J}, $$ where $f_{\alpha}: A \to X_{\alpha}$ for each $\alpha$ . Let $\prod X_{\alpha}$ have the product topology. Then the function f is continuous if and only if each function $f_{\alpha}$ is continuous.
- **Dependencies:** FC02-C02-U001, FC02-C02-U074, FC02-C02-U094, FC02-C02-U098.

### FC02-C02-U108

- **Kind:** Example 2.
- **Locator:** §19 “The Product Topology”; printed pp. 112–118; extraction L4449.
- **Statement/data:** Consider $\mathbb{R}^{\omega}$ , the countably infinite product of $\mathbb{R}$ with itself. Recall that $$ \mathbb {R} ^ {\omega} = \prod_ {n \in \mathbf {Z} _ {+}} X _ {n}, $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U094.

### FC02-C02-U109

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4533.
- **Statement/data:** A metric on X is a function d:X×X→R satisfying nonnegativity with d(x,y)=0 iff x=y, symmetry, and the triangle inequality.
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U110

- **Kind:** Definition/terminology.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4547.
- **Statement/data:** $d(x,y)$ is the distance between $x,y$; $B_d(x,\epsilon)={y:d(x,y)<\epsilon}$ is the $\epsilon$-ball centered at $x$.
- **Dependencies:** FC02-C02-U109.

### FC02-C02-U111

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4555.
- **Statement/data:** If $d$ is a metric on the set $X$ , then the collection of all $\epsilon$ -balls $B_d(x, \epsilon)$ , for $x \in X$ and $\epsilon > 0$ , is a basis for a topology on $X$ , called the metric topology induced by $d$ .
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U112

- **Kind:** Example 1.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4576.
- **Statement/data:** Given a set $X$ , define $$ \begin{array}{l l} d (x, y) = 1 & \text { if } x \neq y, \ d (x, y) = 0 & \text { if } x = y \end{array} $$
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U113

- **Kind:** Example 2.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4584.
- **Statement/data:** The standard metric on the real numbers R is defined by the equation $$ d (x, y) = | x - y | $$
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U114

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4598.
- **Statement/data:** If X is a topological space, X is said to be metrizable if there exists a metric d on the set X that induces the topology of X. A metric space is a metrizable space X together with a specific metric d that gives the topology of X.
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U115

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4606.
- **Statement/data:** Let X be a metric space with metric d. A subset A of X is said to be bounded if there is some number M such that $$ d (a _ {1}, a _ {2}) \leq M $$ for every pair $a_{1}$ , $a_{2}$ of points of A. If A is bounded and nonempty, the diameter of A is defined to be the number $$ \operatorname{diam} A = \sup \left{d \left(a _ {1}, a _ {2}\right) \mid a _ {1}, a _ {2} \in A \right}. $$ Boundedness of a set is not a topological property, for it depends on the particular metric d that is used for X. For instance, if X is a metric space with metric d, then there exists a metric $\bar{d}$ that gives the topology of X, relative to which every subset of X is bounded. It is defined as follows:
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U116

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4612.
- **Statement/data:** For nonempty bounded $A$ in a metric space, $\operatorname{diam}A=\sup{d(a_1,a_2):a_i\in A}$.
- **Dependencies:** FC02-C02-U115.

### FC02-C02-U117

- **Kind:** Theorem 20.1.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4620.
- **Statement/data:** Let $X$ be a metric space with metric $d$ . Define $\bar{d}: X \times X \to \mathbb{R}$ by the equation $$ \bar {d} (x, y) = \min {d (x, y), 1 } $$ Then $\bar{d}$ is a metric that induces the same topology as $d$ . The metric $\bar{d}$ is called the standard bounded metric corresponding to d.
- **Dependencies:** FC02-C01-U077, FC02-C02-U001, FC02-C02-U109.

### FC02-C02-U118

- **Kind:** Definition/terminology.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4628.
- **Statement/data:** $\bar d(x,y)=\min{d(x,y),1}$ is the standard bounded metric corresponding to $d$.
- **Dependencies:** FC02-C02-U117.

### FC02-C02-U119

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4648.
- **Statement/data:** Given $\mathbf{x} = (x_{1}, \ldots, x_{n})$ in $R^{n}$ , we define the norm of x by the equation $$ | x | = (x _ {1} ^ {2} + \dots + x _ {n} ^ {2}) ^ {1 / 2}; $$ and we define the euclidean metric d on $R^{n}$ by the equation $$ d (\mathbf {x}, \mathbf {y}) = | \mathbf {x} - \mathbf {y} | = [ (x _ {1} - y _ {1}) ^ {2} + \dots + (x _ {n} - y _ {n}) ^ {2} ] ^ {1 / 2}. $$ We define the square metric $\rho$ by the equation
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U120

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4654.
- **Statement/data:** On $\mathbb R^n$, $d(x,y)=|x-y|$ is the Euclidean metric.
- **Dependencies:** FC02-C02-U119.

### FC02-C02-U121

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4660.
- **Statement/data:** On $\mathbb R^n$, $\rho(x,y)=\max_i|x_i-y_i|$ is the square metric.
- **Dependencies:** —.

### FC02-C02-U122

- **Kind:** Lemma 20.2.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4692.
- **Statement/data:** Let $d$ and $d'$ be two metrics on the set $X$ ; let $\mathcal{T}$ and $\mathcal{T}'$ be the topologies they induce, respectively. Then $\mathcal{T}'$ is finer than $\mathcal{T}$ if and only if for each $x$ in $X$ and each $\epsilon > 0$ , there exists a $\delta > 0$ such that $$ B _ {d ^ {\prime}} (x, \delta) \subset B _ {d} (x, \epsilon) $$
- **Dependencies:** FC02-C01-U077, FC02-C02-U001, FC02-C02-U111.

### FC02-C02-U123

- **Kind:** Theorem 20.3.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4702.
- **Statement/data:** The topologies on $\mathbb{R}^n$ induced by the euclidean metric $d$ and the square metric $\rho$ are the same as the product topology on $\mathbb{R}^n$ .
- **Dependencies:** FC02-C01-U077, FC02-C02-U001, FC02-C02-U031, FC02-C02-U120, FC02-C02-U121.

### FC02-C02-U124

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4766.
- **Statement/data:** On $\mathbb R^\omega$, replacing the coordinate metric by its bounded version makes the supremum formula finite; this is the uniform metric.
- **Dependencies:** FC02-C02-U118.

### FC02-C02-U125

- **Kind:** Definition.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4770.
- **Statement/data:** For x,y in R^J, define bar-rho(x,y)=sup_{alpha in J} bar-d(x_alpha,y_alpha), with bar-d the standard bounded metric on R. This is the uniform metric; its induced topology is the uniform topology.
- **Dependencies:** FC02-C01-U077, FC02-C02-U001.

### FC02-C02-U126

- **Kind:** Theorem 20.4.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4780.
- **Statement/data:** The uniform topology on $\mathbb{R}^J$ is finer than the product topology and coarser than the box topology; these three topologies are all different if $J$ is infinite.
- **Dependencies:** FC02-C01-U077, FC02-C02-U001, FC02-C02-U097, FC02-C02-U100.

### FC02-C02-U127

- **Kind:** Theorem 20.5.
- **Locator:** §20 “The Metric Topology”; printed pp. 119–128; extraction L4796.
- **Statement/data:** Let $\bar{d}(a, b) = \min{|a - b|, 1}$ be the standard bounded metric on $\mathbb{R}$ . If $x$ and $y$ are two points of $\mathbb{R}^{\omega}$ , define $$ D (\mathbf {x}, \mathbf {y}) = \sup \left{\frac {\bar {d} (x _ {i} , y _ {i})}{i} \right}. $$ Then D is a metric that induces the product topology on $R^{\omega}$ .
- **Dependencies:** FC02-C01-U077, FC02-C02-U001, FC02-C02-U100.

### FC02-C02-U128

- **Kind:** Theorem 21.1.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5024.
- **Statement/data:** Let $f: X \to Y$ ; let $X$ and $Y$ be metrizable with metrics $d_X$ and $d_Y$ , respectively. Then continuity of $f$ is equivalent to the requirement that given $x \in X$ and given $\epsilon > 0$ , there exists $\delta > 0$ such that $$ d _ {X} (x, y) < \delta \Longrightarrow d _ {Y} (f (x), f (y)) < \epsilon . $$
- **Dependencies:** FC02-C02-U074, FC02-C02-U109.

### FC02-C02-U129

- **Kind:** Lemma 21.2.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5042.
- **Statement/data:** (The sequence lemma). Let $X$ be a topological space; let $A \subset X$ . If there is a sequence of points of $A$ converging to $x$ , then $x \in \bar{A}$ ; the converse holds if $X$ is metrizable.
- **Dependencies:** FC02-C02-U061, FC02-C02-U074, FC02-C02-U109.

### FC02-C02-U130

- **Kind:** Theorem 21.3.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5046.
- **Statement/data:** Let $f: X \to Y$ . If the function $f$ is continuous, then for every convergent sequence $x_{n} \to x$ in $X$ , the sequence $f(x_{n})$ converges to $f(x)$ . The converse holds if $X$ is metrizable.
- **Dependencies:** FC02-C02-U074, FC02-C02-U109, FC02-C02-U129.

### FC02-C02-U131

- **Kind:** Lemma 21.4.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5068.
- **Statement/data:** The addition, subtraction, and multiplication operations are continuous functions from $\mathbb{R} \times \mathbb{R}$ into $\mathbb{R}$ ; and the quotient operation is a continuous function from $\mathbb{R} \times (\mathbb{R} - {0})$ into $\mathbb{R}$ . You have probably seen this lemma proved before; it is a standard “ε-δ argument.” If not, a proof is outlined in Exercise 12 below; you should have no trouble filling in the details.
- **Dependencies:** FC02-C02-U074, FC02-C02-U109, FC02-C02-U123.

### FC02-C02-U132

- **Kind:** Theorem 21.5.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5072.
- **Statement/data:** If $X$ is a topological space, and if $f, g: X \to \mathbb{R}$ are continuous functions, then $f + g, f - g$ , and $f \cdot g$ are continuous. If $g(x) \neq 0$ for all $x$ , then $f / g$ is continuous.
- **Dependencies:** FC02-C02-U074, FC02-C02-U089, FC02-C02-U109, FC02-C02-U131.

### FC02-C02-U133

- **Kind:** Definition.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5090.
- **Statement/data:** Let $f_n: X \to Y$ be a sequence of functions from the set $X$ to the metric space $Y$ . Let $d$ be the metric for $Y$ . We say that the sequence $(f_n)$ converges uniformly to the function $f: X \to Y$ if given $\epsilon > 0$ , there exists an integer $N$ such that $$ d (f _ {n} (x), f (x)) < \epsilon $$ for all $n > N$ and all $x$ in $X$ . Uniformity of convergence depends not only on the topology of Y but also on its metric. We have the following theorem about uniformly convergent sequences:
- **Dependencies:** FC02-C02-U074, FC02-C02-U109.

### FC02-C02-U134

- **Kind:** Theorem 21.6.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5100.
- **Statement/data:** (Uniform limit theorem). Let $f_{n}: X \to Y$ be a sequence of continuous functions from the topological space $X$ to the metric space $Y$ . If $(f_{n})$ converges uniformly to $f$ , then $f$ is continuous.
- **Dependencies:** FC02-C02-U074, FC02-C02-U109, FC02-C02-U130, FC02-C02-U133.

### FC02-C02-U135

- **Kind:** Example 1.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5124.
- **Statement/data:** $\mathbb{R}^{\omega}$ in the box topology is not metrizable.
- **Dependencies:** FC02-C02-U074, FC02-C02-U109.

### FC02-C02-U136

- **Kind:** Example 2.
- **Locator:** §21 “The Metric Topology (continued)”; printed pp. 129–135; extraction L5160.
- **Statement/data:** An uncountable product of $\mathbb{R}$ with itself is not metrizable.
- **Dependencies:** FC02-C02-U074, FC02-C02-U109.

### FC02-C02-U137

- **Kind:** Definition.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5320.
- **Statement/data:** Let $X$ and $Y$ be topological spaces; let $p: X \to Y$ be a surjective map. The map $p$ is said to be a quotient map provided a subset $U$ of $Y$ is open in $Y$ if and only if $p^{-1}(U)$ is open in $X$ .
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U138

- **Kind:** Definition/comparison.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5330.
- **Statement/data:** A map is open if it sends open sets to open sets and closed if it sends closed sets to closed sets; a surjective continuous open or closed map is quotient.
- **Dependencies:** FC02-C02-U137.

### FC02-C02-U139

- **Kind:** Example 1.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5332.
- **Statement/data:** Let $X$ be the subspace $[0,1] \cup [2,3]$ of $\mathbb{R}$ , and let $Y$ be the subspace $[0,2]$ of $\mathbb{R}$ . The map $p: X \to Y$ defined by $$ p (x) = \left{ \begin{array}{l l} x & \text { for } x \in [ 0, 1 ], \ x - 1 & \text { for } x \in [ 2, 3 ] \end{array} \right. $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U140

- **Kind:** Example 2.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5342.
- **Statement/data:** Let $\pi_1: \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be projection onto the first coordinate; then $\pi_1$ is continuous and surjective. Furthermore, $\pi_1$ is an open map. For if $U \times V$ is a nonempty basis element for $\mathbb{R} \times \mathbb{R}$ , then $\pi_1(U \times V) = U$ is open in $\mathbb{R}$ ; it follows that $\pi_1$ carries open sets of $\mathbb{R} \times \mathbb{R}$ to open sets of $\mathbb{R}$ . However, $\pi_1$ is not a closed map. The subset $$ C = {x \times y \mid x y = 1 } $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U141

- **Kind:** Definition.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5354.
- **Statement/data:** If $X$ is a space and $A$ is a set and if $p: X \to A$ is a surjective map, then there exists exactly one topology $\mathcal{T}$ on $A$ relative to which $p$ is a quotient map; it is called the quotient topology induced by $p$ .
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U142

- **Kind:** Example 3.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5366.
- **Statement/data:** Let $p$ be the map of the real line $\mathbb{R}$ onto the three-point set $A = {a, b, c}$ defined by $$ p (x) = \left{ \begin{array}{l l} a & \text { if } x > 0, \ b & \text { if } x < 0, \ c & \text { if } x = 0. \end{array} \right. $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U143

- **Kind:** Definition.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5379.
- **Statement/data:** Let $X$ be a topological space, and let $X^*$ be a partition of $X$ into disjoint subsets whose union is $X$ . Let $p: X \to X^*$ be the surjective map that carries each point of $X$ to the element of $X^*$ containing it. In the quotient topology induced by $p$ , the space $X^*$ is called a quotient space of $X$ .
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U144

- **Kind:** Example 4.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5385.
- **Statement/data:** Let X be the closed unit ball $$ {x \times y \mid x ^ {2} + y ^ {2} \leq 1 } $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U145

- **Kind:** Definition.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5387.
- **Statement/data:** A subset $A\subset X$ is saturated with respect to $p:X\to Y$ if it is a union of fibers, equivalently $A=p^{-1}(p(A))$.
- **Dependencies:** FC02-C02-U137.

### FC02-C02-U146

- **Kind:** Example 5.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5400.
- **Statement/data:** Let $X$ be the rectangle $[0, 1] \times [0, 1]$ . Define a partition $X^*$ of $X$ as follows: It consists of all the one-point sets ${x \times y}$ where $0 < x < 1$ and $0 < y < 1$ , the following types of two-point sets: $$ {x \times 0, x \times 1 } \quad \text { where } 0 < x < 1, $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U147

- **Kind:** Theorem 22.1.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5430.
- **Statement/data:** Let $p: X \to Y$ be a quotient map; let $A$ be a subspace of $X$ that is saturated with respect to $p$ ; let $q: A \to p(A)$ be the map obtained by restricting $p$ . (1) If $A$ is either open or closed in $X$ , then $q$ is a quotient map. *(2) If $p$ is either an open map or a closed map, then $q$ is a quotient map.
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001, FC02-C02-U137, FC02-C02-U145.

### FC02-C02-U148

- **Kind:** Theorem 22.2.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5478.
- **Statement/data:** Let $p: X \to Y$ be a quotient map. Let $Z$ be a space and let $g: X \to Z$ be a map that is constant on each set $p^{-1}({y})$ , for $y \in Y$ . Then $g$ induces a map $f: Y \to Z$ such that $f \circ p = g$ . The induced map $f$ is continuous if and only if $g$ is continuous; $f$ is a quotient map if and only if $g$ is a quotient map.
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001, FC02-C02-U074, FC02-C02-U137.

### FC02-C02-U149

- **Kind:** Corollary 22.3.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5486.
- **Statement/data:** Let $g: X \to Z$ be a surjective continuous map. Let $X^*$ be the following collection of subsets of $X$ : $$ X ^ {*} = {g ^ {- 1} ({z }) \mid z \in Z }. $$ Give $X^{*}$ the quotient topology. (a) The map $g$ induces a bijective continuous map $f: X^* \to Z$ , which is a homeomorphism if and only if $g$ is a quotient map. (b) If $Z$ is Hausdorff, so is $X^*$ .
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001, FC02-C02-U143, FC02-C02-U148.

### FC02-C02-U150

- **Kind:** Example 6.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5504.
- **Statement/data:** Let $X$ be the subspace of $\mathbb{R}^2$ that is the union of the line segments $[0,1] \times {n}$ , for $n \in \mathbb{Z}*+$ , and let $Z$ be the subspace of $\mathbb{R}^2$ consisting of all points of the form $x \times (x / n)$ for $x \in [0,1]$ and $n \in \mathbb{Z}*+$ . Then $X$ is the union of countably many disjoint line segments, and $Z$ is the union of countably many line segments having an end point in common. See Figure 22.7.
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

### FC02-C02-U151

- **Kind:** Example 7.
- **Locator:** *§22 “The Quotient Topology”; printed pp. 136–144; extraction L5513.
- **Statement/data:** The product of two quotient maps need not be a quotient map We give an example that involves non-Hausdorff spaces in the exercises. Here is another involving spaces that are nicer. Let $X = \mathbb{R}$ and let $X^{*}$ be the quotient space obtained from $X$ by identifying the subset $\mathbb{Z}_{+}$ to a point $b$ ; let $p: X \to X^{*}$ be the quotient map. Let $\mathbb{Q}$ be the subspace of $\mathbb{R}$ consisting of the rational numbers; let $i: \mathbb{Q} \to \mathbb{Q}$ be the identity map. We show that $$ p \times i: X \times \mathbb {Q} \rightarrow X ^ {*} \times \mathbb {Q} $$
- **Dependencies:** FC02-C01-U039, FC02-C01-U046, FC02-C02-U001.

## C03 — Connectedness and Compactness

Units: 92.

### FC02-C03-U001

- **Kind:** Definition.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5646.
- **Statement/data:** Let $X$ be a topological space. A separation of $X$ is a pair $U, V$ of disjoint nonempty open subsets of $X$ whose union is $X$ . The space $X$ is said to be connected if there does not exist a separation of $X$ .
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U002

- **Kind:** Lemma 23.1.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5658.
- **Statement/data:** If Y is a subspace of X, a separation of Y is a pair of disjoint nonempty sets A and B whose union is Y, neither of which contains a limit point of the other. The space Y is connected if there exists no separation of Y.
- **Dependencies:** FC02-C02-U001, FC02-C02-U061, FC02-C03-U001.

### FC02-C03-U003

- **Kind:** Example 1.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5666.
- **Statement/data:** Let X denote a two-point space in the indiscrete topology. Obviously there is no separation of X, so X is connected.
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U004

- **Kind:** Example 2.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5668.
- **Statement/data:** Let Y denote the subspace $[-1,0)\cup(0,1]$ of the real line R. Each of the sets $[-1,0)$ and $(0,1]$ is nonempty and open in Y (although not in R); therefore, they form a separation of Y. Alternatively, note that neither of these sets contains a limit point of the other. (They do have a limit point 0 in common, but that does not matter.)
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U005

- **Kind:** Example 3.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5670.
- **Statement/data:** Let $X$ be the subspace $[-1, 1]$ of the real line. The sets $[-1, 0]$ and $(0, 1]$ are disjoint and nonempty, but they do not form a separation of $X$ , because the first set is not open in $X$ . Alternatively, note that the first set contains a limit point, $0$ , of the second. Indeed, there exists no separation of the space $[-1, 1]$ . We shall prove this fact shortly.
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U006

- **Kind:** Example 4.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5672.
- **Statement/data:** The rationals $\mathbb{Q}$ are not connected. Indeed, the only connected subspaces of $\mathbb{Q}$ are the one-point sets: If $Y$ is a subspace of $\mathbb{Q}$ containing two points $p$ and $q$ , one can choose an irrational number $a$ lying between $p$ and $q$ , and write $Y$ as the union of the open sets $$ Y \cap (- \infty , a) \quad \text { and } \quad Y \cap (a, + \infty). $$
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U007

- **Kind:** Example 5.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5678.
- **Statement/data:** Consider the following subset of the plane $\mathbb{R}^2$ : $$ X = {x \times y \mid y = 0 } \cup {x \times y \mid x > 0 \text { and } y = 1 / x }. $$
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U008

- **Kind:** Lemma 23.2.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5691.
- **Statement/data:** If the sets $C$ and $D$ form a separation of $X$ , and if $Y$ is a connected subspace of $X$ , then $Y$ lies entirely within either $C$ or $D$ .
- **Dependencies:** FC02-C02-U001, FC02-C03-U001.

### FC02-C03-U009

- **Kind:** Theorem 23.3.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5695.
- **Statement/data:** The union of a collection of connected subspaces of $X$ that have a point in common is connected.
- **Dependencies:** FC02-C02-U001, FC02-C03-U001.

### FC02-C03-U010

- **Kind:** Theorem 23.4.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5699.
- **Statement/data:** Let $A$ be a connected subspace of $X$ . If $A \subset B \subset \tilde{A}$ , then $B$ is also connected. Said differently: If B is formed by adjoining to the connected subspace A some or all of its limit points, then B is connected.
- **Dependencies:** FC02-C02-U001, FC02-C02-U054, FC02-C03-U009.

### FC02-C03-U011

- **Kind:** Theorem 23.5.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5705.
- **Statement/data:** The image of a connected space under a continuous map is connected.
- **Dependencies:** FC02-C02-U001, FC02-C02-U074, FC02-C03-U001.

### FC02-C03-U012

- **Kind:** Theorem 23.6.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5715.
- **Statement/data:** A finite cartesian product of connected spaces is connected.
- **Dependencies:** FC02-C02-U001, FC02-C02-U031, FC02-C03-U011.

### FC02-C03-U013

- **Kind:** Example 6.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5734.
- **Statement/data:** Consider the cartesian product $\mathbb{R}^{\omega}$ in the box topology. We can write $\mathbb{R}^{\omega}$ as the union of the set $A$ consisting of all bounded sequences of real numbers, and the set $B$ of all unbounded sequences. These sets are disjoint, and each is open in the box topology. For if a is a point of $\mathbb{R}^{\omega}$ , the open set $$ U = (a _ {1} - 1, a _ {1} + 1) \times (a _ {2} - 1, a _ {2} + 1) \times \dots $$
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U014

- **Kind:** Example 7.
- **Locator:** §23 “Connected Spaces”; printed pp. 148–152; extraction L5742.
- **Statement/data:** Now consider $\mathbb{R}^{\omega}$ in the product topology. Assuming that $\mathbb{R}$ is connected, we show that $\mathbb{R}^{\omega}$ is connected. Let $\bar{\mathbb{R}}^{n}$ denote the subspace of $\mathbb{R}^{\omega}$ consisting of all sequences $\mathbf{x} = (x_{1}, x_{2}, \ldots)$ such that $x_{i} = 0$ for $i > n$ . The space $\bar{\mathbb{R}}^{n}$ is clearly homeomorphic to $\mathbb{R}^{n}$ , so that it is connected, by the preceding theorem. It follows that the space $\mathbb{R}^{\infty}$ that is the union of the spaces $\bar{\mathbb{R}}^{n}$ is connected, for these spaces have the point $\mathbf{0} = (0, 0, \ldots)$ in common. We show that the closure of $\mathbb{R}^{\infty}$ equals all of $\mathbb{R}^{\omega}$ , from which it follows that $\mathbb{R}^{\omega}$ is connected as well.
- **Dependencies:** FC02-C02-U001.

### FC02-C03-U015

- **Kind:** Definition.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5806.
- **Statement/data:** A simply ordered set L having more than one element is called a linear continuum if the following hold: (1) L has the least upper bound property. (2) If $x < y$ , there exists $z$ such that $x < z < y$ .
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U016

- **Kind:** Theorem 24.1.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5812.
- **Statement/data:** If $L$ is a linear continuum in the order topology, then $L$ is connected, and so are intervals and rays in $L$ .
- **Dependencies:** FC02-C01-U074, FC02-C02-U024, FC02-C03-U001, FC02-C03-U015.

### FC02-C03-U017

- **Kind:** Definition.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5814.
- **Statement/data:** A subset $Y$ of an ordered set is convex if $a,b\in Y$, $a<b$, implies $[a,b]\subset Y$.
- **Dependencies:** —.

### FC02-C03-U018

- **Kind:** Corollary 24.2.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5838.
- **Statement/data:** The real line R is connected and so are intervals and rays in R. As an application, we prove the intermediate value theorem of calculus, suitably generalized.
- **Dependencies:** FC02-C01-U074, FC02-C03-U001, FC02-C03-U016.

### FC02-C03-U019

- **Kind:** Theorem 24.3.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5842.
- **Statement/data:** (Intermediate value theorem). Let $f: X \to Y$ be a continuous map, where $X$ is a connected space and $Y$ is an ordered set in the order topology. If $a$ and $b$ are two points of $X$ and if $r$ is a point of $Y$ lying between $f(a)$ and $f(b)$ , then there exists a point $c$ of $X$ such that $f(c) = r$ . The intermediate value theorem of calculus is the special case of this theorem that occurs when we take X to be a closed interval in R and Y to be R.
- **Dependencies:** FC02-C01-U074, FC02-C03-U001, FC02-C03-U011, FC02-C03-U015.

### FC02-C03-U020

- **Kind:** Example 1.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5854.
- **Statement/data:** One example of a linear continuum different from $\mathbb{R}$ is the ordered square. We check the least upper bound property. (The second property of a linear continuum is trivial to check.) Let $A$ be a subset of $I \times I$ ; let $\pi_1: I \times I \to I$ be projection on the first coordinate; let $b = \sup \pi_1(A)$ . If $b \in \pi_1(A)$ , then $A$ intersects the subset $b \times I$ of $I \times I$ . Because $b \times I$ has the order type of $I$ , the set $A \cap (b \times I)$ will have a least upper bound $b \times c$ , which will be the least upper bound of $A$ . See Figure 24.3. If $b \notin \pi_1(A)$ , then $b \times 0$ is the least upper bound of $A$ ; no element of the form $b' \times c$ with $b' < b$ can be an upper bound for $A$ , for then $b'$ would be an upper bound for $\pi_1(A)$ .
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U021

- **Kind:** Example 2.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5859.
- **Statement/data:** If X is a well-ordered set, then $X \times [0,1)$ is a linear continuum in the dictionary order; this we leave to you to check. This set can be thought of as having been constructed by “fitting in” a set of the order type of $(0,1)$ immediately following each element of X.
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U022

- **Kind:** Definition.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5863.
- **Statement/data:** Given points $x$ and $y$ of the space $X$ , a path in $X$ from $x$ to $y$ is a continuous map $f: [a, b] \to X$ of some closed interval in the real line into $X$ , such that $f(a) = x$ and $f(b) = y$ . A space $X$ is said to be path connected if every pair of points of $X$ can be joined by a path in $X$ .
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U023

- **Kind:** Example 3.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5869.
- **Statement/data:** Define the unit ball $B^n$ in $\mathbb{R}^n$ by the equation $$ B ^ {n} = {\mathbf {x} \mid | \mathbf {x} | \leq 1 }, $$
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U024

- **Kind:** Construction.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5881.
- **Statement/data:** A straight-line path from $x$ to $y$ in a convex subset of $\mathbb R^n$ is $f(t)=(1-t)x+ty$.
- **Dependencies:** FC02-C03-U022.

### FC02-C03-U025

- **Kind:** Example 4.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5895.
- **Statement/data:** Define punctured euclidean space to be the space $\mathbb{R}^n - {\mathbf{0}}$ , where $\mathbf{0}$ is the origin in $\mathbb{R}^n$ . If $n > 1$ , this space is path connected: Given $\mathbf{x}$ and $\mathbf{y}$ different from $\mathbf{0}$ , we can join $\mathbf{x}$ and $\mathbf{y}$ by the straight-line path between them if that path does not go through the origin. Otherwise, we can choose a point $\mathbf{z}$ not on the line joining $\mathbf{x}$ and $\mathbf{y}$ , and take the broken-line path from $\mathbf{x}$ to $\mathbf{z}$ , and then from $\mathbf{z}$ to $\mathbf{y}$ .
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U026

- **Kind:** Example 5.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5897.
- **Statement/data:** Define the unit sphere $S^{n-1}$ in $\mathbb{R}^n$ by the equation $$ S ^ {n - 1} = {\mathbf {x} \mid | \mathbf {x} | = 1 }. $$
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U027

- **Kind:** Example 6.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5905.
- **Statement/data:** The ordered square $I_0^2$ is connected but not path connected.
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U028

- **Kind:** Example 7.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5915.
- **Statement/data:** Let S denote the following subset of the plane.
- **Dependencies:** FC02-C01-U074, FC02-C03-U001.

### FC02-C03-U029

- **Kind:** Named example.
- **Locator:** §24 “Connected Subspaces of the Real Line”; printed pp. 153–158; extraction L5921.
- **Statement/data:** The closure of the graph $S={(x,\sin(1/x)):0<x\le1}$ is the topologist’s sine curve; it is connected but not path connected.
- **Dependencies:** —.

### FC02-C03-U030

- **Kind:** Definition.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L5993.
- **Statement/data:** Given $X$ , define an equivalence relation on $X$ by setting $x \sim y$ if there is a connected subspace of $X$ containing both $x$ and $y$ . The equivalence classes are called the components (or the "connected components") of $X$ .
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U031

- **Kind:** Theorem 25.1.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L5999.
- **Statement/data:** The components of $X$ are connected disjoint subspaces of $X$ whose union is $X$ , such that each nonempty connected subspace of $X$ intersects only one of them.
- **Dependencies:** FC02-C03-U001, FC02-C03-U009, FC02-C03-U022, FC02-C03-U030.

### FC02-C03-U032

- **Kind:** Definition.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6011.
- **Statement/data:** We define another equivalence relation on the space $X$ by defining $x \sim y$ if there is a path in $X$ from $x$ to $y$ . The equivalence classes are called the path components of $X$ .
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U033

- **Kind:** Theorem 25.2.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6017.
- **Statement/data:** The path components of X are path-connected disjoint subspaces of X whose union is X, such that each nonempty path-connected subspace of X intersects only one of them. Note that each component of a space X is closed in X, since the closure of a connected subspace of X is connected. If X has only finitely many components, then each component is also open in X, since its complement is a finite union of closed sets. But in general the components of X need not be open in X. One can say even less about the path components of X, for they need be neither open nor closed in X. Consider the following examples:
- **Dependencies:** FC02-C03-U001, FC02-C03-U022, FC02-C03-U032.

### FC02-C03-U034

- **Kind:** Example 1.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6023.
- **Statement/data:** If Q is the subspace of R consisting of the rational numbers, then each component of Q consists of a single point. None of the components of Q are open in Q.
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U035

- **Kind:** Example 2.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6025.
- **Statement/data:** The "topologist's sine curve" $\tilde{S}$ of the preceding section is a space that has a single component (since it is connected) and two path components. One path component is the curve $S$ and the other is the vertical interval $V = 0 \times [-1, 1]$ . Note that $S$ is open in $\tilde{S}$ but not closed, while $V$ is closed but not open.
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U036

- **Kind:** Definition.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6031.
- **Statement/data:** A space $X$ is said to be locally connected at $x$ if for every neighborhood $U$ of $x$ , there is a connected neighborhood $V$ of $x$ contained in $U$ . If $X$ is locally connected at each of its points, it is said simply to be locally connected. Similarly, a space $X$ is said to be locally path connected at $x$ if for every neighborhood $U$ of $x$ , there is a path-connected neighborhood $V$ of $x$ contained in $U$ . If $X$ is locally path connected at each of its points, then it is said to be locally path connected.
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U037

- **Kind:** Example 3.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6033.
- **Statement/data:** Each interval and each ray in the real line is both connected and locally connected. The subspace $[-1,0)\cup(0,1]$ of $\mathbb{R}$ is not connected, but it is locally connected. The topologist's sine curve is connected but not locally connected. The rationals $\mathbb{Q}$ are neither connected nor locally connected.
- **Dependencies:** FC02-C03-U001, FC02-C03-U022.

### FC02-C03-U038

- **Kind:** Theorem 25.3.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6035.
- **Statement/data:** A space $X$ is locally connected if and only if for every open set $U$ of $X$ , each component of $U$ is open in $X$ .
- **Dependencies:** FC02-C03-U001, FC02-C03-U022, FC02-C03-U031, FC02-C03-U036.

### FC02-C03-U039

- **Kind:** Theorem 25.4.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6043.
- **Statement/data:** A space $X$ is locally path connected if and only if for every open set $U$ of $X$ , each path component of $U$ is open in $X$ . The relation between path components and components is given in the following theorem:
- **Dependencies:** FC02-C03-U001, FC02-C03-U022, FC02-C03-U033, FC02-C03-U036.

### FC02-C03-U040

- **Kind:** Theorem 25.5.
- **Locator:** *§25 “Components and Local Connectedness”; printed pp. 159–162; extraction L6047.
- **Statement/data:** If X is a topological space, each path component of X lies in a component of X. If X is locally path connected, then the components and the path components of X are the same.
- **Dependencies:** FC02-C03-U001, FC02-C03-U022, FC02-C03-U031, FC02-C03-U033.

### FC02-C03-U041

- **Kind:** Definition.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6118.
- **Statement/data:** A collection $\mathcal{A}$ of subsets of a space $X$ is said to cover $X$ , or to be a covering of $X$ , if the union of the elements of $\mathcal{A}$ is equal to $X$ . It is called an open covering of $X$ if its elements are open subsets of $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U042

- **Kind:** Definition.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6120.
- **Statement/data:** A space $X$ is said to be compact if every open covering $\mathcal{A}$ of $X$ contains a finite subcollection that also covers $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U043

- **Kind:** Example 1.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6122.
- **Statement/data:** The real line R is not compact, for the covering of R by open intervals $$ \mathcal {A} = {(n, n + 2) \mid n \in \mathbb {Z} } $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U044

- **Kind:** Example 2.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6130.
- **Statement/data:** The following subspace of $\mathbb{R}$ is compact: $$ X = {0 } \cup {1 / n \mid n \in \mathbb {Z} _ {+} }. $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U045

- **Kind:** Example 3.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6138.
- **Statement/data:** Any space X containing only finitely many points is necessarily compact, because in this case every open covering of X is finite.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U046

- **Kind:** Example 4.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6140.
- **Statement/data:** The interval $(0, 1]$ is not compact; the open covering $$ \mathcal {A} = {(1 / n, 1 ] \mid n \in \mathbb {Z} _ {+} } $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U047

- **Kind:** Lemma 26.1.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6152.
- **Statement/data:** Let $Y$ be a subspace of $X$ . Then $Y$ is compact if and only if every covering of $Y$ by sets open in $X$ contains a finite subcollection covering $Y$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C03-U041, FC02-C03-U042.

### FC02-C03-U048

- **Kind:** Theorem 26.2.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6176.
- **Statement/data:** Every closed subspace of a compact space is compact.
- **Dependencies:** FC02-C02-U001, FC02-C02-U045, FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U049

- **Kind:** Theorem 26.3.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6186.
- **Statement/data:** Every compact subspace of a Hausdorff space is closed.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U050

- **Kind:** Lemma 26.4.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6209.
- **Statement/data:** If $Y$ is a compact subspace of the Hausdorff space $X$ and $x_0$ is not in $Y$ , then there exist disjoint open sets $U$ and $V$ of $X$ containing $x_0$ and $Y$ , respectively.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U051

- **Kind:** Example 5.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6211.
- **Statement/data:** Once we prove that the interval $[a, b]$ in $\mathbb{R}$ is compact, it follows from Theorem 26.2 that any closed subspace of $[a, b]$ is compact. On the other hand, it follows from Theorem 26.3 that the intervals $(a, b]$ and $(a, b)$ in $\mathbb{R}$ cannot be compact (which we knew already) because they are not closed in the Hausdorff space $\mathbb{R}$
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U052

- **Kind:** Example 6.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6213.
- **Statement/data:** One needs the Hausdorff condition in the hypothesis of Theorem 26.3 Consider, for example, the finite complement topology on the real line. The only proper subsets of $\mathbb{R}$ that are closed in this topology are the finite sets. But every subset of $\mathbb{R}$ is compact in this topology, as you can check.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U053

- **Kind:** Theorem 26.5.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6215.
- **Statement/data:** The image of a compact space under a continuous map is compact.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C02-U074, FC02-C03-U042.

### FC02-C03-U054

- **Kind:** Theorem 26.6.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6233.
- **Statement/data:** Let $f: X \to Y$ be a bijective continuous function. If $X$ is compact and $Y$ is Hausdorff, then $f$ is a homeomorphism
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C02-U079, FC02-C03-U053.

### FC02-C03-U055

- **Kind:** Theorem 26.7.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6237.
- **Statement/data:** The product of finitely many compact spaces is compact.
- **Dependencies:** FC02-C02-U001, FC02-C02-U031, FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U056

- **Kind:** Lemma 26.8.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6286.
- **Statement/data:** (The tube lemma). Consider the product space $X \times Y$ , where $Y$ is compact. If $N$ is an open set of $X \times Y$ containing the slice $x_0 \times Y$ of $X \times Y$ , then $N$ contains some tube $W \times Y$ about $x_0 \times Y$ , where $W$ is a neighborhood of $x_0$ in $X$ .
- **Dependencies:** FC02-C02-U001, FC02-C02-U031, FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U057

- **Kind:** Example 7.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6288.
- **Statement/data:** The tube lemma is certainly not true if $Y$ is not compact. For example, let $Y$ be the $y$ -axis in $\mathbb{R}^2$ , and let $$ N = {x \times y, | x | < 1 / (y ^ {2} + 1) }. $$
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U058

- **Kind:** Named theorem reference.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6299.
- **Statement/data:** The compactness of arbitrary products in the product topology is the Tychonoff theorem, proved in Chapter 5.
- **Dependencies:** FC02-C03-U055.

### FC02-C03-U059

- **Kind:** Definition.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6305.
- **Statement/data:** A collection C of subsets of X is said to have the finite intersection property if for every finite subcollection $$ {C _ {1}, \dots , C _ {n} } $$ of C, the intersection $C_{1} \cap \cdots \cap C_{n}$ is nonempty.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067.

### FC02-C03-U060

- **Kind:** Theorem 26.9.
- **Locator:** §26 “Compact Spaces”; printed pp. 163–171; extraction L6313.
- **Statement/data:** Let X be a topological space. Then X is compact if and only if for every collection C of closed sets in X having the finite intersection property, the intersection $\bigcap_{C\in C}C$ of all the elements of C is nonempty.
- **Dependencies:** FC02-C02-U001, FC02-C02-U067, FC02-C03-U042, FC02-C03-U059.

### FC02-C03-U061

- **Kind:** Theorem 27.1.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6419.
- **Statement/data:** Let X be a simply ordered set having the least upper bound property. In the order topology, each closed interval in X is compact.
- **Dependencies:** FC02-C01-U074, FC02-C02-U024, FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U062

- **Kind:** Corollary 27.2.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6439.
- **Statement/data:** Every closed interval in R is compact. Now we characterize the compact subspaces of $\mathbb{R}^n$ :
- **Dependencies:** FC02-C02-U109, FC02-C03-U042, FC02-C03-U061.

### FC02-C03-U063

- **Kind:** Theorem 27.3.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6443.
- **Statement/data:** A subspace $A$ of $\mathbb{R}^n$ is compact if and only if it is closed and is bounded in the euclidean metric $d$ or the square metric $\rho$ .
- **Dependencies:** FC02-C02-U109, FC02-C02-U115, FC02-C03-U042.

### FC02-C03-U064

- **Kind:** Example 1.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6465.
- **Statement/data:** The unit sphere $S^{n-1}$ and the closed unit ball $B^n$ in $\mathbb{R}^n$ are compact because they are closed and bounded. The set $$ A = {x \times (1 / x) \mid 0 < x \leq 1 } $$
- **Dependencies:** FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U065

- **Kind:** Theorem 27.4.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6481.
- **Statement/data:** (Extreme value theorem). Let $f \colon X \to Y$ be continuous, where $Y$ is an ordered set in the order topology. If $X$ is compact, then there exist points $c$ and $d$ in $X$ such that $f(c) \leq f(x) \leq f(d)$ for every $x \in X$ . The extreme value theorem of calculus is the special case of this theorem that occurs when we take X to be a closed interval in R and Y to be R.
- **Dependencies:** FC02-C01-U059, FC02-C02-U109, FC02-C03-U042, FC02-C03-U053.

### FC02-C03-U066

- **Kind:** Definition.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6505.
- **Statement/data:** Let $(X, d)$ be a metric space; let $A$ be a nonempty subset of $X$ . For each $x \in X$ , we define the distance from $x$ to $A$ by the equation $$ d (x, A) = \inf {d (x, a) \mid a \in A }. $$ It is easy to show that for fixed $A$ , the function $d(x, A)$ is a continuous function of $x$ : Given $x, y \in X$ , one has the inequalities $$ d (x, A) \leq d (x, a) \leq d (x, y) + d (y, a), $$ for each $a \in A$ . It follows that
- **Dependencies:** FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U067

- **Kind:** Lemma 27.5.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6537.
- **Statement/data:** (The Lebesgue number lemma). Let A be an open covering of the metric space $(X, d)$ . If X is compact, there is a $\delta > 0$ such that for each subset of X having diameter less than $\delta$ , there exists an element of A containing it. The number $\delta$ is called a Lebesgue number for the covering A.
- **Dependencies:** FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U068

- **Kind:** Definition/terminology.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6539.
- **Statement/data:** A $\delta>0$ satisfying the conclusion of the Lebesgue number lemma is a Lebesgue number for the covering.
- **Dependencies:** FC02-C03-U067.

### FC02-C03-U069

- **Kind:** Definition.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6559.
- **Statement/data:** A function f from the metric space $(X, d_{X})$ to the metric space $(Y, d_{Y})$ is said to be uniformly continuous if given $\epsilon > 0$ , there is a $\delta > 0$ such that for every pair of points $x_{0}, x_{1}$ of X, $$ d _ {X} (x _ {0}, x _ {1}) < \delta \Longrightarrow d _ {Y} (f (x _ {0}), f (x _ {1})) < \epsilon $$
- **Dependencies:** FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U070

- **Kind:** Theorem 27.6.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6565.
- **Statement/data:** (Uniform continuity theorem). Let $f \cdot X \to Y$ be a continuous map of the compact metric space $(X, d_X)$ to the metric space $(Y, d_Y)$ . Then $f$ is uniformly continuous.
- **Dependencies:** FC02-C02-U109, FC02-C03-U042, FC02-C03-U069.

### FC02-C03-U071

- **Kind:** Definition.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6571.
- **Statement/data:** If X is a space, a point x of X is said to be an isolated point of X if the one-point set ${x}$ is open in X
- **Dependencies:** FC02-C02-U109, FC02-C03-U042.

### FC02-C03-U072

- **Kind:** Theorem 27.7.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6573.
- **Statement/data:** Let X be a nonempty compact Hausdorff space. If X has no isolated points, then X is uncountable.
- **Dependencies:** FC02-C02-U067, FC02-C02-U109, FC02-C03-U042, FC02-C03-U071.

### FC02-C03-U073

- **Kind:** Corollary 27.8.
- **Locator:** §27 “Compact Subspaces of the Real Line”; printed pp. 172–177; extraction L6592.
- **Statement/data:** Every closed interval in R is uncountable.
- **Dependencies:** FC02-C02-U109, FC02-C03-U042, FC02-C03-U062, FC02-C03-U072.

### FC02-C03-U074

- **Kind:** Definition.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6658.
- **Statement/data:** A space $X$ is said to be limit point compact if every infinite subset of $X$ has a limit point.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U075

- **Kind:** Theorem 28.1.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6662.
- **Statement/data:** Compactness implies limit point compactness, but not conversely.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042, FC02-C03-U074.

### FC02-C03-U076

- **Kind:** Example 1.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6668.
- **Statement/data:** Let Y consist of two points, give Y the topology consisting of Y and the empty set. Then the space $X = Z_{+} \times Y$ is limit point compact, for every nonempty subset of X has a limit point. It is not compact, for the covering of X by the open sets $U_{n} = {n} \times Y$ has no finite subcollection covering X
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U077

- **Kind:** Example 2.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6670.
- **Statement/data:** Here is a less trivial example Consider the minimal uncountable well-ordered set $S_{\Omega}$ , in the order topology The space $S_{\Omega}$ is not compact, since it has no largest element However, it is limit point compact: Let $A$ be an infinite subset of $S_{\Omega}$ . Choose a subset $B$ of $A$ that is countably infinite Being countable, the set $B$ has an upper bound $b$ in $S_{\Omega}$ ; then $B$ is a subset of the interval $[a_0, b]$ of $S_{\Omega}$ , where $a_0$ is the smallest element of $S_{\Omega}$ . Since $S_{\Omega}$ has the least upper bound property, the interval $[a_0, b]$ is compact By the preceding theorem, $B$ has a limit point $x$ in $[a_0, b]$ . The point $x$ is also a limit point of $A$ . Thus $S_{\Omega}$ is limit point compact We now show these two versions of compactness coincide for metrizable spaces; for this purpose, we introduce yet another version of compactness called sequential compactness. This result will be used in Chapter 7.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U078

- **Kind:** Definition.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6674.
- **Statement/data:** Let $X$ be a topological space. If $(x_{n})$ is a sequence of points of $X$ , and if $$ n _ {1} < n _ {2} < \dots < n _ {i} < \dots $$ is an increasing sequence of positive integers, then the sequence $(y_{i})$ defined by setting $y_{i} = x_{n_{i}}$ is called a subsequence of the sequence $(x_{n})$ . The space X is said to be sequentially compact if every sequence of points of X has a convergent subsequence. *Theorem 28.2. Let $X$ be a metrizable space. Then the following are equivalent: (1) $X$ is compact. (2) $X$ is limit point compact. (3) $X$ is sequentially compact.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U079

- **Kind:** Definition.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6680.
- **Statement/data:** A subsequence has the form $y_i=x_{n_i}$ for a strictly increasing index sequence; $X$ is sequentially compact if every sequence has a convergent subsequence.
- **Dependencies:** FC02-C02-U066.

### FC02-C03-U080

- **Kind:** Theorem 28.2.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6682.
- **Statement/data:** Let $X$ be a metrizable space. Then the following are equivalent: (1) $X$ is compact. (2) $X$ is limit point compact. (3) $X$ is sequentially compact.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U081

- **Kind:** Example 3.
- **Locator:** §28 “Limit Point Compactness”; printed pp. 178–181; extraction L6720.
- **Statement/data:** Recall that $\bar{S}*{\Omega}$ denotes the minimal uncountable well-ordered set $S*{\Omega}$ with the point $\Omega$ adjoined. (In the order topology, $\Omega$ is a limit point of $S_{\Omega}$ , which is why we introduced the notation $\bar{S}*{\Omega}$ for $S*{\Omega} \cup {\Omega}$ , back in §10.) It is easy to see that the space $\bar{S}*{\Omega}$ is not metrizable, for it does not satisfy the sequence lemma: The point $\Omega$ is a limit point of $S*{\Omega}$ , but it is not the limit of a sequence of points of $S_{\Omega}$ , for any sequence of points of $S_{\Omega}$ has an upper bound in $S_{\Omega}$ . The space $S_{\Omega}$ , on the other hand, does satisfy the sequence lemma, as you can readily check. Nevertheless, $S_{\Omega}$ is not metrizable, for it is limit point compact but not compact.
- **Dependencies:** FC02-C02-U061, FC02-C02-U066, FC02-C03-U042.

### FC02-C03-U082

- **Kind:** Definition.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6775.
- **Statement/data:** A space $X$ is said to be locally compact at $x$ if there is some compact subspace $C$ of $X$ that contains a neighborhood of $x$ . If $X$ is locally compact at each of its points, $X$ is said simply to be locally compact.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U083

- **Kind:** Example 1.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6779.
- **Statement/data:** The real line R is locally compact. The point x lies in some interval $(a, b)$ , which in turn is contained in the compact subspace $[a, b]$ . The subspace Q of rational numbers is not locally compact, as you can check.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U084

- **Kind:** Example 2.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6781.
- **Statement/data:** The space $\mathbb{R}^n$ is locally compact; the point $x$ lies in some basis element $(a_1, b_1) \times \cdot \times (a_n, b_n)$ , which in turn lies in the compact subspace $[a_1, b_1] \times \cdot \times [a_n, b_n]$ . The space $\mathbb{R}^\omega$ is not locally compact; none of its basis elements are contained in compact subspaces. For if $$ B = (a _ {1}, b _ {1}) \times \cdot \times (a _ {n}, b _ {n}) \times \mathbb {R} \times \cdot \times \mathbb {R} \times $$
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U085

- **Kind:** Example 3.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6795.
- **Statement/data:** Every simply ordered set X having the least upper bound property is locally compact: Given a basis element for X, it is contained in a closed interval in X, which is compact.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U086

- **Kind:** Theorem 29.1.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6799.
- **Statement/data:** Let $X$ be a space. Then $X$ is locally compact Hausdorff if and only if there exists a space $Y$ satisfying the following conditions: (1) $X$ is a subspace of $Y$ . (2) The set $Y - X$ consists of a single point. (3) Y is a compact Hausdorff space. If $Y$ and $Y'$ are two spaces satisfying these conditions, then there is a homeomorphism of $Y$ with $Y'$ that equals the identity map on $X$ .
- **Dependencies:** FC02-C02-U067, FC02-C03-U042, FC02-C03-U082.

### FC02-C03-U087

- **Kind:** Definition.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6840.
- **Statement/data:** If Y is a compact Hausdorff space and X is a proper subspace of Y whose closure equals Y, then Y is said to be a compactification of X. If Y - X equals a single point, then Y is called the one-point compactification of X.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U088

- **Kind:** Named examples/comparison.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6844.
- **Statement/data:** The one-point compactification of $\mathbb R$ is homeomorphic to $S^1$, and that of $\mathbb R^2$ to $S^2$.
- **Dependencies:** FC02-C03-U087.

### FC02-C03-U089

- **Kind:** Example 4.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6844.
- **Statement/data:** The one-point compactification of the real line $\mathbb{R}$ is homeomorphic with the circle, as you may readily check. Similarly, the one-point compactification of $\mathbb{R}^2$ is homeomorphic to the sphere $S^2$ . If $\mathbb{R}^2$ is looked at as the space $\mathbb{C}$ of complex numbers, then $\mathbb{C} \cup {\infty}$ is called the Riemann sphere, or the extended complex plane In some ways our definition of local compactness is not very satisfying. Usually one says that a space X satisfies a given property “locally” if every $x \in X$ has “arbitrarily small” neighborhoods having the given property. Our definition of local compactness has nothing to do with “arbitrarily small” neighborhoods, so there is some question whether we should call it local compactness at all. Here is another formulation of local compactness, one more truly “local” in nature; it is equivalent to our definition when X is Hausdorff.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042.

### FC02-C03-U090

- **Kind:** Theorem 29.2.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6850.
- **Statement/data:** Let X be a Hausdorff space Then X is locally compact if and only if given x in X, and given a neighborhood U of x, there is a neighborhood V of x such that $\bar{V}$ is compact and $\bar{V} \subset U$
- **Dependencies:** FC02-C02-U067, FC02-C03-U042, FC02-C03-U082.

### FC02-C03-U091

- **Kind:** Corollary 29.3.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6854.
- **Statement/data:** Let $X$ be locally compact Hausdorff; let $A$ be a subspace of $X$ . If $A$ is closed in $X$ or open in $X$ , then $A$ is locally compact.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042, FC02-C03-U090.

### FC02-C03-U092

- **Kind:** Corollary 29.4.
- **Locator:** §29 “Local Compactness”; printed pp. 182–186; extraction L6860.
- **Statement/data:** A space $X$ is homeomorphic to an open subspace of a compact Hausdorff space if and only if $X$ is locally compact Hausdorff.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042, FC02-C03-U086.

## C04 — Countability and Separation Axioms

Units: 42.

### FC02-C04-U001

- **Kind:** Definition.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L6996.
- **Statement/data:** A space X is said to have a countable basis at x if there is a countable collection B of neighborhoods of x such that each neighborhood of x contains at least one of the elements of B. A space that has a countable basis at each of its points is said to satisfy the first countability axiom, or to be first-countable.
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U002

- **Kind:** Definition.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L6998.
- **Statement/data:** $X$ is first-countable if it has a countable neighborhood basis at every point.
- **Dependencies:** FC02-C04-U001.

### FC02-C04-U003

- **Kind:** Theorem 30.1.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7002.
- **Statement/data:** Let $X$ be a topological space. (a) Let $A$ be a subset of $X$ . If there is a sequence of points of $A$ converging to $x$ , then $x \in \bar{A}$ ; the converse holds if $X$ is first-countable. (b) Let $f: X \to Y$ . If $f$ is continuous, then for every convergent sequence $x_{n} \to x$ in $X$ , the sequence $f(x_{n})$ converges to $f(x)$ . The converse holds if $X$ is first-countable.
- **Dependencies:** FC02-C02-U008, FC02-C04-U001.

### FC02-C04-U004

- **Kind:** Definition.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7012.
- **Statement/data:** If a space X has a countable basis for its topology, then X is said to satisfy the second countability axiom, or to be second-countable.
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U005

- **Kind:** Example 1.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7018.
- **Statement/data:** The real line $\mathbb{R}$ has a countable basis—the collection of all open intervals $(a, b)$ with rational end points. Likewise, $\mathbb{R}^n$ has a countable basis—the collection of all products of intervals having rational end points. Even $\mathbb{R}^\omega$ has a countable basis—the collection of all products $\prod_{n \in \mathbb{Z}_+} U_n$ , where $U_n$ is an open interval with rational end points for finitely many values of $n$ , and $U_n = \mathbb{R}$ for all other values of $n$ .
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U006

- **Kind:** Example 2.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7020.
- **Statement/data:** In the uniform topology, $\mathbb{R}^{\omega}$ satisfies the first countability axiom (being metrizable). However, it does not satisfy the second. To verify this fact, we first show that if $X$ is a space having a countable basis $\mathcal{B}$ , then any discrete subspace $A$ of $X$ must be countable Choose, for each $a \in A$ , a basis element $B_a$ that intersects $A$ in the point $a$ alone. If $a$ and $b$ are distinct points of $A$ , the sets $B_a$ and $B_b$ are different, since the first contains $a$ and the second does not. It follows that the map $a \to B_a$ is an injection of $A$ into $\mathcal{B}$ , so $A$ must be countable.
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U007

- **Kind:** Theorem 30.2.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7026.
- **Statement/data:** A subspace of a first-countable space is first-countable, and a countable product of first-countable spaces is first-countable. A subspace of a second-countable space is second-countable, and a countable product of second-countable spaces is second-countable.
- **Dependencies:** FC02-C02-U008, FC02-C04-U001, FC02-C04-U004.

### FC02-C04-U008

- **Kind:** Definition.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7034.
- **Statement/data:** A subset $A$ of a space $X$ is said to be dense in $X$ if $\hat{A} = X$ .
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U009

- **Kind:** Theorem 30.3.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7036.
- **Statement/data:** Suppose that $X$ has a countable basis. Then: (a) Every open covering of $X$ contains a countable subcollection covering $X$ . (b) There exists a countable subset of $X$ that is dense in $X$ .
- **Dependencies:** FC02-C02-U008, FC02-C04-U004, FC02-C04-U008.

### FC02-C04-U010

- **Kind:** Definition/comparison.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7048.
- **Statement/data:** A space is Lindelöf if every open cover has a countable subcover; it is separable if it has a countable dense subset.
- **Dependencies:** FC02-C04-U009.

### FC02-C04-U011

- **Kind:** Example 3.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7052.
- **Statement/data:** The space $\mathbb{R}_{\ell}$ satisfies all the countability axioms but the second.
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U012

- **Kind:** Example 4.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7084.
- **Statement/data:** The product of two Lindelöf spaces need not be Lindelöf. Although the space $\mathbb{R}*{\ell}$ is Lindelöf, we shall show that the product space $\mathbb{R}*{\ell} \times \mathbb{R}*{\ell} = \mathbb{R}*{\ell}^{2}$ is not. The space $\mathbb{R}*{\ell}^{2}$ is an extremely useful example in topology called the Sorgenfrey plane The space $\mathbb{R}*{\ell}^{2}$ has as basis all sets of the form $[a, b) \times [c, d)$ . To show it is not Lindelöf, consider the subspace $$ L = {x \times (- x) \mid x \in \mathbb {R} _ {\ell} } $$
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U013

- **Kind:** Example 5.
- **Locator:** §30 “The Countability Axioms”; printed pp. 190–194; extraction L7103.
- **Statement/data:** A subspace of a Lindelöf space need not be Lindelöf. The ordered square $I_0^2$ is compact; therefore it is Lindelöf, trivially. However, the subspace $A = I \times (0,1)$ is not Lindelöf. For $A$ is the union of the disjoint sets $U_x = {x} \times (0,1)$ , each of which is open in $A$ . This collection of sets is uncountable, and no proper subcollection covers $A$ .
- **Dependencies:** FC02-C02-U008.

### FC02-C04-U014

- **Kind:** Recall/definition.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7155.
- **Statement/data:** Hausdorff means distinct points admit disjoint neighborhoods.
- **Dependencies:** FC02-C02-U067.

### FC02-C04-U015

- **Kind:** Definition.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7157.
- **Statement/data:** Suppose that one-point sets are closed in X. Then X is said to be regular if for each pair consisting of a point x and a closed set B disjoint from x, there exist disjoint open sets containing x and B, respectively. The space X is said to be normal if for each pair A, B of disjoint closed sets of X, there exist disjoint open sets containing A and B, respectively.
- **Dependencies:** FC02-C02-U045, FC02-C02-U067.

### FC02-C04-U016

- **Kind:** Terminology.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7161.
- **Statement/data:** The $T_1$, Hausdorff, regular, and normal conditions are separation axioms.
- **Dependencies:** —.

### FC02-C04-U017

- **Kind:** Lemma 31.1.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7171.
- **Statement/data:** Let $X$ be a topological space. Let one-point sets in $X$ be closed. (a) $X$ is regular if and only if given a point $x$ of $X$ and a neighborhood $U$ of $x$ , there is a neighborhood $V$ of $x$ such that $\bar{V} \subset U$ . (b) X is normal if and only if given a closed set A and an open set U containing A, there is an open set V containing A such that $\bar{V} \subset U$ .
- **Dependencies:** FC02-C02-U045, FC02-C02-U067, FC02-C04-U015.

### FC02-C04-U018

- **Kind:** Theorem 31.2.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7185.
- **Statement/data:** (a) A subspace of a Hausdorff space is Hausdorff; a product of Hausdorff spaces is Hausdorff. (b) A subspace of a regular space is regular; a product of regular spaces is regular.
- **Dependencies:** FC02-C02-U045, FC02-C02-U067, FC02-C04-U015.

### FC02-C04-U019

- **Kind:** Example 1.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7199.
- **Statement/data:** The space $\mathbb{R}_K$ is Hausdorff but not regular. Recall that $\mathbb{R}*K$ denotes the reals in the topology having as basis all open intervals $(a, b)$ and all sets of the form $(a, b) - K$ , where $K = {1/n \mid n \in \mathbb{Z}*+}$ . This space is Hausdorff, because any two distinct points have disjoint open intervals containing them.
- **Dependencies:** FC02-C02-U045, FC02-C02-U067.

### FC02-C04-U020

- **Kind:** Example 2.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7206.
- **Statement/data:** The space $\mathbb{R}*{\ell}$ is normal It is immediate that one-point sets are closed in $\mathbb{R}*{\ell}$ , since the topology of $\mathbb{R}*{\ell}$ is finer than that of $\mathbb{R}$ . To check normality, suppose that $A$ and $B$ are disjoint closed sets in $\mathbb{R}*{\ell}$ . For each point $a$ of $A$ choose a basis element $[a, x_{a})$ not intersecting $B$ , and for each point $b$ of $B$ choose a basis element $[b, x_{b})$ not intersecting $A$ . The open sets $$ U = \bigcup_ {a \in A} [ a, x _ {a}) \quad \text { and } \quad V = \bigcup_ {b \in B} [ b, x _ {b}) $$
- **Dependencies:** FC02-C02-U045, FC02-C02-U067.

### FC02-C04-U021

- **Kind:** Example 3.
- **Locator:** §31 “The Separation Axioms”; printed pp. 195–199; extraction L7214.
- **Statement/data:** The Sorgenfrey plane $\mathbb{R}*{\ell}^{2}$ is not normal The space $\mathbb{R}*{\ell}$ is regular (in fact, normal), so the product space $\mathbb{R}*{\ell}^{2}$ is also regular. Thus this example serves two purposes. It shows that a regular space need not be normal, and it shows that the product of two normal spaces need not be normal We suppose $\mathbb{R}*{\ell}^{2}$ is normal and derive a contradiction Let $L$ be the subspace of $\mathbb{R}*{\ell}^{2}$ consisting of all points of the form $x \times (-x)$ . Then $L$ is closed in $\mathbb{R}*{\ell}^{2}$ , and $L$ has the discrete topology. Hence every subset $A$ of $L$ , being closed in $L$ , is closed in $\mathbb{R}*{\ell}^{2}$ . Because $L - A$ is also closed in $\mathbb{R}*{\ell}^{2}$ , this means that for every nonempty proper subset $A$ of $L$ , one can find disjoint open sets $U_{A}$ and $V_{A}$ containing $A$ and $L - A$ , respectively Let $D$ denote the set of points of $\mathbb{R}_t^2$ having rational coordinates; it is dense in $\mathbb{R}_L^2$ . We define a map $\theta$ that assigns, to each subset of the line $L$ , a subset of the set $D$ , by setting $$ \begin{array}{l l} \theta (A) = D \cap U _ {A} & \text { if } \varnothing \subsetneq A \subsetneq L, \ \theta (\varnothing) = \varnothing , \ \theta (L) = D. \end{array} $$
- **Dependencies:** FC02-C02-U045, FC02-C02-U067.

### FC02-C04-U022

- **Kind:** Theorem 32.1.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7298.
- **Statement/data:** Every regular space with a countable basis is normal.
- **Dependencies:** FC02-C04-U004, FC02-C04-U015.

### FC02-C04-U023

- **Kind:** Theorem 32.2.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7323.
- **Statement/data:** Every metrizable space is normal.
- **Dependencies:** FC02-C02-U109, FC02-C04-U015.

### FC02-C04-U024

- **Kind:** Theorem 32.3.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7339.
- **Statement/data:** Every compact Hausdorff space is normal.
- **Dependencies:** FC02-C02-U067, FC02-C03-U042, FC02-C04-U015.

### FC02-C04-U025

- **Kind:** Theorem 32.4.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7353.
- **Statement/data:** Every well-ordered set X is normal in the order topology. It is, in fact, true that every order topology is normal (see Example 39 of [S-S]); but we shall not have occasion to use this stronger result.
- **Dependencies:** FC02-C01-U133, FC02-C04-U015.

### FC02-C04-U026

- **Kind:** Example 1.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7369.
- **Statement/data:** If $J$ is uncountable, the product space $\mathbb{R}^J$ is not normal. The proof is fairly difficult; we leave it as a challenging exercise (see Exercise 9).
- **Dependencies:** FC02-C04-U015.

### FC02-C04-U027

- **Kind:** Example 2.
- **Locator:** §32 “Normal Spaces”; printed pp. 200–206; extraction L7373.
- **Statement/data:** The product space $S_{\Omega} \times \bar{S}*{\Omega}$ is not normal. $^{\dagger}$ Consider the well-ordered set $\tilde{S}*{\Omega}$ , in the order topology, and consider the subset $S_{\Omega}$ , in the subspace topology (which is the same as the order topology). Both spaces are normal, by Theorem 32.4. We shall show that the product space $S_{\Omega} \times \tilde{S}*{\Omega}$ is not normal. This example serves three purposes. First, it shows that a regular space need not be normal, for $S*{\Omega} \times \bar{S}*{\Omega}$ is a product of regular spaces and therefore regular. Second, it shows that a subspace of a normal space need not be normal, for $S*{\Omega} \times \bar{S}*{\Omega}$ is a subspace of $\bar{S}*{\Omega} \times \bar{S}*{\Omega}$ , which is a compact Hausdorff space and therefore normal. Third, it shows that the product of two normal spaces need not be normal. First, we consider the space $\tilde{S}*{\Omega} \times \tilde{S}*{\Omega}$ , and its "diagonal" $\Delta = {x \times x \mid x \in \tilde{S}*{\Omega}}$ . Because $\tilde{S}*{\Omega}$ is Hausdorff, $\Delta$ is closed in $\tilde{S}*{\Omega} \times \tilde{S}*{\Omega}$ . If $U$ and $V$ are disjoint neighborhoods of $x$ and $y$ , respectively, then $U \times V$ is a neighborhood of $x \times y$ that does not intersect $\Delta$ . Therefore, in the subspace $S*{\Omega} \times \bar{S}_{\Omega}$ , the set $$ A = \Delta \cap (S _ {\Omega} \times \bar {S} _ {\Omega}) = \Delta - {\Omega \times \Omega } $$
- **Dependencies:** FC02-C04-U015.

### FC02-C04-U028

- **Kind:** Theorem 33.1.
- **Locator:** §33 “The Urysohn Lemma”; printed pp. 207–213; extraction L7521.
- **Statement/data:** (Urysohn lemma). Let X be a normal space, let A and B be disjoint closed subsets of X. Let $[a, b]$ be a closed interval in the real line. Then there exists a continuous map $$ f: X \longrightarrow [ a, b ] $$ such that $f(x) = a$ for every $x$ in $A$ , and $f(x) = b$ for every $x$ in $B$ .
- **Dependencies:** FC02-C02-U074, FC02-C04-U015.

### FC02-C04-U029

- **Kind:** Definition.
- **Locator:** §33 “The Urysohn Lemma”; printed pp. 207–213; extraction L7653.
- **Statement/data:** If $A$ and $B$ are two subsets of the topological space $X$ , and if there is a continuous function $f$ . $X \to [0,1]$ such that $f(A) = {0}$ and $f(B) = {1}$ , we say that $A$ and $B$ can be separated by a continuous function.
- **Dependencies:** FC02-C02-U074, FC02-C04-U015.

### FC02-C04-U030

- **Kind:** Definition.
- **Locator:** §33 “The Urysohn Lemma”; printed pp. 207–213; extraction L7663.
- **Statement/data:** A space X is completely regular if one-point sets are closed in X and if for each point $x_{0}$ and each closed set A not containing $x_{0}$ , there is a continuous function $f: X \to [0, 1]$ such that $f(x_{0}) = 1$ and $f(A) = {0}$ .
- **Dependencies:** FC02-C02-U074, FC02-C04-U015.

### FC02-C04-U031

- **Kind:** Theorem 33.2.
- **Locator:** §33 “The Urysohn Lemma”; printed pp. 207–213; extraction L7671.
- **Statement/data:** A subspace of a completely regular space is completely regular. A product of completely regular spaces is completely regular.
- **Dependencies:** FC02-C02-U074, FC02-C04-U015, FC02-C04-U030.

### FC02-C04-U032

- **Kind:** Example 1.
- **Locator:** §33 “The Urysohn Lemma”; printed pp. 207–213; extraction L7689.
- **Statement/data:** The spaces $\mathbb{R}*{\ell}^{2}$ and $S*{\Omega} \times \bar{S}_{\Omega}$ are completely regular but not normal. For they are products of spaces that are completely regular (in fact, normal).
- **Dependencies:** FC02-C02-U074, FC02-C04-U015.

### FC02-C04-U033

- **Kind:** Theorem 34.1.
- **Locator:** §34 “The Urysohn Metrization Theorem”; printed pp. 214–218; extraction L7795.
- **Statement/data:** (Urysohn metrization theorem). Every regular space X with a countable basis is metrizable.
- **Dependencies:** FC02-C04-U004, FC02-C04-U015, FC02-C04-U028.

### FC02-C04-U034

- **Kind:** Theorem 34.2.
- **Locator:** §34 “The Urysohn Metrization Theorem”; printed pp. 214–218; extraction L7891.
- **Statement/data:** (Imbedding theorem). Let $X$ be a space in which one-point sets are closed. Suppose that ${f_{\alpha}}*{\alpha \in J}$ is an indexed family of continuous functions $f*{\alpha} \cdot X \to \mathbb{R}$ satisfying the requirement that for each point $x_0$ of $X$ and each neighborhood $U$ of $x_0$ , there is an index $\alpha$ such that $f_{\alpha}$ is positive at $x_0$ and vanishes outside $U$ . Then the function $F: X \to \mathbb{R}^J$ defined by $$ F (x) = \left(f _ {\alpha} (x)\right) _ {\alpha \in J} $$ is an imbedding of $X$ in $\mathbb{R}^J$ . If $f_{\alpha}$ maps $X$ into [0, 1] for each $\alpha$ , then $F$ imbeds $X$ in $[0, 1]^J$ .
- **Dependencies:** FC02-C02-U067, FC02-C02-U074, FC02-C04-U015, FC02-C04-U028.

### FC02-C04-U035

- **Kind:** Theorem 34.3.
- **Locator:** §34 “The Urysohn Metrization Theorem”; printed pp. 214–218; extraction L7903.
- **Statement/data:** A space $X$ is completely regular if and only if it is homeomorphic to a subspace of $[0,1]^J$ for some $J$ .
- **Dependencies:** FC02-C04-U015, FC02-C04-U028, FC02-C04-U030, FC02-C04-U034.

### FC02-C04-U036

- **Kind:** Theorem 35.1.
- **Locator:** *§35 “The Tietze Extension Theorem”; printed pp. 219–223; extraction L7929.
- **Statement/data:** (Tietze extension theorem). Let $X$ be a normal space; let $A$ be a closed subspace of $X$ . (a) Any continuous map of $A$ into the closed interval $[a, b]$ of $\mathbb{R}$ may be extended to a continuous map of all of $X$ into $[a, b]$ . (b) Any continuous map of $A$ into $\mathbb{R}$ may be extended to a continuous map of all of $X$ into $\mathbb{R}$ .
- **Dependencies:** FC02-C02-U134, FC02-C04-U015, FC02-C04-U028.

### FC02-C04-U037

- **Kind:** Definition.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8141.
- **Statement/data:** An $m$ -manifold is a Hausdorff space $X$ with a countable basis such that each point $x$ of $X$ has a neighborhood that is homeomorphic with an open subset of $\mathbb{R}^m$ .
- **Dependencies:** FC02-C02-U067, FC02-C04-U004, FC02-C04-U015.

### FC02-C04-U038

- **Kind:** Terminology.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8143.
- **Statement/data:** A 1-manifold is called a curve and a 2-manifold a surface.
- **Dependencies:** FC02-C04-U037.

### FC02-C04-U039

- **Kind:** Definition.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8149.
- **Statement/data:** The support of $\phi:X\to\mathbb R$ is the closure of $\phi^{-1}(\mathbb R-{0})$.
- **Dependencies:** FC02-C02-U054.

### FC02-C04-U040

- **Kind:** Definition.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8151.
- **Statement/data:** Let ${U_1, \ldots, U_n}$ be a finite indexed open covering of the space $X$ . An indexed family of continuous functions $$ \phi_ {i}: X \longrightarrow [ 0, 1 ] \quad \text { for } i = 1, \dots , n, $$ is said to be a partition of unity dominated by ${U_{i}}$ if (1) (support $\phi_i$ ) $\subset U_i$ for each $i$ . (2) $\sum_{i=1}^{n} \phi_i(x) = 1$ for each $x$ .
- **Dependencies:** FC02-C02-U067, FC02-C04-U004, FC02-C04-U015.

### FC02-C04-U041

- **Kind:** Theorem 36.1.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8163.
- **Statement/data:** (Existence of finite partitions of unity). Let ${U_1, \ldots, U_n}$ be a finite open covering of the normal space $X$ . Then there exists a partition of unity dominated by ${U_i}$
- **Dependencies:** FC02-C02-U067, FC02-C04-U004, FC02-C04-U015, FC02-C04-U040.

### FC02-C04-U042

- **Kind:** Theorem 36.2.
- **Locator:** *§36 “Imbeddings of Manifolds”; printed pp. 224–227; extraction L8211.
- **Statement/data:** If $X$ is a compact $m$ -manifold, then $X$ can be imbedded in $\mathbb{R}^N$ for some positive integer $N$ .
- **Dependencies:** FC02-C02-U067, FC02-C04-U004, FC02-C04-U015, FC02-C04-U037, FC02-C04-U041.

## C05 — The Tychonoff Theorem

Units: 15.

### FC02-C05-U001

- **Kind:** Lemma 37.1.
- **Locator:** §37 “The Tychonoff Theorem”; printed pp. 230–236; extraction L8399.
- **Statement/data:** Let X be a set; let A be a collection of subsets of X having the finite intersection property. Then there is a collection D of subsets of X such that D contains A, and D has the finite intersection property, and no collection of subsets of X that properly contains D has this property. We often say that a collection D satisfying the conclusion of this theorem is maximal with respect to the finite intersection property
- **Dependencies:** FC02-C01-U147, FC02-C02-U100, FC02-C03-U059, FC02-C03-U060.

### FC02-C05-U002

- **Kind:** Lemma 37.2.
- **Locator:** §37 “The Tychonoff Theorem”; printed pp. 230–236; extraction L8427.
- **Statement/data:** Let $X$ be a set; let $\mathcal{D}$ be a collection of subsets of $X$ that is maximal with respect to the finite intersection property. Then: (a) Any finite intersection of elements of $\mathcal{D}$ is an element of $\mathcal{D}$ . (b) If $A$ is a subset of $X$ that intersects every element of $\mathcal{D}$ , then $A$ is an element of $\mathcal{D}$ .
- **Dependencies:** FC02-C01-U147, FC02-C02-U100, FC02-C03-U059, FC02-C03-U060.

### FC02-C05-U003

- **Kind:** Theorem 37.3.
- **Locator:** §37 “The Tychonoff Theorem”; printed pp. 230–236; extraction L8451.
- **Statement/data:** (Tychonoff theorem). An arbitrary product of compact spaces is compact in the product topology
- **Dependencies:** FC02-C01-U147, FC02-C02-U100, FC02-C03-U042, FC02-C03-U060, FC02-C05-U002.

### FC02-C05-U004

- **Kind:** Definition.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8567.
- **Statement/data:** A compactification of a space X is a compact Hausdorff space Y containing X as a subspace such that $\bar{X} = Y$ . Two compactifications $Y_{1}$ and $Y_{2}$ of X are said to be equivalent if there is a homeomorphism $h : Y_{1} \to Y_{2}$ such that $\boldsymbol{h}(x) = x$ for every $x \in X$ .
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U005

- **Kind:** Lemma 38.1.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8571.
- **Statement/data:** Let X be a space; suppose that $h : X \to Z$ is an imbedding of X in the compact Hausdorff space Z. Then there exists a corresponding compactification Y of X; it has the property that there is an imbedding $H : Y \to Z$ that equals h on X. The compactification Y is uniquely determined up to equivalence. We call Y the compactification induced by the imbedding h.
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U006

- **Kind:** Example 1.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8589.
- **Statement/data:** Take the unit circle $S^1$ in $\mathbb{R}^2$ and let $h$ . (0, 1) → $S^1$ be the map $$ h (t) = (\cos 2 \pi t) \times (\sin 2 \pi t). $$
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U007

- **Kind:** Example 2.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8597.
- **Statement/data:** Let Y be the space [0, 1] Then Y is a compactification of X, it is obtained by “adding one point at each end of (0, 1)”
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U008

- **Kind:** Example 3.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8599.
- **Statement/data:** Consider the square $[-1, 1]^2$ in $\mathbb{R}^2$ and let $h \to (-1, 1]^2$ be the map $$ h (x) = x \times \sin (1 / x). $$
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U009

- **Kind:** Example 4.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8613.
- **Statement/data:** Let $X = (0,1)$ . Consider the one-point compactification of $X$ given in Example I. A bounded continuous function $f:(0,1)\to \mathbb{R}$ is extendable to this compactification if and only if the limits $$ \lim _ {x \rightarrow 0 +} f (x) \quad \text { and } \quad \lim _ {x \rightarrow 1 -} f (x) $$
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U010

- **Kind:** Construction.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8639.
- **Statement/data:** The Stone–Čech construction embeds a completely regular $X$ by all bounded continuous real-valued functions into a product of compact intervals and takes the closure.
- **Dependencies:** FC02-C04-U035, FC02-C05-U003.

### FC02-C05-U011

- **Kind:** Theorem 38.2.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8641.
- **Statement/data:** Let X be a completely regular space. There exists a compactification Y of X having the property that every bounded continuous map $f : X \to R$ extends uniquely to a continuous map of Y into R.
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U012

- **Kind:** Lemma 38.3.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8665.
- **Statement/data:** Let $A \subset X$ ; let $f: A \to Z$ be a continuous map of $A$ into the Hausdorff space $Z$ . There is at most one extension of $f$ to a continuous function $g: \tilde{A} \to Z$ .
- **Dependencies:** FC02-C02-U054, FC02-C02-U067, FC02-C02-U074, FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

### FC02-C05-U013

- **Kind:** Theorem 38.4.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8669.
- **Statement/data:** Let X be a completely regular space; let Y be a compactification of X satisfying the extension property of Theorem 38.2 Given any continuous map $f \cdot X \to C$ of X into a compact Hausdorff space C, the map f extends uniquely to a continuous map $g \cdot Y \to C$ .
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003, FC02-C05-U011, FC02-C05-U012.

### FC02-C05-U014

- **Kind:** Theorem 38.5.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8679.
- **Statement/data:** Let X be a completely regular space. If $Y_{1}$ and $Y_{2}$ are two compactifications of X satisfying the extension property of Theorem 38.2, then $Y_{1}$ and $Y_{2}$ are equivalent.
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003, FC02-C05-U011, FC02-C05-U013.

### FC02-C05-U015

- **Kind:** Definition.
- **Locator:** §38 “The Stone-Čech Compactification”; printed pp. 237–242; extraction L8687.
- **Statement/data:** For each completely regular space X, let us choose, once and for all, a compactification of X satisfying the extension condition of Theorem 38.2. We will denote this compactification of X by $\beta(X)$ and call it the Stone-Čech compactification of X. It is characterized by the fact that any continuous map $f \cdot X \to C$ of X into a compact Hausdorff space C extends uniquely to a continuous map $g \cdot \beta(X) \to C$ .
- **Dependencies:** FC02-C03-U087, FC02-C04-U030, FC02-C05-U003.

## C06 — Metrization Theorems and Paracompactness

Units: 32.

### FC02-C06-U001

- **Kind:** Definition.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8763.
- **Statement/data:** Let X be a topological space. A collection A of subsets of X is said to be locally finite in X if every point of X has a neighborhood that intersects only finitely many elements of A
- **Dependencies:** FC02-C02-U001.

### FC02-C06-U002

- **Kind:** Example 1.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8765.
- **Statement/data:** The collection of intervals $$ \mathcal {A} = {(n, n + 2) \mid n \in \mathbb {Z} } $$
- **Dependencies:** FC02-C02-U001.

### FC02-C06-U003

- **Kind:** Lemma 39.1.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8783.
- **Statement/data:** Let $\mathcal{A}$ be a locally finite collection of subsets of $X$ . Then: (a) Any subcollection of $\mathcal{A}$ is locally finite. (b) The collection $\mathcal{B} = {\bar{A}}*{A\in \mathcal{A}}$ of the closures of the elements of $\mathcal{A}$ is locally finite. (c) $\overline{\bigcup*{A\in\mathcal{A}}A}=\bigcup_{A\in\mathcal{A}}\bar{A}$ .
- **Dependencies:** FC02-C02-U001, FC02-C06-U001.

### FC02-C06-U004

- **Kind:** Definition.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8801.
- **Statement/data:** An indexed family is locally finite if each point has a neighborhood intersecting $A_\alpha$ for only finitely many indices $\alpha$.
- **Dependencies:** FC02-C06-U001.

### FC02-C06-U005

- **Kind:** Definition.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8805.
- **Statement/data:** A collection B of subsets of X is said to be countably locally finite if B can be written as the countable union of collections $B_{n}$ , each of which is locally finite.
- **Dependencies:** FC02-C02-U001.

### FC02-C06-U006

- **Kind:** Definition.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8809.
- **Statement/data:** Let A be a collection of subsets of the space X. A collection B of subsets of X is said to be a refinement of A (or is said to refine A) if for each element B of B, there is an element A of A containing B. If the elements of B are open sets, we call B an open refinement of A; if they are closed sets, we call B a closed refinement
- **Dependencies:** FC02-C02-U001.

### FC02-C06-U007

- **Kind:** Lemma 39.2.
- **Locator:** §39 “Local Finiteness”; printed pp. 244–247; extraction L8811.
- **Statement/data:** Let $X$ be a metrizable space. If $\mathcal{A}$ is an open covering of $X$ , then there is an open covering $\mathcal{E}$ of $X$ refining $\mathcal{A}$ that is countably locally finite.
- **Dependencies:** FC02-C02-U001, FC02-C02-U109, FC02-C06-U001, FC02-C06-U006.

### FC02-C06-U008

- **Kind:** Definition.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8895.
- **Statement/data:** A subset $A$ of a space $X$ is called a $G_{\delta}$ set in $X$ if it equals the intersection of a countable collection of open subsets of $X$ .
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001.

### FC02-C06-U009

- **Kind:** Example 1.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8897.
- **Statement/data:** Each open subset of $X$ is a $G_{\delta}$ set, initially In a first-countable Hausdorff space, each one-point set is a $G_{\delta}$ set The one-point subset ${\Omega}$ of $\bar{S}*{\Omega}$ is not a $G*{\delta}$ set, as you can check
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001.

### FC02-C06-U010

- **Kind:** Example 2.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8899.
- **Statement/data:** In a metric space $X$ , each closed set is a $G_{\delta}$ set. Given $A \subset X$ , let $U(A, \epsilon)$ denote the $\epsilon$ -neighborhood of $A$ . If $A$ is closed, you can check that $$ A = \bigcap_ {n \in \mathbf {Z} _ {+}} U (A, 1 / n) $$
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001.

### FC02-C06-U011

- **Kind:** Lemma 40.1.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8905.
- **Statement/data:** Let X be a regular space with a basis B that is countably locally finite. Then X is normal, and every closed set in X is a $G_{\delta}$ set in X
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001, FC02-C06-U005, FC02-C06-U008.

### FC02-C06-U012

- **Kind:** Lemma 40.2.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8957.
- **Statement/data:** Let $X$ be normal; let $A$ be a closed $G_{\delta}$ set in $X$ . Then there is a continuous function $f \cdot X \to [0,1]$ such that $f(x) = 0$ for $x \in A$ and $f(x) > 0$ for $x \notin A$ .
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001, FC02-C06-U008.

### FC02-C06-U013

- **Kind:** Theorem 40.3.
- **Locator:** §40 “The Nagata-Smirnov Metrization Theorem”; printed pp. 248–251; extraction L8961.
- **Statement/data:** (Nagata-Smirnov metrization theorem). A space X is metrizable if and only if X is regular and has a basis that is countably locally finite.
- **Dependencies:** FC02-C02-U008, FC02-C04-U015, FC02-C06-U001, FC02-C06-U005, FC02-C06-U011, FC02-C06-U012.

### FC02-C06-U014

- **Kind:** Comparison.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9051.
- **Statement/data:** Paracompactness weakens compactness by replacing a finite subcover requirement with existence of a locally finite open refinement.
- **Dependencies:** FC02-C03-U042.

### FC02-C06-U015

- **Kind:** Definition.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9059.
- **Statement/data:** A space $X$ is paracompact if every open covering $\mathcal{A}$ of $X$ has a locally finite open refinement $\mathcal{B}$ that covers $X$ .
- **Dependencies:** FC02-C02-U067.

### FC02-C06-U016

- **Kind:** Example 1.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9063.
- **Statement/data:** The space $\mathbb{R}^n$ is paracompact Let $X = \mathbb{R}^n$ . Let $\mathcal{A}$ be an open covering of $X$ . Let $B_0 = \varnothing$ , and for each positive integer $m$ , let $B_m$ denote the open ball of radius $m$ centered at the origin. Given $m$ , choose finitely many elements of $\mathcal{A}$ that cover $\tilde{B}*m$ and intersect each one with the open set $X - \tilde{B}*{m-1}$ , let this finite collection of open sets be denoted $\mathcal{C}_m$ . Then the collection $\mathcal{C} = \bigcup \mathcal{C}_m$ is a refinement of $\mathcal{A}$ . It is clearly locally finite, for the open set $B_m$ intersects only finitely many elements of $\mathcal{C}$ , namely those elements belonging to the collection $\mathcal{C}_1 \cup \cup \mathcal{C}_m$ . Finally, $\mathcal{C}$ covers $X$ . For, given $x$ , let $m$ be the smallest integer such that $x \in \tilde{B}_m$ . Then $x$ belongs to an element of $\mathcal{C}_m$ , by definition.
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U017

- **Kind:** Theorem 41.1.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9067.
- **Statement/data:** Every paracompact Hausdorff space $X$ is normal
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U018

- **Kind:** Theorem 41.2.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9087.
- **Statement/data:** Every closed subspace of a paracompact space is paracompact.
- **Dependencies:** FC02-C02-U045, FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U019

- **Kind:** Example 2.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9097.
- **Statement/data:** A paracompact subspace of a Hausdorff space $X$ need not be closed in $X$ . Indeed, the open interval $(0,1)$ is paracompact, being homeomorphic to $\mathbb{R}$ , but it is not closed in $\mathbb{R}$
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U020

- **Kind:** Example 3.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9099.
- **Statement/data:** A subspace of a paracompact space need not be paracompact. The space $\bar{S}*{\Omega} \times \bar{S}*{\Omega}$ is compact and, therefore, paracompact. But the subspace $S_{\Omega} \times \bar{S}_{\Omega}$ is not paracompact, for it is Hausdorff but not normal.
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U021

- **Kind:** Lemma 41.3.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9103.
- **Statement/data:** Let X be regular. Then the following conditions on X are equivalent: Every open covering of X has a refinement that is: (1) An open covering of X and countably locally finite. (2) A covering of $X$ and locally finite. (3) A closed covering of $X$ and locally finite. (4) An open covering of $X$ and locally finite.
- **Dependencies:** FC02-C02-U067, FC02-C04-U015, FC02-C06-U015.

### FC02-C06-U022

- **Kind:** Theorem 41.4.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9194.
- **Statement/data:** Every metrizable space is paracompact
- **Dependencies:** FC02-C02-U067, FC02-C02-U109, FC02-C06-U015.

### FC02-C06-U023

- **Kind:** Theorem 41.5.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9198.
- **Statement/data:** Every regular Lindelöf space is paracompact
- **Dependencies:** FC02-C02-U067, FC02-C04-U010, FC02-C04-U015, FC02-C06-U015.

### FC02-C06-U024

- **Kind:** Example 4.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9202.
- **Statement/data:** The product of two paracompact spaces need not be paracompact. The space $\mathbb{R}*{\ell}$ is paracompact, for it is regular and Lindelöf. However, $\mathbb{R}*{\ell} \times \mathbb{R}_{\ell}$ is not paracompact, for it is Hausdorff but not normal
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U025

- **Kind:** Example 5.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9204.
- **Statement/data:** The space $\mathbb{R}^{\omega}$ is paracompact in both the product and uniform topologies. This result follows from the fact that $\mathbb{R}^{\omega}$ is metrizable in these topologies. It is not known whether $\mathbb{R}^{\omega}$ is paracompact in the box topology (See the comment in Exercise 5 of §32)
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U026

- **Kind:** Example 6.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9206.
- **Statement/data:** The product space $\mathbb{R}^J$ is not paracompact if $J$ is uncountable For $\mathbb{R}^J$ is Hausdorff but not normal One of the most useful properties that a paracompact space $X$ possesses has to do with the existence of partitions of unity on $X$ . We have already seen the finite version of this notion in §36; we discuss the general case now. Recall that if $\phi \cdot X \to \mathbb{R}$ , the support of $\phi$ is the closure of the set of those $x$ for which $\phi(x) \neq 0$ .
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U027

- **Kind:** Definition.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9210.
- **Statement/data:** Let ${U_{\alpha}}*{\alpha \in J}$ be an indexed open covering of $X$ . An indexed family of continuous functions $$ \phi* {\alpha}: X \rightarrow [ 0, 1 ] $$ is said to be a partition of unity on $X$ , dominated by ${U_{\alpha}}$ , if: (1) (Support $\phi_{\alpha}) \subset U_{\alpha}$ for each $\alpha$ . (2) The indexed family ${\text{Support } \phi_{\alpha}}$ is locally finite (3) $\sum \phi_{\alpha}(x) = 1$ for each $x$ .
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U028

- **Kind:** Lemma 41.6.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9228.
- **Statement/data:** Let $X$ be a paracompact Hausdorff space; let ${U_{\alpha}}*{\alpha \in J}$ be an indexed family of open sets covering $X$ . Then there exists a locally finite indexed family ${V*{\alpha}}*{\alpha \in J}$ of open sets covering $X$ such that $\tilde{V}*{\alpha} \subset U_{\alpha}$ for each $\alpha$ . The condition that $\bar{V}*{\alpha} \subset U*{\alpha}$ for each $\alpha$ is sometimes expressed by saying that the family ${\bar{V}*{\alpha}}$ is a precise refinement of the family ${U*{\alpha}}$ .
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U029

- **Kind:** Theorem 41.7.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9248.
- **Statement/data:** Let $X$ be a paracompact Hausdorff space; let ${U_{\alpha}}*{\alpha \in J}$ be an indexed open covering of $X$ . Then there exists a partition of unity on $X$ dominated by ${U*{\alpha}}$ .
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U030

- **Kind:** Theorem 41.8.
- **Locator:** §41 “Paracompactness”; printed pp. 252–260; extraction L9274.
- **Statement/data:** Let $X$ be a paracompact Hausdorff space; let $\mathcal{C}$ be a collection of subsets of $X$ ; for each $C \in \mathcal{C}$ , let $\epsilon_C$ be a positive number. If $\mathcal{C}$ is locally finite, there is a continuous function $f: X \to \mathbb{R}$ such that $f(x) > 0$ for all $x$ , and $f(x) \leq \epsilon_C$ for $x \in C$ .
- **Dependencies:** FC02-C02-U067, FC02-C06-U015.

### FC02-C06-U031

- **Kind:** Definition.
- **Locator:** §42 “The Smirnov Metrization Theorem”; printed pp. 261–262; extraction L9336.
- **Statement/data:** A space $X$ is locally metrizable if every point $x$ of $X$ has a neighborhood $U$ that is metrizable in the subspace topology
- **Dependencies:** FC02-C06-U015.

### FC02-C06-U032

- **Kind:** Theorem 42.1.
- **Locator:** §42 “The Smirnov Metrization Theorem”; printed pp. 261–262; extraction L9338.
- **Statement/data:** (Smirnov metrization theorem). A space $X$ is metrizable if and only if it is a paracompact Hausdorff space that is locally metrizable.
- **Dependencies:** FC02-C02-U067, FC02-C06-U015, FC02-C06-U031.

## C07 — Complete Metric Spaces and Function Spaces

Units: 45.

### FC02-C07-U001

- **Kind:** Definition.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9396.
- **Statement/data:** Let $(X, d)$ be a metric space A sequence $(x_{n})$ of points of $X$ is said to be a Cauchy sequence in $(X, d)$ if it has the property that given $\epsilon > 0$ , there is an integer $N$ such that $$ d (x _ {n}, x _ {m}) < \epsilon \quad \text { whenever } n, m \geq N $$ The metric space $(X, d)$ is said to be complete if every Cauchy sequence in $X$ converges. Any convergent sequence in X is necessarily a Cauchy sequence, of course; completeness requires that the converse hold Note that a closed subset A of a complete metric space $(X, d)$ is necessarily complete in the restricted metric. For a Cauchy sequence in A is also a Cauchy sequence in X, hence it converges in X. Because A is a closed subset of X, the limit must lie in A. Note also that if X is complete under the metric d, then X is complete under the standard bounded metric $$
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U002

- **Kind:** Definition.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9402.
- **Statement/data:** A metric space is complete if every Cauchy sequence converges.
- **Dependencies:** FC02-C07-U001.

### FC02-C07-U003

- **Kind:** Lemma 43.1.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9418.
- **Statement/data:** A metric space $X$ is complete if every Cauchy sequence in $X$ has a convergent subsequence.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109, FC02-C07-U001, FC02-C07-U002.

### FC02-C07-U004

- **Kind:** Theorem 43.2.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9440.
- **Statement/data:** Euclidean space $\mathbb{R}^k$ is complete in either of its usual metrics, the euclidean metric $d$ or the square metric $\rho$ .
- **Dependencies:** FC02-C02-U066, FC02-C02-U109, FC02-C07-U002.

### FC02-C07-U005

- **Kind:** Lemma 43.3.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9460.
- **Statement/data:** Let $X$ be the product space $X = \prod X_{\alpha}$ ; let $\mathbf{x}_n$ be a sequence of points of $X$ . Then $\mathbf{x}*n \to \mathbf{x}$ if and only if $\pi*{\alpha}(\mathbf{x}*n) \to \pi*{\alpha}(\mathbf{x})$ for each $\alpha$ .
- **Dependencies:** FC02-C02-U066, FC02-C02-U100, FC02-C02-U109.

### FC02-C07-U006

- **Kind:** Theorem 43.4.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9464.
- **Statement/data:** There is a metric for the product space $\mathbb{R}^{\omega}$ relative to which $\mathbb{R}^{\omega}$ is complete.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109, FC02-C02-U127, FC02-C07-U002.

### FC02-C07-U007

- **Kind:** Example 1.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9480.
- **Statement/data:** An example of a noncomplete metric space is the space $\mathbb{Q}$ of rational numbers in the usual metric $d(x, y) = |x - y|$ . For instance, the sequence $$ 1. 4, 1. 4 1, 1. 4 1 4, 1. 4 1 4 2, 1. 4 1 4 2 1, \dots $$
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U008

- **Kind:** Example 2.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9488.
- **Statement/data:** Another noncomplete space is the open interval $(-1, 1)$ in $\mathbb{R}$ , in the metric $d(x, y) = |x - y|$ . In this space the sequence $(x_n)$ defined by $$ x _ {n} = 1 - 1 / n $$
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U009

- **Kind:** Definition.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9500.
- **Statement/data:** For a metric space (Y,d), let bar-d=min(d,1). On Y^J define bar-rho(f,g)=sup_{alpha in J} bar-d(f(alpha),g(alpha)); this is the uniform metric corresponding to d.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U010

- **Kind:** Theorem 43.5.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9514.
- **Statement/data:** If the space Y is complete in the metric d, then the space $Y^{J}$ is complete in the uniform metric $\bar{\rho}$ corresponding to d.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109, FC02-C07-U002.

### FC02-C07-U011

- **Kind:** Theorem 43.6.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9546.
- **Statement/data:** Let X be a topological space and let $(Y, d)$ be a metric space. The set $\mathcal{C}(X, Y)$ of continuous functions is closed in $Y^{X}$ under the uniform metric. So is the set $\mathcal{B}(X, Y)$ of bounded functions. Therefore, if Y is complete, these spaces are complete in the uniform metric.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109, FC02-C02-U134.

### FC02-C07-U012

- **Kind:** Definition.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9568.
- **Statement/data:** For bounded functions f,g:X→Y, define rho(f,g)=sup_{x in X} d(f(x),g(x)); this metric is the sup metric.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U013

- **Kind:** Theorem 43.7.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9588.
- **Statement/data:** Let $(X, d)$ be a metric space. There is an isometric imbedding of $X$ into a complete metric space.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U014

- **Kind:** Definition.
- **Locator:** §43 “Complete Metric Spaces”; printed pp. 264–270; extraction L9640.
- **Statement/data:** Let X be a metric space. If $h: X \to Y$ is an isometric imbedding of X into a complete metric space Y, then the subspace $\overline{h(X)}$ of Y is a complete metric space. It is called the completion of X.
- **Dependencies:** FC02-C02-U066, FC02-C02-U109.

### FC02-C07-U015

- **Kind:** Theorem 44.1.
- **Locator:** *§44 “A Space-Filling Curve”; printed pp. 271–274; extraction L9736.
- **Statement/data:** Let $I = [0,1]$ . There exists a continuous map $f: I \to I^2$ whose image fills up the entire square $I^2$ . The existence of this path violates one's naive geometric intuition in much the same way as does the existence of the continuous nowhere-differentiable function (which we shall come to later).
- **Dependencies:** FC02-C07-U002, FC02-C07-U011.

### FC02-C07-U016

- **Kind:** Definition.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9833.
- **Statement/data:** A metric space $(X, d)$ is said to be totally bounded if for every $\epsilon > 0$ , there is a finite covering of $X$ by $\epsilon$ -balls.
- **Dependencies:** FC02-C07-U002.

### FC02-C07-U017

- **Kind:** Example 1.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9835.
- **Statement/data:** Total boundedness clearly implies boundedness. For if $B(x_1, 1/2), \ldots, B(x_n, 1/2)$ is a finite covering of $X$ by open balls of radius $1/2$ , then $X$ has diameter at most $1 + \max{d(x_i, x_j)}$ . The converse does not hold, however. For example, in the metric $\tilde{d}(a, b) = \min{1, |a - b|}$ , the real line $\mathbb{R}$ is bounded but not totally bounded.
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U018

- **Kind:** Example 2.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9837.
- **Statement/data:** Under the metric $d(a, b) = |a - b|$ , the real line $\mathbb{R}$ is complete but not totally bounded, while the subspace $(-1, 1)$ is totally bounded but not complete. The subspace $[-1, 1]$ is both complete and totally bounded.
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U019

- **Kind:** Theorem 45.1.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9839.
- **Statement/data:** A metric space $(X, d)$ is compact if and only if it is complete and totally bounded.
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U020

- **Kind:** Definition.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9853.
- **Statement/data:** Let $(Y, d)$ be a metric space. Let $\mathcal{F}$ be a subset of the function space $\mathcal{C}(X, Y)$ . If $x_0 \in X$ , the set $\mathcal{F}$ of functions is said to be equicontinuous at $x_0$ if given $\epsilon > 0$ , there is a neighborhood $U$ of $x_0$ such that for all $x \in U$ and all $f \in \mathcal{F}$ , $$ d (f (x), f (x _ {0})) < \epsilon . $$ If the set $\mathcal{F}$ is equicontinuous at $x_0$ for each $x_0 \in X$ , it is said simply to be equicontinuous. Continuity of the function $f$ at $x_0$ means that given $f$ and given $\epsilon > 0$ , there exists a neighborhood $U$ of $x_0$ such that $d(f(x), f(x_0)) < \epsilon$ for $x \in U$ . Equicontinuity of $\mathcal{F}$ means that a single neighborhood $U$ can be chosen that will work for all the functions $f$ in the collection $\mathcal{F}$ . Note that equicontinuity depends on the specific metric d rather than merely on the topology of Y.
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U021

- **Kind:** Lemma 45.2.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9865.
- **Statement/data:** Let X be a space; let $(Y, d)$ be a metric space. If the subset F of $\mathcal{C}(X, Y)$ is totally bounded under the uniform metric corresponding to d, then F is equicontinuous under d.
- **Dependencies:** FC02-C07-U002, FC02-C07-U016, FC02-C07-U020.

### FC02-C07-U022

- **Kind:** Lemma 45.3.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9895.
- **Statement/data:** Let $X$ be a space; let $(Y, d)$ be a metric space; assume $X$ and $Y$ are compact. If the subset $\mathcal{F}$ of $\mathcal{C}(X, Y)$ is equicontinuous under $d$ , then $\mathcal{F}$ is totally bounded under the uniform and sup metrics corresponding to $d$ .
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U023

- **Kind:** Definition.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9921.
- **Statement/data:** If $(Y, d)$ is a metric space, a subset $\mathcal{F}$ of $\mathcal{C}(X, Y)$ is said to be pointwise bounded under $d$ if for each $x \in X$ , the subset $$ \mathcal {F} _ {a} = {f (a) \mid f \in \mathcal {F} } $$ of Y is bounded under d. *Theorem 45.4 (Ascoli's theorem, classical version). Let $X$ be a compact space; let $(\mathbb{R}^n, d)$ denote euclidean space in either the square metric or the euclidean metric; give $\mathcal{C}(X, \mathbb{R}^n)$ the corresponding uniform topology. A subspace $\mathcal{F}$ of $\mathcal{C}(X, \mathbb{R}^n)$ has compact closure if and only if $\mathcal{F}$ is equicontinuous and pointwise bounded under $d$ .
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U024

- **Kind:** Theorem 45.4.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9929.
- **Statement/data:** (Ascoli's theorem, classical version). Let $X$ be a compact space; let $(\mathbb{R}^n, d)$ denote euclidean space in either the square metric or the euclidean metric; give $\mathcal{C}(X, \mathbb{R}^n)$ the corresponding uniform topology. A subspace $\mathcal{F}$ of $\mathcal{C}(X, \mathbb{R}^n)$ has compact closure if and only if $\mathcal{F}$ is equicontinuous and pointwise bounded under $d$ .
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U025

- **Kind:** Corollary 45.5.
- **Locator:** §45 “Compactness in Metric Spaces”; printed pp. 275–280; extraction L9953.
- **Statement/data:** Let $X$ be compact; let $d$ denote either the square metric or the euclidean metric on $\mathbb{R}^n$ ; give $\mathcal{C}(X, \mathbb{R}^n)$ the corresponding uniform topology. A subspace $\mathcal{F}$ of $\mathcal{C}(X, \mathbb{R}^n)$ is compact if and only if it is closed, bounded under the sup metric $\rho$ , and equicontinuous under $d$ .
- **Dependencies:** FC02-C07-U002, FC02-C07-U016.

### FC02-C07-U026

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10021.
- **Statement/data:** For x in X and U open in Y, let S(x,U)={f in Y^X | f(x) in U}. These sets form a subbasis for the topology of pointwise convergence (point-open topology).
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U027

- **Kind:** Theorem 46.1.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10038.
- **Statement/data:** A sequence $f_{n}$ of functions converges to the function $f$ in the topology of pointwise convergence if and only if for each $x$ in $X$ , the sequence $f_{n}(x)$ of points of $Y$ converges to the point $f(x)$ .
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U028

- **Kind:** Example 1.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10042.
- **Statement/data:** Consider the space $\mathbb{R}^I$ , where $I = [0,1]$ . The sequence $(f_n)$ of continuous functions given by $f_n(x) = x^n$ converges in the topology of pointwise convergence to the function $f$ defined by $$ f (x) = \left{ \begin{array}{l l} 0 & \text { for } 0 \leq x < 1, \ 1 & \text { for } x = 1. \end{array} \right. $$
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U029

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10052.
- **Statement/data:** For f in Y^X, compact C⊆X, and epsilon>0, B_C(f,epsilon) consists of g with sup_{x in C} d(f(x),g(x))<epsilon. These sets form a basis for the topology of compact convergence (uniform convergence on compact sets).
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U030

- **Kind:** Theorem 46.2.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10072.
- **Statement/data:** A sequence $f_{n}: X \to Y$ of functions converges to the function $f$ in the topology of compact convergence if and only if for each compact subspace $C$ of $X$ , the sequence $f_{n}|C$ converges uniformly to $f|C$ .
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U031

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10074.
- **Statement/data:** A space X is said to be compactly generated if it satisfies the following condition: A set A is open in X if $A \cap C$ is open in C for each compact subspace C of X.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U032

- **Kind:** Lemma 46.3.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10078.
- **Statement/data:** If X is locally compact, or if X satisfies the first countability axiom, then X is compactly generated.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C03-U082, FC02-C04-U001, FC02-C07-U031.

### FC02-C07-U033

- **Kind:** Lemma 46.4.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10092.
- **Statement/data:** If X is compactly generated, then a function $f: X \to Y$ is continuous if for each compact subspace C of X, the restricted function $f|C$ is continuous.
- **Dependencies:** FC02-C02-U074, FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C07-U031.

### FC02-C07-U034

- **Kind:** Theorem 46.5.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10102.
- **Statement/data:** Let X be a compactly generated space: let $(Y, d)$ be a metric space. Then $\mathcal{C}(X, Y)$ is closed in $Y^{X}$ in the topology of compact convergence.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C07-U031.

### FC02-C07-U035

- **Kind:** Corollary 46.6.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10106.
- **Statement/data:** Let X be a compactly generated space; let $(Y, d)$ be a metric space. If a sequence of continuous functions $f_{n}: X \to Y$ converges to f in the topology of compact convergence, then f is continuous. Now we have three topologies for the function space $Y^{X}$ when Y is metric. The relation between them is stated in the following theorem, whose proof is straightforward.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C07-U034.

### FC02-C07-U036

- **Kind:** Theorem 46.7.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10110.
- **Statement/data:** Let X be a space; let $(Y, d)$ be a metric space. For the function space $Y^{X}$ , one has the following inclusions of topologies: $$ (\text { uniform }) \supset (\text { compact convergence }) \supset (\text { pointwise convergence }). $$ If X is compact, the first two coincide, and if X is discrete, the second two coincide. Now the definitions of the uniform topology and the compact convergence topology made specific use of the metric d for the space Y. But the topology of pointwise convergence did not; in fact, it is defined for any space Y. It is natural to ask whether either of these other topologies can be extended to the case where Y is an arbitrary topological space. There is no satisfactory answer to this question for the space $Y^{X}$ of all functions mapping X into Y. But for the subspace $\mathcal{C}(X,Y)$ of continuous functions, one can prove something. It turns out that there is in general a topology on $\mathcal{C}(X,Y)$ , called the compact-open topology, that coincides with the compact convergence topology when Y is a metric space. This topology is important in its own right, as we shall see.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U037

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10120.
- **Statement/data:** For compact C⊆X and open U⊆Y, S(C,U)={f in C(X,Y) | f(C)⊆U}. These sets form a subbasis for the compact-open topology.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U038

- **Kind:** Theorem 46.8.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10130.
- **Statement/data:** Let $X$ be a space and let $(Y, d)$ be a metric space. On the set $\mathcal{C}(X, Y)$ , the compact-open topology and the topology of compact convergence coincide.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U039

- **Kind:** Corollary 46.9.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10150.
- **Statement/data:** Let Y be a metric space The compact convergence topology on $\mathcal{C}(X,Y)$ does not depend on the metric of Y. Therefore if X is compact, the uniform topology on $\mathcal{C}(X,Y)$ does not depend on the metric of Y. The fact that the definition of the compact-open topology does not involve a metric is just one of its useful features. Another is the fact that it satisfies the requirement of "joint continuity." Roughly speaking, this means that the expression $f(x)$ is continuous not only in the single "variable" $x$ , but is continuous jointly in both the "variables" $x$ and $f$ . More precisely, one has the following theorem:
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C07-U038.

### FC02-C07-U040

- **Kind:** Theorem 46.10.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10154.
- **Statement/data:** Let $X$ be locally compact Hausdorff; let $\mathcal{C}(X, Y)$ have the compact-open topology. Then the map $$ e: X \times \mathcal {C} (X, Y) \rightarrow Y $$ defined by the equation $$ e (x, f) = f (x) $$ is continuous The map e is called the evaluation map.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042, FC02-C03-U082.

### FC02-C07-U041

- **Kind:** Definition/terminology.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10168.
- **Statement/data:** The map $e:X\times\mathcal C(X,Y)\to Y$, $e(x,f)=f(x)$, is the evaluation map.
- **Dependencies:** FC02-C07-U040.

### FC02-C07-U042

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10174.
- **Statement/data:** Given a function $f: X \times Z \to Y$ , there is a corresponding function $F: Z \to \mathcal{C}(X, Y)$ , defined by the equation $$ (F (z)) (x) = f (x, z). $$ Conversely, given $F \cdot Z \to \mathcal{C}(X, Y)$ , this equation defines a corresponding function $f: X \times Z \to Y$ . We say that $F$ is the map of $Z$ into $\mathcal{C}(X, Y)$ that is induced by $f$ . *Theorem 46.11. Let $X$ and $Y$ be spaces; give $\mathcal{C}(X, Y)$ the compact-open topology. If $f: X \times Z \to Y$ is continuous, then so is the induced function $F: Z \to \mathcal{C}(X, Y)$ . The converse holds if $X$ is locally compact Hausdorff.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U043

- **Kind:** Theorem 46.11.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10182.
- **Statement/data:** Let $X$ and $Y$ be spaces; give $\mathcal{C}(X, Y)$ the compact-open topology. If $f: X \times Z \to Y$ is continuous, then so is the induced function $F: Z \to \mathcal{C}(X, Y)$ . The converse holds if $X$ is locally compact Hausdorff.
- **Dependencies:** FC02-C02-U094, FC02-C02-U109, FC02-C03-U042.

### FC02-C07-U044

- **Kind:** Definition.
- **Locator:** §46 “Pointwise and Compact Convergence”; printed pp. 281–289; extraction L10213.
- **Statement/data:** A continuous $h:X\times I\to Y$ with $h(x,0)=f(x)$ and $h(x,1)=g(x)$ is a homotopy between $f$ and $g$.
- **Dependencies:** —.

### FC02-C07-U045

- **Kind:** Theorem 47.1.
- **Locator:** §47 “Ascoli's Theorem”; printed pp. 290–293; extraction L10303.
- **Statement/data:** (Ascoli's theorem). Let $X$ be a space and let $(Y, d)$ be a metric space. Give $\mathcal{C}(X, Y)$ the topology of compact convergence; let $\mathcal{F}$ be a subset of $\mathcal{C}(X, Y)$ . (a) If $\mathcal{F}$ is equicontinuous under $d$ and the set $$ \mathcal {F} _ {a} = {f (a) \mid f \in \mathcal {F} } $$ has compact closure for each $a \in X$ , then $\mathcal{F}$ is contained in a compact subspace of $\mathcal{C}(X, Y)$ . (b) The converse holds if $X$ is locally compact Hausdorff.
- **Dependencies:** FC02-C05-U003, FC02-C07-U020.

## Extraction/OCR ambiguities and normalizations

- The extraction is sufficiently clean for section and theorem numbering, but a few glyphs are inconsistent: closure bars/tildes, $\bar S_\Omega$ versus a tilde-like rendering, and some arrows/punctuation. The catalogue normalizes these only where the intended notation is unambiguous from the surrounding source.
- The table of contents gives section start pages rather than end pages. Printed section spans above are the inclusive ranges from each section start through the page preceding the next section (or supplementary-exercise/chapter start).
- Starred material is part of the requested main-text scope. The corrected 236-label backstop supplied by the prime matches the ordinary (non-leading-star) explicit labels in unstarred sections. In addition, the extraction contains 26 ordinary explicit labels in the starred sections *§8, *§11, *§22, *§25, *§35, *§36, and *§44, and 9 individually starred formal labels inside ordinary sections; all are included here.
- Some source definitions are introduced in running prose rather than with a `Definition.` label (for example equivalence relations, order relations, continuity, closed sets, and several function-space topologies). These are catalogued as source units in addition to the explicit-label backstop.
- Explicit numbered examples are included mechanically only outside section exercise regions. This deliberately errs toward retaining reusable source examples rather than silently dropping examples later reused as standard counterexamples.

## Chapter 8: Baire Spaces and Dimension Theory

### §48 Baire Spaces (pp. 295–299)

#### FC02-C08-U001

- **kind:** Definition
- **source:** §48; printed pp. 295–299; extraction line 10463
- **statement/data:** Recall that if A is a subset of a space X, the interior of A is defined as the union of all open sets of X that are contained in A. To say that A has empty interior is to say then that A contains no open set of X other than the empty set. Equivalently, A has empty interior if every point of A is a limit point of the complement of A, that is, if the complement of A is dense in X.
- **dependencies:** —

#### FC02-C08-U002

- **kind:** Named example
- **source:** §48; printed pp. 295–299; extraction line 10465
- **statement/data:** In R, Q has empty interior while [0,1] has nonempty interior; in R^2, [0,1]×{0} and Q×R have empty interior.
- **dependencies:** —

#### FC02-C08-U003

- **kind:** Definition
- **source:** §48; printed pp. 295–299; extraction line 10467
- **statement/data:** A space X is said to be a Baire space if the following condition holds: Given any countable collection ${A_{n}}$ of closed sets of X each of which has empty interior in X, their union $\bigcup A_{n}$ also has empty interior in X.
- **dependencies:** —

#### FC02-C08-U004

- **kind:** Named comparison
- **source:** §48; printed pp. 295–299; extraction line 10469
- **statement/data:** Q is not a Baire space; the discrete space Z_+ is Baire.
- **dependencies:** —

#### FC02-C08-U005

- **kind:** Lemma 48.1
- **source:** §48; printed pp. 295–299; extraction line 10483
- **statement/data:** $X$ is a Baire space if and only if given any countable collection ${U_n}$ of open sets in $X$ , each of which is dense in $X$ , their intersection $\bigcap U_n$ is also dense in $X$ .
- **dependencies:** FC02-C08-U003

#### FC02-C08-U006

- **kind:** Theorem 48.2 (Baire category theorem)
- **source:** §48; printed pp. 295–299; extraction line 10493
- **statement/data:** If X is a compact Hausdorff space or a complete metric space, then X is a Baire space.
- **dependencies:** FC02-C08-U003

#### FC02-C08-U007

- **kind:** Lemma 48.3
- **source:** §48; printed pp. 295–299; extraction line 10517
- **statement/data:** Let $C_1 \supset C_2 \supset \cdots$ be a nested sequence of nonempty closed sets in the complete metric space $X$ . If $\text{diam } C_n \to 0$ , then $\bigcap C_n \neq \varnothing$ .
- **dependencies:** —

#### FC02-C08-U008

- **kind:** Lemma 48.4
- **source:** §48; printed pp. 295–299; extraction line 10527
- **statement/data:** Any open subspace $Y$ of a Baire space $X$ is itself a Baire space.
- **dependencies:** FC02-C08-U003

#### FC02-C08-U009

- **kind:** Theorem 48.5
- **source:** §48; printed pp. 295–299; extraction line 10535
- **statement/data:** Let $X$ be a space; let $(Y, d)$ be a metric space. Let $f_n: X \to Y$ be a sequence of continuous functions such that $f_n(x) \to f(x)$ for all $x \in X$ , where $f: X \to Y$ . If $X$ is a Baire space, the set of points at which $f$ is continuous is dense in $X$ .
- **dependencies:** FC02-C08-U003

### *§49 A Nowhere-Differentiable Function (pp. 300–303)

#### FC02-C08-U010

- **kind:** Theorem 49.1
- **source:** *§49; printed pp. 300–303; extraction line 10657
- **statement/data:** Let $h:[0,1]\to \mathbb{R}$ be a continuous function. Given $\epsilon >0$ , there is a function $g:[0,1]\to \mathbb{R}$ with $|h(x) - g(x)| < \epsilon$ for all $x$ , such that $g$ is continuous and nowhere differentiable.
- **dependencies:** —

#### FC02-C08-U011

- **kind:** Named example
- **source:** *§49; printed pp. 300–303; extraction line 10695
- **statement/data:** For α>0, f(x)=4αx(1−x) on [0,1] has Δ_h f(x)≥α for h=1/4; if α>4 then f belongs to U_4.
- **dependencies:** —

### §50 Introduction to Dimension Theory (pp. 304–315)

#### FC02-C08-U012

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10814
- **statement/data:** A collection $\mathcal{A}$ of subsets of the space $X$ is said to have order $m + 1$ if some point of $X$ lies in $m + 1$ elements of $\mathcal{A}$ , and no point of $X$ lies in more than $m + 1$ elements of $\mathcal{A}$ .
- **dependencies:** —

#### FC02-C08-U013

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10816
- **statement/data:** For collections of subsets of X, B refines A if every B∈B is contained in some A∈A.
- **dependencies:** —

#### FC02-C08-U014

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10818
- **statement/data:** A space X is said to be finite dimensional if there is some integer m such that for every open covering A of X, there is an open covering B of X that refines A and has order at most $m + 1$ . The topological dimension of X is defined to be the smallest value of m for which this statement holds; we denote it by dim X.
- **dependencies:** FC02-C08-U012

#### FC02-C08-U015

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10820
- **statement/data:** Every compact subspace of R has topological dimension at most 1.
- **dependencies:** FC02-C08-U014

#### FC02-C08-U016

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10824
- **statement/data:** The interval [0,1] has topological dimension 1.
- **dependencies:** FC02-C08-U014

#### FC02-C08-U017

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10826
- **statement/data:** Every compact subspace of R^2 has topological dimension at most 2.
- **dependencies:** FC02-C08-U014

#### FC02-C08-U018

- **kind:** Theorem 50.1
- **source:** §50; printed pp. 304–315; extraction line 10855
- **statement/data:** Let $X$ be a space having finite dimension. If $Y$ is a closed subspace of $X$ , then $Y$ has finite dimension and $\dim Y \leq \dim X$ .
- **dependencies:** FC02-C08-U014

#### FC02-C08-U019

- **kind:** Theorem 50.2
- **source:** §50; printed pp. 304–315; extraction line 10865
- **statement/data:** Let $X = Y \cup Z$ , where $Y$ and $Z$ are closed subspaces of $X$ having finite topological dimension. Then $$ \dim X = \max {\dim Y, \dim Z }. $$
- **dependencies:** FC02-C08-U014

#### FC02-C08-U020

- **kind:** Corollary 50.3
- **source:** §50; printed pp. 304–315; extraction line 10897
- **statement/data:** Let $X = Y_{1} \cup \cdots \cup Y_{k}$ , where each $Y_{i}$ is a closed subspace of $X$ and is finite dimensional. Then $$ \dim X = \max {\dim Y _ {1}, \dots , \dim Y _ {k} }. $$
- **dependencies:** FC02-C08-U019

#### FC02-C08-U021

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10903
- **statement/data:** Every compact 1-manifold has topological dimension 1.
- **dependencies:** FC02-C08-U020

#### FC02-C08-U022

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10905
- **statement/data:** Every compact 2-manifold has topological dimension at most 2.
- **dependencies:** FC02-C08-U020

#### FC02-C08-U023

- **kind:** Definition / named example
- **source:** §50; printed pp. 304–315; extraction line 10909
- **statement/data:** A finite linear graph is a Hausdorff space that is a union of finitely many arcs, pairwise meeting in at most a common endpoint; the arcs are edges and their endpoints vertices. Such a graph has topological dimension 1.
- **dependencies:** FC02-C08-U020

#### FC02-C08-U024

- **kind:** Named example
- **source:** §50; printed pp. 304–315; extraction line 10916
- **statement/data:** Every finite linear graph embeds in R^3; vertices may be placed in general position and edges mapped to straight segments.
- **dependencies:** —

#### FC02-C08-U025

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10936
- **statement/data:** A set ${\mathbf{x}*0, \ldots, \mathbf{x}*k}$ of points of $\mathbb{R}^N$ is said to be geometrically independent, or affinely independent, if the equations $$ \sum* {i = 0} ^ {k} a _ {i} \mathbf {x} _ {i} = \mathbf {0} \quad \text { and } \quad \sum* {i = 0} ^ {k} a _ {i} = 0 $$ hold only if each $a_{i}=0$ .
- **dependencies:** —

#### FC02-C08-U026

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10968
- **statement/data:** Let ${\mathbf{x}*0, \ldots, \mathbf{x}*k}$ be a set of points of $\mathbb{R}^N$ that is geometrically independent. The plane $P$ determined by these points is defined to be the set of all points $\mathbf{x}$ of $\mathbb{R}^N$ such that $$ \mathbf {x} = \sum* {i = 0} ^ {k} t _ {i} \mathbf {x} _ {i}, \quad \text { where } \sum* {i = 0} ^ {k} t _ {i} = 1. $$
- **dependencies:** —

#### FC02-C08-U027

- **kind:** Definition / convention
- **source:** §50; printed pp. 304–315; extraction line 10984
- **statement/data:** The map T(x)=x−x_0 is a translation of R^N; the plane through x_0 parallel to k independent direction vectors is called a k-plane.
- **dependencies:** —

#### FC02-C08-U028

- **kind:** Definition
- **source:** §50; printed pp. 304–315; extraction line 10994
- **statement/data:** A set $A$ of points of $\mathbb{R}^{N}$ is said to be in general position in $\mathbb{R}^{N}$ if every subset of $A$ containing $N+1$ or fewer points is geometrically independent.
- **dependencies:** —

#### FC02-C08-U029

- **kind:** Lemma 50.4
- **source:** §50; printed pp. 304–315; extraction line 10998
- **statement/data:** Given a finite set ${\mathbf{x}_1, \ldots, \mathbf{x}_n}$ of points of $\mathbb{R}^N$ and given $\delta > 0$ , there exists a set ${\mathbf{y}_1, \ldots, \mathbf{y}_n}$ of points of $\mathbb{R}^N$ in general position in $\mathbb{R}^N$ , such that $|\mathbf{x}_i - \mathbf{y}_i| < \delta$ for all $i$ .
- **dependencies:** —

#### FC02-C08-U030

- **kind:** Theorem 50.5 (The imbedding theorem)
- **source:** §50; printed pp. 304–315; extraction line 11008
- **statement/data:** Every compact metrizable space $X$ of topological dimension $m$ can be imbedded in $\mathbb{R}^{2m + 1}$ .
- **dependencies:** FC02-C08-U014

#### FC02-C08-U031

- **kind:** Theorem 50.6
- **source:** §50; printed pp. 304–315; extraction line 11116
- **statement/data:** Every compact subspace of $\mathbb{R}^N$ has topological dimension at most $N$ .
- **dependencies:** FC02-C08-U014

#### FC02-C08-U032

- **kind:** Corollary 50.7
- **source:** §50; printed pp. 304–315; extraction line 11148
- **statement/data:** Every compact $m$ -manifold has topological dimension at most $m$
- **dependencies:** FC02-C08-U031

#### FC02-C08-U033

- **kind:** Corollary 50.8
- **source:** §50; printed pp. 304–315; extraction line 11150
- **statement/data:** Every compact $m$ -manifold can be imbedded in $\mathbb{R}^{2m+1}$ .
- **dependencies:** FC02-C08-U030

#### FC02-C08-U034

- **kind:** Corollary 50.9
- **source:** §50; printed pp. 304–315; extraction line 11152
- **statement/data:** Let $X$ be a compact metrizable space. Then $X$ can be imbedded in some euclidean space $\mathbb{R}^N$ if and only if $X$ has finite topological dimension.
- **dependencies:** FC02-C08-U030

## Chapter 9: The Fundamental Group

### §51 Homotopy of Paths (pp. 322–329)

#### FC02-C09-U001

- **kind:** Definition
- **source:** §51; printed pp. 322–329; extraction line 11335
- **statement/data:** If $f$ and $f'$ are continuous maps of the space $X$ into the space $Y$ , we say that $f$ is homotopic to $f'$ if there is a continuous map $F: X \times I \to Y$ such that $$ F (x, 0) = f (x) \quad \text { and } \quad F (x, 1) = f ^ {\prime} (x) $$ for each $x$ . (Here $I = [0,1]$ .) The map $F$ is called a homotopy between $f$ and $f'$ . If $f$ is homotopic to $f'$ , we write $f \simeq f'$ . If $f \simeq f'$ and $f'$ is a constant map, we say that $f$ is nulhomotopic.
- **dependencies:** —

#### FC02-C09-U002

- **kind:** Definition
- **source:** §51; printed pp. 322–329; extraction line 11349
- **statement/data:** Two paths $f$ and $f'$ , mapping the interval $I = [0,1]$ into $X$ , are said to be path homotopic if they have the same initial point $x_0$ and the same final point $x_1$ , and if there is a continuous map $F: I \times I \to X$ such that $$ \begin{array}{l l} F (s, 0) = f (s) & \text { and } \quad F (s, 1) = f ^ {\prime} (s), \ F (0, t) = x _ {0} & \text { and } \quad F (1, t) = x _ {1}, \end{array} $$ for each $s \in I$ and each $t \in I$ . We call $F$ a path homotopy between $f$ and $f'$ . See Figure 51.1. If $f$ is path homotopic to $f'$ , we write $f \simeq_p f'$ .
- **dependencies:** FC02-C09-U001

#### FC02-C09-U003

- **kind:** Lemma 51.1
- **source:** §51; printed pp. 322–329; extraction line 11362
- **statement/data:** The relations $\simeq$ and $\simeq_{p}$ are equivalence relations. If $f$ is a path, we shall denote its path-homotopy equivalence class by $[f]$ .
- **dependencies:** FC02-C09-U002

#### FC02-C09-U004

- **kind:** Notation
- **source:** §51; printed pp. 322–329; extraction line 11364
- **statement/data:** The path-homotopy class of a path f is denoted [f].
- **dependencies:** —

#### FC02-C09-U005

- **kind:** Named example
- **source:** §51; printed pp. 322–329; extraction line 11384
- **statement/data:** Any two maps X→R^2 are homotopic by the straight-line homotopy; paths with common endpoints in a convex A⊆R^n are path homotopic in A.
- **dependencies:** —

#### FC02-C09-U006

- **kind:** Construction
- **source:** §51; printed pp. 322–329; extraction line 11390
- **statement/data:** For maps f,g:X→R^n, F(x,t)=(1−t)f(x)+tg(x) is the straight-line homotopy whenever its image remains in the target subspace.
- **dependencies:** —

#### FC02-C09-U007

- **kind:** Named example / comparison
- **source:** §51; printed pp. 322–329; extraction line 11401
- **statement/data:** In R^2−0, the upper semicircle f(s)=(cos πs,sin πs) is path homotopic to g(s)=(cos πs,2 sin πs), but not to the lower semicircle h(s)=(cos πs,−sin πs).
- **dependencies:** —

#### FC02-C09-U008

- **kind:** Definition
- **source:** §51; printed pp. 322–329; extraction line 11421
- **statement/data:** If $f$ is a path in $X$ from $x_0$ to $x_1$ , and if $g$ is a path in $X$ from $x_1$ to $x_2$ , we define the product $f * g$ of $f$ and $g$ to be the path $h$ given by the equations $$ h (s) = \left{ \begin{array}{l l} f (2 s) & \text {for} s \in [ 0, \frac {1}{2} ], \ g (2 s - 1) & \text {for} s \in [ \frac {1}{2}, 1 ]. \end{array} \right. $$ The function h is well-defined and continuous, by the pasting lemma; it is a path in X from $x_{0}$ to $x_{2}$ . We think of h as the path whose first half is the path f and whose second half is the path g. The product operation on paths induces a well-defined operation on path-homotopy classes, defined by the equation $$ [ f ] * [ g ] = [ f * g ] $$
- **dependencies:** FC02-C09-U002

#### FC02-C09-U009

- **kind:** Theorem 51.2
- **source:** §51; printed pp. 322–329; extraction line 11448
- **statement/data:** The operation * has the following properties: (1) (Associativity) If $[f] * ([g] * [h])$ is defined, so is $([f] * [g]) * [h]$ , and they are equal. (2) (Right and left identities) Given $x \in X$ , let $e_x$ denote the constant path $e_x \cdot I \to X$ carrying all of $I$ to the point $x$ . If $f$ is a path in $X$ from $x_0$ to $x_1$ , then $$ [ f ] * [ e _ {x _ {1}} ] = [ f ] \quad a n d \quad [ e _ {x _ {0}} ] * [ f ] = [ f ]. $$ (3) (Inverse) Given the path $f$ in $X$ from $x_0$ to $x_1$ , let $\bar{f}$ be the path defined by $\bar{f}(s) = f(1 - s)$ . It is called the reverse of $f$ . Then $$ [ f ] * [ \bar {f} ] = [ e _ {x _ {0}} ] \quad a n d \quad [ \bar {f} ] * [ f ] = [ e _ {x _ {1}} ]. $$
- **dependencies:** FC02-C09-U008

#### FC02-C09-U010

- **kind:** Convention
- **source:** §51; printed pp. 322–329; extraction line 11502
- **statement/data:** The positive linear map [a,b]→[c,d] is the unique affine map carrying a↦c and b↦d; positive linear maps are closed under inverse and composition.
- **dependencies:** —

#### FC02-C09-U011

- **kind:** Theorem 51.3
- **source:** §51; printed pp. 322–329; extraction line 11517
- **statement/data:** Let f be a path in X, and let $a_{0}, \ldots, a_{n}$ be numbers such that $0 = a_{0} < a_{1} < \cdots < a_{n} = 1$ . Let $f_{i}: I \to X$ be the path that equals the positive linear map of I onto $[a_{i-1}, a_{i}]$ followed by f. Then $$ [ f ] = [ f _ {1} ] * \dots * [ f _ {n} ]. $$
- **dependencies:** FC02-C09-U008

### §52 The Fundamental Group (pp. 330–334)

#### FC02-C09-U012

- **kind:** Convention / review
- **source:** §52; printed pp. 330–334; extraction line 11549
- **statement/data:** For group homomorphisms, kernel/image, monomorphism/epimorphism/isomorphism, left/right cosets, normal subgroups, quotient G/H for normal H, and the induced quotient-isomorphism convention are as stated; for nonnormal H, G/H denotes right cosets.
- **dependencies:** —

#### FC02-C09-U013

- **kind:** Definition
- **source:** §52; printed pp. 330–334; extraction line 11563
- **statement/data:** Let X be a space; let $x_{0}$ be a point of X. A path in X that begins and ends at $x_{0}$ is called a loop based at $x_{0}$ . The set of path homotopy classes of loops based at $x_{0}$ , with the operation *, is called the fundamental group of X relative to the base point $x_{0}$ . It is denoted by $\pi_{1}(X, x_{0})$ .
- **dependencies:** FC02-C09-U009

#### FC02-C09-U014

- **kind:** Named example
- **source:** §52; printed pp. 330–334; extraction line 11569
- **statement/data:** Every convex subset of R^n has trivial fundamental group; in particular R^n and B^n have trivial π1.
- **dependencies:** —

#### FC02-C09-U015

- **kind:** Definition
- **source:** §52; printed pp. 330–334; extraction line 11579
- **statement/data:** Let $\alpha$ be a path in $X$ from $x_0$ to $x_1$ . We define a map $$ \hat {\alpha}: \pi_ {1} (X, x _ {0}) \longrightarrow \pi_ {1} (X, x _ {1}) $$ by the equation $$ \hat {\alpha} ([ f ]) = [ \bar {\alpha} ] * [ f ] * [ \alpha ]. $$ The map $\hat{\alpha}$ , which we call “ $\alpha$ -hat,” is well-defined because the operation $*$ is well-defined. If $f$ is a loop based at $x_0$ , then $\bar{\alpha} * (f * \alpha)$ is a loop based at $x_1$ . Hence $\hat{\alpha}$ maps $\pi_1(X, x_0)$ into $\pi_1(X, x_1)$ , as desired; note that it depends only on the path-homotopy class of $\alpha$ . It is pictured in Figure 52 1.
- **dependencies:** FC02-C09-U013

#### FC02-C09-U016

- **kind:** Theorem 52.1
- **source:** §52; printed pp. 330–334; extraction line 11596
- **statement/data:** The map $\hat{\alpha}$ is a group isomorphism.
- **dependencies:** FC02-C09-U015

#### FC02-C09-U017

- **kind:** Corollary 52.2
- **source:** §52; printed pp. 330–334; extraction line 11612
- **statement/data:** If X is path connected and $x_{0}$ and $x_{1}$ are two points of X, then $\pi_{1}(X, x_{0})$ is isomorphic to $\pi_{1}(X, x_{1})$ .
- **dependencies:** FC02-C09-U016

#### FC02-C09-U018

- **kind:** Definition
- **source:** §52; printed pp. 330–334; extraction line 11620
- **statement/data:** A space X is said to be simply connected if it is a path-connected space and if $\pi_{1}(X, x_{0})$ is the trivial (one-element) group for some $x_{0} \in X$ , and hence for every $x_{0} \in X$ . We often express the fact that $\pi_{1}(X, x_{0})$ is the trivial group by writing $\pi_{1}(X, x_{0}) = 0$ .
- **dependencies:** FC02-C09-U013

#### FC02-C09-U019

- **kind:** Lemma 52.3
- **source:** §52; printed pp. 330–334; extraction line 11622
- **statement/data:** In a simply connected space $X$ , any two paths having the same initial and final points are path homotopic.
- **dependencies:** FC02-C09-U018

#### FC02-C09-U020

- **kind:** Definition
- **source:** §52; printed pp. 330–334; extraction line 11642
- **statement/data:** Let $h \cdot (X, x_0) \to (Y, y_0)$ be a continuous map. Define $$ h _ {*}. \pi_ {1} (X, x _ {0}) \longrightarrow \pi_ {1} (Y, y _ {0}) $$ by the equation $$ h _ {*} ([ f ]) = [ h \circ f ]. $$ The map $h_{*}$ is called the homomorphism induced by h, relative to the base point $x_{0}$ .
- **dependencies:** FC02-C09-U013

#### FC02-C09-U021

- **kind:** Theorem 52.4
- **source:** §52; printed pp. 330–334; extraction line 11672
- **statement/data:** If $h: (X, x_0) \to (Y, y_0)$ and $k: (Y, y_0) \to (Z, z_0)$ are continuous, then $(k \circ h)** = k** \circ h_*$ . If $i: (X, x_0) \to (X, x_0)$ is the identity map, then $i_*$ is the identity homomorphism.
- **dependencies:** FC02-C09-U020

#### FC02-C09-U022

- **kind:** Corollary 52.5
- **source:** §52; printed pp. 330–334; extraction line 11686
- **statement/data:** If $h: (X, x_0) \to (Y, y_0)$ is a homeomorphism of $X$ with $Y$ , then $h_*$ is an isomorphism of $\pi_1(X, x_0)$ with $\pi_1(Y, y_0)$ .
- **dependencies:** FC02-C09-U021

### §53 Covering Spaces (pp. 335–340)

#### FC02-C09-U023

- **kind:** Definition
- **source:** §53; printed pp. 335–340; extraction line 11744
- **statement/data:** Let $p \quad E \to B$ be a continuous surjective map. The open set $U$ of $B$ is said to be evenly covered by $p$ if the inverse image $p^{-1}(U)$ can be written as the union of disjoint open sets $V_{\alpha}$ in $E$ such that for each $\alpha$ , the restriction of $p$ to $V_{\alpha}$ is a homeomorphism of $V_{\alpha}$ onto $U$ . The collection ${V_{\alpha}}$ will be called a partition of $p^{-1}(U)$ into slices
- **dependencies:** —

#### FC02-C09-U024

- **kind:** Definition
- **source:** §53; printed pp. 335–340; extraction line 11751
- **statement/data:** Let $p \to B$ be continuous and surjective. If every point $b$ of $B$ has a neighborhood $U$ that is evenly covered by $p$ , then $p$ is called a covering map, and $E$ is said to be a covering space of $B$
- **dependencies:** FC02-C09-U023

#### FC02-C09-U025

- **kind:** Named example
- **source:** §53; printed pp. 335–340; extraction line 11757
- **statement/data:** For any X, id_X is a covering map; more generally X×{1,…,n}→X is the trivial n-sheet covering.
- **dependencies:** —

#### FC02-C09-U026

- **kind:** Theorem 53.1
- **source:** §53; printed pp. 335–340; extraction line 11761
- **statement/data:** The map $p$ . $\mathbb{R} \to S^1$ given by the equation $$ p (x) = (\cos 2 \pi x, \sin 2 \pi x) $$ is a covering map. One can picture $p$ as a function that wraps the real line $\mathbb{R}$ around the circle $S^1$ , and in the process maps each interval $[n, n + 1]$ onto $S^1$ .
- **dependencies:** —

#### FC02-C09-U027

- **kind:** Named counterexample
- **source:** §53; printed pp. 335–340; extraction line 11786
- **statement/data:** R_+→S^1, x↦(cos 2πx,sin 2πx), is a surjective local homeomorphism but not a covering map.
- **dependencies:** —

#### FC02-C09-U028

- **kind:** Named example
- **source:** §53; printed pp. 335–340; extraction line 11797
- **statement/data:** S^1→S^1, z↦z^2, is a connected covering distinct from the standard R→S^1 covering.
- **dependencies:** —

#### FC02-C09-U029

- **kind:** Theorem 53.2
- **source:** §53; printed pp. 335–340; extraction line 11807
- **statement/data:** Let $p: E \to B$ be a covering map. If $B_0$ is a subspace of $B$ , and if $E_0 = p^{-1}(B_0)$ , then the map $p_0: E_0 \to B_0$ obtained by restricting $p$ is a covering map.
- **dependencies:** FC02-C09-U024

#### FC02-C09-U030

- **kind:** Theorem 53.3
- **source:** §53; printed pp. 335–340; extraction line 11811
- **statement/data:** It $p: E \to B$ and $p': E' \to B'$ are covering maps, then $$ p \times p ^ {\prime}: E \times E ^ {\prime} \rightarrow B \times B ^ {\prime} $$ is a covering map.
- **dependencies:** FC02-C09-U024

#### FC02-C09-U031

- **kind:** Named example
- **source:** §53; printed pp. 335–340; extraction line 11821
- **statement/data:** The torus T=S^1×S^1 is covered by p×p:R^2→S^1×S^1, where p:R→S^1 is the standard covering.
- **dependencies:** —

#### FC02-C09-U032

- **kind:** Named example
- **source:** §53; printed pp. 335–340; extraction line 11836
- **statement/data:** The figure-eight B_0=(S^1×b_0)∪(b_0×S^1) is covered by the infinite grid E_0=(R×Z)∪(Z×R), via restriction of p×p.
- **dependencies:** —

#### FC02-C09-U033

- **kind:** Named example
- **source:** §53; printed pp. 335–340; extraction line 11852
- **statement/data:** p×id:R×R_+→S^1×R_+, followed by S^1×R_+≅R^2−0, gives a covering of the punctured plane.
- **dependencies:** —

### §54 The Fundamental Group of the Circle (pp. 341–347)

#### FC02-C09-U034

- **kind:** Definition
- **source:** §54; printed pp. 341–347; extraction line 11889
- **statement/data:** Let $p \cdot E \to B$ be a map. If $f$ is a continuous mapping of some space $X$ into $B$ , a lifting of $f$ is a map $\bar{f} : X \to E$ such that $p \circ \bar{f} = f$ .
- **dependencies:** FC02-C09-U024

#### FC02-C09-U035

- **kind:** Named example
- **source:** §54; printed pp. 341–347; extraction line 11895
- **statement/data:** For R→S^1, the upper/lower semicircle paths lift from 0 to paths ending at ±1/2, while a loop winding twice lifts from 0 to a path ending at 2.
- **dependencies:** —

#### FC02-C09-U036

- **kind:** Lemma 54.1
- **source:** §54; printed pp. 341–347; extraction line 11900
- **statement/data:** Let $p: E \to B$ be a covering map, let $p(e_0) = b_0$ . Any path $f: [0,1] \to B$ beginning at $b_0$ has a unique lifting to a path $\bar{f}$ in $E$ beginning at $e_0$ .
- **dependencies:** FC02-C09-U034

#### FC02-C09-U037

- **kind:** Lemma 54.2
- **source:** §54; printed pp. 341–347; extraction line 11916
- **statement/data:** Let $p: E \to B$ be a covering map; let $p(e_0) = b_0$ . Let the map $F: I \times I \to B$ be continuous, with $F(0, 0) = b_0$ . There is a unique lifting of $F$ to a continuous map $$ \tilde {F}: I \times I \rightarrow E $$ such that $\bar{F}(0,0) = e_0$ . If $F$ is a path homotopy, then $\tilde{F}$ is a path homotopy.
- **dependencies:** FC02-C09-U034

#### FC02-C09-U038

- **kind:** Theorem 54.3
- **source:** §54; printed pp. 341–347; extraction line 11965
- **statement/data:** Let $p \cdot E \to B$ be a covering map; let $p(e_0) = b_0$ . Let $f$ and $g$ be two paths in $B$ from $b_0$ to $b_1$ , let $\tilde{f}$ and $\bar{g}$ be their respective lifungs to paths in $E$ beginning at $e_0$ . If $f$ and $g$ are path homotopic, then $\tilde{f}$ and $\bar{g}$ end at the same point of $E$ and are path homotopic.
- **dependencies:** FC02-C09-U037

#### FC02-C09-U039

- **kind:** Definition
- **source:** §54; printed pp. 341–347; extraction line 11971
- **statement/data:** Let $p: E \to B$ be a covering map; let $b_0 \in B$ . Choose $e_0$ so that $p(e_0) = b_0$ . Given an element $[f]$ of $\pi_1(B, b_0)$ , let $\tilde{f}$ be the lifting of $f$ to a path in $E$ that begins at $e_0$ . Let $\phi([f])$ denote the end point $\tilde{f}(1)$ of $\tilde{f}$ . Then $\phi$ is a well-defined set map $$ \phi : \pi_ {1} (B, b _ {0}) \rightarrow p ^ {- 1} (b _ {0}). $$ We call $\phi$ the lifting correspondence derived from the covering map $p$ . It depends on course on the choice of the point $e_0$ .
- **dependencies:** FC02-C09-U038

#### FC02-C09-U040

- **kind:** Theorem 54.4
- **source:** §54; printed pp. 341–347; extraction line 11979
- **statement/data:** Let $p: E \to B$ be a covering map; let $p(e_0) = b_0$ . If $E$ is path connected, then the lifting correspondence $$ \phi : \pi_ {1} (B, b _ {0}) \rightarrow p ^ {- 1} (b _ {0}) $$ is surjective. If $E$ is simply connected, it is bijective.
- **dependencies:** FC02-C09-U039

#### FC02-C09-U041

- **kind:** Theorem 54.5
- **source:** §54; printed pp. 341–347; extraction line 11991
- **statement/data:** The fundamental group of $S^1$ is isomorphic to the additive group of integers.
- **dependencies:** FC02-C09-U026

#### FC02-C09-U042

- **kind:** Definition
- **source:** §54; printed pp. 341–347; extraction line 12013
- **statement/data:** Let G be a group; let x be an element of G. We denote the inverse of x by $x^{-1}$ . The symbol $x^{n}$ denotes the n-fold product of x with itself, $x^{-n}$ denotes the n-fold product of $x^{-1}$ with itself, and $x^{0}$ denotes the identity element of G. If the set of all elements of the form $x^{m}$ , for $m \in Z$ , equals G, then G is said to be a cyclic group, and x is said to be a generator of G.
- **dependencies:** —

#### FC02-C09-U043

- **kind:** Convention / comparison
- **source:** §54; printed pp. 341–347; extraction line 12015
- **statement/data:** The cardinality of a group is its order; an infinite cyclic group is isomorphic to Z, and a cyclic group of order k is isomorphic to Z/k.
- **dependencies:** —

#### FC02-C09-U044

- **kind:** Construction / universal property
- **source:** §54; printed pp. 341–347; extraction line 12017
- **statement/data:** If x generates an infinite cyclic group G and y∈H, there is a unique homomorphism h:G→H with h(x)=y, namely h(x^n)=y^n.
- **dependencies:** —

#### FC02-C09-U045

- **kind:** Theorem 54.6
- **source:** §54; printed pp. 341–347; extraction line 12021
- **statement/data:** Let $p: E \to B$ be a covering map; let $p(e_0) = b_0$ . (a) The homomorphism $p_*: \pi_1(E, e_0) \to \pi_1(B, b_0)$ is a monomorphism. (b) Let $H = p_{*}(\pi_{1}(E, e_{0}))$ . The lifting correspondence $\phi$ induces an injective map $$ \Phi : \pi_ {1} (B, b _ {0}) / H \rightarrow p ^ {- 1} (b _ {0}) $$ of the collection of right cosets of $H$ into $p^{-1}(b_0)$ , which is bijective if $E$ is path connected. (c) If $f$ is a loop in $B$ based at $b_0$ , then $[f] \in H$ if and only if $f$ lifts to a loop in $E$ based at $e_0$ .
- **dependencies:** FC02-C09-U039

### §55 Retractions and Fixed Points (pp. 348–352)

#### FC02-C09-U046

- **kind:** Definition
- **source:** §55; printed pp. 348–352; extraction line 12092
- **statement/data:** If $A \subset X$ , a retraction of $X$ onto $A$ is a continuous map $r: X \to A$ such that $r|A$ is the identity map of $A$ . If such a map $r$ exists, we say that $A$ is a retract of $X$ .
- **dependencies:** —

#### FC02-C09-U047

- **kind:** Lemma 55.1
- **source:** §55; printed pp. 348–352; extraction line 12094
- **statement/data:** If $A$ is a retract of $X$ , then the homomorphism of fundamental groups induced by inclusion $j: A \to X$ is injective.
- **dependencies:** FC02-C09-U046

#### FC02-C09-U048

- **kind:** Theorem 55.2 (No-retraction theorem)
- **source:** §55; printed pp. 348–352; extraction line 12098
- **statement/data:** There is no retraction of $B^2$ onto $S^1$ .
- **dependencies:** FC02-C09-U047

#### FC02-C09-U049

- **kind:** Lemma 55.3
- **source:** §55; printed pp. 348–352; extraction line 12102
- **statement/data:** Let $h: S^1 \to X$ be a continuous map. Then the following conditions are equivalent: (1) $h$ is nulhomotopic. (2) $h$ extends to a continuous map $k:B^{2}\to X$ . (3) $h_*$ is the trivial homomorphism of fundamental groups.
- **dependencies:** FC02-C09-U018

#### FC02-C09-U050

- **kind:** Corollary 55.4
- **source:** §55; printed pp. 348–352; extraction line 12136
- **statement/data:** The inclusion map $j: S^1 \to \mathbb{R}^2 - 0$ is not nulhomotopic. The identity map $i: S^1 \to S^1$ is not nulhomotopic.
- **dependencies:** FC02-C09-U049

#### FC02-C09-U051

- **kind:** Theorem 55.5
- **source:** §55; printed pp. 348–352; extraction line 12140
- **statement/data:** Given a nonvanishing vector field on $B^{2}$ , there exists a point of $S^{1}$ where the vector field points directly inward and a point of $S^{1}$ where it points directly outward.
- **dependencies:** —

#### FC02-C09-U052

- **kind:** Theorem 55.6 (Brouwer fixed-point theorem for the disc)
- **source:** §55; printed pp. 348–352; extraction line 12169
- **statement/data:** If $f: B^2 \to B^2$ is continuous, then there exists a point $x \in B^2$ such that $f(x) = x$ .
- **dependencies:** FC02-C09-U048

#### FC02-C09-U053

- **kind:** Corollary 55.7
- **source:** §55; printed pp. 348–352; extraction line 12181
- **statement/data:** Let $A$ be a 3 by 3 matrix of positive real numbers. Then $A$ has a positive real eigenvalue (characteristic value).
- **dependencies:** —

#### FC02-C09-U054

- **kind:** Theorem 55.8
- **source:** §55; printed pp. 348–352; extraction line 12209
- **statement/data:** There is an $\epsilon > 0$ such that for every open covering $\mathcal{A}$ of $T$ by sets of diameter less than $\epsilon$ , some point of $T$ belongs to at least three elements of $\mathcal{A}$ .
- **dependencies:** —

### *§56 The Fundamental Theorem of Algebra (pp. 353–355)

#### FC02-C09-U055

- **kind:** Theorem 56.1 (The fundamental theorem of algebra)
- **source:** *§56; printed pp. 353–355; extraction line 12263
- **statement/data:** A polynomial equation $$ x ^ {n} + a _ {n - 1} x ^ {n - 1} + \dots + a _ {1} x + a _ {0} = 0 $$ of degree $n > 0$ with real or complex coefficients has at least one (real or complex) root.
- **dependencies:** —

### *§57 The Borsuk-Ulam Theorem (pp. 356–358)

#### FC02-C09-U056

- **kind:** Definition
- **source:** *§57; printed pp. 356–358; extraction line 12376
- **statement/data:** If $x$ is a point of $S^n$ , then its antipode is the point $-x$ . A map $h: S^n \to S^m$ is said to be antipode-preserving if $h(-x) = -h(x)$ for all $x \in S^n$ .
- **dependencies:** —

#### FC02-C09-U057

- **kind:** Theorem 57.1
- **source:** *§57; printed pp. 356–358; extraction line 12378
- **statement/data:** If $h: S^1 \to S^1$ is continuous and antipode-preserving, then $h$ is not nulhomotopic.
- **dependencies:** FC02-C09-U056

#### FC02-C09-U058

- **kind:** Theorem 57.2
- **source:** *§57; printed pp. 356–358; extraction line 12402
- **statement/data:** There is no continuous antipode-preserving map $g: S^2 \to S^1$ .
- **dependencies:** FC02-C09-U057

#### FC02-C09-U059

- **kind:** Theorem 57.3 (Borsuk-Ulam theorem for $S^2$ )
- **source:** *§57; printed pp. 356–358; extraction line 12406
- **statement/data:** Given a continuous map $f: S^2 \to \mathbb{R}^2$ , there is a point $x$ of $S^2$ such that $f(x) = f(-x)$ .
- **dependencies:** FC02-C09-U058

#### FC02-C09-U060

- **kind:** Theorem 57.4 (The bisection theorem)
- **source:** *§57; printed pp. 356–358; extraction line 12416
- **statement/data:** Given two bounded polygonal regions in $\mathbb{R}^2$ , there exists a line in $\mathbb{R}^2$ that bisects each of them.
- **dependencies:** FC02-C09-U059

### §58 Deformation Retracts and Homotopy Type (pp. 359–367)

#### FC02-C09-U061

- **kind:** Lemma 58.1
- **source:** §58; printed pp. 359–367; extraction line 12463
- **statement/data:** Let $h, k : (X, x_0) \to (Y, y_0)$ be continuous maps. If $h$ and $k$ are homotopic, and if the image of the base point $x_0$ of $X$ remains fixed at $y_0$ during the homotopy, then the homomorphisms $h_*$ and $k_*$ are equal.
- **dependencies:** —

#### FC02-C09-U062

- **kind:** Theorem 58.2
- **source:** §58; printed pp. 359–367; extraction line 12475
- **statement/data:** The inclusion map $j: S^n \to \mathbb{R}^{n+1} - 0$ induces an isomorphism of fundamental groups.
- **dependencies:** —

#### FC02-C09-U063

- **kind:** Definition
- **source:** §58; printed pp. 359–367; extraction line 12502
- **statement/data:** Let $A$ be a subspace of $X$ . We say that $A$ is a deformation retract of $X$ if the identity map of $X$ is homotopic to a map that carries all of $X$ into $A$ , such that each point of $A$ remains fixed during the homotopy. This means that there is a continuous map $H: X \times I \to X$ such that $H(x, 0) = x$ and $H(x, 1) \in A$ for all $x \in X$ , and $H(a, t) = a$ for all $a \in A$ . The homotopy $H$ is called a deformation retraction of $X$ onto $A$ . The map $r: X \to A$ defined by the equation $r(x) = H(x, 1)$ is a retraction of $X$ onto $A$ , and $H$ is a homotopy between the identity map of $X$ and the map $j \circ r$ , where $j: A \to X$ is inclusion.
- **dependencies:** FC02-C09-U046

#### FC02-C09-U064

- **kind:** Theorem 58.3
- **source:** §58; printed pp. 359–367; extraction line 12506
- **statement/data:** Let $A$ be a deformation retract of $X$ ; let $x_0 \in A$ . Then the inclusion map $$ j: (A, x _ {0}) \rightarrow (X, x _ {0}) $$ induces an isomorphism of fundamental groups.
- **dependencies:** FC02-C09-U063

#### FC02-C09-U065

- **kind:** Named example
- **source:** §58; printed pp. 359–367; extraction line 12514
- **statement/data:** R^3 minus the z-axis deformation retracts onto the punctured xy-plane and has infinite cyclic fundamental group.
- **dependencies:** —

#### FC02-C09-U066

- **kind:** Named example
- **source:** §58; printed pp. 359–367; extraction line 12522
- **statement/data:** The doubly punctured plane has the figure-eight as a deformation retract.
- **dependencies:** —

#### FC02-C09-U067

- **kind:** Named example
- **source:** §58; printed pp. 359–367; extraction line 12526
- **statement/data:** The doubly punctured plane also has a theta space as a deformation retract.
- **dependencies:** —

#### FC02-C09-U068

- **kind:** Definition
- **source:** §58; printed pp. 359–367; extraction line 12538
- **statement/data:** Let $f: X \to Y$ and $g: Y \to X$ be continuous maps. Suppose that the map $g \circ f: X \to X$ is homotopic to the identity map of $X$ , and the map $f \circ g: Y \to Y$ is homotopic to the identity map of $Y$ . Then the maps $f$ and $g$ are called homotopy equivalences, and each is said to be a homotopy inverse of the other.
- **dependencies:** FC02-C09-U001

#### FC02-C09-U069

- **kind:** Lemma 58.4
- **source:** §58; printed pp. 359–367; extraction line 12546
- **statement/data:** Let $h, k: X \to Y$ be continuous maps; let $h(x_0) = y_0$ and $k(x_0) = y_1$ . If $h$ and $k$ are homotopic, there is a path $\alpha$ in $Y$ from $y_0$ to $y_1$ such that $k_* = \hat{\alpha} \circ h_*$ . Indeed, if $H: X \times I \to Y$ is the homotopy between $h$ and $k$ , then $\alpha$ is the path $\alpha(t) = H(x_0, t)$ . $$ \begin{array}{c} \pi_ {1} (X, x _ {0}) \xrightarrow {h _ {*}} \pi_ {1} (Y, y _ {0}) \ \Biggl \downarrow k _ {*} \quad \hat {\alpha} \Biggl \downarrow \ \pi_ {1} (Y, y _ {1}) \end{array} $$
- **dependencies:** FC02-C09-U015

#### FC02-C09-U070

- **kind:** Corollary 58.5
- **source:** §58; printed pp. 359–367; extraction line 12597
- **statement/data:** Let $h, k: X \to Y$ be homotopic continuous maps; let $h(x_0) = y_0$ and $k(x_0) = y_1$ . If $h_*$ is injective, or surjective, or trivial, so is $k_*$ .
- **dependencies:** FC02-C09-U069

#### FC02-C09-U071

- **kind:** Corollary 58.6
- **source:** §58; printed pp. 359–367; extraction line 12599
- **statement/data:** Let $h: X \to Y$ . If $h$ is nullhomotopic, then $h_*$ is the trivial homomorphism.
- **dependencies:** FC02-C09-U070

#### FC02-C09-U072

- **kind:** Theorem 58.7
- **source:** §58; printed pp. 359–367; extraction line 12603
- **statement/data:** Let $f: X \to Y$ be continuous; let $f(x_0) = y_0$ . If $f$ is a homotopy equivalence, then $$ f _ {*}: \pi_ {1} (X, x _ {0}) \longrightarrow \pi_ {1} (Y, y _ {0}) $$ is an isomorphism.
- **dependencies:** FC02-C09-U068

### §59 The Fundamental Group of a Sum of Spaces (pp. 368–369)

#### FC02-C09-U073

- **kind:** Theorem 59.1
- **source:** §59; printed pp. 368–369; extraction line 12755
- **statement/data:** Suppose $X = U \cup V$ , where $U$ and $V$ are open sets of $X$ . Suppose that $U \cap V$ is path connected, and that $x_0 \in U \cap V$ . Let $i$ and $j$ be the inclusion mappings of $U$ and $V$ , respectively, into $X$ . Then the images of the induced homomorphisms $$ i _ {*}: \pi_ {1} (U, x _ {0}) \rightarrow \pi_ {1} (X, x _ {0}) \quad a n d \quad j _ {*}: \pi_ {1} (V, x _ {0}) \rightarrow \pi_ {1} (X, x _ {0}) $$ generate $\pi_1(X, x_0)$ .
- **dependencies:** —

#### FC02-C09-U074

- **kind:** Corollary 59.2
- **source:** §59; printed pp. 368–369; extraction line 12794
- **statement/data:** Suppose $X = U \cup V$ , where $U$ and $V$ are open sets of $X$ ; suppose $U \cap V$ is nonempty and path connected. If $U$ and $V$ are simply connected, then $X$ is simply connected.
- **dependencies:** FC02-C09-U073

#### FC02-C09-U075

- **kind:** Theorem 59.3
- **source:** §59; printed pp. 368–369; extraction line 12796
- **statement/data:** If $n \geq 2$ , the $n$ -sphere $S^n$ is simply connected.
- **dependencies:** FC02-C09-U074

#### FC02-C09-U076

- **kind:** Construction
- **source:** §59; printed pp. 368–369; extraction line 12808
- **statement/data:** Stereographic projection gives a homeomorphism S^n−{p}≅R^n.
- **dependencies:** —

### §60 The Fundamental Group of Some Surfaces (pp. 370–375)

#### FC02-C09-U077

- **kind:** Theorem 60.1
- **source:** §60; printed pp. 370–375; extraction line 12856
- **statement/data:** $\pi_1(X\times Y,x_0\times y_0)$ is isomorphic with $\pi_1(X,x_0)\times \pi_1(Y,y_0)$ .
- **dependencies:** FC02-C09-U020

#### FC02-C09-U078

- **kind:** Corollary 60.2
- **source:** §60; printed pp. 370–375; extraction line 12900
- **statement/data:** The fundamental group of the torus $T = S^1 \times S^1$ is isomorphic to the group $\mathbb{Z} \times \mathbb{Z}$ .
- **dependencies:** FC02-C09-U077

#### FC02-C09-U079

- **kind:** Definition
- **source:** §60; printed pp. 370–375; extraction line 12904
- **statement/data:** The projective plane $P^{2}$ is the quotient space obtained from $S^{2}$ by identifying each point x of $S^{2}$ with its antipodal point -x.
- **dependencies:** —

#### FC02-C09-U080

- **kind:** Theorem 60.3
- **source:** §60; printed pp. 370–375; extraction line 12908
- **statement/data:** The projective plane $P^2$ is a compact surface, and the quotient map $p: S^2 \to P^2$ is a covering map.
- **dependencies:** FC02-C09-U079

#### FC02-C09-U081

- **kind:** Corollary 60.4
- **source:** §60; printed pp. 370–375; extraction line 12944
- **statement/data:** $\pi_1(P^2, y)$ is a group of order 2.
- **dependencies:** FC02-C09-U080

#### FC02-C09-U082

- **kind:** Named comparison
- **source:** §60; printed pp. 370–375; extraction line 12950
- **statement/data:** Projective n-space P^n is S^n with antipodal points identified; S^n→P^n is a covering, and for n≥2 its fundamental group has two elements.
- **dependencies:** —

#### FC02-C09-U083

- **kind:** Lemma 60.5
- **source:** §60; printed pp. 370–375; extraction line 12954
- **statement/data:** The fundamental group of the figure eight is not abelian.
- **dependencies:** —

#### FC02-C09-U084

- **kind:** Theorem 60.6
- **source:** §60; printed pp. 370–375; extraction line 12974
- **statement/data:** The fundamental group of the double torus is not abelian.
- **dependencies:** —

#### FC02-C09-U085

- **kind:** Corollary 60.7
- **source:** §60; printed pp. 370–375; extraction line 12983
- **statement/data:** The 2-sphere, torus, projective plane, and double torus are topologically distinct.
- **dependencies:** FC02-C09-U081

## Chapter 10: Separation Theorems in the Plane

### §61 The Jordan Separation Theorem (pp. 376–380)

#### FC02-C10-U001

- **kind:** Lemma 61.1
- **source:** §61; printed pp. 376–380; extraction line 13014
- **statement/data:** Let $C$ be a compact subspace of $S^2$ ; let $b$ be a point of $S^2 - C$ ; and let $h$ be a homeomorphism of $S^2 - b$ with $\mathbb{R}^2$ . Suppose $U$ is a component of $S^2 - C$ . If $U$ does not contain $b$ , then $h(U)$ is a bounded component of $\mathbb{R}^2 - h(C)$ . If $U$ contains $b$ , then $h(U - b)$ is the unbounded component of $\mathbb{R}^2 - h(C)$ . In particular, if $S^2 - C$ has $n$ components, then $\mathbb{R}^2 - h(C)$ has $n$ components.
- **dependencies:** —

#### FC02-C10-U002

- **kind:** Lemma 61.2 (Nulhomotopy lemma)
- **source:** §61; printed pp. 376–380; extraction line 13024
- **statement/data:** Let $a$ and $b$ be points of $S^2$ . Let $A$ be a compact space, and let $$ f: A \longrightarrow S ^ {2} - a - b $$ be a continuous map. If $a$ and $b$ lie in the same component of $S^{2} - f(A)$ , then $f$ is nulhomotopic.
- **dependencies:** —

#### FC02-C10-U003

- **kind:** Definition
- **source:** §61; printed pp. 376–380; extraction line 13057
- **statement/data:** For connected X and A⊆X, A separates X if X−A is disconnected; if X−A has n components, A separates X into n components.
- **dependencies:** —

#### FC02-C10-U004

- **kind:** Definition
- **source:** §61; printed pp. 376–380; extraction line 13062
- **statement/data:** An arc is a space homeomorphic to [0,1]; its two distinguished endpoints are those whose deletion leaves it connected, and all other points are interior points.
- **dependencies:** —

#### FC02-C10-U005

- **kind:** Theorem 61.3 (The Jordan separation theorem)
- **source:** §61; printed pp. 376–380; extraction line 13066
- **statement/data:** Let $C$ be a simple closed curve in $S^2$ . Then $C$ separates $S^2$ .
- **dependencies:** FC02-C10-U003

#### FC02-C10-U006

- **kind:** Theorem 61.4 (A general separation theorem)
- **source:** §61; printed pp. 376–380; extraction line 13101
- **statement/data:** Let $A_1$ and $A_2$ be closed connected subsets of $S^2$ whose intersection consists of precisely two points $a$ and $b$ . Then the set $C = A_1 \cup A_2$ separates $S^2$ .
- **dependencies:** FC02-C10-U003

### *§62 Invariance of Domain (pp. 381–384)

#### FC02-C10-U007

- **kind:** Lemma 62.1 (Homotopy extension lemma)
- **source:** *§62; printed pp. 381–384; extraction line 13120
- **statement/data:** Let X be a space such that $X \times I$ is normal. Let A be a closed subspace of X, and let $f : A \to Y$ be a continuous map, where Y is an open subspace of $R^{n}$ . If f is nullhomotopic, then f may be extended to a continuous map $g : X \to Y$ that is also nullhomotopic.
- **dependencies:** FC02-C09-U001

#### FC02-C10-U008

- **kind:** Lemma 62.2 (Borsuk lemma)
- **source:** *§62; printed pp. 381–384; extraction line 13137
- **statement/data:** Let $a$ and $b$ be points of $S^2$ . Let $A$ be a compact space, and let $f: A \to S^2 - a - b$ be a continuous injective map. If $f$ is nullhomotopic, then $a$ and $b$ lie in the same component of $S^2 - f(A)$ .
- **dependencies:** FC02-C10-U007

#### FC02-C10-U009

- **kind:** Theorem 62.3 (Invariance of domain)
- **source:** *§62; printed pp. 381–384; extraction line 13154
- **statement/data:** If $U$ is an open subset of $\mathbb{R}^2$ and $f: U \to \mathbb{R}^2$ is continuous and injective, then $f(U)$ is open in $\mathbb{R}^2$ and the inverse function $f^{-1}: f(U) \to U$ is continuous.
- **dependencies:** —

### §63 The Jordan Curve Theorem (pp. 385–393)

#### FC02-C10-U010

- **kind:** Theorem 63.1
- **source:** §63; printed pp. 385–393; extraction line 13199
- **statement/data:** Let X be the union of two open sets U and V, such that $U \cap V$ can be written as the union of two disjoint open sets A and B. Assume that there is a path $\alpha$ in U from a point a of A to a point b of B, and that there is a path $\beta$ in V from b to a. Let f be the loop $f = \alpha * \beta$ . (a) The path-homotopy class $[f]$ generates an infinite cyclic subgroup of $\pi_1(X, a)$ . $^{*}(b)$ If $\pi_{1}(X, a)$ is itself infinite cyclic, it is generated by [f]. $^{\dagger}$ (c) Assume there is a path $\gamma$ in $U$ from $a$ to the point $a'$ of $A$ , and that there is a path $\delta$ in $V$ from $a'$ to $a$ . Let $g$ be the loop $g = \gamma * \delta$ . Then the subgroups of $\pi_1(X, a)$ generated by $[f]$ and $[g]$ intersect in the identity element alone.
- **dependencies:** —

#### FC02-C10-U011

- **kind:** Theorem 63.2 (A nonseparation theorem)
- **source:** §63; printed pp. 385–393; extraction line 13309
- **statement/data:** Let $D$ be an arc in $S^2$ . Then $D$ does not separate $S^2$ .
- **dependencies:** FC02-C10-U003

#### FC02-C10-U012

- **kind:** Theorem 63.3 (A general nonseparation theorem)
- **source:** §63; printed pp. 385–393; extraction line 13345
- **statement/data:** Let $D_{1}$ and $D_{2}$ be closed subsets of $S^{2}$ such that $S^{2} - D_{1} \cap D_{2}$ is simply connected. If neither $D_{1}$ nor $D_{2}$ separates $S^{2}$ , then $D_{1} \cup D_{2}$ does not separate $S^{2}$ .
- **dependencies:** FC02-C10-U003

#### FC02-C10-U013

- **kind:** Theorem 63.4 (The Jordan curve theorem)
- **source:** §63; printed pp. 385–393; extraction line 13349
- **statement/data:** Let C be a simple closed curve in $S^{2}$ . Then C separates $S^{2}$ into precisely two components $W_{1}$ and $W_{2}$ . Each of the sets $W_{1}$ and $W_{2}$ has C as its boundary; that is, $C = \overline{W}*{i} - W*{i}$ for i = 1, 2.
- **dependencies:** FC02-C10-U005

#### FC02-C10-U014

- **kind:** Theorem 63.5
- **source:** §63; printed pp. 385–393; extraction line 13376
- **statement/data:** Let $C_1$ and $C_2$ be closed connected subsets of $S^2$ whose intersection consists of two points. If neither $C_1$ nor $C_2$ separates $S^2$ , then $C_1 \cup C_2$ separates $S^2$ into precisely two components.
- **dependencies:** FC02-C10-U013

#### FC02-C10-U015

- **kind:** Named theorem / comparison
- **source:** §63; printed pp. 385–393; extraction line 13385
- **statement/data:** Schoenflies theorem: if C⊂S^2 is a simple closed curve and U,V are the components of S^2−C, then cl(U) and cl(V) are each homeomorphic to B^2.
- **dependencies:** —

### §64 Imbedding Graphs in the Plane (pp. 394–397)

#### FC02-C10-U016

- **kind:** Definition / convention
- **source:** §64; printed pp. 394–397; extraction line 13423
- **statement/data:** A finite linear graph is a Hausdorff union of finitely many arcs, pairwise intersecting in at most a common endpoint; arcs are edges and endpoints are vertices.
- **dependencies:** —

#### FC02-C10-U017

- **kind:** Named example
- **source:** §64; printed pp. 394–397; extraction line 13429
- **statement/data:** The complete graph on n vertices, denoted G_n in the source, has an edge joining every pair of distinct vertices.
- **dependencies:** —

#### FC02-C10-U018

- **kind:** Named example
- **source:** §64; printed pp. 394–397; extraction line 13434
- **statement/data:** The utilities graph is the bipartite graph joining each of three utilities to each of three houses (K_{3,3}).
- **dependencies:** —

#### FC02-C10-U019

- **kind:** Definition
- **source:** §64; printed pp. 394–397; extraction line 13436
- **statement/data:** A theta space $X$ is a Hausdorff space that is written as the union of three arcs $A, B$ , and $C$ , each pair of which intersect precisely in their end points. (The space $X$ is of course homeomorphic to the Greek letter theta.)
- **dependencies:** —

#### FC02-C10-U020

- **kind:** Lemma 64.1
- **source:** §64; printed pp. 394–397; extraction line 13443
- **statement/data:** Let X be a theta space that is a subspace of $S^{2}$ ; let A, B, and C be the arcs whose union is X. Then X separates $S^{2}$ into three components, whose boundaries are $A \cup B$ , $B \cup C$ , and $A \cup C$ , respectively. The component having $A \cup B$ as its boundary equals one of the components of $S^{2} - A \cup B$ .
- **dependencies:** FC02-C10-U019

#### FC02-C10-U021

- **kind:** Theorem 64.2
- **source:** §64; printed pp. 394–397; extraction line 13454
- **statement/data:** Let X be the utilities graph. Then X cannot be imbedded in the plane.
- **dependencies:** FC02-C10-U018

#### FC02-C10-U022

- **kind:** Lemma 64.3
- **source:** §64; printed pp. 394–397; extraction line 13470
- **statement/data:** Let X be a subspace of $S^{2}$ that is a complete graph on four vertices $a_{1}$ , $a_{2}$ , $a_{3}$ , and $a_{4}$ . Then X separates $S^{2}$ into four components. The boundaries of these components are the sets $X_{1}$ , $X_{2}$ , $X_{3}$ , and $X_{4}$ , where $X_{i}$ is the union of those edges of X that do not have $a_{i}$ as a vertex.
- **dependencies:** —

#### FC02-C10-U023

- **kind:** Theorem 64.4
- **source:** §64; printed pp. 394–397; extraction line 13488
- **statement/data:** The complete graph on five vertices cannot be imbedded in the plane.
- **dependencies:** FC02-C10-U017

#### FC02-C10-U024

- **kind:** Named theorem / comparison
- **source:** §64; printed pp. 394–397; extraction line 13500
- **statement/data:** Kuratowski theorem (stated without proof): a finite graph is nonplanar exactly when it contains a subgraph of the utilities-graph or K_5 type in the source formulation.
- **dependencies:** FC02-C10-U021

### §65 The Winding Number of a Simple Closed Curve (pp. 398–402)

#### FC02-C10-U025

- **kind:** Lemma 65.1
- **source:** §65; printed pp. 398–402; extraction line 13530
- **statement/data:** Let $G$ be a subspace of $S^2$ that is a complete graph on four vertices $a_1, \ldots, a_4$ . Let $C$ be the subgraph $a_1a_2a_3a_4a_1$ , which is a simple closed curve. Let $p$ and $q$ be interior points of the edges $a_1a_3$ and $a_2a_4$ , respectively. Then: (a) The points $p$ and $q$ lie in different components of $S^2 - C$ . (b) The inclusion $j: C \to S^2 - p - q$ induces an isomorphism of fundamental groups.
- **dependencies:** —

#### FC02-C10-U026

- **kind:** Theorem 65.2
- **source:** §65; printed pp. 398–402; extraction line 13563
- **statement/data:** Let $C$ be a simple closed curve in $S^2$ ; let $p$ and $q$ lie in different components of $S^2 - C$ . Then the inclusion mapping $j: C \to S^2 - p - q$ induces an isomorphism of fundamental groups.
- **dependencies:** FC02-C10-U013

### §66 The Cauchy Integral Formula (pp. 403–406)

#### FC02-C10-U027

- **kind:** Definition
- **source:** §66; printed pp. 403–406; extraction line 13608
- **statement/data:** Let $f$ be a loop in $\mathbb{R}^2$ , and let $a$ be a point not in the image of $f$ . Set $$ g (s) = [ f (s) - a ] / | f (s) - a |; $$ then $g$ is a loop in $S^1$ . Let $p: \mathbb{R} \to S^1$ be the standard covering map, and let $\tilde{g}$ be a lifting of $g$ to $S^1$ . Because $g$ is a loop, the difference $\tilde{g}(1) - \tilde{g}(0)$ is an integer. This integer is called the winding number of $f$ with respect to $a$ , and is denoted $n(f, a)$ . Note that $n(f, a)$ is independent of the choice of the lifting of $g$ . For if $\bar{g}$ is one lifting of $g$ , then uniqueness of liftings implies that any other lifting of $g$ has the form $\bar{g}(s) + m$ for some integer $m$ .
- **dependencies:** FC02-C09-U039

#### FC02-C10-U028

- **kind:** Definition
- **source:** §66; printed pp. 403–406; extraction line 13618
- **statement/data:** Let $F: I \times I \to X$ be a continuous map such that $F(0, t) = F(1, t)$ for all $t$ . Then for each $t$ , the map $f_t(s) = F(s, t)$ is a loop in $X$ . The map $F$ is called a free homotopy between the loops $f_0$ and $f_1$ . It is a homotopy of loops in which the base point of the loop is allowed to move during the homotopy.
- **dependencies:** —

#### FC02-C10-U029

- **kind:** Lemma 66.1
- **source:** §66; printed pp. 403–406; extraction line 13620
- **statement/data:** Let $f$ be a loop in $\mathbb{R}^2 - a$ . (a) If $\bar{f}$ is the reverse of $f$ , then $n(\bar{f}, a) = -n(f, a)$ . (b) If $f$ is freely homotopic to $f'$ , through loops lying in $\mathbb{R}^2 - a$ , then $n(f, a) = n(f', a)$ . (c) If $a$ and $b$ lie in the same component of $\mathbb{R}^2 - f(I)$ , then $n(f, a) = n(f, b)$ .
- **dependencies:** FC02-C10-U027

#### FC02-C10-U030

- **kind:** Definition
- **source:** §66; printed pp. 403–406; extraction line 13640
- **statement/data:** Let $f$ be a loop in $X$ . We call $f$ a simple loop provided $f(s) = f(s')$ only if $s = s'$ or if one of the points $s, s'$ is 0 and the other is 1. If $f$ is a simple loop, its image set is a simple closed curve in $X$ .
- **dependencies:** FC02-C10-U027

#### FC02-C10-U031

- **kind:** Theorem 66.2
- **source:** §66; printed pp. 403–406; extraction line 13642
- **statement/data:** Let $f$ be a simple loop in $\mathbb{R}^2$ . If a lies in the unbounded component of $\mathbb{R}^2 - f(I)$ , then $n(f, a) = 0$ ; while if a lies in the bounded component, $n(f, a) = \pm 1$ .
- **dependencies:** FC02-C10-U029

#### FC02-C10-U032

- **kind:** Definition
- **source:** §66; printed pp. 403–406; extraction line 13652
- **statement/data:** Let $f$ be a simple loop in $\mathbb{R}^2$ . We say $f$ is a counterclockwise loop if $n(f, a) = +1$ for some $a$ (and hence for every $a$ ) in the bounded component of $\mathbb{R}^2 - f(l)$ . We say it is a clockwise loop if $n(f, a) = -1$ . The standard loop $p(s) = (\cos 2\pi s, \sin 2\pi s)$ is thus a counterclockwise loop.
- **dependencies:** FC02-C10-U031

#### FC02-C10-U033

- **kind:** Lemma 66.3
- **source:** §66; printed pp. 403–406; extraction line 13658
- **statement/data:** Let $f$ be a piecewise-differentiable loop in the complex plane; let $a$ be a point not in the image of $f$ . Then $$ n (f, a) = \frac {1}{2 \pi i} \int_ {f} \frac {d z}{z - a}. $$ This equation is often used as the definition of the winding number of $f$ .
- **dependencies:** FC02-C10-U027

#### FC02-C10-U034

- **kind:** Theorem 66.4 (Cauchy integral formula-classical version)
- **source:** §66; printed pp. 403–406; extraction line 13670
- **statement/data:** Let $C$ be a simple closed piecewise-differentiable curve in the complex plane. Let $B$ be the bounded component of $\mathbb{R}^2 - C$ . If $F(z)$ is analytic in an open set $\Omega$ that contains $B$ and $C$ , then for each point $a$ of $B$ , $$ F (a) = \pm \frac {1}{2 \pi i} \int_ {C} \frac {F (z)}{z - a} d z. $$ The sign is + if C is oriented counterclockwise, and - otherwise.
- **dependencies:** FC02-C10-U033

## Chapter 11: The Seifert-van Kampen Theorem

### §67 Direct Sums of Abelian Groups (pp. 407–411)

#### FC02-C11-U001

- **kind:** Definition
- **source:** §67; printed pp. 407–411; extraction line 13712
- **statement/data:** A family of subgroups {G_α} of an abelian group G generates G if every element is a finite sum of elements from the G_α.
- **dependencies:** —

#### FC02-C11-U002

- **kind:** Definition
- **source:** §67; printed pp. 407–411; extraction line 13724
- **statement/data:** G is the direct sum of subgroups G_α if every x∈G has a unique finite-support expression x=Σx_α with x_α∈G_α; notation G=⊕G_α.
- **dependencies:** FC02-C11-U001

#### FC02-C11-U003

- **kind:** Named example
- **source:** §67; printed pp. 407–411; extraction line 13732
- **statement/data:** R^∞, the finite-support subgroup of R^ω, is the direct sum of its coordinate subgroups G_n≅R.
- **dependencies:** —

#### FC02-C11-U004

- **kind:** Lemma 67.1
- **source:** §67; printed pp. 407–411; extraction line 13736
- **statement/data:** Let $G$ be an abelian group; let ${G_{\alpha}}$ be a family of subgroups of $G$ . If $G$ is the direct sum of the groups $G_{\alpha}$ , then $G$ satisfies the following condition: Given any abelian group H and any family of homomorphisms (*) $h_{\alpha}: G_{\alpha} \to H$ , there exists a homomorphism $h: G \to H$ whose restriction to $G_{\alpha}$ equals $h_{\alpha}$ , for each $\alpha$ . Furthermore, h is unique. Conversely, if the groups $G_{\alpha}$ generate G and the extension condition (*) holds, then G is the direct sum of the groups $G_{\alpha}$ .
- **dependencies:** FC02-C11-U002

#### FC02-C11-U005

- **kind:** Corollary 67.2
- **source:** §67; printed pp. 407–411; extraction line 13754
- **statement/data:** Let $G = G_{1} \oplus G_{2}$ . Suppose $G_{1}$ is the direct sum of subgroups $H_{\alpha}$ for $\alpha \in J$ , and $G_{2}$ is the direct sum of subgroups $H_{\beta}$ for $\beta \in K$ , where the index sets $J$ and $K$ are disjoint. Then $G$ is the direct sum of the subgroups $H_{\gamma}$ , for $\gamma \in J \cup K$ .
- **dependencies:** FC02-C11-U004

#### FC02-C11-U006

- **kind:** Corollary 67.3
- **source:** §67; printed pp. 407–411; extraction line 13764
- **statement/data:** If $G = G_{1} \oplus G_{2}$ , then $G / G_{2}$ is isomorphic to $G_{1}$ .
- **dependencies:** FC02-C11-U002

#### FC02-C11-U007

- **kind:** Definition
- **source:** §67; printed pp. 407–411; extraction line 13770
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be an indexed family of abelian groups. Suppose that $G$ is an abelian group, and that $i*{\alpha}: G_{\alpha} \to G$ is a family of monomorphisms, such that $G$ is the direct sum of the groups $i_{\alpha}(G_{\alpha})$ . Then we say that $G$ is the external direct sum of the groups $G_{\alpha}$ , relative to the monomorphisms $i_{\alpha}$ .
- **dependencies:** FC02-C11-U002

#### FC02-C11-U008

- **kind:** Theorem 67.4
- **source:** §67; printed pp. 407–411; extraction line 13774
- **statement/data:** Given a family of abelian groups ${G_{\alpha}}*{\alpha \in J}$ , there exists an abelian group $G$ and a family of monomorphisms $i*{\alpha}: G_{\alpha} \to G$ such that $G$ is the direct sum of the groups $i_{\alpha}(G_{\alpha})$ .
- **dependencies:** FC02-C11-U007

#### FC02-C11-U009

- **kind:** Lemma 67.5
- **source:** §67; printed pp. 407–411; extraction line 13786
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be an indexed family of abelian groups; let $G$ be an abelian group; let $i*{\alpha}: G_{\alpha} \to G$ be a family of homomorphisms. If each $i_{\alpha}$ is a monomorphism and $G$ is the direct sum of the groups $i_{\alpha}(G_{\alpha})$ , then $G$ satisfies the following extension condition: Given any abelian group $H$ and any family of homomorphisms $h_{\alpha}$ : (*) $G_{\alpha} \to H$ , there exists a homomorphism $h: G \to H$ such that $h \circ i_{\alpha} = h_{\alpha}$ for each $\alpha$ . Furthermore, h is unique. Conversely, suppose the groups $i_{\alpha}(G_{\alpha})$ generate G and the extension condition (*) holds. Then each $i_{\alpha}$ is a monomorphism, and G is the direct sum of the groups $i_{\alpha}(G_{\alpha})$ .
- **dependencies:** FC02-C11-U007

#### FC02-C11-U010

- **kind:** Theorem 67.6 (Uniqueness of direct sums)
- **source:** §67; printed pp. 407–411; extraction line 13798
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be a family of abelian groups. Suppose $G$ and $G'$ are abelian groups and $i*{\alpha}: G_{\alpha} \to G$ and $i'*{\alpha}: G*{\alpha} \to G'$ are families of monomorphisms, such that $G$ is the direct sum of the groups $i_{\alpha}(G_{\alpha})$ and $G'$ is the direct sum of the groups $i'*{\alpha}(G*{\alpha})$ . Then there is a unique isomorphism $\phi: G \to G'$ such that $\phi \circ i_{\alpha} = i'_{\alpha}$ for each $\alpha$ .
- **dependencies:** FC02-C11-U009

#### FC02-C11-U011

- **kind:** Convention
- **source:** §67; printed pp. 407–411; extraction line 13802
- **statement/data:** For an external direct sum, the source often identifies each G_α with its image and writes G=⊕G_α.
- **dependencies:** —

#### FC02-C11-U012

- **kind:** Definition
- **source:** §67; printed pp. 407–411; extraction line 13806
- **statement/data:** Let G be an abelian group and let ${a_{\alpha}}$ be an indexed family of elements of G; let $G_{\alpha}$ be the subgroup of G generated by $a_{\alpha}$ . If the groups $G_{\alpha}$ generate G, we also say that the elements $a_{\alpha}$ generate G. If each group $G_{\alpha}$ is infinite cyclic, and if G is the direct sum of the groups $G_{\alpha}$ , then G is said to be a free abelian group having the elements ${a_{\alpha}}$ as a basis.
- **dependencies:** FC02-C11-U002

#### FC02-C11-U013

- **kind:** Lemma 67.7
- **source:** §67; printed pp. 407–411; extraction line 13810
- **statement/data:** Let $G$ be an abelian group; let ${a_{\alpha}}*{\alpha \in J}$ be a family of elements of $G$ that generates $G$ . Then $G$ is a free abelian group with basis ${a*{\alpha}}$ if and only if for any abelian group $H$ and any family ${y_{\alpha}}$ of elements of $H$ , there is a homomorphism $h$ of $G$ into $H$ such that $h(a_{\alpha}) = y_{\alpha}$ for each $\alpha$ . In such case, $h$ is unique.
- **dependencies:** FC02-C11-U012

#### FC02-C11-U014

- **kind:** Theorem 67.8
- **source:** §67; printed pp. 407–411; extraction line 13816
- **statement/data:** If $G$ is a free abelian group with basis ${a_1, \ldots, a_n}$ , then $n$ is uniquely determined by $G$ .
- **dependencies:** FC02-C11-U012

#### FC02-C11-U015

- **kind:** Definition
- **source:** §67; printed pp. 407–411; extraction line 13820
- **statement/data:** The rank of a free abelian group with a finite basis is the number of basis elements.
- **dependencies:** FC02-C11-U014

### §68 Free Products of Groups (pp. 412–420)

#### FC02-C11-U016

- **kind:** Definition
- **source:** §68; printed pp. 412–420; extraction line 13864
- **statement/data:** A family of subgroups generates a group G if every element is a finite product of elements from them; such a finite sequence is a word representing that element.
- **dependencies:** —

#### FC02-C11-U017

- **kind:** Definition / convention
- **source:** §68; printed pp. 412–420; extraction line 13876
- **statement/data:** A reduced word has no identity letters and no adjacent letters from the same factor; the empty word is the reduced word representing the identity.
- **dependencies:** FC02-C11-U016

#### FC02-C11-U018

- **kind:** Definition
- **source:** §68; printed pp. 412–420; extraction line 13880
- **statement/data:** Let $G$ be a group, let ${G_{\alpha}}*{\alpha \in J}$ be a family of subgroups of $G$ that generates $G$ . Suppose that $G*{\alpha} \cap G_{\beta}$ consists of the identity element alone whenever $\alpha \neq \beta$ . We say that $G$ is the free product of the groups $G_{\alpha}$ if for each $x \in G$ , there is only one reduced word in the groups $G_{\alpha}$ that represents $x$ . In this case, we write $$ G = \prod_ {\alpha \in J} ^ {*} G _ {\alpha}, $$
- **dependencies:** FC02-C11-U017

#### FC02-C11-U019

- **kind:** Named counterexample
- **source:** §68; printed pp. 412–420; extraction line 13916
- **statement/data:** S_3 is generated by two order-2 subgroups but is not their free product: the reduced words π_1π_2π_1 and π_2π_1π_2 represent the same element.
- **dependencies:** —

#### FC02-C11-U020

- **kind:** Lemma 68.1
- **source:** §68; printed pp. 412–420; extraction line 13920
- **statement/data:** Let $G$ be a group; let ${G_{\alpha}}$ be a family of subgroups of $G$ . If $G$ is the free product of the groups $G_{\alpha}$ , then $G$ satisfies the following condition: Given any group $H$ and any family of homomorphisms $h_{\alpha}: G_{\alpha} \to$ (*) H, there exists a homomorphism $h: G \to H$ whose restriction to $G_{\alpha}$ equals $h_{\alpha}$ , for each $\alpha$ . Furthermore, $h$ is unique. The converse of this lemma holds, but the proof is not as easy as it was for direct sums. We postpone it until later.
- **dependencies:** FC02-C11-U018

#### FC02-C11-U021

- **kind:** Definition
- **source:** §68; printed pp. 412–420; extraction line 13970
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be an indexed family of groups. Suppose that $G$ is a group, and that $i*{\alpha}: G_{\alpha} \to G$ is a family of monomorphisms, such that $G$ is the free product of the groups $i_{\alpha}(G_{\alpha})$ . Then we say that $G$ is the external free product of the groups $G_{\alpha}$ , relative to the monomorphisms $i_{\alpha}$ .
- **dependencies:** FC02-C11-U018

#### FC02-C11-U022

- **kind:** Theorem 68.2
- **source:** §68; printed pp. 412–420; extraction line 13974
- **statement/data:** Given a family ${G_{\alpha}}*{\alpha \in J}$ of groups, there exists a group $G$ and a family of monomorphisms $i*{\alpha}: G_{\alpha} \to G$ such that $G$ is the free product of the groups $i_{\alpha}(G_{\alpha})$ .
- **dependencies:** FC02-C11-U021

#### FC02-C11-U023

- **kind:** Lemma 68.3
- **source:** §68; printed pp. 412–420; extraction line 14088
- **statement/data:** Let ${G_{\alpha}}$ be a family of groups; let $G$ be a group; let $i_{\alpha}: G_{\alpha} \to G$ be a family of homomorphisms. If each $i_{\alpha}$ is a monomorphism and $G$ is the free product of the groups $i_{\alpha}(G_{\alpha})$ , then $G$ satisfies the following condition: Given a group $H$ and a family of homomorphisms $h_{\alpha}: G_{\alpha} \to H$ , (*) there exists a homomorphism $h: G \to H$ such that $h \circ i_{\alpha} = h_{\alpha}$ for each $\alpha$ . Furthermore, $h$ is unique.
- **dependencies:** FC02-C11-U021

#### FC02-C11-U024

- **kind:** Theorem 68.4 (Uniqueness of free products)
- **source:** §68; printed pp. 412–420; extraction line 14096
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be a family of groups. Suppose $G$ and $G'$ are groups and $i*{\alpha}: G_{\alpha} \to G$ and $i_{\alpha}': G_{\alpha} \to G'$ are families of monomorphisms, such that the families ${i_{\alpha}(G_{\alpha})}$ and ${i_{\alpha}'(G_{\alpha})}$ generate $G$ and $G'$ , respectively. If both $G$ and $G'$ have the extension property stated in the preceding lemma, then there is a unique isomorphism $\phi: G \to G'$ such that $\phi \circ i_{\alpha} = i_{\alpha}'$ for all $\alpha$ .
- **dependencies:** FC02-C11-U023

#### FC02-C11-U025

- **kind:** Lemma 68.5
- **source:** §68; printed pp. 412–420; extraction line 14100
- **statement/data:** Let ${G_{\alpha}}*{\alpha \in J}$ be a family of groups; let $G$ be a group; let $i*{\alpha}: G_{\alpha} \to G$ be a family of homomorphisms. If the extension condition of Lemma 68.3 holds, then each $i_{\alpha}$ is a monomorphism and $G$ is the free product of the groups $i_{\alpha}(G_{\alpha})$ .
- **dependencies:** FC02-C11-U023

#### FC02-C11-U026

- **kind:** Corollary 68.6
- **source:** §68; printed pp. 412–420; extraction line 14108
- **statement/data:** Let $G = G_{1} * G_{2}$ , where $G_{1}$ is the free product of the subgroups ${H_{\alpha}}*{\alpha \in J}$ and $G*{2}$ is the free product of the subgroups ${H_{\beta}}*{\beta \in K}$ . If the index sets $J$ and $K$ are disjoint, then $G$ is the free product of the subgroups ${H*{\gamma}}_{\gamma \in J \cup K}$ .
- **dependencies:** FC02-C11-U025

#### FC02-C11-U027

- **kind:** Definition / convention
- **source:** §68; printed pp. 412–420; extraction line 14118
- **statement/data:** Elements x,y∈G are conjugate if y=cxc^{-1}; a subgroup is normal if it contains every conjugate of each of its elements.
- **dependencies:** —

#### FC02-C11-U028

- **kind:** Construction
- **source:** §68; printed pp. 412–420; extraction line 14120
- **statement/data:** The least normal subgroup containing S⊆G is the intersection of all normal subgroups containing S.
- **dependencies:** FC02-C11-U027

#### FC02-C11-U029

- **kind:** Theorem 68.7
- **source:** §68; printed pp. 412–420; extraction line 14122
- **statement/data:** Let $G = G_{1} * G_{2}$ . Let $N_{i}$ be a normal subgroup of $G_{i}$ , for $i = 1, 2$ . If $N$ is the least normal subgroup of $G$ that contains $N_{1}$ and $N_{2}$ , then $$ G / N \cong (G _ {1} / N _ {1}) * (G _ {2} / N _ {2}). $$
- **dependencies:** FC02-C11-U028

#### FC02-C11-U030

- **kind:** Corollary 68.8
- **source:** §68; printed pp. 412–420; extraction line 14156
- **statement/data:** If $N$ is the least normal subgroup of $G_1 * G_2$ that contains $G_1$ , then $(G_1 * G_2) / N \cong G_2$ .
- **dependencies:** FC02-C11-U029

#### FC02-C11-U031

- **kind:** Lemma 68.9
- **source:** §68; printed pp. 412–420; extraction line 14160
- **statement/data:** Let $S$ be a subset of the group $G$ . If $N$ is the least normal subgroup of $G$ containing $S$ , then $N$ is generated by all conjugates of elements of $S$ .
- **dependencies:** FC02-C11-U028

### §69 Free Groups (pp. 421–425)

#### FC02-C11-U032

- **kind:** Definition
- **source:** §69; printed pp. 421–425; extraction line 14190
- **statement/data:** A family {a_α} generates G if every element is a product of powers of the a_α; G is finitely generated when such a family is finite.
- **dependencies:** —

#### FC02-C11-U033

- **kind:** Definition
- **source:** §69; printed pp. 421–425; extraction line 14192
- **statement/data:** Let ${a_{\alpha}}$ be a family of elements of a group G. Suppose each $a_{\alpha}$ generates an infinite cyclic subgroup $G_{\alpha}$ of G. If G is the free product of the groups ${G_{\alpha}}$ , then G is said to be a free group, and the family ${a_{\alpha}}$ is called a system of free generators for G.
- **dependencies:** FC02-C11-U018

#### FC02-C11-U034

- **kind:** Lemma 69.1
- **source:** §69; printed pp. 421–425; extraction line 14204
- **statement/data:** Let $G$ be a group; let ${a_{\alpha}}*{\alpha \in J}$ be a family of elements of $G$ . If $G$ is a free group with system of free generators ${a*{\alpha}}$ , then $G$ satisfies the following condition: Given any group $H$ and any family ${y_{\alpha}}$ of elements of $H$ , there is a homomorphism $h: G \to H$ such that $h(a_{\alpha}) = y_{\alpha}$ for each $\alpha$ . Furthermore, h is unique. Conversely, if the extension condition (*) holds, then G is a free group with system of free generators ${a_{\alpha}}$ .
- **dependencies:** FC02-C11-U033

#### FC02-C11-U035

- **kind:** Theorem 69.2
- **source:** §69; printed pp. 421–425; extraction line 14216
- **statement/data:** Let $G = G_{1} * G_{2}$ , where $G_{1}$ and $G_{2}$ are free groups with ${a_{\alpha}}*{\alpha \in J}$ and ${a*{\alpha}}*{\alpha \in K}$ as respective systems of free generators. If $J$ and $K$ are disjoint, then $G$ is a free group with ${a*{\alpha}}_{\alpha \in J \cup K}$ as a system of free generators.
- **dependencies:** FC02-C11-U033

#### FC02-C11-U036

- **kind:** Definition
- **source:** §69; printed pp. 421–425; extraction line 14218
- **statement/data:** Let ${a_{\alpha}}*{\alpha \in J}$ be an arbitrary indexed family. Let $G*{\alpha}$ denote the set of all symbols of the form $a_{\alpha}^{n}$ for $n\in \mathbb{Z}$ . We make $G_{\alpha}$ into a group by defining $$ a _ {\alpha} ^ {n} \cdot a _ {\alpha} ^ {m} = a _ {\alpha} ^ {n + m}. $$ Then $a_{\alpha}^{0}$ is the identity element of $G_{\alpha}$ , and $a_{\alpha}^{-n}$ is the inverse of $a_{\alpha}^{n}$ . We denote $a_{\alpha}^{1}$ simply by $a_{\alpha}$ . The external free product of the groups ${G_{\alpha}}$ is called the free group on the elements $a_{\alpha}$ . If G is the free group on the elements $a_{\alpha}$ , we normally abuse notation and identify the elements of the group $G_{\alpha}$ with their images under the monomorphism $i_{\alpha}:G_{\alpha}\to G$ involved in the construction of the external free product. Then each $a_{\alpha}$ is treated as an element of G, and the family ${a_{\alpha}}$ forms a system of free generators for G.
- **dependencies:** FC02-C11-U022

#### FC02-C11-U037

- **kind:** Definition
- **source:** §69; printed pp. 421–425; extraction line 14230
- **statement/data:** Let $G$ be a group. If $x, y \in G$ , we denote by $[x, y]$ the element $$ [ x, y ] = x y x ^ {- 1} y ^ {- 1} $$ of $G$ ; it is called the commutator of $x$ and $y$ . The subgroup of $G$ generated by the set of all commutators in $G$ is called the commutator subgroup of $G$ and denoted $[G, G]$ .
- **dependencies:** FC02-C11-U027

#### FC02-C11-U038

- **kind:** Lemma 69.3
- **source:** §69; printed pp. 421–425; extraction line 14240
- **statement/data:** Given $G$ , the subgroup $[G, G]$ is a normal subgroup of $G$ and the quotient group $G / [G, G]$ is abelian. If $h: G \to H$ is any homomorphism from $G$ to an abelian group $H$ , then the kernel of $h$ contains $[G, G]$ , so $h$ induces a homomorphism $k: G / [G, G] \to H$ .
- **dependencies:** FC02-C11-U037

#### FC02-C11-U039

- **kind:** Theorem 69.4
- **source:** §69; printed pp. 421–425; extraction line 14280
- **statement/data:** If G is a free group with free generators $a_{\alpha}$ , then G/[G, G] is a free abelian group with basis $[a_{\alpha}]$ , where $[a_{\alpha}]$ denotes the coset of $a_{\alpha}$ in G/[G, G].
- **dependencies:** FC02-C11-U038

#### FC02-C11-U040

- **kind:** Corollary 69.5
- **source:** §69; printed pp. 421–425; extraction line 14284
- **statement/data:** If G is a free group with n free generators, then any system of free generators for G has n elements.
- **dependencies:** FC02-C11-U039

#### FC02-C11-U041

- **kind:** Named comparison
- **source:** §69; printed pp. 421–425; extraction line 14298
- **statement/data:** For finitely generated abelian G, G=H⊕T with H finite-rank free abelian and T the torsion subgroup; rank(H) is the Betti number, and T decomposes into finite prime-power cyclic groups.
- **dependencies:** —

#### FC02-C11-U042

- **kind:** Construction / terminology
- **source:** §69; printed pp. 421–425; extraction line 14302
- **statement/data:** Given generators a_α of G and the free group F on them, the canonical surjection F→G has kernel N, the relations subgroup; elements of N are relations, and a generating set for N as a normal subgroup is a complete set of relations.
- **dependencies:** FC02-C11-U036

#### FC02-C11-U043

- **kind:** Definition
- **source:** §69; printed pp. 421–425; extraction line 14306
- **statement/data:** If $G$ is a group, a presentation of $G$ consists of a family ${a_{\alpha}}$ of generators for $G$ , along with a complete set ${r_{\beta}}$ of relations for $G$ , where each $r_{\beta}$ is an element of the free group on the set ${a_{\alpha}}$ . If the family ${a_{\alpha}}$ is finite, then $G$ is finitely generated, of course. If both the families ${a_{\alpha}}$ and ${r_{\beta}}$ are finite, then $G$ is said to be finitely presented, and these families form what is called a finite presentation for $G$ .
- **dependencies:** FC02-C11-U042

### §70 The Seifert-van Kampen Theorem (pp. 426–433)

#### FC02-C11-U044

- **kind:** Theorem 70.1 (Seifert-van Kampen theorem)
- **source:** §70; printed pp. 426–433; extraction line 14346
- **statement/data:** Let $X = U \cup V$ , where $U$ and $V$ are open in $X$ ; assume $U, V$ , and $U \cap V$ are path connected; let $x_0 \in U \cap V$ . Let $H$ be a group, and let $$ \phi_ {1}: \pi_ {1} (U, x _ {0}) \longrightarrow H \quad a n d \quad \phi_ {2}: \pi_ {1} (V, x _ {0}) \longrightarrow H $$ be homomorphisms. Let $i_{1}, i_{2}, j_{1}, j_{2}$ be the homomorphisms indicated in the following diagram, each induced by inclusion. If $\phi_1 \circ i_1 = \phi_2 \circ i_2$ , then there is a unique homomorphism $\Phi: \pi_1(X, x_0) \to H$ such that $\Phi \circ j_1 = \phi_1$ and $\Phi \circ j_2 = \phi_2$ . This theorem says that if $\phi_1$ and $\phi_2$ are arbitrary homomorphisms that are "compatible on $U \cap V$ ," then they induce a homomorphism of $\pi_1(X, x_0)$ into $H$ .
- **dependencies:** FC02-C09-U073

#### FC02-C11-U045

- **kind:** Notation
- **source:** §70; printed pp. 426–433; extraction line 14362
- **statement/data:** For a path f in X, [f] denotes its path-homotopy class in X; if f lies in U, [f]_U denotes its class computed in U, similarly for V and U∩V.
- **dependencies:** —

#### FC02-C11-U046

- **kind:** Theorem 70.2 (Seifert-van Kampen theorem, classical version)
- **source:** §70; printed pp. 426–433; extraction line 14541
- **statement/data:** Assume the hypotheses of the preceding theorem. Let $$ j: \pi_ {1} (U, x _ {0}) * \pi_ {1} (V, x _ {0}) \longrightarrow \pi_ {1} (X, x _ {0}) $$ be the homomorphism of the free product that extends the homomorphisms $j_{1}$ and $j_{2}$ induced by inclusion. Then j is surjective, and its kernel is the least normal subgroup N of the free product that contains all elements represented by words of the form $$ (i _ {1} (g) ^ {- 1}, i _ {2} (g)), $$ for $g \in \pi_1(U \cap V, x_0)$ . Said differently, the kernel of j is generated by all elements of the free product of the form $i_{1}(g)^{-1}i_{2}(g)$ , and their conjugates.
- **dependencies:** FC02-C11-U044

#### FC02-C11-U047

- **kind:** Corollary 70.3
- **source:** §70; printed pp. 426–433; extraction line 14595
- **statement/data:** Assume the hypotheses of the Seifert-van Kampen theorem. If $U \cap V$ is simply connected, then there is an isomorphism $$ k: \pi_ {1} (U, x _ {0}) * \pi_ {1} (V, x _ {0}) \longrightarrow \pi_ {1} (X, x _ {0}). $$
- **dependencies:** FC02-C11-U046

#### FC02-C11-U048

- **kind:** Corollary 70.4
- **source:** §70; printed pp. 426–433; extraction line 14601
- **statement/data:** Assume the hypotheses of the Seifert-van Kampen theorem. If V is simply connected, there is an isomorphism $$ k: \pi_ {1} (U, x _ {0}) / N \longrightarrow \pi_ {1} (X, x _ {0}), $$ where N is the least normal subgroup of $\pi_{1}(U, x_{0})$ containing the image of the homomorphism $$ i _ {1}: \pi_ {1} (U \cap V, x _ {0}) \rightarrow \pi_ {1} (U, x _ {0}). $$
- **dependencies:** FC02-C11-U046

#### FC02-C11-U049

- **kind:** Named example
- **source:** §70; printed pp. 426–433; extraction line 14613
- **statement/data:** A theta space has fundamental group the free product of two infinite cyclic groups, hence is free on two generators.
- **dependencies:** —

### §71 The Fundamental Group of a Wedge of Circles (pp. 434–437)

#### FC02-C11-U050

- **kind:** Definition
- **source:** §71; printed pp. 434–437; extraction line 14656
- **statement/data:** Let $X$ be a Hausdorff space that is the union of the subspaces $S_1, \ldots, S_n$ , each of which is homeomorphic to the unit circle $S^1$ . Assume that there is a point $p$ of $X$ such that $S_i \cap S_j = {p}$ whenever $i \neq j$ . Then $X$ is called the wedge of the circles $S_1, \ldots, S_n$ .
- **dependencies:** —

#### FC02-C11-U051

- **kind:** Theorem 71.1
- **source:** §71; printed pp. 434–437; extraction line 14660
- **statement/data:** Let X be the wedge of the circles $S_{1}, \ldots, S_{n}$ ; let p be the common point of these circles. Then $\pi_{1}(X, p)$ is a free group. If $f_{i}$ is a loop in $S_{i}$ that represents a generator of $\pi_{1}(S_{i}, p)$ , then the loops $f_{1}, \ldots, f_{n}$ represent a system of free generators for $\pi_{1}(X, p)$ .
- **dependencies:** FC02-C11-U050

#### FC02-C11-U052

- **kind:** Definition
- **source:** §71; printed pp. 434–437; extraction line 14681
- **statement/data:** Let X be a space that is the union of the subspaces $X_{\alpha}$ , for $\alpha \in J$ . The topology of X is said to be coherent with the subspaces $X_{\alpha}$ provided a subset C of X is closed in X if $C \cap X_{\alpha}$ is closed in $X_{\alpha}$ for each $\alpha$ . An equivalent condition is that a set be open in X if its intersection with each $X_{\alpha}$ is open in $X_{\alpha}$ .
- **dependencies:** —

#### FC02-C11-U053

- **kind:** Definition
- **source:** §71; printed pp. 434–437; extraction line 14685
- **statement/data:** Let X be a space that is the union of the subspaces $S_{\alpha}$ , for $\alpha \in J$ , each of which is homeomorphic to the unit circle. Assume there is a point p of X such that $S_{\alpha} \cap S_{\beta} = {p}$ whenever $\alpha \neq \beta$ . If the topology of X is coherent with the subspaces $S_{\alpha}$ , then X is called the wedge of the circles $S_{\alpha}$ .
- **dependencies:** FC02-C11-U052

#### FC02-C11-U054

- **kind:** Lemma 71.2
- **source:** §71; printed pp. 434–437; extraction line 14689
- **statement/data:** Let X be the wedge of the circles $S_{\alpha}$ , for $\alpha \in J$ . Then X is normal. Furthermore, any compact subspace of X is contained in the union of finitely many circles $S_{\alpha}$ .
- **dependencies:** FC02-C11-U053

#### FC02-C11-U055

- **kind:** Theorem 71.3
- **source:** §71; printed pp. 434–437; extraction line 14695
- **statement/data:** Let $X$ be the wedge of the circles $S_{\alpha}$ , for $\alpha \in J$ ; let $p$ be the common point of these circles. Then $\pi_1(X, p)$ is a free group. If $f_{\alpha}$ is a loop in $S_{\alpha}$ representing a generator of $\pi_1(S_{\alpha}, p)$ , then the loops ${f_{\alpha}}$ represent a system of free generators for $\pi_1(X, p)$ .
- **dependencies:** FC02-C11-U054

#### FC02-C11-U056

- **kind:** Named example / comparison
- **source:** §71; printed pp. 434–437; extraction line 14713
- **statement/data:** The infinite earring ⋃C_n⊂R^2 (circles tangent at the origin with radii 1/n) is not the wedge of the circles C_n.
- **dependencies:** FC02-C11-U053

#### FC02-C11-U057

- **kind:** Lemma 71.4
- **source:** §71; printed pp. 434–437; extraction line 14726
- **statement/data:** Given an index set $J$ , there exists a space $X$ that is a wedge of circles $S_{\alpha}$ for $\alpha \in J$ .
- **dependencies:** FC02-C11-U053

### §72 Adjoining a 2-Cell (pp. 438–441)

#### FC02-C11-U058

- **kind:** Theorem 72.1
- **source:** §72; printed pp. 438–441; extraction line 14772
- **statement/data:** Let $X$ be a Hausdorff space; let $A$ be a closed path-connected subspace of $X$ . Suppose that there is a continuous map $h: B^2 \to X$ that maps $\operatorname{Int} B^2$ bijectively onto $X - A$ and maps $S^1 = \operatorname{Bd} B^2$ into $A$ . Let $p \in S^1$ and let $a = h(p)$ ; let $k: (S^1, p) \to (A, a)$ be the map obtained by restricting $h$ . Then the homomorphism $$ i _ {*}: \pi_ {1} (A, a) \longrightarrow \pi_ {1} (X, a) $$ induced by inclusion is surjective, and its kernel is the least normal subgroup of $\pi_{1}(A,a)$ containing the image of $k_{*}:\pi_{1}(S^{1},p)\to\pi_{1}(A,a)$ . We sometimes say that the fundamental group of $X$ is obtained from the fundamental group of $A$ by "killing off" the class $k_{*}[f]$ , where $[f]$ generates $\pi_1(S^1, p)$ .
- **dependencies:** FC02-C11-U046

#### FC02-C11-U059

- **kind:** Definition / construction
- **source:** §72; printed pp. 438–441; extraction line 14839
- **statement/data:** A 2-cell is a space homeomorphic to B^2; the setup of Theorem 72.1 is described as adjoining a 2-cell to A along its boundary map.
- **dependencies:** FC02-C11-U058

### §73 The Fundamental Groups of the Torus and the Dunce Cap (pp. 442–445)

#### FC02-C11-U060

- **kind:** Theorem 73.1
- **source:** §73; printed pp. 442–445; extraction line 14853
- **statement/data:** The fundamental group of the torus has a presentation consisting of two generators $\alpha, \beta$ and a single relation $\alpha\beta\alpha^{-1}\beta^{-1}$ .
- **dependencies:** FC02-C11-U058

#### FC02-C11-U061

- **kind:** Corollary 73.2
- **source:** §73; printed pp. 442–445; extraction line 14870
- **statement/data:** The fundamental group of the torus is a free abelian group of rank 2.
- **dependencies:** FC02-C11-U060

#### FC02-C11-U062

- **kind:** Definition
- **source:** §73; printed pp. 442–445; extraction line 14876
- **statement/data:** Let $n$ be a positive integer with $n > 1$ . Let $r: S^1 \to S^1$ be rotation through the angle $2\pi / n$ , mapping the point $(\cos \theta, \sin \theta)$ to the point $(\cos (\theta + 2\pi / n), \sin (\theta + 2\pi / n))$ . Form a quotient space $X$ from the unit ball $B^2$ by identifying each point $x$ of $S^1$ with the points $r(x), r^2(x), \ldots, r^{n-1}(x)$ . We shall show that $X$ is a compact Hausdorff space; we call it the $n$ -fold dunce cap.
- **dependencies:** —

#### FC02-C11-U063

- **kind:** Lemma 73.3
- **source:** §73; printed pp. 442–445; extraction line 14882
- **statement/data:** Let $\pi : E \to X$ be a closed quotient map. If $E$ is normal, then so is $X$ .
- **dependencies:** —

#### FC02-C11-U064

- **kind:** Theorem 73.4
- **source:** §73; printed pp. 442–445; extraction line 14900
- **statement/data:** The fundamental group of the $n$ -fold dunce cap is a cyclic group of order $n$ .
- **dependencies:** FC02-C11-U062

## Chapter 12: Classification of Surfaces

### §74 Fundamental Groups of Surfaces (pp. 446–453)

#### FC02-C12-U001

- **kind:** Definition / notation
- **source:** §74; printed pp. 446–453; extraction line 14969
- **statement/data:** A polygonal region P is bounded by successive line segments joining cyclically ordered vertices; these are its edges, their union is Bd P, and P−Bd P is Int P.
- **dependencies:** —

#### FC02-C12-U002

- **kind:** Definition / convention
- **source:** §74; printed pp. 446–453; extraction line 14971
- **statement/data:** An orientation of a line segment orders its endpoints; the positive linear map between oriented segments is the affine homeomorphism carrying initial to initial and final to final endpoint.
- **dependencies:** —

#### FC02-C12-U003

- **kind:** Definition
- **source:** §74; printed pp. 446–453; extraction line 14977
- **statement/data:** Let P be a polygonal region in the plane. A labelling of the edges of P is a map from the set of edges of P to a set S called the set of labels. Given an orientation of each edge of P, and given a labelling of the edges of P, we define an equivalence relation on the points of P as follows: Each point of Int P is equivalent only to itself. Given any two edges of P that have the same label, let h be the positive linear map of one onto the other, and define each point x of the first edge to be equivalent to the point $h(x)$ of the second edge. This relation generates an equivalence relation on P. The quotient space X obtained from this equivalence relation is said to have been obtained by pasting the edges of P together according to the given orientations and labelling.
- **dependencies:** FC02-C12-U002

#### FC02-C12-U004

- **kind:** Named example
- **source:** §74; printed pp. 446–453; extraction line 14981
- **statement/data:** The triangular edge-pasting of Example 1 gives a quotient homeomorphic to B^2.
- **dependencies:** —

#### FC02-C12-U005

- **kind:** Named example
- **source:** §74; printed pp. 446–453; extraction line 14986
- **statement/data:** The square edge-pasting of Example 2 gives a quotient homeomorphic to S^2.
- **dependencies:** —

#### FC02-C12-U006

- **kind:** Definition
- **source:** §74; printed pp. 446–453; extraction line 14993
- **statement/data:** Let P be a polygonal region with successive vertices $p_{0}, \ldots, p_{n}$ , where $p_{0} = p_{n}$ . Given orientations and a labelling of the edges of P, let $a_{1}, \ldots, a_{m}$ be the distinct labels that are assigned to the edges of P. For each k, let $a_{i_{k}}$ be the label assigned to the edge $p_{k-1}p_{k}$ , and let $\cdot\epsilon_{k} = +1$ or -1 according as the orientation assigned to this edge goes from $p_{k-1}$ to $p_{k}$ or the reverse. Then the number of edges of P, the orientations of the edges, and the labelling are completely specified by the symbol $$ w = (a _ {i _ {1}}) ^ {\epsilon_ {1}} (a _ {i _ {2}}) ^ {\epsilon_ {2}} \dots (a _ {i _ {n}}) ^ {\epsilon_ {n}}. $$ We call this symbol a labelling scheme of length n for the edges of P; it is simply a sequence of labels with exponents +1 or -1.
- **dependencies:** FC02-C12-U003

#### FC02-C12-U007

- **kind:** Named example
- **source:** §74; printed pp. 446–453; extraction line 15007
- **statement/data:** The torus is obtained from a square by the labelling scheme aba^{-1}b^{-1}.
- **dependencies:** —

#### FC02-C12-U008

- **kind:** Named example
- **source:** §74; printed pp. 446–453; extraction line 15012
- **statement/data:** The projective plane is obtained from a square by the labelling scheme abab.
- **dependencies:** —

#### FC02-C12-U009

- **kind:** Named example
- **source:** §74; printed pp. 446–453; extraction line 15018
- **statement/data:** A suitable edge-pasting of two squares yields the Möbius band; it can also be obtained from one square with scheme abac.
- **dependencies:** —

#### FC02-C12-U010

- **kind:** Named comparison
- **source:** §74; printed pp. 446–453; extraction line 15023
- **statement/data:** Pasting finitely many polygonal regions can yield a disconnected quotient; Example 6 gives a two-square instance.
- **dependencies:** —

#### FC02-C12-U011

- **kind:** Theorem 74.1
- **source:** §74; printed pp. 446–453; extraction line 15027
- **statement/data:** Let X be the space obtained from a finite collection of polygonal regions by pasting edges together according to some labelling scheme. Then X is a compact Hausdorff space.
- **dependencies:** FC02-C12-U003

#### FC02-C12-U012

- **kind:** Theorem 74.2
- **source:** §74; printed pp. 446–453; extraction line 15037
- **statement/data:** Let $P$ be a polygonal region; let $$ w = (a _ {i _ {1}}) ^ {\epsilon_ {1}} \dots (a _ {i _ {n}}) ^ {\epsilon_ {n}} $$ be a labelling scheme for the edges of $P$ . Let $X$ be the resulting quotient space; let $\pi : P \to X$ be the quotient map. If $\pi$ maps all the vertices of $P$ to a single point $x_0$ of $X$ , and if $a_1, \ldots, a_k$ are the distinct labels that appear in the labelling scheme, then $\pi_1(X, x_0)$ is isomorphic to the quotient of the free group on $k$ generators $\alpha_1, \ldots, \alpha_k$ by the least normal subgroup containing the element $$ \left(\alpha_ {i _ {1}}\right) ^ {\epsilon_ {1}} \dots \left(\alpha_ {i _ {n}}\right) ^ {\epsilon_ {n}}. $$
- **dependencies:** FC02-C12-U006

#### FC02-C12-U013

- **kind:** Definition
- **source:** §74; printed pp. 446–453; extraction line 15057
- **statement/data:** Consider the space obtained from a 4n-sided polygonal region P by means of the labelling scheme $$ (a _ {1} b _ {1} a _ {1} ^ {- 1} b _ {1} ^ {- 1}) (a _ {2} b _ {2} a _ {2} ^ {- 1} b _ {2} ^ {- 1}) \dots (a _ {n} b _ {n} a _ {n} ^ {- 1} b _ {n} ^ {- 1}). $$ This space is called the n-fold connected sum of tori, or simply the n-fold torus, and denoted $T#\cdots#T$ .
- **dependencies:** FC02-C12-U006

#### FC02-C12-U014

- **kind:** Theorem 74.3
- **source:** §74; printed pp. 446–453; extraction line 15072
- **statement/data:** Let $X$ denote the $n$ -fold torus. Then $\pi_1(X, x_0)$ is isomorphic to the quotient of the free group on the $2n$ generators $\alpha_1, \beta_1, \ldots, \alpha_n, \beta_n$ by the least normal subgroup containing the element $$ [ \alpha_ {1}, \beta_ {1} ] [ \alpha_ {2}, \beta_ {2} ] \dots [ \alpha_ {n}, \beta_ {n} ], $$ where $[\alpha, \beta] = \alpha \beta \alpha^{-1} \beta^{-1}$ , as usual.
- **dependencies:** FC02-C12-U012

#### FC02-C12-U015

- **kind:** Definition
- **source:** §74; printed pp. 446–453; extraction line 15082
- **statement/data:** Let $m > 1$ Consider the space obtained from a $2m$ -sided polygonal region $P$ in the plane by means of the labelling scheme $$ (a _ {1} a _ {1}) (a _ {2} a _ {2}) \dots (a _ {m} a _ {m}) $$ This space is called the m-fold connected sum of projective planes, or simply the m-fold projective plane, and denoted $P^{2}#\cdots#P^{2}$ .
- **dependencies:** FC02-C12-U006

#### FC02-C12-U016

- **kind:** Theorem 74.4
- **source:** §74; printed pp. 446–453; extraction line 15094
- **statement/data:** Let X denote the m-fold projective plane. Then $\pi_{1}(X, x_{0})$ is isomorphic to the quotient of the free group on m generators $\alpha_{1}, \ldots, \alpha_{m}$ by the least normal subgroup containing the element $$ (\alpha_ {1}) ^ {2} (\alpha_ {2}) ^ {2} \dots (\alpha_ {m}) ^ {2}. $$
- **dependencies:** FC02-C12-U012

### §75 The Homology of Surfaces (pp. 454–456)

#### FC02-C12-U017

- **kind:** Definition
- **source:** §75; printed pp. 454–456; extraction line 15143
- **statement/data:** If $X$ is a path-connected space, let $$ H _ {1} (X) = \pi_ {1} (X, x _ {0}) / [ \pi_ {1} (X, x _ {0}), \pi_ {1} (X, x _ {0}) ]. $$ We call $H_{1}(X)$ the first homology group of X. We omit the base point from the notation because there is a unique path-induced isomorphism between the abelianized fundamental groups based at two different points.
- **dependencies:** FC02-C11-U037

#### FC02-C12-U018

- **kind:** Theorem 75.1
- **source:** §75; printed pp. 454–456; extraction line 15155
- **statement/data:** Let $F$ be a group; let $N$ be a normal subgroup of $F$ ; let $q: F \to F / N$ be the projection. The projection homomorphism $$ p: F \to F / [ F, F ] $$ induces an isomorphism $$ \phi : q (F) / [ q (F), q (F) ] \rightarrow p (F) / p (N). $$ This theorem states, roughly speaking, that if one divides F by N and then abelianizes the quotient, one obtains the same result as if one first abelianizes F and then divides by the image of N in this abelianization.
- **dependencies:** FC02-C12-U017

#### FC02-C12-U019

- **kind:** Corollary 75.2
- **source:** §75; printed pp. 454–456; extraction line 15177
- **statement/data:** Let $F$ be a free group with free generators $\alpha_1, \ldots, \alpha_n$ ; let $N$ be the least normal subgroup of $F$ containing the element $x$ of $F$ ; let $G = F / N$ . Let $p \cdot F \to F / [F, F]$ be projection. Then $G / [G, G]$ is isomorphic to the quotient of $F / [F, F]$ , which is free abelian with basis $p(\alpha_1), \ldots, p(\alpha_n)$ , by the subgroup generated by $p(x)$ .
- **dependencies:** FC02-C12-U018

#### FC02-C12-U020

- **kind:** Theorem 75.3
- **source:** §75; printed pp. 454–456; extraction line 15181
- **statement/data:** If $X$ is the $n$ -fold connected sum of tori, then $H_{1}(X)$ is a free abelian group of rank $2n$ .
- **dependencies:** FC02-C12-U019

#### FC02-C12-U021

- **kind:** Theorem 75.4
- **source:** §75; printed pp. 454–456; extraction line 15185
- **statement/data:** If $X$ is the $m$ -fold connected sum of projective planes, then the torsion subgroup $T(X)$ of $H_1(X)$ has order 2, and $H_1(X) / T(X)$ is a free abelian group of rank $m - 1$ .
- **dependencies:** FC02-C12-U019

#### FC02-C12-U022

- **kind:** Theorem 75.5
- **source:** §75; printed pp. 454–456; extraction line 15189
- **statement/data:** Let $T_{n}$ and $P_{m}$ denote the $n$ -fold connected sum of tori and the $m$ -fold connected sum of projective planes, respectively. Then the surfaces $S^{2}$ ; $T_{1}, T_{2}, \ldots; P_{1}, P_{2}, \ldots$ are topologically distinct.
- **dependencies:** FC02-C12-U020

### §76 Cutting and Pasting (pp. 457–461)

#### FC02-C12-U023

- **kind:** Theorem 76.1
- **source:** §76; printed pp. 457–461; extraction line 15244
- **statement/data:** Suppose X is the space obtained by pasting the edges of m polygonal regions together according to the labelling scheme $$ y _ {0} y _ {1}, w _ {2}, \dots , w _ {m}.\tag{*} $$ Let c be a label not appearing in this scheme. If both $y_{0}$ and $y_{1}$ have length at least two, then X can also be obtained by pasting the edges of $m + 1$ polygonal regions together according to the scheme $$ y _ {0} c ^ {- 1}, c y _ {1}, w _ {2}, \dots , w _ {m}.\tag{**} $$ Conversely, if X is the space obtained from $m + 1$ polygonal regions by means of the scheme ( $*$ ), it can also be obtained from m polygonal regions by means of the scheme (*), providing that c does not appear in scheme (*).
- **dependencies:** —

#### FC02-C12-U024

- **kind:** Construction / convention
- **source:** §76; printed pp. 457–461; extraction line 15260
- **statement/data:** Elementary scheme operations preserving the quotient space are cut, paste, relabel (including reversing every orientation carrying one label), cyclic permutation, flip/formal inverse, cancel aa^{-1}, and uncancel.
- **dependencies:** —

#### FC02-C12-U025

- **kind:** Definition
- **source:** §76; printed pp. 457–461; extraction line 15294
- **statement/data:** We define two labelling schemes for collections of polygonal regions to be equivalent if one can be obtained from the other by a sequence of elementary scheme operations. Since each elementary operation has as its inverse another such operation, this is an equivalence relation.
- **dependencies:** FC02-C12-U023

#### FC02-C12-U026

- **kind:** Named example
- **source:** §76; printed pp. 457–461; extraction line 15296
- **statement/data:** The Klein bottle has scheme aba^{-1}b; elementary scheme operations transform it to aacc, exhibiting it as the 2-fold projective plane P^2#P^2.
- **dependencies:** —

### §77 The Classification Theorem (pp. 462–470)

#### FC02-C12-U027

- **kind:** Definition
- **source:** §77; printed pp. 462–470; extraction line 15332
- **statement/data:** A labelling scheme is proper when every label appears exactly twice.
- **dependencies:** —

#### FC02-C12-U028

- **kind:** Definition
- **source:** §77; printed pp. 462–470; extraction line 15336
- **statement/data:** Let w be a proper labelling scheme for a single polygonal region. We say that w is of torus type if each label in it appears once with exponent +1 and once with exponent -1. Otherwise, we say w is of projective type.
- **dependencies:** FC02-C12-U027

#### FC02-C12-U029

- **kind:** Lemma 77.1
- **source:** §77; printed pp. 462–470; extraction line 15360
- **statement/data:** Let $w$ be a proper scheme of the form $$ w = [ y _ {0} ] a [ y _ {1} ] a [ y _ {2} ], $$ where some of the $y_{i}$ may be empty. Then one has the equivalence $$ w \sim a a [ y _ {0} y _ {1} ^ {- 1} y _ {2} ] $$ where $y_1^{-1}$ denotes the formal inverse of $y_1$ .
- **dependencies:** FC02-C12-U028

#### FC02-C12-U030

- **kind:** Corollary 77.2
- **source:** §77; printed pp. 462–470; extraction line 15400
- **statement/data:** If w is a scheme of projective type, then w is equivalent to a scheme of the same length having the form $$ (a _ {1} a _ {1}) (a _ {2} a _ {2}) \dots (a _ {k} a _ {k}) w _ {1}, $$ where $k \geq 1$ and $w_{1}$ is either empty or of torus type.
- **dependencies:** FC02-C12-U029

#### FC02-C12-U031

- **kind:** Lemma 77.3
- **source:** §77; printed pp. 462–470; extraction line 15440
- **statement/data:** Let w be a proper scheme of the form $w = w_{0}w_{1}$ , where $w_{1}$ is a scheme of torus type that does not contain two adjacent terms having the same label. Then w is equivalent to a scheme of the form $w_{0}w_{2}$ , where $w_{2}$ has the same length as $w_{1}$ and has the form $$ w _ {2} = a b a ^ {- 1} b ^ {- 1} w _ {3}, $$ where $w_{3}$ is of torus type or is empty.
- **dependencies:** FC02-C12-U028

#### FC02-C12-U032

- **kind:** Lemma 77.4
- **source:** §77; printed pp. 462–470; extraction line 15542
- **statement/data:** Let $w$ be a proper scheme of the form $$ w = w _ {0} (c c) \left(a b a ^ {- 1} b ^ {- 1}\right) w _ {1}. $$ Then $w$ is equivalent to the scheme $$ w ^ {\prime} = w _ {0} (a a b b c c) w _ {1}. $$
- **dependencies:** FC02-C12-U028

#### FC02-C12-U033

- **kind:** Theorem 77.5 (The classification theorem)
- **source:** §77; printed pp. 462–470; extraction line 15566
- **statement/data:** Let X be the quotient space obtained from a polygonal region in the plane by pasting its edges together in pairs. Then X is homeomorphic either to $S^{2}$ , to the n-fold torus $T_{n}$ , or to the m-fold projective plane $P_{m}$ .
- **dependencies:** FC02-C12-U030

### §78 Constructing Compact Surfaces (pp. 471–476)

#### FC02-C12-U034

- **kind:** Definition
- **source:** §78; printed pp. 471–476; extraction line 15674
- **statement/data:** Let X be a compact Hausdorff space. A curved triangle in X is a subspace A of X and a homeomorphism $h : T \to A$ , where T is a closed triangular region in the plane. If e is an edge of T, then $h(e)$ is said to be an edge of A; if v is a vertex of T, then $h(v)$ is said to be a vertex of A. A triangulation of X is a collection of curved triangles $A_{1}, \ldots, A_{n}$ in X whose union is X such that for $i \neq j$ , the intersection $A_{i} \cap A_{j}$ is either empty, or a vertex of both $A_{i}$ and $A_{j}$ , or an edge of both. Furthermore, if $h_{i} : T_{i} \to A_{i}$ is the homeomorphism associated with $A_{i}$ , we require that when $A_{i} \cap A_{j}$ is an edge e of both, then the map $h_{j}^{-1}h_{i}$ defines a linear homeomorphism of the edge $h_{i}^{-1}(e)$ of $T_{i}$ with the edge $h_{j}^{-1}(e)$ of $T_{j}$ . If X has a triangulation, it is said to be triangulable.
- **dependencies:** —

#### FC02-C12-U035

- **kind:** Theorem 78.1
- **source:** §78; printed pp. 471–476; extraction line 15678
- **statement/data:** If X is a compact triangulable surface, then X is homeomorphic to the quotient space obtained from a collection of disjoint triangular regions in the plane by pasting their edges together in pairs.
- **dependencies:** FC02-C12-U034

#### FC02-C12-U036

- **kind:** Theorem 78.2
- **source:** §78; printed pp. 471–476; extraction line 15739
- **statement/data:** If X is a compact connected triangulable surface, then X is homeomorphic to a space obtained from a polygonal region in the plane by pasting the edges together in pairs.
- **dependencies:** FC02-C12-U035

#### FC02-C12-U037

- **kind:** Convention
- **source:** §78; printed pp. 471–476; extraction line 15777
- **statement/data:** For the classification discussion the base B is taken path connected and locally path connected, and covering spaces E are taken path connected unless stated otherwise.
- **dependencies:** —

#### FC02-C12-U038

- **kind:** Notation
- **source:** §78; printed pp. 471–476; extraction line 15785
- **statement/data:** For p:E→B with p(e_0)=b_0, the associated subgroup is H_0=p_*(π_1(E,e_0))≤π_1(B,b_0).
- **dependencies:** —

## Chapter 13: Classification of Covering Spaces

### §79 Equivalence of Covering Spaces (pp. 478–483)

#### FC02-C13-U001

- **kind:** Definition
- **source:** §79; printed pp. 478–483; extraction line 15801
- **statement/data:** Let $p: E \to B$ and $p': E' \to B$ be covering maps. They are said to be equivalent if there exists a homeomorphism $h: E \to E'$ such that $p = p' \circ h$ . The homeomorphism $h$ is called an equivalence of covering maps or an equivalence of covering spaces.
- **dependencies:** —

#### FC02-C13-U002

- **kind:** Lemma 79.1 (The general lifting lemma)
- **source:** §79; printed pp. 478–483; extraction line 15807
- **statement/data:** Let $p: E \to B$ be a covering map; let $p(e_0) = b_0$ . Let $f: Y \to B$ be a continuous map, with $f(y_0) = b_0$ . Suppose $Y$ is path connected and locally path connected. The map $f$ can be lifted to a map $\tilde{f}: Y \to E$ such that $\tilde{f}(y_0) = e_0$ if and only if $$ f _ {*} (\pi_ {1} (Y, y _ {0})) \subset p _ {*} (\pi_ {1} (E, e _ {0})). $$ Furthermore, if such a lifting exists, it is unique.
- **dependencies:** FC02-C09-U045

#### FC02-C13-U003

- **kind:** Theorem 79.2
- **source:** §79; printed pp. 478–483; extraction line 15848
- **statement/data:** Let $p: E \to B$ and $p': E' \to B$ be covering maps; let $p(e_0) = p'(e_0') = b_0$ . There is an equivalence $h: E \to E'$ such that $h(e_0) = e_0'$ if and only if the groups $$ H _ {0} = p _ {*} (\pi_ {1} (E, e _ {0})) \quad \text { and } \quad H _ {0} ^ {\prime} = p _ {*} ^ {\prime} (\pi_ {1} (E ^ {\prime}, e _ {0} ^ {\prime})) $$ are equal. If $h$ exists, it is unique.
- **dependencies:** FC02-C13-U002

#### FC02-C13-U004

- **kind:** Definition
- **source:** §79; printed pp. 478–483; extraction line 15876
- **statement/data:** Subgroups H_1,H_2≤G are conjugate if H_2=αH_1α^{-1}; the corresponding equivalence class is the conjugacy class of H.
- **dependencies:** —

#### FC02-C13-U005

- **kind:** Lemma 79.3
- **source:** §79; printed pp. 478–483; extraction line 15878
- **statement/data:** Let $p: E \to B$ be a covering map. Let $e_0$ and $e_1$ be points of $p^{-1}(b_0)$ , and let $H_i = p_*(\pi_1(E, e_i))$ . (a) If $\gamma$ is a path in $E$ from $e_0$ to $e_1$ , and $\alpha$ is the loop $p \circ \gamma$ in $B$ , then the equation $[\alpha] * H_1 * [\alpha]^{-1} = H_0$ holds; hence $H_0$ and $H_1$ are conjugate. (b) Conversely, given $e_0$ , and given a subgroup $H$ of $\pi_1(B, b_0)$ conjugate to $H_0$ , there exists a point $e_1$ of $p^{-1}(b_0)$ such that $H_1 = H$ .
- **dependencies:** FC02-C12-U038

#### FC02-C13-U006

- **kind:** Theorem 79.4
- **source:** §79; printed pp. 478–483; extraction line 15905
- **statement/data:** Let $p: E \to B$ and $p': E' \to B$ be covering maps; let $p(e_0) = p'(e_0') = b_0$ . The covering maps $p$ and $p'$ are equivalent if and only if the subgroups $$ H _ {0} = p _ {*} (\pi_ {1} (E, e _ {0})) \quad a n d \quad H _ {0} ^ {\prime} = p _ {*} ^ {\prime} (\pi_ {1} (E ^ {\prime}, e _ {0} ^ {\prime})) $$ of $\pi_1(B, b_0)$ are conjugate.
- **dependencies:** FC02-C13-U003

#### FC02-C13-U007

- **kind:** Named example / classification
- **source:** §79; printed pp. 478–483; extraction line 15917
- **statement/data:** Connected covers of S^1 are classified by subgroups nZ≤Z: R→S^1 corresponds to 0 and z↦z^n corresponds to nZ; every path-connected cover of S^1 is equivalent to one of these.
- **dependencies:** —

### §80 The Universal Covering Space (pp. 484–486)

#### FC02-C13-U008

- **kind:** Definition
- **source:** §80; printed pp. 484–486; extraction line 15985
- **statement/data:** A covering p:E→B with E simply connected is a universal covering space of B.
- **dependencies:** FC02-C13-U006

#### FC02-C13-U009

- **kind:** Lemma 80.1
- **source:** §80; printed pp. 484–486; extraction line 15989
- **statement/data:** Let B be path connected and locally path connected. Let $p: E \to B$ be a covering map in the former sense (so that E is not required to be path connected). If $E_{0}$ is a path component of E, then the map $p_{0}: E_{0} \to B$ obtained by restricting p is a covering map.
- **dependencies:** FC02-C09-U024

#### FC02-C13-U010

- **kind:** Lemma 80.2
- **source:** §80; printed pp. 484–486; extraction line 15997
- **statement/data:** Let $p, q$ , and $r$ be continuous maps with $p = r \circ q$ , as in the following diagram: (a) If $p$ and $r$ are covering maps, so is $q$ . (b) If $p$ and $q$ are covering maps, so is $r$ .
- **dependencies:** —

#### FC02-C13-U011

- **kind:** Theorem 80.3
- **source:** §80; printed pp. 484–486; extraction line 16027
- **statement/data:** Let $p: E \to B$ be a covering map, with $E$ simply connected. Given any covering map $r: Y \to B$ , there is a covering map $q: E \to Y$ such that $r \circ q = p$ . $$ \begin{array}{c} E \ \Big \downarrow_ {p} \ B \end{array} \begin{array}{c} q \ \Big \downarrow_ {r} \ Y \end{array} $$ This theorem shows why E is called a universal covering space of B; it covers every other covering space of B.
- **dependencies:** FC02-C13-U008

#### FC02-C13-U012

- **kind:** Lemma 80.4
- **source:** §80; printed pp. 484–486; extraction line 16045
- **statement/data:** Let $p: E \to B$ be a covering map; let $p(e_0) = b_0$ . If $E$ is simply connected, then $b_0$ has a neighborhood $U$ such that inclusion $i: U \to B$ induces the trivial homomorphism $$ i _ {*}: \pi_ {1} (U, b _ {0}) \longrightarrow \pi_ {1} (B, b _ {0}). $$
- **dependencies:** FC02-C13-U008

#### FC02-C13-U013

- **kind:** Named counterexample
- **source:** §80; printed pp. 484–486; extraction line 16053
- **statement/data:** The infinite earring is path connected and locally path connected but has no universal covering space.
- **dependencies:** —

### *§81 Covering Transformations (pp. 487–493)

#### FC02-C13-U014

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16071
- **statement/data:** An equivalence E→E of a covering p:E→B is a covering transformation; all covering transformations form the group C(E,p,B).
- **dependencies:** FC02-C13-U001

#### FC02-C13-U015

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16077
- **statement/data:** If $H$ is a subgroup of the group $G$ , then the normalizer of $H$ in $G$ is the subset of $G$ defined by the equation $$ N (H) = {g \mid g H g ^ {- 1} = H }. $$ It is easy to see that $N(H)$ is a subgroup of $G$ . It follows from the definition that it contains $H$ as a normal subgroup and is the largest such subgroup of $G$ .
- **dependencies:** FC02-C13-U004

#### FC02-C13-U016

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16087
- **statement/data:** Given $p: E \to B$ with $p(e_0) = b_0$ , let $F$ be the set $F = p^{-1}(e_0)$ . Let $$ \Phi : \pi_ {1} (B, b _ {0}) / H _ {0} \rightarrow F $$ be the lifting correspondence of Theorem 54.6; it is a bijection. Define also a correspondence $$ \Psi : \mathcal {C} (E, p, B) \rightarrow F $$ by setting $\Psi(h)=h(e_{0})$ for each covering transformation $h:E\to E$ . Since h is uniquely determined once its value at $e_{0}$ is known, the correspondence $\Psi$ is injective.
- **dependencies:** FC02-C09-U045

#### FC02-C13-U017

- **kind:** Lemma 81.1
- **source:** *§81; printed pp. 487–493; extraction line 16101
- **statement/data:** The image of the map $\Psi$ equals the image under $\Phi$ of the subgroup $N(H_0) / H_0$ of $\pi_1(B, b_0) / H_0$ .
- **dependencies:** FC02-C13-U016

#### FC02-C13-U018

- **kind:** Theorem 81.2
- **source:** *§81; printed pp. 487–493; extraction line 16107
- **statement/data:** The bijection $$ \Phi^ {- 1} \circ \Psi : \mathcal {C} (E, p, B) \rightarrow N (H _ {0}) / H _ {0} $$ is an isomorphism of groups.
- **dependencies:** FC02-C13-U017

#### FC02-C13-U019

- **kind:** Corollary 81.3
- **source:** *§81; printed pp. 487–493; extraction line 16140
- **statement/data:** The group $H_0$ is a normal subgroup of $\pi_1(B, b_0)$ if and only if for every pair of points $e_1$ and $e_2$ of $p^{-1}(b_0)$ , there is a covering transformation $h: E \to E$ with $h(e_1) = e_2$ . In this case, there is an isomorphism $$ \Phi^ {- 1} \circ \Psi : \mathcal {C} (E, p, B) \rightarrow \pi_ {1} (B, b _ {0}) / H _ {0}. $$
- **dependencies:** FC02-C13-U018

#### FC02-C13-U020

- **kind:** Corollary 81.4
- **source:** *§81; printed pp. 487–493; extraction line 16146
- **statement/data:** Let $p: E \to B$ be a covering map. If $E$ is simply connected, then $$ \mathcal {C} (E, p, B) \cong \pi_ {1} (B, b _ {0}). $$
- **dependencies:** FC02-C13-U019

#### FC02-C13-U021

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16152
- **statement/data:** A covering p:E→B is regular when H_0=p_*(π_1(E,e_0)) is normal in π_1(B,b_0).
- **dependencies:** FC02-C13-U019

#### FC02-C13-U022

- **kind:** Named example
- **source:** *§81; printed pp. 487–493; extraction line 16154
- **statement/data:** Every covering of S^1 is regular; for R→S^1 the covering transformations are x↦x+n and form a group isomorphic to Z.
- **dependencies:** —

#### FC02-C13-U023

- **kind:** Named counterexample
- **source:** *§81; printed pp. 487–493; extraction line 16156
- **statement/data:** The displayed covering of the figure eight has trivial covering-transformation group.
- **dependencies:** —

#### FC02-C13-U024

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16165
- **statement/data:** Let X be a space, and let G be a subgroup of the group of homeomorphisms of X with itself. The orbit space X/G is defined to be the quotient space obtained from X by means of the equivalence relation $x \sim g(x)$ for all $x \in X$ and all $g \in G$ . The equivalence class of x is called the orbit of x.
- **dependencies:** FC02-C13-U014

#### FC02-C13-U025

- **kind:** Definition
- **source:** *§81; printed pp. 487–493; extraction line 16167
- **statement/data:** If $G$ is a group of homeomorphisms of $X$ , the action of $G$ on $X$ is said to be properly discontinuous if for every $x \in X$ there is a neighborhood $U$ of $x$ such that $g(U)$ is disjoint from $U$ whenever $g \neq e$ . (Here $e$ is the identity element of $G$ .) It follows that $g_0(U)$ and $g_1(U)$ are disjoint whenever $g_0 \neq g_1$ , for otherwise $U$ and $g_0^{-1}g_1(U)$ would not be disjoint.
- **dependencies:** FC02-C13-U024

#### FC02-C13-U026

- **kind:** Theorem 81.5
- **source:** *§81; printed pp. 487–493; extraction line 16169
- **statement/data:** Let X be path connected and locally path connected; let G be a group of homeomorphisms of X. The quotient map $\pi: X \to X/G$ is a covering map if and only if the action of G is properly discontinuous. In this case, the covering map $\pi$ is regular and G is its group of covering transformations.
- **dependencies:** FC02-C13-U025

#### FC02-C13-U027

- **kind:** Theorem 81.6
- **source:** *§81; printed pp. 487–493; extraction line 16181
- **statement/data:** If $p: X \to B$ is a regular covering map and $G$ is its group of covering transformations, then there is a homeomorphism $k: X / G \to B$ such that $p = k \circ \pi$ , where $\pi: X \to X / G$ is the projection. $$ \begin{array}{c c c} X & = & X \ \Biggl \downarrow_ {\pi} & & \Biggl \downarrow_ {p} \ X / G & \xrightarrow {k} & B \end{array} $$
- **dependencies:** FC02-C13-U021

#### FC02-C13-U028

- **kind:** Named comparison
- **source:** *§81; printed pp. 487–493; extraction line 16189
- **statement/data:** Two properly discontinuous Z/2-actions on S^1×I have orbit spaces respectively homeomorphic to the cylinder and to the Möbius band.
- **dependencies:** —

### §82 Existence of Covering Spaces (pp. 494–498)

#### FC02-C13-U029

- **kind:** Definition
- **source:** §82; printed pp. 494–498; extraction line 16262
- **statement/data:** A space $B$ is said to be semilocally simply connected if for each $b \in B$ , there is a neighborhood $U$ of $b$ such that the homomorphism $$ i _ {*}: \pi_ {1} (U, b) \rightarrow \pi_ {1} (B, b) $$ induced by inclusion is trivial.
- **dependencies:** FC02-C13-U012

#### FC02-C13-U030

- **kind:** Theorem 82.1
- **source:** §82; printed pp. 494–498; extraction line 16274
- **statement/data:** Let B be path connected, locally path connected, and semilocally simply connected. Let $b_{0} \in B$ . Given a subgroup H of $\pi_{1}(B, b_{0})$ , there exists a covering map $p : E \to B$ and a point $e_{0} \in p^{-1}(b_{0})$ such that $$ p _ {*} (\pi_ {1} (E, e _ {0})) = H. $$
- **dependencies:** FC02-C13-U029

#### FC02-C13-U031

- **kind:** Corollary 82.2
- **source:** §82; printed pp. 494–498; extraction line 16399
- **statement/data:** The space B has a universal covering space if and only if B is path connected, locally path connected, and semilocally simply connected.
- **dependencies:** FC02-C13-U030

## Chapter 14: Applications to Group Theory

### §83 Covering Spaces of Graphs (pp. 501–505)

#### FC02-C14-U001

- **kind:** Definition
- **source:** §83; printed pp. 501–505; extraction line 16479
- **statement/data:** A linear graph is a space $X$ that is written as the union of a collection of subspaces $A_{\alpha}$ , each of which is an arc, such that: (1) The intersection $A_{\alpha} \cap A_{\beta}$ of two arcs is either empty or consists of a single point that is an end point of each. (2) The topology of $X$ is coherent with the subspaces $A_{\alpha}$ . The arcs $A_{\alpha}$ are called the edges of X, and their interiors are called the open edges of X. Their end points are called the vertices of X; we denote the set of vertices of X by $X^{0}$ .
- **dependencies:** FC02-C11-U052

#### FC02-C14-U002

- **kind:** Lemma 83.1
- **source:** §83; printed pp. 501–505; extraction line 16491
- **statement/data:** Every linear graph $X$ is Hausdorff; in fact, it is normal.
- **dependencies:** —

#### FC02-C14-U003

- **kind:** Named example
- **source:** §83; printed pp. 501–505; extraction line 16499
- **statement/data:** An arbitrary wedge of circles can be given the structure of a linear graph by subdividing each circle into three edges with the wedge point as a vertex.
- **dependencies:** FC02-C14-U001

#### FC02-C14-U004

- **kind:** Named example
- **source:** §83; printed pp. 501–505; extraction line 16501
- **statement/data:** For discrete J, collapsing {0}×J in [0,1]×J to one point gives a linear graph whose edges are the images of [0,1]×{α}.
- **dependencies:** —

#### FC02-C14-U005

- **kind:** Definition
- **source:** §83; printed pp. 501–505; extraction line 16507
- **statement/data:** Let X be a linear graph. Let Y be a subspace of X that is a union of edges of X. Then Y is closed in X and is itself a linear graph; we call it a subgraph of X.
- **dependencies:** FC02-C14-U001

#### FC02-C14-U006

- **kind:** Lemma 83.2
- **source:** §83; printed pp. 501–505; extraction line 16511
- **statement/data:** Let X be a linear graph. If C is a compact subspace of X, there exists a finite subgraph Y of X that contains C. If C is connected, Y can be chosen to be connected.
- **dependencies:** FC02-C14-U005

#### FC02-C14-U007

- **kind:** Lemma 83.3
- **source:** §83; printed pp. 501–505; extraction line 16517
- **statement/data:** If X is a linear graph, then X is locally path connected and semilocally simply connected.
- **dependencies:** FC02-C14-U001

#### FC02-C14-U008

- **kind:** Definition / notation
- **source:** §83; printed pp. 501–505; extraction line 16523
- **statement/data:** For a vertex x, the closed star is the union of edges incident to x; St x is obtained from it by deleting every other vertex and is called the star of x.
- **dependencies:** FC02-C14-U001

#### FC02-C14-U009

- **kind:** Theorem 83.4
- **source:** §83; printed pp. 501–505; extraction line 16537
- **statement/data:** Let $p: E \to X$ be a covering map, where $X$ is a linear graph. If $A_{\alpha}$ is an edge of $X$ and $B$ is a path component of $p^{-1}(A_{\alpha})$ , then $p$ maps $B$ homeomorphically onto $A_{\alpha}$ . Furthermore, the space $E$ is a linear graph, with the path components of the spaces $p^{-1}(A_{\alpha})$ as its edges.
- **dependencies:** FC02-C14-U001

### §84 The Fundamental Group of a Graph (pp. 506–512)

#### FC02-C14-U010

- **kind:** Convention
- **source:** §84; printed pp. 506–512; extraction line 16559
- **statement/data:** From §84 onward, the source uses “graph” for “linear graph”.
- **dependencies:** —

#### FC02-C14-U011

- **kind:** Definition
- **source:** §84; printed pp. 506–512; extraction line 16561
- **statement/data:** An oriented edge e of a graph X is an edge of X together with an ordering of its vertices; the first is called the initial vertex, and the second, the final vertex, of e. An edge path in X is a sequence $e_{1}, \ldots, e_{n}$ of oriented edges of X such that the final vertex of $e_{i}$ equals the initial vertex of $e_{i+1}$ , for $i = 1, \ldots, n-1$ . Such an edge path is entirely specified by the sequence of vertices $x_{0}, \ldots, x_{n}$ , where $x_{0}$ is the initial vertex of $e_{1}$ and $x_{i}$ is the final vertex of $e_{i}$ for $i = 1, \ldots, n$ . It is said to be an edge path from $x_{0}$ to $x_{n}$ . It is called a closed edge path if $x_{0} = x_{n}$ .
- **dependencies:** FC02-C14-U001

#### FC02-C14-U012

- **kind:** Construction
- **source:** §84; printed pp. 506–512; extraction line 16569
- **statement/data:** An oriented edge path determines a canonical path obtained by concatenating the linear parametrizations of its oriented edges; a closed edge path determines a loop.
- **dependencies:** FC02-C14-U011

#### FC02-C14-U013

- **kind:** Lemma 84.1
- **source:** §84; printed pp. 506–512; extraction line 16571
- **statement/data:** A graph X is connected if and only if every pair of vertices of X can be joined by an edge path in X.
- **dependencies:** FC02-C14-U011

#### FC02-C14-U014

- **kind:** Definition
- **source:** §84; printed pp. 506–512; extraction line 16577
- **statement/data:** Let $e_{1}, \ldots, e_{n}$ be an edge path in the linear graph X. It can happen that for some i, the oriented edges $e_{i}$ and $e_{i+1}$ consist of the same edge of X, but with opposite orientations. If this situation does not occur, then the edge path is said to be a reduced edge path.
- **dependencies:** FC02-C14-U011

#### FC02-C14-U015

- **kind:** Construction
- **source:** §84; printed pp. 506–512; extraction line 16579
- **statement/data:** Reducing an edge path deletes consecutive occurrences of the same edge with opposite orientations; repeated reduction yields reduced edge paths.
- **dependencies:** FC02-C14-U014

#### FC02-C14-U016

- **kind:** Definition
- **source:** §84; printed pp. 506–512; extraction line 16584
- **statement/data:** A subgraph T of X is said to be a tree in X if T is connected and T contains no closed reduced edge paths.
- **dependencies:** FC02-C14-U014

#### FC02-C14-U017

- **kind:** Lemma 84.2
- **source:** §84; printed pp. 506–512; extraction line 16593
- **statement/data:** If T is a tree in X, and if A is an edge of X that intersects T in a single vertex, then $T \cup A$ is a tree in X. Conversely, if T is a finite tree in X that consists of more than one edge, then there is a tree $T_{0}$ in X and an edge A of X that intersects $T_{0}$ in a single vertex, such that $T = T_{0} \cup A$ .
- **dependencies:** FC02-C14-U016

#### FC02-C14-U018

- **kind:** Theorem 84.3
- **source:** §84; printed pp. 506–512; extraction line 16603
- **statement/data:** Any tree $T$ is simply connected.
- **dependencies:** FC02-C14-U016

#### FC02-C14-U019

- **kind:** Definition
- **source:** §84; printed pp. 506–512; extraction line 16609
- **statement/data:** A tree $T$ in $X$ is maximal if there is no tree in $X$ that properly contains $T$ .
- **dependencies:** FC02-C14-U016

#### FC02-C14-U020

- **kind:** Theorem 84.4
- **source:** §84; printed pp. 506–512; extraction line 16611
- **statement/data:** Let X be a connected graph. A tree T in X is maximal if and only if it contains all the vertices of X.
- **dependencies:** FC02-C14-U019

#### FC02-C14-U021

- **kind:** Theorem 84.5
- **source:** §84; printed pp. 506–512; extraction line 16617
- **statement/data:** If $X$ is a linear graph, every tree $T_0$ in $X$ is contained in a maximal tree in $X$ .
- **dependencies:** FC02-C14-U019

#### FC02-C14-U022

- **kind:** Lemma 84.6
- **source:** §84; printed pp. 506–512; extraction line 16629
- **statement/data:** Suppose $X = U \cup V$ , where $U$ and $V$ are open sets of $X$ . Suppose that $U \cap V$ is the union of two disjoint open path-connected sets $A$ and $B$ , that $\alpha$ is a path in $U$ from the point $a$ of $A$ to the point $b$ of $B$ , and that $\beta$ is a path in $V$ from $b$ to $a$ . If $U$ and $V$ are simply connected, then the class $[\alpha * \beta]$ generates $\pi_1(X, a)$ .
- **dependencies:** FC02-C11-U046

#### FC02-C14-U023

- **kind:** Theorem 84.7
- **source:** §84; printed pp. 506–512; extraction line 16644
- **statement/data:** Let X be a connected graph that is not a tree. Then the fundamental group of X is a nontrivial free group. Indeed, if T is a maximal tree in X, then the fundamental group of X has a system of free generators that is in bijective correspondence with the collection of edges of X that are not in T.
- **dependencies:** FC02-C14-U021

### §85 Subgroups of Free Groups (pp. 513–516)

#### FC02-C14-U024

- **kind:** Theorem 85.1
- **source:** §85; printed pp. 513–516; extraction line 16720
- **statement/data:** If $H$ is a subgroup of a free group $F$ , then $H$ is free.
- **dependencies:** FC02-C14-U023

#### FC02-C14-U025

- **kind:** Definition
- **source:** §85; printed pp. 513–516; extraction line 16734
- **statement/data:** If X is a finite linear graph, we define the Euler number of X to be the number of vertices of X minus the number of edges. It is commonly denoted by the Greek letter chi, as $\chi(X)$ .
- **dependencies:** FC02-C14-U001

#### FC02-C14-U026

- **kind:** Lemma 85.2
- **source:** §85; printed pp. 513–516; extraction line 16736
- **statement/data:** If X is a finite, connected linear graph, then the cardinality of a system of free generators for the fundamental group of X is $1 - \chi(X)$ .
- **dependencies:** FC02-C14-U025

#### FC02-C14-U027

- **kind:** Definition
- **source:** §85; printed pp. 513–516; extraction line 16748
- **statement/data:** Let H be a subgroup of the group G. If the collection G/H of right cosets of H in G is finite, its cardinality is called the index of H in G. (The collection of left cosets of H in G has the same cardinality, of course.)
- **dependencies:** —

#### FC02-C14-U028

- **kind:** Theorem 85.3
- **source:** §85; printed pp. 513–516; extraction line 16750
- **statement/data:** Let $F$ be a free group with $n + 1$ free generators; let $H$ be a subgroup of $F$ . If $H$ has index $k$ in $F$ , then $H$ has $kn + 1$ free generators.
- **dependencies:** FC02-C14-U024, FC02-C14-U026
