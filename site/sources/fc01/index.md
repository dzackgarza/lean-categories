---
title: "FC01 — Dummit & Foote, Abstract Algebra"
---

---
title: FC01 — Dummit–Foote, Abstract Algebra
---


Corpus source: `FC01` in [Foundational source corpus v1 (frozen)](/corpus.html).

Pinned source: David S. Dummit and Richard M. Foote, *Abstract Algebra*, 3rd ed., Wiley, 2004; complete book, exercises excluded.

Markdown extraction: ``local-write-api-1783380265761-A4FFDNKB_extracted.md``.

This is the canonical Sweep-I source-unit catalogue for FC01. Every unit has a stable source-local ID consumed unchanged by Sweeps II–IV. Existing [definition-only catalogue](/catalogues/dummit-and-foote-definition-catalogue.html) is retained as a legacy cross-check/mapping input; it does not define source scope.


Included: definitions, constructions, conventions/notation, lemmas, propositions, theorems, corollaries, and reusable named examples/comparisons in source order. Excluded: exercises, proof text, and purely expository prose. The extraction does not preserve dependable unit-level printed page boundaries, so body records give exact section page spans from the source table of contents plus exact extraction lines instead of inventing per-unit page numbers.

Dependencies are stable FC01 unit IDs. A dash means no additional earlier corpus unit was recorded as necessary beyond the ambient mathematical data stated in the unit itself.


The legacy definition-only inventory was used as a completeness cross-check, not copied mechanically. In particular, several legacy labels do not define additional corpus-v1 units: `generalized eigenspace` occurs only in the Chapter 12 exercise block; `subrepresentation` is the legacy name for the main-text `G`-invariant/`G`-stable subspace = `FG`-submodule unit; `restriction of a character` is ordinary function restriction inside a main-text example/proof rather than a standalone source definition; and the extraction/source does not state a separate "refinement of a composition series" definition in §3.4. The main-text constructible-element definition is catalogued under the source's own wording.


Units: 37.


- **Kind:** Convention/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L422.
- **Statement/data:** For a subset B of a set A specified by a condition, use set-builder notation B={a∈A | condition on a}.
- **Dependencies:** —


- **Kind:** Convention/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L428.
- **Statement/data:** The order/cardinality of a set A is denoted |A|; for finite A this is its number of elements.
- **Dependencies:** —


- **Kind:** Definition/construction.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L430.
- **Statement/data:** For sets A,B, the Cartesian product A×B is the set of ordered pairs (a,b) with a∈A and b∈B.
- **Dependencies:** —


- **Kind:** Convention/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L432.
- **Statement/data:** Use Z,Q,R,C for the integers, rationals, reals, and complex numbers, and Z^+,Q^+,R^+ for their positive nonzero elements where applicable.
- **Dependencies:** —


- **Kind:** Convention/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L444.
- **Statement/data:** For a function f:A→B, A is the domain, B the codomain, f(a) its value; functions/maps are synonymous and are written with arguments on the left.
- **Dependencies:** —


- **Kind:** Definition/convention.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L446.
- **Statement/data:** A purported function is well defined when its rule determines an unambiguous value for every element of its domain.
- **Dependencies:** FC01-C00-U005 (`function-conventions`)


- **Kind:** Definition/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L450.
- **Statement/data:** For f:A→B and subsets/points, f(C) is the image, f^{-1}(C) the preimage, and f^{-1}({b}) the fiber over b.
- **Dependencies:** FC01-C00-U005 (`function-conventions`)


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L466.
- **Statement/data:** A map is injective if equal values imply equal inputs, surjective if every codomain element has a preimage, and bijective if both.
- **Dependencies:** FC01-C00-U005 (`function-conventions`)


- **Kind:** Proposition 1.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L480.
- **Statement/data:** For f:A→B: f injective iff it has a left inverse; f surjective iff it has a right inverse (assuming the usual choice implicit in the text); f bijective iff it has a two-sided inverse.
- **Dependencies:** FC01-C00-U008 (`injective-surjective-bijective`)


- **Kind:** Definition/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L492.
- **Statement/data:** For a bijection f, its unique two-sided inverse is denoted f^{-1}.
- **Dependencies:** FC01-C00-U009 (`inverse-characterization`)


- **Kind:** Definition/notation.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L496.
- **Statement/data:** If A⊆B and f:B→C, the restriction of f to A is f|_A:A→C.
- **Dependencies:** FC01-C00-U005 (`function-conventions`)


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L498.
- **Statement/data:** If A⊆B and g:A→C, a map f:B→C with f|_A=g is an extension of g to B.
- **Dependencies:** FC01-C00-U011 (`restriction`)


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L502.
- **Statement/data:** A binary relation on A is a subset of A×A; write a~b when (a,b) lies in the relation.
- **Dependencies:** —


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L504.
- **Statement/data:** A relation ~ on A is reflexive, symmetric, or transitive in the usual respective senses; an equivalence relation has all three properties.
- **Dependencies:** FC01-C00-U013 (`binary-relation`)


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L514.
- **Statement/data:** For an equivalence relation on A, [a]={x∈A:x~a} is the equivalence class of a; any member of a class is a representative.
- **Dependencies:** FC01-C00-U014 (`equivalence-relation`)


- **Kind:** Definition.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L516.
- **Statement/data:** A partition of a nonempty set A is a collection of nonempty pairwise disjoint subsets whose union is A.
- **Dependencies:** —


- **Kind:** Proposition 2.
- **Locator:** §0.1 “Basics”; printed pp. 1–3 (section span); extraction L526.
- **Statement/data:** An equivalence relation on a nonempty set partitions it into equivalence classes; conversely, a partition defines an equivalence relation by declaring two elements equivalent exactly when they lie in the same part.
- **Dependencies:** FC01-C00-U015 (`equivalence-class`), FC01-C00-U016 (`partition`)


- **Kind:** Recorded theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L588.
- **Statement/data:** Every nonempty subset of Z_{>0} has a least element.
- **Dependencies:** —


- **Kind:** Definition/notation.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L590.
- **Statement/data:** For a,b∈Z with a≠0, a divides b (a|b) if b=ac for some c∈Z.
- **Dependencies:** —


- **Kind:** Definition/theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L592.
- **Statement/data:** For nonzero a,b∈Z there is a unique positive gcd d=(a,b): d divides a,b and every common divisor divides d.
- **Dependencies:** FC01-C00-U019 (`integer-divisibility`)


- **Kind:** Definition.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L598.
- **Statement/data:** Nonzero integers a,b are relatively prime if (a,b)=1.
- **Dependencies:** FC01-C00-U020 (`gcd-integers`)


- **Kind:** Definition/theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L600.
- **Statement/data:** For nonzero a,b∈Z there is a unique positive lcm l divisible by a,b and dividing every common multiple; gcd(a,b)·lcm(a,b)=ab (up to the sign convention implicit in the printed statement).
- **Dependencies:** FC01-C00-U019 (`integer-divisibility`), FC01-C00-U020 (`gcd-integers`)


- **Kind:** Theorem/construction.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L608.
- **Statement/data:** For nonzero integers a,b there are unique q,r∈Z with a=qb+r and 0≤r<|b|.
- **Dependencies:** FC01-C00-U018 (`well-ordering-Z`)


- **Kind:** Algorithm/theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L616.
- **Statement/data:** Iterating the Division Algorithm on nonzero a,b terminates; the last nonzero remainder is gcd(a,b).
- **Dependencies:** FC01-C00-U023 (`integer-division-algorithm`), FC01-C00-U020 (`gcd-integers`)


- **Kind:** Corollary.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L658.
- **Statement/data:** For nonzero a,b∈Z there exist x,y∈Z such that (a,b)=ax+by.
- **Dependencies:** FC01-C00-U024 (`euclidean-algorithm-Z`)


- **Kind:** Definition.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L678.
- **Statement/data:** A positive integer p>1 is prime if its only positive divisors are 1 and p; n>1 nonprime is composite.
- **Dependencies:** FC01-C00-U019 (`integer-divisibility`)


- **Kind:** Recorded proposition.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L680.
- **Statement/data:** If p is prime and p|ab for a,b∈Z, then p|a or p|b.
- **Dependencies:** FC01-C00-U026 (`prime-composite-Z`)


- **Kind:** Theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L682.
- **Statement/data:** Every integer n>1 has a factorization into powers of distinct positive primes, unique up to ordering.
- **Dependencies:** FC01-C00-U026 (`prime-composite-Z`), FC01-C00-U027 (`euclid-lemma-Z`)


- **Kind:** Corollary/comparison.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L696.
- **Statement/data:** For positive a,b written over the same distinct primes with exponents α_i,β_i, gcd uses min(α_i,β_i) and lcm uses max(α_i,β_i).
- **Dependencies:** FC01-C00-U028 (`fundamental-theorem-arithmetic`), FC01-C00-U020 (`gcd-integers`), FC01-C00-U022 (`lcm-integers`)


- **Kind:** Definition.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L714.
- **Statement/data:** Euler’s φ-function is φ(n)=#{1≤a≤n:(a,n)=1}.
- **Dependencies:** FC01-C00-U021 (`relatively-prime`)


- **Kind:** Recorded theorem.
- **Locator:** §0.2 “Properties of the Integers”; printed pp. 4–7 (section span); extraction L714.
- **Statement/data:** For prime p and a≥1, φ(p^a)=p^{a-1}(p-1); φ is multiplicative on coprime arguments, hence φ(∏p_i^{α_i})=∏p_i^{α_i-1}(p_i-1).
- **Dependencies:** FC01-C00-U030 (`euler-phi`), FC01-C00-U028 (`fundamental-theorem-arithmetic`)


- **Kind:** Definition/notation.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L778.
- **Statement/data:** For fixed n>0, a≡b (mod n) iff n|(a-b); this is an equivalence relation on Z. The class of a is its congruence/residue class mod n.
- **Dependencies:** FC01-C00-U019 (`integer-divisibility`), FC01-C00-U014 (`equivalence-relation`)


- **Kind:** Construction/notation.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L786.
- **Statement/data:** Z/nZ is the set of residue classes modulo n, represented by 0̄,1̄,…,(n−1)̄.
- **Dependencies:** FC01-C00-U032 (`congruence-mod-n`)


- **Kind:** Construction.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L798.
- **Statement/data:** Define ā+b̄=(a+b)̄ and ā·b̄=(ab)̄ on Z/nZ.
- **Dependencies:** FC01-C00-U033 (`Zmodn`)


- **Kind:** Theorem 3.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L818.
- **Statement/data:** Addition and multiplication on Z/nZ are independent of representatives.
- **Dependencies:** FC01-C00-U034 (`modular-arithmetic`), FC01-C00-U032 (`congruence-mod-n`)


- **Kind:** Definition/notation.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L840.
- **Statement/data:** (Z/nZ)^× is the set of residue classes having multiplicative inverses modulo n.
- **Dependencies:** FC01-C00-U035 (`modular-arithmetic-well-defined`)


- **Kind:** Proposition 4.
- **Locator:** §0.3 “The Integers Modulo n”; printed pp. 8–12 (section span); extraction L848.
- **Statement/data:** (Z/nZ)^×={ā:(a,n)=1}.
- **Dependencies:** FC01-C00-U036 (`units-Zmodn`), FC01-C00-U021 (`relatively-prime`), FC01-C00-U025 (`bezout-Z`)


Units: 48.


- **Kind:** Definition.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L948.
- **Statement/data:** A binary operation on a set G is a function G×G→G; it is associative if (a*b)*c=a*(b*c), and a,b commute if a*b=b*a.
- **Dependencies:** —


- **Kind:** Definition.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L970.
- **Statement/data:** A group is a set G with an associative binary operation, an identity element, and inverses for every element; it is abelian if the operation is commutative.
- **Dependencies:** FC01-C01-U001 (`binary-operation`)


- **Kind:** Reusable examples.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L984.
- **Statement/data:** Z,Q,R,C under addition are abelian groups; Q^×,R^×,C^× denote the corresponding nonzero multiplicative groups where applicable.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Construction/example.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1008.
- **Statement/data:** For groups A,B, define A×B with componentwise operation (a1,b1)(a2,b2)=(a1a2,b1b2); this is the direct-product group.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Proposition 1.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1018.
- **Statement/data:** In a group the identity and each inverse are unique; (a^{-1})^{-1}=a, (ab)^{-1}=b^{-1}a^{-1}; products of any finite length are unambiguous by generalized associativity.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Convention/notation.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1088.
- **Statement/data:** Use 1 for the identity, a^{-1} for inverse, and integer powers a^n; in additive groups use 0, −a, and na.
- **Dependencies:** FC01-C01-U005 (`group-basic-identities`)


- **Kind:** Proposition 2.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1096.
- **Statement/data:** For a,b∈G the equations ax=b and ya=b have unique solutions; consequently left and right cancellation hold.
- **Dependencies:** FC01-C01-U005 (`group-basic-identities`)


- **Kind:** Definition.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1106.
- **Statement/data:** The order |x| of x∈G is the least n>0 with x^n=1, or ∞ if no such n exists.
- **Dependencies:** FC01-C01-U006 (`multiplicative-notation`)


- **Kind:** Definition.
- **Locator:** §1.1 “Basic Axioms and Examples”; printed pp. 16–22 (section span); extraction L1120.
- **Statement/data:** For finite G={g1,…,gn} with g1=1, the multiplication/group table is the n×n matrix with (i,j)-entry g_i g_j.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Construction/definition.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1250.
- **Statement/data:** D_{2n} is the group of symmetries of a regular n-gon under composition; it has order 2n.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Construction/comparison.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1269.
- **Statement/data:** With r a rotation through 2π/n and s a reflection, |r|=n, |s|=2, every element is uniquely r^i or sr^i (0≤i<n), and rs=sr^{-1}.
- **Dependencies:** FC01-C01-U010 (`dihedral-group`), FC01-C01-U008 (`element-order`)


- **Kind:** Definition.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1299.
- **Statement/data:** A subset S of a group is a set of generators if every group element can be expressed using elements of S and their inverses; the group is generated by S.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Definition.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1301.
- **Statement/data:** An equation among generators that holds in the group is a relation among those generators.
- **Dependencies:** FC01-C01-U012 (`generating-set-informal`)


- **Kind:** Definition/notation.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1303.
- **Statement/data:** A presentation specifies generators together with defining relations, written ⟨S | R⟩.
- **Dependencies:** FC01-C01-U012 (`generating-set-informal`), FC01-C01-U013 (`relation`)


- **Kind:** Reusable presentation.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1309.
- **Statement/data:** D_{2n}=⟨r,s | r^n=s^2=1, rs=sr^{-1}⟩ (equivalently srs=r^{-1}).
- **Dependencies:** FC01-C01-U011 (`dihedral-standard-generators`), FC01-C01-U014 (`presentation-informal`)


- **Kind:** Reusable comparisons.
- **Locator:** §1.2 “Dihedral Groups”; printed pp. 23–28 (section span); extraction L1322.
- **Statement/data:** The section exhibits presentations whose displayed relations force additional hidden relations, illustrating that a presentation can define a smaller group than a naive normal-form count suggests.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`)


- **Kind:** Definition/construction.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1403.
- **Statement/data:** For a nonempty set Ω, S_Ω is the group of all permutations Ω→Ω under composition; for Ω={1,…,n}, write S_n, with |S_n|=n!.
- **Dependencies:** FC01-C01-U002 (`group`), FC01-C00-U010 (`inverse-map`)


- **Kind:** Definition/notation.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1411.
- **Statement/data:** A cycle (a1 a2 … ak) is the permutation sending a_i↦a_{i+1}, a_k↦a_1 and fixing all other points; k is its length.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`)


- **Kind:** Algorithm/construction.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1441.
- **Statement/data:** Every permutation is decomposed by following the orbit of an unused point until it closes, recording that cycle, then repeating on unused points.
- **Dependencies:** FC01-C01-U018 (`cycle`)


- **Kind:** Definition/convention.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1451.
- **Statement/data:** Cycles with disjoint supports are disjoint; 1-cycles are normally omitted from cycle notation.
- **Dependencies:** FC01-C01-U018 (`cycle`)


- **Kind:** Convention.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1481.
- **Statement/data:** Products of permutations are composed right-to-left: in στ, apply τ first and then σ.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`)


- **Kind:** Lemma/recorded fact.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1497.
- **Statement/data:** Disjoint cycles commute.
- **Dependencies:** FC01-C01-U020 (`disjoint-cycles`), FC01-C01-U021 (`permutation-composition-convention`)


- **Kind:** Convention/identity.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1501.
- **Statement/data:** A cycle is unchanged by cyclic rotation of its entries; the text often starts a displayed cycle with its least entry for readability.
- **Dependencies:** FC01-C01-U018 (`cycle`)


- **Kind:** Recorded theorem.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1509.
- **Statement/data:** The decomposition of a permutation into disjoint cycles is unique up to reordering the cycles and cyclically rotating entries within each cycle.
- **Dependencies:** FC01-C01-U019 (`cycle-decomposition-algorithm`), FC01-C01-U020 (`disjoint-cycles`)


- **Kind:** Recorded corollary.
- **Locator:** §1.3 “Symmetric Groups”; printed pp. 29–33 (section span); extraction L1509.
- **Statement/data:** The order of a permutation is the least common multiple of the lengths of the disjoint cycles in its cycle decomposition.
- **Dependencies:** FC01-C01-U024 (`cycle-decomposition-uniqueness`), FC01-C01-U008 (`element-order`)


- **Kind:** Notation/convention.
- **Locator:** §1.4 “Matrix Groups”; printed pp. 34–35 (section span); extraction L1701.
- **Statement/data:** For prime p, F_p denotes the field Z/pZ.
- **Dependencies:** FC01-C00-U035 (`modular-arithmetic-well-defined`), FC01-C00-U037 (`units-Zmodn-coprime`)


- **Kind:** Definition/example.
- **Locator:** §1.4 “Matrix Groups”; printed pp. 34–35 (section span); extraction L1703.
- **Statement/data:** A field is a commutative system with addition and multiplication in which nonzero elements form a multiplicative group; F^× denotes that group.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Definition/construction.
- **Locator:** §1.4 “Matrix Groups”; printed pp. 34–35 (section span); extraction L1715.
- **Statement/data:** GL_n(F) is the group of invertible n×n matrices over a field F under matrix multiplication.
- **Dependencies:** FC01-C01-U027 (`field-multiplicative-group`), FC01-C01-U002 (`group`)


- **Kind:** Recorded theorem.
- **Locator:** §1.4 “Matrix Groups”; printed pp. 34–35 (section span); extraction L1727.
- **Statement/data:** Every finite field has order p^m for some prime p and m≥1.
- **Dependencies:** FC01-C01-U026 (`finite-field-notation`)


- **Kind:** Recorded proposition.
- **Locator:** §1.4 “Matrix Groups”; printed pp. 34–35 (section span); extraction L1729.
- **Statement/data:** For |F|=q, |GL_n(F)|=(q^n−1)(q^n−q)⋯(q^n−q^{n−1}).
- **Dependencies:** FC01-C01-U028 (`general-linear-group`), FC01-C01-U029 (`finite-field-order-record`)


- **Kind:** Construction/definition.
- **Locator:** §1.5 “The Quaternion Group”; printed p. 36 (section span); extraction L1783.
- **Statement/data:** Q_8={±1,±i,±j,±k} with i^2=j^2=k^2=ijk=−1; it is a nonabelian group of order 8.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Definition.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1829.
- **Statement/data:** A map φ:G→H is a group homomorphism if φ(xy)=φ(x)φ(y) for all x,y∈G.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Definition.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1845.
- **Statement/data:** A bijective group homomorphism is an isomorphism; groups are isomorphic if an isomorphism exists.
- **Dependencies:** FC01-C01-U032 (`group-homomorphism`), FC01-C00-U008 (`injective-surjective-bijective`)


- **Kind:** Recorded fact.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1855.
- **Statement/data:** Isomorphism is an equivalence relation on groups, so groups partition into isomorphism classes.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`), FC01-C00-U014 (`equivalence-relation`)


- **Kind:** Reusable comparison.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1857.
- **Statement/data:** The exponential map x↦e^x is an isomorphism from (R,+) to (R_{>0},×).
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Reusable comparison.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1861.
- **Statement/data:** If Ω and Δ are in bijection then S_Ω≅S_Δ; for finite sets the converse follows from equality of factorial orders.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Recorded classification.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1867.
- **Statement/data:** Every nonabelian group of order 6 is isomorphic to S_3; hence groups of order 6 are, up to isomorphism, Z/6Z and S_3.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`), FC01-C01-U017 (`symmetric-group`)


- **Kind:** Recorded proposition.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1871.
- **Statement/data:** Isomorphic groups have equal order, agree on being abelian, and have matching multisets/existence patterns of element orders under an isomorphism.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`), FC01-C01-U008 (`element-order`)


- **Kind:** Construction principle.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1883.
- **Statement/data:** A map on generators satisfying the defining relations extends to a homomorphism; if the images generate the target it is surjective, and if source and target are finite of equal order it is an isomorphism.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Reusable comparison.
- **Locator:** §1.6 “Homomorphisms and Isomorphisms”; printed pp. 36–40 (section span); extraction L1897.
- **Statement/data:** D_6≅S_3, via their standard presentations/actions.
- **Dependencies:** FC01-C01-U015 (`dihedral-presentation`), FC01-C01-U017 (`symmetric-group`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Definition.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L1997.
- **Statement/data:** A left action of G on a nonempty set A is a map G×A→A with 1·a=a and g1·(g2·a)=(g1g2)·a.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Construction.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2005.
- **Statement/data:** An action defines for each g a permutation σ_g(a)=g·a and hence a homomorphism G→S_A; conversely every homomorphism G→S_A defines an action.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C01-U017 (`symmetric-group`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Convention/definition.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2039.
- **Statement/data:** A right action is written a·g and obeys a·1=a and (a·g1)·g2=a·(g1g2).
- **Dependencies:** FC01-C01-U041 (`group-action`)


- **Kind:** Definition/example.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2045.
- **Statement/data:** The trivial action has g·a=a for every g∈G,a∈A.
- **Dependencies:** FC01-C01-U041 (`group-action`)


- **Kind:** Definition.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2047.
- **Statement/data:** An action is faithful if only 1 fixes every point; its kernel is {g∈G:g·a=a for all a∈A}.
- **Dependencies:** FC01-C01-U041 (`group-action`)


- **Kind:** Reusable example.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2059.
- **Statement/data:** S_n acts naturally on {1,…,n} by evaluation of permutations.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`), FC01-C01-U041 (`group-action`)


- **Kind:** Reusable example.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2061.
- **Statement/data:** D_{2n} acts faithfully on the n vertices of the regular n-gon, giving an embedding into S_n.
- **Dependencies:** FC01-C01-U010 (`dihedral-group`), FC01-C01-U041 (`group-action`), FC01-C01-U045 (`faithful-action-kernel`)


- **Kind:** Reusable construction.
- **Locator:** §1.7 “Group Actions”; printed pp. 41–45 (section span); extraction L2065.
- **Statement/data:** Every group G acts faithfully on itself by left multiplication g·a=ga (the left regular action).
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C01-U007 (`group-equations-cancellation`)


Units: 40.


- **Kind:** Definition.
- **Locator:** §2.1 “Definition and Examples”; printed pp. 46–48 (section span); extraction L2163.
- **Statement/data:** A nonempty subset H of a group G is a subgroup, written H≤G, if it is closed under products and inverses.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Reusable examples.
- **Locator:** §2.1 “Definition and Examples”; printed pp. 46–48 (section span); extraction L2173.
- **Statement/data:** For every group G, {1} and G are subgroups; {1} is the trivial subgroup.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Proposition 1 (Subgroup Criterion).
- **Locator:** §2.1 “Definition and Examples”; printed pp. 46–48 (section span); extraction L2191.
- **Statement/data:** A subset H⊆G is a subgroup iff H≠∅ and xy^{-1}∈H for all x,y∈H. If H is finite, nonemptiness and closure under multiplication already suffice.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Definition.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2285.
- **Statement/data:** For A⊆G, C_G(A)={g∈G:gag^{-1}=a for every a∈A}, equivalently the elements commuting with every element of A.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Convention/notation.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2293.
- **Statement/data:** For a∈G, write C_G(a) for C_G({a}).
- **Dependencies:** FC01-C02-U004 (`centralizer`)


- **Kind:** Definition.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2299.
- **Statement/data:** Z(G)={g∈G:gx=xg for every x∈G}; equivalently Z(G)=C_G(G).
- **Dependencies:** FC01-C02-U004 (`centralizer`)


- **Kind:** Construction/notation.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2303.
- **Statement/data:** For g∈G and A⊆G, gAg^{-1}={gag^{-1}:a∈A}.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Definition.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2303.
- **Statement/data:** N_G(A)={g∈G:gAg^{-1}=A}, the normalizer of A in G.
- **Dependencies:** FC01-C02-U007 (`conjugate-subset`)


- **Kind:** Definition.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2337.
- **Statement/data:** If G acts on S and s∈S, the stabilizer G_s={g∈G:g·s=s}; it is a subgroup of G.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Definition.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2355.
- **Statement/data:** For an action of G on S, its kernel is {g∈G:g·s=s for all s∈S}; it is a subgroup of G.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Reusable example.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2367.
- **Statement/data:** For the natural action of D_8 on the vertices of a square, each vertex stabilizer has order 2 and the action kernel is trivial.
- **Dependencies:** FC01-C01-U047 (`dihedral-vertex-action`), FC01-C02-U009 (`stabilizer`), FC01-C02-U010 (`action-kernel`)


- **Kind:** Reusable example.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2369.
- **Statement/data:** For D_8 acting on the two unordered pairs of opposite vertices, the kernel is {1,s,r^2,sr^2}, and it equals either point stabilizer.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C02-U009 (`stabilizer`), FC01-C02-U010 (`action-kernel`)


- **Kind:** Construction/comparison.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2371.
- **Statement/data:** G acts on P(G) by g·B=gBg^{-1}; under this action N_G(A) is the stabilizer of A.
- **Dependencies:** FC01-C02-U007 (`conjugate-subset`), FC01-C02-U008 (`normalizer`), FC01-C02-U009 (`stabilizer`)


- **Kind:** Comparison.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2379.
- **Statement/data:** N_G(A) acts on A by conjugation, and C_G(A) is the kernel of this action; hence C_G(A)≤N_G(A).
- **Dependencies:** FC01-C02-U004 (`centralizer`), FC01-C02-U008 (`normalizer`), FC01-C02-U010 (`action-kernel`)


- **Kind:** Comparison.
- **Locator:** §2.2 “Centralizers and Normalizers, Stabilizers and Kernels”; printed pp. 49–53 (section span); extraction L2385.
- **Statement/data:** Z(G) is the kernel of the conjugation action of G on itself, hence Z(G)≤G.
- **Dependencies:** FC01-C02-U006 (`center`), FC01-C02-U010 (`action-kernel`)


- **Kind:** Definition.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2469.
- **Statement/data:** A group H is cyclic if H=⟨x⟩={x^n:n∈Z} for some x∈H; such x is a generator.
- **Dependencies:** FC01-C01-U002 (`group`)


- **Kind:** Construction/algorithm.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2487.
- **Statement/data:** If x has finite order n and t=nq+k with 0≤k<n, then x^t=x^k; thus exponents of powers of x may be reduced modulo n using integer division.
- **Dependencies:** FC01-C01-U008 (`element-order`), FC01-C00-U023 (`integer-division-algorithm`)


- **Kind:** Proposition 2.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2505.
- **Statement/data:** If H=⟨x⟩ then |H|=|x|. If |x|=n<∞, the distinct elements are 1,x,…,x^{n−1}; if |x|=∞, all integer powers of x are distinct.
- **Dependencies:** FC01-C02-U016 (`cyclic-group`), FC01-C01-U008 (`element-order`)


- **Kind:** Proposition 3.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2525.
- **Statement/data:** If x^m=x^n=1 in a group and d=(m,n), then x^d=1. In particular, if x^m=1 and |x|<∞ then |x| divides m.
- **Dependencies:** FC01-C01-U008 (`element-order`), FC01-C00-U025 (`bezout-Z`)


- **Kind:** Theorem 4.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2537.
- **Statement/data:** Any two cyclic groups of the same order are isomorphic. Finite cyclic groups of order n are isomorphic via x^k↦y^k; every infinite cyclic group is isomorphic to (Z,+).
- **Dependencies:** FC01-C02-U018 (`cyclic-order-cardinality`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Notation/convention.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2571.
- **Statement/data:** Z_n denotes the cyclic group of order n, written multiplicatively; Z_n≅Z/nZ. The infinite cyclic group is represented by Z additively.
- **Dependencies:** FC01-C02-U020 (`cyclic-groups-classified-by-order`), FC01-C00-U033 (`Zmodn`)


- **Kind:** Proposition 5.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2577.
- **Statement/data:** For x∈G and a∈Z−{0}: if |x|=∞ then |x^a|=∞; if |x|=n<∞ then |x^a|=n/(n,a). In particular, if a|n then |x^a|=n/a.
- **Dependencies:** FC01-C02-U019 (`common-power-gcd`), FC01-C02-U018 (`cyclic-order-cardinality`)


- **Kind:** Proposition 6.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2627.
- **Statement/data:** If H=⟨x⟩ is infinite then x^a generates H iff a=±1. If |H|=n, x^a generates H iff (a,n)=1; hence H has φ(n) generators.
- **Dependencies:** FC01-C02-U022 (`order-of-power`), FC01-C00-U030 (`euler-phi`)


- **Kind:** Theorem 7.
- **Locator:** §2.3 “Cyclic Groups and Cyclic Subgroups”; printed pp. 54–60 (section span); extraction L2647.
- **Statement/data:** Every subgroup of a cyclic group is cyclic. For infinite ⟨x⟩, nontrivial subgroups are uniquely ⟨x^d⟩ for d≥1. For finite |⟨x⟩|=n, for each a|n there is a unique subgroup of order a, namely ⟨x^{n/a}⟩, and ⟨x^m⟩=⟨x^{(n,m)}⟩.
- **Dependencies:** FC01-C02-U016 (`cyclic-group`), FC01-C02-U022 (`order-of-power`), FC01-C00-U018 (`well-ordering-Z`), FC01-C00-U023 (`integer-division-algorithm`)


- **Kind:** Proposition 8.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2823.
- **Statement/data:** The intersection of any nonempty collection of subgroups of G is a subgroup of G.
- **Dependencies:** FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Definition/construction.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2833.
- **Statement/data:** For A⊆G, ⟨A⟩ is the intersection of all subgroups of G containing A; equivalently, the unique smallest subgroup containing A.
- **Dependencies:** FC01-C02-U025 (`intersection-subgroups`)


- **Kind:** Construction.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2845.
- **Statement/data:** The word closure of A consists of all finite products a_1^{ε_1}⋯a_n^{ε_n} with a_i∈A and ε_i=±1, including the empty word 1.
- **Dependencies:** FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Proposition 9.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2853.
- **Statement/data:** The word closure of A equals ⟨A⟩.
- **Dependencies:** FC01-C02-U027 (`word-closure`), FC01-C02-U026 (`generated-subgroup`), FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Corollary/construction.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2873.
- **Statement/data:** If G is abelian and A={a_1,…,a_k}, then ⟨A⟩={a_1^{α_1}⋯a_k^{α_k}:α_i∈Z}; if |a_i|=d_i<∞ then |⟨A⟩|≤∏d_i.
- **Dependencies:** FC01-C02-U028 (`generated-subgroup-word-description`), FC01-C01-U002 (`group`)


- **Kind:** Reusable comparison.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2887.
- **Statement/data:** For D_{2n}, taking a=s and b=rs gives |a|=|b|=2 and D_{2n}=⟨a,b⟩, while |D_{2n}|=2n; generator orders alone do not bound a nonabelian group’s order.
- **Dependencies:** FC01-C01-U011 (`dihedral-standard-generators`), FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Reusable comparison.
- **Locator:** §2.4 “Subgroups Generated by Subsets of a Group”; printed pp. 61–65 (section span); extraction L2895.
- **Statement/data:** S_n=⟨(1 2),(1 2 … n)⟩.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`), FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Construction/definition.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L2989.
- **Statement/data:** For finite G, the subgroup lattice is the Hasse diagram of subgroups ordered by inclusion: connect A<B when no subgroup lies strictly between them.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Definition/comparison.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L2991.
- **Statement/data:** For H,K≤G, their join is the smallest subgroup containing both, ⟨H,K⟩; in the subgroup lattice it is the least common upper bound, while H∩K is the greatest common lower bound.
- **Dependencies:** FC01-C02-U026 (`generated-subgroup`), FC01-C02-U025 (`intersection-subgroups`), FC01-C02-U032 (`subgroup-lattice`)


- **Kind:** Reusable comparison.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L2995.
- **Statement/data:** Isomorphic groups have isomorphic subgroup lattices, but nonisomorphic groups can have identical subgroup lattices.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`), FC01-C02-U032 (`subgroup-lattice`)


- **Kind:** Reusable comparison.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3001.
- **Statement/data:** For Z_n, the subgroup lattice is the divisor lattice of n via the unique subgroup of each divisor order.
- **Dependencies:** FC01-C02-U024 (`cyclic-subgroup-classification`), FC01-C02-U032 (`subgroup-lattice`)


- **Kind:** Reusable named example.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3019.
- **Statement/data:** The Klein four-group V_4 is the abelian group {1,a,b,c} with each nonidentity element of order 2 and ab=c, bc=a, ca=b; V_4 is not cyclic.
- **Dependencies:** FC01-C01-U002 (`group`), FC01-C01-U008 (`element-order`)


- **Kind:** Reusable named examples.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3029.
- **Statement/data:** The section records subgroup lattices for S_3, D_8, Q_8, and D_{16} for later use.
- **Dependencies:** FC01-C02-U032 (`subgroup-lattice`), FC01-C01-U017 (`symmetric-group`), FC01-C01-U010 (`dihedral-group`), FC01-C01-U031 (`quaternion-group`)


- **Kind:** Convention.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3045.
- **Statement/data:** A displayed partial subgroup lattice may omit intermediate subgroups; an unbroken line in such a sublattice need not be a cover relation.
- **Dependencies:** FC01-C02-U032 (`subgroup-lattice`)


- **Kind:** Reusable example.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3049.
- **Statement/data:** In D_{16}, the displayed subgroups ⟨sr^2,r^4⟩ and ⟨r^2⟩ have join ⟨s,r^2⟩ and intersection ⟨r^4⟩.
- **Dependencies:** FC01-C02-U033 (`join-subgroups`), FC01-C01-U010 (`dihedral-group`)


- **Kind:** Reusable comparison.
- **Locator:** §2.5 “The Lattice of Subgroups of a Group”; printed pp. 66–72 (section span); extraction L3051.
- **Statement/data:** The subgroup lattice plus a commutation check determines C_{D_8}(s)=⟨s,r^2⟩.
- **Dependencies:** FC01-C02-U004 (`centralizer`), FC01-C02-U032 (`subgroup-lattice`)


Units: 57.


- **Kind:** Definition.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3168.
- **Statement/data:** For a group homomorphism φ:G→H, ker φ={g∈G:φ(g)=1_H}.
- **Dependencies:** FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Proposition 1.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3176.
- **Statement/data:** For φ:G→H: φ(1_G)=1_H; φ(g^{-1})=φ(g)^{-1}; φ(g^n)=φ(g)^n for n∈Z; ker φ≤G; and im φ≤H.
- **Dependencies:** FC01-C01-U032 (`group-homomorphism`), FC01-C03-U001 (`homomorphism-kernel`), FC01-C02-U001 (`subgroup`)


- **Kind:** Definition/construction.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3212.
- **Statement/data:** If φ:G→H has kernel K, the quotient/factor group G/K is initially defined as the set of fibers of φ, with the product of the fibers over a,b defined as the fiber over ab.
- **Dependencies:** FC01-C03-U001 (`homomorphism-kernel`), FC01-C03-U002 (`homomorphism-basic-properties`)


- **Kind:** Proposition 2.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3218.
- **Statement/data:** If X=φ^{-1}(a) and u∈X, then X=uK=Ku, where K=ker φ.
- **Dependencies:** FC01-C03-U003 (`quotient-as-fibers`), FC01-C03-U001 (`homomorphism-kernel`)


- **Kind:** Definition/notation.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3246.
- **Statement/data:** For N≤G and g∈G, gN={gn:n∈N} is a left coset and Ng={ng:n∈N} a right coset; any element of a coset is a representative.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Convention.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3256.
- **Statement/data:** For additive G write g+N and N+g for left and right cosets.
- **Dependencies:** FC01-C03-U005 (`left-right-cosets`)


- **Kind:** Theorem 3.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3260.
- **Statement/data:** If K is the kernel of a group homomorphism, the fibers are the cosets of K and multiplication (uK)(vK)=uvK is well defined; left and right cosets coincide.
- **Dependencies:** FC01-C03-U004 (`fibers-as-cosets`), FC01-C03-U005 (`left-right-cosets`)


- **Kind:** Convention/notation.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3286.
- **Statement/data:** For K=ker φ and u∈G, write ū for the coset uK and Ḡ for G/K; multiplication is ūv̄=uv̄.
- **Dependencies:** FC01-C03-U007 (`coset-multiplication-kernel`)


- **Kind:** Reusable named example.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3294.
- **Statement/data:** The map G→1 sending every g to 1 is the trivial homomorphism; its kernel is G and G/G is the trivial group.
- **Dependencies:** FC01-C01-U032 (`group-homomorphism`), FC01-C03-U001 (`homomorphism-kernel`), FC01-C03-U007 (`coset-multiplication-kernel`)


- **Kind:** Reusable example.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3296.
- **Statement/data:** Projection φ:R^2→R, (x,y)↦x, is an additive homomorphism with kernel the y-axis; its fibers are affine vertical lines.
- **Dependencies:** FC01-C01-U032 (`group-homomorphism`), FC01-C03-U004 (`fibers-as-cosets`)


- **Kind:** Reusable example.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3320.
- **Statement/data:** The displayed surjection Q_8→V_4 has kernel {±1}, yielding Q_8/{±1}≅V_4.
- **Dependencies:** FC01-C01-U031 (`quaternion-group`), FC01-C02-U036 (`Klein-four-group`), FC01-C03-U003 (`quotient-as-fibers`)


- **Kind:** Proposition 4.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3332.
- **Statement/data:** For N≤G, left cosets partition G; uN=vN iff v^{-1}u∈N, equivalently u and v represent the same coset.
- **Dependencies:** FC01-C03-U005 (`left-right-cosets`), FC01-C00-U016 (`partition`)


- **Kind:** Proposition 5.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3362.
- **Statement/data:** For N≤G, the rule (uN)(vN)=uvN is well defined iff gng^{-1}∈N for every g∈G,n∈N; when well defined it gives the left cosets a group structure with identity N and inverse (gN)^{-1}=g^{-1}N.
- **Dependencies:** FC01-C03-U012 (`cosets-partition`), FC01-C03-U005 (`left-right-cosets`)


- **Kind:** Definition.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3418.
- **Statement/data:** gng^{-1} is the conjugate of n by g and gNg^{-1} the conjugate of N. An element g normalizes N if gNg^{-1}=N; N is normal in G, written N◁G, if every g∈G normalizes N.
- **Dependencies:** FC01-C02-U007 (`conjugate-subset`), FC01-C02-U008 (`normalizer`)


- **Kind:** Theorem 6.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3424.
- **Statement/data:** For N≤G the following are equivalent: N◁G; N_G(N)=G; gN=Ng for every g; coset multiplication makes G/N a group; and gNg^{-1}⊆N for every g.
- **Dependencies:** FC01-C03-U014 (`conjugate-element-subgroup-normal`), FC01-C02-U008 (`normalizer`), FC01-C03-U013 (`coset-product-well-defined-criterion`)


- **Kind:** Proposition 7.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3442.
- **Statement/data:** A subgroup N≤G is normal iff N is the kernel of some group homomorphism.
- **Dependencies:** FC01-C03-U015 (`normal-subgroup-equivalences`), FC01-C03-U001 (`homomorphism-kernel`)


- **Kind:** Definition.
- **Locator:** §3.1 “Definitions and Examples”; printed pp. 73–88 (section span); extraction L3468.
- **Statement/data:** For N◁G, π:G→G/N, π(g)=gN, is the natural projection homomorphism; for H̄≤G/N, π^{-1}(H̄) is its complete preimage in G.
- **Dependencies:** FC01-C03-U016 (`normal-iff-kernel`), FC01-C03-U007 (`coset-multiplication-kernel`)


- **Kind:** Theorem 8 (Lagrange).
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3750.
- **Statement/data:** If G is finite and H≤G, then |H| divides |G| and the number of left cosets of H is |G|/|H|.
- **Dependencies:** FC01-C03-U012 (`cosets-partition`), FC01-C02-U001 (`subgroup`)


- **Kind:** Definition/notation.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3768.
- **Statement/data:** For H≤G, possibly with G infinite, the number of left cosets of H in G is the index |G:H|.
- **Dependencies:** FC01-C03-U005 (`left-right-cosets`)


- **Kind:** Corollary 9.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3774.
- **Statement/data:** If G is finite and x∈G, then |x| divides |G|; consequently x^{|G|}=1.
- **Dependencies:** FC01-C03-U018 (`lagrange`), FC01-C02-U018 (`cyclic-order-cardinality`)


- **Kind:** Corollary 10.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3778.
- **Statement/data:** Every group of prime order p is cyclic, hence isomorphic to Z_p.
- **Dependencies:** FC01-C03-U018 (`lagrange`), FC01-C02-U020 (`cyclic-groups-classified-by-order`)


- **Kind:** Reusable comparison.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3804.
- **Statement/data:** Normality is not transitive: the section gives H◁K◁G with H not normal in G.
- **Dependencies:** FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Definition.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3812.
- **Statement/data:** A group G is simple if its only normal subgroups are 1 and G (with the nontriviality convention |G|>1 made explicit later in §3.4).
- **Dependencies:** FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Theorem 11 (Cauchy).
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3858.
- **Statement/data:** If p is prime and p divides the order of a finite group G, then G has an element of order p.
- **Dependencies:** FC01-C03-U018 (`lagrange`), FC01-C01-U008 (`element-order`)


- **Kind:** Theorem 12 (Sylow existence).
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3864.
- **Statement/data:** If |G|=p^αm with p∤m, then G has a subgroup of order p^α.
- **Dependencies:** FC01-C03-U024 (`cauchy`), FC01-C02-U001 (`subgroup`)


- **Kind:** Definition.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3870.
- **Statement/data:** For subgroups H,K of a group, HK={hk:h∈H,k∈K}.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Proposition 13.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3876.
- **Statement/data:** For finite subgroups H,K, |HK|=|H||K|/|H∩K|; no assumption that HK is a subgroup is needed.
- **Dependencies:** FC01-C03-U026 (`subgroup-set-product`), FC01-C03-U018 (`lagrange`)


- **Kind:** Proposition 14.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3898.
- **Statement/data:** For subgroups H,K≤G, HK is a subgroup iff HK=KH.
- **Dependencies:** FC01-C03-U026 (`subgroup-set-product`), FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Corollary 15.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3924.
- **Statement/data:** If H≤N_G(K), then HK≤G. In particular, if K◁G then HK≤G for every H≤G.
- **Dependencies:** FC01-C03-U028 (`subgroup-product-criterion`), FC01-C02-U008 (`normalizer`), FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Definition.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3934.
- **Statement/data:** A subset A⊆N_G(K) is said to normalize K; a subset A⊆C_G(K) is said to centralize K.
- **Dependencies:** FC01-C02-U008 (`normalizer`), FC01-C02-U004 (`centralizer`)


- **Kind:** Convention.
- **Locator:** §3.2 “More on Cosets and Lagrange's Theorem”; printed pp. 89–96 (section span); extraction L3948.
- **Statement/data:** The text does not use G/H for the set of left cosets when H is nonnormal; “quotient group” notation G/H is reserved for H◁G.
- **Dependencies:** FC01-C03-U005 (`left-right-cosets`), FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Theorem 16 (First Isomorphism Theorem).
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4026.
- **Statement/data:** For a homomorphism φ:G→H, ker φ◁G and G/ker φ≅φ(G).
- **Dependencies:** FC01-C03-U001 (`homomorphism-kernel`), FC01-C03-U016 (`normal-iff-kernel`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Corollary 17.
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4028.
- **Statement/data:** For φ:G→H, φ is injective iff ker φ=1; moreover |G:ker φ|=|φ(G)| (cardinal/index interpretation as in the text).
- **Dependencies:** FC01-C03-U032 (`first-isomorphism-group`), FC01-C03-U019 (`group-index`)


- **Kind:** Theorem 18 (Second/Diamond Isomorphism Theorem).
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4038.
- **Statement/data:** If A,B≤G and A≤N_G(B), then AB≤G, B◁AB, A∩B◁A, and AB/B≅A/(A∩B).
- **Dependencies:** FC01-C03-U029 (`normalizer-product-corollary`), FC01-C03-U032 (`first-isomorphism-group`)


- **Kind:** Theorem 19 (Third Isomorphism Theorem).
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4059.
- **Statement/data:** If H◁G, K◁G and H≤K, then K/H◁G/H and (G/H)/(K/H)≅G/K.
- **Dependencies:** FC01-C03-U017 (`natural-projection-group`), FC01-C03-U032 (`first-isomorphism-group`)


- **Kind:** Theorem 20 (Fourth/Lattice Isomorphism Theorem).
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4089.
- **Statement/data:** If N◁G, A↦A/N gives a bijection between subgroups A of G containing N and subgroups of G/N, preserving inclusion, indices, joins, intersections, and normality.
- **Dependencies:** FC01-C03-U017 (`natural-projection-group`), FC01-C02-U032 (`subgroup-lattice`), FC01-C02-U033 (`join-subgroups`)


- **Kind:** Construction/convention.
- **Locator:** §3.3 “The Isomorphism Theorems”; printed pp. 97–100 (section span); extraction L4127.
- **Statement/data:** If Φ:G→H is a homomorphism with N◁G and N≤ker Φ, then Φ factors uniquely through π:G→G/N via an induced homomorphism φ:G/N→H; the triangle Φ=φ∘π is said to commute.
- **Dependencies:** FC01-C03-U017 (`natural-projection-group`), FC01-C03-U032 (`first-isomorphism-group`)


- **Kind:** Proposition 21.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4164.
- **Statement/data:** If G is finite abelian and p divides |G|, then G contains an element of order p.
- **Dependencies:** FC01-C03-U024 (`cauchy`)


- **Kind:** Definition.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4178.
- **Statement/data:** A group G is simple if |G|>1 and its only normal subgroups are 1 and G.
- **Dependencies:** FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Definition.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4184.
- **Statement/data:** A chain 1=N_0◁N_1◁⋯◁N_k=G is a composition series if each N_{i+1}/N_i is simple; these quotient groups are the composition factors.
- **Dependencies:** FC01-C03-U039 (`simple-group`), FC01-C03-U017 (`natural-projection-group`)


- **Kind:** Theorem 22 (Jordan–Hölder).
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4200.
- **Statement/data:** Every nontrivial finite group has a composition series, and any two composition series have the same length and the same composition factors up to permutation and isomorphism.
- **Dependencies:** FC01-C03-U040 (`composition-series`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Recorded theorem.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4224.
- **Statement/data:** Every finite simple group belongs to one of 18 infinite families or is one of 26 sporadic groups.
- **Dependencies:** FC01-C03-U039 (`simple-group`)


- **Kind:** Recorded theorem (Feit–Thompson consequence).
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4236.
- **Statement/data:** A finite simple group of odd order is cyclic of prime order.
- **Dependencies:** FC01-C03-U039 (`simple-group`), FC01-C02-U016 (`cyclic-group`)


- **Kind:** Construction/comparison.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4240.
- **Statement/data:** The extension problem asks, for groups A,B, for all groups G with N◁G, N≅B and G/N≅A; this is the second part of the Hölder program.
- **Dependencies:** FC01-C03-U040 (`composition-series`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Definition.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4244.
- **Statement/data:** A group G is solvable if there is a chain 1=G_0◁G_1◁⋯◁G_s=G whose successive quotients G_{i+1}/G_i are abelian.
- **Dependencies:** FC01-C03-U014 (`conjugate-element-subgroup-normal`), FC01-C03-U017 (`natural-projection-group`)


- **Kind:** Recorded theorem.
- **Locator:** §3.4 “Composition Series and the Hölder Program”; printed pp. 101–105 (section span); extraction L4256.
- **Statement/data:** A finite group G is solvable iff for every divisor n of |G| with gcd(n,|G|/n)=1, G has a subgroup of order n.
- **Dependencies:** FC01-C03-U045 (`solvable-group`), FC01-C00-U020 (`gcd-integers`)


- **Kind:** Definition.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4336.
- **Statement/data:** A 2-cycle in S_n is a transposition.
- **Dependencies:** FC01-C01-U018 (`cycle`)


- **Kind:** Recorded proposition.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4351.
- **Statement/data:** S_n is generated by all transpositions (i j), 1≤i<j≤n.
- **Dependencies:** FC01-C03-U047 (`transposition`), FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Construction.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4364.
- **Statement/data:** For Δ=∏_{1≤i<j≤n}(x_i−x_j), define ε(σ)∈{±1} by σ(Δ)=ε(σ)Δ.
- **Dependencies:** FC01-C01-U017 (`symmetric-group`)


- **Kind:** Definition.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4412.
- **Statement/data:** ε(σ) is the sign of σ; σ is even if ε(σ)=1 and odd if ε(σ)=−1.
- **Dependencies:** FC01-C03-U049 (`vandermonde-sign-construction`)


- **Kind:** Proposition 23.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4420.
- **Statement/data:** The sign map ε:S_n→{±1} is a group homomorphism.
- **Dependencies:** FC01-C03-U050 (`permutation-sign-parity`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Proposition 24.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4464.
- **Statement/data:** Every transposition is odd, and ε:S_n→{±1} is surjective for n≥2.
- **Dependencies:** FC01-C03-U047 (`transposition`), FC01-C03-U051 (`sign-homomorphism`)


- **Kind:** Definition.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4466.
- **Statement/data:** A_n=ker ε is the alternating group of degree n, i.e. the subgroup of even permutations.
- **Dependencies:** FC01-C03-U051 (`sign-homomorphism`), FC01-C03-U001 (`homomorphism-kernel`)


- **Kind:** Corollary/comparison.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4468.
- **Statement/data:** For n≥2, S_n/A_n≅{±1}, so [S_n:A_n]=2 and |A_n|=n!/2.
- **Dependencies:** FC01-C03-U053 (`alternating-group`), FC01-C03-U032 (`first-isomorphism-group`), FC01-C01-U017 (`symmetric-group`)


- **Kind:** Corollary.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4480.
- **Statement/data:** The parity of the number of transpositions in any transposition factorization of σ∈S_n is independent of the factorization and equals its sign.
- **Dependencies:** FC01-C03-U052 (`transpositions-odd-sign-surjective`), FC01-C03-U048 (`symmetric-generated-transpositions`)


- **Kind:** Proposition 25.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4492.
- **Statement/data:** A permutation is odd iff the number of even-length cycles in its disjoint cycle decomposition is odd.
- **Dependencies:** FC01-C01-U024 (`cycle-decomposition-uniqueness`), FC01-C03-U050 (`permutation-sign-parity`)


- **Kind:** Reusable comparisons.
- **Locator:** §3.5 “Transpositions and the Alternating Group”; printed pp. 106–111 (section span); extraction L4502.
- **Statement/data:** A_1 and A_2 are trivial, A_3=⟨(1 2 3)⟩≅Z_3, and A_4 has order 12 and is isomorphic to the rotational symmetry group of a regular tetrahedron.
- **Dependencies:** FC01-C03-U053 (`alternating-group`), FC01-C03-U054 (`alternating-index-order`), FC01-C02-U021 (`Zn-cyclic-notation`)


Units: 44.


- **Kind:** Definition.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4570.
- **Statement/data:** For G acting on nonempty A: the kernel consists of elements acting trivially on all A; G_a is the stabilizer of a; the action is faithful iff its kernel is 1.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C02-U010 (`action-kernel`), FC01-C02-U009 (`stabilizer`), FC01-C01-U045 (`faithful-action-kernel`)


- **Kind:** Comparison.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4578.
- **Statement/data:** The action kernel equals the kernel of its associated permutation representation and equals ⋂_{a∈A}G_a; it is normal, and G/ker acts faithfully on A.
- **Dependencies:** FC01-C04-U001 (`action-kernel-stabilizer-faithful-recap`), FC01-C03-U016 (`normal-iff-kernel`)


- **Kind:** Proposition 1.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4610.
- **Statement/data:** For any group G and nonempty set A, actions of G on A are in bijection with homomorphisms G→S_A via g·a=φ(g)(a).
- **Dependencies:** FC01-C01-U042 (`action-to-permutation-hom`), FC01-C01-U017 (`symmetric-group`)


- **Kind:** Definition.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4614.
- **Statement/data:** A permutation representation of G is a homomorphism G→S_A for some nonempty A; an action affords/induces its associated permutation representation.
- **Dependencies:** FC01-C04-U003 (`actions-homs-bijection`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Proposition 2.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4620.
- **Statement/data:** For G acting on nonempty A, a~b iff a=g·b for some g∈G is an equivalence relation. The orbit of a has cardinality |G:G_a|.
- **Dependencies:** FC01-C01-U041 (`group-action`), FC01-C02-U009 (`stabilizer`), FC01-C00-U014 (`equivalence-relation`), FC01-C03-U019 (`group-index`)


- **Kind:** Definition.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4658.
- **Statement/data:** The orbit of a is {g·a:g∈G}; an action is transitive if it has one orbit, equivalently any a,b are related by a=g·b for some g.
- **Dependencies:** FC01-C04-U005 (`orbit-equivalence-orbit-stabilizer`)


- **Kind:** Construction/comparison.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4680.
- **Statement/data:** For σ∈S_n, the orbits of ⟨σ⟩ on {1,…,n} are exactly the supports of the disjoint cycles; this gives existence and uniqueness of disjoint cycle decomposition up to cycle order and cyclic rotation.
- **Dependencies:** FC01-C04-U006 (`orbit-transitive`), FC01-C01-U024 (`cycle-decomposition-uniqueness`), FC01-C02-U016 (`cyclic-group`)


- **Kind:** Definition/convention.
- **Locator:** §4.1 “Group Actions and Permutation Representations”; printed pp. 112–117 (section span); extraction L4708.
- **Statement/data:** A subgroup of a symmetric group is a permutation group. Its orbits mean the orbits in the natural action; the orbits of σ mean those of ⟨σ⟩.
- **Dependencies:** FC01-C02-U001 (`subgroup`), FC01-C01-U017 (`symmetric-group`), FC01-C04-U006 (`orbit-transitive`)


- **Kind:** Construction.
- **Locator:** §4.2 “Groups Acting on Themselves by Left Multiplication—Cayley's Theorem”; printed pp. 118–121 (section span); extraction L4824.
- **Statement/data:** For H≤G, G acts on the set of left cosets G/H by left multiplication g·(xH)=(gx)H.
- **Dependencies:** FC01-C03-U005 (`left-right-cosets`), FC01-C01-U041 (`group-action`)


- **Kind:** Theorem 3.
- **Locator:** §4.2 “Groups Acting on Themselves by Left Multiplication—Cayley's Theorem”; printed pp. 118–121 (section span); extraction L4862.
- **Statement/data:** For the left action of G on cosets of H: the action is transitive; the stabilizer of H is H; the kernel is ⋂_{x∈G}xHx^{-1}, the largest normal subgroup of G contained in H.
- **Dependencies:** FC01-C04-U009 (`coset-left-action`), FC01-C04-U006 (`orbit-transitive`), FC01-C02-U009 (`stabilizer`), FC01-C02-U007 (`conjugate-subset`)


- **Kind:** Corollary 4 (Cayley).
- **Locator:** §4.2 “Groups Acting on Themselves by Left Multiplication—Cayley's Theorem”; printed pp. 118–121 (section span); extraction L4886.
- **Statement/data:** Every group is isomorphic to a subgroup of a symmetric group; if |G|=n then G embeds in S_n.
- **Dependencies:** FC01-C04-U010 (`coset-action-core-theorem`), FC01-C01-U048 (`left-regular-action`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Definition.
- **Locator:** §4.2 “Groups Acting on Themselves by Left Multiplication—Cayley's Theorem”; printed pp. 118–121 (section span); extraction L4890.
- **Statement/data:** The permutation representation afforded by left multiplication of G on itself is the left regular representation.
- **Dependencies:** FC01-C01-U048 (`left-regular-action`), FC01-C04-U004 (`permutation-representation`)


- **Kind:** Corollary 5.
- **Locator:** §4.2 “Groups Acting on Themselves by Left Multiplication—Cayley's Theorem”; printed pp. 118–121 (section span); extraction L4896.
- **Statement/data:** If finite G has order n and p is the least prime divisor of n, every subgroup of index p is normal.
- **Dependencies:** FC01-C04-U010 (`coset-action-core-theorem`), FC01-C03-U018 (`lagrange`)


- **Kind:** Definition.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L4978.
- **Statement/data:** a,b∈G are conjugate if b=gag^{-1} for some g; the conjugacy classes are the orbits for conjugation of G on itself.
- **Dependencies:** FC01-C02-U007 (`conjugate-subset`), FC01-C04-U006 (`orbit-transitive`)


- **Kind:** Definition.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L4996.
- **Statement/data:** Subsets S,T⊆G are conjugate if T=gSg^{-1} for some g; equivalently they lie in the same orbit for conjugation on subsets.
- **Dependencies:** FC01-C02-U007 (`conjugate-subset`), FC01-C04-U006 (`orbit-transitive`)


- **Kind:** Proposition 6.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5006.
- **Statement/data:** The number of conjugates of S⊆G is |G:N_G(S)|. In particular, the conjugacy class of s has size |G:C_G(s)|.
- **Dependencies:** FC01-C04-U005 (`orbit-equivalence-orbit-stabilizer`), FC01-C02-U008 (`normalizer`), FC01-C02-U004 (`centralizer`)


- **Kind:** Theorem 7 (Class Equation).
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5012.
- **Statement/data:** If finite G has representatives g_1,…,g_r for the noncentral conjugacy classes, then |G|=|Z(G)|+Σ_i |G:C_G(g_i)|.
- **Dependencies:** FC01-C04-U016 (`number-conjugates-index-normalizer`), FC01-C02-U006 (`center`)


- **Kind:** Theorem 8.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5064.
- **Statement/data:** Every nontrivial finite p-group P has nontrivial center Z(P).
- **Dependencies:** FC01-C04-U017 (`class-equation`), FC01-C02-U006 (`center`)


- **Kind:** Corollary 9.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5074.
- **Statement/data:** Every group of order p^2 is abelian; up to isomorphism it is Z_{p^2} or Z_p×Z_p.
- **Dependencies:** FC01-C04-U018 (`p-group-nontrivial-center`), FC01-C02-U020 (`cyclic-groups-classified-by-order`), FC01-C01-U004 (`product-group-two`)


- **Kind:** Proposition 10.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5082.
- **Statement/data:** If σ∈S_n has a disjoint-cycle decomposition, then τστ^{-1} is obtained by applying τ to every entry in every cycle.
- **Dependencies:** FC01-C01-U024 (`cycle-decomposition-uniqueness`), FC01-C04-U014 (`conjugate-elements-classes`)


- **Kind:** Definition.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5112.
- **Statement/data:** The cycle type of σ∈S_n is the nondecreasing list of lengths of all disjoint cycles, including 1-cycles. A partition of n is a nondecreasing sequence of positive integers summing to n.
- **Dependencies:** FC01-C01-U024 (`cycle-decomposition-uniqueness`), FC01-C00-U016 (`partition`)


- **Kind:** Proposition 11.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5120.
- **Statement/data:** Two elements of S_n are conjugate iff they have the same cycle type; hence conjugacy classes of S_n are indexed by partitions of n.
- **Dependencies:** FC01-C04-U020 (`conjugation-cycle-relabeling`), FC01-C04-U021 (`cycle-type-partition`)


- **Kind:** Theorem 12.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5182.
- **Statement/data:** A_5 is simple.
- **Dependencies:** FC01-C03-U053 (`alternating-group`), FC01-C03-U039 (`simple-group`), FC01-C04-U017 (`class-equation`)


- **Kind:** Definition/convention.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5216.
- **Statement/data:** A right action A×G→A satisfies (a·g_1)·g_2=a·(g_1g_2) and a·1=a. Conjugation is often written a^g=g^{-1}ag and S^g=g^{-1}Sg.
- **Dependencies:** FC01-C01-U043 (`right-action`), FC01-C02-U007 (`conjugate-subset`)


- **Kind:** Convention/notation.
- **Locator:** §4.3 “Groups Acting on Themselves by Conjugation—The Class Equation”; printed pp. 122–132 (section span); extraction L5220.
- **Statement/data:** Conjugation may be written as a right action: a^g=g^{-1}ag for elements and S^g=g^{-1}Sg for subsets.
- **Dependencies:** FC01-C04-U024 (`right-action-revisited`), FC01-C02-U007 (`conjugate-subset`)


- **Kind:** Definition.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5366.
- **Statement/data:** An automorphism of G is an isomorphism G→G; Aut(G) is the group of all automorphisms under composition.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Proposition 13.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5372.
- **Statement/data:** If H◁G, conjugation by each g∈G restricts to an automorphism of H, defining an action/homomorphism G→Aut(H).
- **Dependencies:** FC01-C04-U026 (`automorphism`), FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Corollary 14.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5398.
- **Statement/data:** For K≤G and g∈G, K≅gKg^{-1}; conjugate elements and conjugate subgroups have the same order.
- **Dependencies:** FC01-C04-U027 (`conjugation-on-normal-subgroup`), FC01-C04-U015 (`conjugate-subsets`)


- **Kind:** Corollary 15.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5402.
- **Statement/data:** For H≤G, N_G(H)/C_G(H) is isomorphic to a subgroup of Aut(H). In particular, G/Z(G) embeds in Aut(G).
- **Dependencies:** FC01-C04-U027 (`conjugation-on-normal-subgroup`), FC01-C03-U032 (`first-isomorphism-group`), FC01-C02-U008 (`normalizer`), FC01-C02-U004 (`centralizer`), FC01-C02-U006 (`center`)


- **Kind:** Definition.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5406.
- **Statement/data:** Conjugation by g∈G is an inner automorphism; Inn(G)≤Aut(G) is the subgroup of all inner automorphisms.
- **Dependencies:** FC01-C04-U026 (`automorphism`), FC01-C02-U007 (`conjugate-subset`)


- **Kind:** Definition.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5426.
- **Statement/data:** H≤G is characteristic, written H char G, if σ(H)=H for every σ∈Aut(G).
- **Dependencies:** FC01-C04-U026 (`automorphism`), FC01-C02-U001 (`subgroup`)


- **Kind:** Recorded propositions.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5428.
- **Statement/data:** Characteristic subgroups are normal; a unique subgroup of a given order is characteristic; and if K char H with H◁G then K◁G.
- **Dependencies:** FC01-C04-U031 (`characteristic-subgroup`), FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Proposition 16.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5440.
- **Statement/data:** Aut(Z_n)≅(Z/nZ)^×, an abelian group of order φ(n).
- **Dependencies:** FC01-C02-U023 (`generators-of-cyclic-group`), FC01-C00-U037 (`units-Zmodn-coprime`), FC01-C00-U030 (`euler-phi`)


- **Kind:** Proposition 17.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5484.
- **Statement/data:** Records: for odd prime p, Aut(Z_{p^n}) is cyclic of order p^{n−1}(p−1); for n≥3, Aut(Z_{2^n})≅Z_2×Z_{2^{n−2}}; an elementary abelian group V of order p^n has Aut(V)≅GL_n(F_p); Aut(S_n)=Inn(S_n)≅S_n for n≠6 with outer index 2 for n=6; Aut(D_8)≅D_8 and Aut(Q_8)≅S_4.
- **Dependencies:** FC01-C04-U033 (`aut-cyclic`), FC01-C01-U028 (`general-linear-group`), FC01-C04-U030 (`inner-automorphism`)


- **Kind:** Definition/comparison.
- **Locator:** §4.4 “Automorphisms”; printed pp. 133–138 (section span); extraction L5502.
- **Statement/data:** An abelian group V of order p^n with pv=0 for all v is the elementary abelian group of order p^n; it is an n-dimensional F_p-vector space. In particular V_4 is elementary abelian of order 4.
- **Dependencies:** FC01-C02-U036 (`Klein-four-group`), FC01-C04-U034 (`automorphism-known-groups`)


- **Kind:** Definition/notation.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5616.
- **Statement/data:** A p-group has order p^α (α≥1); a p-subgroup is a subgroup that is a p-group. If |G|=p^αm with p∤m, a subgroup of order p^α is a Sylow p-subgroup. Syl_p(G) denotes the set and n_p(G) its cardinality.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Theorem 18 (Sylow).
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5624.
- **Statement/data:** For |G|=p^αm with p∤m: Sylow p-subgroups exist; every p-subgroup lies in a conjugate of a Sylow p-subgroup, so all Sylow p-subgroups are conjugate; and n_p≡1 (mod p), with n_p=|G:N_G(P)| dividing m.
- **Dependencies:** FC01-C04-U036 (`p-group-p-subgroup-sylow`), FC01-C03-U025 (`sylow-existence`), FC01-C04-U016 (`number-conjugates-index-normalizer`)


- **Kind:** Lemma 19.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5640.
- **Statement/data:** If P∈Syl_p(G) and Q is any p-subgroup, then Q∩N_G(P)=Q∩P.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C02-U008 (`normalizer`)


- **Kind:** Corollary 20.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5732.
- **Statement/data:** For P∈Syl_p(G), equivalent: P is the unique Sylow p-subgroup; P◁G; P char G; and every subgroup generated by elements of p-power order is a p-group.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C04-U031 (`characteristic-subgroup`), FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Reusable named comparison.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5810.
- **Statement/data:** If |G|=p^2q for distinct primes p,q, then G has a normal Sylow subgroup; the only exceptional counting branch reduces to |G|=12.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C04-U039 (`unique-sylow-equivalences`)


- **Kind:** Proposition 21.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5828.
- **Statement/data:** If |G|=60 and G has more than one Sylow 5-subgroup, then G is simple.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C03-U039 (`simple-group`)


- **Kind:** Corollary 22.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5836.
- **Statement/data:** A_5 is simple (second proof, via its distinct Sylow 5-subgroups).
- **Dependencies:** FC01-C04-U041 (`order60-many-sylow5-simple`), FC01-C03-U053 (`alternating-group`)


- **Kind:** Proposition 23.
- **Locator:** §4.5 “Sylow's Theorems”; printed pp. 139–148 (section span); extraction L5842.
- **Statement/data:** Every simple group of order 60 is isomorphic to A_5.
- **Dependencies:** FC01-C03-U039 (`simple-group`), FC01-C04-U042 (`A5-simple-sylow`), FC01-C04-U010 (`coset-action-core-theorem`)


- **Kind:** Theorem 24.
- **Locator:** §4.6 “The Simplicity of A_n”; printed pp. 149–151 (section span); extraction L5986.
- **Statement/data:** A_n is simple for every n≥5.
- **Dependencies:** FC01-C03-U053 (`alternating-group`), FC01-C03-U039 (`simple-group`), FC01-C04-U023 (`A5-simple-first-proof`)


Units: 46.


- **Kind:** Definition/construction.
- **Locator:** §5.1 “Direct Products”; printed pp. 152–157 (section span); extraction L6088.
- **Statement/data:** For groups G_i, the finite direct product consists of tuples and the countable direct product of sequences, with multiplication defined componentwise.
- **Dependencies:** FC01-C01-U004 (`product-group-two`), FC01-C01-U002 (`group`)


- **Kind:** Convention.
- **Locator:** §5.1 “Direct Products”; printed pp. 152–157 (section span); extraction L6102.
- **Statement/data:** Even when direct-product factors are naturally written with different operations, abstract direct products are written multiplicatively, with coordinatewise multiplication.
- **Dependencies:** FC01-C05-U001 (`direct-product-finite-countable`)


- **Kind:** Proposition 1.
- **Locator:** §5.1 “Direct Products”; printed pp. 152–157 (section span); extraction L6122.
- **Statement/data:** A finite direct product G_1×⋯×G_n is a group of order ∏|G_i| (infinite if any factor is infinite).
- **Dependencies:** FC01-C05-U001 (`direct-product-finite-countable`)


- **Kind:** Proposition 2.
- **Locator:** §5.1 “Direct Products”; printed pp. 152–157 (section span); extraction L6140.
- **Statement/data:** Each factor G_i embeds as the i-th coordinate subgroup of G=∏G_j; quotienting by that copy removes the factor. The coordinate projection π_i:G→G_i is surjective with kernel the product of the remaining factors.
- **Dependencies:** FC01-C05-U003 (`direct-product-order`), FC01-C03-U032 (`first-isomorphism-group`)


- **Kind:** Definition.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6376.
- **Statement/data:** G is finitely generated if G=⟨A⟩ for some finite subset A.
- **Dependencies:** FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Definition/notation.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6380.
- **Statement/data:** Z^r is the direct product of r copies of Z, with Z^0=1; it is called the free abelian group of rank r.
- **Dependencies:** FC01-C05-U001 (`direct-product-finite-countable`), FC01-C02-U020 (`cyclic-groups-classified-by-order`)


- **Kind:** Theorem 3 (Fundamental Theorem of Finitely Generated Abelian Groups).
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6384.
- **Statement/data:** Every finitely generated abelian G has a unique decomposition G≅Z^r×Z_{n_1}×⋯×Z_{n_s} with r≥0, n_j≥2, and n_{i+1}|n_i. The parameters r,s,n_i are uniquely determined.
- **Dependencies:** FC01-C05-U005 (`finitely-generated-group`), FC01-C05-U006 (`free-abelian-Zr`), FC01-C02-U021 (`Zn-cyclic-notation`), FC01-C05-U001 (`direct-product-finite-countable`)


- **Kind:** Definition.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6402.
- **Statement/data:** In Theorem 3, r is the free rank/Betti number, the n_i are invariant factors, and the displayed decomposition is the invariant-factor decomposition.
- **Dependencies:** FC01-C05-U007 (`fundamental-theorem-fg-abelian`)


- **Kind:** Definition.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6406.
- **Statement/data:** A finite abelian group with invariant factors (n_1,…,n_s) is said to be of type (n_1,…,n_s).
- **Dependencies:** FC01-C05-U008 (`free-rank-invariant-factors`)


- **Kind:** Construction/comparison.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6408.
- **Statement/data:** Isomorphism classes of finite abelian groups of order n correspond bijectively to lists n_1,…,n_s with n_j≥2, n_{i+1}|n_i, and ∏n_i=n.
- **Dependencies:** FC01-C05-U007 (`fundamental-theorem-fg-abelian`), FC01-C05-U009 (`finite-abelian-type`)


- **Kind:** Corollary 4.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6424.
- **Statement/data:** If n is squarefree, the only abelian group of order n up to isomorphism is Z_n.
- **Dependencies:** FC01-C05-U010 (`finite-abelian-classification-sequences`)


- **Kind:** Theorem 5 (Primary/Elementary-Divisor Decomposition).
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6454.
- **Statement/data:** If finite abelian |G|=∏p_i^{α_i}, then G≅∏A_i with |A_i|=p_i^{α_i}; each A_i uniquely decomposes as ∏*j Z*{p_i^{β_j}} with β_1≥⋯≥β_t≥1 and Σβ_j=α_i; all these data are unique.
- **Dependencies:** FC01-C05-U007 (`fundamental-theorem-fg-abelian`), FC01-C05-U001 (`direct-product-finite-countable`), FC01-C00-U028 (`fundamental-theorem-arithmetic`)


- **Kind:** Definition.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6474.
- **Statement/data:** The prime powers p^{β_j} in Theorem 5 are the elementary divisors of G; the resulting expression is the elementary-divisor decomposition.
- **Dependencies:** FC01-C05-U012 (`elementary-divisor-decomposition`)


- **Kind:** Corollary/comparison.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6488.
- **Statement/data:** Isomorphism classes of abelian groups of order p^α are indexed by partitions of α.
- **Dependencies:** FC01-C05-U012 (`elementary-divisor-decomposition`), FC01-C04-U021 (`cycle-type-partition`)


- **Kind:** Proposition 6.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6558.
- **Statement/data:** Z_m×Z_n≅Z_{mn} iff (m,n)=1. Hence if n=∏p_i^{α_i}, then Z_n≅∏Z_{p_i^{α_i}}.
- **Dependencies:** FC01-C05-U001 (`direct-product-finite-countable`), FC01-C02-U021 (`Zn-cyclic-notation`), FC01-C00-U021 (`relatively-prime`)


- **Kind:** Construction.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6574.
- **Statement/data:** Elementary divisors are obtained from invariant factors by prime-power factorization; invariant factors are recovered by aligning prime-power factors by decreasing exponent and multiplying across primes.
- **Dependencies:** FC01-C05-U015 (`coprime-cyclic-product`), FC01-C05-U013 (`elementary-divisors`), FC01-C05-U008 (`free-rank-invariant-factors`)


- **Kind:** Definition.
- **Locator:** §5.2 “The Fundamental Theorem of Finitely Generated Abelian Groups”; printed pp. 158–166 (section span); extraction L6666.
- **Statement/data:** For finite abelian G of type (n_1,…,n_t), t is its rank. For any group G, the exponent is the least n>0 with x^n=1 for all x∈G, or ∞ if none exists.
- **Dependencies:** FC01-C05-U009 (`finite-abelian-type`), FC01-C01-U008 (`element-order`)


- **Kind:** Reusable classification table.
- **Locator:** §5.3 “Table of Groups of Small Order”; printed pp. 167–168 (section span); extraction L6760.
- **Statement/data:** The section tabulates isomorphism types of groups of orders 7 through 20 where established, separating abelian and nonabelian types.
- **Dependencies:** FC01-C01-U033 (`group-isomorphism`), FC01-C05-U007 (`fundamental-theorem-fg-abelian`)


- **Kind:** Reusable named presentation.
- **Locator:** §5.3 “Table of Groups of Small Order”; printed pp. 167–168 (section span); extraction L6764.
- **Statement/data:** The nonabelian group Z_3⋊Z_4 of order 12 is presented as ⟨x,y | x^4=y^3=1, x^{-1}yx=y^{-1}⟩.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`), FC01-C01-U002 (`group`)


- **Kind:** Reusable named presentation.
- **Locator:** §5.3 “Table of Groups of Small Order”; printed pp. 167–168 (section span); extraction L6772.
- **Statement/data:** (Z_3×Z_3)⋊Z_2 is presented with commuting y,z of order 3 and an involution x inverting both.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`), FC01-C01-U004 (`product-group-two`)


- **Kind:** Reusable named presentation.
- **Locator:** §5.3 “Table of Groups of Small Order”; printed pp. 167–168 (section span); extraction L6780.
- **Statement/data:** A nonabelian Z_5⋊Z_4 of order 20 is presented with a normal Z_5 inverted by a generator of Z_4.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`)


- **Kind:** Reusable named example.
- **Locator:** §5.3 “Table of Groups of Small Order”; printed pp. 167–168 (section span); extraction L6802.
- **Statement/data:** F_{20}=⟨x,y | x^4=y^5=1, xyx^{-1}=y^2⟩≅⟨(2 3 5 4),(1 2 3 4 5)⟩≤S_5; it is called the Frobenius group of order 20.
- **Dependencies:** FC01-C01-U014 (`presentation-informal`), FC01-C01-U017 (`symmetric-group`)


- **Kind:** Definition/notation.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6816.
- **Statement/data:** [x,y]=x^{-1}y^{-1}xy is the commutator; [A,B]=⟨[a,b]:a∈A,b∈B⟩; G′=[G,G] is the commutator subgroup.
- **Dependencies:** FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Proposition 7.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6826.
- **Statement/data:** xy=yx[x,y]; H◁G iff [H,G]≤H; automorphisms preserve commutators, so G′ char G and G/G′ is abelian; G/G′ is the largest abelian quotient; every homomorphism from G to an abelian group kills G′ and factors through G/G′.
- **Dependencies:** FC01-C05-U023 (`commutator-subgroup`), FC01-C04-U031 (`characteristic-subgroup`), FC01-C03-U037 (`factor-through-quotient`)


- **Kind:** Construction/terminology.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6832.
- **Statement/data:** G/G′ is the canonical maximal abelian quotient (the abelianization in standard terminology; the source states its universal property explicitly).
- **Dependencies:** FC01-C05-U024 (`commutator-properties`)


- **Kind:** Reusable comparisons.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6884.
- **Statement/data:** G is abelian iff G′=1; D_8′=Z(D_8), Q_8′=Z(Q_8); and D_{2n}′=⟨r^2⟩, of index 2 for n odd and 4 for n even.
- **Dependencies:** FC01-C05-U024 (`commutator-properties`), FC01-C01-U010 (`dihedral-group`), FC01-C01-U031 (`quaternion-group`), FC01-C02-U006 (`center`)


- **Kind:** Proposition 8.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6894.
- **Statement/data:** Each element of HK has exactly |H∩K| representations hk with h∈H,k∈K; in particular representation is unique if H∩K=1.
- **Dependencies:** FC01-C03-U026 (`subgroup-set-product`), FC01-C03-U027 (`subgroup-product-cardinality`)


- **Kind:** Theorem 9.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6900.
- **Statement/data:** If H,K◁G and H∩K=1, then HK≅H×K.
- **Dependencies:** FC01-C05-U027 (`HK-unique-factor-count`), FC01-C03-U029 (`normalizer-product-corollary`), FC01-C05-U001 (`direct-product-finite-countable`)


- **Kind:** Definition.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6930.
- **Statement/data:** If H,K◁G with H∩K=1, HK is their internal direct product; H×K is the corresponding external direct product.
- **Dependencies:** FC01-C05-U028 (`internal-direct-product-recognition`)


- **Kind:** Reusable comparison.
- **Locator:** §5.4 “Recognizing Direct Products”; printed pp. 169–174 (section span); extraction L6936.
- **Statement/data:** For odd n, D_{4n}≅D_{2n}×Z_2, by identifying commuting normal subgroups with trivial intersection.
- **Dependencies:** FC01-C05-U028 (`internal-direct-product-recognition`), FC01-C01-U010 (`dihedral-group`)


- **Kind:** Theorem 10.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7074.
- **Statement/data:** Given φ:K→Aut(H), let K act on H via φ and define (h_1,k_1)(h_2,k_2)=(h_1(k_1·h_2),k_1k_2). This makes H×K into a group of order |H||K| containing canonical copies of H◁G and K with H∩K=1, and khk^{-1}=φ(k)(h).
- **Dependencies:** FC01-C04-U026 (`automorphism`), FC01-C04-U003 (`actions-homs-bijection`)


- **Kind:** Definition/notation.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7134.
- **Statement/data:** The group of Theorem 10 is the semidirect product H⋊_φK (or H⋊K when φ is understood).
- **Dependencies:** FC01-C05-U031 (`semidirect-product-construction`)


- **Kind:** Proposition 11.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7138.
- **Statement/data:** For H⋊_φK, equivalent: the identity set map H⋊K→H×K is a group homomorphism/isomorphism; φ is trivial; and K◁H⋊K.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C05-U028 (`internal-direct-product-recognition`)


- **Kind:** Reusable named construction.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7168.
- **Statement/data:** For abelian H and K=Z_2 acting by inversion, H⋊K has an index-2 copy of H. For H=Z_n this is D_{2n}; for H=Z it is the infinite dihedral group D_∞.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C01-U010 (`dihedral-group`)


- **Kind:** Reusable named construction.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7178.
- **Statement/data:** The quotient construction in Example 3 produces the generalized quaternion group Q_{2^{n+1}}, with presentation ⟨h,x | h^{2^n}=x^4=1, x^{-1}hx=h^{-1}, h^{2^{n-1}}=x^2⟩.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C01-U031 (`quaternion-group`), FC01-C01-U014 (`presentation-informal`)


- **Kind:** Definition/construction.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7186.
- **Statement/data:** Hol(H)=H⋊Aut(H) for the identity action of Aut(H) on H. The section records Hol(V_4)≅S_4 and N_{S_n}(π(G))≅Hol(G) for the left regular embedding π.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C04-U026 (`automorphism`), FC01-C04-U012 (`left-regular-representation`)


- **Kind:** Reusable construction.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7198.
- **Statement/data:** For primes p<q with p|(q−1), a nontrivial homomorphism Z_p→Aut(Z_q) yields a nonabelian semidirect product Z_q⋊Z_p of order pq; for p=2 it is D_{2q}.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C04-U033 (`aut-cyclic`), FC01-C03-U024 (`cauchy`)


- **Kind:** Reusable named example.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7200.
- **Statement/data:** For odd prime p, (Z_p×Z_p)⋊Z_p with action x·a=ab, x·b=b is the Heisenberg group over Z/pZ, with the displayed order-p^3 presentation.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C04-U035 (`elementary-abelian-group`), FC01-C01-U014 (`presentation-informal`)


- **Kind:** Reusable comparison.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7220.
- **Statement/data:** For odd p, Z_{p^2}⋊Z_p with x·y=y^{1+p} is a nonabelian group of order p^3 containing an element of order p^2; it is not isomorphic to the Heisenberg example.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C05-U038 (`heisenberg-mod-p-group`)


- **Kind:** Reusable named comparison.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7234.
- **Statement/data:** The displayed semidirect product (Q_8×V_4)⋊Z_3 has order 96 and contains an element of G′ that is not a single commutator [x,y].
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C05-U023 (`commutator-subgroup`), FC01-C01-U031 (`quaternion-group`), FC01-C02-U036 (`Klein-four-group`)


- **Kind:** Theorem 12.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7250.
- **Statement/data:** If H◁G, K≤G, and H∩K=1, then with φ:K→Aut(H) induced by conjugation, HK≅H⋊_φK. If moreover G=HK, then G is that semidirect product.
- **Dependencies:** FC01-C05-U032 (`semidirect-product`), FC01-C05-U027 (`HK-unique-factor-count`), FC01-C04-U027 (`conjugation-on-normal-subgroup`)


- **Kind:** Definition.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7260.
- **Statement/data:** K≤G is a complement to H≤G if G=HK and H∩K=1.
- **Dependencies:** FC01-C03-U026 (`subgroup-set-product`)


- **Kind:** Reusable classification.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7286.
- **Statement/data:** For primes p<q, every group of order pq is Z_q⋊Z_p. If p∤(q−1) it is cyclic; if p|(q−1), there is, up to isomorphism, one nonabelian semidirect product in addition to the cyclic group.
- **Dependencies:** FC01-C05-U041 (`internal-semidirect-recognition`), FC01-C05-U037 (`nonabelian-order-pq-construction`)


- **Kind:** Reusable classification.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7294.
- **Statement/data:** The section classifies groups of order 30 via Z_{15}⋊Z_2: the cyclic group Z_30 and three nontrivial actions yielding Z_5×D_6, Z_3×D_{10}, and D_{30}.
- **Dependencies:** FC01-C05-U041 (`internal-semidirect-recognition`), FC01-C04-U033 (`aut-cyclic`)


- **Kind:** Reusable classification.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7326.
- **Statement/data:** The section derives the isomorphism types of groups of order 12 from Sylow subgroups and semidirect products, recovering the familiar cyclic/direct-product and nonabelian cases including A_4 and D_{12}.
- **Dependencies:** FC01-C05-U041 (`internal-semidirect-recognition`), FC01-C04-U037 (`sylow-theorem`), FC01-C04-U019 (`groups-order-p2`)


- **Kind:** Reusable classification.
- **Locator:** §5.5 “Semidirect Products”; printed pp. 175–187 (section span); extraction L7354.
- **Statement/data:** For odd prime p, the section classifies groups of order p^3: three abelian types and two nonabelian types, represented by the Heisenberg group and Z_{p^2}⋊Z_p.
- **Dependencies:** FC01-C05-U007 (`fundamental-theorem-fg-abelian`), FC01-C05-U038 (`heisenberg-mod-p-group`), FC01-C05-U039 (`second-nonabelian-p3-group`), FC01-C05-U041 (`internal-semidirect-recognition`)


Units: 42.


- **Kind:** Definition.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7518.
- **Statement/data:** A maximal subgroup M of G is a proper subgroup with no H satisfying M<H<G.
- **Dependencies:** FC01-C02-U001 (`subgroup`)


- **Kind:** Theorem 1.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7524.
- **Statement/data:** For |P|=p^a: Z(P)≠1; every nontrivial normal H meets Z(P) nontrivially (and normal order-p subgroups are central); each p^b||H| occurs as the order of a subgroup of H normal in P; every proper H<P is properly contained in N_P(H); and every maximal subgroup has index p and is normal.
- **Dependencies:** FC01-C04-U036 (`p-group-p-subgroup-sylow`), FC01-C04-U018 (`p-group-nontrivial-center`), FC01-C06-U001 (`maximal-subgroup`), FC01-C02-U008 (`normalizer`)


- **Kind:** Definition/construction.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7566.
- **Statement/data:** Define Z_0(G)=1, Z_1(G)=Z(G), and Z_{i+1}(G)/Z_i(G)=Z(G/Z_i(G)); the chain Z_0≤Z_1≤⋯ is the upper central series.
- **Dependencies:** FC01-C02-U006 (`center`), FC01-C03-U017 (`natural-projection-group`)


- **Kind:** Definition.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7588.
- **Statement/data:** G is nilpotent if Z_c(G)=G for some c; the least such c is its nilpotence class.
- **Dependencies:** FC01-C06-U003 (`upper-central-series`)


- **Kind:** Definition/notation.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7610.
- **Statement/data:** For an ascending upper central series that does not terminate finitely, the source records its union as the hypercenter and calls G hypernilpotent when that union is G.
- **Dependencies:** FC01-C06-U003 (`upper-central-series`)


- **Kind:** Proposition 2.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7618.
- **Statement/data:** Every finite p-group of order p^a is nilpotent of class at most a−1.
- **Dependencies:** FC01-C06-U002 (`p-group-omnibus`), FC01-C06-U004 (`nilpotent-group-class`)


- **Kind:** Theorem 3.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7634.
- **Statement/data:** For finite G with Sylow P_i, equivalent: G is nilpotent; every proper H is properly contained in N_G(H); every Sylow subgroup is normal; and G≅P_1×⋯×P_s.
- **Dependencies:** FC01-C06-U004 (`nilpotent-group-class`), FC01-C04-U037 (`sylow-theorem`), FC01-C05-U028 (`internal-direct-product-recognition`)


- **Kind:** Corollary 4.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7678.
- **Statement/data:** Every finite abelian group is the direct product of its Sylow subgroups.
- **Dependencies:** FC01-C06-U007 (`finite-nilpotent-equivalences`)


- **Kind:** Proposition 5.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7682.
- **Statement/data:** If finite G has at most n solutions of x^n=1 for every positive divisor n of |G|, then G is cyclic.
- **Dependencies:** FC01-C01-U008 (`element-order`), FC01-C02-U016 (`cyclic-group`)


- **Kind:** Proposition 6 (Frattini Argument).
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7688.
- **Statement/data:** If finite G has H◁G and P is a Sylow p-subgroup of H, then G=H N_G(P), and |G:H| divides |N_G(P)|.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C02-U008 (`normalizer`), FC01-C03-U026 (`subgroup-set-product`)


- **Kind:** Proposition 7.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7700.
- **Statement/data:** A finite group is nilpotent iff every maximal subgroup is normal.
- **Dependencies:** FC01-C06-U007 (`finite-nilpotent-equivalences`), FC01-C06-U001 (`maximal-subgroup`)


- **Kind:** Definition/construction.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7724.
- **Statement/data:** Define G^0=G and G^{i+1}=[G,G^i]; this descending chain is the lower central series.
- **Dependencies:** FC01-C05-U023 (`commutator-subgroup`)


- **Kind:** Theorem 8.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7740.
- **Statement/data:** G is nilpotent iff G^n=1 for some n≥0; the nilpotence class is the least such n. If class is c, the upper and lower central series each have length c.
- **Dependencies:** FC01-C06-U004 (`nilpotent-group-class`), FC01-C06-U012 (`lower-central-series`)


- **Kind:** Definition/construction.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7778.
- **Statement/data:** Define G^{(0)}=G and G^{(i+1)}=(G^{(i)})′; this descending chain is the derived/commutator series.
- **Dependencies:** FC01-C05-U023 (`commutator-subgroup`)


- **Kind:** Theorem 9.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7796.
- **Statement/data:** G is solvable iff G^{(n)}=1 for some n≥0.
- **Dependencies:** FC01-C03-U045 (`solvable-group`), FC01-C06-U014 (`derived-series`)


- **Kind:** Definition.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7814.
- **Statement/data:** For solvable G, the least n with G^{(n)}=1 is the solvable length.
- **Dependencies:** FC01-C06-U015 (`solvable-derived-criterion`)


- **Kind:** Proposition 10.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7816.
- **Statement/data:** Subgroups of solvable groups are solvable; surjective images/quotients of solvable groups are solvable; and if N◁G with N and G/N solvable, then G is solvable.
- **Dependencies:** FC01-C06-U015 (`solvable-derived-criterion`), FC01-C01-U032 (`group-homomorphism`), FC01-C03-U017 (`natural-projection-group`)


- **Kind:** Theorem 11.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7850.
- **Statement/data:** Records: Burnside p^aq^b groups are solvable; Hall’s Sylow-complement criterion implies solvability; Feit–Thompson says every finite odd-order group is solvable; Thompson says if every 2-generated subgroup is solvable then G is solvable.
- **Dependencies:** FC01-C03-U045 (`solvable-group`), FC01-C04-U037 (`sylow-theorem`), FC01-C02-U026 (`generated-subgroup`)


- **Kind:** Definition.
- **Locator:** §6.1 “p-groups, Nilpotent Groups, and Solvable Groups”; printed pp. 188–200 (section span); extraction L7854.
- **Statement/data:** For |G|=p^a m with (p,m)=1, a subgroup of order m (index p^a) is a Sylow p-complement.
- **Dependencies:** FC01-C06-U018 (`finite-solvability-theorems`), FC01-C04-U037 (`sylow-theorem`)


- **Kind:** Proposition 12.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8105.
- **Statement/data:** If G≤S_k has no subgroup of index 2, then G≤A_k. If p is odd and P∈Syl_p(S_k), then P∈Syl_p(A_k) and |N_{A_k}(P)|=|N_{S_k}(P)|/2.
- **Dependencies:** FC01-C03-U053 (`alternating-group`), FC01-C04-U037 (`sylow-theorem`), FC01-C02-U008 (`normalizer`)


- **Kind:** Lemma 13.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8183.
- **Statement/data:** If G is finite and n_p(G) is not congruent to 1 modulo p², then distinct Sylow p-subgroups P,R exist with P∩R of index p in both P and R; hence P∩R is normal in each.
- **Dependencies:** FC01-C04-U037 (`sylow-theorem`), FC01-C06-U002 (`p-group-omnibus`)


- **Kind:** Reusable comparison.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8187.
- **Statement/data:** There is no simple group of order 1053=3^4·13: Lemma 13 forces Sylow 3-subgroups with intersection of order 3³ whose normalizer must be all of G, contradicting simplicity.
- **Dependencies:** FC01-C06-U021 (`sylow-large-intersection-lemma`), FC01-C03-U039 (`simple-group`), FC01-C02-U008 (`normalizer`)


- **Kind:** Proposition 14.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8239.
- **Statement/data:** For simple |G|=168: n_2=21,n_3=7,n_7=8; Sylow 2-subgroups are D_8 and Sylow 3,7-subgroups cyclic; G embeds in A_7 and has no subgroup of index ≤6; the conjugacy classes and maximal-subgroup classes are as listed; normalizers of the two Klein-four types are S_4.
- **Dependencies:** FC01-C03-U039 (`simple-group`), FC01-C04-U037 (`sylow-theorem`), FC01-C01-U010 (`dihedral-group`), FC01-C03-U053 (`alternating-group`), FC01-C02-U036 (`Klein-four-group`)


- **Kind:** Construction.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8257.
- **Statement/data:** For a hypothetical simple group G of order 168, call the seven conjugates U_i of one Klein four-subgroup type points and the seven conjugates W_j of the other type lines; declare U_i incident with W_j iff U_i normalizes W_j. The resulting incidence structure has three points per line and three lines per point, with unique line through two points and unique intersection point of two lines.
- **Dependencies:** FC01-C06-U023 (`simple168-structure`), FC01-C02-U036 (`Klein-four-group`), FC01-C02-U008 (`normalizer`)


- **Kind:** Definition/construction.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8273.
- **Statement/data:** The incidence structure with 7 points and 7 lines, 3 points on each line and 3 lines through each point, with unique line through two points and unique intersection of two lines, is the projective plane of order 2 (Fano plane), denoted F.
- **Dependencies:** FC01-C06-U023 (`simple168-structure`)


- **Kind:** Definition.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8278.
- **Statement/data:** An automorphism of the Fano plane is a permutation of points and lines preserving incidence.
- **Dependencies:** FC01-C06-U025 (`fano-plane`), FC01-C04-U026 (`automorphism`)


- **Kind:** Construction/comparison.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8286.
- **Statement/data:** For V=F_2^3, the 1-dimensional subspaces are the 7 points and 2-dimensional subspaces the 7 lines of the Fano plane; GL_3(F_2) acts faithfully by incidence-preserving automorphisms and has order 168.
- **Dependencies:** FC01-C06-U025 (`fano-plane`), FC01-C01-U028 (`general-linear-group`), FC01-C04-U035 (`elementary-abelian-group`)


- **Kind:** Theorem 15.
- **Locator:** §6.2 “Applications in Groups of Medium Order”; printed pp. 201–214 (section span); extraction L8294.
- **Statement/data:** Up to isomorphism there is a unique simple group of order 168, GL_3(F_2), and it is Aut(F), the automorphism group of the Fano plane.
- **Dependencies:** FC01-C06-U023 (`simple168-structure`), FC01-C06-U027 (`Fano-GL3F2-model`), FC01-C03-U039 (`simple-group`)


- **Kind:** Construction.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8412.
- **Statement/data:** Given a set S, choose a disjoint copy S^{-1} with involution s↔s^{-1}, adjoin a symbol 1 with 1^{-1}=1.
- **Dependencies:** —


- **Kind:** Definition.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8416.
- **Statement/data:** A word on S is a sequence in S∪S^{-1}∪{1} that is eventually 1, hence represents a finite string of letters and formal inverses.
- **Dependencies:** FC01-C06-U029 (`formal-inverse-alphabet`)


- **Kind:** Definition.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8422.
- **Statement/data:** A word is reduced when adjacent nonidentity letters are never inverse and, once 1 occurs, all later entries are 1. The all-1 word is the empty word.
- **Dependencies:** FC01-C06-U030 (`word-on-set`)


- **Kind:** Construction.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8428.
- **Statement/data:** F(S) is the set of reduced words on S, with S embedded by one-letter words; F(∅)={1}.
- **Dependencies:** FC01-C06-U031 (`reduced-word`)


- **Kind:** Construction.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8436.
- **Statement/data:** Multiply reduced words by concatenation followed by maximal cancellation of adjacent inverse pairs; the source gives an explicit casewise formula producing a reduced word.
- **Dependencies:** FC01-C06-U032 (`free-word-set`)


- **Kind:** Theorem 16.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8444.
- **Statement/data:** F(S) is a group under reduced-word multiplication.
- **Dependencies:** FC01-C06-U033 (`free-word-multiplication`), FC01-C01-U002 (`group`)


- **Kind:** Theorem 17.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8462.
- **Statement/data:** For every set map φ:S→G to a group G, there is a unique group homomorphism Φ:F(S)→G extending φ.
- **Dependencies:** FC01-C06-U034 (`free-word-group`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Corollary 18.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8468.
- **Statement/data:** F(S) is unique up to a unique isomorphism restricting to the identity on S.
- **Dependencies:** FC01-C06-U035 (`free-group-universal-property`), FC01-C01-U033 (`group-isomorphism`)


- **Kind:** Definition.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8472.
- **Statement/data:** F(S) is the free group on S; S is a free generating set/free basis, and |S| is the rank. A group is free if it is F(S) for some S.
- **Dependencies:** FC01-C06-U036 (`free-group-uniqueness`)


- **Kind:** Theorem 19 (Schreier).
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8476.
- **Statement/data:** Every subgroup of a free group is free.
- **Dependencies:** FC01-C06-U037 (`free-group-basis-rank`), FC01-C02-U001 (`subgroup`)


- **Kind:** Definition.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8484.
- **Statement/data:** If S⊆G generates G and π:F(S)→G extends the identity on S, a presentation (S,R) has R⊆F(S) whose normal closure is ker π. S are generators and R relations; G is finitely presented when S,R may both be finite.
- **Dependencies:** FC01-C06-U035 (`free-group-universal-property`), FC01-C02-U026 (`generated-subgroup`), FC01-C03-U014 (`conjugate-element-subgroup-normal`)


- **Kind:** Convention/notation.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8490.
- **Statement/data:** For finite S={s_i},R={w_j}, write G=⟨s_1,…,s_n | w_1=⋯=w_k=1⟩; a relation w_1w_2^{-1}=1 may be written w_1=w_2.
- **Dependencies:** FC01-C06-U039 (`presentation-rigorous`)


- **Kind:** Reusable comparison.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8500.
- **Statement/data:** Every finite group is finitely presented: take S=G and relations recording its multiplication table.
- **Dependencies:** FC01-C06-U039 (`presentation-rigorous`), FC01-C01-U009 (`group-table`)


- **Kind:** Construction criterion.
- **Locator:** §6.3 “A Word on Free Groups”; printed pp. 215–221 (section span); extraction L8502.
- **Statement/data:** For finite G, a proposed finite presentation on generators S is valid if the relations hold in G and the presented quotient has order at most |G|; the induced surjection then has equal finite order and is an isomorphism.
- **Dependencies:** FC01-C06-U039 (`presentation-rigorous`), FC01-C01-U033 (`group-isomorphism`)


Units: 95.


- **Kind:** Definition.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8624.
- **Statement/data:** A ring R is a set with addition and multiplication such that (R,+) is an abelian group, multiplication is associative, and both distributive laws hold. R is commutative if multiplication is commutative and has an identity if some 1 satisfies 1a=a1=a for all a.
- **Dependencies:** FC01-C01-U001 (`binary-operation`), FC01-C01-U002 (`group`)


- **Kind:** Convention/notation.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8646.
- **Statement/data:** Ring multiplication is normally written by juxtaposition; 0 denotes the additive identity and −a the additive inverse.
- **Dependencies:** FC01-C07-U001 (`ring`)


- **Kind:** Definition.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8664.
- **Statement/data:** A ring with identity 1≠0 is a division ring (skew field) if every nonzero element has a two-sided multiplicative inverse; a commutative division ring is a field.
- **Dependencies:** FC01-C07-U001 (`ring`)


- **Kind:** Reusable named example.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8670.
- **Statement/data:** Giving an abelian group zero multiplication ab=0 produces a trivial ring; for the one-element group this is the zero ring, denoted 0, the unique ring with 1=0.
- **Dependencies:** FC01-C07-U001 (`ring`)


- **Kind:** Reusable named construction.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8680.
- **Statement/data:** The real Hamilton quaternions H={a+bi+cj+dk:a,b,c,d∈R}, with componentwise addition and multiplication determined by i²=j²=k²=−1, ij=−ji=k, jk=−kj=i, ki=−ik=j, form a noncommutative division ring. The inverse of nonzero a+bi+cj+dk is (a−bi−cj−dk)/(a²+b²+c²+d²).
- **Dependencies:** FC01-C07-U003 (`division-ring-field`), FC01-C01-U031 (`quaternion-group`)


- **Kind:** Reusable construction.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8706.
- **Statement/data:** For nonempty X and ring A, all functions X→A form a ring under pointwise addition and multiplication; it is commutative iff A is and has an identity iff A does.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C00-U005 (`function-conventions`)


- **Kind:** Definition/example.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8712.
- **Statement/data:** A function f:R→R has compact support in the source’s elementary sense if f vanishes outside some bounded interval [a,b]. Such functions, and the continuous ones among them, form commutative rings without identity.
- **Dependencies:** FC01-C07-U006 (`function-ring`)


- **Kind:** Proposition 1.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8716.
- **Statement/data:** In every ring: 0a=a0=0; (−a)b=a(−b)=−ab; (−a)(−b)=ab. If R has an identity, it is unique and −a=(−1)a.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U002 (`ring-notation`)


- **Kind:** Definition.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8732.
- **Statement/data:** A nonzero a∈R is a zero divisor if some nonzero b has ab=0 or ba=0. If R has 1≠0, u∈R is a unit if uv=vu=1 for some v; R^× denotes the group of units.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Reusable comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8748.
- **Statement/data:** In Z/nZ, a residue class is a unit iff represented by an integer coprime to n; every nonzero nonunit is a zero divisor. Consequently Z/nZ is a field iff n is prime.
- **Dependencies:** FC01-C00-U037 (`units-Zmodn-coprime`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Reusable named construction.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8768.
- **Statement/data:** For nonsquare D∈Q, Q(√D)={a+b√D:a,b∈Q} is a field; (a+b√D)^{-1}=(a−b√D)/(a²−Db²) for nonzero a+b√D.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`)


- **Kind:** Definition/comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8776.
- **Statement/data:** Writing a nonsquare rational D=f²D′ with D′ a unique squarefree integer, D′ is the squarefree part and Q(√D)=Q(√D′).
- **Dependencies:** FC01-C07-U011 (`quadratic-field`), FC01-C00-U028 (`fundamental-theorem-arithmetic`)


- **Kind:** Definition.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8780.
- **Statement/data:** An integral domain is a commutative ring with identity 1≠0 having no zero divisors.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U009 (`zero-divisor-unit`)


- **Kind:** Proposition 2.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8784.
- **Statement/data:** If a is not a zero divisor and ab=ac, then a=0 or b=c. Hence cancellation by nonzero elements holds in an integral domain.
- **Dependencies:** FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U013 (`integral-domain`)


- **Kind:** Corollary 3.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8788.
- **Statement/data:** Every finite integral domain is a field.
- **Dependencies:** FC01-C07-U014 (`domain-cancellation`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Recorded theorem (Wedderburn).
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8792.
- **Statement/data:** Every finite division ring is commutative, hence is a field.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`)


- **Kind:** Definition/criterion.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8798.
- **Statement/data:** A subring of R is an additive subgroup closed under multiplication. Equivalently, a nonempty subset closed under subtraction and multiplication is a subring.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C02-U003 (`subgroup-criterion`)


- **Kind:** Reusable named example.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8812.
- **Statement/data:** The integral quaternions Z+Zi+Zj+Zk form a subring of the real and rational Hamilton quaternion division rings; this subring is not itself a division ring.
- **Dependencies:** FC01-C07-U005 (`hamilton-quaternions-ring`), FC01-C07-U017 (`subring`)


- **Kind:** Recorded comparison/theorem.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8814.
- **Statement/data:** A unital subring of a field is an integral domain; conversely, every integral domain embeds in a field (constructed in §7.5 as its field of fractions).
- **Dependencies:** FC01-C07-U017 (`subring`), FC01-C07-U013 (`integral-domain`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Reusable named construction.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8816.
- **Statement/data:** For squarefree D, define O=O_{Q(√D)}=Z[ω]={a+bω:a,b∈Z}, where ω=√D for D≡2,3 (mod 4) and ω=(1+√D)/2 for D≡1 (mod 4). This is the ring of integers in Q(√D). For D=−1 it is the Gaussian integer ring Z[i].
- **Dependencies:** FC01-C07-U011 (`quadratic-field`), FC01-C07-U017 (`subring`), FC01-C07-U012 (`squarefree-part`)


- **Kind:** Definition/construction.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8842.
- **Statement/data:** For Q(√D), the field norm is N(a+b√D)=(a+b√D)(a−b√D)=a²−Db². It is multiplicative; on O it is integer-valued, with the displayed formula in the integral basis 1,ω.
- **Dependencies:** FC01-C07-U011 (`quadratic-field`), FC01-C07-U020 (`quadratic-integer-ring`)


- **Kind:** Proposition/comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8864.
- **Statement/data:** For α∈O, α is a unit iff N(α)=±1.
- **Dependencies:** FC01-C07-U021 (`quadratic-field-norm`), FC01-C07-U009 (`zero-divisor-unit`)


- **Kind:** Reusable named comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8868.
- **Statement/data:** Solving Pell’s equation x²−Dy²=±1 is equivalent to determining units of the corresponding quadratic integer ring in the cases expressed by the source’s integral basis.
- **Dependencies:** FC01-C07-U022 (`quadratic-integer-unit-norm`)


- **Kind:** Reusable comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8870.
- **Statement/data:** The Gaussian integers have unit group {±1,±i}; for D=−3 the quadratic integer ring has six units {±1,±ρ,±ρ²}; for other D<0 in the stated family the only units are ±1.
- **Dependencies:** FC01-C07-U022 (`quadratic-integer-unit-norm`), FC01-C07-U020 (`quadratic-integer-ring`)


- **Kind:** Reusable comparison.
- **Locator:** §7.1 “Basic Definitions and Examples”; printed pp. 223–232 (section span); extraction L8872.
- **Statement/data:** For D>0 the unit group O^× is infinite; e.g. in Z[√2], ±(1+√2)^n are distinct units for n∈Z (and form the full unit group in this example, as recorded by the source).
- **Dependencies:** FC01-C07-U022 (`quadratic-integer-unit-norm`), FC01-C07-U020 (`quadratic-integer-ring`)


- **Kind:** Definition/construction.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9046.
- **Statement/data:** For a commutative ring R with identity and indeterminate x, R[x] consists of formal finite sums a_nx^n+⋯+a_0. If a_n≠0, n is the degree, a_nx^n the leading term, and a_n the leading coefficient; a polynomial is monic if its leading coefficient is 1.
- **Dependencies:** FC01-C07-U001 (`ring`)


- **Kind:** Construction.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9054.
- **Statement/data:** Polynomial addition is coefficientwise; multiplication is determined by (ax^i)(bx^j)=abx^{i+j} and distributivity, so the coefficient of x^k in a product is Σ_{i=0}^k a_i b_{k−i}. These operations make R[x] a ring.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U001 (`ring`)


- **Kind:** Construction/comparison.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9068.
- **Statement/data:** R embeds in R[x] as constant polynomials; for commutative R with identity, R[x] is commutative with the same identity.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U017 (`subring`)


- **Kind:** Proposition 4.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9092.
- **Statement/data:** If R is an integral domain and p,q∈R[x] are nonzero, deg(pq)=deg p+deg q; the units of R[x] are exactly the units of R; and R[x] is an integral domain.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U013 (`integral-domain`), FC01-C07-U009 (`zero-divisor-unit`)


- **Kind:** Definition/construction.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9110.
- **Statement/data:** For a ring R and n≥1, M_n(R) is the ring of n×n matrices over R, with componentwise addition and multiplication (AB)*{ij}=Σ_k a*{ik}b_{kj}.
- **Dependencies:** FC01-C07-U001 (`ring`)


- **Kind:** Reusable comparison.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9112.
- **Statement/data:** If R is nonzero and n≥2, M_n(R) is noncommutative and has zero divisors, even when R is commutative.
- **Dependencies:** FC01-C07-U030 (`matrix-ring`), FC01-C07-U009 (`zero-divisor-unit`)


- **Kind:** Definition/construction.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9116.
- **Statement/data:** A scalar matrix has one a∈R on every diagonal entry and zeros elsewhere; scalar matrices form a subring isomorphic to R and are central when R is commutative. If R has 1, the units of M_n(R) form GL_n(R).
- **Dependencies:** FC01-C07-U030 (`matrix-ring`), FC01-C07-U017 (`subring`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C01-U028 (`general-linear-group`)


- **Kind:** Reusable example.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9118.
- **Statement/data:** Upper-triangular matrices over R form a subring of M_n(R).
- **Dependencies:** FC01-C07-U030 (`matrix-ring`), FC01-C07-U017 (`subring`)


- **Kind:** Definition/construction.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9122.
- **Statement/data:** For a finite group G={g_1,…,g_n} and commutative ring R with 1≠0, the group ring RG consists of formal sums Σa_i g_i. Addition is coefficientwise and multiplication is induced by (ag_i)(bg_j)=ab(g_i g_j) and distributivity.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C01-U002 (`group`)


- **Kind:** Convention/notation.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9128.
- **Statement/data:** In RG, identify a·1_G with the scalar a∈R and 1_R·g with the group element g∈G.
- **Dependencies:** FC01-C07-U034 (`group-ring`)


- **Kind:** Construction/comparison.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9136.
- **Statement/data:** The operations make RG a ring; RG is commutative iff G is abelian. R embeds as central scalar multiples of 1_G, and G embeds as a subgroup of (RG)^×.
- **Dependencies:** FC01-C07-U034 (`group-ring`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U017 (`subring`)


- **Kind:** Reusable comparison.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9150.
- **Statement/data:** If |G|>1, RG has zero divisors: for g of order m>1, (1−g)(1+g+⋯+g^{m−1})=0.
- **Dependencies:** FC01-C07-U034 (`group-ring`), FC01-C01-U008 (`element-order`), FC01-C07-U009 (`zero-divisor-unit`)


- **Kind:** Definition/notation.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9158.
- **Statement/data:** ZG is the integral group ring and QG the rational group ring; if H≤G then RH is a subring of RG.
- **Dependencies:** FC01-C07-U034 (`group-ring`), FC01-C07-U017 (`subring`)


- **Kind:** Reusable comparison.
- **Locator:** §7.2 “Examples: Polynomial Rings, Matrix Rings, and Group Rings”; printed pp. 233–238 (section span); extraction L9160.
- **Statement/data:** The real group ring RQ_8 is not the Hamilton quaternion division ring H: in RQ_8 the group element customarily denoted −1 is not the additive inverse of 1, and RQ_8 has zero divisors.
- **Dependencies:** FC01-C07-U034 (`group-ring`), FC01-C07-U005 (`hamilton-quaternions-ring`), FC01-C01-U031 (`quaternion-group`)


- **Kind:** Definition.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9254.
- **Statement/data:** A ring homomorphism φ:R→S preserves addition and multiplication. Its kernel is {r:φ(r)=0}; a bijective ring homomorphism is a ring isomorphism.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Convention.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9266.
- **Statement/data:** For rings A,B, A≅B means ring isomorphism unless stated otherwise.
- **Dependencies:** FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Reusable example.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9274.
- **Statement/data:** Evaluation at 0, Q[x]→Q, p(x)↦p(0), is a surjective ring homomorphism whose kernel is the polynomials with zero constant term.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Proposition 5.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9276.
- **Statement/data:** For a ring homomorphism φ:R→S, im φ is a subring of S; ker φ is a subring of R and is closed under left and right multiplication by arbitrary elements of R.
- **Dependencies:** FC01-C07-U040 (`ring-homomorphism`), FC01-C07-U017 (`subring`)


- **Kind:** Construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9288.
- **Statement/data:** For I=ker φ, fibers are additive cosets r+I and inherit ring operations (r+I)+(s+I)=r+s+I and (r+I)(s+I)=rs+I.
- **Dependencies:** FC01-C07-U043 (`ring-hom-image-kernel`), FC01-C03-U005 (`left-right-cosets`)


- **Kind:** Definition/terminology.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9298.
- **Statement/data:** For a ring homomorphism φ:R→S with I=ker φ, the ring of cosets R/I inherited from the fibers is called the quotient ring of R by I.
- **Dependencies:** FC01-C07-U044 (`quotient-ring-from-kernel`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Definition.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9324.
- **Statement/data:** For I⊆R and r∈R, rI={ra:a∈I}, Ir={ar:a∈I}. A left ideal is a subring with rI⊆I for all r; a right ideal analogously has Ir⊆I; an ideal/two-sided ideal is both.
- **Dependencies:** FC01-C07-U017 (`subring`)


- **Kind:** Criterion/convention.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9338.
- **Statement/data:** In a ring with identity, I is an ideal iff it is nonempty, closed under addition, and closed under multiplication by every ring element on both sides; in a commutative ring left/right/two-sided ideals coincide.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`), FC01-C07-U008 (`ring-basic-identities`)


- **Kind:** Proposition 6.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9344.
- **Statement/data:** If I is an ideal of R, the additive quotient R/I is a ring under coset addition and multiplication. Conversely, if these coset operations are well defined for an additive subgroup I, then I is an ideal.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`), FC01-C07-U044 (`quotient-ring-from-kernel`)


- **Kind:** Definition.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9352.
- **Statement/data:** For an ideal I of R, R/I with the operations of Proposition 6 is the quotient ring of R by I.
- **Dependencies:** FC01-C07-U048 (`quotient-ring-construction`)


- **Kind:** Theorem 7(1) (First Isomorphism Theorem for Rings).
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9354.
- **Statement/data:** For a ring homomorphism φ:R→S, ker φ is an ideal, im φ is a subring, and R/ker φ≅φ(R).
- **Dependencies:** FC01-C07-U043 (`ring-hom-image-kernel`), FC01-C07-U049 (`quotient-ring`)


- **Kind:** Theorem 7(2)/construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9358.
- **Statement/data:** For every ideal I◁R, r↦r+I is a surjective ring homomorphism R→R/I with kernel I, called the natural projection. Thus ideals are exactly kernels of ring homomorphisms.
- **Dependencies:** FC01-C07-U049 (`quotient-ring`), FC01-C07-U050 (`first-isomorphism-ring`)


- **Kind:** Convention/notation.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9374.
- **Statement/data:** Reduction modulo an ideal I is written r̄=r+I; then r̄+s̄=(r+s)̄ and r̄s̄=(rs)̄.
- **Dependencies:** FC01-C07-U051 (`natural-projection-ring`)


- **Kind:** Definition.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9380.
- **Statement/data:** An ideal I is proper if I≠R; {0} is the trivial ideal, denoted 0.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`)


- **Kind:** Definition/notation.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9384.
- **Statement/data:** The natural projection Z→Z/nZ is called reduction modulo n.
- **Dependencies:** FC01-C07-U051 (`natural-projection-ring`), FC01-C00-U033 (`Zmodn`)


- **Kind:** Reusable construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9402.
- **Statement/data:** For a function ring R=A^X and c∈X, evaluation E_c(f)=f(c) is a surjective ring homomorphism with kernel the functions vanishing at c; hence R/ker E_c≅A.
- **Dependencies:** FC01-C07-U006 (`function-ring`), FC01-C07-U050 (`first-isomorphism-ring`)


- **Kind:** Reusable construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9414.
- **Statement/data:** For an ideal J of R, M_n(J) is a two-sided ideal of M_n(R), the kernel of entrywise reduction M_n(R)→M_n(R/J); hence M_n(R)/M_n(J)≅M_n(R/J).
- **Dependencies:** FC01-C07-U030 (`matrix-ring`), FC01-C07-U051 (`natural-projection-ring`), FC01-C07-U050 (`first-isomorphism-ring`)


- **Kind:** Definition/construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9418.
- **Statement/data:** For finite G and commutative unital R, the augmentation map RG→R sends Σa_i g_i↦Σa_i. It is surjective; its kernel is the augmentation ideal, so RG/I≅R.
- **Dependencies:** FC01-C07-U034 (`group-ring`), FC01-C07-U040 (`ring-homomorphism`), FC01-C07-U050 (`first-isomorphism-ring`)


- **Kind:** Reusable example.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9422.
- **Statement/data:** In M_n(R), matrices supported in a fixed column form a left ideal that is not generally a right ideal; matrices supported in a fixed row analogously form a right ideal that is not generally left.
- **Dependencies:** FC01-C07-U030 (`matrix-ring`), FC01-C07-U046 (`left-right-two-sided-ideal`)


- **Kind:** Reusable construction.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9446.
- **Statement/data:** For prime p, reducing every coefficient modulo p defines a ring homomorphism Z[x]→(Z/pZ)[x].
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U054 (`reduction-mod-n`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Theorem 8 (Second/Third/Fourth Isomorphism Theorems for Rings).
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9450.
- **Statement/data:** For a subring A and ideal B, (A+B)/B≅A/(A∩B). If I⊆J are ideals, J/I is an ideal of R/I and (R/I)/(J/I)≅R/J. For ideal I, A↦A/I bijects subrings A⊇I with subrings of R/I, preserving inclusion and idealhood.
- **Dependencies:** FC01-C07-U050 (`first-isomorphism-ring`), FC01-C07-U049 (`quotient-ring`), FC01-C07-U017 (`subring`)


- **Kind:** Definition.
- **Locator:** §7.3 “Ring Homomorphisms and Quotient Rings”; printed pp. 239–250 (section span); extraction L9462.
- **Statement/data:** For ideals I,J: I+J={a+b:a∈I,b∈J}; IJ is the set of finite sums of products ab with a∈I,b∈J; I^n is the analogous n-fold product. I+J is the least ideal containing I,J and IJ⊆I∩J.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`)


- **Kind:** Definition.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9652.
- **Statement/data:** For A⊆R, (A) is the smallest ideal containing A. RA, AR, and RAR are the finite sums of terms ra, ar, and rar′ respectively. A one-element generated ideal is principal; one generated by a finite set is finitely generated.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`)


- **Kind:** Convention/notation.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9664.
- **Statement/data:** For a singleton or listed generating set, omit braces and write (a), (a_1,a_2,…) for the generated ideal.
- **Dependencies:** FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Construction.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9674.
- **Statement/data:** RA is the left ideal generated by A, AR the right ideal, and RAR the two-sided ideal generated by A. If R is commutative, RA=AR=RAR=(A).
- **Dependencies:** FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Comparison/notation.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9682.
- **Statement/data:** In a commutative ring, b∈(a) iff b=ra for some r, i.e. a divides b; equivalently b∈(a) iff (b)⊆(a).
- **Dependencies:** FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Reusable comparison.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9688.
- **Statement/data:** Every ideal of Z is principal nZ=(n)=(−n); mZ⊆nZ iff n|m, and the ideal generated by m,n equals (gcd(m,n)).
- **Dependencies:** FC01-C07-U065 (`principal-ideal-divisibility`), FC01-C00-U020 (`gcd-integers`)


- **Kind:** Reusable comparison.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9690.
- **Statement/data:** The ideal (2,x) in Z[x], consisting of integer polynomials with even constant term, is not principal.
- **Dependencies:** FC01-C07-U062 (`ideal-generated-by-subset`), FC01-C07-U029 (`polynomial-domain-properties`)


- **Kind:** Reusable construction.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9700.
- **Statement/data:** For finite G, the augmentation ideal of RG is generated by {g−1:g∈G}; if G=⟨a⟩ is cyclic, it is the principal ideal (a−1).
- **Dependencies:** FC01-C07-U057 (`augmentation-map-ideal`), FC01-C07-U062 (`ideal-generated-by-subset`), FC01-C02-U016 (`cyclic-group`)


- **Kind:** Proposition 9.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9702.
- **Statement/data:** An ideal I equals R iff it contains a unit. If R is commutative, R is a field iff its only ideals are 0 and R.
- **Dependencies:** FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U046 (`left-right-two-sided-ideal`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Corollary 10.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9718.
- **Statement/data:** Every nonzero ring homomorphism from a field to another ring is injective.
- **Dependencies:** FC01-C07-U069 (`unit-ideal-field-criterion`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Definition/comparison.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9724.
- **Statement/data:** A ring whose only two-sided ideals are 0 and itself is called simple. A division ring has only trivial left/right/two-sided ideals, while M_n(F) for n≥2 over a field is simple but not a division ring.
- **Dependencies:** FC01-C07-U046 (`left-right-two-sided-ideal`), FC01-C07-U003 (`division-ring-field`), FC01-C07-U030 (`matrix-ring`)


- **Kind:** Definition.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9728.
- **Statement/data:** An ideal M of a ring S is maximal if M≠S and the only ideals containing M are M and S.
- **Dependencies:** FC01-C07-U053 (`proper-trivial-ideal`)


- **Kind:** Proposition 11.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9732.
- **Statement/data:** In a ring with identity 1≠0, every proper ideal is contained in a maximal ideal.
- **Dependencies:** FC01-C07-U072 (`maximal-ideal`), FC01-C07-U053 (`proper-trivial-ideal`)


- **Kind:** Proposition 12.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9746.
- **Statement/data:** For commutative R, an ideal M is maximal iff R/M is a field.
- **Dependencies:** FC01-C07-U072 (`maximal-ideal`), FC01-C07-U060 (`ring-isomorphism-theorems`), FC01-C07-U069 (`unit-ideal-field-criterion`)


- **Kind:** Definition.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9764.
- **Statement/data:** For commutative R, an ideal P is prime if P≠R and ab∈P implies a∈P or b∈P.
- **Dependencies:** FC01-C07-U053 (`proper-trivial-ideal`)


- **Kind:** Proposition 13.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9770.
- **Statement/data:** For commutative R, P is prime iff R/P is an integral domain.
- **Dependencies:** FC01-C07-U075 (`prime-ideal`), FC01-C07-U049 (`quotient-ring`), FC01-C07-U013 (`integral-domain`)


- **Kind:** Corollary/comparison.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9774.
- **Statement/data:** A commutative ring with identity is an integral domain iff the zero ideal is prime.
- **Dependencies:** FC01-C07-U076 (`prime-quotient-domain`), FC01-C07-U013 (`integral-domain`)


- **Kind:** Corollary 14.
- **Locator:** §7.4 “Properties of Ideals”; printed pp. 251–259 (section span); extraction L9776.
- **Statement/data:** In a commutative ring, every maximal ideal is prime.
- **Dependencies:** FC01-C07-U074 (`maximal-quotient-field`), FC01-C07-U076 (`prime-quotient-domain`), FC01-C07-U015 (`finite-domain-field`)


- **Kind:** Theorem 15 (Ring of Fractions).
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L9994.
- **Statement/data:** Let R be commutative and D⊆R nonempty, multiplicatively closed, containing neither 0 nor zero divisors. Then there is a commutative ring Q with 1 containing R as a subring in which every d∈D is a unit; every q∈Q has form rd^{-1}. It is initial/minimal among injective embeddings of R into commutative unital rings making D invertible. If D=R−{0}, then Q is a field.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U017 (`subring`)


- **Kind:** Construction.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10002.
- **Statement/data:** For F={(r,d):r∈R,d∈D}, define (r,d)~(s,e) iff re=sd; because denominators are nonzero non-zero-divisors, this is an equivalence relation. Write the class of (r,d) as r/d.
- **Dependencies:** FC01-C07-U079 (`localization-theorem`), FC01-C00-U014 (`equivalence-relation`)


- **Kind:** Construction.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10016.
- **Statement/data:** On localization classes define a/b+c/d=(ad+bc)/(bd) and (a/b)(c/d)=ac/(bd); these are well defined and make Q a commutative ring with 1.
- **Dependencies:** FC01-C07-U080 (`localization-equivalence-classes`), FC01-C07-U001 (`ring`)


- **Kind:** Construction.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10042.
- **Statement/data:** Embed R into Q by ι(r)=rd/d for any d∈D; this is well defined and injective, so R is identified with its image. Every d∈D then has an inverse and every q is rd^{-1}.
- **Dependencies:** FC01-C07-U081 (`localization-arithmetic`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Definition/notation.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10068.
- **Statement/data:** The localization Q is the ring of fractions of D with respect to R, denoted D^{-1}R. If R is an integral domain and D=R−{0}, Q is the field of fractions/quotient field of R.
- **Dependencies:** FC01-C07-U079 (`localization-theorem`), FC01-C07-U013 (`integral-domain`)


- **Kind:** Definition.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10074.
- **Statement/data:** For A⊆F with F a field, the intersection of all subfields of F containing A is the subfield generated by A, the smallest subfield containing A.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`)


- **Kind:** Corollary 16.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10078.
- **Statement/data:** If R is an integral domain with fraction field Q and a field F contains a subring R′≅R, then the subfield of F generated by R′ is isomorphic to Q.
- **Dependencies:** FC01-C07-U083 (`ring-field-of-fractions`), FC01-C07-U084 (`subfield-generated`), FC01-C07-U041 (`ring-isomorphism-notation`)


- **Kind:** Definition/construction.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10090.
- **Statement/data:** For an integral domain R with fraction field F, the fraction field of R[x] equals the fraction field of F[x]; for a field F this field of rational functions is denoted F(x).
- **Dependencies:** FC01-C07-U083 (`ring-field-of-fractions`), FC01-C07-U029 (`polynomial-domain-properties`)


- **Kind:** Reusable construction.
- **Locator:** §7.5 “Rings of Fractions”; printed pp. 260–264 (section span); extraction L10094.
- **Statement/data:** If R is commutative with 1 and d is nonzero and not a zero divisor, R[1/d] means D^{-1}R for D={1,d,d²,…}; it is the ring obtained by adjoining an inverse of d.
- **Dependencies:** FC01-C07-U083 (`ring-field-of-fractions`), FC01-C07-U079 (`localization-theorem`)


- **Kind:** Definition/construction.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10116.
- **Statement/data:** The direct product of rings is their direct product as additive abelian groups with multiplication componentwise; e.g. (r_1,r_2)(s_1,s_2)=(r_1s_1,r_2s_2).
- **Dependencies:** FC01-C05-U001 (`direct-product-finite-countable`), FC01-C07-U001 (`ring`)


- **Kind:** Comparison.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10122.
- **Statement/data:** A map R→∏R_i is a ring homomorphism iff each coordinate map R→R_i is a ring homomorphism.
- **Dependencies:** FC01-C07-U088 (`ring-direct-product`), FC01-C07-U040 (`ring-homomorphism`)


- **Kind:** Definition.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10126.
- **Statement/data:** Ideals A,B in a commutative ring are comaximal if A+B=R.
- **Dependencies:** FC01-C07-U061 (`ideal-sum-product-power`)


- **Kind:** Construction.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10128.
- **Statement/data:** For ideals A_1,…,A_k, their product is the ideal of finite sums of products x_1⋯x_k with x_i∈A_i; for principal A_i=(a_i), the product is (a_1⋯a_k).
- **Dependencies:** FC01-C07-U061 (`ideal-sum-product-power`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Theorem 17 (Chinese Remainder Theorem).
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10130.
- **Statement/data:** For ideals A_1,…,A_k of commutative unital R, r↦(r+A_1,…,r+A_k) is a ring homomorphism with kernel ⋂A_i. If the ideals are pairwise comaximal, it is surjective and ⋂A_i=A_1⋯A_k, hence R/(A_1⋯A_k)≅∏R/A_i.
- **Dependencies:** FC01-C07-U089 (`hom-into-ring-product`), FC01-C07-U090 (`comaximal-ideals`), FC01-C07-U050 (`first-isomorphism-ring`), FC01-C07-U091 (`multiple-ideal-product`)


- **Kind:** Reusable comparison.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10152.
- **Statement/data:** For coprime m,n, Z/mnZ≅Z/mZ×Z/nZ as rings; equivalently, simultaneous congruences modulo m and n have a unique solution modulo mn.
- **Dependencies:** FC01-C07-U092 (`chinese-remainder-ring`), FC01-C00-U021 (`relatively-prime`)


- **Kind:** Construction/comparison.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10154.
- **Statement/data:** An element of a direct product of rings is a unit iff each coordinate is a unit. Thus for coprime m,n, (Z/mnZ)^×≅(Z/mZ)^××(Z/nZ)^×.
- **Dependencies:** FC01-C07-U088 (`ring-direct-product`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U093 (`CRT-coprime-integers`)


- **Kind:** Corollary 18.
- **Locator:** §7.6 “The Chinese Remainder Theorem”; printed pp. 265–269 (section span); extraction L10162.
- **Statement/data:** If n=∏p_i^{α_i}, then Z/nZ≅∏Z/p_i^{α_i}Z as rings and (Z/nZ)^×≅∏(Z/p_i^{α_i}Z)^×. Consequently φ(n)=∏φ(p_i^{α_i}) and Euler’s φ is multiplicative on coprime integers.
- **Dependencies:** FC01-C07-U092 (`chinese-remainder-ring`), FC01-C07-U094 (`units-of-ring-product`), FC01-C00-U028 (`fundamental-theorem-arithmetic`), FC01-C00-U030 (`euler-phi`)


Units: 55.


- **Kind:** Definition.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10310.
- **Statement/data:** A norm on an integral domain R is any function N:R→Z_{≥0} with N(0)=0. It is positive if N(a)>0 for every a≠0.
- **Dependencies:** FC01-C07-U013 (`integral-domain`)


- **Kind:** Definition.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10314.
- **Statement/data:** An integral domain R is Euclidean (has a Division Algorithm) if it has a norm N such that for all a,b∈R with b≠0 there are q,r∈R with a=qb+r and either r=0 or N(r)<N(b).
- **Dependencies:** FC01-C08-U001 (`norm-domain`), FC01-C07-U013 (`integral-domain`)


- **Kind:** Definition/terminology.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10320.
- **Statement/data:** In a Euclidean division a=qb+r, q is the quotient and r the remainder.
- **Dependencies:** FC01-C08-U002 (`euclidean-domain`)


- **Kind:** Construction/algorithm.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10322.
- **Statement/data:** Successively apply Euclidean division to a,b and subsequent remainders; strict decrease of nonnegative norms forces termination at a last nonzero remainder r_n.
- **Dependencies:** FC01-C08-U002 (`euclidean-domain`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10350.
- **Statement/data:** Every field is a Euclidean domain: for b≠0 take q=ab^{-1}, r=0; any norm satisfies the division condition.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`), FC01-C08-U002 (`euclidean-domain`)


- **Kind:** Reusable named example.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10352.
- **Statement/data:** Z is Euclidean for N(a)=|a|. Quotient and remainder satisfying |r|<|b| are generally not unique unless one additionally requires 0≤r<|b|.
- **Dependencies:** FC01-C08-U002 (`euclidean-domain`), FC01-C00-U023 (`integer-division-algorithm`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10356.
- **Statement/data:** For a field F, F[x] is Euclidean with norm deg p on nonzero polynomials; if R is not a field, R[x] is not Euclidean.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C08-U002 (`euclidean-domain`), FC01-C07-U003 (`division-ring-field`)


- **Kind:** Reusable named example.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10360.
- **Statement/data:** The Gaussian integers Z[i] are Euclidean for N(a+bi)=a²+b²; choosing a Gaussian-integer quotient by rounding the real and imaginary parts of α/β gives remainder γ with N(γ)≤N(β)/2.
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C07-U021 (`quadratic-field-norm`), FC01-C08-U002 (`euclidean-domain`)


- **Kind:** Definition.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10376.
- **Statement/data:** A discrete valuation on a field K is a surjective homomorphism ν:K^×→Z satisfying ν(x+y)≥min{ν(x),ν(y)} whenever x,y,x+y are nonzero.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`), FC01-C01-U032 (`group-homomorphism`)


- **Kind:** Definition/construction.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10384.
- **Statement/data:** The valuation ring of a discrete valuation ν is {x∈K^×:ν(x)≥0}∪{0}. An integral domain R is a discrete valuation ring if it is the valuation ring of a discrete valuation on its field of fractions.
- **Dependencies:** FC01-C08-U009 (`discrete-valuation`), FC01-C07-U083 (`ring-field-of-fractions`), FC01-C07-U017 (`subring`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10388.
- **Statement/data:** Every discrete valuation ring is Euclidean for N(0)=0 and N=ν on nonzero elements: if N(a)<N(b), use quotient 0 and remainder a; otherwise a/b lies in R and gives remainder 0.
- **Dependencies:** FC01-C08-U010 (`discrete-valuation-ring`), FC01-C08-U002 (`euclidean-domain`)


- **Kind:** Proposition 1.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10396.
- **Statement/data:** Every ideal of a Euclidean domain is principal. More precisely, a nonzero ideal I is generated by any nonzero d∈I of minimal norm.
- **Dependencies:** FC01-C08-U002 (`euclidean-domain`), FC01-C07-U062 (`ideal-generated-by-subset`), FC01-C00-U018 (`well-ordering-Z`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10406.
- **Statement/data:** Z[x] is not Euclidean for any norm because the ideal (2,x) is nonprincipal; Q[x] is Euclidean.
- **Dependencies:** FC01-C08-U012 (`euclidean-ideals-principal`), FC01-C07-U067 (`Zx-nonprincipal-example`), FC01-C08-U007 (`field-polynomial-euclidean`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10408.
- **Statement/data:** Z[√−5] is not Euclidean for any norm because the ideal (3,2+√−5) is nonprincipal, as shown using the quadratic field norm.
- **Dependencies:** FC01-C08-U012 (`euclidean-ideals-principal`), FC01-C07-U020 (`quadratic-integer-ring`), FC01-C07-U021 (`quadratic-field-norm`)


- **Kind:** Definition/notation.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10412.
- **Statement/data:** In a commutative ring, b divides a (b|a) if a=bx; a greatest common divisor d of nonzero a,b is a nonzero common divisor divisible by every common divisor. Write gcd(a,b), or (a,b) when context distinguishes it from the generated ideal.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U065 (`principal-ideal-divisibility`)


- **Kind:** Proposition 2.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10436.
- **Statement/data:** If nonzero a,b in a commutative ring generate a principal ideal (d), then d is a greatest common divisor of a and b.
- **Dependencies:** FC01-C08-U015 (`ring-divisibility-gcd`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Definition.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10438.
- **Statement/data:** A Bézout domain is an integral domain in which every ideal generated by two elements is principal.
- **Dependencies:** FC01-C07-U013 (`integral-domain`), FC01-C08-U016 (`gcd-principal-ideal`)


- **Kind:** Proposition 3.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10444.
- **Statement/data:** In an integral domain, generators d,d′ of the same principal ideal differ by a unit: d′=ud. In particular any two gcds of a,b are associates.
- **Dependencies:** FC01-C07-U013 (`integral-domain`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C08-U015 (`ring-divisibility-gcd`)


- **Kind:** Theorem 4.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10450.
- **Statement/data:** In a Euclidean domain, the last nonzero remainder d in the Euclidean Algorithm for nonzero a,b is a gcd; (d)=(a,b), and there exist x,y∈R with d=ax+by.
- **Dependencies:** FC01-C08-U004 (`euclidean-algorithm-general`), FC01-C08-U016 (`gcd-principal-ideal`), FC01-C08-U012 (`euclidean-ideals-principal`)


- **Kind:** Recorded theorem.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10492.
- **Statement/data:** For integers a,b, the Euclidean Algorithm uses at most five times the number of decimal digits of the smaller integer many division steps; in particular its step count is logarithmic in operand size.
- **Dependencies:** FC01-C08-U019 (`euclidean-algorithm-gcd-bezout`), FC01-C08-U006 (`integers-euclidean`)


- **Kind:** Recorded theorem/comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10494.
- **Statement/data:** If x_0,y_0 solve ax+by=N over Z and d=gcd(a,b), then all solutions are x=x_0+m(b/d), y=y_0−m(a/d), m∈Z.
- **Dependencies:** FC01-C08-U019 (`euclidean-algorithm-gcd-bezout`), FC01-C00-U020 (`gcd-integers`)


- **Kind:** Corollary/comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10506.
- **Statement/data:** The integer equation ax+by=N is solvable iff gcd(a,b) divides N.
- **Dependencies:** FC01-C08-U021 (`linear-diophantine-solutions`), FC01-C08-U019 (`euclidean-algorithm-gcd-bezout`)


- **Kind:** Definition.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10508.
- **Statement/data:** For an integral domain R let R~=R^×∪{0}. A nonunit u∈R−R~ is a universal side divisor if for every x∈R some z∈R~ satisfies u|(x−z), equivalently x=qu+z with z=0 or a unit.
- **Dependencies:** FC01-C07-U009 (`zero-divisor-unit`), FC01-C08-U015 (`ring-divisibility-gcd`)


- **Kind:** Proposition 5.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10510.
- **Statement/data:** If an integral domain R is Euclidean and not a field, then R contains a universal side divisor.
- **Dependencies:** FC01-C08-U002 (`euclidean-domain`), FC01-C08-U023 (`universal-side-divisor`)


- **Kind:** Reusable comparison.
- **Locator:** §8.1 “Euclidean Domains”; printed pp. 270–278 (section span); extraction L10516.
- **Statement/data:** R=Z[(1+√−19)/2] has no universal side divisor, hence is not Euclidean for any norm; §8.2 shows nevertheless that R is a PID.
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C08-U024 (`euclidean-has-universal-side-divisor`)


- **Kind:** Definition.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10604.
- **Statement/data:** A principal ideal domain (PID) is an integral domain in which every ideal is principal.
- **Dependencies:** FC01-C07-U013 (`integral-domain`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Corollary/comparison.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10606.
- **Statement/data:** Every Euclidean domain is a PID.
- **Dependencies:** FC01-C08-U012 (`euclidean-ideals-principal`), FC01-C08-U026 (`principal-ideal-domain`)


- **Kind:** Reusable comparison.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10612.
- **Statement/data:** Z[√−5] is not a PID; e.g. the displayed ideal (3,1+√−5) is nonprincipal. The source also records nonprincipal ideals whose product is principal.
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C08-U026 (`principal-ideal-domain`)


- **Kind:** Reusable comparison.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10614.
- **Statement/data:** Z[(1+√−19)/2] is a PID but not a Euclidean domain, so the inclusion Euclidean domains⊂PIDs is strict.
- **Dependencies:** FC01-C08-U025 (`quadratic-PID-not-euclidean-preexample`), FC01-C08-U026 (`principal-ideal-domain`)


- **Kind:** Proposition 6.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10620.
- **Statement/data:** If R is a PID and nonzero a,b generate (d), then d is a gcd of a,b, d=ax+by for some x,y∈R, and d is unique up to multiplication by a unit.
- **Dependencies:** FC01-C08-U026 (`principal-ideal-domain`), FC01-C08-U016 (`gcd-principal-ideal`), FC01-C08-U018 (`gcd-associates`)


- **Kind:** Proposition 7.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10634.
- **Statement/data:** Every nonzero prime ideal in a PID is maximal.
- **Dependencies:** FC01-C08-U026 (`principal-ideal-domain`), FC01-C07-U075 (`prime-ideal`), FC01-C07-U072 (`maximal-ideal`)


- **Kind:** Corollary 8.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10640.
- **Statement/data:** If R is commutative and R[x] is a PID (or Euclidean domain), then R is a field.
- **Dependencies:** FC01-C08-U031 (`PID-nonzero-prime-maximal`), FC01-C07-U026 (`polynomial-ring`), FC01-C07-U074 (`maximal-quotient-field`)


- **Kind:** Definition.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10646.
- **Statement/data:** A Dedekind–Hasse norm on an integral domain R is a positive norm N such that for nonzero a,b, either a∈(b), or (a,b) contains a nonzero element of norm strictly less than N(b); equivalently there exist s,t with 0<N(sa−tb)<N(b).
- **Dependencies:** FC01-C08-U001 (`norm-domain`), FC01-C07-U013 (`integral-domain`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Proposition 9.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10650.
- **Statement/data:** An integral domain is a PID iff it admits a Dedekind–Hasse norm.
- **Dependencies:** FC01-C08-U026 (`principal-ideal-domain`), FC01-C08-U033 (`dedekind-hasse-norm`)


- **Kind:** Reusable named comparison.
- **Locator:** §8.2 “Principal Ideal Domains”; printed pp. 279–282 (section span); extraction L10656.
- **Statement/data:** The positive field norm on Z[(1+√−19)/2] is a Dedekind–Hasse norm; hence this ring is a PID although it is not Euclidean.
- **Dependencies:** FC01-C07-U021 (`quadratic-field-norm`), FC01-C08-U034 (`PID-iff-DH-norm`), FC01-C08-U029 (`PID-not-euclidean-example`)


- **Kind:** Definition.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10726.
- **Statement/data:** In an integral domain, a nonzero nonunit r is irreducible if r=ab forces a or b to be a unit; otherwise reducible. A nonzero p is prime if (p) is a prime ideal, equivalently p is a nonunit and p|ab implies p|a or p|b. Elements differing by a unit are associates.
- **Dependencies:** FC01-C07-U013 (`integral-domain`), FC01-C07-U009 (`zero-divisor-unit`), FC01-C07-U075 (`prime-ideal`), FC01-C07-U065 (`principal-ideal-divisibility`)


- **Kind:** Proposition 10.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10734.
- **Statement/data:** In any integral domain, every prime element is irreducible.
- **Dependencies:** FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10738.
- **Statement/data:** In Z[√−5], 3 is irreducible but not prime because 3 divides (2+√−5)(2−√−5)=9 while dividing neither factor.
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Proposition 11.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10742.
- **Statement/data:** In a PID, a nonzero element is prime iff it is irreducible.
- **Dependencies:** FC01-C08-U031 (`PID-nonzero-prime-maximal`), FC01-C08-U037 (`prime-implies-irreducible`), FC01-C08-U026 (`principal-ideal-domain`)


- **Kind:** Definition.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10758.
- **Statement/data:** A UFD is an integral domain in which every nonzero nonunit is a finite product of irreducibles, and every two such factorizations have the same number of factors after reordering, with corresponding factors associate.
- **Dependencies:** FC01-C07-U013 (`integral-domain`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10766.
- **Statement/data:** Every field is vacuously a UFD because it has no nonzero nonunits.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`), FC01-C08-U040 (`unique-factorization-domain`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10772.
- **Statement/data:** Z[2i]={a+2bi:a,b∈Z} is an integral domain but not a UFD: 4=2·2=(−2i)(2i) gives distinct irreducible factorizations since 2 and 2i are not associates in this subring.
- **Dependencies:** FC01-C07-U017 (`subring`), FC01-C08-U040 (`unique-factorization-domain`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10774.
- **Statement/data:** Z[√−5] is not a UFD because 6=2·3=(1+√−5)(1−√−5) gives two nonassociate irreducible factorizations.
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C08-U040 (`unique-factorization-domain`)


- **Kind:** Recorded theorem/comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10776.
- **Statement/data:** Although elements of a quadratic integer ring need not factor uniquely, the source records the later theorem that every nonzero ideal in such a ring factors uniquely into prime ideals (the Dedekind-domain phenomenon proved later).
- **Dependencies:** FC01-C07-U020 (`quadratic-integer-ring`), FC01-C07-U075 (`prime-ideal`)


- **Kind:** Proposition 12.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10780.
- **Statement/data:** In a UFD, a nonzero element is prime iff it is irreducible.
- **Dependencies:** FC01-C08-U040 (`unique-factorization-domain`), FC01-C08-U037 (`prime-implies-irreducible`)


- **Kind:** Proposition 13.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10788.
- **Statement/data:** If nonzero a,b in a UFD have prime factorizations over distinct p_i with exponents e_i,f_i, then ∏p_i^{min(e_i,f_i)} is a gcd of a,b.
- **Dependencies:** FC01-C08-U040 (`unique-factorization-domain`), FC01-C08-U015 (`ring-divisibility-gcd`)


- **Kind:** Theorem 14.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10810.
- **Statement/data:** Every PID is a UFD; hence every Euclidean domain is a UFD.
- **Dependencies:** FC01-C08-U026 (`principal-ideal-domain`), FC01-C08-U040 (`unique-factorization-domain`), FC01-C08-U039 (`PID-prime-iff-irreducible`), FC01-C08-U027 (`euclidean-implies-PID`)


- **Kind:** Corollary 15 (Fundamental Theorem of Arithmetic).
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10838.
- **Statement/data:** Z is a UFD.
- **Dependencies:** FC01-C08-U006 (`integers-euclidean`), FC01-C08-U047 (`PID-implies-UFD`)


- **Kind:** Corollary 16.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10844.
- **Statement/data:** Every PID has a multiplicative Dedekind–Hasse norm; one may take N(0)=0, N(unit)=1, and N(a)=2^n when a has n irreducible factors counted with multiplicity.
- **Dependencies:** FC01-C08-U047 (`PID-implies-UFD`), FC01-C08-U033 (`dedekind-hasse-norm`)


- **Kind:** Reusable criterion.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10852.
- **Statement/data:** In a quadratic integer ring O, if |N(α)| is a prime integer then α is irreducible.
- **Dependencies:** FC01-C07-U021 (`quadratic-field-norm`), FC01-C07-U022 (`quadratic-integer-unit-norm`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10862.
- **Statement/data:** For a rational prime p, p factors in Z[i] iff p is a sum a²+b²; then p=(a+bi)(a−bi). The prime 2=(1+i)(1−i), and primes p≡3 (mod 4) remain irreducible in Z[i].
- **Dependencies:** FC01-C08-U008 (`gaussian-integers-euclidean`), FC01-C08-U050 (`quadratic-norm-prime-implies-irreducible`), FC01-C08-U047 (`PID-implies-UFD`)


- **Kind:** Lemma 17.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10870.
- **Statement/data:** A prime integer p divides n²+1 for some integer n iff p=2 or p≡1 (mod 4).
- **Dependencies:** FC01-C00-U037 (`units-Zmodn-coprime`), FC01-C03-U020 (`element-order-divides-group`)


- **Kind:** Proposition 18.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10882.
- **Statement/data:** A prime p is a sum of two integer squares iff p=2 or p≡1 (mod 4), uniquely up to exchanging the two summands and changing signs. The Gaussian irreducibles, up to associates, are 1+i; rational primes p≡3 (mod 4); and the conjugate factors a±bi of primes p=a²+b²≡1 (mod 4).
- **Dependencies:** FC01-C08-U052 (`prime-divides-n2plus1`), FC01-C08-U051 (`gaussian-prime-factor-pattern`), FC01-C08-U040 (`unique-factorization-domain`)


- **Kind:** Corollary 19.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10896.
- **Statement/data:** For n=2^k∏p_i^{a_i}∏q_j^{b_j}, with p_i≡1 and q_j≡3 (mod 4), n is a sum of two integer squares iff every b_j is even. If so the number of ordered signed representations n=A²+B² is 4∏(a_i+1).
- **Dependencies:** FC01-C08-U053 (`fermat-two-squares-gaussian-irreducibles`), FC01-C08-U048 (`fundamental-theorem-arithmetic-UFD`)


- **Kind:** Reusable comparison.
- **Locator:** §8.3 “Unique Factorization Domains”; printed pp. 283–294 (section span); extraction L10920.
- **Statement/data:** For commutative unital rings: fields ⊊ Euclidean domains ⊊ PIDs ⊊ UFDs ⊊ integral domains; the source supplies Z, Z[(1+√−19)/2], Z[x], and Z[√−5] as witnesses that each inclusion is proper.
- **Dependencies:** FC01-C08-U005 (`fields-euclidean`), FC01-C08-U029 (`PID-not-euclidean-example`), FC01-C08-U047 (`PID-implies-UFD`), FC01-C08-U043 (`Zsqrtminus5-not-UFD`)


Units: 71.


- **Kind:** Definition/construction recap.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11006.
- **Statement/data:** For commutative unital R, R[x] consists of finite formal sums in x, with degree, leading term/coefficient, monic polynomial, coefficientwise addition, and convolution multiplication as stated; R is identified with the constant subring.
- **Dependencies:** FC01-C07-U026 (`polynomial-ring`), FC01-C07-U027 (`polynomial-operations`), FC01-C07-U028 (`polynomial-constants`)


- **Kind:** Proposition 1.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11022.
- **Statement/data:** If R is an integral domain, then for nonzero p,q∈R[x], deg(pq)=deg p+deg q; the units of R[x] are exactly R^×; and R[x] is an integral domain.
- **Dependencies:** FC01-C07-U029 (`polynomial-domain-properties`)


- **Kind:** Definition/recap.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11030.
- **Statement/data:** If R is an integral domain, the quotient field of R[x] consists of p(x)/q(x) with q≠0 and is called the field of rational functions in x with coefficients in R.
- **Dependencies:** FC01-C07-U086 (`rational-function-field`), FC01-C09-U002 (`polynomial-domain-properties-recap`)


- **Kind:** Proposition 2.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11034.
- **Statement/data:** For an ideal I of R, let I[x]=(I) be the ideal of R[x] generated by I, equivalently polynomials all of whose coefficients lie in I. Then R[x]/I[x]≅(R/I)[x]. In particular, if I is prime in R then I[x] is prime in R[x].
- **Dependencies:** FC01-C07-U049 (`quotient-ring`), FC01-C09-U001 (`polynomial-ring-recap`), FC01-C07-U076 (`prime-quotient-domain`)


- **Kind:** Reusable comparison.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11044.
- **Statement/data:** If I is maximal in R, I[x] need not be maximal in R[x]; however the ideal (I,x) generated by I and x is maximal.
- **Dependencies:** FC01-C09-U004 (`polynomial-ideal-quotient`), FC01-C07-U074 (`maximal-quotient-field`)


- **Kind:** Reusable construction.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11050.
- **Statement/data:** For n≥1, Z[x]/nZ[x]≅(Z/nZ)[x]; the natural projection reduces coefficients modulo n. For prime p, pZ[x] is a prime ideal and the quotient is an integral domain.
- **Dependencies:** FC01-C09-U004 (`polynomial-ideal-quotient`), FC01-C07-U054 (`reduction-mod-n`)


- **Kind:** Definition/construction.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11060.
- **Statement/data:** Define R[x_1,…,x_n] inductively by R[x_1,…,x_n]=R[x_1,…,x_{n−1}][x_n]. Equivalently its elements are finite sums of monomial terms a x_1^{d_1}⋯x_n^{d_n}.
- **Dependencies:** FC01-C09-U001 (`polynomial-ring-recap`)


- **Kind:** Definitions/notation.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11072.
- **Statement/data:** For a term a x_1^{d_1}⋯x_n^{d_n}: its monomial part is x_1^{d_1}⋯x_n^{d_n}; d_i is its degree in x_i; total degree is Σd_i; (d_1,…,d_n) is its multidegree. A polynomial is homogeneous/a form if all terms have the same total degree; its degree-k homogeneous component is the sum of its degree-k terms, giving a unique decomposition f=Σ f_k.
- **Dependencies:** FC01-C09-U007 (`multivariable-polynomial-ring`)


- **Kind:** Construction.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11080.
- **Statement/data:** A polynomial ring in an arbitrary set of variables over R consists of finite sums of monomial terms, equivalently the union of the polynomial rings in finite subsets of the variables.
- **Dependencies:** FC01-C09-U007 (`multivariable-polynomial-ring`)


- **Kind:** Recorded extension.
- **Locator:** §9.1 “Definitions and Basic Properties”; printed pp. 295–298 (section span); extraction L11116.
- **Statement/data:** All three assertions of Proposition 1—degree additivity for products, unit characterization, and preservation of integral-domain status—extend to polynomial rings in any finite or arbitrary number of variables.
- **Dependencies:** FC01-C09-U002 (`polynomial-domain-properties-recap`), FC01-C09-U009 (`arbitrary-variable-polynomial-ring`)


- **Kind:** Theorem 3 (Polynomial Division Algorithm).
- **Locator:** §9.2 “Polynomial Rings over Fields I”; printed pp. 299–302 (section span); extraction L11182.
- **Statement/data:** If F is a field and a,b∈F[x] with b≠0, there are unique q,r∈F[x] such that a=qb+r and r=0 or deg r<deg b. Thus F[x] is Euclidean for the degree norm.
- **Dependencies:** FC01-C07-U003 (`division-ring-field`), FC01-C08-U002 (`euclidean-domain`), FC01-C09-U001 (`polynomial-ring-recap`)


- **Kind:** Corollary 4.
- **Locator:** §9.2 “Polynomial Rings over Fields I”; printed pp. 299–302 (section span); extraction L11216.
- **Statement/data:** For a field F, F[x] is a PID and a UFD.
- **Dependencies:** FC01-C09-U011 (`field-polynomial-division`), FC01-C08-U027 (`euclidean-implies-PID`), FC01-C08-U047 (`PID-implies-UFD`)


- **Kind:** Reusable comparison.
- **Locator:** §9.2 “Polynomial Rings over Fields I”; printed pp. 299–302 (section span); extraction L11230.
- **Statement/data:** Q[x,y]=Q[x][y] is not a PID because its coefficient ring Q[x] is not a field; the source points to (x,y) as a nonprincipal ideal.
- **Dependencies:** FC01-C09-U007 (`multivariable-polynomial-ring`), FC01-C08-U032 (`Rx-PID-implies-field`)


- **Kind:** Recorded comparison.
- **Locator:** §9.2 “Polynomial Rings over Fields I”; printed pp. 299–302 (section span); extraction L11232.
- **Statement/data:** If F⊆E are fields and a,b∈F[x] with b≠0, the quotient and remainder obtained by division in E[x] are the same elements q,r∈F[x] obtained in F[x]. Hence b|a and the monic gcd of a,b are unchanged by extension of the coefficient field.
- **Dependencies:** FC01-C09-U011 (`field-polynomial-division`), FC01-C08-U015 (`ring-divisibility-gcd`)


- **Kind:** Proposition 5 (Gauss’s Lemma).
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11324.
- **Statement/data:** Let R be a UFD with fraction field F and p∈R[x]. If p=A B with nonconstant A,B∈F[x], then there exist nonzero r,s∈F such that a=rA,b=sB lie in R[x] and p=ab. In particular reducibility over F implies reducibility over R.
- **Dependencies:** FC01-C08-U040 (`unique-factorization-domain`), FC01-C07-U083 (`ring-field-of-fractions`), FC01-C09-U001 (`polynomial-ring-recap`)


- **Kind:** Corollary 6.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11332.
- **Statement/data:** Let R be a UFD with fraction field F. If p∈R[x] has coefficients with gcd 1, then p is irreducible in R[x] iff irreducible in F[x]. In particular a monic polynomial irreducible in R[x] remains irreducible in F[x].
- **Dependencies:** FC01-C09-U015 (`gauss-lemma`), FC01-C08-U046 (`UFD-gcd-prime-exponents`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Theorem 7.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11336.
- **Statement/data:** R is a UFD iff R[x] is a UFD.
- **Dependencies:** FC01-C09-U015 (`gauss-lemma`), FC01-C09-U016 (`primitive-polynomial-irreducibility`), FC01-C08-U040 (`unique-factorization-domain`)


- **Kind:** Corollary 8.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11350.
- **Statement/data:** If R is a UFD, then a polynomial ring in any finite or arbitrary number of variables over R is a UFD.
- **Dependencies:** FC01-C09-U017 (`UFD-polynomial-iff`), FC01-C09-U009 (`arbitrary-variable-polynomial-ring`)


- **Kind:** Reusable comparison.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11356.
- **Statement/data:** Z[x] (and multivariable polynomial rings over Z) are UFDs; Z[x] is a UFD that is not a PID.
- **Dependencies:** FC01-C09-U018 (`arbitrary-polynomial-UFD`), FC01-C07-U067 (`Zx-nonprincipal-example`)


- **Kind:** Recorded criterion.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11362.
- **Statement/data:** Over an integral domain, a nonconstant monic p∈R[x] is reducible iff it factors as a product of two monic polynomials of smaller positive degree.
- **Dependencies:** FC01-C09-U002 (`polynomial-domain-properties-recap`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Reusable comparison.
- **Locator:** §9.3 “Polynomial Rings that are Unique Factorization Domains”; printed pp. 303–306 (section span); extraction L11364.
- **Statement/data:** For R=Z[2i] with fraction field Q(i), x²+1 is monic and irreducible in R[x] but factors as (x−i)(x+i) in Q(i)[x]. Thus the monic conclusion of Corollary 6 fails without the UFD hypothesis, and R is not a UFD.
- **Dependencies:** FC01-C08-U042 (`Z2i-not-UFD`), FC01-C09-U016 (`primitive-polynomial-irreducibility`), FC01-C09-U020 (`monic-factorization-criterion`)


- **Kind:** Proposition 9.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11402.
- **Statement/data:** For a field F and p∈F[x], p has a degree-one factor iff p has a root α∈F; equivalently p(α)=0 iff x−α divides p.
- **Dependencies:** FC01-C09-U011 (`field-polynomial-division`)


- **Kind:** Proposition 10.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11414.
- **Statement/data:** A polynomial of degree 2 or 3 over a field F is reducible iff it has a root in F.
- **Dependencies:** FC01-C09-U022 (`linear-factor-root`), FC01-C08-U036 (`irreducible-prime-associate`)


- **Kind:** Proposition 11 (Rational Root Criterion).
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11420.
- **Statement/data:** For p(x)=a_nx^n+⋯+a_0∈Z[x], if r/s∈Q in lowest terms is a root then r|a_0 and s|a_n. In particular, for monic p, any rational root is an integer divisor of a_0.
- **Dependencies:** FC01-C00-U021 (`relatively-prime`), FC01-C09-U022 (`linear-factor-root`), FC01-C07-U065 (`principal-ideal-divisibility`)


- **Kind:** Proposition 12.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11444.
- **Statement/data:** Let I be a proper ideal in an integral domain R and p∈R[x] a nonconstant monic polynomial. If the image of p in (R/I)[x] cannot be factored into two lower-degree polynomials, then p is irreducible in R[x].
- **Dependencies:** FC01-C09-U004 (`polynomial-ideal-quotient`), FC01-C09-U020 (`monic-factorization-criterion`), FC01-C07-U053 (`proper-trivial-ideal`)


- **Kind:** Reusable comparison.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11448.
- **Statement/data:** The converse to reduction-based irreducibility fails: the source records irreducible integer polynomials whose reductions are reducible modulo every prime/every integer, respectively.
- **Dependencies:** FC01-C09-U025 (`reduction-irreducibility-criterion`)


- **Kind:** Proposition 13 (Eisenstein–Schönemann Criterion).
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11460.
- **Statement/data:** Let P be a prime ideal of an integral domain R and f=x^n+a_{n−1}x^{n−1}+⋯+a_0∈R[x], n≥1. If every a_i lies in P and a_0∉P², then f is irreducible in R[x].
- **Dependencies:** FC01-C07-U075 (`prime-ideal`), FC01-C07-U013 (`integral-domain`), FC01-C09-U001 (`polynomial-ring-recap`)


- **Kind:** Corollary 14 (Eisenstein for Z[x]).
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11466.
- **Statement/data:** If p is prime and monic f=x^n+a_{n−1}x^{n−1}+⋯+a_0∈Z[x] has p|a_i for every i<n but p²∤a_0, then f is irreducible in both Z[x] and Q[x].
- **Dependencies:** FC01-C09-U027 (`eisenstein-general`), FC01-C09-U016 (`primitive-polynomial-irreducibility`)


- **Kind:** Reusable comparison.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11474.
- **Statement/data:** If an integer a is divisible by a prime p but not p², then x^n−a is irreducible in Z[x]; in particular x^n−p is irreducible for every n≥1.
- **Dependencies:** FC01-C09-U028 (`eisenstein-Z`)


- **Kind:** Reusable construction/comparison.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11476.
- **Statement/data:** Irreducibility may be checked after translating x: x^4+1 is irreducible because f(x+1)=x^4+4x^3+6x²+4x+2 is Eisenstein at 2; any factorization of f would translate to one of f(x+1).
- **Dependencies:** FC01-C09-U028 (`eisenstein-Z`)


- **Kind:** Reusable named construction.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11480.
- **Statement/data:** For prime p, Φ_p(x)=(x^p−1)/(x−1)=x^{p−1}+⋯+x+1 is a cyclotomic polynomial; Φ_p(x+1) is Eisenstein at p, hence Φ_p is irreducible in Z[x].
- **Dependencies:** FC01-C09-U028 (`eisenstein-Z`), FC01-C09-U030 (`translation-preserves-irreducibility-example`)


- **Kind:** Reusable comparison.
- **Locator:** §9.4 “Irreducibility Criteria”; printed pp. 307–312 (section span); extraction L11492.
- **Statement/data:** For an integral domain k and R=k[x], the polynomial X^n−x∈R[X] is Eisenstein at the prime ideal (x), hence irreducible in R[X].
- **Dependencies:** FC01-C09-U027 (`eisenstein-general`), FC01-C09-U004 (`polynomial-ideal-quotient`)


- **Kind:** Proposition 15.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11586.
- **Statement/data:** For a field F, the maximal ideals of F[x] are exactly (f(x)) with f irreducible. Equivalently F[x]/(f) is a field iff f is irreducible.
- **Dependencies:** FC01-C09-U012 (`field-polynomial-PID-UFD`), FC01-C08-U031 (`PID-nonzero-prime-maximal`), FC01-C07-U074 (`maximal-quotient-field`)


- **Kind:** Proposition 16.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11590.
- **Statement/data:** If nonconstant g∈F[x] factors as g=∏*{i=1}^k f_i^{n_i} with distinct irreducibles f_i, then F[x]/(g)≅∏*{i=1}^k F[x]/(f_i^{n_i}).
- **Dependencies:** FC01-C09-U012 (`field-polynomial-PID-UFD`), FC01-C07-U092 (`chinese-remainder-ring`), FC01-C08-U040 (`unique-factorization-domain`)


- **Kind:** Definition.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11604.
- **Statement/data:** A root α of f∈F[x] has multiplicity m if (x−α)^m divides f but (x−α)^{m+1} does not.
- **Dependencies:** FC01-C09-U022 (`linear-factor-root`), FC01-C08-U015 (`ring-divisibility-gcd`)


- **Kind:** Proposition 17.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11606.
- **Statement/data:** If f∈F[x] has roots α_1,…,α_k listed with multiplicity, then ∏(x−α_i) divides f. Hence a degree-n polynomial over a field has at most n roots, counted with multiplicity.
- **Dependencies:** FC01-C09-U035 (`root-multiplicity`), FC01-C09-U022 (`linear-factor-root`), FC01-C09-U012 (`field-polynomial-PID-UFD`)


- **Kind:** Proposition 18.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11612.
- **Statement/data:** Every finite subgroup of the multiplicative group of a field is cyclic. In particular, for a finite field F, F^× is cyclic.
- **Dependencies:** FC01-C09-U036 (`polynomial-root-bound`), FC01-C05-U007 (`fundamental-theorem-fg-abelian`)


- **Kind:** Corollary 19.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11622.
- **Statement/data:** For prime p, (Z/pZ)^× is cyclic.
- **Dependencies:** FC01-C09-U037 (`finite-field-multiplicative-subgroup-cyclic`), FC01-C01-U026 (`finite-field-notation`)


- **Kind:** Corollary 20.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11626.
- **Statement/data:** For n=∏p_i^{α_i}, (Z/nZ)^×≅∏(Z/p_i^{α_i}Z)^×. For α≥2, (Z/2^αZ)^×≅Z_2×Z_{2^{α−2}} (with the order-1 factor at α=2 understood). For odd prime p, (Z/p^αZ)^× is cyclic of order p^{α−1}(p−1).
- **Dependencies:** FC01-C07-U095 (`CRT-prime-power-decomposition`), FC01-C09-U038 (`Fp-units-cyclic`), FC01-C00-U028 (`fundamental-theorem-arithmetic`)


- **Kind:** Reusable comparison.
- **Locator:** §9.5 “Polynomial Rings over Fields II”; printed pp. 313–314 (section span); extraction L11636.
- **Statement/data:** Since Aut(Z_n)≅(Z/nZ)^×, Corollary 20 determines the automorphism group of every finite cyclic group; in particular Aut(Z_p) is cyclic of order p−1.
- **Dependencies:** FC01-C04-U033 (`aut-cyclic`), FC01-C09-U039 (`units-mod-n-structure`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11670.
- **Statement/data:** A commutative ring R with identity is Noetherian if every ideal of R is finitely generated.
- **Dependencies:** FC01-C07-U001 (`ring`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Theorem 21 (Hilbert Basis Theorem).
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11676.
- **Statement/data:** If R is Noetherian, then R[x] is Noetherian.
- **Dependencies:** FC01-C09-U041 (`noetherian-ring`), FC01-C09-U001 (`polynomial-ring-recap`)


- **Kind:** Corollary 22.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11698.
- **Statement/data:** Every ideal in F[x_1,…,x_n] over a field F is finitely generated.
- **Dependencies:** FC01-C09-U042 (`hilbert-basis-theorem`), FC01-C09-U007 (`multivariable-polynomial-ring`)


- **Kind:** Definition/construction.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11702.
- **Statement/data:** Given x_1>⋯>x_n, lexicographic order compares monomials by the first coordinate in which their exponent tuples differ; the one with larger exponent there is larger.
- **Dependencies:** FC01-C09-U008 (`monomial-multidegree-homogeneous`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11704.
- **Statement/data:** A monomial ordering is a well-order ≥ on monomials compatible with multiplication: m_1≥m_2 implies mm_1≥mm_2 for every monomial m. Equivalently it is a translation-invariant well-order on nonnegative multidegree tuples.
- **Dependencies:** FC01-C09-U044 (`lexicographic-monomial-order`), FC01-C09-U008 (`monomial-multidegree-homogeneous`)


- **Kind:** Recorded criterion/properties.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11706.
- **Statement/data:** For any monomial ordering, every monomial m satisfies m≥1. Conversely a total monomial order with 1 minimal and compatible with multiplication is automatically a well-order, hence a monomial ordering.
- **Dependencies:** FC01-C09-U045 (`monomial-ordering`), FC01-C09-U042 (`hilbert-basis-theorem`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11710.
- **Statement/data:** Fix a monomial ordering. LT(f) is the maximal monomial term of nonzero f (LT(0)=0); ∂(f) is the multidegree of LT(f). For nonzero f,g, ∂(fg)=∂f+∂g and LT(fg)=LT(f)LT(g).
- **Dependencies:** FC01-C09-U045 (`monomial-ordering`), FC01-C09-U008 (`monomial-multidegree-homogeneous`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11714.
- **Statement/data:** For an ideal I⊆F[x_1,…,x_n], LT(I) is the ideal generated by {LT(f):f∈I}.
- **Dependencies:** FC01-C09-U047 (`leading-term-multidegree`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Definition/comparison.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11718.
- **Statement/data:** An ideal generated by monomials is a monomial ideal. A polynomial lies in a monomial ideal iff each of its monomial terms is a multiple of one of the monomial generators.
- **Dependencies:** FC01-C09-U048 (`leading-term-ideal`), FC01-C07-U065 (`principal-ideal-divisibility`)


- **Kind:** Recorded comparison.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11720.
- **Statement/data:** If I=(f_1,…,f_m), then (LT(f_1),…,LT(f_m))⊆LT(I), and the inclusion may be strict.
- **Dependencies:** FC01-C09-U048 (`leading-term-ideal`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11744.
- **Statement/data:** A Gröbner basis for an ideal I⊆F[x_1,…,x_n] is a finite generating set {g_1,…,g_m} such that LT(I)=(LT(g_1),…,LT(g_m)). It depends on the chosen monomial ordering.
- **Dependencies:** FC01-C09-U048 (`leading-term-ideal`), FC01-C09-U050 (`leading-terms-generators-inclusion`), FC01-C09-U043 (`field-multivar-ideals-fg`)


- **Kind:** Algorithm/construction.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11756.
- **Statement/data:** Fix a monomial order and ordered nonzero divisors g_1,…,g_m. Repeatedly cancel LT(f) by the first LT(g_i) dividing it; if none divides, move LT(f) to the remainder. The process terminates with f=Σq_i g_i+r, each ∂(q_i g_i)≤∂f, and no nonzero term of r divisible by any LT(g_i). In general q_i and r depend on divisor order.
- **Dependencies:** FC01-C09-U045 (`monomial-ordering`), FC01-C09-U047 (`leading-term-multidegree`)


- **Kind:** Theorem 23.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11810.
- **Statement/data:** Fix a monomial order and a Gröbner basis G={g_1,…,g_m} of a nonzero ideal I⊆F[x_1,…,x_n]. Every f has a unique decomposition f=f_I+r with f_I∈I and no nonzero term of r divisible by any LT(g_i). General polynomial division computes f_I,r independently of divisor order; r is the unique representative of f+I of this form, so f∈I iff r=0.
- **Dependencies:** FC01-C09-U051 (`groebner-basis`), FC01-C09-U052 (`general-polynomial-division`), FC01-C07-U049 (`quotient-ring`)


- **Kind:** Proposition 24.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11834.
- **Statement/data:** If g_1,…,g_m∈I satisfy LT(I)=(LT(g_1),…,LT(g_m)), then they generate I and form a Gröbner basis. Every nonzero ideal I⊆F[x_1,…,x_n] has a Gröbner basis.
- **Dependencies:** FC01-C09-U053 (`groebner-normal-form`), FC01-C09-U043 (`field-multivar-ideals-fg`), FC01-C09-U048 (`leading-term-ideal`)


- **Kind:** Definition/construction.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11846.
- **Statement/data:** For f_1,f_2, let M be the monic least common multiple of LT(f_1),LT(f_2). Their S-polynomial is S(f_1,f_2)=(M/LT(f_1))f_1−(M/LT(f_2))f_2, which cancels the leading terms.
- **Dependencies:** FC01-C09-U047 (`leading-term-multidegree`)


- **Kind:** Lemma 25.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11854.
- **Statement/data:** If f_1,…,f_m have the same multidegree α and h=Σa_i f_i with a_i∈F has strictly smaller multidegree, then h is an F-linear combination of successive S-polynomials S(f_{i−1},f_i).
- **Dependencies:** FC01-C09-U055 (`S-polynomial`), FC01-C09-U047 (`leading-term-multidegree`)


- **Kind:** Definition/notation.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11870.
- **Statement/data:** For an ordered set G={g_1,…,g_m}, write f≡r mod G when r is the remainder produced by general polynomial division of f by G in that order.
- **Dependencies:** FC01-C09-U052 (`general-polynomial-division`)


- **Kind:** Proposition 26 (Buchberger’s Criterion).
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11872.
- **Statement/data:** Let I=(g_1,…,g_m) be nonzero in F[x_1,…,x_n] with a fixed monomial ordering. G={g_i} is a Gröbner basis iff S(g_i,g_j)≡0 mod G for every 1≤i<j≤m.
- **Dependencies:** FC01-C09-U056 (`same-multidegree-cancellation`), FC01-C09-U057 (`remainder-congruence-mod-G`), FC01-C09-U051 (`groebner-basis`)


- **Kind:** Algorithm (Buchberger).
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11892.
- **Statement/data:** Starting from generators G of I, compute S-pair remainders modulo G; whenever a nonzero remainder r occurs, append r to G and repeat. The procedure terminates after finitely many additions at a generating set satisfying Buchberger’s Criterion, hence at a Gröbner basis.
- **Dependencies:** FC01-C09-U058 (`buchberger-criterion`), FC01-C09-U054 (`groebner-LT-criterion-existence`)


- **Kind:** Definition/properties.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11896.
- **Statement/data:** A Gröbner basis is minimal if every leading term is monic and no LT(g_j) is divisible by LT(g_i) for i≠j. Redundant generators may be deleted to obtain one. Minimal Gröbner bases need not be unique, but their number of elements and leading terms are unique for a fixed monomial order.
- **Dependencies:** FC01-C09-U051 (`groebner-basis`), FC01-C09-U054 (`groebner-LT-criterion-existence`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11934.
- **Statement/data:** A Gröbner basis {g_1,…,g_m} is reduced if each LT(g_i) is monic and no term of g_j is divisible by LT(g_i) for j≠i. Every reduced basis is minimal.
- **Dependencies:** FC01-C09-U060 (`minimal-groebner-basis`)


- **Kind:** Construction.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11940.
- **Statement/data:** Starting from a minimal Gröbner basis, divide each g_j by the other basis elements and replace it by its unique remainder; after normalizing leading coefficients this produces a reduced Gröbner basis.
- **Dependencies:** FC01-C09-U061 (`reduced-groebner-basis`), FC01-C09-U053 (`groebner-normal-form`)


- **Kind:** Theorem 27.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11942.
- **Statement/data:** For a fixed monomial ordering on F[x_1,…,x_n], every nonzero ideal has a unique reduced Gröbner basis.
- **Dependencies:** FC01-C09-U062 (`reduce-minimal-groebner`), FC01-C09-U060 (`minimal-groebner-basis`)


- **Kind:** Corollary 28.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11948.
- **Statement/data:** Two ideals I,J⊆F[x_1,…,x_n] are equal iff they have the same reduced Gröbner basis for any fixed monomial ordering.
- **Dependencies:** FC01-C09-U063 (`unique-reduced-groebner`)


- **Kind:** Reusable comparison.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11952.
- **Statement/data:** The source gives distinct generating sets I and J whose Buchberger reductions yield the same reduced Gröbner basis {x+y, y^4−y^3−1}; hence I=J, illustrating Corollary 28 computationally.
- **Dependencies:** FC01-C09-U064 (`ideal-equality-reduced-groebner`), FC01-C09-U059 (`buchberger-algorithm`)


- **Kind:** Recorded comparison.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11978.
- **Statement/data:** The common zero set of a polynomial generating set S depends only on the ideal (S): replacing S by any other generating set of the same ideal does not change the solution set.
- **Dependencies:** FC01-C07-U062 (`ideal-generated-by-subset`), FC01-C00-U005 (`function-conventions`)


- **Kind:** Definition/terminology.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11984.
- **Statement/data:** Finding elements of an ideal that omit selected variables is called elimination theory.
- **Dependencies:** FC01-C09-U007 (`multivariable-polynomial-ring`)


- **Kind:** Definition.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11986.
- **Statement/data:** For I⊆F[x_1,…,x_n], the i-th elimination ideal with respect to x_1>⋯>x_n is I_i=I∩F[x_{i+1},…,x_n].
- **Dependencies:** FC01-C09-U067 (`elimination-theory`), FC01-C09-U044 (`lexicographic-monomial-order`)


- **Kind:** Proposition 29 (Elimination).
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L11992.
- **Statement/data:** If G is a Gröbner basis of nonzero I⊆F[x_1,…,x_n] for lexicographic x_1>⋯>x_n, then G∩F[x_{i+1},…,x_n] is a Gröbner basis of I_i. In particular I_i=0 iff this intersection of G is empty.
- **Dependencies:** FC01-C09-U051 (`groebner-basis`), FC01-C09-U068 (`elimination-ideal`), FC01-C09-U044 (`lexicographic-monomial-order`)


- **Kind:** Construction.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L12050.
- **Statement/data:** If I=(f_1,…,f_s) and J=(h_1,…,h_t), then I+J is generated by all f_i,h_j and IJ is generated by all products f_i h_j.
- **Dependencies:** FC01-C07-U061 (`ideal-sum-product-power`), FC01-C07-U062 (`ideal-generated-by-subset`)


- **Kind:** Proposition 30.
- **Locator:** §9.6 “Polynomials in Several Variables over a Field and Gröbner Bases”; printed pp. 315–335 (section span); extraction L12052.
- **Statement/data:** For ideals I,J⊆F[x_1,…,x_n], tI+(1−t)J is an ideal in F[t,x_1,…,x_n] and I∩J=(tI+(1−t)J)∩F[x_1,…,x_n]. Thus I∩J is the first elimination ideal for lexicographic t>x_1>⋯>x_n and can be computed from a Gröbner basis.
- **Dependencies:** FC01-C09-U069 (`elimination-theorem`), FC01-C09-U070 (`ideal-sum-product-from-generators`)


- Printed page breaks are not reliably represented in the Markdown extraction. The catalogue therefore records exact section page spans from the source table of contents together with exact extraction lines, rather than inventing per-unit printed pages.
- The preliminary extraction renders `\mathbb{R}` and `\mathbb{Q}` inconsistently as forms such as `IR` and `Ql`; the catalogue normalizes these to `R` and `Q` in mathematical prose.
- Several group-theory formulas lose glyphs or spacing (notably around Proposition 1.2/1.1 numbering, normal-subgroup symbols, and some presentation tables). Statements were normalized only where the surrounding source text makes the intended mathematical expression unambiguous.
- In §6.3, OCR around the formal-word construction intermittently drops or mangles the word “reduced”; the defining cancellation conditions and subsequent use of “reduced words” disambiguate the construction.
- In §8.1, “norm” is occasionally OCR-degraded; the catalogue uses the source’s mathematically unambiguous term “norm.”
- In §9.6, Gröbner terminology is repeatedly OCR-rendered as `Grabner`/`Grebner`; the catalogue normalizes it to “Gröbner.”
- Extraction L11704 presents the exponent-tuple ambient set with degraded typography; monomial exponent tuples are nonnegative, and the catalogue states the monomial-order condition on nonnegative multidegrees.
- Extraction L11716 renders the leading-term product identity with a `+` where the mathematical statement is `LT(fg)=LT(f)LT(g)`; the catalogue uses the multiplicative identity and flags this normalization here.
- A few numerical subscripts/superscripts in semidirect-product and small-group examples are visibly OCR-damaged. Only examples whose hypotheses/relations are recoverable from their surrounding main-text statements were catalogued.



- **kind:** Definition
- **source:** §10.1; printed pp. 337–344; extraction line 12254
- **statement/data:** Let R be a ring (not necessarily comutative nor with 1 ). A left R -module or a left module over R is a set M together with (1) a binary operation + on M under which M is an abelian group, and (2) an action of R on M (that is, a map $R \times M \to M )$ ) denoted by rm, for all $r \in R$ and for all $m \in M$ which satisfies (a) $( r + s ) m = r m + s m , \quad { \mathrm { f o r ~ a l l ~ } } r , s \in R , m \in M ,$ (b) (rs)m = r (sm), for all $r , s \in R , m \in M ,$ , and (c) $r ( m + n ) = r m + r n ,$ for all $r \in R , m , n \in M$ If the ring R has a 1 we impose the additional axiom: (d) lm = m, for all m E M.
- **dependencies:** —


- **kind:** Convention
- **source:** §10.1; printed pp. 337–344; extraction line 12270
- **statement/data:** Unless explicitly stated otherwise, “module” means a left unital module; right modules are defined analogously, and for commutative R a left R-module is made right by mr=rm.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §10.1; printed pp. 337–344; extraction line 12274
- **statement/data:** Modules over a field F are exactly vector spaces over F; F-submodules are exactly vector subspaces.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.1; printed pp. 337–344; extraction line 12278
- **statement/data:** Let R be a ring and let M be an R -module. An R -submodule of M is a subgroup N of M which is closed under the action of ring elements, i.e., $r n \in N .$ , for all $r \in R , n \in N$
- **dependencies:** —


- **kind:** Construction
- **source:** §10.1; printed pp. 337–344; extraction line 12306
- **statement/data:** For a unital ring R, R^n with componentwise operations is the free R-module of rank n.
- **dependencies:** —


- **kind:** Construction
- **source:** §10.1; printed pp. 337–344; extraction line 12316
- **statement/data:** If an R-module M is annihilated by a two-sided ideal I, then (r+I)m:=rm gives M an R/I-module structure.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §10.1; printed pp. 337–344; extraction line 12320
- **statement/data:** Z-modules are exactly abelian groups, with scalar multiplication by repeated addition; Z-submodules are exactly subgroups.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §10.1; printed pp. 337–344; extraction line 12344
- **statement/data:** For a field F, an F[x]-module structure on V is equivalent to an F-vector space V with an endomorphism T:V→V; p(x) acts as p(T).
- **dependencies:** —


- **kind:** Named comparison
- **source:** §10.1; printed pp. 337–344; extraction line 12410
- **statement/data:** Under the F[x]-module/endomorphism dictionary, F[x]-submodules are precisely the T-stable vector subspaces.
- **dependencies:** FC01-C10-U008


- **kind:** Proposition 1 (The Submodule Criterion)
- **source:** §10.1; printed pp. 337–344; extraction line 12438
- **statement/data:** (The Submodule Criterion) Let R be a ring and let M be an R-module. A subset N of M is a submodule of M if and only if (1) $N \neq \emptyset ,$ , and (2) ${ \boldsymbol { x } } + { \boldsymbol { r } } { \boldsymbol { y } } \in N$ for all $r \in R$ and for all $x , y \in N$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.1; printed pp. 337–344; extraction line 12448
- **statement/data:** Let R be a commutative ring with identity. An R -algebra is a ring A with identity together with a ring homomorphism $f : R A$ mapping $1 _ { R }$ to $\mathbf { 1 } _ { A }$ such that the subring $f ( R )$ of A is contained in the center of A. If A is an R-algebra then it is easy to check that A has a natural left and right (unital) R-module structure defined by $r \cdot a = a \cdot r = f ( r ) a$ where $f ( r ) a$ is just the multiplication in the ring A (and this is the same as $a f ( r )$ since by assumption $f ( r )$ lies in the center of A). In general it is possible for an R-algebra A to have other left (or right) R-module structures, but unless otherwise stated, this natural module structure on an algebra will be assumed.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.1; printed pp. 337–344; extraction line 12452
- **statement/data:** If A and B are two R -algebras, an R -algebra homomorphism (or isomorphism) is a ring homomorphism (isomorphism, respectively) $\varphi : A B$ mapping l A to $1 _ { B }$ such that $\varphi ( r \cdot a ) = r \cdot \varphi ( a )$ for all $r \in R$ and $a \in A$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.2; printed pp. 345–350; extraction line 12570
- **statement/data:** Let R be a ring and let M and N be R-modules. (1) A map $\varphi : M \to N$ is an R-module homomorphism if it respects the R-module structures of M and N, i.e., (a) ({J(x + y) = ({J(X) + 97 (y), for all $x , y \in M$ and (b) $\varphi ( r x ) = r \varphi ( x ) , \quad { \mathrm { f o r ~ a l l ~ } } r \in R , x \in M .$ (2) An R-module homomorphism is an isomorphism (of R-modules) if it is both injective and surjective. The modules M and N are said to be isomorphic, denoted $M \cong N$ , if there is some R -module isomorphism $\varphi : M \to N$ (3) If $\varphi : M \to N$ is an R -module homomorphism, let ker $\varphi = { m \in M \mid \varphi ( m ) =$ 0} (the kernel of 97) and let $\varphi ( M ) = { n \in N \mid n = \varphi ( m )$ for some $m \in M }$ (the image of $\varphi$ , as usual). (4) Let M and N be R-modules and define ${ \bf H o m } _ { R } ( M , N )$ to be the set of all Rmodule homomorphisms from M into N. Any R -module homomorphism is also a homomorphism of the additive groups, but not every group homomorphism need be a module homomorphism (because condition (b) may not be satisfied). The unqualifed term "isomorphism" when applied to Rmodules will always mean R -module isomorphism. When the symbol ? is used without qualifcation it will denote an isomorphism of the respective structures (which will be evident from the context). It is an easy exercise using the submodule criterion (Proposition 1 ) to show that kernels and images of R -module homomorphisms are submodules.
- **dependencies:** FC01-C10-U010


- **kind:** Named comparison
- **source:** §10.2; printed pp. 345–350; extraction line 12600
- **statement/data:** If R=F is a field, R-module homomorphisms are exactly linear transformations of F-vector spaces.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §10.2; printed pp. 345–350; extraction line 12604
- **statement/data:** Z-module homomorphisms are exactly homomorphisms of abelian groups.
- **dependencies:** —


- **kind:** Proposition 2
- **source:** §10.2; printed pp. 345–350; extraction line 12608
- **statement/data:** Let M, N and L be R-modules. (1) A map $\varphi : M \to N$ is an R-module homomorphism if and only if $\varphi ( r x + y ) = r \varphi ( x ) + \varphi ( y )$ for all $x , y \in M$ and all $r \in R$ (2) Let $\varphi , \psi$ be elements of ${ \bf H o m } _ { R } ( M , N )$ . Define $\varphi + \psi$ by $$ (\varphi + \psi) (m) = \varphi (m) + \psi (m) \quad \text { for all } m \in M. $$ Then $\varphi + \psi \in { \mathrm { H o m } } _ { R } ( M , N )$ and with this operation ${ \bf H o m } _ { R } ( M , N )$ is an abelian group. If R is a commutative ring then for $r \in R$ define rcp by $$ (r \varphi) (m) = r (\varphi (m)) \quad \text { for all } m \in M. $$ Then $r \varphi \in { \mathrm { H o m } } _ { R } ( M , N )$ and with this action of the commutative ring R the abelian group ${ \bf H o m } _ { R } ( M , N )$ is an R-module. (3) If $\varphi \in \mathbf { H o m } _ { R } ( L , M )$ and $\psi \in { \bf H o m } _ { R } ( M , N )$ then 't/f $\circ \varphi \in { \bf H o m } _ { R } ( L , N )$ (4) With addition as above and multiplication defined as function composition, ${ \bf H o m } _ { R } ( M , M )$ is a ring with 1 . When R is comutative ${ \bf H o m } _ { R } ( M , M )$ is an R-algebra.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.2; printed pp. 345–350; extraction line 12652
- **statement/data:** The ring ${ \bf H o m } _ { R } ( M , M )$ is called the endomorphism ring of M and will often be denoted by ${ \mathrm { E n d } } _ { R } ( M )$ , or just End(M) when the ring R is clear from the context. Elements of End{M) are called endomorphisms.
- **dependencies:** —


- **kind:** Proposition 3
- **source:** §10.2; printed pp. 345–350; extraction line 12658
- **statement/data:** Let R be a ring, let M be an R -module and let N be a submodule of M. The (additive, abelian) quotient group $M / N$ can be made into an R -module by defining an action of elements of R by $$ r (x + N) = (r x) + N, \quad \text { for all } r \in R, x + N \in M / N. $$ The natural projection map r : $M \to M / N$ defined by $~ \pi ( x ) = x + N$ is an R -module homomorphism with kernel N.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.2; printed pp. 345–350; extraction line 12682
- **statement/data:** Let A , B be submodules of the R-module M. The sum of A and B is the set $$ A + B = {a + b \mid a \in A, b \in B }. $$ One can easily check that the sum of two submodules A and B is a submodule and is the smallest submodule which contains both A and B.
- **dependencies:** —


- **kind:** Theorem 4 (Isomorphism Theorems)
- **source:** §10.2; printed pp. 345–350; extraction line 12690
- **statement/data:** (Isomorphism Theorems) (1) (The First Isomorphism Theorem for Modules) Let M, N be R-modules and let $\varphi : M \to N$ be an R-module homomorphism. Then ker ({J is a submodule of M and Ml ker $\varphi \cong \varphi ( M )$ (2) (The Second Isomorphism Theorem) Let A, B be submodules of the R-module M. Then $( A + B ) / B \cong A / ( A \cap B )$ (3) (The Third Isomorphism Theorem) Let M be an R-module, and let A and B be submodules of M with $A \subseteq B .$ . Then $( M / A ) / ( B / A ) \cong M / B$ (4) (The Fourth or Lattice Isomorphism Theorem) Let N be a submodule of the R-module M. There is a bijection between the submodules of M which contain N and the submodules of $M / N .$ . The corespondence is given by $A A / N _ { : }$ for all $A \supseteq N$ . This corespondence comutes with the processes of taking sums and intersections (i.e., is a lattice isomorphism between the lattice of submodules of $M / N$ and the lattice of submodules of M which contain N).
- **dependencies:** —


- **kind:** Definition
- **source:** §10.3; printed pp. 351–358; extraction line 12754
- **statement/data:** Let M be an R-module and let $N _ { 1 } , \ldots , N _ { n }$ be submodules of M. (1) The sum of $N _ { 1 } , \ldots , N _ { n }$ is the set of all finite sums of elements from the sets $N _ { i }$ : ${ a _ { 1 } + a _ { 2 } + \cdots + a _ { n } \mid a _ { i } \in N _ { i }$ for all i } . Denote this sum by $N _ { 1 } + \cdots + N _ { n }$ (2) For any subset A of M let $$ R A = \left{r _ {1} a _ {1} + r _ {2} a _ {2} + \dots + r _ {m} a _ {m} \mid r _ {1}, \dots , \dot {r} _ {m} \in R, a _ {1}, \dots , a _ {m} \in A, m \in \mathbb {Z} ^ {+} \right} $$ (where by convention $R A = \left{ 0 \right} \mathrm { i f } A = \varnothing )$ . lf A is the finite set ${ a _ { 1 } , a _ { 2 } , \ldots , a _ { n } }$ we shall write $R a _ { 1 } + R a _ { 2 } + \cdots + R a _ { n }$ for RA. Call RA the submodule of M generated by A. If N is a submodule of M (possibly $N = M )$ and $N = R A ,$ for some subset A of M, we call A a set of generators or generating set for N, and we say N is generated by A. (3) A submodule N of M (possibly $N = M )$ is finitely generated if there is some finite subset A of M such that $N = R A$ , that is, if N is generated by some finite subset. (4) A submodule N of M (possibly $N = M )$ is cyclic if there exists an element $a \in M$ such that $N = R a ,$ that is, if N is generated by one element: $$ N = R a = {r a \mid r \in R }. $$
- **dependencies:** —


- **kind:** Convention
- **source:** §10.3; printed pp. 351–358; extraction line 12776
- **statement/data:** A generating set of smallest finite cardinality for a finitely generated module is called a minimal set of generators.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.3; printed pp. 351–358; extraction line 12802
- **statement/data:** Le $M _ { 1 } , \ldots , M _ { k }$ be a collection of R-modules. The collection of k-tuples $( m _ { 1 } , m _ { 2 } , \ldots , m _ { k } )$ where $m _ { i } \in M _ { i }$ with addition and action of R defined componentwise is called the direct product of $M _ { 1 } , \ldots , M _ { k }$ , denoted $M _ { 1 } \times \cdots \times M _ { k }$ It is evident that the direct product of a collection of R-modules is again an $R \mathrm { - }$ module. The direct product of $M _ { 1 } , \ldots , M _ { k }$ is also refered to as the (external) direct sum of $M _ { 1 } , \ldots , M _ { k }$ and denoted $M _ { 1 } \oplus \dots \oplus M _ { k }$ . The direct product and direct sum of an infinite number of modules (which are diferent in general) are defined in Exercise 20.
- **dependencies:** —


- **kind:** Proposition 5
- **source:** §10.3; printed pp. 351–358; extraction line 12808
- **statement/data:** Let $N _ { 1 } , N _ { 2 } , \ldots , N _ { k }$ be submodules of the R-module M. Then the following are equivalent: (1) The map r : $N _ { 1 } \times N _ { 2 } \times \cdots \times N _ { k } N _ { 1 } + N _ { 2 } + \cdots + N _ { k }$ defined by $$ \pi (a _ {1}, a _ {2}, \dots , a _ {k}) = a _ {1} + a _ {2} + \dots + a _ {k} $$ is an isomorphism (of R-modules): $N _ { 1 } + N _ { 2 } + \cdots + N _ { k } \cong N _ { 1 } \times N _ { 2 } \times \cdots \times N _ { k }$ (2) $N _ { j } \cap ( N _ { 1 } + N _ { 2 } + \cdot \cdot \cdot + N _ { j - 1 } + N _ { j + 1 } + \cdot \cdot \cdot + N _ { k } ) = 0$ for all $j \in \left{ { 1 , 2 , \dots , k } \right}$ (3) Every $x \in N _ { 1 } + \cdots + N _ { k }$ can be written uniquely in the form $a _ { 1 } + a _ { 2 } + \cdots + a _ { k }$ with $a _ { i } \in N _ { i }$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.3; printed pp. 351–358; extraction line 12860
- **statement/data:** An R-module F is said to be $f r e e$ on the subset A of F if for every nonzero element x of $F ,$ , ther exist unique nonzero elements $r _ { 1 } , r _ { 2 } , \ldots , r _ { n }$ of R and unique $a _ { 1 } , a _ { 2 } , \ldots , a _ { n }$ in A such that $x = r _ { 1 } a _ { 1 } + r _ { 2 } a _ { 2 } + \cdot \cdot \cdot + r _ { n } a _ { n }$ , for some ${ \pmb n } \in \mathbb { Z } ^ { + }$ . In this situation we say A is a basis or set of free generators for F. If R is a comutative ring the cardinality of A is called the rank of F ( cf. Exercise 27). One should be careful to note the diference between the uniqueness property of direct sums (Proposition 5(3)) and the uniqueness property of free modules. Namely, in the direct sum of two modules, say $N _ { 1 } \oplus N _ { 2 }$ , each element can be written uniquely as $n _ { 1 } + n _ { 2 } ;$ ; here the uniqueness refers to the module elements $\pmb { n _ { 1 } }$ and $\pmb { n } _ { 2 }$ . In the case of free modules, the uniqueness is on the ring elements as well as the module elements. For example, if $R = \mathbb { Z }$ and $N _ { 1 } = N _ { 2 } = \mathbb { Z } / 2 \mathbb { Z } ,$ , then each element of $N _ { 1 } \oplus N _ { 2 }$ has a unique representation in the form ${ \pmb n } _ { 1 } + { \pmb n } _ { 2 }$ where each $n _ { i } \in N _ { i }$ , however $\pmb { n _ { 1 } }$ (for instance) can be expressed as $\pmb { n _ { 1 } }$ or $3 n _ { 1 } \mathrm { o r } 5 n _ { 1 } \dots \mathrm { e t c . , }$ so each element does not have a unique representation in the form $r _ { 1 } a _ { 1 } + r _ { 2 } a _ { 2 } . …
- **dependencies:** FC01-C10-U024


- **kind:** Theorem 6
- **source:** §10.3; printed pp. 351–358; extraction line 12864
- **statement/data:** For any set A there is a free R-module $F ( A )$ on the set A and $F ( A )$ satisfies the folowing universal property: if M is any R-module and $\varphi : A M$ is any map of sets, then there is a unique R-module homomorphism ${ \Phi } : F ( A ) \to M$ such that $\Phi ( a ) = \varphi ( a )$ , for all ${ \pmb a } \in { \pmb A }$ , tha is, the folowing diagram comutes. When A is the finite set ${ a _ { 1 } , a _ { 2 } , \ldots , a _ { n } } , \ : { \cal F } ( A ) = { \cal R } a _ { 1 } \oplus { \cal R } a _ { 2 } \oplus \cdots \oplus { \cal R } a _ { n } \cong { \cal R } ^ { n } .$ (Compare: Section 6.3, free groups.)
- **dependencies:** —


- **kind:** Corollary 7
- **source:** §10.3; printed pp. 351–358; extraction line 12888
- **statement/data:** (1) If ${ \cal F } _ { 1 }$ and ${ \cal F } _ { 2 }$ are free modules on the same set A, there is a unique isomorphism between ${ \cal F } _ { 1 }$ and $F _ { 2 }$ which is the identity map on A. (2) If F is any fre R-module with basis A, then ${ \pmb F } \cong { \pmb F } ( { \pmb A } )$ . In particular, F enjoys the same universal property with respect to A as $F ( A )$ does in Theorem 6.
- **dependencies:** FC01-C10-U026


- **kind:** Named comparison
- **source:** §10.3; printed pp. 351–358; extraction line 12898
- **statement/data:** For R=Z, the free module F(A) is the free abelian group on A; if |A|=n it is the free abelian group of rank n and is isomorphic to Z^n.
- **dependencies:** —


- **kind:** Construction
- **source:** §10.4; printed pp. 359–377; extraction line 13020
- **statement/data:** Restriction of scalars: for a unital homomorphism f:R→S and a left S-module N, r·n:=f(r)n gives N a left R-module structure.
- **dependencies:** —


- **kind:** Construction
- **source:** §10.4; printed pp. 359–377; extraction line 13056
- **statement/data:** For R⊆S and a left R-module N, S⊗_R N is constructed from the free abelian group on S×N modulo additivity and balancing relations and carries the natural left S-action.
- **dependencies:** —


- **kind:** Construction
- **source:** §10.4; printed pp. 359–377; extraction line 13084
- **statement/data:** The S-module S⊗_R N is the extension of scalars of N from R to S; its natural R-linear map is ι(n)=1⊗n.
- **dependencies:** FC01-C10-U030


- **kind:** Theorem 8
- **source:** §10.4; printed pp. 359–377; extraction line 13088
- **statement/data:** Let R be a subring of S, let N be a left R-module and let $\iota : N \to S \otimes _ { R } N$ be the R-module homomorphism defined by $\iota ( n ) = 1 \otimes n$ . Suppose that $\cal L$ is any left $s \mathrm { - }$ module (hence also an R -module) and that $\varphi : N \to L$ is an R -module homomorphism from N to L. Then there is a unique S-module homomorphism ${ \pmb { \phi } } : S \otimes _ { R } { \pmb { N } } { \pmb { L } }$ such that $\varphi$ factors through $\Phi$ , i.e., $\varphi = \Phi \circ \iota$ and the diagram comutes. Conversely, if ${ \pmb { \phi } } : S \otimes _ { R } { \pmb { N } } { \pmb { L } }$ is an S-module homomorphism then $\varphi = \Phi \circ \iota$ is an R-module homomorphism from N to L.
- **dependencies:** —


- **kind:** Corollary 9
- **source:** §10.4; printed pp. 359–377; extraction line 13104
- **statement/data:** Let $\iota : N \to S \otimes _ { R }$ N be the R-module homomorphism in Theorem 8. Then $N /$ ker t is the unique largest quotient of N that can be embedded in any S-module. In particular, $N$ can be embedded as an R -submodule of some left S -module if and only if t is injective (in which case N is isomorphic to the R -submodule t (N) of the S-module $s \otimes _ { R } N )$
- **dependencies:** FC01-C10-U032


- **kind:** Named example
- **source:** §10.4; printed pp. 359–377; extraction line 13130
- **statement/data:** For a commutative ring R, finite group G, subgroup H≤G, and RH-module N, the induced module is RG⊗_{RH}N.
- **dependencies:** FC01-C10-U031


- **kind:** Construction
- **source:** §10.4; printed pp. 359–377; extraction line 13146
- **statement/data:** For a right R-module M and left R-module N, M⊗_R N is the quotient of the free abelian group on M×N by additivity and (mr,n)∼(m,rn); every tensor is a finite sum of simple tensors.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.4; printed pp. 359–377; extraction line 13160
- **statement/data:** Let M be a right R -module, let N be a left R -module and let L be an abelian group (writen additively). A map $\varphi : M \times N \to L$ is called R-balanced o middle linear with respect to R if $$ \begin{array}{c} \varphi (m _ {1} + m _ {2}, n) = \varphi (m _ {1}, n) + \varphi (m _ {2}, n) \ \varphi (m, n _ {1} + n _ {2}) = \varphi (m, n _ {1}) + \varphi (m, n _ {2}) \ \varphi (m, r n) = \varphi (m r, n) \end{array} $$ for all m , $m _ { 1 } , m _ { 2 } \in M , n , n _ { 1 } , n _ { 2 } \in N $ , and $r \in R$ With this teninology, it follows imediately from the relations in (7) tha the map $\iota : M \times N \to M \otimes _ { R }$ N is R-balanced. The next theorem proves the extremly usefu universal property of the tensor product with respect to balanced maps.
- **dependencies:** —


- **kind:** Theorem 10
- **source:** §10.4; printed pp. 359–377; extraction line 13170
- **statement/data:** Suppose R is a ring with 1 , M is a right R-module, and N is a left R -module. Let $M \otimes _ { R } N$ be the tensor product of M and N over R and let $\iota : M \times N \to$ $M \otimes _ { R } N$ be the R-balanced map defined above. (1) If $\pmb { \phi } : { \cal M } \otimes _ { \cal R } { \cal N } { \cal L }$ is any group homomorphism from $M \otimes _ { R } N$ to an abelian group L then the composite map $\varphi = \Phi \circ \iota$ is an R -balanced map from ${ M } \times { N }$ to $L .$ . (2) Conversely, suppose L is an abelian group and $\varphi : M \times N \to L$ is any Rbalanced map. Then there is a unique group homomorphism ${ \pmb { \phi } } : { \pmb { M } } \otimes _ { R } { \pmb { N } } { \pmb { L } }$ such that $\varphi$ factors through t, i.e., $\varphi = \Phi \circ \iota$ as in ( 1 ). Equivalently, the corespondence $\varphi \Phi$ in the comutative diagram establishes a bijection $$ \left{ \begin{array}{c} R \text {-balanced maps} \ \varphi : M \times N \to L \end{array} \right} \longleftrightarrow \left{ \begin{array}{c} \text { group homomorphisms } \ \Phi : M \otimes_ {R} N \to L \end{array} \right}. $$
- **dependencies:** —


- **kind:** Corollary 11
- **source:** §10.4; printed pp. 359–377; extraction line 13204
- **statement/data:** Suppose D is an abelian group and $\iota ^ { \prime } : M \times N \to D$ is an R-balanced map such that (i) the image of $\pmb { \iota } ^ { \prime }$ generates D as an abelian group, and (i) every R-balanced map defined on $M \times N$ factors through $\pmb { \iota } ^ { \prime }$ as in Theorem LO. Then there is an isomorphism $f : M \otimes _ { R } N \cong D$ of abelian groups with $\iota ^ { \prime } = f \circ \iota .$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.4; printed pp. 359–377; extraction line 13214
- **statement/data:** Let R and S be any rings with 1. An abelian group M is caled an $( S , R ) \mathrm { \cdot }$ bimodule if M is a left S-module, a right R-module, and $s ( m r ) = ( s m ) r$ for all $\pmb { s } \in \pmb { S }$ $r \in R$ and $m \in M$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.4; printed pp. 359–377; extraction line 13234
- **statement/data:** Suppose M is a left (or right) R-module over the comutative ring R. Then the (R, R)-bimodule structure on M defined by letting the left and right R-actions coincide, i.e., mr = rm for all $m \in M$ and $r \in R ,$ , will be called the standard R -module structure on M. Suppose now that N is a left R-module and M is an (S, R)-bimodule. Then just as in the example of extension of scalars the (S, R)-bimodule structure on M implies that $$ s \left(\sum_ {\text { finite }} m _ {i} \otimes n _ {i}\right) = \sum_ {\text { finite }} (s m _ {i}) \otimes n _ {i}\tag{10.8} $$ gives a well defined action of S under which M $\otimes _ { R } N$ is a left S-module. Note that Theorem 10 may be used to give an alternate proof that (8) is well defined, replacing the direct calculations on the relations defining the tensor product with the easier check that a map is R -balanced, as follows. It is very easy to see that for each fixed $s \in S$ the map $( m , n ) \mapsto s m \otimes n$ is an R-balanced map from $M \times N$ to M $\otimes _ { R }$ N. By Theorem 10 there is a well defined group homomorphism $\lambda _ { s }$ from $M \otimes _ { R } N$ to itself such that $\lambda _ { s } ( m \otimes n ) = s m \otimes n$ . Since the right side of (8) is then $\lambda _ { s } ( \sum m _ { i } \otimes n _ { i } )$ ) the fact that $\lambda _ { s }$ is well defined shows that this expression is indeed independent of the representation of the tensor $\sum m _ { i } \otimes n _ { i }$ as a sum of simple tensors. Because $\lambda _ { s }$ is additive, equation (8) holds. …
- **dependencies:** FC01-C10-U037


- **kind:** Definition
- **source:** §10.4; printed pp. 359–377; extraction line 13256
- **statement/data:** Let R be a commutative ring with 1 and let M, N, and L be left R -modules. The map $\varphi : M \times N \to L$ is called R -bilinear if it is R -linear in each factor, i.e., if $$ \varphi (r _ {1} m _ {1} + r _ {2} m _ {2}, n) = r _ {1} \varphi (m _ {1}, n) + r _ {2} \varphi (m _ {2}, n), \quad \text { and } $$ $$ \varphi (m, r _ {1} n _ {1} + r _ {2} n _ {2}) = r _ {1} \varphi (m, n _ {1}) + r _ {2} \varphi (m, n _ {2}) $$ for all $m , m _ { 1 } , m _ { 2 } \in M , n , n _ { 1 } , n _ { 2 } \in N$ and $r _ { 1 } , r _ { 2 } \in R .$ With this terminology Theorem 10 gives
- **dependencies:** FC01-C10-U037


- **kind:** Corollary 12
- **source:** §10.4; printed pp. 359–377; extraction line 13270
- **statement/data:** Suppose $R$ is a commutative ring. Let M and N be two left R-modules and let $M \otimes _ { R } N$ be the tensor product of M and N over $R ,$ where M is given the standard R-module structure. Then $M \otimes _ { R } N$ is a left R-module with $$ r (m \otimes n) = (r m) \otimes n = (m r) \otimes n = m \otimes (r n), $$ and the map $\iota : M \times N \to M \otimes _ { R } N$ with $\iota ( m , n ) = m \otimes n$ is an R-bilinear map. If L is any left R-module then there is a bijection $$ \left{ \begin{array}{c} R \text {-bilinear maps} \ \varphi : M \times N \to L \end{array} \right} \longleftrightarrow \left{ \begin{array}{c} R \text {-module homomorphisms} \ \Phi : M \otimes_ {R} N \to L \end{array} \right} $$ where the corespondence between $\varphi$ and $\Phi$ is given by the commutative diagram $$ \begin{array}{c} M \times N \xrightarrow {\iota} M \otimes_ {R} N \ \varphi \Biggl \downarrow \Phi \ L \end{array} $$
- **dependencies:** —


- **kind:** Theorem 13 (The "Tensor Product" of Two Homomorphisms)
- **source:** §10.4; printed pp. 359–377; extraction line 13380
- **statement/data:** (The "Tensor Product" of Two Homomorphisms) Let $M , M ^ { \prime }$ be right R-modules, let $N , N ^ { \prime }$ be left R-modules, and suppose $\varphi : M \to M ^ { \prime }$ and $\psi : N \to N ^ { \prime }$ are R-module homomorphisms. (1) There is a unique group homomorphism, denoted by $\varphi \otimes \psi$ , mapping $M \otimes _ { R } N$ into $M ^ { \prime } \otimes _ { R } N ^ { \prime }$ such that $( \varphi \otimes \psi ) ( m \otimes n ) = \varphi ( m )$ ® l/f (n) for all $m \in M$ and $\pmb { n } \in N$ (2) If $M , M ^ { \prime }$ are also $( S , R )$ -bimodules for some ring S and $\pmb { \varphi }$ is also an S-module homomorphism, then $\varphi \otimes \psi$ is a homomorphism ofleft S-modules. In particular, if R is comutative then $\varphi \otimes \psi$ is always an R -module homomorphism for the standard R-module structures. (3) If $\lambda : M ^ { \prime } \to M ^ { \prime \prime }$ and $\mu : N ^ { \prime } \to N ^ { \prime \prime }$ are R-module homomorphisms then $( \lambda \otimes \mu ) \circ ( \varphi \otimes \psi ) = ( \lambda \circ \varphi ) \otimes ( \mu \circ \psi )$
- **dependencies:** —


- **kind:** Theorem 14 (Associativity of the Tensor Product)
- **source:** §10.4; printed pp. 359–377; extraction line 13402
- **statement/data:** (Associativity of the Tensor Product) Suppose M is a right R-module, N is an (R, T)-bimodule, and L is a left T -module. Then there is a unique isomorphism $$ (M \otimes_ {R} N) \otimes_ {T} L \cong M \otimes_ {R} (N \otimes_ {T} L) $$ of abelian groups such that (m ® n) ® l ? m ® (n ® l). If M is an (S, R)-bimodule. then this is an isomorphism of S-modules.
- **dependencies:** —


- **kind:** Corollary 15
- **source:** §10.4; printed pp. 359–377; extraction line 13420
- **statement/data:** Suppose R is comutative and M, N, and L are left R -modules. Then $$ (M \otimes N) \otimes L \cong M \otimes (N \otimes L) $$ as R-modules for the standard R-module structures on M, N and L. There is a natural extension of the notion of a bilinear map:
- **dependencies:** —


- **kind:** Definition
- **source:** §10.4; printed pp. 359–377; extraction line 13430
- **statement/data:** Let R be a comutative ring with 1 and let $M _ { 1 } , M _ { 2 } , \ldots , M _ { n }$ and L be R-modules with the standard R-module structures. A map $\varphi : M _ { 1 } \times \cdots \times M _ { n } \to L$ is called n-multilinear over R (or simply multilinear if n and R are clear from the context) if it is an R -module homomorphism in each component when the other component entries are kept constant, i.e., for each i $$ \begin{array}{r l} \varphi (m _ {1}, \ldots , m _ {i - 1}, r m _ {i} + r ^ {\prime} m _ {i} ^ {\prime}, m _ {i + 1}, \ldots , m _ {n}) \ & = r \varphi (m _ {1}, \ldots , m _ {i}, \ldots , m _ {n}) + r ^ {\prime} \varphi (m _ {1}, \ldots , m _ {i} ^ {\prime}, \ldots , m _ {n}) \end{array} $$ for all $m _ { i } , m _ { i } ^ { \prime } \in M _ { i }$ and $r , r ^ { \prime } \in R .$ . When $n = 2$ (respectively, 3) one says cp is bilinear (respectively trilinear) rather than 2-multilinear (or 3-multilinear). One may construct the n-fold tensor product $M _ { 1 } \otimes M _ { 2 } \otimes \cdot \cdot \cdot \otimes M _ { n }$ from first principles and prove its analogous universal property with respect to multilinear maps from $M _ { 1 } \times \cdots \times M _ { n }$ to L. By the previous theorem and corollary, however, an nfold tensor product may be obtained unambiguously by iterating the tensor product of pairs of modules since any bracketing of $M _ { 1 } \otimes \cdots \otimes M _ { n }$ into tensor products of pairs gives an isomorphic R -module. …
- **dependencies:** —


- **kind:** Corollary 16
- **source:** §10.4; printed pp. 359–377; extraction line 13440
- **statement/data:** Let R be a comutative ring and let $M _ { 1 } , \ldots , M _ { n } , L$ be R-modules. Let $M _ { 1 } \otimes M _ { 2 } \otimes \cdots \otimes M _ { n }$ denote any bracketing of the tensor product of these modules and let $$ \iota : M _ {1} \times \dots \times M _ {n} \rightarrow M _ {1} \otimes \dots \otimes M _ {n} $$ be the map defined by $\iota ( m _ { 1 } , \ldots , m _ { n } ) = m _ { 1 } \otimes \cdot \cdot \cdot \otimes m _ { n }$ . Then (1) for every R-module homomorphism $\Phi : M _ { 1 } \otimes \cdots \otimes M _ { n } \to L$ the map $\varphi = \Phi$ o t i s n-multilinear from $M _ { 1 } \times \cdots \times M _ { n }$ to L, and (2) if $\varphi : M _ { 1 } \times \cdot \cdot \cdot \times M _ { n } \to L$ is an n-multilinear map then there is a unique R-module homomorphism $\pmb { \phi } : M _ { 1 } \otimes \cdot \cdot \cdot \otimes M _ { n } L$ such that $\varphi = \Phi \circ \pmb { \mathscr { \iota } } _ { \mathbf { \iota } }$ Hence there is a bijection $$ \left{ \begin{array}{c} n \text {-multilinear maps} \ \varphi : M _ {1} \times \dots \times M _ {n} \to L \end{array} \right} \longleftrightarrow \left{ \begin{array}{c} R \text {-module homomorphisms} \ \Phi : M _ {1} \otimes \dots \otimes M _ {n} \to L \end{array} \right} $$ with respect to which the following diagram comutes: $$ M \times \dots \times M _ {n} \xrightarrow {\iota} M \otimes \dots \otimes M _ {n} \Biggl \downarrow_ {\varphi} \Biggl \downarrow_ {\Phi} L $$
- **dependencies:** —


- **kind:** Theorem 17 (Tensor Products of Direct Sums)
- **source:** §10.4; printed pp. 359–377; extraction line 13466
- **statement/data:** (Tensor Products of Direct Sums) Let M, M' be right R-modules and let $N , N ^ { \prime }$ be left R-modules. Then there are unique group isomorphisms $$ (M \oplus M ^ {\prime}) \otimes_ {R} N \cong (M \otimes_ {R} N) \oplus (M ^ {\prime} \otimes_ {R} N) $$ $$ M \otimes_ {R} (N \oplus N ^ {\prime}) \cong (M \otimes_ {R} N) \oplus (M \otimes_ {R} N ^ {\prime}) $$ such that $( m , m ^ { \prime } ) \otimes n \mapsto ( m \otimes n , m ^ { \prime } \otimes n )$ and $m \otimes ( n , n ^ { \prime } ) \mapsto ( m \otimes n , m \otimes n ^ { \prime } )$ ) respectively. If M, M' are also (S, R)-bimodules, then these are isomorphisms of left S-modules. In particular, if R is comutative, these are isomorphisms of R -modules.
- **dependencies:** —


- **kind:** Corollary 18 (Extension of Scalars for Free Modules)
- **source:** §10.4; printed pp. 359–377; extraction line 13500
- **statement/data:** (Extension of Scalars for Free Modules) The module obtained from the free R-module $N \cong R ^ { n }$ by extension of scalars from R to S is the free S-module $s ^ { n }$ i . e . , $$ S \otimes_ {R} R ^ {n} \cong S ^ {n} $$ as left S-modules.
- **dependencies:** —


- **kind:** Corollary 19
- **source:** §10.4; printed pp. 359–377; extraction line 13510
- **statement/data:** Let R be a commutative ring and let $M \cong R ^ { s }$ and $N \cong R ^ { t }$ be free R-modules with bases $\mathbf { \omega } _ { m _ { 1 } } , \ldots , \mathbf { \omega } _ { m _ { s } }$ and $n _ { 1 } , \ldots , n _ { t } ,$ , respectively. Then $M \otimes _ { R } N$ is a free R-module of rank st, with basis $m _ { i } \otimes n _ { j } , 1 \leq i \leq s$ and $1 \leq j \leq t , \mathrm { i . e }$ ., $$ R ^ {s} \otimes_ {R} R ^ {t} \cong R ^ {s t}. $$
- **dependencies:** —


- **kind:** Proposition 20
- **source:** §10.4; printed pp. 359–377; extraction line 13520
- **statement/data:** Suppose R is a commutative ring and M, N are left R-modules, considered with the standard R-module structures. Then there is a unique R-module isomorphism $$ M \otimes_ {R} N \cong N \otimes_ {R} M $$ mapping m ® n to n ® m.
- **dependencies:** —


- **kind:** Proposition 21
- **source:** §10.4; printed pp. 359–377; extraction line 13534
- **statement/data:** Let R be a commutative ring and let A and B be R -algebras. Then the multiplication $( a \otimes b ) ( a ^ { \prime } \otimes b ^ { \prime } ) = a a ^ { \prime } \otimes b b ^ { \prime }$ is well defined and makes $\pmb { A } \otimes _ { R }$ B into an R-algebra.
- **dependencies:** —


- **kind:** Convention
- **source:** §10.5; printed pp. 378–407; extraction line 13676
- **statement/data:** Exactness of A→B→C means image(A→B)=kernel(B→C); adjoining 0 at the ends encodes injectivity or surjectivity.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 13684
- **statement/data:** (1) The pair of homomorphisms $\ = X \ { \xrightarrow { \alpha } } \ Y \ { \xrightarrow { \beta } } \ Z$ is said to be exact (at Y) if image $\pmb { \alpha } = \mathbf { k e r } \pmb { \beta }$ (2) A sequence $\cdots \to X _ { n - 1 } \to X _ { n } \to X _ { n + 1 } \to \cdots$ ofhomomorphisms is said to be an exact sequence if it is exact at every $X _ { n }$ between a pair of homomorphisms. With this terminology, the pair of h?; morphisms $A { \stackrel { \psi } { } } B { \stackrel { \bullet } { } } c$ above is exact at B. We can also use this terminology to express the fact that for thes maps $\psi$ i s injective and $\varphi$ is surjective:
- **dependencies:** —


- **kind:** Proposition 22
- **source:** §10.5; printed pp. 378–407; extraction line 13692
- **statement/data:** Let A, B and C be R-modules over some ring R. 'Iben (1) The sequence $0 A \stackrel { \psi } { }$ B is exact (at A) if and only if $\pmb { \psi }$ is injective. (2) The sequence $B \stackrel { \varphi } { \to } C \to 0$ is exact (at C) if and only if $\varphi$ ({ is surjective.
- **dependencies:** —


- **kind:** Corollary 23
- **source:** §10.5; printed pp. 378–407; extraction line 13700
- **statement/data:** The sequence $0 \to A { \overset { \psi } { \to } } B { \overset { \varphi } { \to } } C \to 0$ is exact if and only if $\pmb { \psi }$ is injective, $\pmb { \varphi }$ is surjective, and image 1/f = ker ({J, i.e., B is an extension of $c$ by A.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 13702
- **statement/data:** The exact sequence $0 \to A \ { \overset { \psi } { \to } } \ B \ { \overset { \varphi } { \to } } \ C \to 0$ is called a short exact sequence. In terms of this notation, the extension problem can be stated succinctly as follows: given modules A and $c ,$ determine all the short exact sequences $$ 0 \longrightarrow A \stackrel {\psi} {\longrightarrow} B \stackrel {\varphi} {\longrightarrow} C \longrightarrow 0.\tag{10.9} $$
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 13776
- **statement/data:** Let $0 \to A \to B \to C \to 0 { \mathrm { ~ a n d } } 0 \to A ^ { \prime } \to B ^ { \prime } \to C ^ { \prime } \to 0$ be two short exact sequences of modules. (1) A homomorphism of short exact sequences is a triple $\alpha , \beta , \gamma$ of module homo morphisms such that the following diagram commutes: The homomorphism is an isomorphism of short exact sequences if $\alpha , \beta , \gamma$ are all isomorphisms, in which case the extensions B and $\pmb { B } ^ { \prime }$ are said to be isomorphic extensions. (2) The two exact sequences are called equivalent if $\begin{array} { r } { A = A ^ { \prime } , C = C ^ { \prime } , } \end{array}$ , and there is an isomorphism between them as in ( 1 ) that is the identity maps on A and C $( \texttt { i } . \texttt { e } . , \alpha$ and $\gamma$ are the identity). In this case the coresponding extensions B and $\pmb { B } ^ { \prime }$ are said to be equivalent extensions. If B and $B ^ { \prime }$ are isomorphic extensions then in particular B and $\pmb { B } ^ { \prime }$ are isomorphic as R-modules, but more is true: there is an R-module isomorphism between B and $\pmb { B ^ { \prime } }$ that restricts to an isomorphism from A to A' and induces an isomorphism on the quotients $c$ and $C ^ { \prime }$ . For a given A and C the condition that two extensions B and $B ^ { \prime }$ of C by A are equivalent is stronger still: there must exist an R-module isomorphism between B and $B ^ { \prime }$ that restricts to the identity map on A and induces the identity map on C. …
- **dependencies:** —


- **kind:** Proposition 24 (The Short Five Lemma)
- **source:** §10.5; printed pp. 378–407; extraction line 13830
- **statement/data:** (The Short Five Lemma) Let a, $\beta , \gamma$ be a homomorphism of short exact sequences (1) If a and $\gamma$ are injective then so is $\beta .$ . (2) I f a and $\gamma$ are smjective then so is $\beta .$ . (3) If a and $\gamma$ are isomorphisms then so is $\beta$ (and then the two sequences are isomorphic).
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 13846
- **statement/data:** (1) Let R be a ring and let $0 \to A { \overset { \psi } { \to } } B { \overset { \varphi } { \to } } C \to 0$ be a short exact sequence of R -modules. The sequence is said to be split if there is an R -module complement to $\psi ( A )$ in B . In this case, up to isomorphism, $B = A \oplus C$ (more precisely, $B = \psi ( A ) \oplus C ^ { \prime }$ for some submodule $C ^ { \prime }$ , and $C ^ { \prime }$ is mapped isomorphically onto C by cp: $\varphi ( C ^ { \prime } ) \cong C )$ (2) If $1 \to A \ { \stackrel { \psi } { \to } } \ B \ { \stackrel { \varphi } { \to } } \ C \to 1$ is a short exact sequence of groups, then the sequence is said to be split if there is a subgroup complement to $\psi ( A )$ in B . In this case, up to isomorphism, $B = A \rtimes C$ (more precisely, $B = \psi ( A ) \rtimes C ^ { \prime }$ for some subgroup $C ^ { \prime }$ , and $c$ is mapped isomorphically onto C by <p: $\varphi ( C ^ { \prime } ) \cong C )$ In either case the extension B is said to be a split extension of C by A. The question of whether an extension splits is the question of the existence of a complement to $\psi ( A )$ in B isomorphic (by $\varphi )$ to $^ { c , }$ , so the notion of a split extension may equivalently be phrased in the language of homomorphisms:
- **dependencies:** —


- **kind:** Proposition 25
- **source:** §10.5; printed pp. 378–407; extraction line 13854
- **statement/data:** The short exact sequence $0 \to A { \overset { \psi } { \to } } B { \overset { \varphi } { \to } } C \to 0$ of R -modules is split if and only if there is an R -module homomorphism $\mu : C \to B$ such that $\varphi \circ \mu$ is the identity map on $c .$ Similarly, the short exact sequence $1 \to A { \overset { \psi } { \to } } B { \overset { \varphi } { \to } } C \to 1$ of groups is split if and only if there is a group homomorphism $\mu : C \to B$ such that $\varphi \circ \mu$ is the identity map on C
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 13858
- **statement/data:** With notation as i n Proposition 25, any set map $\mu : C \to B$ such that $\varphi \circ \mu = \mathbf { i d }$ is called a section of $\varphi .$ If $\mu$ is a homommphism as in Proposition 25 then $\mu$ is called a splitting homomorphism for the sequence.
- **dependencies:** FC01-C10-U061


- **kind:** Proposition 26
- **source:** §10.5; printed pp. 378–407; extraction line 13890
- **statement/data:** Let $0 \to A { \overset { \psi } { \to } } B { \overset { \varphi } { \to } } C \to 0$ be a short exact sequence of modules (respectively, $1 \to A \ { \stackrel { \psi } { \to } } \ B \ { \stackrel { \varphi } { \to } } \ C \to 1$ a short exact sequence of groups). Then $\pmb { B } =$ $\psi ( A ) \oplus C ^ { \prime }$ for some submodule $C ^ { \prime }$ of B with $\varphi ( C ^ { \prime } ) \cong C$ (respectively, $B = \psi ( A ) \times C ^ { \prime }$ for some subgroup $C ^ { \prime }$ of B with $\varphi ( C ^ { \prime } ) \cong C )$ if and only if there is a homomorphism $\lambda : B A$ such that $\lambda \circ$ 1/ is the identity map on A .
- **dependencies:** —


- **kind:** Proposition 27
- **source:** §10.5; printed pp. 378–407; extraction line 13920
- **statement/data:** Let $D , L$ and M be R-modules and let $\psi : L \to M$ be an R-module homomorphism. Then the map $$ \begin{array}{c} \psi^ {\prime}: \operatorname{Hom} _ {R} (D, L) \longrightarrow \operatorname{Hom} _ {R} (D, M) \ f \longmapsto f ^ {\prime} = \psi \circ f \end{array} $$ is a homomorphism of abelian groups. If 1/ is injective, then $\psi ^ { \prime }$ is also injective, i.e., $$ \begin{array}{c} \text {if} 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \quad \text {is exact,} \ \text {then} 0 \longrightarrow \operatorname{Hom} _ {R} (D, L) \stackrel {\psi^ {\prime}} {\longrightarrow} \operatorname{Hom} _ {R} (D, M) \quad \text {is also exact.} \end{array} $$
- **dependencies:** —


- **kind:** Theorem 28
- **source:** §10.5; printed pp. 378–407; extraction line 13962
- **statement/data:** Let $D , L , M ,$ , and N be R-modules. If $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 \quad \text { is exact }, $$ then the associated sequence $$ 0 \to \operatorname{Hom} _ {R} (D, L) \xrightarrow {\psi^ {\prime}} \operatorname{Hom} _ {R} (D, M) \xrightarrow {\varphi^ {\prime}} \operatorname{Hom} _ {R} (D, N) \quad \text { is exact. }\tag{10.10} $$ A homomorphism $f : D \to N$ lifts to a homomorphism $F : D M$ if and only if $f \in { \bf H o m } _ { R } ( D , N )$ is in the image of $\varphi ^ { \prime }$ . In general $\varphi ^ { \prime } : { \mathrm { H o m } } _ { R } ( D , M ) \to { \mathrm { H o m } } _ { R } ( D , N )$ need not be smjective; the map $\varphi ^ { \prime }$ is smjective if and only if every homomorphism from D to N lifts to a homomorphism from D to $M ,$ , in which case the sequence (10) can be extended to a short exact sequence. The sequence (10) is exact for all R-modules D if and only if the sequence $$ 0 \to L \xrightarrow {\psi} M \xrightarrow {\varphi} N \quad \text { is exact. } $$
- **dependencies:** —


- **kind:** Proposition 29
- **source:** §10.5; printed pp. 378–407; extraction line 13996
- **statement/data:** Let D, L and N be R-modules. Then (1) H $\mathsf { I o m } _ { R } ( D , L \oplus N ) \cong \mathbf { H o m } _ { R } ( D , L ) \oplus \mathbf { H o m } _ { R } ( D , N )$ , and $$ \text { (2) } \operatorname{Hom} _ {R} (L \oplus N, D) \cong \operatorname{Hom} _ {R} (L, D) \oplus \operatorname{Hom} _ {R} (N, D). $$
- **dependencies:** —


- **kind:** Proposition 30
- **source:** §10.5; printed pp. 378–407; extraction line 14024
- **statement/data:** Let P be an R-module. Then the following are equivalent: (1) For any R-modules L, M, and N, if $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 $$ is a short exact sequence, then $$ 0 \longrightarrow \operatorname{Hom} _ {R} (P, L) \stackrel {\psi^ {\prime}} {\longrightarrow} \operatorname{Hom} _ {R} (P, M) \stackrel {\varphi^ {\prime}} {\longrightarrow} \operatorname{Hom} _ {R} (P, N) \longrightarrow 0 $$ is also a short exact sequence. (2) For any R-modules M and N, if $M \stackrel { \varphi } { \longrightarrow } N 0$ is exact, then every R-module homomorphism from P into N lifts to an R-module homomorphism into M, i.e., given $f \in \mathrm { H o m } _ { R } ( P , N )$ there is a lift ${ \cal F } \in \mathrm { H o m } _ { R } ( P , M )$ making the following diagram commute: {3) If $P$ is a quotient of the R -module M then P is isomorphic to a direct sumand of M, i.e., every short exact sequence $0 L M P 0$ splits. (4) P is a direct sumand of a free R-module.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 14072
- **statement/data:** An R-module P is called projective if it satisfies any of the equivalent conditions of Proposition 30. The third statement in Proposition 30 can be rephrased as saying that any module M that projects onto P has (an isomorphic copy of) P as a direct summand, which explains the terminology. The following result is imediate from Proposition 30 (and its proof):
- **dependencies:** FC01-C10-U067


- **kind:** Corollary 31
- **source:** §10.5; printed pp. 378–407; extraction line 14078
- **statement/data:** Free modules are projective. A finitely generated module is projective if and only if it is a direct sumand of a finitely generated free module. Every module is a quotient of a projective module. If D is fixed, then given any R -module X we have an associated abelian group Hom $\iota _ { R } ( D , X )$ . Further, an R-module homomorphism $\alpha : X Y$ induces an abelian group homomorphism $\alpha ^ { \prime } : { \mathrm { H o m } } _ { R } ( D , X ) \to { \mathrm { H o m } } _ { R } ( D , Y )$ , defined by $\alpha ^ { \prime } ( f ) = \alpha \circ f$ Put another way, the map ${ \bf H o m } _ { R } ( D , _ _ )$ is a covariant functor from the category of R-modules to the category of abelian groups (cf. Appendix II). Theorem 28 shows that applying this functor to the terms in the exact sequence $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 $$ produces an exact sequence $$ 0 \to \operatorname{Hom} _ {R} (D, L) \xrightarrow {\psi^ {\prime}} \operatorname{Hom} _ {R} (D, M) \xrightarrow {\varphi^ {\prime}} \operatorname{Hom} _ {R} (D, N). $$ This is refered to by saying that ${ \bf H o m } _ { R } ( D , _ _ )$ is a left exact functor. By Proposition 30, the functor ${ \bf H o m } _ { R } ( D , _ _ )$ is exact, i.e., always takes short exact sequences to short exact sequences, if and only if D is projective. We sumarize this as
- **dependencies:** FC01-C10-U065, FC01-C10-U067


- **kind:** Corollary 32
- **source:** §10.5; printed pp. 378–407; extraction line 14094
- **statement/data:** If D is an R-module, then the functor Hom $\cdot _ { R } ( D , _ )$ from the category of R-modules to the category of abelian groups is left exact. It is exact if and only if D is a projective R -module.
- **dependencies:** —


- **kind:** Theorem 33
- **source:** §10.5; printed pp. 378–407; extraction line 14186
- **statement/data:** Let $D , L , M .$ , and N be R-modules. If $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 \quad \text { is exact }, $$ then the associated sequence $$ 0 \to \operatorname{Hom} _ {R} (N, D) \xrightarrow {\varphi^ {\prime}} \operatorname{Hom} _ {R} (M, D) \xrightarrow {\psi^ {\prime}} \operatorname{Hom} _ {R} (L, D) \quad \text { is exact. }\tag{10.12} $$ A homomorphism $f : L \to D$ lifts to a homomorphism $F : M D$ if and only if $f \in { \mathrm { H o m } } _ { R } ( L , D )$ is in the image of $\psi ^ { \prime }$ . In general $\psi ^ { \prime }$ $: { \mathrm { H o m } } _ { R } ( M , D ) \to { \mathrm { H o m } } _ { R } ( L , D )$ need not be swjective; the map $\psi ^ { \prime }$ is swjective if and only if every homomorphism from $\cal L$ to D lifts to a homomorphism from $M$ to $\scriptstyle D ,$ in which case the sequence (12) can be extended to a short exact sequence. The sequence (12) is exact for all R-modules D if and only if the sequence $$ L \xrightarrow {\psi} M \xrightarrow {\varphi} N \to 0 \quad \text { is exact. } $$
- **dependencies:** —


- **kind:** Proposition 34
- **source:** §10.5; printed pp. 378–407; extraction line 14222
- **statement/data:** Let $Q$ be an R-module. Then the following are equivalent: (1) For any R -modules $L , M ,$ , and N , if $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 $$ is a short exact sequence, then $$ 0 \longrightarrow \operatorname{Hom} _ {R} (N, Q) \stackrel {\varphi^ {\prime}} {\longrightarrow} \operatorname{Hom} _ {R} (M, Q) \stackrel {\psi^ {\prime}} {\longrightarrow} \operatorname{Hom} _ {R} (L, Q) \longrightarrow 0 $$ is also a short exact sequence. (2) For any R-modules L and M, if $0 \to L { \xrightarrow { \psi } } M$ is exact, then every R-module homomorphism from L into Q lifts to an R-module homomorphism of M into Q, i.e., given $f \in { \bf H o m } _ { R } ( L , Q )$ there is a lift ${ \cal F } \in { \bf H o m } _ { R } ( M , Q )$ making the following diagram comute: (3) If $Q$ is a submodule of the R-module M then Q is a direct summand of M, i.e., every short exact sequence $0 \to Q \to M \to N \to 0$ splits.
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 14246
- **statement/data:** An R-module $Q$ is called injective if it satisfies any of the equivalent conditions of Proposition 34. The third statement in Proposition 34 can be rephrased as saying that any module M into which $Q$ injects has (an isomorphic copy of) $Q$ as a direct sumand, which explains the terminology. If D is fixed, then given any R -module X we have an associated abelian group ${ \bf H o m } _ { R } ( X , D )$ . Further, an R-module homomorphism $\alpha : X Y$ induces an abelian group homomorphism $\pmb { \alpha } ^ { \prime }$ : ${ \bf H o m } _ { R } ( Y , D ) { \bf H o m } _ { R } ( X , D )$ , defined by $\alpha ^ { \prime } ( f ) = f \circ \alpha ,$ that "reverses" the direction of the arrow. Put another way, the map ${ \bf H o m } _ { R } ( D , _ _ )$ is a contravariant functor from the category of R -modules to the category of abelian groups ( cf. Appendix II). Theorem 33 shows that applying this functor to the terms in the exact sequence $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 $$ produces an exact sequence $$ 0 \to \operatorname{Hom} _ {R} (N, D) \xrightarrow {\varphi^ {\prime}} \operatorname{Hom} _ {R} (M, D) \xrightarrow {\psi^ {\prime}} \operatorname{Hom} _ {R} (L, D). $$ This is refered to by saying that ${ \bf H o m } _ { R } ( _ , D )$ is a left exact (contravariant) functor. Note that the functor Hom $_ R ( _ , D )$ and the functor ${ \bf H o m } _ { R } ( D , _ )$ considered earlie are both left exact; …
- **dependencies:** FC01-C10-U072, FC01-C10-U071


- **kind:** Corollary 35
- **source:** §10.5; printed pp. 378–407; extraction line 14266
- **statement/data:** If D is an R-module, then the functor ${ \bf H o m } _ { R } ( _ { D } )$ from the category of R -modules to the category of abelian groups is left exact. It is exact if and only if D is an injective R-module.
- **dependencies:** —


- **kind:** Proposition 36
- **source:** §10.5; printed pp. 378–407; extraction line 14270
- **statement/data:** Let Q be an R -module. (1) (Baer's Criterion) The module Q is injective if and only if for every left ideal I of R any R -module homomorphism $g : I Q$ can be extended to an R -module homomorphism $G : R Q$ (2) If R i s a P.I.D. then Q is injective i f an d only i f $r Q = Q$ for every nonzero $r \in R .$ . In particular, a Z-module is injective if and only if it is divisible. When R is a P.I.D., quotient modules of injective R-modules are again injective.
- **dependencies:** —


- **kind:** Corollary 37
- **source:** §10.5; printed pp. 378–407; extraction line 14306
- **statement/data:** Every Z-module is a submodule of an injective Z-module.
- **dependencies:** —


- **kind:** Theorem 38
- **source:** §10.5; printed pp. 378–407; extraction line 14312
- **statement/data:** Let R be a ring with 1 and let M be an R-module. Then M is contained in an injective R -module.
- **dependencies:** —


- **kind:** Theorem 39
- **source:** §10.5; printed pp. 378–407; extraction line 14332
- **statement/data:** Suppose that $\pmb { D }$ is a right R-module and that L, M and N are left R-modules. If $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 \quad \text { is exact }, $$ then the associated sequence of abelian groups $$ D \otimes_ {R} L \xrightarrow {\mathbf {1} \otimes \psi} D \otimes_ {R} M \xrightarrow {\mathbf {1} \otimes \varphi} D \otimes_ {R} N \longrightarrow 0 \quad \text { is exact. }\tag{10.13} $$ If D is an $( S , R )$ -bimodule then ( 1 3) is an exact sequence of left S-modules. In particular, if ${ \pmb S } = { \pmb R }$ is a commutative ring, then ( 1 3) is an exact sequence of R-modules with respect to the standard R-module structures. The map 1 $\otimes \varphi$ is not in general injective, i.e., the sequence (13) canot in general be extended to a short exact sequence. The sequence ( 1 3) is exact for al right R-modules D if and only if $$ L \xrightarrow {\psi} M \xrightarrow {\varphi} N \to 0 \quad \text { is exact. } $$
- **dependencies:** —


- **kind:** Proposition 40
- **source:** §10.5; printed pp. 378–407; extraction line 14384
- **statement/data:** Let A be a right R -module. Then the following are equivalent: (1) For any left R-modules L, M, and N, if $$ 0 \longrightarrow L \stackrel {\psi} {\longrightarrow} M \stackrel {\varphi} {\longrightarrow} N \longrightarrow 0 $$ is a short exact sequence, then $$ 0 \longrightarrow A \otimes_ {R} L \stackrel {1 \otimes \psi} {\longrightarrow} A \otimes_ {R} M \stackrel {1 \otimes \varphi} {\longrightarrow} A \otimes_ {R} N \longrightarrow 0 $$ is also a short exact sequence. (2) For any left R-modules L and M, if $0 L \stackrel { \psi } { \longrightarrow } $ M is an exact sequence of left R-modules $( \mathrm { i . e . , } \psi : L \to M$ is injective) then $0 \to A \otimes _ { R } L \stackrel { 1 \otimes \psi } { \longrightarrow } A \otimes _ { R }$ M is an exact sequence of abelian groups (i.e., 1 $\otimes \psi : A \otimes _ { R } L \to A \otimes _ { R }$ M is injective).
- **dependencies:** —


- **kind:** Definition
- **source:** §10.5; printed pp. 378–407; extraction line 14402
- **statement/data:** A right R -module A is called flat if it satisfies either of the two equivalent conditions of Proposition 40. For a fixed right R-module D, the first part of Theorem 39 is refered to by saying that the functor $D \otimes _ { R } \underline { { \ : \ : } } _ { - }$ is right exact.
- **dependencies:** FC01-C10-U079, FC01-C10-U078


- **kind:** Corollary 41
- **source:** §10.5; printed pp. 378–407; extraction line 14406
- **statement/data:** If D is a right R-module, then the functor $D \otimes _ { R _ { \mathrm { ~ - ~ } } }$ from the category of left R-modules to the category of abelian groups is right exact. If D is an (S, R)­ bimodule (for example when $s = R$ is comutative and D is given the standard R -module structure), then $D \otimes _ { R } \underline { { \ : \ : } } _ { - }$ is a right exact functor from the category of left R-modules to the category of left S-modules. The functor is exact if and only if D is a flat R-module.
- **dependencies:** —


- **kind:** Corollary 42
- **source:** §10.5; printed pp. 378–407; extraction line 14410
- **statement/data:** Free modules are flat; more generally, projective modules are flat.
- **dependencies:** —


- **kind:** Theorem 43 (Adjoint Associativity)
- **source:** §10.5; printed pp. 378–407; extraction line 14434
- **statement/data:** (Adjoint Associativity) Let R and S be rings, let A be a right R -module, let B be an $( R , s )$ -bimodule and let C be a right S-module. Then there is an isomorphism of abelian groups: $$ \operatorname{Hom} _ {S} (A \otimes_ {R} B, C) \cong \operatorname{Hom} _ {R} (A, \operatorname{Hom} _ {S} (B, C)) $$ (the homomorphism groups are right module homomorphisms-note that $\mathrm { H o m } _ { S } ( B , C )$ has the structure of a right R-module, cf. the exercises). If $R = S$ is comutative this is an isomorphism of R-modules with the standard R-module structures.
- **dependencies:** —


- **kind:** Corollary 44
- **source:** §10.5; printed pp. 378–407; extraction line 14472
- **statement/data:** If R is comutative then the tensor product of two projective R -modules is projective.
- **dependencies:** —



- **kind:** Definition
- **source:** §11.1; printed pp. 408–414; extraction line 14684
- **statement/data:** (1) A subset S of V is called a set of linearly independent vectors if an equation $\alpha _ { 1 } \upsilon _ { 1 } + \alpha _ { 2 } \upsilon _ { 2 } + \cdot \cdot \cdot + \alpha _ { n } \upsilon _ { n } = 0$ with $\alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { n } \in F$ and $v _ { 1 } , v _ { 2 } , \ldots , v _ { n } \in S$ implies $\alpha _ { 1 } = \alpha _ { 2 } = \cdots = \alpha _ { n } = 0 \nonumber$ (2) A basis of a vector space V is an ordered set of linearly independent vectors which span V. In particular two bases will be considered different even if one is simply a rearangement of the other. This is sometimes refered to ordered basis.
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §11.1; printed pp. 408–414; extraction line 14696
- **statement/data:** Assume the set $\mathcal { A } = { v _ { 1 } , v _ { 2 } , \ldots , v _ { n } }$ spans the vector space V but no proper subset of A spans V. Then A is a basis of V. In particular, any finitely generatd (i.e., finitely spanned) vector space over F is a fre F -module.
- **dependencies:** —


- **kind:** Corollary 2
- **source:** §11.1; printed pp. 408–414; extraction line 14710
- **statement/data:** Assume the finite set A spans the vector space V. Then A contains a basis of V .
- **dependencies:** —


- **kind:** Theorem 3 (A Replacement Theorem)
- **source:** §11.1; printed pp. 408–414; extraction line 14714
- **statement/data:** (A Replacement Theorem) Assume $\mathcal { A } = { a _ { 1 } , a _ { 2 } , \ldots , a _ { n } }$ is a basis for V containing n elements and ${ b _ { 1 } , b _ { 2 } , \dots , b _ { m } }$ is a set of linearly independent vectors in V. Then there is an ordering $a _ { 1 } , a _ { 2 } , \ldots , a _ { n }$ such that for each $k \in { 1 , 2 , \ldots , m }$ the set ${ b _ { 1 } , b _ { 2 } , \dots , b _ { k } , a _ { k + 1 } , a _ { k + 2 } , \dots , a _ { n } }$ is a basis of V. I n other words, the elements $b _ { 1 } , b _ { 2 } , \ldots , b _ { m }$ can be used to successively replace the elements of the basis $\mathbfcal { A } ,$ still retaining a basis. In particular, $n \geq m$
- **dependencies:** —


- **kind:** Corollary 4
- **source:** §11.1; printed pp. 408–414; extraction line 14742
- **statement/data:** (1) Suppose V has a finite basis with n elements. Any set of linearly independent vectors has $\leq n$ elements. Any spaning set has $\geq n$ elements. (2) If V has some finite basis then any two bases of V have the same cardinality.
- **dependencies:** —


- **kind:** Definition
- **source:** §11.1; printed pp. 408–414; extraction line 14750
- **statement/data:** If V is a finitely generated F -module (i.e., has a finite basis) the cardinality of any basis is called the dimension of V and is denoted by dim $_ { F } V ,$ , or just dim V when F is clear from the context, and V is said to be finite dimensional over F. If V is not finitely generated, V is said to be infinite dimensional (written dim $V = \infty )$ .
- **dependencies:** —


- **kind:** Corollary 5 (Building-Up Lemma)
- **source:** §11.1; printed pp. 408–414; extraction line 14758
- **statement/data:** (Building-Up Lemma) If A is a set of linearly independent vectors in the finite dimensional space V then there exists a basis of V containing A.
- **dependencies:** —


- **kind:** Theorem 6
- **source:** §11.1; printed pp. 408–414; extraction line 14762
- **statement/data:** If V is an n dimensional vector space over F, then $V \cong F ^ { n }$ . In particular, any two finite dimensional vector spaces over F of the same dimension are isomorphic
- **dependencies:** —


- **kind:** Theorem 7
- **source:** §11.1; printed pp. 408–414; extraction line 14792
- **statement/data:** Let V be a vector space over F and let W be a subspace of V. Then $V / W$ is a vector space with dim $V = \dim W + \dim V / W$ (where if one side is infinite then both are).
- **dependencies:** —


- **kind:** Corollary 8
- **source:** §11.1; printed pp. 408–414; extraction line 14796
- **statement/data:** Let $\varphi : V U$ be a linear transformation of vector spaces over F. Then ker $\varphi$ is a subspace of $V , \varphi ( V )$ is a subspace of U and dim $V = \mathbf { d i m }$ ker $\varphi + \dim \varphi ( V )$
- **dependencies:** —


- **kind:** Corollary 9
- **source:** §11.1; printed pp. 408–414; extraction line 14800
- **statement/data:** Let $\varphi : V \to W$ be a linear transformation of vector spaces of the same finite dimension. Then the following are equivalent: (1) $\varphi$ is an isomorphism (2) $\varphi$ is injective, i.e., ker $\varphi = 0$ (3) $\varphi$ is suljective, i.e., $\varphi ( V ) = W$ (4) $\varphi$ sends a basis of V to a basis of W.
- **dependencies:** —


- **kind:** Definition
- **source:** §11.1; printed pp. 408–414; extraction line 14812
- **statement/data:** If $\varphi : V U$ is a linear transformation of vector spaces over ${ \pmb F } .$ , ker $\varphi$ is sometimes caled the null space of $\varphi$ and the dimension of ker rp is called the nullity of $\varphi .$ The dimension of $\varphi ( V )$ is called the rank of $\varphi .$ . If ker $\varphi = 0$ , the transformation is nonsingular
- **dependencies:** —


- **kind:** Construction
- **source:** §11.2; printed pp. 415–430; extraction line 14870
- **statement/data:** For bases B=(v_j) of V and E=(w_i) of W, the representing matrix M_B^E(φ)=(a_ij) is determined by φ(v_j)=Σ_i a_ij w_i.
- **dependencies:** —


- **kind:** Definition
- **source:** §11.2; printed pp. 415–430; extraction line 14890
- **statement/data:** The $m \times n$ matrix $A = ( a _ { i j } )$ associated to the linear transformation ${ \pmb \varphi }$ above is said to represent the linear transformation $\varphi$ with respect to the bases $\pmb { \cal B } , \pmb { \cal \varepsilon } .$ Similarly, $\varphi$ is the linear transformation represented by A with respect to the base $\pmb { B } ,$ $\varepsilon .$
- **dependencies:** —


- **kind:** Theorem 10
- **source:** §11.2; printed pp. 415–430; extraction line 14910
- **statement/data:** Let V be a vector space over F of dimension n and let W be a vector space over F of dimension m , with bases B, f respectively. Then the map ${ \bf H o m } _ { F } ( V , W ) $ $M _ { m \times n } ( F )$ from the space of linear transformations from V to W to the space of m x n matrices with coeficients in F defined by $\varphi \mapsto M _ { B } ^ { \varepsilon } ( \varphi )$ is a vector space isomorphism. In particular, there is a bijective corespondence between linear transformations and their associated matrices with respect to a fixed choice of bases.
- **dependencies:** —


- **kind:** Corollary 11
- **source:** §11.2; printed pp. 415–430; extraction line 14916
- **statement/data:** The dimension of Hom $_ { F } ( V , W )$ is (dim V ) (dim W).
- **dependencies:** —


- **kind:** Definition
- **source:** §11.2; printed pp. 415–430; extraction line 14920
- **statement/data:** An $m \times n$ matrix A is called nonsingular if $A x = 0$ with $x \in F ^ { n }$ implies ${ \boldsymbol { x } } = \mathbf { 0 }$ The connection of the term nonsingular applied to matrices and to linear transformations is the following: let $A = M _ { B } ^ { \varepsilon } ( \varphi )$ be the matrix iated to the linear transformation $\varphi$ (with some choice of bases $B , \varepsilon )$ . Then independntly of the choice of bases, the $m \times n$ matrix $A$ is nonsingular ifand only if the linear transformation $\varphi$ is a nonsingular linear transformation from the n-dimensional space V to the m-dimensional space $W$ (cf. the exercises). Assume now that $U , \pmb { V }$ and $W$ are all finite dimensional vector spaces over $F$ with ordered bases $\mathcal { D } , B$ and $\varepsilon$ respectively, where $_ B$ and $\varepsilon$ are as before and suppose $\mathcal { D } = { u _ { 1 } , u _ { 2 } , \ldots , u _ { k } }$ . Assume $\psi : U \to V$ and $\varphi : V \to W$ arelineart:ransformations. Their composite, $\varphi \circ \psi$ , is a linear transformation from $U$ to $W$ , so we can compute its matrix with respect to the appropriate bases; namely, $M _ { \mathcal { D } } ^ { \mathcal { E } } ( \varphi \circ \psi )$ is found by computing $$ \varphi \circ \psi (u _ {j}) = \sum_ {i = 1} ^ {m} \gamma_ {i j} w _ {i} $$ and putting the coeficients $\gamma _ { i j }$ down the $j ^ { \Uparrow }$ column of $M _ { \mathcal { D } } ^ { \mathcal { E } } ( \varphi \circ \psi )$ . …
- **dependencies:** —


- **kind:** Theorem 12
- **source:** §11.2; printed pp. 415–430; extraction line 14958
- **statement/data:** With notations as above, $M _ { D } ^ { \varepsilon } ( \varphi \circ \psi ) = M _ { B } ^ { \varepsilon } ( \varphi ) M _ { D } ^ { B } ( \psi )$ , i.e., with respect to a compatible choice of bases, the product of the matrices representing the linear transformations $\varphi$ and 1/f is the matrix representing the composite linear transformation $\varphi \circ \psi$
- **dependencies:** —


- **kind:** Corollary 13
- **source:** §11.2; printed pp. 415–430; extraction line 14960
- **statement/data:** Matrix multiplication is associative and distributive (whenever the dimensions are such as to make products defined). An $n \times n$ matrix A is nonsingular if and only if it is invertible.
- **dependencies:** —


- **kind:** Corollary 14
- **source:** §11.2; printed pp. 415–430; extraction line 14966
- **statement/data:** (1) If B is a basis of the n-dimensional space V, the map $\varphi \mapsto M _ { B } ^ { B } ( \varphi )$ is a ring and a vector space isomorphism of ${ \bf H o m } _ { F } ( V , V )$ onto the space $M _ { n } ( F )$ of $n \times n$ matrices with coeficients in F. (2) $G L ( V ) \cong G L _ { n } ( F )$ where dim $V ~ = n$ . In particular, if F is a finite field the order of the finite group $G L _ { n } ( F )$ (which equals $| G L ( V ) | )$ is given by the formula at the end of Section 1 .
- **dependencies:** —


- **kind:** Definition
- **source:** §11.2; printed pp. 415–430; extraction line 14976
- **statement/data:** If A is any $m \times n$ matrix with entries from F, the row rank (respectively, column rank) of A is the maximal number of linearly independent rows (respectively, columns) of A (where the rows or columns of A are considered as vectors in afine n-space, m-space, respectively). The relation between the rank of a matrix and the rank of the associated linear transformation is the following: the rank of $\varphi$ as a linear transformation equals the column rank of the matrix $M _ { B } ^ { \varepsilon } ( \varphi )$ (cf. the exercises). We shall also see that the row rank and the column rank of any matrix are the same.
- **dependencies:** —


- **kind:** Definition
- **source:** §11.2; printed pp. 415–430; extraction line 14982
- **statement/data:** Two $\pmb { n } \times \pmb { n }$ matrices A and B are said to be similar if there is an invertible (i.e., nonsingular) $\pmb { n } \times \pmb { n }$ matrix P such that $P ^ { - 1 } A P = B$ Two linear transformations $\varphi$ and $\psi$ from a vector space V to itself are said to be similar if there is a nonsingular linear transformation $\pmb { \xi }$ from V to V such that $\xi ^ { - 1 } \varphi \xi = \psi$ Suppose $\pmb { \imath }$ and $\varepsilon$ are two bases of the same vector space V and le $\varphi \in \mathrm { H o m } _ { F } ( V , V )$ Let I be the identity map from V to V and let $P = M _ { \varepsilon } ^ { B } ( I )$ be its associated matrix (in other words, write the elements of the basis $\varepsilon$ in terms of the basis $\pmb { B } -$ note the order - and use the resulting coordinates for the columns of the matrix P). Note that if $\boldsymbol { B } \neq \boldsymbol { \mathcal { E } }$ then $P$ is not the identity matrix. Then $P ^ { - 1 } M _ { B } ^ { B } ( \varphi ) P = M _ { \varepsilon } ^ { \varepsilon } ( \varphi )$ . If $[ v ] _ { B }$ is the $n \times 1$ matrix of coordinates for $v \in V$ with respect to the basis $B ,$ , and similarly $[ v ] _ { \varepsilon }$ is the $n \times 1$ matrix of coordinates for $v \in V$ with respect to the basis $\varepsilon ,$ then $[ \boldsymbol { \upsilon } ] _ { \mathcal { B } } = P [ \boldsymbol { \upsilon } ] _ { \mathcal { E } }$ . …
- **dependencies:** —


- **kind:** Construction
- **source:** §11.2; printed pp. 415–430; extraction line 14984
- **statement/data:** Change of basis: if P=M_E^B(id) for bases B,E of V, then the matrices of an endomorphism are related by conjugation P^{-1}AP.
- **dependencies:** —


- **kind:** Proposition 15
- **source:** §11.2; printed pp. 415–430; extraction line 15038
- **statement/data:** Let F be a subfield of the field K . If W is an m-dimensional vector space over F with basis $w _ { 1 } , \ldots , w _ { m }$ , then $K \otimes _ { F } W$ is an m-dimensional vector space over K with basis $1 \otimes w _ { 1 } , . . . , 1 \otimes w _ { m }$
- **dependencies:** —


- **kind:** Proposition 16
- **source:** §11.2; printed pp. 415–430; extraction line 15040
- **statement/data:** Let V and W be finite dimensional vector spaces over the field F with bases $\boldsymbol { v } _ { 1 } , \ldots , \boldsymbol { v } _ { n }$ and $\boldsymbol { w } _ { 1 } , \ldots , \boldsymbol { w } _ { m }$ respectively. Then $V \otimes _ { F } W$ is a vector space over F of dimension nm with basis $v _ { i } \otimes w _ { j } , 1 \leq i \leq n$ and $1 \leq j \leq m$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.2; printed pp. 415–430; extraction line 15070
- **statement/data:** Let $A = ( \alpha _ { i j } )$ and B be $r \times n$ and $s \times m$ matrices, respectively, with coeficients from any comutative ring. The Kronecker product or tensor product of A and $B ,$ denoted by ${ \pmb A } \otimes { \pmb B } ,$ is the $r s \times$ nm matrix consisting of an $r \times n$ block matrix whose $i , j$ block is the $s \times m$ matrix $\alpha _ { i j } B$ With this terminology we have
- **dependencies:** —


- **kind:** Proposition 17
- **source:** §11.2; printed pp. 415–430; extraction line 15074
- **statement/data:** Let $\varphi : V \to X$ and $\psi : W \to Y$ be linear transformations of finite dimensional vector spaces. Then the Kronecker product of matrices representing $\varphi$ and $\psi$ is a matrix representation of $\varphi \otimes \psi$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.3; printed pp. 431–434; extraction line 15540
- **statement/data:** (1) For V any vector space over F let $V ^ { * } = \operatorname { H o m } _ { F } ( V , F )$ the space of linear transformations from V to $F ,$ , called the dual space of V. Elements of $V ^ { \ast }$ are called linear functionals. (2) If $B = { v _ { 1 } , v _ { 2 } , \ldots , v _ { n } }$ is a basis of the finite dimensional space $V _ { \mathrm { { ; } } }$ , define $v _ { i } ^ { * } \in V ^ { * }$ for each $i \in { 1 , 2 , \ldots , n }$ by its action on the basis $\pmb { B } \mathrm { : }$ : $$ v _ {i} ^ {*} (v _ {j}) = \left{ \begin{array}{l l} 1, & \text { if } i = j \ 0, & \text { if } i \neq j \end{array} \right. \quad 1 \leq j \leq n.\tag{11.6} $$
- **dependencies:** —


- **kind:** Proposition 18
- **source:** §11.3; printed pp. 431–434; extraction line 15550
- **statement/data:** With notations as above, ${ v _ { 1 } ^ { * } , v _ { 2 } ^ { * } , \ldots , v _ { n } ^ { * } }$ is a basis of $V ^ { \ast }$ . In particular, if V is finite dimensional then $V ^ { \ast }$ has the same dimension as $V .$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.3; printed pp. 431–434; extraction line 15560
- **statement/data:** The basis ${ v _ { 1 } ^ { * } , v _ { 2 } ^ { * } , \ldots , v _ { n } ^ { * } }$ of $V ^ { \ast }$ is called the dual basis to ${ v _ { 1 } , v _ { 2 } , \ldots , v _ { n } }$ The exercises later show that if V is infinite dimensional it is always true that dim $V < \dim V ^ { * }$ . For spaces of arbitrary dimension the space $V ^ { \ast }$ is the "algebraic" dual space to V. If V has some additional structure, for example a continuous structure $( \tt i . e . ,$ a topology), then one may define other types of dual spaces (e.g., the continuous dual of $\bar { \nu } ,$ defined by requiring the linear functionals to be continuous maps). One has to be careful when reading other worlcs (particularly analysis books) to ascertain what qualifiers are implicit in the use of the terms "dual space" and "linear functional."
- **dependencies:** —


- **kind:** Definition
- **source:** §11.3; printed pp. 431–434; extraction line 15568
- **statement/data:** The dual of $V ^ { \ast }$ , namely $V ^ { \ast \ast }$ , is called the double dual or second dual of $V .$ Note that for a finite dimensional space V, dim $V = \dim V ^ { * }$ and also dim $V ^ { * } =$ dim $V ^ { \ast \ast }$ , hence V and $V ^ { \ast \ast }$ are isomorphic vector spaces. For infinte dimensional spaces dim $V < \dim V ^ { * * }$ (cf. the exercises) so V and $V ^ { \ast \ast }$ canot be isomorphic. In the case of finite dimensional spaces there is a natural, i.e., basis independent or coordinate free way of exhibiting the isomorphism between a vector space and its second dual. The basic idea, in a more general setting, is as follows: if X is any set and S is any set of functions of X into the field F, we normally think of choosing or fixing an $f \in S$ and computing $f ( x )$ as x ranges over all of X. Alternatively, we could think of fixing a point x in X and computing $f ( x )$ as f ranges over all of S. The latter process, called evaluation at x shows that for each $x \in X$ there is a function $E _ { x } : S \to F$ defined by $E _ { x } ( f ) = f ( x )$ (i.e., evaluate $f \mathrm { \bf ~ a t } x )$ . This gives a map $x \mapsto E _ { x }$ of X into the set of F -valued functions on S. If S "separates points" in the sense that for distinct points x and y of X there is some $f \in S$ such that $f ( x ) \neq f ( y )$ , then the map $x \mapsto E _ { x }$ is injective. …
- **dependencies:** —


- **kind:** Theorem 19
- **source:** §11.3; printed pp. 431–434; extraction line 15574
- **statement/data:** There is a natural injective linear transformation from V to $V ^ { \ast \ast }$ . If V is finite dimensional then this linear transformation is an isomorphism
- **dependencies:** —


- **kind:** Construction
- **source:** §11.3; printed pp. 431–434; extraction line 15604
- **statement/data:** For φ:V→W, the dual map φ*:W*→V* is f↦f∘φ.
- **dependencies:** FC01-C11-U028


- **kind:** Theorem 20
- **source:** §11.3; printed pp. 431–434; extraction line 15606
- **statement/data:** With notations as above, $\varphi ^ { * }$ is a linear transformation from $W ^ { * }$ to $V ^ { * }$ and $M _ { \mathcal { E } ^ { * } } ^ { B ^ { * } } ( \varphi ^ { * } )$ is the transpose of the matrix $M _ { B } ^ { \varepsilon } ( \varphi )$ (recall that the transpose of the matrix $( a _ { i j } )$ is the matrix $( a _ { j i } ) )$ 1
- **dependencies:** —


- **kind:** Corollary 21
- **source:** §11.3; printed pp. 431–434; extraction line 15634
- **statement/data:** For any matrix A, the row rank of A equals the column rank of A.
- **dependencies:** —


- **kind:** Definition
- **source:** §11.4; printed pp. 435–440; extraction line 15680
- **statement/data:** (1) A map $\varphi : V _ { 1 } \times V _ { 2 } \times \cdots \times V _ { n } \to W$ is called multilinear if for each fixed and fixed elements $v _ { j } \in V _ { j } , j \neq i$ , the map $$ V _ {i} \rightarrow W \quad \text { defined by } \quad x \mapsto \varphi (v _ {1}, \dots , v _ {i - 1}, x, v _ {i + 1}, \dots , v _ {n}) $$ is an R-module homomorphism. If $V _ { i } = V , i = 1 , 2 , \ldots , n$ , then $\varphi$ is called an n-multilinear function on $\boldsymbol { V } ,$ and if in addition $W = R , \varphi$ is called an $\pmb { n } -$ multilinear form on $\pmb { V } .$ (2) An n-multilinear function $\varphi$ on $V$ is called alternating if $\varphi ( v _ { 1 } , v _ { 2 } , \ldots , v _ { n } ) = 0$ whenever $\boldsymbol { v } _ { i } = \boldsymbol { v } _ { i + 1 }$ for some $i \in { 1 , 2 , \ldots , n - 1 } \mathrm { ( i . e . , } \varphi$ is zero whenever two consecutive arguments are equal). The function $\varphi$ is called symmetric if interchanging $v _ { i }$ and $v _ { j }$ for any i and $j$ in $( v _ { 1 } , v _ { 2 } , \ldots , v _ { n } )$ does not alter the value of $\varphi$ on this n-tuple. When $\pmb { n } = 2$ (respectively, 3) one says $\varphi$ is bilinear (respectively, trilinear) rather than 2-multilinear (respectively, 3-multilinear). Also, when n is clear from the context we shall simply say $\varphi$ is multilinear.
- **dependencies:** —


- **kind:** Proposition 22 [source OCR: Proposition 2]
- **source:** §11.4; printed pp. 435–440; extraction line 15698
- **statement/data:** Let $\varphi$ < be an n-multilinear alternating function on V. Then (1) $\varphi ( v _ { 1 } , \ldots , v _ { i - 1 } , v _ { i + 1 } , v _ { i } , v _ { i + 2 } , \ldots , v _ { n } ) \ = \ - \varphi ( v _ { 1 } , v _ { 2 } , \ldots , v _ { n } )$ for any $\textit { i } \in$ $\left{ 1 , 2 , \ldots , n { - } 1 \right}$ , i.e., the value of $\varphi$ on an n-tuple is negated if two adjacent components are interchanged. (2) For each $\sigma \in S _ { n } , \varphi ( v _ { \sigma ( 1 ) } , v _ { \sigma ( 2 ) } , \ldots , v _ { \sigma ( n ) } ) = \epsilon ( \sigma ) \varphi ( v _ { 1 } , v _ { 2 } , \ldots , v _ { n } )$ where $\epsilon ( \sigma )$ is the sign of the permutation $\pmb { \sigma }$ (cf. Section 3.5). (3) If $v _ { i } = v _ { j }$ for any pair ofdistinct i, $j \in \left{ 1 , 2 , \ldots , n \right}$ then $\varphi ( v _ { 1 } , v _ { 2 } , \ldots , v _ { n } ) = 0$ (4) If $v _ { i }$ is replaced by $\boldsymbol { v } _ { i } + \alpha \boldsymbol { v } _ { j }$ in $( v _ { 1 } , \ldots , v _ { n } )$ for any $j \neq i$ and any $\alpha \in R$ , the value of $\varphi$ on this n-tuple is not changed.
- **dependencies:** —


- **kind:** Proposition 23
- **source:** §11.4; printed pp. 435–440; extraction line 15722
- **statement/data:** Assume $\varphi$ is an n-multilinear alternating function on V and that for some $\boldsymbol { \upsilon } _ { 1 } , \boldsymbol { \upsilon } _ { 2 } , \ldots , \boldsymbol { \upsilon } _ { n }$ and $w _ { 1 } , w _ { 2 } , \dotsc , w _ { n } \in V$ and some $\alpha _ { i j } \in R$ we have $$ \begin{array}{c} w _ {1} = \alpha_ {1 1} v _ {1} + \alpha_ {2 1} v _ {2} + \dots + \alpha_ {n 1} v _ {n} \ w _ {2} = \alpha_ {1 2} v _ {1} + \alpha_ {2 2} v _ {2} + \dots + \alpha_ {n 2} v _ {n} \ \vdots \ w _ {n} = \alpha_ {1 n} v _ {1} + \alpha_ {2 n} v _ {2} + \dots + \alpha_ {n n} v _ {n} \end{array} $$ (we have purposely written the indices of the $\alpha _ { i j }$ in "column format"). Then $$ \varphi \left(w _ {1}, w _ {2}, \dots , w _ {n}\right) = \sum_ {\sigma \in S _ {n}} \epsilon (\sigma) \alpha_ {\sigma (1) 1} \alpha_ {\sigma (2) 2} \dots \alpha_ {\sigma (n) n} \varphi \left(v _ {1}, v _ {2}, \dots , v _ {n}\right). $$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.4; printed pp. 435–440; extraction line 15736
- **statement/data:** An n x n deteninant function on R is any function $$ \det: M _ {n \times n} (R) \to R $$ that satisfies the following two axioms: (1) det is an n-multilinear alternating form on $R ^ { n } ( = V )$ , where the n-tuples are the n columns of the matrices in $M _ { n \times n } ( R )$ (2) det {l) = 1 , where I is the $n \times n$ identity matrix. On occasion we shall write det $( A _ { 1 } , A _ { 2 } , \ldots , A _ { n } )$ for det A, where $A _ { 1 } , A _ { 2 } , \ldots , A _ { n }$ are the columns of A.
- **dependencies:** —


- **kind:** Convention
- **source:** §11.4; printed pp. 435–440; extraction line 15748
- **statement/data:** If A has columns A_1,…,A_n, the notation det(A_1,…,A_n) may be used for det A.
- **dependencies:** —


- **kind:** Theorem 24
- **source:** §11.4; printed pp. 435–440; extraction line 15750
- **statement/data:** There is a unique $n \times n$ determinant function on R and it can be computed for any $n \times n$ matrix $( \alpha _ { i j } )$ by the formula: $$ \det (\alpha_ {i j}) = \sum_ {\sigma \in S _ {n}} \epsilon (\sigma) \alpha_ {\sigma (1) 1} \alpha_ {\sigma (2) 2} \dots \alpha_ {\sigma (n) n}. $$
- **dependencies:** —


- **kind:** Corollary 25
- **source:** §11.4; printed pp. 435–440; extraction line 15764
- **statement/data:** The determinant is an n-mu1tilinear function of the rows of $M _ { n \times n } ( R )$ and for any $\pmb { n } \times \pmb { n }$ matrix A, det $A = \operatorname* { d e t } ( A ^ { t } )$ , where $A ^ { t }$ is the transpose of A.
- **dependencies:** —


- **kind:** Theorem 26 (Cramer's Rule)
- **source:** §11.4; printed pp. 435–440; extraction line 15780
- **statement/data:** (Cramer's Rule) If $A _ { 1 } , A _ { 2 } , \ldots , A _ { n }$ are the columns of an $n \times n$ matrix A and $B = \beta _ { 1 } A _ { 1 } + \beta _ { 2 } A _ { 2 } + \cdot \cdot \cdot + \beta _ { n } A _ { n }$ , for some $\beta _ { 1 } , \ldots , \beta _ { n } \in R$ , then $$ \beta_ {i} \det A = \det (A _ {1}, \dots , A _ {i - 1}, B, A _ {i + 1}, \dots , A _ {n}). $$
- **dependencies:** —


- **kind:** Corollary 27
- **source:** §11.4; printed pp. 435–440; extraction line 15788
- **statement/data:** If R is an integral domain, then det $\pmb { A } = \pmb { 0 }$ for $A \in M _ { n } ( R )$ if and only if the columns of A are R -linearly dependent as elements of the free R -module of rank n . Also, det $\pmb { A } = \pmb { 0 }$ if and only if the rows of A are R -linearly dependent.
- **dependencies:** —


- **kind:** Theorem 28
- **source:** §11.4; printed pp. 435–440; extraction line 15808
- **statement/data:** For matrices A, $B \in M _ { n \times n } ( R )$ , det $A B = ( \operatorname* { d e t } A ) ( \operatorname* { d e t } B )$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.4; printed pp. 435–440; extraction line 15818
- **statement/data:** Let $A = ( \alpha _ { i j } )$ be an $n \times n$ matrix. For each $i , j ,$ , let $A _ { i j }$ be the $n { - } 1 \times n { - } 1$ matrix obtained from A by deleting its $i ^ { \mathrm { t h } }$ row and $j ^ { \Uparrow }$ column (an $n { - } 1 \times n { - } 1$ minor of $A )$ . Then $( - 1 ) ^ { i + j }$ det $( A _ { i j } )$ is called the ij cofactor of A.
- **dependencies:** —


- **kind:** Theorem 29 (The Cofactor Expansion Formula along the $i ^ { \mathrm { t h } } r o w )
- **source:** §11.4; printed pp. 435–440; extraction line 15820
- **statement/data:** (The Cofactor Expansion Formula along the $i ^ { \mathrm { t h } } r o w )$ If $A = ( \alpha _ { i j } )$ i s an n x n matrix, then for each fixed $i \in { 1 , 2 , \ldots , n }$ the determinant of A can be computed from the formula $$ \det A = (- 1) ^ {i + 1} \alpha_ {i 1} \det A _ {i 1} + (- 1) ^ {i + 2} \alpha_ {i 2} \det A _ {i 2} + \dots + (- 1) ^ {i + n} \alpha_ {i n} \det A _ {i n}. $$
- **dependencies:** —


- **kind:** Theorem 30 (Cofactor Fonula for the Inverse of a Matrix)
- **source:** §11.4; printed pp. 435–440; extraction line 15832
- **statement/data:** (Cofactor Fonula for the Inverse of a Matrix) Let $A = ( \alpha _ { i j } )$ be an n x n matrix and let B be the transpose of its matrix of cofactors, i.e., $B = ( \beta _ { i j } )$ , where $\beta _ { i j } = ( - 1 ) ^ { i + j }$ det $A _ { j i } , 1 \le i , j \le n$ . Then $A B = B A = ( \operatorname* { d e t } A ) I$ . Moreover, det A is a unit in R if and only if A is a unit in $M _ { n \times n } ( R )$ ; in this case the matrix ${ \frac { 1 } { \operatorname* { d e t } A } } B$ is the inverse of A.
- **dependencies:** —


- **kind:** Construction
- **source:** §11.5; printed pp. 441–455; extraction line 15894
- **statement/data:** For an R-module M, T^k(M)=M^{⊗k} for k≥1 and T^0(M)=R; their direct sum carries multiplication by concatenating tensors.
- **dependencies:** —


- **kind:** Theorem 31
- **source:** §11.5; printed pp. 441–455; extraction line 15902
- **statement/data:** If M is any R-module over the commutative ring R then (1) $\mathcal { T } ( M )$ is an R-algebra containing M with multiplication defined by mapping $$ (m _ {1} \otimes \dots \otimes m _ {i}) (m _ {1} ^ {\prime} \otimes \dots \otimes m _ {j} ^ {\prime}) = m _ {1} \otimes \dots \otimes m _ {i} \otimes m _ {1} ^ {\prime} \otimes \dots \otimes m _ {j} ^ {\prime} $$ and extended to sums via the distributive laws. With respect to this multiplica tion $\mathcal { T } ^ { i } ( M ) \mathcal { T } ^ { j } ( M ) \subseteq \mathcal { T } ^ { i + j } ( M )$ (2) (Universal Property) If A i s any R-algebra and $\varphi : M \to A$ is an R-module homomorphism, then there is a unique R-algebrahomomorphism $\Phi : \mathcal { T } ( M ) $ A such that $\Phi | _ { M } = \varphi$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.5; printed pp. 441–455; extraction line 15934
- **statement/data:** The ring T(M) is called the tensor algebra of M.
- **dependencies:** —


- **kind:** Proposition 32
- **source:** §11.5; printed pp. 441–455; extraction line 15936
- **statement/data:** Let V be a finite dimensional vector space over the field F with basis $B = { v _ { 1 } , \ldots , v _ { n } }$ . Then the k-tensors $$ \boldsymbol {v} _ {i _ {1}} \otimes \boldsymbol {v} _ {i _ {2}} \otimes \dots \otimes \boldsymbol {v} _ {i _ {k}} \quad \text { with } \boldsymbol {v} _ {i _ {j}} \in \mathcal {B} $$ are a vector space basis of ${ \mathcal { T } } ^ { k } ( V )$ over F (with the understanding that the basis vector is the element $1 \in F$ when $k = 0 )$ . In particular, dim $_ { F } ( \mathcal { T } ^ { k } ( V ) ) = n ^ { k }$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.5; printed pp. 441–455; extraction line 15956
- **statement/data:** (1) A ring S is called a graded ring if it is the direct sum of additive subgroups: ${ \cal S } = { \cal S } _ { 0 } \oplus { \cal S } _ { 1 } \oplus { \cal S } _ { 2 } \oplus \cdot \cdot \cdot$ · such that $S _ { i } S _ { j } \subseteq S _ { i + j }$ for all $i , j \geq 0$ . The elements of $s _ { k }$ are said to be homogeneous of degree $k ,$ and $s _ { k }$ is called the homogeneous component of S of degree k. (2) An ideal I of the graded ring S is called a graded ideal if $I = \oplus _ { k = 0 } ^ { \infty } ( I \cap S _ { k } )$ (3) A ring homomorphism $\varphi : S T$ between two graded rings is called a homomorphism of graded rings if it respects the grading structures on S and T, i.e., if $\varphi ( S _ { k } ) \subseteq T _ { k }$ for k = 0, 1 , 2 , . . . .
- **dependencies:** —


- **kind:** Proposition 33
- **source:** §11.5; printed pp. 441–455; extraction line 15976
- **statement/data:** Let S be a graded ring, let I be a graded ideal in S and let $I _ { k } = I \cap S _ { k }$ for all $k \geq 0$ . Then $S / I$ is naturally a graded ring whose homogeneous component of degree k is isomorphic to $S _ { k } / I _ { k }$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.5; printed pp. 441–455; extraction line 15990
- **statement/data:** The symmetric algebra of an R -module M is the R -algebra obtained by taking the quotient of the tensor algebra $\mathcal { T } ( M )$ by the idea $c ( M )$ generated by all elements of the form $m _ { 1 } \otimes m _ { 2 } - m _ { 2 } \otimes m _ { 1 }$ , for al $m _ { 1 } , m _ { 2 } \in M .$ . The symmetric algebra ${ \mathcal { T } } ( M ) / C ( M )$ is denoted by $\pmb { S } ( \pmb { M } )$ The tensor algebra $\tau ( M )$ is generated as a ring by $R = \mathcal { T } ^ { 0 } ( M )$ and $M = \mathcal { T } ^ { 1 } ( M )$ and these elements comute in the quotient ring $\pmb { S } ( \pmb { M } )$ by definition. It follows that the symetric algebra $s ( M )$ is a comutative ring. The ideal $\mathcal { C } ( M )$ is generated by homogeneous tensors of degree 2 and it follows easily that $\mathcal { C } ( M )$ is a graded ideal. Then by Proposition 33 the symmetric algebra is a graded ring whose homogeneous component of degree k is $\mathcal { S } ^ { k } ( \mathcal { M } ) = \mathcal { T } ^ { k } ( \bar { M } ) / \mathcal { C } ^ { k } ( M )$ . Since $\mathcal { C } ( M )$ consists of k-tensors with $k \geq 2 ,$ we have $\mathcal { C } ( M ) \cap M = 0$ and so the image of $M = \mathcal { T } ^ { 1 } ( M )$ in $\mathcal { S } ( M )$ is isomorphic to M . Identifying M with its image we see that $S ^ { 1 } ( M ) = M$ and the symetric algebra contains M. In a similar way $\bar { S ^ { 0 } } ( M ) = R ,$ so the symetric algebra is also an R-algebra. The R-module $S ^ { k } ( M )$ is called the $k ^ { \mathrm { { f h } } }$ symmetric power of M. …
- **dependencies:** FC01-C11-U054


- **kind:** Theorem 34
- **source:** §11.5; printed pp. 441–455; extraction line 15996
- **statement/data:** Let M be an R-module over the comutative ring R and let $\cal { S } ( M )$ be its symmetric algebra. (1) The $k ^ { \mathrm { { f h } } }$ symmetric power, $S ^ { k } ( M )$ , of M is equal to M ® · . · ® M (k factors) modulo the submodule generated by all elements of the form $$ (m _ {1} \otimes m _ {2} \otimes \dots \otimes m _ {k}) - (m _ {\sigma (1)} \otimes m _ {\sigma (2)} \otimes \dots \otimes m _ {\sigma (k)}) $$ for all $m _ { i } \in M$ and all permutations u in the symetric group $S _ { k }$ . (2) (Universal Property for Symmetric Multilinear Maps) $\operatorname { I f } \varphi : M \times \cdots \times M \to N$ is a symetric k-multilinear map over R then there is a unique R-module homomorphism $\Phi : { \mathcal { S } } ^ { k } ( M ) \to N$ such that $\varphi = \Phi \circ \iota ,$ , where $$ \iota : M \times \dots \times M \rightarrow \mathcal {S} ^ {k} (M) $$ is the map defined by $$ \iota (m _ {1}, \dots , m _ {k}) = m _ {1} \otimes \dots \otimes m _ {n} \bmod \mathcal {C} (M). $$ (3) (Universal Property for maps to commutative R -algebras) If A is any comutative R-algebra and $\varphi : M \to A$ is an R-module homomorphism, then there is a unique R -algebra homomorphism $\Phi : { \mathcal { S } } ( M ) \to A$ such that $\Phi | _ { M } = \varphi$
- **dependencies:** —


- **kind:** Corollary 35
- **source:** §11.5; printed pp. 441–455; extraction line 16030
- **statement/data:** Let V be an n-dimensional vector space over the field F. Then $s ( V )$ is isomorphic as a graded F -algebra to the ring of polynomials in n variables over ${ \cal F } \left( \mathrm { i . e . } \right.$ the isomorphism is also a vector space isomorphism from ${ \mathcal { S } } ^ { k } ( V )$ onto the space of al homogeneous polynomials of degree k). In particular, dim $_ { F } ( S ^ { k } ( V ) ) = \binom { k + \bar { n } - 1 } { n - 1 }$
- **dependencies:** —


- **kind:** Definition
- **source:** §11.5; printed pp. 441–455; extraction line 16038
- **statement/data:** The exterior algebra of an R -module M is the R -algebra obtained by taking the quotient of the tensor algebra $\mathcal { T } ( M )$ by the ideal $A ( M )$ generated by al elements of the form m 0 m, for $m \in M$ . The exterior algebra $\mathcal { T } ( M ) / \mathcal { A } ( M )$ is denoted by $\Lambda ( M )$ and the image of $m _ { 1 } { \otimes } m _ { 2 } { \otimes } \cdots { \otimes } m _ { k } \mathrm { i n } \bigwedge ( M )$ is denoted by $m _ { 1 } \wedge m _ { 2 } \wedge \cdots \wedge m _ { k }$ As with the symetric algebra, the ideal $\pmb { \mathcal { A } } ( \pmb { M } )$ is generated by homogeneous elements hence is a graded ideal. By Proposition 33 the exterior algebra is graded, with $k ^ { \mathrm { t h } }$ homogeneous component $\textstyle \bigwedge ^ { k } ( M ) = { \mathcal { T } } ^ { k } ( M ) / { \mathcal { A } } ^ { k } ( M )$ . We can again identify R with $\wedge ^ { \bullet } ( M )$ and M with $\Lambda ^ { 1 } ( M )$ and so consider M as an R-submodule of the R-algebra $\Lambda ( M )$ . The R-module $\textstyle \bigwedge ^ { k } ( M )$ is called the $k ^ { \mathrm { { t h } } }$ exterior power of M. The multiplication $$ \left(m _ {1} \wedge \dots \wedge m _ {i}\right) \wedge \left(m _ {1} ^ {\prime} \wedge \dots \wedge m _ {j} ^ {\prime}\right) = m _ {1} \wedge \dots \wedge m _ {i} \wedge m _ {1} ^ {\prime} \wedge \dots \wedge m _ {j} ^ {\prime} $$ in the exterior algebra is called the wedge (or exterior) product. …
- **dependencies:** FC01-C11-U054


- **kind:** Construction
- **source:** §11.5; printed pp. 441–455; extraction line 16048
- **statement/data:** Multiplication in the exterior algebra is the wedge product; simple wedges are alternating, in particular a repeated adjacent factor gives zero.
- **dependencies:** —


- **kind:** Theorem 36
- **source:** §11.5; printed pp. 441–455; extraction line 16062
- **statement/data:** Let M be an R-module over the comutative ring R and let $\wedge ( M )$ be its exterior algebra. (1) The $k ^ { \mathrm { { f h } } }$ exterior power, $\textstyle \bigwedge ^ { k } ( M )$ , of M is equal to $M \otimes \cdots \otimes M$ (k factors) modulo the submodule generated by all elements of the form $$ m _ {1} \otimes m _ {2} \otimes \dots \otimes m _ {k} \quad \text { where } m _ {i} = m _ {j} \text { for some } i \neq j. $$ In particular, $$ m _ {1} \wedge m _ {2} \wedge \dots \wedge m _ {k} = 0 \quad \text { if } m _ {i} = m _ {j} \text { for some } i \neq j. $$ (2) (Universal PropertyforAltematingMultilinearMaps) If $\varphi : M \times \cdots \times M \to N$ is an alternating k-multilnear map then there is a unique R-module homomorphism $\Phi : { \textstyle \bigwedge } ^ { k } ( M ) \to N$ such that $\varphi = \Phi \circ \pmb { \iota } _ { \pmb { \iota } }$ where $$ \iota : M \times \dots \times M \rightarrow \bigwedge^ {k} (M) $$ is the map defined by $$ \iota (m _ {1}, \dots , m _ {k}) = m _ {1} \wedge \dots \wedge m _ {k}. $$
- **dependencies:** —


- **kind:** Corollary 37
- **source:** §11.5; printed pp. 441–455; extraction line 16138
- **statement/data:** Let V be a finite dimensional vector space over the field F with basis $B = { v _ { 1 } , \ldots , v _ { n } }$ . Then the vectors $$ v _ {i _ {1}} \wedge v _ {i _ {2}} \wedge \dots \wedge v _ {i _ {k}} \quad \text { for } 1 \leq i _ {1} n$ (when $k = 0$ the basis vector is the element $1 \in F )$ . In particular, dim $\begin{array} { r } { { \ v { r } } _ { F } ( \bigwedge ^ { k } ( V ) ) = { \binom { n } { k } } } \end{array}$
- **dependencies:** —


- **kind:** Proposition 38
- **source:** §11.5; printed pp. 441–455; extraction line 16200
- **statement/data:** If $\varphi$ is an endomorphism on a n-dimensional vector space V, then ${ \textstyle \bigwedge } ^ { n } ( \varphi ) ( w ) = \mathbf { d e t } ( \varphi ) w$ for all $w \in { \textstyle \bigwedge } ^ { n } ( V )$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §11.5; printed pp. 441–455; extraction line 16234
- **statement/data:** (1) An element $z \in { \mathcal { T } } ^ { k } ( M )$ is caled a symmetric k-tensor if $\sigma z = z$ for al $\sigma$ in the symetric group $s _ { k }$ . (2) An element $z \in { \mathcal { T } } ^ { k } ( M )$ is called an alternating k-tensor if $\sigma z = \epsilon ( \sigma ) z$ for al (]' in the symetric group $s _ { k }$ where $\epsilon ( \sigma )$ is the sign, ± 1 ' of the permutation (]' . It i s immediate from the definition that the collection of symmetric (respectively, alternating) k-tensors is an R-submodule of the module of all k-tensors
- **dependencies:** —


- **kind:** Proposition 39
- **source:** §11.5; printed pp. 441–455; extraction line 16248
- **statement/data:** Let a be an element in the symetric group $s _ { k }$ and let $\epsilon ( \sigma )$ be the sign of the permutation $\sigma$ . Then (1) for every $w \in { \mathcal { S } } ^ { k } ( M )$ we have $\sigma w = w ,$ and (2) for every $w \in { \textstyle \bigwedge } ^ { k } ( M )$ we have $\sigma w = \epsilon ( \sigma ) w .$
- **dependencies:** —


- **kind:** Construction
- **source:** §11.5; printed pp. 441–455; extraction line 16276
- **statement/data:** For z∈T^k(M), Sym(z)=Σ_{σ∈S_k}σz and Alt(z)=Σ_{σ∈S_k}ε(σ)σz are symmetrization and skew-symmetrization.
- **dependencies:** —


- **kind:** Proposition 40
- **source:** §11.5; printed pp. 441–455; extraction line 16286
- **statement/data:** Suppose k ! is a unit in the ring R and M is an R -module. Then (1) The map $( 1 / k ! ) S y m$ induces an R-module isomorphism between the $k ^ { \mathrm { t h } }$ symmetric power of M and the R-submodule of symetric k-tensors: $$ \frac {1}{k !} \text { Sym }: \mathcal {S} ^ {k} (M) \cong {\text { symmetric } k \text {-tensors} }. $$ (2) The map ( 1 / k !)Alt induces an R-module isomorphism between the $k ^ { \mathrm { t h } }$ exterior power of M and the R-submodule of alternating k-tensors: $$ \frac {1}{k !} A l t: \bigwedge^ {k} (M) \cong {\text { alternating } k \text {-tensors} }. $$
- **dependencies:** —


- **kind:** Named comparison
- **source:** §11.5; printed pp. 441–455; extraction line 16318
- **statement/data:** When k! is invertible, the kth exterior power may equivalently be realized as the submodule of alternating k-tensors; multiplication is tensor product followed by projection to alternating tensors.
- **dependencies:** —



- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16452
- **statement/data:** (1) The left R-module M is said to be a Noetherian R-module or to satisfy the ascending chain condition on submodules (or A. C. C. on submodules) if there are no infinite increasing chains of submodules, i.e., whenever $$ M _ {1} \subseteq M _ {2} \subseteq M _ {3} \subseteq \dots $$ is an increasing chain of submodules of M, then there is a positive integer m such that for all $k \geq m$ $M _ { k } = M _ { m }$ (so the chain becomes stationary at stage m: $M _ { m } = M _ { m + 1 } = M _ { m + 2 } = \ldots ) .$ (2) The ring R is said to be Noetherian if it is Noetherian as a left module over itself, i.e., if there are no infinite increasing chains of left ideals in R . One can formulate analogous notions of A. C. C. on right and on two-sided ideals in a (possibly noncommutative) ring R. For noncommutative rings these properties need not be related.
- **dependencies:** —


- **kind:** Theorem 1
- **source:** §12.1; printed pp. 458–471; extraction line 16466
- **statement/data:** Let R be a ring and let M be a left R-module. Then the following are equivalent: (1) M is a Noetherian R-module. (2) Every nonempty set of submodules of M contains a maximal element under inclusion. (3) Every submodule of M is finitely generated
- **dependencies:** —


- **kind:** Corollary 2
- **source:** §12.1; printed pp. 458–471; extraction line 16486
- **statement/data:** If R is a P.I.D. then every nonempty set of ideals of R has a maximal element and R is a Noetherian ring.
- **dependencies:** —


- **kind:** Proposition 3
- **source:** §12.1; printed pp. 458–471; extraction line 16494
- **statement/data:** Let R be an integral domain and let M be a free R -module of rank $n \ < \ \infty .$ . Then any $n + 1$ elements of M are R-linearly dependent, i.e., for any $y _ { 1 } , y _ { 2 } , \ldots , y _ { n + 1 } \in M$ there are elements $r _ { 1 } , r _ { 2 } , \ldots , r _ { n + 1 } \in R$ , not all zero, such that $$ r _ {1} y _ {1} + r _ {2} y _ {2} + \dots + r _ {n + 1} y _ {n + 1} = 0. $$
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16510
- **statement/data:** For an integral domain R and R-module M, Tor(M)={x∈M | rx=0 for some nonzero r∈R} is the torsion submodule; M is torsion-free when Tor(M)=0, and any submodule of Tor(M) is a torsion submodule.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16512
- **statement/data:** For a submodule N of an R-module M, Ann(N)={r∈R | rn=0 for every n∈N} is its annihilator ideal.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16520
- **statement/data:** For any integral domain R the rank of an R-module M is the maximum number of R-linearly independent elements of M. The preceding proposition states that for a free R -module M over an integral domain the rank of a submodule is bounded by the rank of M. This notion of rank agrees with previous uses of the same term. If the ring $R \ : = \ : F$ is a field, then the rank of an R-module M is the dimension of M as a vector space over F and any maximal set of F -linearly independent elements is a basis for M. For a general integral domain, however, an R-module M of rank n need not have a "basis," i.e., need not be a free R-module even if M is torsion free, so some care is necessary with the notion of rank, particularly with respect to the torsion elements of M. Exercises I to 6 and 20 give an alternate characterization of the rank and provide some examples of (torsion free) R -modules (of rank 1 ) that are not free.
- **dependencies:** —


- **kind:** Theorem 4
- **source:** §12.1; printed pp. 458–471; extraction line 16526
- **statement/data:** Let R be a Principal Ideal Domain, let M be a free R-module of finite rank n and let N be a submodule of M. Then (1) N is free of rank $m , m \leq n$ and (2) there exists a basis $y _ { 1 } , y _ { 2 } , \ldots , y _ { n }$ of M so that $a _ { 1 } y _ { 1 } , a _ { 2 } y _ { 2 } , \ldots , a _ { m } y _ { m }$ is a basis of N where $a _ { 1 } , a _ { 2 } , \ldots , a _ { m }$ are nonzero elements of R with the divisibility relations $$ a _ {1} \mid a _ {2} \mid \dots \mid a _ {m}. $$
- **dependencies:** —


- **kind:** Theorem 5 (Fundamental Theorem, Existence: Invariant Factor Form)
- **source:** §12.1; printed pp. 458–471; extraction line 16600
- **statement/data:** (Fundamental Theorem, Existence: Invariant Factor Form) Let R be a P.I.D. and let M be a finitely generated R-module. (1) Then M is isomorphic to the direct sum of finitely many cyclic modules. More precisely, $$ M \cong R ^ {r} \oplus R / (a _ {1}) \oplus R / (a _ {2}) \oplus \dots \oplus R / (a _ {m}) $$ for some integer $r \geq 0$ and nonzero elements $a _ { 1 } , a _ { 2 } , \ldots , a _ { m }$ of R which are not units in R and which satisfy the divisibility relations $$ a _ {1} \mid a _ {2} \mid \dots \mid a _ {m}. $$ (2) M is torsion free if and only if M is free. (3) In the decomposition in ( 1 ), $$ \operatorname{Tor} (M) \cong R / \left(a _ {1}\right) \oplus R / \left(a _ {2}\right) \oplus \dots \oplus R / \left(a _ {m}\right). $$ In particular M is a torsion module if and only if $\mathbf { r } = \mathbf { 0 }$ and in this case the annihilator of M is the ideal $( a _ { m } )$
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16660
- **statement/data:** The integer r in Theorem 5 is called the free rank or the Betti number of M and the elements $a _ { 1 } , a _ { 2 } , \ldots , a _ { m } \in R$ (defined up to multiplication by units in R) are called the invariant factors of M.
- **dependencies:** FC01-C12-U009


- **kind:** Theorem 6 (Fundamental Theorem, Existence: Elementary Divisor Form)
- **source:** §12.1; printed pp. 458–471; extraction line 16682
- **statement/data:** (Fundamental Theorem, Existence: Elementary Divisor Form) Let R be a P.I.D. and let M be a finitely generated R-module. Then M is the direct sum of a finite number of cyclic modules whose annihilators are either (0) or generated by powers of primes in R, i.e. , $$ M \cong R ^ {r} \oplus R / (p _ {1} ^ {\alpha_ {1}}) \oplus R / (p _ {2} ^ {\alpha_ {2}}) \oplus \dots \oplus R / (p _ {t} ^ {\alpha_ {t}}) $$ where $r \geq 0$ is an integer and $p _ { 1 } ^ { \alpha _ { 1 } } , \ldots , p _ { t } ^ { \alpha _ { t } }$ are positive powers of (not necessaril distinct) primes in R . We proved Theorem 6 by using the prime power factors of the invariant factors for M. In fact we shall see that the decomposition of M into a direct sum of cyclic modules whose annihilators are (0) or prime powers as in Theorem 6 is unique, i.e., the integer r and the ideals $( p _ { 1 } ^ { \alpha _ { 1 } } ) , \ldots , ( \bar { p _ { t } ^ { \alpha _ { t } } } )$ are uniquely defined for M. These prime powers are given a name:
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16692
- **statement/data:** Let R be a P.I.D. and let M be a finitely generated R-module as in Theorem 6. The prime powers $p _ { 1 } ^ { \alpha _ { 1 } } , \ldots , p _ { t } ^ { \alpha _ { t } }$ (defined up to multiplication by units in R) are called the elementary divisors of M. Suppose M is a finitely generated torsion module over the Principal Ideal Domain R. lffor the distinct primes $p 1 , p 2 , \ldots , p _ { n }$ occuring in the decomposition inTheorem 6 we group together all the cyclic factors coresponding to the same prime $p _ { i }$ we see in particular that M can be written as a direct sum $$ M = N _ {1} \oplus N _ {2} \oplus \dots \oplus N _ {n} $$ where $N _ { i }$ consists of all the elements of M which are annihilated by some power of the prime $p _ { i }$ . This result holds also for modules over R which may not be finitely generated:
- **dependencies:** FC01-C12-U011


- **kind:** Theorem 7 (The Primary Decomposition Theorem)
- **source:** §12.1; printed pp. 458–471; extraction line 16702
- **statement/data:** (The Primary Decomposition Theorem) Let R be a P.I.D. and let M be a nonzero torsion R-module (not necessarily finitely generated) with nonzero annihilator a . Suppose the factorization of a into distinct prime powers in R is $$ a = u p _ {1} ^ {\alpha_ {1}} p _ {2} ^ {\alpha_ {2}} \dots p _ {n} ^ {\alpha_ {n}} $$ and let $N _ { i } = { x \in M \mid p _ { i } ^ { \alpha _ { i } } x = 0 } , 1 \leq i \leq n$ . Then $N _ { i }$ is a submodule of M with annihlator $p _ { i } ^ { \alpha _ { i } }$ and is the submodule of M of all elements annihilated by some power of $p _ { i }$ . We have $$ M = N _ {1} \oplus N _ {2} \oplus \dots \oplus N _ {n}. $$ If M is finitely generated then each $N _ { i }$ is the direct sum of finitely many cyclic modules whose annihlators are divisors of $p _ { i } ^ { \alpha _ { i } }$
- **dependencies:** —


- **kind:** Definition
- **source:** §12.1; printed pp. 458–471; extraction line 16718
- **statement/data:** The submodule $N _ { i }$ in the previous theorem is called the Pi -primary component of M. Notice that with this terminology the elementary divisors of a finitely generated module M are just the invariant factors of the primary components of Tor(M).
- **dependencies:** —


- **kind:** Lemma 8
- **source:** §12.1; printed pp. 458–471; extraction line 16726
- **statement/data:** Let R be a P.I.D. and let p be a prime in R. Let F denote the field $R / ( p )$ (1) Let $M = R ^ { r }$ . Then $M / p M \cong F ^ { r }$ (2) Let $M = R / ( a )$ where a i s a nonzero element of R. Then $$ M / p M \cong \left{ \begin{array}{l l} F & \text { if } p \text { divides } a \text { in } R \ 0 & \text { if } p \text { does not divide } a \text { in } R. \end{array} \right. $$ (3) Let $M = R { \bigl / } ( a _ { 1 } ) \oplus R { \bigl / } ( a _ { 2 } ) \oplus \cdots \oplus R { \bigl / } ( a _ { k } )$ where each $a _ { i }$ i s divisible by $\pmb { p } .$ Then $M / p M \cong F ^ { k }$
- **dependencies:** —


- **kind:** Theorem 9 (Fundamental Theorem, Uniqueness)
- **source:** §12.1; printed pp. 458–471; extraction line 16744
- **statement/data:** (Fundamental Theorem, Uniqueness) Let R be a P.I.D. (1) Two finitely generated R -modules $M _ { 1 }$ and $M _ { 2 }$ are isomorphic if and only if they have the same free rank and the same list of invariant factors. (2) Two finitely generated R -modules $M _ { 1 }$ and $M _ { 2 }$ are isomorphic if and only if they have the same free rank and the same list of elementary divisors.
- **dependencies:** —


- **kind:** Corollary 10
- **source:** §12.1; printed pp. 458–471; extraction line 16782
- **statement/data:** Let R be a P.I.D. and let M be a finitely generated R-module. (1) The elementary divisors of M are the prime power factors of the invariant factors of M. (2) The largest invariant factor of M is the product of the largest of the distinct prime powers among the elementary divisors of M, the next largest invariant factor is the product of the largest of the distinct prime powers among the remaining elementary divisors of M, and so on.
- **dependencies:** —


- **kind:** Corollary 11 (The Fundamental Theorem of Finitely Generated Abelian Groups)
- **source:** §12.1; printed pp. 458–471; extraction line 16790
- **statement/data:** (The Fundamental Theorem of Finitely Generated Abelian Groups) See Theorem 5.3 and Theorem 5.5.
- **dependencies:** FC01-C12-U009


- **kind:** Named comparison
- **source:** §12.2; printed pp. 472–490; extraction line 16932
- **statement/data:** A finite-dimensional F-vector space with endomorphism T is a finitely generated F[x]-module by letting x act as T; the PID structure theorem yields the rational/Jordan canonical-form data.
- **dependencies:** FC01-C10-U008


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 16942
- **statement/data:** (1) An element ').. of F is called an eigenvalue of the linear transformation T if there is a nonzero vector $v \in V$ such that $T ( v ) = \lambda v$ . In this situation v is called an eigenvector of T with coresponding eigenvalue 'A. (2) If A is an n x n matrix with coeficients in F, an element A is called an eigenvalue of A with corresponding eigenvector v if v is a nonzero $n \times 1$ column vector such that $A v = \lambda v$ (3) IfA is an eigenvalue of the linear transformation T, the set ${ v \in V \mid T ( v ) = \lambda v }$ is called the eigenspace of T corresponding to the eigenvalue A. Similarly, if A is an eigenvalue of the n x n matrix A, the set of n x 1 matrices v with $A v = \lambda v$ is called the eigenspace of A corresponding to the eigenvalue A.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 16952
- **statement/data:** The determinant of a linear transformation from V to V is the determinant of any matrix representing the linear transformation (note that this does not depend on the choice of the basis used).
- **dependencies:** —


- **kind:** Proposition 12
- **source:** §12.2; printed pp. 472–490; extraction line 16954
- **statement/data:** The following are equivalent: (1) A is an eigenvalue of T (2) $\lambda I - T$ is a singular linear transformation of V (3) det $( \lambda I - T ) = 0 .$
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 16966
- **statement/data:** Let x be an indeterminate over F. The polynomial det $( x I - T )$ is called the characteristic polynomial of T and will be denoted $c _ { T } ( x )$ A is an n n matrix with coeficients in F, det $( x I - A )$ is called the characteristic polynomial of A and will be denoted $c _ { A } ( { \boldsymbol { x } } )$
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 16972
- **statement/data:** The unique monic polynomial which generates the ideal $\mathbf { A n n } ( V )$ in $F [ x ]$ is called the minimal polytWmial of T and will be denoted $m _ { T } ( x )$ . The unique monic polynomial of smallest degree which when evaluated at the matrix A is the zero matrix is called the minimal polynomial of A and will be denoted $m _ { A } ( x )$
- **dependencies:** —


- **kind:** Proposition 13
- **source:** §12.2; printed pp. 472–490; extraction line 16992
- **statement/data:** The minimal polynomial $m _ { T } ( x )$ is the largest invariant factor of V . All the invariant factors of V divide $m _ { T } ( x )$ We shall see below how to calculate not only the minimal polynomial for T bu also the other invariant factors.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 17012
- **statement/data:** Let $a ( x ) = x ^ { k } + b _ { k - 1 } x ^ { k - 1 } + \cdot \cdot \cdot + b _ { 1 } x + b _ { 0 }$ be any monic polynomial in $F [ x ]$ . The companion matrix of ${ \pmb a } ( { \pmb x } )$ is the $k \times k$ matrix with 1 's down the first subdiagonal, $- b _ { 0 } , - b _ { 1 } , \ldots , - b _ { k - 1 }$ down the last column and zeros elsewhere. The companion matrix of ${ \pmb a } ( { \pmb x } )$ will be denoted by $\mathcal { C } _ { a ( x ) }$ We apply this to each of the cyclic modules on the right side of ( 1 ) above and let $\pmb { { B } _ { i } }$ be the elements of V coresponding to the basis chosen above for the cyclic factor $F [ x ] \big / ( a _ { i } ( x ) )$ under the isomorphism in (1 ). Then by definition the linear transformation $_ T$ acts on $\pmb { { B _ { i } } }$ by the companion matrix for $a _ { i } ( x )$ since we have seen that this is how multiplication by x acts. The union B of the $\pmb { { \cal B } } _ { i } \mathbf { \ ' } _ { 8 }$ gives a basis for V since the sum on the right of ( 1 ) is direct and with respect to this basis the linear transformation T has as matrix the direct sum of the companion matrices for the invariant factors, i.e., $$ \left( \begin{array}{c c c c} \mathcal {C} _ {a _ {1} (x)} & & & \ & \mathcal {C} _ {a _ {2} (x)} & & \ & & \ddots & \ & & & \mathcal {C} _ {a _ {m} (x)} \end{array} \right).\tag{12. …
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 17022
- **statement/data:** (1) A matrix is said to be in rational canonical form if it is the direct sum of companion matrices for monic polynomials $a _ { 1 } ( x ) , \ldots , a _ { m } ( x )$ of degree at least one with $a _ { 1 } ( x ) \mid a _ { 2 } ( x ) \mid \cdots \mid a _ { m } ( x )$ . The polynomials $a _ { i } ( x )$ are called the i1Wariant factors of the matrix. Such a matrix is also said to be a block diagonal matrix with blocks the companion matrices for the $a _ { i } ( x )$ (2) A rational canonical form for a linear transformation T is a matrix representing T which is in rational canonical form.
- **dependencies:** —


- **kind:** Theorem 14 (Rational Canonical Form for Linear Transformations)
- **source:** §12.2; printed pp. 472–490; extraction line 17030
- **statement/data:** (Rational Canonical Form for Linear Transformations) Let V be a finite dimensional vector space over the field F and let T be a linear transformation of V. (1) There i s a basis for V with respect to which the matrix for T i s i n rational canonical form, i.e., is a block diagonal matrix whose diagonal blocks are the companion matrices for monic polynomials $a _ { 1 } ( x ) , a _ { 2 } ( x ) , \dots , a _ { m } ( x )$ of degree at least one with $a _ { 1 } ( x ) \mid a _ { 2 } ( x ) \mid \cdots \mid a _ { m } ( x )$ (2) The rational canonical form for T i s unique. The use of the word rational is to indicate that this canonical form is calculated entirely within the field F and exists for any linear transformation $T$ . This is not the case for the Jordan canonical form (considered later), which only exists if the field $F$ contains the eigenvalues for T (cf. also the remarks following Corollary 18). The following result translates the notion of similar linear transformations (i.e., the same linear transformation up to a change of basis) into the language of modules and relates this notion to rational canonical forms.
- **dependencies:** —


- **kind:** Theorem 15
- **source:** §12.2; printed pp. 472–490; extraction line 17040
- **statement/data:** Let S and T be linear transformations of V. Then the following are equivalent: (1) S and $T$ are similar linear transformations (2) the F[x]-modules obtained from V via S and via T are isomorphic F[x]­ modules (3) S and T have the same rational canonical form.
- **dependencies:** —


- **kind:** Theorem 16 (Rational Canonical Fonfor Matrices)
- **source:** §12.2; printed pp. 472–490; extraction line 17058
- **statement/data:** (Rational Canonical Fonfor Matrices) Let A be an n x n matrix over the field F. (1) The matrix A 1s similar to a matrix in rational canonical form, i.e., there is an invertible $n \times n$ matrix P over F such that $P ^ { - 1 } A P$ is a block diagonal matrix whose diagonal blocks are the companion matrices for monic polynomials $a _ { 1 } ( x ) , a _ { 2 } ( x ) , \dots , a _ { m } ( x )$ of degree at least one with $a _ { 1 } ( x ) \mid a _ { 2 } ( x ) \mid \cdots \mid a _ { m } ( x )$ (2) The rational canonical form for A is unique.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.2; printed pp. 472–490; extraction line 17064
- **statement/data:** The invariant factors of an n x n matrix over a field F are the invariant factors of its rational canonical form.
- **dependencies:** —


- **kind:** Theorem 17
- **source:** §12.2; printed pp. 472–490; extraction line 17066
- **statement/data:** Let A and B be n x n matrices over the field F. Then A and B are simlar and only A and B have the same rational canonical form If A is a matrix with entries from a field F and F is a subfield of a larger field K then we may also consider A as a matrix over K. The next result shows that the rational canonical form for A and questions of similarity do not depend on which field contains the entries of A.
- **dependencies:** —


- **kind:** Corollary 18
- **source:** §12.2; printed pp. 472–490; extraction line 17070
- **statement/data:** Let A and B be two n x n matrices over a field F and suppose F is a subfield of the field K. (1) The rational canonical form of A is the same whether it is computed over K or over F. The minimal and characteristic polynomials and the invariant factors of A are the same whether A is considered as a matrix over F or as a matrix over K. (2) The matrices A and B are simlar over K if and only if they are similar over F, i.e., there exists an invertible n x n matrix P with entries from K such that $B = P ^ { - 1 } A P$ if and only if there exists an (in general diferent) invertible $\pmb { n } \times \pmb { n }$ matrix Q with entries from F such that $B = Q ^ { - 1 } A Q$
- **dependencies:** —


- **kind:** Lemma 19
- **source:** §12.2; printed pp. 472–490; extraction line 17084
- **statement/data:** Let $a ( x ) \in F [ x ]$ be any monic polynomial. (1) The characteristic polynomial of the companion matrix of $\pmb { a } ( \pmb { x } )$ is $a ( x )$ (2) If M is the block diagonal matrix $$ M = \left( \begin{array}{c c c c} A _ {1} & 0 & \ldots & 0 \ 0 & A _ {2} & \ldots & 0 \ \vdots & \vdots & \ddots & \vdots \ 0 & 0 & \ldots & A _ {k} \end{array} \right), $$ given by the direct sum of matrices $A _ { 1 } , A _ { 2 } , \ldots , A _ { k }$ then the characteristic poly nomial of M is the product of the charcteristic polynomials o $A _ { 1 } , A _ { 2 } , \ldots , A _ { k }$
- **dependencies:** —


- **kind:** Proposition 20
- **source:** §12.2; printed pp. 472–490; extraction line 17098
- **statement/data:** Let A be an n x n matrix over the field F (1) The charcteristic polynomial of A is the product of all the invariant factors of A . (2) (The Cayley-Hamilton Theorem) The minimal polynomial of A divides the characteristic polynomial of A. (3) The characteristic polynomial of A divides some power of the minimal polynomial of A. In particular these polynomials have the same rots, not counting multiplicities. The same statements are true if the matrix A is replaced by a linear transformation T of an n-dimensional vector space over F.
- **dependencies:** —


- **kind:** Convention
- **source:** §12.2; printed pp. 472–490; extraction line 17120
- **statement/data:** Elementary row/column operations over F[x] are row/column interchange, addition of a polynomial multiple of one row/column to another, and multiplication by a unit of F[x].
- **dependencies:** —


- **kind:** Theorem 21
- **source:** §12.2; printed pp. 472–490; extraction line 17122
- **statement/data:** Let A be an $n \times n$ matrix over the field F. Using the three elementary row and column operations above, the $n \times n$ matrix $x I - A$ with entries from $F [ x ]$ can be put into the diagonal form (called the Smith Normal Form for A) $$ \left( \begin{array}{c c c c c c c c} 1 & & & & & & \ & \ddots & & & & & \ & & 1 & & & & \ & & & a _ {1} (x) & & & \ & & & & a _ {2} (x) & & \ & & & & & \ddots & \ & & & & & & a _ {m} (x) \end{array} \right) $$ with monic nonzero elements $a _ { 1 } ( x ) , a _ { 2 } ( x ) , \dots , a _ { m } ( x )$ of $F [ x ]$ with degrees at least one and satisfying $a _ { 1 } ( x ) \mid a _ { 2 } ( x ) \mid \cdots \mid a _ { m } ( x )$ . The elements $a _ { 1 } ( x ) , \ldots , a _ { m } ( x )$ are the invariant factors of A.
- **dependencies:** —


- **kind:** Definition
- **source:** §12.3; printed pp. 491–509; extraction line 17569
- **statement/data:** The $k \times k$ matrix with .A along the main diagonal and 1 along the "first superdiagonal depicted above is called the $k \times k$ elementary Jordan matrix with eigenvalue .A or the Jordan block of size k with eigenvalue .A Applying this to each of the cyclic factors of V in its elementary divisor decomposition we obtain a vector space basis for V with respect to which the linear transformation T has as matrix the direct sum of the Jordan blocks coresponding to the elementary divisors of V, i.e., is block diagonal with Jordan blocks along the diagonal: $$ \left( \begin{array}{c c c c} J _ {1} & & & \ & J _ {2} & & \ & & \ddots & \ & & & J _ {t} \end{array} \right). $$ Notice that this matrix is uniquely determined up to permutation of the blocks along the diagonal by the elementary divisors of the F[x ]-module V and conversely, by Theorem 9, the list of elementary divisors uniquely determines the module V up to $F [ x ]$ -module isomorphism.
- **dependencies:** FC01-C12-U016


- **kind:** Definition
- **source:** §12.3; printed pp. 491–509; extraction line 17579
- **statement/data:** (1) A matrix is said to be in Jordan canonical form if it is a block diagonal matrix with Jordan blocks along the diagonal. (2) A Jordan canonical form for a linear transformation T is a matrix representing T which is in Jordan canonical form.
- **dependencies:** —


- **kind:** Theorem 22 (Jordan Canonical Form for Linear Transformations)
- **source:** §12.3; printed pp. 491–509; extraction line 17587
- **statement/data:** (Jordan Canonical Form for Linear Transformations) Let V be a finte dimensional vector space over the field F and let T be a linear transformation of V. Assume F contains all the eigenvalues of T. (1) There is a basis for V with respect to which the matrix for T is in Jordan canonical form. i.e., is a block diagonal matrix whose diagonal blocks are the Jordan blocks for the elementary divisors of V. (2) The Jordan canonical form for T is unique up to a permutation of the Jordan blocks along the diagonal. As for the rational canonical form, the following theorem gives the corresponding statement for n x n matrices over F.
- **dependencies:** —


- **kind:** Theorem 23 (Jordan Canonical Form for Matrices)
- **source:** §12.3; printed pp. 491–509; extraction line 17595
- **statement/data:** (Jordan Canonical Form for Matrices) Let A be an n x n matrix over the field F and assume F contains all the eigenvalues of A. (1) The matrix A is similar to a matrix in Jordan canonical form, i.e., there is an invertible n x n matrix P over F such that $P ^ { - 1 } A P$ is a block diagonal matrix whose diagonal blocks are the Jordan blocks for the elementary divisors of A. (2) The Jordan canonical form for A is unique up to a permutation of the Jordan blocks along the diagonal. The Jordan canonical form differs from a diagonal matrix only by the possible presence of some 1 's along the first superdiagonal (and then only if there are Jordan blocks of size greater than one), hence is close to being a diagonal matrix. The folowing result shows in particular that the Jordan canonical form for a matrix A is as close to being a diagonal matrix as possible.
- **dependencies:** —


- **kind:** Corollary 24
- **source:** §12.3; printed pp. 491–509; extraction line 17603
- **statement/data:** (1) If a matrix A is similar to a diagonal matrix D, then D is the Jordan canonical form of A. (2) Two diagonal matrices are similar if and only if their diagonal entries the same up to a permutation.
- **dependencies:** —


- **kind:** Corollary 25
- **source:** §12.3; printed pp. 491–509; extraction line 17613
- **statement/data:** If A is an n x n matrix with entries from F and F contains all the eigenvalues of A, then A is similar to a diagonal matrix over F if and only if the minimal polynomial of A has no repeated roots.
- **dependencies:** —



- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18243
- **statement/data:** The characteristic of a field F , denoted ch(F), i s defined to be the smallest positive integer p such that $p \cdot 1 _ { F } = 0$ if such a p exists and is defined to be 0 otherwise.
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §13.1; printed pp. 510–519; extraction line 18253
- **statement/data:** The characteristic of a field F, ch(F), is either 0 or a prime $\pmb { p } .$ . If ch $( F ) = p$ then for any $\alpha \in F$ $$ p \cdot \alpha = \underbrace {\alpha + \alpha + \cdots + \alpha} _ {p \text { times }} = 0. $$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18283
- **statement/data:** The prime subfield of a field F is the subfield of F generated by the multiplicative identity $1 _ { F }$ of F. It is (isomorphic to) either Q (if ch $( F ) = 0 )$ or $\mathbb { F } _ { p }$ (if ch $( F ) = p )$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18293
- **statement/data:** If K is a field containing the sub field F, then K is said to be an extension field (or simply an extension) of F, denoted $K / F$ or by the diagram $$ \begin{array}{c} K \ \big | \ F \end{array} $$ In particular, every field F is an extension of its prime sub field. The field F is sometimes called the base field of the extension The notation $K / F$ for a field extension is a shorthand for $^ { 6 6 } K$ over $F ^ { \prime \prime }$ and is not the quotient of K by F. If $K / F$ is any extension of fields, then the multiplication defined in K makes K into a vector space over ${ \pmb F } .$ In particular every field F can be considered as a vector space over its prime field.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18305
- **statement/data:** The degree (or relative degree or index) of a field extension $K / F$ , denoted $[ K : F ] ,$ , is the dimension of K as a vector space over $F \left( \mathbf { i . e . , } \left[ K : F \right] = \dim _ { F } K \right)$ . The extension is said to be finite if $[ K : F ]$ is finite and is said to be infinite otherwise. An important class of field extensions are those obtained by trying to solve equations over a given field F. For example, if $F = \mathbb { R }$ is the field of real numbers, then the simple equation $x ^ { 2 } + 1 = 0$ does not have a solution in F. The question arises whether there is some larger field containing ? in which this equation does have a solution, and it was this question that led Gauss to introduce the complex numbers $\mathbb { C } = \mathbb { R } + \mathbb { R } i$ , where i is defined so that $i ^ { 2 } + 1 = 0$ . One then defines addition and multiplication in C by the usual rules familiar from elementary algebra and checks that in fact C so defined is a field, i.e., it is possible to find an inverse for every nonzero element of $\mathbb { C } .$ Given any field F and any polynomial $p ( x ) \in F [ x ]$ one can ask a similar question: does there exist an extension K of $F$ containing a solution of the equation $p ( { \boldsymbol { x } } ) = \mathbf { 0 }$ $( \mathrm { i . e . } ,$ containing a root of $p ( x ) ) ?$ Note that we may assume here that the polynomial $p ( x )$ is ireducible in $F [ x ]$ since a root of any factor of $p ( x )$ is certainly a root of $p ( x )$ itself. …
- **dependencies:** —


- **kind:** Proposition 2
- **source:** §13.1; printed pp. 510–519; extraction line 18311
- **statement/data:** Let $\varphi : F F ^ { \prime }$ be a homomorphism of fields. Then $\varphi$ is either identically 0 or is injective, so that the image of $\varphi$ is either 0 or isomorphic to $F$ .
- **dependencies:** —


- **kind:** Theorem 3
- **source:** §13.1; printed pp. 510–519; extraction line 18313
- **statement/data:** Let F be a field and let $p ( x ) \in F [ x ]$ be an irreducible polynomial. Then there exists a field K containing an isomorphic copy of $F$ in which $p ( x )$ has a rot. Identifying F with this isomorphic copy shows that there exists an extension of $F$ in which $p ( x )$ has a root.
- **dependencies:** —


- **kind:** Theorem 4
- **source:** §13.1; printed pp. 510–519; extraction line 18333
- **statement/data:** Let $p ( x ) \in F [ x ]$ be an ireducible polynomial of degree n over the field F and let K be the field $F [ x ] / ( p ( x ) )$ . Let $\theta = x { \bmod { ( p ( x ) ) } } \in K$ . Then the elements $$ 1, \theta , \theta^ {2}, \dots , \theta^ {n - 1} $$ are a basis for K as a vector space over F, so the degree of the extension is $\pmb { n } ,$ i . e . , $[ K : F ] = n$ . Hence $$ K = {a _ {0} + a _ {1} \theta + a _ {2} \theta^ {2} + \dots + a _ {n - 1} \theta^ {n - 1} \mid a _ {0}, a _ {1}, \ldots , a _ {n - 1} \in F } $$ consists of al polynomials of degree < n in (} .
- **dependencies:** —


- **kind:** Corollary 5
- **source:** §13.1; printed pp. 510–519; extraction line 18389
- **statement/data:** Let K be as in Theorem 4, and let $a ( \theta ) , b ( \theta ) \in K$ be two polynomials of degree $< n$ in $\theta .$ Then addition in K is defined simply by usual polynomial addition and multiplication in K is defined by $$ a (\theta) b (\theta) = r (\theta) $$ where $r ( x )$ is the remainder (of degree $< n )$ obtained after dividing the polynomial $a ( { \boldsymbol { x } } ) b ( { \boldsymbol { x } } )$ by $p ( x )$ in $F [ x ]$ By the results proved above, this definition of addition and multiplication on the polynomials of degree $< n$ in $\theta$ make K into $\mathsf { a } f t e l d ,$ so that one can also divide by nonzero elements as well, which is not so imediately obvious from the definitions of the operations. It is also important in Theorem 4 that the polynomial $p ( x )$ be irreducible over $F .$ . In general the addition and multiplication in Corollary 5 (which can be defined in the same way for any polynomial $p ( { \boldsymbol { x } } ) )$ do not make the polynomials of degree $< n$ in $\theta$ into a field if $p ( x )$ is not irreducible. In fact, this set is not even an integral domain in general (its structure is given by Proposition 16 of Chapter 9). To describe the field containing a root $\theta$ of a general polynomial $f ( x )$ over $F , f ( x )$ is factored into ireducibles in $F [ x ]$ and the results above are applied to an irreducible factor $p ( x )$ of $f ( x )$ having $\theta$ as a root. We shall consider this more in the following sections.
- **dependencies:** FC01-C13-U008


- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18511
- **statement/data:** Let K be an extension of the field F and let a, $\beta , \cdots \in K$ be a collection of elements of K . Then the smallest subfield of K containing both F and the elements $\alpha , \beta , \ldots$ , denoted $F ( \alpha , \beta , \ldots )$ is called the field generated by a, {3, . . . over F.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.1; printed pp. 510–519; extraction line 18513
- **statement/data:** If the field K is generated by a single element a over F, $K = F ( \pmb { \alpha } )$ , then K is said to be a simple extension of F and the element a is caled a primitive element for the extension.
- **dependencies:** —


- **kind:** Theorem 6
- **source:** §13.1; printed pp. 510–519; extraction line 18519
- **statement/data:** Let F be a field and let $p ( x ) \in F [ x ]$ be an ireducible polynomial. Suppose K is an extension field of F containing a root a of $p ( x ) \colon p ( \alpha ) = 0$ . Let $F ( \pmb { \alpha } )$ denote the subfield of K generated over F by a. Then $$ F (\alpha) \cong F [ x ] / (p (x)). $$
- **dependencies:** —


- **kind:** Corollary 7
- **source:** §13.1; printed pp. 510–519; extraction line 18543
- **statement/data:** Suppose in Theorem 6 that $p ( x )$ is of degree n. Then $$ F (\alpha) = \left{a _ {0} + a _ {1} \alpha + a _ {2} \alpha^ {2} + \dots + a _ {n - 1} \alpha^ {n - 1} \mid a _ {0}, a _ {1}, \ldots , a _ {n - 1} \in F \right} \subseteq K. $$ Describing fields generated by more than one element is more complicated and we shall return to this question in the following section.
- **dependencies:** FC01-C13-U012


- **kind:** Theorem 8
- **source:** §13.1; printed pp. 510–519; extraction line 18577
- **statement/data:** Let $\varphi : F \stackrel { \sim } { \to } F ^ { \prime }$ be an isomorphism of fields. Let $p ( x ) \in F [ x ]$ be an ireducible polynomial and let $p ^ { \prime } ( x ) \in F ^ { \prime } [ x ]$ be the ireducible polynomial obtained by applying the map $\varphi$ to the coeficients of $p ( x )$ . Let $\pmb { \alpha }$ be a root of $p ( x )$ (in some extension of $F )$ and let $\beta$ be a rot of $p ^ { \prime } ( x )$ (in some extension of $F ^ { \prime } )$ . Then there is an isomorphism $$ \begin{array}{c} \sigma : F (\alpha) \stackrel {{\sim}} {{\longrightarrow}} F ^ {\prime} (\beta) \ \alpha \longmapsto \beta \end{array} $$ mapping a to $\beta$ and extending $\varphi ,$ i.e., such that $\pmb { \sigma }$ restricted to F is the isomorphism ${ \pmb \varphi } .$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §13.2; printed pp. 520–530; extraction line 18621
- **statement/data:** The element $\alpha \in K$ is said to be algebraic over F if a is a root of some nonzero polynomial $f ( x ) \in F [ x ]$ . If a is not algebraic over F (i.e., is not the root of any nonzero polynomial with coeficients in F) then a is said to be transcendental over F. The extension $K / F$ is said to be algebraic if every element of K is algebraic over F.
- **dependencies:** —


- **kind:** Proposition 9
- **source:** §13.2; printed pp. 520–530; extraction line 18625
- **statement/data:** Let a be algebraic over F. Then there is a unique monic irreducible polynomial $m _ { \alpha , F } ( x ) \in F [ x ]$ which has a as a root. A polynomial $f ( x ) \in F [ x ]$ has a as a rot if and only if $m _ { \alpha , F } ( x )$ divides $f ( x )$ in $F [ x ]$
- **dependencies:** —


- **kind:** Corollary 10
- **source:** §13.2; printed pp. 520–530; extraction line 18635
- **statement/data:** If $L / F$ is an extension of fields and a is algebraic over both F and L, then $m _ { \alpha , L } ( x )$ divides $m _ { \alpha , F } ( x )$ in $\boldsymbol { L } [ \boldsymbol { x } ]$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.2; printed pp. 520–530; extraction line 18639
- **statement/data:** The polynomial $m _ { \alpha , F } ( x )$ (or just $m _ { \alpha } ( x )$ ) if the field F is understood) in Proposition 9 is called the minimal polynomial for a over F. The degree of $m _ { \alpha } ( x )$ is called the degree of a .
- **dependencies:** FC01-C13-U016


- **kind:** Proposition 11
- **source:** §13.2; printed pp. 520–530; extraction line 18643
- **statement/data:** Let a be algebraic over the field F and let $F ( \alpha )$ be the field generated by a over F. Then $$ F (\alpha) \cong F [ x ] / (m _ {\alpha} (x)) $$ so that in particular $$ [ F (\alpha): F ] = \deg m _ {\alpha} (x) = \deg \alpha , $$ i.e., the degree of a over F is the degree of the extension it generates over F.
- **dependencies:** —


- **kind:** Proposition 12
- **source:** §13.2; printed pp. 520–530; extraction line 18671
- **statement/data:** The element a is algebraic over F if and only if the simple extension $F ( \alpha ) / F$ is finite. More precisely, if a is an element of an extension of degree n over F then a satisfies a polynomial of degree at most n over F and if a satisfies a polynomial of degree n over F then the degree of $F ( \alpha )$ over F is at most n.
- **dependencies:** —


- **kind:** Corollary 13
- **source:** §13.2; printed pp. 520–530; extraction line 18687
- **statement/data:** If the extension $K / F$ is finite, then it is algebraic.
- **dependencies:** —


- **kind:** Named example
- **source:** §13.2; printed pp. 520–530; extraction line 18693
- **statement/data:** Quadratic extensions in characteristic ≠2: every degree-2 extension is F(√D) for a nonsquare D∈F, and conversely F(√D)/F has degree 2.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.2; printed pp. 520–530; extraction line 18713
- **statement/data:** If char(F)≠2, every degree-2 extension of F has the form F(√D) with D∈F nonsquare, and conversely; degree-2 extensions are called quadratic extensions.
- **dependencies:** —


- **kind:** Theorem 14
- **source:** §13.2; printed pp. 520–530; extraction line 18717
- **statement/data:** Let $F \subseteq K \subseteq L$ be fields. Then $$ [ L: F ] = [ L: K ] [ K: F ], $$ i.e. extension degrees are multiplicative, where if one side of the equation is infinte, the other side is also infinite. Pictorially,
- **dependencies:** —


- **kind:** Corollary 15
- **source:** §13.2; printed pp. 520–530; extraction line 18773
- **statement/data:** Suppose $L / F$ is a finite extension and let K be any subfield of L containing F, $F \subseteq K \subseteq L .$ . Then $[ K : F ]$ divides $[ L : F ]$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.2; printed pp. 520–530; extraction line 18789
- **statement/data:** An extension $K / F$ is finitely generated if there are elements $\alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { k }$ in K such that $K = F ( \alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { k } )$
- **dependencies:** —


- **kind:** Lemma 16
- **source:** §13.2; printed pp. 520–530; extraction line 18793
- **statement/data:** $F ( \alpha , { \bar { \beta } } ) = ( F ( \alpha ) ) ( \beta )$ , i.e., the field generated over $F$ by a and $\beta$ is the field generated by $\beta$ over the field $F ( \alpha )$ generated by ${ \pmb \alpha } .$
- **dependencies:** —


- **kind:** Theorem 17
- **source:** §13.2; printed pp. 520–530; extraction line 18865
- **statement/data:** The extension $K / F$ is finite if and only if K is generated by a finite number of algebraic elements over $F$ . More precisely, a field generated over $F$ by a finite number of algebraic elements of degrees $n _ { 1 } , \ n _ { 2 } , \ldots , n _ { k }$ is algebraic of degree $\leq n _ { 1 } n _ { 2 } \dotsm \cdot n _ { k }$
- **dependencies:** —


- **kind:** Corollary 18
- **source:** §13.2; printed pp. 520–530; extraction line 18871
- **statement/data:** Suppose a and $\beta$ are algebraic over F. Then $\alpha \pm \beta , \alpha \beta , \alpha / \beta ( { \bf f o r } \beta \ne 0 )$ (in particular $\pmb { \alpha } ^ { - 1 }$ for ${ \pmb { \alpha } } \neq { \bf 0 } )$ are all algebraic.
- **dependencies:** —


- **kind:** Corollary 19
- **source:** §13.2; printed pp. 520–530; extraction line 18875
- **statement/data:** Let $L / F$ be an arbitrary extension. Then the collection of elements o L that are algebraic over F form a subfield K of L.
- **dependencies:** —


- **kind:** Theorem 20
- **source:** §13.2; printed pp. 520–530; extraction line 18887
- **statement/data:** If K is algebraic over F and L is algebraic over $\kappa ,$ , then L is algebraic over F.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.2; printed pp. 520–530; extraction line 18905
- **statement/data:** Let $K _ { 1 }$ and $K _ { 2 }$ be two subfields of a field K . Then the composite field of $K _ { 1 }$ and $K _ { 2 }$ , denoted $K _ { 1 } K _ { 2 }$ , is the smallest subfield of K containing both $K _ { 1 }$ and $K _ { 2 }$ • Similarly, the composite of any collection of subfields of K is the smallest sub field containing all the subfields.
- **dependencies:** —


- **kind:** Proposition 21
- **source:** §13.2; printed pp. 520–530; extraction line 18927
- **statement/data:** Let $K _ { 1 }$ and $K _ { 2 }$ be two finite extensions of a field F contained in K. Then $$ [ K _ {1} K _ {2}: F ] \leq [ K _ {1}: F ] [ K _ {2}: F ] $$ with equality if and only if an F -basis for one of the fields remains linearly independent over the other field. If $\alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { n }$ and $\beta _ { 1 } , \beta _ { 2 } , \ldots , \beta _ { m }$ are bases for $K _ { 1 }$ and $K _ { 2 }$ over $F ,$ respectively, then the elements $\alpha _ { i } \beta _ { j }$ for $i = 1 , 2 , \dots ,$ n and $j = 1 , 2 , \dots , m$ span $K _ { 1 } K _ { 2 }$ over $F _ { \ast }$
- **dependencies:** —


- **kind:** Corollary 22
- **source:** §13.2; printed pp. 520–530; extraction line 18943
- **statement/data:** Suppose that $[ K _ { 1 } : F ] = n , [ K _ { 2 } : F ] = m$ in Proposition 2 1 , where n and m are relatively prime: $( n , m ) = 1$ . Then $[ K _ { 1 } K _ { 2 } : F ] = [ K _ { 1 } : F ] [ K _ { 2 } : F ] = n m .$
- **dependencies:** FC01-C13-U006


- **kind:** Definition
- **source:** §13.3; printed pp. 531–535; extraction line 19020
- **statement/data:** The constructible elements of R are the signed real lengths obtainable from a fixed unit by straightedge and compass; they form a subfield closed under square roots.
- **dependencies:** —


- **kind:** Proposition 23
- **source:** §13.3; printed pp. 531–535; extraction line 19065
- **statement/data:** If the element $\pmb { \alpha } \in \mathbb { R }$ is obtained from a field $F \subset \mathbb { R }$ by a series of compass and straightedge constructions then $[ F ( \alpha ) : F ] = 2 ^ { k }$ for some integer ${ \pmb k } \geq { \bf 0 }$
- **dependencies:** —


- **kind:** Theorem 24
- **source:** §13.3; printed pp. 531–535; extraction line 19067
- **statement/data:** None of the classical Greek problems: (I) Doubling the Cube, (II) Trisecting an Angle, and (III) Squaring the Circle, is possible.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19145
- **statement/data:** The extension field K of F is called a splitting field for the polyno?al $f ( x ) \in F [ x ]$ if $f ( x )$ factors completely into linear factors (or splits completely) in K[x] and f(x) does not factor completely into linear factors over any proper subfield of K containing F. If f (x) is of degree n, then $f ( x )$ has at most n rots in F (Proposition 17 of Chapter 9) and has precisely n roots (counting multiplicities) in F if and only if $f ( x )$ splits completely in $F [ x ]$
- **dependencies:** —


- **kind:** Theorem 25
- **source:** §13.4; printed pp. 536–544; extraction line 19149
- **statement/data:** For any field F, if $f ( x ) \in F [ x ]$ then there exists an extension K of F which is a splitting field for $f ( x )$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19155
- **statement/data:** If K is an algebraic extension of F which is the splitting field over F for a collection of polynomials $f ( x ) \in F [ x ]$ then K is called a normal extension of F. We shall generally use the term "splitting field" rather than "normal extension" ( cf. also Section 1 4.9).
- **dependencies:** —


- **kind:** Proposition 26
- **source:** §13.4; printed pp. 536–544; extraction line 19217
- **statement/data:** A splitting field of a polynomial of degree n over F is of degree at most n ! over As the examples above show, the degree of a splitting field may be smaller than n ! . It will be proved later using Galois Theory that a "general" polynomial of degree n (in a well defined sense) over Q has a splitting field of degree n !, so this may be viewed as the generic situation (although most of the interesting examples we shall consider have splitting fields of smaller degree).
- **dependencies:** —


- **kind:** Named example
- **source:** §13.4; printed pp. 536–544; extraction line 19221
- **statement/data:** The splitting field of x^n−1 is the cyclotomic field generated by the nth roots of unity; the roots form a finite cyclic subgroup of the multiplicative group.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19251
- **statement/data:** A generator of the cyclic group of all $n ^ { \mathrm { t h } }$ roots of unity is called a primitive $n ^ { \mathrm { t h } }$ root of unity. Let $\xi _ { n }$ denote a primitive $n ^ { \mathrm { t h } }$ root of unity. The other primitive $n ^ { \mathrm { t h } }$ roots of unity are then the elements $\zeta _ { n } ^ { \alpha }$ where $1 \leq a < n$ is an integer relatively prime to n, since these are the other generators for a cyclic group of order n. In particular there are precisely $\varphi ( n )$ primitive $n ^ { \mathrm { t h } }$ roots of unity, where $\varphi ( n )$ denotes the Euler .p-function. Over C we can see all of this directly by letting $$ \zeta_ {n} = e ^ {2 \pi i / n} $$ (the first $\pmb { n } ^ { \mathrm { t h } }$ root of unity counterclockwise from 1). Then all the other roots of unity are powers of $\xi _ { n }$ : $$ e ^ {2 \pi k i / n} = \zeta_ {n} ^ {k} $$ so that $\xi _ { n }$ is one possible generator for the multiplicative group of $n ^ { \mathrm { t h } }$ roots of unity. When we view the roots of unity in C we shall usually use $\xi _ { n }$ to denote this choice of a primitive $n ^ { \mathrm { t h } }$ root of unity. …
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19293
- **statement/data:** The field $\mathbb { Q } ( \zeta _ { n } )$ is called the cyclotomic field of $n ^ { \mathrm { t h } }$ roots of unity. Determining the degree of this extension requires some analysis of the minimal polynomia of $\gamma _ { n }$ over Q and will be postponed until later (Section 6). One important special case which we have in fact already considered is when $\pmb { n } = \pmb { p }$ is a prime. In this case, we have the factorization $$ x ^ {p} - 1 = (x - 1) \left(x ^ {p - 1} + x ^ {p - 2} + \dots + x + 1\right) $$ and since $\zeta _ { P } \neq 1$ it follows that $\boldsymbol { \zeta } _ { p }$ is a root of the polynomial $$ \Phi_ {p} (x) = \frac {x ^ {p} - 1}{x - 1} = x ^ {p - 1} + x ^ {p - 2} + \dots + x + 1 $$ which we showed was ireducible in Section 9.4. It follows that $\bar { \pmb { \phi } } _ { p } ( { \pmb x } )$ is the minimal polynomial of $\zeta _ { p }$ over Q, so that $$ [ \mathbb {Q} (\zeta_ {p}): \mathbb {Q} ] = p - 1. $$
- **dependencies:** —


- **kind:** Named example
- **source:** §13.4; printed pp. 536–544; extraction line 19315
- **statement/data:** For prime p, the splitting field of x^p−2 is generated by one pth root of 2 and a primitive pth root of unity.
- **dependencies:** —


- **kind:** Theorem 27
- **source:** §13.4; printed pp. 536–544; extraction line 19343
- **statement/data:** Let $\varphi : F \ { \stackrel { \sim } { \to } } \ F ^ { \prime }$ be an isomorphism of fields. Let $f ( x ) \ \in \ F [ x ]$ be a polynomial and let $f ^ { \prime } ( x ) \in F ^ { \prime } [ x ]$ be the polynomial obtained by applying $\pmb { \varphi }$ to the coefficients of $f ( x )$ . Let E be a splitting field for $f ( x )$ over $\pmb { F }$ and let $E ^ { \prime }$ be a splitting field for $f ^ { \prime } ( x )$ over $F ^ { \prime }$ . Then the isomorphism $\varphi$ extends to an isomorphism $\sigma : E \stackrel { \sim } { \to } E ^ { \prime }$ , i . e . , $\sigma$ restricted to $\pmb { F }$ is the isomorphism $\varphi \colon$ $$ \begin{array}{c c c c} \sigma : & E & \stackrel {{\sim}} {{\longrightarrow}} & E ^ {\prime} \ & \mid & & \mid \ \varphi : & F & \stackrel {{\sim}} {{\longrightarrow}} & F ^ {\prime} \end{array} $$
- **dependencies:** —


- **kind:** Corollary 28 (Uniqueness of Spliting Fields)
- **source:** §13.4; printed pp. 536–544; extraction line 19369
- **statement/data:** (Uniqueness of Spliting Fields) Any two splitting fields for a polynomial $f ( x ) \in F [ x ]$ over a field F are isomorphic.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19377
- **statement/data:** The field $\overline { F }$ is called an algebraic closure of $F$ if $\overline { F }$ is algebraic over F and if every polynomial $f ( x ) \in F [ x ]$ splits completely over $\overline { F }$ (so that $\scriptstyle { \overline { { F } } }$ can be said to contain all the elements algebraic over F).
- **dependencies:** —


- **kind:** Definition
- **source:** §13.4; printed pp. 536–544; extraction line 19379
- **statement/data:** A field K is said to be algebraieally closed if every polynomial with coeficients in K has a root in K. It is not obvious that algebraically closed fields exist nor that there exists an algebraic closure of a given field F (we shall prove this shortly).
- **dependencies:** —


- **kind:** Proposition 29
- **source:** §13.4; printed pp. 536–544; extraction line 19387
- **statement/data:** Let $\overline { F }$ be an algebraic closure of F. Then $\overline { F }$ is algebraically closed
- **dependencies:** —


- **kind:** Proposition 30
- **source:** §13.4; printed pp. 536–544; extraction line 19395
- **statement/data:** For any field F there exists an algebraically closed field K containing F.
- **dependencies:** —


- **kind:** Proposition 31
- **source:** §13.4; printed pp. 536–544; extraction line 19433
- **statement/data:** Let K be an algebraically closed field and let F be a subfield of K . Then the collection of elements $\overline { F }$ of K that are algebraic over F is an algebraic closure of F. An algebraic closure of F is unique up to isomorphism.
- **dependencies:** —


- **kind:** Theorem (Fundamental Theorem of Algebra)
- **source:** §13.4; printed pp. 536–544; extraction line 19441
- **statement/data:** (Fundamental Theorem of Algebra) The field C is algebraically closed. By Proposition 3 1 , we immediately obtain:
- **dependencies:** —


- **kind:** Corollary 32
- **source:** §13.4; printed pp. 536–544; extraction line 19445
- **statement/data:** The field C contains an algebraic closure for any of its subfields. In particular, $\overline { { \mathbb { Q } } } ,$ the collection of complex numbers algebraic over $\mathbb { Q } ,$ is an algebraic closure of Q. The point of these considerations is that all the computations involving elements algebraic over a field F may be viewed as taking place in one (large) field, namely ${ \overline { { F } } } .$ . Similarly, we can speak sensibly of the composite of any collection of algebraic extensions by viewing them all as subfields of an algebraic closure. In the case of Q or finite extensions of Q we may consider all of our computations as occuring in C.
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19477
- **statement/data:** A polynomial over F is caled separable if it has no multiple roots (i.e., all its roots are distinct). A polynomial which is not separable is called inseparable. Note that if a polynomial $f ( x )$ has distinct roots in one splitting field then $f ( x )$ has distinct roots in any splitting field (since this is equivalent to $f ( x )$ factoring into distinct linear factors, and there is an isomorphism over F between any two splitting fields of $f ( x )$ that is bijective on its roots), so that we need not specify the field containing all the rots of $f ( x )$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19495
- **statement/data:** The derivative of the polynomial $$ f (x) = a _ {n} x ^ {n} + a _ {n - 1} x ^ {n - 1} + \dots + a _ {1} x + a _ {0} \in F [ x ] $$ is defined to be the polynomia $$ D _ {x} f (x) = n a _ {n} x ^ {n - 1} + (n - 1) a _ {n - 1} x ^ {n - 2} + \dots + 2 a _ {2} x + a _ {1} \in F [ x ]. $$ This formula is nothing but the usual formula for the derivative of a polynomial familiar from calculus. It is purely algebraic and so can be applied to a polynomial over an arbitrary field $F ,$ , where the analytic notion of derivative (involving limits - a continuous operation) may not exist. The usual (calculus) formulas for derivatives hold for derivatives in this situation as well, for example the formulas for the derivative of a sum and of a product: $$ \begin{array}{c} D _ {x} (f (x) + g (x)) = D _ {x} f (x) + D _ {x} g (x) \ D _ {x} (f (x) g (x)) = f (x) D _ {x} g (x) + (D _ {x} f (x)) g (x). \end{array} $$ These formulas can be proved directly from the definition for polynomials and do not require any limiting operations and are left as an exercise.
- **dependencies:** —


- **kind:** Proposition 33
- **source:** §13.5; printed pp. 545–551; extraction line 19519
- **statement/data:** A polynomial $f ( x )$ has a multiple root a if and only if a is also a root of $D _ { x } f ( x )$ , i . e . , $f ( x )$ and $D _ { x } f ( x )$ are both divisible by the minimal polynomial for a. In particular, $f ( x )$ is separable if and only if it is relatively prime to its derivative: $( f ( x ) , D _ { x } f ( x ) ) = 1$
- **dependencies:** —


- **kind:** Corollary 34
- **source:** §13.5; printed pp. 545–551; extraction line 19565
- **statement/data:** Every ireducible polynomial over a field of characteristic 0 (for example, Q) is separable. A polynomial over such a field is separable if and only if it is the product of distinct ireducible polynomials.
- **dependencies:** —


- **kind:** Proposition 35
- **source:** §13.5; printed pp. 545–551; extraction line 19593
- **statement/data:** Let F be a field of characteristic $p .$ . Then for any a , $b \in F$ $$ (a + b) ^ {p} = a ^ {p} + b ^ {p}, \quad \text { and } \quad (a b) ^ {p} = a ^ {p} b ^ {p}. $$ Put another way, the $p ^ { \mathrm { t h } } .$ -power map defined by $\varphi ( a ) = a ^ { p }$ is an injective field homomorphism from $F$ to $F$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19617
- **statement/data:** The map in Proposition 35 is called the Frobenius endomorphism of F.
- **dependencies:** FC01-C13-U059


- **kind:** Corollary 36
- **source:** §13.5; printed pp. 545–551; extraction line 19619
- **statement/data:** Suppose that IF is a finite field of characteristic p. Then every element of IF is a $p ^ { \mathrm { t h } }$ power in IF (notationally, $\mathbb { F } = \mathbb { F } ^ { p } )$ .
- **dependencies:** —


- **kind:** Proposition 37
- **source:** §13.5; printed pp. 545–551; extraction line 19639
- **statement/data:** Every irreducible polynomial over a finite field IF is separable. A polynomial in IF[x] is separable if and only if it is the product of distinct ireducible polynomials in IF[x]. The important part of the proof of this result is the fact that every element in the characteristic p field IF was a $p ^ { \mathfrak { t h } }$ power in IF. This suggests the following definition:
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19643
- **statement/data:** A field K of characteristic p is called peifect if every element of K is a $p ^ { \mathfrak { t h } }$ power in K, i.e., $K = K ^ { p }$ . Any field of characteristic 0 is also called perfect With this definition, we see that we have proved that every irreducible polynomial over a perfect field is separable. It is not hard to see that if K is not perfect then there are inseparable irreducible polynomials.
- **dependencies:** —


- **kind:** Named example
- **source:** §13.5; printed pp. 545–551; extraction line 19647
- **statement/data:** For every prime power p^n there is, up to isomorphism, a unique field with p^n elements, realized as the splitting field of x^{p^n}−x over F_p.
- **dependencies:** —


- **kind:** Proposition 38
- **source:** §13.5; printed pp. 545–551; extraction line 19663
- **statement/data:** Let $p ( x )$ be an irreducible polynomial over a field F of characteristic $\pmb { p } .$ Then there is a unique integer $k \geq 0$ and a unique irreducible separable polynomial $p _ { s e p } ( x ) \in F [ x ]$ such that $$ p (x) = p _ {s e p} \left(x ^ {p ^ {k}}\right). $$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19669
- **statement/data:** Let $p ( x )$ be an ireducible polynomial over a field of characteristic $\pmb { p } .$ The degree of $p _ { s e p } ( x )$ in the last proposition is called the separable degree of $p ( x ) .$ , denoted $\mathbf { d e g } _ { s } p ( x )$ . The integer $p ^ { k }$ in the proposition is caled the inseparable degree of $p ( x )$ denoted deg; $p ( x )$ From the definitions and the proposition we see that $p ( x )$ is separable if and only if its inseparability degree is 1 if and only if its degree is equal to its separable degree. Also, computing degrees in the relation $p ( x ) = p _ { s e p } ( x ^ { p ^ { k } } )$ we see that $$ \deg p (x) = \deg_ {s} p (x) \deg_ {i} p (x). $$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.5; printed pp. 545–551; extraction line 19687
- **statement/data:** The field K is said to be separable (or separably algebraic) over F if every element of K is the root of a separable polynomial over F (equivalently, the minimal polynomial over $F$ of every element of K is separable). A field which is not separable is inseparable.
- **dependencies:** —


- **kind:** Corollary 39
- **source:** §13.5; printed pp. 545–551; extraction line 19691
- **statement/data:** Every finite extension of a perfect field is separable. In particular, every finite extension of either Q or a finite field is separable. We shall consider separable and inseparable extensions more after developing some Galois Theory, in particular definng the separable and inseparable degree of the extension $K / F$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.6; printed pp. 552–557; extraction line 19735
- **statement/data:** Let $\mu _ { n }$ denote the group of $\cdot _ { n } \mathrm { t h }$ roots of unity over $\mathbb { Q } .$ Then as we have already observed, $\mathbb { Z } / n \mathbb { Z } \cong \mu _ { n }$ as groups (under multiplication on the right, addition on the left), given explicitly by the map $a \mapsto ( \zeta _ { n } ) ^ { a }$ for a fixed primitive $n ^ { \mathrm { t h } }$ root of unity. The primitive $n ^ { \mathrm { t h } }$ roots of unity are given by the residue classes prime to n so there are precisely $\varphi ( n )$ primitive $n ^ { \mathrm { t h } }$ roots of unity. If d i? a divisor of n and $\boldsymbol { \zeta }$ is a $d ^ { \mathrm { t h } }$ root of unity, then $\boldsymbol { \zeta }$ is also an $n ^ { \mathrm { { \dot { t } h } } }$ root of unity since $\zeta ^ { n } = ( \zeta ^ { d } ) ^ { n / d } = 1$ . Hence $$ \mu_ {d} \subseteq \mu_ {n} \quad \text { for all } d \mid n. $$ Conversely, the order of any element of the group $\mu _ { n }$ is a divisor of n so that if $\boldsymbol { \zeta }$ is an $n ^ { \mathrm { t h } }$ root of unity which is also a $d ^ { \mathrm { t h } }$ root of unity for some smaller d then d $\mid n .$
- **dependencies:** —


- **kind:** Definition
- **source:** §13.6; printed pp. 552–557; extraction line 19747
- **statement/data:** Define the $n ^ { \mathrm { t h } }$ cyclotomic polynomial $\Phi _ { n } ( x )$ to be the polynomial whose roots are the primitive $n ^ { \mathrm { t h } }$ roots of unity: $$ \Phi_{n}(x) = \prod_{\zeta \text{primitive}\in \mu_{n}}(x - \zeta) = \prod_{\substack{1\leq a < n\ (a,n) = 1}}(x - \zeta_{n}^{a}) $$ (which is of degree $\varphi ( n ) )$ ). The roots of the polynomial $x ^ { n } - 1$ are precisely the $n ^ { \mathrm { t h } }$ roots of unity so we have the factorization $$ x^{n} - 1 = \prod_{\substack{\zeta^{n} = 1\ \text{i.e.}\zeta \in \mu_{n}}}(x - \zeta). $$ If we group together the factors $( x - \zeta )$ where $\boldsymbol { \zeta }$ is an element of order d in $\mu _ { n }$ (i.e., $\boldsymbol { \zeta }$ is a primitive $\bar { d } ^ { \mathrm { { u } } }$ root of unity) we obtain $$ x^{n} - 1 = \prod_{d|n}\prod_{\substack{\zeta \in \mu_{d}\ \zeta \text{primitive}}} (x - \zeta). $$ The inner product is $\Phi _ { d } ( x )$ by definition so we have the factorization $$ x ^ {n} - 1 = \prod_ {d | n} \Phi_ {d} (x).\tag{13.4} $$ Note incidentally that comparing degrees gives the identity $$ n = \sum_ {d | n} \varphi (d). $$ This factorization allows us to compute $\Phi _ { n } ( x )$ for any n recursively: clearly $\bar { \phi } _ { 1 } ( x ) = x - 1$ and $\bar { \Phi } _ { 2 } ( x ) = x + 1$ . Then $$ x ^ {3} - 1 = \Phi_ {1} (x) \Phi_ {3} (x) = (x - 1) \Phi_ {3} (x) $$ which gives $$ \Phi_ {3} (x) = x ^ {2} + x + 1. …
- **dependencies:** —


- **kind:** Lemma 40
- **source:** §13.6; printed pp. 552–557; extraction line 19845
- **statement/data:** The cyclotomic polynomial $\Phi _ { n } ( x )$ is a monic polynomial in $\mathbb { Z } [ x ]$ of degree $\varphi ( n )$
- **dependencies:** —


- **kind:** Theorem 41
- **source:** §13.6; printed pp. 552–557; extraction line 19851
- **statement/data:** The cyclotomic polynomial $\varPhi _ { n } ( x )$ is an irreducible monic polynomial in $\mathbb { Z } [ x ]$ of degree $\varphi ( n )$
- **dependencies:** —


- **kind:** Corollary 42
- **source:** §13.6; printed pp. 552–557; extraction line 19891
- **statement/data:** The degree over $\mathbb { Q }$ of the cyclotomic field of $n ^ { \mathrm { t h } }$ roots of unity is $\varphi ( n )$ : $$ [ \mathbb {Q} (\zeta_ {n}): \mathbb {Q} ] = \varphi (n). $$
- **dependencies:** —



- **kind:** Definition
- **source:** §14.1; printed pp. 558–566; extraction line 19997
- **statement/data:** (1) An isomorphism $\pmb { \sigma }$ of K with itself is called an automorphism of K. The collection of automorphisms of K is denoted Aut(K). If $\alpha \in K$ we shall write a a for $\sigma ( \alpha )$ (2) An automorphism $\sigma \in \operatorname { A u t } ( K )$ is said to fix an element $\alpha \in K$ if $\sigma \alpha = \alpha$ . I f F is a subset of K (for example, a subfield), then an automorphism a is said to fix F if it fixes all the elements of F, i.e., $\pmb { \sigma } \pmb { a } = \pmb { a }$ for all $a \in F$
- **dependencies:** —


- **kind:** Definition
- **source:** §14.1; printed pp. 558–566; extraction line 20007
- **statement/data:** Let $K / F$ be an extension of fields. Let $\mathbf { A u t } ( K / F )$ be the collection of automorphisms of K which fix F. Note that if F is the prime subfield of K then $\operatorname { \mathbf { A u t } } ( K ) = \operatorname { \mathbf { A u t } } ( K / F )$ ) since every automorphism of K automatically fixes F. If (j and T are automorphisms of K then the composite $\pmb { \sigma \tau }$ (and also the composite $\pmb { \tau \sigma }$ , which may not be the same) is defined and is again an automorphism of K.
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §14.1; printed pp. 558–566; extraction line 20013
- **statement/data:** Aut(K) is a group under composition and $\mathbf { A u t } ( K / F )$ is a subgroup.
- **dependencies:** —


- **kind:** Proposition 2
- **source:** §14.1; printed pp. 558–566; extraction line 20019
- **statement/data:** Let $K / F$ be a field extension and let $\alpha \in K$ be algebraic over F. Then for any $\sigma \in \mathop { \mathrm { A u t } } ( K / F )$ , (j a is a root of the minimal polynomial for a over F i.e., $\mathbf { A u t } ( K / F )$ permutes the roots of ireducible polynomials. Equivalently, any polynomial with coefficients in F having a as a root also has (fa as a root.
- **dependencies:** —


- **kind:** Proposition 3
- **source:** §14.1; printed pp. 558–566; extraction line 20069
- **statement/data:** Let $H \leq \mathbf { A u t } ( K )$ be a subgroup of the group of automorphisms of K. Then the collection F of elements of K fixed by all the elements of H is a subfield of K .
- **dependencies:** —


- **kind:** Definition
- **source:** §14.1; printed pp. 558–566; extraction line 20075
- **statement/data:** If H is a subgroup of the group of automorphisms of K, the subfield of K fixed by all the elements of H is called the fixed field of H.
- **dependencies:** —


- **kind:** Proposition 4
- **source:** §14.1; printed pp. 558–566; extraction line 20077
- **statement/data:** The association of groups to fields and fields to groups defined above is inclusion reversing, namely (1) if $F _ { 1 } \subseteq F _ { 2 } \subseteq K$ are two subfields of K then $\mathsf { A u t } ( K / F _ { 2 } ) \le \mathsf { A u t } ( K / F _ { 1 } )$ . and (2) if $H _ { 1 } \leq H _ { 2 } \leq \mathrm { { A u t } } ( K )$ are two subgroups of automorphisms with associated fixed fields $F _ { 1 }$ and $F _ { 2 }$ , respectively, then $F _ { 2 } \subseteq F _ { 1 }$
- **dependencies:** —


- **kind:** Proposition 5
- **source:** §14.1; printed pp. 558–566; extraction line 20127
- **statement/data:** Let E be the spliting field over $F$ of the polynomial $f ( x ) \in F [ x ]$ Then $$ | \operatorname{Aut} (E / F) | \leq [ E: F ] $$ with equality if $f ( x )$ is separable over F .
- **dependencies:** —


- **kind:** Definition
- **source:** §14.1; printed pp. 558–566; extraction line 20139
- **statement/data:** Let $K / F$ be a finite extension. Then K is said to be Galois over F and $K / F$ is a Galois extension if $| \mathbf { A u t } ( K / F ) | = [ K : F ]$ . If $K / F$ is Galois the group of automorphisms $\scriptstyle \mathbf { A u t } ( K / F )$ is called the Galois group of $K / F$ , denoted $\operatorname { G a l } ( K / F )$ 1
- **dependencies:** —


- **kind:** Corollary 6
- **source:** §14.1; printed pp. 558–566; extraction line 20143
- **statement/data:** If K is the splitting field over F of a separable polynomial $f ( x )$ then $K / F$ is Galois. We shall see in the next section that the converse is also true, which will completely characterize Galois extensions. Note also that Corollary 6 implies that the splitting field of any polynomial over $\mathbb { Q }$ is Galois, since the splitting field of $f ( x )$ is clearly the same as the splitting field of the product of the irreducible factors of $f ( x )$ (i.e., the polynomial obtained by removing multiple factors), which is separable (Corollary 1 3. 34).
- **dependencies:** —


- **kind:** Definition
- **source:** §14.1; printed pp. 558–566; extraction line 20149
- **statement/data:** If $f ( x )$ is a separable polynomial over F, then the Galois group of $f ( x )$ over F is the Galois group of the splitting field of $f ( x )$ over F.
- **dependencies:** —


- **kind:** Construction
- **source:** §14.1; printed pp. 558–566; extraction line 20299
- **statement/data:** For F_{p^n}, the Frobenius automorphism is σ_p(α)=α^p.
- **dependencies:** FC01-C13-U060


- **kind:** Definition
- **source:** §14.2; printed pp. 567–584; extraction line 20369
- **statement/data:** A character1 x of a group $\pmb { G }$ with values in a field L is a homomorphism from G to the multiplicative group of L: $$ \chi : G \to L ^ {\times} $$ i.e., $\chi ( g _ { 1 } g _ { 2 } ) = \chi ( g _ { 1 } ) \chi ( g _ { 2 } )$ for all $g _ { 1 } , g _ { 2 } \in G$ and $\chi ( g )$ i s a nonzero element of $\pmb { L }$ for all $g \in G$
- **dependencies:** —


- **kind:** Definition
- **source:** §14.2; printed pp. 567–584; extraction line 20377
- **statement/data:** The characters $\chi _ { 1 } , \chi _ { 2 } , \ldots , \chi _ { n }$ of $\pmb { G }$ are said to be linearly independent over L if they are linearly independent as functions on $G ,$ i.e., if there is no nontrivia relation $$ a _ {1} \chi_ {1} + a _ {2} \chi_ {2} + \dots + a _ {n} \chi_ {n} = 0 \quad (a _ {1}, \dots , a _ {n} \in L \text { not all } 0)\tag{14.2} $$ as a function on $\pmb { G }$ (that is, $a _ { 1 } \chi _ { 1 } ( g ) + a _ { 2 } \chi _ { 2 } ( g ) + \cdot \cdot \cdot + a _ { n } \chi _ { n } ( g ) = 0 \mathrm { f o r } \mathrm { a l l } g \in G ) .$
- **dependencies:** —


- **kind:** Theorem 7 (Linear Independence of Characters)
- **source:** §14.2; printed pp. 567–584; extraction line 20385
- **statement/data:** (Linear Independence of Characters) If $\chi _ { 1 } , \chi _ { 2 } , \ldots , \chi _ { n }$ are distinct characters of G with values in L then they are linearly independent over L.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.2; printed pp. 567–584; extraction line 20419
- **statement/data:** An embedding K→L of fields is an injective field homomorphism.
- **dependencies:** —


- **kind:** Corollary 8
- **source:** §14.2; printed pp. 567–584; extraction line 20421
- **statement/data:** If $\sigma _ { 1 } , \sigma _ { 2 } , \ldots , \sigma _ { n }$ are distinct embeddings of a field K into a field $L ,$ then they are linearly independent as functions on $\pmb { K }$ . In particular distinct automorphisms of a field K are linearly independent as functions on $\pmb { K }$
- **dependencies:** —


- **kind:** Theorem 9
- **source:** §14.2; printed pp. 567–584; extraction line 20425
- **statement/data:** Let $G = { \sigma _ { 1 } = 1 , \sigma _ { 2 } , \ldots , \sigma _ { n } }$ be a subgroup of automorphisms of a field K and let F be the fixed field. Then $$ [ K: F ] = n = | G |. $$
- **dependencies:** —


- **kind:** Corollary 10
- **source:** §14.2; printed pp. 567–584; extraction line 20521
- **statement/data:** Let $K / F$ be any finite extension. Then $$ | \operatorname{Aut} (K / F) | \leq [ K: F ] $$ with equality if and only if F is the fixed field of $\operatorname { A u t } ( K / F )$ . Put another way, $K / F$ is Galois if and only if F is the fixed field of $\operatorname { A u t } ( K / F )$ .
- **dependencies:** —


- **kind:** Corollary 11
- **source:** §14.2; printed pp. 567–584; extraction line 20537
- **statement/data:** Let G be a finite subgroup of automorphisms of a field K and let F be the fixed field. Then every automorphism of K fixing F is contained in $G ,$ i.e., $\operatorname { A u t } ( K / F ) = G$ , so that $K / F$ is Galois, with Galois group G .
- **dependencies:** —


- **kind:** Corollary 12
- **source:** §14.2; printed pp. 567–584; extraction line 20547
- **statement/data:** If $G _ { 1 } \neq G _ { 2 }$ are distinct finite subgroups of automorphisms of a field K then their fixed fields are also distinct.
- **dependencies:** —


- **kind:** Theorem 13
- **source:** §14.2; printed pp. 567–584; extraction line 20555
- **statement/data:** The extension $K / F$ is Galois if and only if K is the spliting field of some separable polynomial over F. Furthermore, if this is the case then every irreducible polynomial with coeficients in F which has a root in K is separable and has all its roots in K (so in particular $K / F$ is a separable extension)
- **dependencies:** —


- **kind:** Definition
- **source:** §14.2; printed pp. 567–584; extraction line 20589
- **statement/data:** Let $K / F$ be a Galois extension. If $\alpha \in K$ the elements $\pmb { \sigma } \pmb { \alpha }$ for $\pmb { \sigma }$ in $\operatorname { G a l } ( K / F )$ are called the conjugates (or Galois conjugates) of $\pmb { \alpha }$ over F. If E is a subfield of K containing $F ,$ , the field $\pmb { \sigma } ( E )$ is called the conjugate field of E over F. The proof of the theorem shows that in a Galois extension $K / F$ the other roots of the minimal polynomial over F of any element $\alpha \in K$ are precisely the distinct conjugates of a under the Galois group of $K / F$ The second statement in this theorem also shows that K is not Galois over F if we can find even one ireducible polynomial over F having a root in K but not having all its roots in K. This justifies in a very strong sense the intuition from earlier examples that Galois extensions are extensions with "enough" distinct roots of irreducible polynomials (namely, if it contains one root then it contains all the rots). Finally, notice that we now have 4 characterizations of Galois extensions $K / F$ (1) splitting fields of separable polynomials over F (2) fields where F is precisely the set of elements fixed by $\mathsf { A u t } ( K / F )$ (in general, the fixed field may be larger than F) (3) fields with $[ K : F ] = | \mathbf { A u t } ( K / F ) |$ (the original definition) (4) finite, normal and separable extensions.
- **dependencies:** —


- **kind:** Theorem 14 (Fundamental Theorem of Galois Theory)
- **source:** §14.2; printed pp. 567–584; extraction line 20605
- **statement/data:** (Fundamental Theorem of Galois Theory) Let $K / F$ be a Galois extension and set $G = { \mathrm { G a l } } ( K / F )$ . Then there is a bijection $$ \left{ \begin{array}{c c} & K \ \text {subfields} E & | \ \text {of} K & E \ \text {containing} F & | \ & F \end{array} \right} \quad \longleftrightarrow \quad \left{ \begin{array}{c c} & 1 \ \text {subgroups} H & | \ \text {of} G & H \ & | \ & G \end{array} \right} $$ given by the correspondences $$ \begin{array}{c c c} E & \longrightarrow & \left{ \begin{array}{c} \text {the elements of G} \ \text {fixing E} \end{array} \right} \ \left{ \begin{array}{c} \text {the fixed field} \ \text {of H} \end{array} \right} & \longleftarrow & H \end{array} $$ which are inverse to each other. Under this corespondence, (1) (inclusion reversing) If $E _ { 1 } , E _ { 2 }$ corespond to $H _ { 1 } , H _ { 2 }$ , respectively, then $E _ { 1 } \subseteq E _ { 2 }$ if and only if $H _ { 2 } \leq H _ { 1 }$ (2) $[ K : E ] = | H |$ and $[ E : F ] = | G : H |$ , the index of H in G: $$ \begin{array}{l l l} K & \ \mid & } & | H | \ E & \ \mid & } & | G: H | \ F & \end{array} $$ (3) $K / E$ is always Galois, with Galois group $\mathrm { { G a l } } ( K / E ) = H$ $$ \begin{array}{c c} \boldsymbol {K} & \ | & \boldsymbol {H} \ \boldsymbol {E} & \end{array} $$ ( 4) E is Galois over F if and only if H is a normal subgroup in G . If this is the case, then the Galois group is isomorphic to the quotient group $$ \operatorname{Gal} (E / F) \cong G / H. …
- **dependencies:** —


- **kind:** Named example
- **source:** §14.2; printed pp. 567–584; extraction line 20689
- **statement/data:** The Galois correspondences for Q(√2,√3) and Q(∛2,ρ) are worked out as standard applications of the Fundamental Theorem of Galois Theory.
- **dependencies:** —


- **kind:** Named example
- **source:** §14.2; printed pp. 567–584; extraction line 20697
- **statement/data:** Q(√2+√3) is the standard primitive-element example for a biquadratic extension, including its conjugates and minimal polynomial.
- **dependencies:** —


- **kind:** Named example
- **source:** §14.2; printed pp. 567–584; extraction line 20719
- **statement/data:** The splitting field of x^8−2 is worked out as a nonabelian Galois-group example.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §14.2; printed pp. 567–584; extraction line 20850
- **statement/data:** The group ⟨σ,τ | σ^8=τ^2=1, στ=τσ^3⟩ arising as Gal(Q(2^{1/8},i)/Q) is called quasidihedral; it is contrasted with the dihedral group of order 16.
- **dependencies:** —


- **kind:** Convention
- **source:** §14.3; printed pp. 585–590; extraction line 21076
- **statement/data:** The unique finite field with p^n elements is denoted F_{p^n}.
- **dependencies:** FC01-C14-U030


- **kind:** Proposition 15
- **source:** §14.3; printed pp. 585–590; extraction line 21096
- **statement/data:** Any finite field is isomorphic to $\mathbb { F } _ { p ^ { n } }$ for some prime p and some integer $n \geq 1$ . The field $\mathbb { F } _ { p ^ { n } }$ is the splitting field over $\mathbb { F } _ { p }$ of the polynomial $x ^ { p ^ { n } } - x ,$ , with cyclic Galois group of order n generated by the Frobenius automorphism $\sigma _ { p }$ . The subfields of $\mathbb { F } _ { p ^ { n } }$ are all Galois over $\mathbb { F } _ { p }$ and are in one to one corespondence with the divisors d of n. They are the fields $\mathbb { F } _ { p ^ { d } }$ , the fixed fields of ${ \sigma _ { p } } ^ { d }$ The coresponding statements for the finite extensions of any finite field are easy consequences of Proposition 15 and are outlined in the exercises. As an elementary application we have the following result on the polynomial $x ^ { 4 } + 1$ in $\mathbb { Z } [ x ]$
- **dependencies:** —


- **kind:** Corollary 16
- **source:** §14.3; printed pp. 585–590; extraction line 21102
- **statement/data:** The irreducible polynomial $x ^ { 4 } + 1 \in \mathbb { Z } [ x ]$ is reducible modulo every prime p.
- **dependencies:** —


- **kind:** Proposition 17
- **source:** §14.3; printed pp. 585–590; extraction line 21114
- **statement/data:** The finite field $\mathbb { F } _ { p ^ { n } }$ is simple. In particular, there exists an irreducible polynomial of degree n over $\mathbb { F } _ { p }$ for every $n \geq 1$ We have described the finite fields $\mathbb { F } _ { p ^ { n } }$ above as the splitting fields of the polynomials $x ^ { p ^ { n } } - x$ . By the previous proposition, this field can also be described as a quotient of $\mathbb { F } _ { p } [ { \boldsymbol { x } } ]$ , namely by the minimal polynomial for $\pmb { \theta } .$ . Since $\theta$ is necessarily a root of $x ^ { p ^ { n } } - x$ we see that the minimal polynomial for e is a divisor of $x ^ { p ^ { n } } - x$ o f degree n. Conversely, let $p ( x )$ be any irreducible polynomial of degree $^ { d , }$ , say, dividing $x ^ { p ^ { n } } - x$ . If a is a root of $p ( x )$ , then the extension $\mathbb { F } _ { p } ( \pmb { \alpha } )$ is a subfield of $\mathbb { F } _ { p ^ { n } }$ of de gree d. Hence d is a divisor of and the extension is Galois by Proposition 15 (in fact, the extension $\mathbb { F } _ { p ^ { d } } )$ so in particular all the roots of $p ( x )$ are contained in $\mathbb { F } _ { p } ( \pmb { \alpha } )$ The elements of $\mathbb { F } _ { p ^ { n } }$ are precisely the roots of $x ^ { p ^ { n } } - x$ . If we group together the factors $x - \alpha$ of this polynomial according to the degree d of their minmal polynomials over $\mathbb { F } _ { p } ,$ we obtain
- **dependencies:** FC01-C14-U030


- **kind:** Proposition 18
- **source:** §14.3; printed pp. 585–590; extraction line 21124
- **statement/data:** The polynomial $x ^ { p ^ { n } } - x$ is precisely the product of all the distinct ireducible polynomials in $\mathbb { F } _ { p } [ { \boldsymbol { x } } ]$ of degree d where d runs through all divisors of n
- **dependencies:** —


- **kind:** Definition
- **source:** §14.3; printed pp. 585–590; extraction line 21164
- **statement/data:** The Möbius function satisfies μ(1)=1, μ(n)=0 when n has a squared prime factor, and μ(p_1⋯p_r)=(−1)^r for distinct primes.
- **dependencies:** —


- **kind:** Proposition 19
- **source:** §14.4; printed pp. 591–595; extraction line 21334
- **statement/data:** Suppose $K / F$ is a Galois extension and $F ^ { \prime } / F$ is any extension. Then $K F ^ { \prime } / F ^ { \prime }$ is a Galois extension, with Galois group $$ \operatorname{Gal} (K F ^ {\prime} / F ^ {\prime}) \cong \operatorname{Gal} (K / K \cap F ^ {\prime}) $$ isomorphic to a subgroup of $\operatorname { G a l } ( K / F )$ . Pictorially,
- **dependencies:** —


- **kind:** Corollary 20
- **source:** §14.4; printed pp. 591–595; extraction line 21362
- **statement/data:** Suppose $K / F$ is a Galois extension and $F ^ { \prime } / F$ is any finite extension. Then $$ [ K F ^ {\prime}: F ] = \frac {[ K : F ] [ F ^ {\prime} : F ]}{[ K \cap F ^ {\prime} : F ]}. $$
- **dependencies:** —


- **kind:** Proposition 21
- **source:** §14.4; printed pp. 591–595; extraction line 21372
- **statement/data:** Let $K _ { 1 }$ and $K _ { 2 }$ be Galois extensions of a field F. Then (1) The intersection $K _ { 1 } \cap K _ { 2 }$ is Galois over F . (2) The composite $K _ { 1 } K _ { 2 }$ is Galois over F. The Galois group is isomorphic to the subgroup $$ H = {(\sigma , \tau) | \sigma | _ {K _ {1} \cap K _ {2}} = \tau | _ {K _ {1} \cap K _ {2}} } $$ of the direct product $\mathbf { G a l } ( K _ { 1 } / F ) \times \mathbf { G a l } ( K _ { 2 } / F )$ consisting of elements whose restrictions to the intersection $K _ { 1 } \cap K _ { 2 }$ are equal.
- **dependencies:** —


- **kind:** Corollary 22
- **source:** §14.4; printed pp. 591–595; extraction line 21416
- **statement/data:** Let $K _ { 1 }$ and $K _ { 2 }$ be Galois extensions of a field F with $K _ { 1 } \cap K _ { 2 } = F$ Then $$ \operatorname{Gal} (K _ {1} K _ {2} / F) \cong \operatorname{Gal} (K _ {1} / F) \times \operatorname{Gal} (K _ {2} / F). $$ Conversely, if K is Galois over F and $\boldsymbol { G } = \mathbf { G a l } ( \boldsymbol { K } / F ) = \boldsymbol { G } _ { 1 } \times \boldsymbol { G } _ { 2 }$ is the direct produc of two subgroups $G _ { 1 }$ and $G _ { 2 }$ , then K is the composite of two Galois extensions $K _ { 1 }$ and $K _ { 2 }$ of $F$ with $K _ { 1 } \cap K _ { 2 } = F$
- **dependencies:** —


- **kind:** Corollary 23
- **source:** §14.4; printed pp. 591–595; extraction line 21426
- **statement/data:** Let $E / F$ be any finite separable extension. Then E is contained in an extension K which is Galois over F and is minimal in the sense that in a fixed algebraic closure of K any other Galois extension of F containing E contains K.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.4; printed pp. 591–595; extraction line 21430
- **statement/data:** The Galois extension K of F containing E in the previous corollary is called the Galois closure of E over F. It is often simpler to work in a Galois extension (for example in computing degrees as in Corollary 20). The existence of a Galois closure for a separable extension is frequently useful for reducing computations to consideration of Galois extensions.
- **dependencies:** FC01-C14-U036


- **kind:** Proposition 24
- **source:** §14.4; printed pp. 591–595; extraction line 21436
- **statement/data:** Let $K / F$ be a finite extension. Then $K = F ( \theta )$ if and only if there exist only finitely many subfields of K containing F.
- **dependencies:** —


- **kind:** Theorem 25 (The Primitive Element Theorem)
- **source:** §14.4; printed pp. 591–595; extraction line 21466
- **statement/data:** (The Primitive Element Theorem) If $K / F$ is finite and separable, then $K / F$ is simple. In particular, any finite extension of fields of characteristic 0 is simple.
- **dependencies:** —


- **kind:** Theorem 26
- **source:** §14.5; printed pp. 596–605; extraction line 21522
- **statement/data:** The Galois group of the cyclotomic field $\mathbb { Q } ( \xi _ { n } )$ of $n ^ { \mathrm { t h } }$ rots of unity is isomorphic to the multiplicative group $( \mathbb { Z } / n \mathbb { Z } ) ^ { \times }$ . The isomorphism is given explicitly by the map $$ \begin{array}{c} (\mathbb {Z} / n \mathbb {Z}) ^ {\times} \stackrel {{\sim}} {{\longrightarrow}} \operatorname{Gal} (\mathbb {Q} (\zeta_ {n}) / \mathbb {Q}) \ a (\mathrm{mod} n) \longmapsto \sigma_ {a} \end{array} $$ where $\sigma _ { \alpha }$ is the automorphism defined by $$ \sigma_ {a} (\zeta_ {n}) = \zeta_ {n} ^ {a}. $$
- **dependencies:** —


- **kind:** Construction
- **source:** §14.5; printed pp. 596–605; extraction line 21609
- **statement/data:** Gaussian periods are sums of conjugate roots of unity associated to subgroups in the cyclotomic Galois group; their systematic study is called cyclotomy.
- **dependencies:** —


- **kind:** Corollary 27
- **source:** §14.5; printed pp. 596–605; extraction line 21613
- **statement/data:** Let $\pmb { n } = p _ { 1 } ^ { a _ { 1 } } p _ { 2 } ^ { a _ { 2 } } \cdot \cdot \cdot p _ { k } ^ { a _ { k } }$ be the decomposition of the positive integer n into distinct prime powers. Then the cyclotomic fields $\mathbb { Q } ( \xi _ { p _ { z } ^ { a _ { i } } } ) , i = 1 , 2 , \ldots , k$ intersect only in the field Q and their composite is the cyclotomic field $\mathbb { Q } ( \xi _ { n } )$ . We have $$ \operatorname{Gal} \left(\mathbb {Q} \left(\zeta_ {n}\right) / \mathbb {Q}\right) \cong \operatorname{Gal} \left(\mathbb {Q} \left(\zeta_ {p _ {1} ^ {a _ {1}}}\right) / \mathbb {Q}\right) \times \operatorname{Gal} \left(\mathbb {Q} \left(\zeta_ {p _ {2} ^ {a _ {2}}}\right) / \mathbb {Q}\right) \times \dots \times \operatorname{Gal} \left(\mathbb {Q} \left(\zeta_ {p _ {k} ^ {a _ {k}}}\right) / \mathbb {Q}\right) $$ which under the isomorphism in Theorem 26 is the Chinese Remainder Theorem: $$ (\mathbb {Z} / n \mathbb {Z}) ^ {\times} \cong (\mathbb {Z} / p _ {1} ^ {a _ {1}} \mathbb {Z}) ^ {\times} \times (\mathbb {Z} / p _ {2} ^ {a _ {2}} \mathbb {Z}) ^ {\times} \times \dots \times (\mathbb {Z} / p _ {k} ^ {a _ {k}} \mathbb {Z}) ^ {\times}. $$
- **dependencies:** FC01-C14-U043


- **kind:** Definition
- **source:** §14.5; printed pp. 596–605; extraction line 21629
- **statement/data:** The extension $K / F$ is called an abelian extension if $K / F$ is Galois and $\operatorname { G a l } ( K / F )$ is an abelian group. Since al the subgroups and quotient groups of abelian groups are abelian, we see by the Fundamental Theorem of Galois Theory that every subfield containing F of an abelian extension of F is again an abelian extension of $F .$ . By the results on composites of extensions in the last section, we also see that the composite of abelian extensions is again an abelian extension (since the Galois group of the composite is isomorphic to a subgroup of the direct product of the Galois groups, hence is abelian). It is an open problem to determine which groups arise as the Galois groups of Galois extensions of $\mathbb { Q } .$ . Using the results above we can see that every abelian group appears as the Galois group of some extension of $\mathbb { Q } ,$ in fact as the Galois group of some subfield of a cyclotomic field. Let $n = p _ { 1 } p _ { 2 } \cdots p _ { k }$ be the product of distinct primes. Then by the Chinese Remainder Theorem $$ \begin{array}{r c l} (\mathbb {Z} / n \mathbb {Z}) ^ {\times} & \cong & (\mathbb {Z} / p _ {1} \mathbb {Z}) ^ {\times} \times (\mathbb {Z} / p _ {2} \mathbb {Z}) ^ {\times} \times \dots \times (\mathbb {Z} / p _ {k} \mathbb {Z}) ^ {\times} \ & \cong & Z _ {p _ {1} - 1} \times Z _ {p _ {2} - 1} \times \dots \times Z _ {p _ {k} - 1}. \end{array}\tag{14.11} $$ Now, suppose $\pmb { G }$ is any finite abelian group. …
- **dependencies:** —


- **kind:** Corollary 28
- **source:** §14.5; printed pp. 596–605; extraction line 21659
- **statement/data:** Let G be any finite abelian group. Then there is a subfield K of a cyclotomic field with ${ \mathrm { G a l } } ( K / \mathbb { Q } ) \cong G$ There is a converse to this result (whose prof is beyond our scope), the celebrated Kronecker-Weber Theorem:
- **dependencies:** —


- **kind:** Theorem (Kronecker-Weber)
- **source:** §14.5; printed pp. 596–605; extraction line 21663
- **statement/data:** (Kronecker-Weber) Let K be a finite abelian extension of $\mathbb { Q } .$ Then K is contained in a cyclotomic extension of Q The abelian extensions of Q are the "easiest" Galois extensions (at least in so far as the structure of their Galois groups is concerned) and the previous result shows they can be classified by the cyclotomic extensions of Q. For other finite extensions of Q as base field, it is more dificult to describe the abelian extensions. The study of the abelian extensions of an arbitrary finite extension $F$ of Q is refered to as class field theory. There is a classification of the abelian extensions of $F$ by invariants associated to F which greatly generalizes the results on cyclotomic fields over $\mathbb { Q } .$ In general, however, the construction of abelian extensions is not nearly as explicit as in the case of the cyclotomic fields. One case where such a description is possible is for the abelian extensions of an imaginary quadratic field $\textstyle ( \mathbb { Q } ( { \sqrt { - D } } )$ ) for $D$ positive), where the abelian extensions can be constructed by adjoining values of certain elliptic functions (this is the analogue of adjoining the roots of unity, which are the values of the exponential function $e ^ { x }$ for certain ) The study of the arithmetic of such abelian extensions and the search for similar results for non-abelian extensions are rich and fascinating areas of current mathematical research We end our discussion of the cyclotomic fields with the problem of the constructibility of the regular n-gon by straightedge and compass. …
- **dependencies:** —


- **kind:** Definition
- **source:** §14.5; printed pp. 596–605; extraction line 21705
- **statement/data:** A Fermat prime is a prime of the form 2^{2^m}+1.
- **dependencies:** —


- **kind:** Proposition 29
- **source:** §14.5; printed pp. 596–605; extraction line 21713
- **statement/data:** The regular n-gon can be constructed by straightedge and compass if and only if $n = 2 ^ { k } p _ { 1 } \cdot \cdot \cdot p _ { r }$ is the product of a power of 2 and distinct Fermat primes. The proof above actually indicates a procedure for constructing the regular n-gon as a succession of square roots. For example, the construction of the regular 17 -gon (solved by Gauss in 1796 at age 19) requires the construction of the subfields of degrees 2, 4, 8 and 16 in $\mathbb { Q } ( \zeta _ { 1 7 } )$ . These subfields can be constructed by forming the periods of $\xi _ { 1 7 }$ as in the example of the $1 3 ^ { \mathrm { t h } }$ roots of unity above. In this case, the fact that $\mathbb { Q } ( \zeta _ { 1 7 } )$ is obtained by a series of quadratic extensions reflects itself in the fact that the periods can be "halved" successively (i.e., if $H _ { 1 } < H _ { 2 }$ are subgroups with $[ H _ { 2 } : H _ { 1 } ] = 2$ then the periods for $H _ { 1 }$ satisfy a quadratic equation whose coefficients involve the periods for $H _ { 2 } )$ . …
- **dependencies:** —


- **kind:** Definition
- **source:** §14.6; printed pp. 606–624; extraction line 21896
- **statement/data:** Let $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$ be indeterminates. Tbe elementary symmetricfunctions $s _ { 1 } , s _ { 2 } , \ldots , s _ { n }$ are defined by $$ \begin{array}{l} s _ {1} = x _ {1} + x _ {2} + \dots + x _ {n} \ s _ {2} = x _ {1} x _ {2} + x _ {1} x _ {3} + \dots + x _ {2} x _ {3} + x _ {2} x _ {4} + \dots + x _ {n - 1} x _ {n} \ \vdots \ s _ {n} = x _ {1} x _ {2} \dots x _ {n} \end{array} $$ i.e. , the $i ^ { \mathrm { t h } }$ symetric function $s _ { i }$ of $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$ is the sum of all products of the $x _ { j } { ' } { \bf s }$ taken i at a time.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.6; printed pp. 606–624; extraction line 21904
- **statement/data:** The general polynomial of degree n is the polynomial $$ (x - x _ {1}) (x - x _ {2}) \dots (x - x _ {n}) $$ whose rots are the indeterminates $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$
- **dependencies:** —


- **kind:** Proposition 30
- **source:** §14.6; printed pp. 606–624; extraction line 21930
- **statement/data:** The fixed field of the symmetric group $S _ { n }$ acting on the field of rational functions in n variables $F ( x _ { 1 } , x _ { 2 } , \ldots , x _ { n } )$ is the field of rational functions in the elementary symetric functions $F ( s _ { 1 } , s _ { 2 } , \ldots , s _ { n } )$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §14.6; printed pp. 606–624; extraction line 21932
- **statement/data:** Arational function $f ( x _ { 1 } , x _ { 2 } , \ldots , x _ { n } )$ is called symmetric if it is not changed by any permutation of the variables $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$
- **dependencies:** —


- **kind:** Corollary 31 (Fundamental Theorem on Symmetric Functions)
- **source:** §14.6; printed pp. 606–624; extraction line 21934
- **statement/data:** (Fundamental Theorem on Symmetric Functions) Any symetric function in the variables $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$ is a rational function in the elementary symetric functions $s _ { 1 } , s _ { 2 } , \ldots , s _ { n }$
- **dependencies:** —


- **kind:** Theorem 32
- **source:** §14.6; printed pp. 606–624; extraction line 21978
- **statement/data:** The general polynomial $$ x ^ {n} - s _ {1} x ^ {n - 1} + s _ {2} x ^ {n - 2} + \dots + (- 1) ^ {n} s _ {n} $$ over the field $F ( s _ { 1 } , s _ { 2 } , \ldots , s _ { n } )$ is separable with Galois group $S _ { n }$ . This result says that if there are no relations among the coeficients of a polynomial of degree n (which is what we mean when we say the $s _ { i }$ are indeterminates above) then the Galois group of this polynomial over the field generated by its coefficients is the full symmetric group $s _ { n }$ . Loosely speaking, this means that the "generic" polynomial of degree n will have $s _ { n }$ as Galois group. Note, however, that over finite fields every polynomial has a cyclic Galois group (all extensions of finite fields are cyclic), so that "generic" polynomials in this sense do not exist. Over $\mathbb { Q }$ one can make precise the notion of "generic" polynomial and then it is true that most polynomials have the ful symetric group as Galois group. For $n \geq 5$ there is only one normal subgroup of $S _ { n }$ , namely the subgroup $A _ { n }$ of index 2. Hence in general there is only one normal subfield of $F ( x _ { 1 } , x _ { 2 } , \ldots , x _ { n } )$ containing $F ( s _ { 1 } , s _ { 2 } , \ldots , s _ { n } )$ and it is an extension of degree 2.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.6; printed pp. 606–624; extraction line 21990
- **statement/data:** Define the discriminant D of $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$ by the formula $$ D = \prod_ {i < j} (x _ {i} - x _ {j}) ^ {2}. $$ Define the discrimnant of a polynomial to be the discriminant of the roots of the polynomial. The discrimnant D is a symetric function in $x _ { 1 } , \ldots , x _ { n }$ , hence is an element of $K = F ( s _ { 1 } , s _ { 2 } , \ldots , s _ { n } )$ When we first defined the alternating group $A _ { n }$ we saw that a permutation $\sigma \in S _ { n }$ is an element of the subgroup $A _ { n }$ if and only if $\pmb { \sigma }$ fixes the product $$ \sqrt {D} = \prod_ {i < j} (x _ {i} - x _ {j}) \in \mathbb {Z} [ x _ {1}, x _ {2}, \dots , x _ {n} ]. $$ It follows (by the Fundamental Theorem) that if F has characteristic diferent from 2 then $\sqrt { D }$ generates the fixed field of $A _ { n }$ and generates a quadratic extension of K. This proves the following proposition.
- **dependencies:** —


- **kind:** Construction
- **source:** §14.6; printed pp. 606–624; extraction line 21996
- **statement/data:** The discriminant of a polynomial is the discriminant of its roots; it is symmetric in the roots and vanishes exactly when roots repeat.
- **dependencies:** FC01-C14-U057


- **kind:** Proposition 33
- **source:** §14.6; printed pp. 606–624; extraction line 22008
- **statement/data:** If $\mathbf { c h } ( F ) \neq 2$ then the permutation $\sigma \in S _ { n }$ is an element of $A _ { n }$ if and only if it fixes the square root of the discriminant $D$ We now consider the Galois groups of separable polynomials of small degree $( \leq 4 )$ over a field F which we assume is of characteristic diferent from 2 and 3. Note that over Q or over a finite field (or, more generally, over any perfect field) the splitting field of an arbitrary polynomial $f ( x )$ is the same as the splitting field for the product of the irreducible factors of $f ( x )$ taken precisely once, which is a separable polynomial. If the roots of the polynomial $f ( x ) = x ^ { n } + a _ { n - 1 } x ^ { n - 1 } + \cdot \cdot \cdot + a _ { 1 } x + a _ { 0 }$ are $\alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { n }$ , then the discrimnant of $f ( x ) \mathrm { i } s ^ { 2 }$ $$ D = \prod_ {i < j} (\alpha_ {i} - \alpha_ {j}) ^ {2}. $$
- **dependencies:** —


- **kind:** Proposition 34
- **source:** §14.6; printed pp. 606–624; extraction line 22032
- **statement/data:** The Galois group of $f ( x ) \in F [ x ]$ is a subgroup of $A _ { n }$ if and only if the discriminant $D \in F$ is the square of an element of F.
- **dependencies:** —


- **kind:** Construction
- **source:** §14.6; printed pp. 606–624; extraction line 22196
- **statement/data:** The cubic obtained from the three pairings of four roots in solving a quartic is called its resolvent cubic.
- **dependencies:** —


- **kind:** Theorem 35 (Fundamental Theorem of Algebra)
- **source:** §14.6; printed pp. 606–624; extraction line 22246
- **statement/data:** (Fundamental Theorem of Algebra) Every polynomial $f ( x ) \in \mathbb { C } [ x ]$ of degree n has precisely n roots in C (counted with multiplicity). Equivalently, C is algebraically closed.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.7; printed pp. 625–639; extraction line 22562
- **statement/data:** The extension $K / F$ is said to b e cyclic if i t is Galois with a cyclic Galois group.
- **dependencies:** —


- **kind:** Proposition 36
- **source:** §14.7; printed pp. 625–639; extraction line 22564
- **statement/data:** Let F be a field of characteristic not dividing n which contains the $n ^ { \mathrm { t h } }$ roots of unity. Then the extension $F ( \sqrt [ n ] { a } )$ for $a \in F$ is cyclic over F of degree dividing n.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.7; printed pp. 625–639; extraction line 22586
- **statement/data:** For $\alpha \in K$ and any $n ^ { \mathrm { t h } }$ root of unity $\zeta ,$ , define the Lagrange resolvent $( \alpha , \zeta ) \in K$ by $$ (\alpha , \zeta) = \alpha + \zeta \sigma (\alpha) + \zeta^ {2} \sigma^ {2} (\alpha) + \dots + \zeta^ {n - 1} \sigma^ {n - 1} (\alpha). $$ If we apply the automorphism $\sigma$ to $( \alpha , \zeta )$ we obtain $$ \sigma (\alpha , \zeta) = \sigma \alpha + \zeta \sigma^ {2} (\alpha) + \zeta^ {2} \sigma^ {3} (\alpha) + \dots + \zeta^ {n - 1} \sigma^ {n} (\alpha) $$ since $\boldsymbol { \zeta }$ is an element of the base field F so is fixed by a . We have $\zeta ^ { n } = 1$ in $\mu _ { n }$ and $\sigma ^ { n } = 1$ in $\operatorname { G a l } ( K / F )$ so this can be written $$ \begin{array}{r l} \sigma (\alpha , \zeta) & = \sigma \alpha + \zeta \sigma^ {2} (\alpha) + \zeta^ {2} \sigma^ {3} (\alpha) + \dots + \zeta^ {- 1} \alpha \ & = \zeta^ {- 1} (\alpha + \zeta \sigma (\alpha) + \zeta^ {2} \sigma^ {2} (\alpha) + \dots + \zeta^ {n - 1} \sigma^ {n - 1} (\alpha)) \ & = \zeta^ {- 1} (\alpha , \zeta). \end{array}\tag{14.19} $$ It follows that $$ \sigma (\alpha , \zeta) ^ {n} = (\zeta^ {- 1}) ^ {n} (\alpha , \zeta) ^ {n} = (\alpha , \zeta) ^ {n} $$ so that $( \alpha , \zeta ) ^ { n }$ is fixed by $\operatorname { G a l } ( K / F )$ , hence is an element of F for any $\alpha \in K$ Let l; be a primitive $n ^ { \mathrm { t h } }$ root of unity. …
- **dependencies:** —


- **kind:** Proposition 37
- **source:** §14.7; printed pp. 625–639; extraction line 22620
- **statement/data:** Any cyclic extension of degree n over a field F of characteristic not dividing n which contains the $n ^ { \mathrm { t h } }$ roots of unity is of the form $F ( \sqrt [ n ] { a } )$ for some $a \in F$
- **dependencies:** —


- **kind:** Definition
- **source:** §14.7; printed pp. 625–639; extraction line 22632
- **statement/data:** Under characteristic and roots-of-unity hypotheses, Kummer extensions are finite abelian extensions of exponent n classified by finitely generated subgroups of F×/(F×)^n.
- **dependencies:** FC01-C14-U066


- **kind:** Definition
- **source:** §14.7; printed pp. 625–639; extraction line 22638
- **statement/data:** (1) An element a which is algebraic over F can be expressed by radicals or solved for in terms of radicals if a is an element of a field K which can be obtained by a succession of simple radical extensions $$ F = K _ {0} \subset K _ {1} \subset \dots \subset K _ {i} \subset K _ {i + 1} \subset \dots \subset K _ {s} = K\tag{14.21} $$ where $K _ { i + 1 } = K _ { i } ( \sqrt [ n _ { i } ] { a _ { i } } )$ for some $a _ { i } \in K _ { i } , i = 0 , 1 , \dots , s - 1$ . Here $\sqrt [ n ] { a _ { i } }$ denotes some root of the polynomial $x ^ { n _ { i } } - a _ { i }$ . Such a field K will be called a root extension of F. (2) A polynomial $f ( x ) \in F [ x ]$ can be solved by radicals if all its rots can be solved for in terms of radicals
- **dependencies:** —


- **kind:** Lemma 38
- **source:** §14.7; printed pp. 625–639; extraction line 22666
- **statement/data:** If a is contained in a root extension K as in (21 ) above, then a is contained in a root extension which is Galois over F and where each extension $K _ { i + 1 } / K _ { i }$ is cyclic.
- **dependencies:** —


- **kind:** Theorem 39
- **source:** §14.7; printed pp. 625–639; extraction line 22694
- **statement/data:** The polynomial $f ( x )$ can be solved by radicals if and only if its Galois group is a solvable group.
- **dependencies:** —


- **kind:** Corollary 40
- **source:** §14.7; printed pp. 625–639; extraction line 22718
- **statement/data:** The general equation of degree cannot be solved by radicals for $n \geq 5$
- **dependencies:** —


- **kind:** Theorem
- **source:** §14.8; printed pp. 640–644; extraction line 23164
- **statement/data:** For any prime $\pmb { p }$ not dividing the discrimnant D of $f ( x ) \in \mathbb { Z } [ x ]$ , the Galois group over $\mathbb { F } _ { p }$ of the reduction ${ \overline { { f } } } ( x ) = f ( x )$ (mod $p )$ is permutation group isomorphic to a subgroup of the Galois group over Q of $f ( x )$ The meaning of the statement "permutation group isomorphic" in the theorem is that not only is the Galois group of the reduction ${ \overline { { f } } } ( x )$ mod $\pmb { p }$ of $f ( x )$ isomorphic to a subgroup of the Galois group of $f ( x )$ but that there is an ordering of the rots of ${ \overline { { f } } } ( x )$ and of $f ( x )$ (depending on $p )$ so that under this isomorphism the action of the coresponding automorphisms as permutations of these roots is the same. In particular there are automorphisms in the Galois group of $f ( x )$ with the same cycle types as the automorphisms of ${ \overline { { f } } } ( x )$ The Galois group of ${ \overline { { f } } } ( x )$ is a cyclic group since every finite extension of $\mathbb { F } _ { p }$ is a cyclic extension. Let $\sigma$ be a generator for this Galois group over $\mathbb { F } _ { p }$ (for example, the Frobenius automorphism). The roots of $\overline { { f } } _ { 1 } ( x )$ are permuted amongst themselves by the Galois group, and given any two of these roots there is a Galois automorphism taking the first root to the second (recall that the group is said to be transitive on the roots when this is the case). …
- **dependencies:** —


- **kind:** Corollary 41
- **source:** §14.8; printed pp. 640–644; extraction line 23174
- **statement/data:** For any prime p not dividing the discriminant of $f ( x ) \in \mathbb { Z } [ x ]$ , the Galois group of $f ( x )$ over $\mathbb { Q }$ contains an element with cycle decomposition $( n _ { 1 } , n _ { 2 } , \ldots , n _ { k } )$ where $n _ { 1 } , n _ { 2 } , \ldots , n _ { k }$ are the degrees of the ireducible factors of $f ( x )$ ) reduced modulo $\pmb { p } .$
- **dependencies:** —


- **kind:** Proposition 42
- **source:** §14.8; printed pp. 640–644; extraction line 23192
- **statement/data:** For each $n \in \mathbb { Z } ^ { + }$ there exist infinitely many polynomials $f ( x ) \in \mathbb { Z } [ x ]$ with $S _ { n }$ as Galois group over $\mathbb { Q } .$ There are extremely efficient algorithms for factoring polynomials $f ( x ) \in \mathbb { Z } [ x ]$ modulo $\pmb { p }$ (cf. Exercises 12 to 17 of Section 3), so the corollary above is an efective procedure for determining some of the cycle types of the elements of the Galois group. In using Corollary 41 some care should be taken not to assume that a particular cycle is an element of the Galois group. For example, one factorization might imply the existence of a (2,2) cycle, say ( 1 2)(34) and another factorization imply the existence of a transposition. One cannot conclude that the transposition is necessarily ( 1 2), however (nor (34), nor ( 1 3), etc.). The choice of ( 1 2)(34) to represent the first cycle fixes a particular ordering on the rots and this may not be the ordering with respect to which the transposition appears as ( 1 2). Corollary 41 is particularly eficient in determining when the Galois group is large $( \boldsymbol { \mathbf { e } } . \boldsymbol { \mathbf { g } } . , \ : S _ { n } )$ , since a transitive group containing sufficiently many cycle types must be $S _ { n }$ (for example, a transitive subgroup of $S _ { n }$ containing a transposition and an $n - 1 \cdot$ cycle is $S _ { n }$ , as used above). The most dificult Galois groups to determine in this way are the small Galois groups (e.g. …
- **dependencies:** FC01-C14-U073


- **kind:** Theorem
- **source:** §14.8; printed pp. 640–644; extraction line 23198
- **statement/data:** The density of primes p for which $f ( x )$ splits into type T modulo $\pmb { p }$ is precisely $d _ { T }$ . This says that if we knew the factorization of $f ( x )$ modulo every prime we could at least determine the number of elements of G with a given cycle type. Unfortunately, even this would not be suficient to determine G (up to isomorphism): it is known that there are nonisomorphic groups containing the same number of elements of al cycle types (there are two nonisomorphic groups of order 96 in $s _ { 8 }$ both having cycle type distributions: 1 1 -cycle, 6 (2,2)-cycles, l3 (2,2,2,2)-cycles, 32 (3,3)-cycles, 1 2 (4,4)-cycles, 3 2 (2,6)-cycles). There are infinitely many such examples (the regular representation of the elementary abelian group of order $p ^ { \bar { 3 } }$ and for the nonabelian group of order $p ^ { 3 }$ of exponent p give two nonisomorphic groups in $S _ { p ^ { 3 } }$ whose nonidentity elements are all the product of $p ^ { 2 }$ p-cycles for any prime $p )$ . In practice one uses the factorizations of $f ( x )$ modulo small primes to get an idea of the probable Galois group (based on the previous result). One then tries to prove this is indeed the Galois group - often a dificult problem. For polynomials of small degree, definitive algorithms exist, based in part on the computation of resolvent polynomials. These are analogues of the cubic resolvent used in the previous sections to determine the Galois group of quartic polynomials. …
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23260
- **statement/data:** (1) A subset ${ a _ { 1 } , a _ { 2 } , \ldots , a _ { n } }$ of E is called algebraically independent over F if there is no nonzero polynomial $f ( x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ) \in F [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ such that $f ( a _ { 1 } , a _ { 2 } , \ldots , a _ { n } ) = 0$ . An arbitrary subset S of E is called algebraically independent over F if every finite subset of S is algebraically independent. The elements of S are called independent transcendentals over $F$ (2) A transcendence base for $E / F$ i s a maximal subset (with respect t o inclusion) of E which is algebraically independent over $F .$
- **dependencies:** —


- **kind:** Theorem
- **source:** §14.9; printed pp. 645–655; extraction line 23268
- **statement/data:** The extension $E / F$ has a transcendence base and any two transcendence bases of $E / F$ have the same cardinality.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23272
- **statement/data:** The cardinality of a transcendence base for $E / F$ is called the transcendence degree of $E / F$ Algebraic extensions are precisely the extensions of transcendence degree 0 One special case of this theorem is when E is finitely generated over $F ,$ , that is, $E = F ( \alpha _ { 1 } , \alpha _ { 2 } , \ldots , \alpha _ { n } )$ , for some (not necessarily algebraically independent) elements $\alpha _ { 1 } , \ldots , \alpha _ { n }$ of $E .$ . It is clear that we may renumber $\alpha _ { 1 } , \ldots , \alpha _ { n }$ so that $\alpha _ { 1 } , \ldots , \alpha _ { m }$ are independent transcendentals and $\alpha _ { m + 1 } , \ldots , \alpha _ { n }$ are algebraic over $F ( \alpha _ { 1 } , \ldots , \alpha _ { m } )$ (so E is a finite extension of the latter field). In this case E is called a function field in m variables over F. Such fields play a fundamental role in algebraic geometry as fields of functions on m-dimensional surfaces. For instance, when $\pmb { F } = \mathbb { C }$ and $m = 1$ these fields arise i n analysis a s fields of meromorphic functions on compact Riemann surfaces.
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23276
- **statement/data:** A finitely generated extension E/F of transcendence degree m is a function field in m variables when E is finite algebraic over a purely transcendental subfield F(t_1,…,t_m).
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23294
- **statement/data:** An extension $E / F$ is called purely transcendental if it has a transcendence base S such that $E = F ( S )$ In the preceding discussion, both $F ( x _ { 1 } , \ldots , x _ { n } )$ and $F ( s _ { 1 } , \ldots , s _ { n } )$ are purely transcendental over F. As an exercise (following) one can show that $\mathbb { Q } ( t , { \sqrt { t ^ { 3 } - t } } )$ is not a purely transcendental extension of Q even though it contains no elements that are algebraic over Q other than those in Q itself (i.e., the process of decomposing a general extension into a purely transcendental extension followed by an algebraic extension cannot generally be reversed so that the algebraic piece occurs first). is a purely transcendental extension of F of transcendence degree $n = 1$ or 2 and L is an intermediate field, $F \subseteq L \subseteq E$ with the same transcendence degree, then L is again a purely transcendental extension of F (Liroth $( n = 1 )$ , Castelnuovo $( n = 2 ) )$ ) . This result is not true if the transcendence degree is $\geq 3 ,$ however, although examples where L fails to be purely transcendental are difficult to construct. For extensions of transcendence degree 1 the intermediate fields are described by the following theorem.
- **dependencies:** —


- **kind:** Theorem
- **source:** §14.9; printed pp. 645–655; extraction line 23300
- **statement/data:** Let t be transcendental over F. (1) (Ltiroth) If $F \subseteq K \subseteq F ( t )$ , then $K = F ( r )$ , for some $r \in F ( t )$ . In particular, every nontrivial extension of F contained in $F ( t )$ is purely transcendenta over F. (2) If $P = P ( t ) , Q = Q ( t )$ are nonzero relatively prime polynomials in $F [ t ]$ which are not both constant, $$ [ F (t): F (P / Q) ] = \max (\deg P, \deg Q). $$
- **dependencies:** —


- **kind:** Theorem (Hilbert)
- **source:** §14.9; printed pp. 645–655; extraction line 23345
- **statement/data:** (Hilbert) Let $x _ { 1 } , x _ { 2 } , \ldots , x _ { n }$ be independent transcendentals over $\mathbb { Q } ,$ , let $E =$ $\mathbb { Q } ( \boldsymbol { x } _ { 1 } , \ldots , \boldsymbol { x _ { n } } )$ and let G be a finite group of automorphisms of E with fixed field K. If K is a purely transcendental extension of Q with transcendence basis $a _ { 1 } , a _ { 2 } , \ldots , a _ { n } .$ then there are infinitely many specializations of $a _ { 1 } , \ldots , a _ { n }$ in Q such that E specializes to a Galois extension of Q with Galois group isomorphic to G. Hilbert's Theorem gives a suficient condition for the specialized extension not to collapse. In general, the Galois group of the specialized extension is a subgroup of G ( cf. Proposition 19) and may be a proper subgroup of G. It is also known that the fixed field K need not always be a purely transcendental extension of $\mathbb { Q } .$ . An example of this occurs when $G$ is the cyclic group of order 4 7.
- **dependencies:** FC01-C14-U035


- **kind:** Corollary
- **source:** §14.9; printed pp. 645–655; extraction line 23351
- **statement/data:** $S _ { n }$ is a Galois group over $\mathbb { Q } ,$ , for all $\pmb { n }$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23361
- **statement/data:** An algebraic extension $E / F$ is called purely inseparable if for each a $\in E$ the minimal polynomial of a over F has only one distinct root. It is easy to see that the following are equivalent: (1) $E / F$ is purely inseparable (2) if $\alpha \in E$ is separable over $F _ { \ast }$ , then $\alpha \in F$ (3) if $\alpha \in E .$ , then $\alpha ^ { p ^ { n } } \in F$ for some n (depending on a), and $m _ { \alpha , F } ( x ) = x ^ { p ^ { n } } - \alpha ^ { p ^ { n } }$ The following easy proposition describes composites of separable and purely inseparable extensions.
- **dependencies:** —


- **kind:** Proposition
- **source:** §14.9; printed pp. 645–655; extraction line 23373
- **statement/data:** If $E _ { 1 }$ and $E _ { 2 }$ are sub fields of $E$ which are both separable (or both purely inseparable) extensions of $F$ , then their composite $E _ { 1 } E _ { 2 }$ is separable (purely inseparable, respectively) over $F$
- **dependencies:** —


- **kind:** Proposition
- **source:** §14.9; printed pp. 645–655; extraction line 23381
- **statement/data:** Let $E / F$ be an algebraic extension. Then there is a unique field $E _ { s e p }$ with $F \subseteq E _ { s e p } \subseteq E$ such that $E _ { s e p }$ is separable over F and E is purely inseparable over $E _ { s e p }$ · The field $E _ { s e p }$ is the set of elements of E which are separable over $F .$ The degree of $E _ { s e p } / F$ is called the separable degree of $E / F$ and the degree of $E / E _ { s e p }$ is called the inseparable degree of $E / F$ (often denoted as $[ E : F ] _ { s }$ s and $[ E : F ] _ { i }$ respectively). The product of these two degrees is the (ordinary) degree. The propositions immediately give the following corollary
- **dependencies:** —


- **kind:** Convention
- **source:** §14.9; printed pp. 645–655; extraction line 23383
- **statement/data:** For algebraic E/F, [E:F]_s=[E_sep:F] is the separable degree and [E:F]_i=[E:E_sep] is the inseparable degree; [E:F]=[E:F]_s[E:F]_i.
- **dependencies:** —


- **kind:** Corollary
- **source:** §14.9; printed pp. 645–655; extraction line 23385
- **statement/data:** Separable degrees (respectively inseparable degrees) are multiplicative. When E is generated over F by the root of an ireducible polynomial $p ( { \boldsymbol { x } } ) \in F [ { \boldsymbol { x } } ]$ the separable and inseparable degrees of the extension $E / F$ are the same as the separable and inseparable degrees of the polynomial $p ( { \pmb x } )$ defined in Section 1 3.5. The proposition asserts that any algebraic extension may be decomposed into a separable extension followed by a purely inseparable one. Exercise 3 at the end of this section outlines an example illustrating that this decomposition cannot generally be reversed, namely an extension which is not a separable extension of a purely inseparable extension. We shall shortly state conditions on an extension under which the decomposition into separable and purely inseparable subextensions may be reversed.
- **dependencies:** —


- **kind:** Proposition
- **source:** §14.9; printed pp. 645–655; extraction line 23393
- **statement/data:** If E is a finitely generated extension of a perfect field F, then there is a transcendence base T of $E / F$ such that E is a separable (algebraic) extension of $F ( T )$ A transcendence base T as described in the proposition is called a separating transcendence base. Exercise 4 at the end of this section illustrates this with a nontrivia example.
- **dependencies:** —


- **kind:** Proposition
- **source:** §14.9; printed pp. 645–655; extraction line 23399
- **statement/data:** Let $E / F$ be an arbitrary algebraic extension and let Q be an algebraic closure of E. The following are equivalent: (1) $E / F$ is a normal extension (i.e., is the splitting field over F of some set of polynomials in $F [ \boldsymbol { x } ] )$ (2) whenever $\sigma : E \Omega$ is an embedding such that ${ \pmb { \sigma } } | _ { F }$ is the identity, $\sigma ( E ) = E$ (3) whenever an irreducible polynomia $f ( x ) \in F [ x ]$ has one root in E, it has all its roots in E .
- **dependencies:** —


- **kind:** Proposition
- **source:** §14.9; printed pp. 645–655; extraction line 23415
- **statement/data:** If $E / F$ is normal with $[ E : F ] _ { s } < \infty$ , then $E = E _ { s e p } E _ { p i }$ , where $E _ { p i }$ is a purely inseparable extension of $F \left( { \cal { E } } _ { p i } \right.$ consists of all purely inseparable elements of E over F) and $E _ { s e p } \cap E _ { p i } = F$ Finally, we mention how Galois Theory generalizes to infinite extensions
- **dependencies:** —


- **kind:** Definition
- **source:** §14.9; printed pp. 645–655; extraction line 23419
- **statement/data:** An extension $E / F$ is called Galois if it is algebraic, normal and separable In this case $\mathsf { A u t } ( E / F )$ is called the Galois group of the extension and is denoted by $\operatorname { G a l } ( E / F )$ For infinite extensions there need not be a bijection between the set of all subgroups of the Galois group and the set of all subfields of E containing $F ,$ , as the following example illustrates. Let E be the subfield of R obtained by adjoining to $\mathbb { Q }$ all square roots of positive rational numbers. One easily sees that E may also be described as the splitting field of the set of polynomials $x ^ { 2 } - p ,$ where $\pmb { p }$ runs over all primes in $\mathbb { Z } ^ { + }$ . Note that E is a (countably) infinite Galois extension of Q. Since every automorphism $\pmb { \sigma }$ of $E$ is determined by its action on the square roots of the primes and $\sigma$ either fixes or negates each of these, $\sigma ^ { 2 }$ is the identity automorphism. It follows that Aut( E) is an infinite elementary abelian 2-group. Thus Aut( E) is an infinite dimensional vector space over $\mathbb { F } _ { 2 }$ · By an exercise in the section on dual spaces (Section 1 1 .3) the number of nonzero homomorphisms of Aut(E) into $\mathbb { F } _ { 2 }$ is uncountable, whence their kernels (which are subspaces of co-dimension 1) are uncountable in number (and distinct). Thus Aut(E) has uncountably many subgroups of index 2, whereas Q has only a countable number of quadratic extensions. …
- **dependencies:** —


- **kind:** Theorem (Krull)
- **source:** §14.9; printed pp. 645–655; extraction line 23427
- **statement/data:** (Krull) Let E 1 F be a Galois extension with Galois group G. Topologize G by taking as a base for the closed sets the subgroups of G which are the fixing subgroups of the finite extensions of F in E, together with all left and right cosets of these subgroups. Then with this $( ^ { 6 6 } { \bf K n u l l ^ { \circ } } )$ topology the closed subgroups of G correspond bijectively with the subfields of E containing F and the corresponding lattices are dual. Closed normal subgroups of $\pmb { G }$ correspond to normal extensions of $F$ in E . One important area of current research is to describe (as a topological group) the Galois group of certain field extensions such as $\overline { { F } } / F$ , where $\overline { F }$ is the algebraic closure of F. Litle is known about the latter group when $F = \mathbb { Q }$ (in particular, its normal subgroups of finite index, i.e., which finite groups occur as Galois groups over $\mathbb { Q } ,$ , are not known). If E is the algebraic closure of the finite field $\mathbb { F } _ { p }$ • the Galois group of this extension is the topologically cyclic group $\widehat { \mathbb { Z } }$ with the Frobenius automorphism as a topological generator. The group $\widehat { \mathbb { Z } }$ is an uncountable group (in particular, is not isomorphic to $\mathbb { Z } )$ with the property that every closed subgroup of finite index is normal with cyclic quotient. …
- **dependencies:** —



- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23534
- **statement/data:** A commutative ring R is said to be Noetherian or to satisfy the ascending chain condition on ideals (or A. C. C. on ideals) if there is no infinite increasing chain of ideals in R, i.e., whenever $I _ { 1 } \subseteq I _ { 2 } \subseteq I _ { 3 } \subseteq \cdots$ is an increasing chain of ideals of R, then there is a positive integer such that $I _ { k } = I _ { m }$ for all $k \geq m$
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §15.1; printed pp. 656–672; extraction line 23536
- **statement/data:** If I is an ideal of the Noetherian ring R, then the quotient R j I is a Noetherian ring. Any homomorphic image of a Noetherian ring is Noetherian.
- **dependencies:** —


- **kind:** Theorem 2
- **source:** §15.1; printed pp. 656–672; extraction line 23540
- **statement/data:** The following are equivalent: (1) R is a Noetherian ring. (2) Every nonempty set of ideals of R contains a maximal element under inclusion. (3) Every ideal of R is finitely generated.
- **dependencies:** —


- **kind:** Theorem 3 (Hilbert's Basis Theorem)
- **source:** §15.1; printed pp. 656–672; extraction line 23564
- **statement/data:** (Hilbert's Basis Theorem) If R is a Noetherian ring then so is the polynomia ring R [x] . Note that Hilbert's Basis Theorem shows how larger Noetherian rings may be built from existing ones in a manner analogous to Theorem 7 of Section 9.3 (which proved that if R is a U.F.D., then so is R [x]).
- **dependencies:** —


- **kind:** Corollary 4
- **source:** §15.1; printed pp. 656–672; extraction line 23568
- **statement/data:** The polynomial ring $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ with coefficients from a field k is a Noetherian ring. Let k be a field. Recall that a ring R is a k-algebra if k is contained in the center of R and the identity of k is the identity of R .
- **dependencies:** —


- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23572
- **statement/data:** (1) The ring R is a finitely generated k-algebra if R is generated as a ring by k together with some finite set $r _ { 1 } , r _ { 2 } , \ldots , r _ { n }$ of elements of R. (2) Let R and S be k-algebras. A map $\psi : R s$ is a k-algebra homomorphism if $\psi$ is a ring homomorphism that is the identity on k. If R is a k-algebra then R is both a ring and a vector space over $\mathbf { \Psi } _ { k , \mathrm { ~ \tiny ~ ( ~ , ~ } }$ an d i t is important to distinguish the sense in which elements of R are generators for R. For example, the polynomial ring $k [ x _ { 1 } , \ldots , x _ { n } ]$ in a finite number of variables over k is a finitely generated k-algebra since $x _ { 1 } , \ldots , x _ { n }$ are ring generators, but for ${ \pmb n } > { \bf 0 }$ this ring is an infinite dimensional vector space over k.
- **dependencies:** —


- **kind:** Corollary 5
- **source:** §15.1; printed pp. 656–672; extraction line 23580
- **statement/data:** The ring R is a finitely generated k-algebra if and only if there is some surjective k-algebra homomorphism $$ \varphi : k [ x _ {1}, x _ {2}, \dots , x _ {n} ] \rightarrow R $$ from the polynomial ring in a finite number of variables onto R that is the identity map on k. Any finitely generated k-algebra is therefore Noetherian.
- **dependencies:** —


- **kind:** Construction
- **source:** §15.1; printed pp. 656–672; extraction line 23604
- **statement/data:** Polynomial functions on affine n-space form the coordinate ring k[A^n], identified with k[x_1,…,x_n] when k is infinite.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23614
- **statement/data:** A subset V of $\mathbb { A } ^ { n }$ is called an afine algebraic set (or just an algebraic set) if V is the set of common zeros of some set S of polynomials, i.e., if $V = \mathcal { Z } ( S )$ for some $S \subseteq k [ \mathbb { A } ^ { n } ]$ . In this case $V = \mathcal { Z } ( S )$ is called the locus of S in $\mathbb { A } ^ { n }$ If $S = { f } \circ \mathbf { r } \left{ f _ { 1 } , \ldots , f _ { m } \right}$ we shall simply write $\mathcal { Z } ( f )$ or $\mathcal { Z } ( f _ { 1 } , \ldots , f _ { m } )$ for ${ \mathcal { Z } } ( S )$ and call it the locus of $f$ or $f _ { 1 } , \ldots , f _ { m }$ , respectively. Note that the locus of a single polynomial of the form $f - g$ is the same as the solutions in afine n-space of the equation $f = g ,$ , so afine algebraic sets are the solution sets to systems of polynomial equations, and as a result ocur frequently in mathematics.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23626
- **statement/data:** The zero locus Z(f) of a nonconstant polynomial in affine n-space is a hypersurface.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23704
- **statement/data:** If $V \subseteq { \mathbb { A } } ^ { n }$ is an affine algebraic set the quotient ring $k [ \mathbb { A } ^ { n } ] / \mathbb { Z } ( V )$ is called the coordinate ring of V, and is denoted by $k [ V ]$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.1; printed pp. 656–672; extraction line 23714
- **statement/data:** A map $\varphi : V \to W$ is called a morphism (or polynomial map or regular map) of algebraic sets if there are polynomials $\varphi _ { 1 } , \dots , \varphi _ { m } \in k [ x _ { 1 } , x _ { 2 } , \dots , x _ { n } ]$ such that $$ \varphi ((a _ {1}, \dots , a _ {n})) = (\varphi_ {1} (a _ {1}, \dots , a _ {n}), \dots , \varphi_ {m} (a _ {1}, \dots , a _ {n})) $$ for all $( a _ { 1 } , \ldots , a _ { n } ) \in V$ . The map $\varphi : V \to W$ is an isomorphism of algebraic sets if there is a morphism l/r : $W \to V$ with $\varphi \circ \psi = 1 _ { W }$ and l/r $\circ \varphi = 1 _ { V }$
- **dependencies:** —


- **kind:** Theorem 6
- **source:** §15.1; printed pp. 656–672; extraction line 23764
- **statement/data:** Let $V \subseteq \mathbb { A } ^ { n }$ and $W \subseteq \mathbb { A } ^ { m }$ be affine algebraic sets. Then there is a bijective corespondence $$ \left{ \begin{array}{c} \text {morphisms from V to W} \ \text {as algebraic sets} \end{array} \right} \longleftrightarrow \left{ \begin{array}{c} k \text {-algebra homomorphisms} \ \text {from k[W] to k[V]} \end{array} \right}. $$ More precisely, (1) Every morphism $\varphi : V \to W$ induces an associated k-algebra homomorphism $\widetilde { \varphi } : k [ W ] \to k [ V ]$ defined by $\widetilde { \varphi } ( f ) = f \circ \varphi .$ (2) Every k-algebra homomorphism $\phi : k [ W ] \to k [ V ]$ is induced by a unique morphism $\varphi : V \to W , { \mathrm { i . e . , } } \varPhi = \widetilde { \varphi } .$ (3) If $\varphi : V \to W$ and $\psi : W \to U$ are morphisms of affine algebraic sets, then ;- $\begin{array} { r } { \circ \varphi = \widetilde \varphi \circ \widetilde \psi : k [ U ] k [ V ] . } \end{array}$ (4) The morphism $\varphi : V \to W$ is an isomorphism if and only i ${ \widetilde { \varphi } } : k [ W ] \to k [ V ]$ is a k-algebra isomorphism.
- **dependencies:** —


- **kind:** Corollary 7
- **source:** §15.1; printed pp. 656–672; extraction line 23794
- **statement/data:** Suppose $\varphi : V \to W$ is a map of afine algebraic sets. Then $\varphi$ is a morphism if and only if for every $f \in k [ W ]$ the composite map $f \circ \varphi$ is an element of $k [ V ]$ (as a k-valued function on V). When $\varphi$ is a morphism, $\varphi ( \boldsymbol { \upsilon } ) = \boldsymbol { \upsilon }$ with $\upsilon \in V$ and $w \in W$ if and only if $\widetilde { \varphi } ^ { - 1 } ( \mathscr { T } ( { v } ) ) = \mathscr { T } ( { w } )$ .
- **dependencies:** —


- **kind:** Proposition 8
- **source:** §15.1; printed pp. 656–672; extraction line 23830
- **statement/data:** With notation as above, let $R = k [ y _ { 1 } , \dots , y _ { m } , x _ { 1 } , \dots , x _ { n } ]$ and let $\pmb { A }$ be the ideal generated by $y _ { 1 } - \varphi _ { 1 } , . . . , y _ { m } - \varphi _ { m }$ together with generators for I . Let G be the reduced Grobner basis of A with respect to the lexicographic monomial ordering $x _ { 1 } > \cdots > x _ { n } > y _ { 1 } > \cdots > y _ { m }$ Then (a) The kernel of tP is $\pmb { \mathscr { A } } \cap \pmb { \mathscr { k } } [ y _ { 1 } , \dotsc , \dotsc , y _ { m } ]$ modulo J. The elements of $\pmb { G }$ i n $k [ y _ { 1 } , \dots , y _ { m } ]$ (taken modulo J) generate ker $\Phi$ . (b) If $f \in k [ x _ { 1 } , \ldots , x _ { n } ] .$ . then $\bar { \ b { f } }$ is in the image of $\Phi$ if and only if the remainder after general polynomial division of $f$ by the elements in G is an element $h \in k [ y _ { 1 } , \dotsc , y _ { m } ]$ . in which case $\bar { \boldsymbol { \phi } } ( \bar { h } ) = \bar { \boldsymbol { f } }$
- **dependencies:** —


- **kind:** Corollary 9
- **source:** §15.1; printed pp. 656–672; extraction line 23878
- **statement/data:** The map $\Phi$ is surjective if and only if for each i , $1 \leq i \leq n ,$ , the reduced Grobner basis G contains a polynomial $x _ { i } - h _ { i }$ where $h _ { i } \in k [ y _ { 1 } , \ldots , y _ { m } ]$
- **dependencies:** —


- **kind:** Proposition 10
- **source:** §15.1; printed pp. 656–672; extraction line 23918
- **statement/data:** Suppose $\pmb { \alpha }$ is a root of the ireducible polynomial $p ( x ) \in k [ x ]$ and $\beta \in k ( \alpha )$ , say $\beta = f ( \alpha )$ for the polynomial $f \in k [ x ]$ . Let $G$ be the reduced Grobner basis for the ideal $( p , y - f )$ in $k [ x$ , y] for the lexicographic monomial ordering $x > y$ Then the minimal polynomial of $\boldsymbol { \beta }$ over $\pmb { k }$ is the monic polynomial in $G \cap k [ y ]$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24122
- **statement/data:** Let I be an ideal in a commutative ring R. (1) The radical of 1 , denoted by rad I, is the collection of elements in R some power of which lie in $I , \mathrm { i . e . }$ , $$ \operatorname{rad} I = {a \in R \mid a ^ {k} \in I \text { for some } k \geq 1 }. $$ (2) The radical of the zero ideal i s called the nilradical of R . (3) A n ideal I i s called a radical ideal if $I = { \bf r a d } I$
- **dependencies:** —


- **kind:** Proposition 11
- **source:** §15.2; printed pp. 673–690; extraction line 24136
- **statement/data:** Let I be an ideal in the commutative ring R. Then rad I is an ideal containing I, and (rad $I ) / I$ is the nilradical of $R / I$ . In particular, $R / I$ has no nilpotent elements if and only if $I = { \bf r a d } I$ is a radical ideaL
- **dependencies:** —


- **kind:** Proposition 12
- **source:** §15.2; printed pp. 673–690; extraction line 24146
- **statement/data:** The radical of a proper ideal I is the intersection of all prime ideals containing I. In particular, the nilradical is the intersection of all the prime ideals in R.
- **dependencies:** —


- **kind:** Corollary 13
- **source:** §15.2; printed pp. 673–690; extraction line 24156
- **statement/data:** Prime (and hence also maximal) ideals are radical
- **dependencies:** —


- **kind:** Proposition 14
- **source:** §15.2; printed pp. 673–690; extraction line 24168
- **statement/data:** If R is a Noetherian ring then for any ideal I some positive power of rad I is contained in I . In particular, the nilradical, N, of a Noetherian ring is a nilpotent ideal: $N ^ { k } = 0$ for some $k \geq 1$
- **dependencies:** —


- **kind:** Theorem (Hilbert's Nullstellensatz)
- **source:** §15.2; printed pp. 673–690; extraction line 24178
- **statement/data:** (Hilbert's Nullstellensatz) Let E be an algebraically closed field. Then I(Z(l)) = rad I for every ideal I of $E [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ . Moreover, the maps $\boldsymbol { z }$ and $\boldsymbol { \tau }$ in the corespondence $$ {\text { affine algebraic sets } } \xrightarrow [ \leftarrow ]{\mathcal {I}} {\text { radical ideals } } $$ are bijections that are inverses of each other.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24194
- **statement/data:** A topology in closed-set form is a collection τ of subsets of X closed under arbitrary intersections and finite unions and containing ∅ and X; U⊆X is open iff X\U is closed.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24208
- **statement/data:** The Zariski topology on affine n-space over an arbitrary field k is the topology in which the closed sets are the affine algebraic sets in $\mathbb { A } ^ { n }$ The Zariski topology is quite "coarse" in the sense that there are "relatively few" closed (or open) sets. For example, for the Zariski topology on $\mathbb { A } ^ { 1 }$ the only closed sets are $\varnothing ,$ k and the finite sets (cf. Exercise 14 in Section 1), and so the nonempty open sets are the complements of finite sets. If k is an infinite field it follows that in the Zariski topology any two nonempty open sets in $\mathbb { A } ^ { 1 }$ have nonempty intersection. In the language of point-set topology, the Zariski topology is always $T _ { 1 }$ (points are closed sets), but for infinite fields the Zariski topology is never $T _ { 2 }$ (Hausdorff), i.e., two distinct points never belong to two disjoint open sets (cf. the exercises). For example, when $k = \mathbb { R }$ , a nonempty Zariski open set is just the real line IR. with some finite number of points removed, and any two such sets have (infinitely many) points in common. Note also that the Zariski open (respectively, dosed) sets in IR. are also open (respectively, closed) sets with respect to the usual Euclidean topology. The converse is not true; for example the interval [0, 1] is closed in the Euclidean topology but is not closed in the Zariski topology. In this sense the Euclidean topology on IR. is much "finer"; …
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24228
- **statement/data:** For any subset A of $\mathbb { A } ^ { n }$ the Zariski closure of A is the smallest algebraic set containing A. If $A \subseteq V$ for an algebraic set $V$ then A is Zariski dense in $V$ if the Zariski closure of A is V. For example, if $k = \mathbb { R }$ , the algebraic sets in $\mathbb { A } ^ { 1 }$ are $\varnothing ,$ IR, and finite subsets of IR by Exercise 14 in Section 1 . The Zariski closure of any infinite set A of real numbers is then all of $\mathbb { A } ^ { 1 }$ and A is Zariski dense in $\mathbb { A } ^ { 1 }$
- **dependencies:** —


- **kind:** Proposition 15
- **source:** §15.2; printed pp. 673–690; extraction line 24232
- **statement/data:** The Zariski closure of a subset A in $\mathbb { A } ^ { n }$ is $\mathcal { Z } ( \mathcal { T } ( A ) )$ ) .
- **dependencies:** —


- **kind:** Proposition 16
- **source:** §15.2; printed pp. 673–690; extraction line 24240
- **statement/data:** Suppose $\varphi : V \to W$ is a morphism of algebraic sets and $\widetilde { \varphi } : k [ W ] \to$ $k [ V ]$ is the associated k-algebra homomorphism of coordinate rings. Then (1) The kernel of $\widetilde { \varphi }$ is $\mathcal { T } ( \varphi ( V ) )$ (2) The Zariski closure of $\varphi ( V )$ is the zero set in W of ker ${ \widetilde { \varphi } } .$ . In particular, the homomorphism $\widetilde { \varphi }$ is injective if and only if $\varphi ( V )$ is Zariski dense in $W$
- **dependencies:** —


- **kind:** Named example
- **source:** §15.2; printed pp. 673–690; extraction line 24252
- **statement/data:** Implicitization: elimination by Gröbner bases computes defining equations for the Zariski closure of the image of a polynomial parametrization.
- **dependencies:** —


- **kind:** Named example
- **source:** §15.2; printed pp. 673–690; extraction line 24272
- **statement/data:** Projections of algebraic sets give the standard example that a morphism of affine algebraic sets need not have Zariski-closed image.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24296
- **statement/data:** A nonempty affine algebraic set V is called irreducible if it cannot be written as $V = V _ { 1 } \cup V _ { 2 }$ , where $V _ { 1 }$ and $V _ { 2 }$ are proper algebraic sets in V. An ireducible afine algebraic set is called an affine variety. Equivalently, an algebraic set (which is a closed set in the Zariski topology) is irreducible if it cannot be written as the union of two proper, closed subsets.
- **dependencies:** —


- **kind:** Proposition 17
- **source:** §15.2; printed pp. 673–690; extraction line 24300
- **statement/data:** (1) The afine algebraic set V is irreducible if and only if $\boldsymbol { \mathcal { T } } ( V )$ is a prime ideaL (2) Every nonempty afine algebraic set V may be written uniquely in the form $$ V = V _ {1} \cup V _ {2} \cup \dots \cup V _ {q} $$ where each $V _ { i }$ is irreducible, and $V _ { i } \not \in V _ { j }$ for all $j \neq i \ ( \mathbf { i . e . }$ ., the decomposition is "minimal" or "irredundant").
- **dependencies:** —


- **kind:** Corollary 18
- **source:** §15.2; printed pp. 673–690; extraction line 24330
- **statement/data:** An afine algebraic set V is a variety if and only if its coordinate ring k[V] is an integral domain.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24334
- **statement/data:** If V is a variety, then the field of fractions of the integral domain $k [ V ]$ is called the field of rational functions on V and is denoted by $k ( V )$ . The dimension of a variety $V ,$ denoted dim $V ,$ is defined to be the transcendence degree of $k ( V )$ over k.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24354
- **statement/data:** A proper ideal $Q$ in the commutative ring R is called primary if whenever $a b \in Q$ and $a \notin { \cal Q } ,$ then $b ^ { n } \in { \cal Q }$ for some positive integer n . Equivalently, if ab $\in { \cal Q }$ and $a \not \in { \cal Q }$ , then $b \in$ rad $Q$ . Some of the basic properties of primary ideals are given in the following proposition.
- **dependencies:** —


- **kind:** Proposition 19
- **source:** §15.2; printed pp. 673–690; extraction line 24358
- **statement/data:** Let R be a commutative ring with 1 . (1) Prime ideals are primary. (2) The ideal Q is primary if and only if every zero divisor in $R / Q$ is nilpotent (3) If Q is primary then rad Q is a prime ideal, and is the unique smallest prime ideal containing $Q$ (4) I f Q i s an ideal whose radical i s a maximal ideal, then Q i s a primary ideal. (5) Suppose M is a maximal ideal and Q is an ideal with $M ^ { n } \subseteq Q \subseteq M$ for some $n \geq 1$ Then $Q$ is a primary ideal with rad $Q = M .$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24374
- **statement/data:** If Q is a primary ideal, then the prime ideal $P = \operatorname { r a d } Q$ is called the associated prime to $Q .$ , and Q is said to belong to P (or to be $P / - p r i m a r y )$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24408
- **statement/data:** (1) An ideal I in R has a primary decomposition if it may be written as a finite intersection of primary ideals: $$ I = \bigcap_ {i = 1} ^ {m} Q _ {i} \quad Q _ {i} \text { a primary ideal. } $$ (2) The primary decomposition above is minimal and the $Q _ { i }$ are called the primary components of I if (a) no primary ideal contains the intersection of the remaining primary ideals, i.e., $Q _ { i } \nsupseteq { \cap _ { j \neq i } Q _ { j } }$ for all i , and (b) the associated prime ideals are all distinct: rad $Q _ { i } \neq$ rad $Q _ { j }$ for i $\neq j$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24424
- **statement/data:** A proper ideal I in the commutative ring R is said to be irreducible if I cannot be written nontrivialy as the intersection of two other ideals, i.e., if $I = J \cap K$ with ideals J, K implies that I = J or $I = K$ I t is easy to see that a prime ideal i s irreducible (see Exercise 1 1 in Section 7.4). The ideal $( x , y ) ^ { 2 }$ in $k [ x , y ]$ in Example 2 earlier shows that primary ideals need not be ireducible since it is the intersection of the ideals $( x ) + ( x , y ) ^ { 2 } = ( x , y ^ { 2 } )$ and $( y ) + ( x , y ) ^ { 2 } = ( y , x ^ { 2 } )$ . In a Noetherian ring, however, ireducible ideals are necessarily primary:
- **dependencies:** —


- **kind:** Proposition 20
- **source:** §15.2; printed pp. 673–690; extraction line 24428
- **statement/data:** Let R be a Noetherian ring. Then (1) every irreducible ideal is primary, and (2) every proper ideal in R is a finite intersection of ireducible ideals.
- **dependencies:** —


- **kind:** Theorem 21 (Primary Decomposition Theorem)
- **source:** §15.2; printed pp. 673–690; extraction line 24440
- **statement/data:** (Primary Decomposition Theorem) Let R be a Noetherian ring. Then every proper ideal I in R has a minimal primary decomposition. If $$ I = \bigcap_ {i = 1} ^ {m} Q _ {i} = \bigcap_ {i = 1} ^ {n} Q _ {i} ^ {\prime} $$ are two minimal primary decompositions for I then the sets of associated primes in the two decompositions are the same: $$ {\operatorname{rad} Q _ {1}, \operatorname{rad} Q _ {2}, \dots , \operatorname{rad} Q _ {m} } = {\operatorname{rad} Q _ {1} ^ {\prime}, \operatorname{rad} Q _ {2} ^ {\prime}, \dots , \operatorname{rad} Q _ {n} ^ {\prime} }. $$ Moreover, the primary components $Q _ { i }$ belonging to the minimal elements in this set of associated primes are uniquely determined by I.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.2; printed pp. 673–690; extraction line 24456
- **statement/data:** If I is an ideal in the Noetherian ring R then the associated prime ideals in any primary decomposition of I are called the associated prime ideals of I . If an associated prime ideal P of I does not contain any other associated prime ideal of I then P is called an isolated prime ideal; the remaining associated prime ideals of I are called embedded prime ideals. The prime ideals associated to an ideal I provide a great deal of information abou the ideal I (cf. for example Exercises 41 and 43):
- **dependencies:** —


- **kind:** Corollary 22
- **source:** §15.2; printed pp. 673–690; extraction line 24460
- **statement/data:** Let I be a proper ideal in the Noetherian ring R. (1) A prime ideal P contains the ideal I if and only if P contains one of the associated primes of I , hence if and only if P contains one of the isolated primes of I , i.e., the isolated primes of I are precisely the minimal elements in the set of all prime ideals containing I . In particular, there are only finitely many minimal elements among the prime ideals containing I. (2) The radical of I i s the intersection of the associated primes of I , hence also the intersection of the isolated primes of I. (3) There are prime ideals $P _ { 1 } , \ldots , P _ { n }$ (not necessarily distinct) containing I such that $P _ { 1 } P _ { 2 } \dots P _ { n } \subseteq I$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.3; printed pp. 691–705; extraction line 24692
- **statement/data:** Suppose R is a sub ring of the comutative ring S with $1 = 1 _ { S } \in R .$ (1) An element $s \in S$ is integral over R if s is the root of a monic polynomial in $R [ x ]$ (2) The ring S is an integral extension of R or just integral over R if every $s \in S$ is integral over R. (3) The integral closure of R in S is the set of elements of S that are integral over R. (4) The ring R is said to be integrally closed in S if R is equal to its integral closure in S. The integral closure of an integral domain R in its field of fractions is called the normalization of R. An integral domain is called integrally closed or normal if it is integrally closed in its field of fractions.
- **dependencies:** —


- **kind:** Proposition 23
- **source:** §15.3; printed pp. 691–705; extraction line 24704
- **statement/data:** Let R be a subring of the comutative ring S with $1 \in R$ and let $s \in S .$ Then the following are equivalent: (1) s is integral over R, (2) $R [ s ]$ is a finitely generated R-module (where $R [ s ]$ is the ring of al R-linear combinations of powers of s ), and (3) $s \in T$ for some subring T, $R \subseteq T \subseteq S$ , that is a finitely generated R-module.
- **dependencies:** —


- **kind:** Corollary 24
- **source:** §15.3; printed pp. 691–705; extraction line 24736
- **statement/data:** Let $R \subseteq S$ be as in Proposition 23 and let $s , t \in S .$ (1) If s and t are integral over R then so are $s \pm t$ and st. (2) The integral closure of R in S is a subring of S containing R. (3) Integrality is transitive: let S be a subring of T ; if T is integral over S and S is integral over R, then T is integral over R.
- **dependencies:** FC01-C15-U045


- **kind:** Corollary 25
- **source:** §15.3; printed pp. 691–705; extraction line 24766
- **statement/data:** Let R be a subring of the commutative ring S with $1 \in R$ . Then the integral closure of R in S is integrally closed in S.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.3; printed pp. 691–705; extraction line 24786
- **statement/data:** Let $\varphi : R S$ be a homomorphism of commutative rings. (a) If I is an ideal in R then the extension of I to S is the idea $\varphi ( I ) S$ of S generated by the image of I . (b) I f J is an ideal of S , then the contraction in R of J i s the ideal $\varphi ^ { - 1 } ( J )$ . In the special case where R is a subring of S and cp is the natural injection, the extension of $I \subseteq R$ is the ideal I S in S and the contraction of $J \subseteq S$ is the ideal J n R of R. It is imediate from the definition that (1) $I \subseteq I S \cap R ,$ more generally, I is contained in the contraction of its extension to S, and (2) $( J \cap R ) S \subseteq J ,$ , more generally, J contains the extension of its contraction in R.
- **dependencies:** —


- **kind:** Theorem 26
- **source:** §15.3; printed pp. 691–705; extraction line 24804
- **statement/data:** Let R be a subring of the commutative ring S with $1 \in R$ and suppose that S integral over R. (1) Assume that S is an integral domain. Then R is a field if and only if S is a field (2) Let P be a prime ideal in R. Then there is a prime ideal Q in S with $P = Q \cap R$ Moreover, P is maximal if and only if Q is maximal. (3) (The Going-up Theorem) Let $P _ { 1 } \subseteq P _ { 2 } \subseteq \cdots \subseteq P _ { n }$ be a chain of prime ideals in R and suppose there are prime ideals $Q _ { 1 } \subseteq Q _ { 2 } \subseteq \cdots \subseteq Q _ { m }$ of S with $P _ { i } = Q _ { i } \cap R , 1 \leq i \leq m$ and $\textit { \textbf { m } } < \textit { \textbf { n } }$ . Then the ascending chain of ideals can be completed: there are prime ideals $Q _ { m + 1 } \subseteq \cdots \subseteq Q _ { n }$ in S such that $P _ { i } = Q _ { i } \cap R$ for all i . (4) (The Going-down Theorem) Assume that S is an integral domain and R is integrally closed in S. Let $P _ { 1 } \supseteq P _ { 2 } \supseteq \cdots \supseteq P _ { n }$ be a chain of prime ideals in R and suppose there are prime ideals $Q _ { 1 } \supseteq Q _ { 2 } \supseteq \cdots \supseteq Q _ { m }$ of S with $P _ { i } = Q _ { i } \cap R , 1 \leq i \leq m$ and $m \ < \ n .$ Then the descending chain of ideals can be completed: there are prime ideals $Q _ { m + 1 } \supseteq \cdots \supseteq Q _ { n }$ in S such that $P _ { i } = Q _ { i } \cap R$ for all i .
- **dependencies:** —


- **kind:** Corollary 27
- **source:** §15.3; printed pp. 691–705; extraction line 24838
- **statement/data:** Suppose R is a subring of the ring S with $1 \in R$ and assume S is integral and finitely generated (as a ring) over R. If P is a maximal ideal in R then there is a nonzero and finite number of maximal ideals $Q$ of S with $Q \cap R = P$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.3; printed pp. 691–705; extraction line 24846
- **statement/data:** Let K be an extension field of $\mathbb { Q } .$ (1) An element $\alpha \in K$ is called an algebraic integer if a is integral over $\mathbb { Z } ,$ , i.e., if a is the root of some monic polynomial with coeficients in $\mathbb { Z }$ (2) The integral closure of $\mathbb { Z }$ in K is called the ring of integers of K, and is denoted by ${ \mathcal { O } } _ { K }$ An algebraic integer is clearly algebraic over $\mathbb { Q } ,$ , so the ring of all algebraic integers is the ring of integers in $\overline { { \mathbb { Q } } } ,$ , an algebraic closure of Q. Examples of algebraic integers include ${ \sqrt { 2 } } , { \sqrt { - 1 } } , { \sqrt [ { 3 } ] { 5 } } ,$ etc. since these elements are certainly roots of monic polynomials with coefficients in $\mathbb { Z } .$ . The definition of an algebraic integer a is that a be a rot of some monic polynomial in $\mathbb { Z } [ x ]$ , a condition which seems difficult to check. The next proposition gives a simple criterion for a to be an algebraic integer in terms of the minimal polynomial for a.
- **dependencies:** —


- **kind:** Proposition 28
- **source:** §15.3; printed pp. 691–705; extraction line 24854
- **statement/data:** An element a in some field extension of $\mathbb { Q }$ i s a n algebraic integer if and only if $\pmb { \alpha }$ is algebraic over Q and its minimal polynomial $m _ { \alpha , \mathbb { Q } } ( x )$ has integer coefficients. In particular, the algebraic integers in Q are the integers $\mathbb { Z } , \mathbf { i . e . , } \mathcal { O } _ { \mathbb { Q } } = \mathbb { Z } .$
- **dependencies:** —


- **kind:** Theorem 29
- **source:** §15.3; printed pp. 691–705; extraction line 24860
- **statement/data:** Let K be a number field of degree n over $\mathbb { Q } .$ (1) The ring ${ \mathcal { O } } _ { K }$ of integers in K is a Noetherian ring and is a free Z-module of rank n. (2) For every $\beta \in K$ there is some nonzero d $\epsilon \mathbb { Z }$ such that $d \beta$ is an algebraic integer. In particular, K is the field of fractions of ${ \mathcal { O } } _ { K }$ (3) If $\beta _ { 1 } , \beta _ { 2 } , \ldots , \beta _ { n }$ is any Q-basis of K , then there is an integer d such that $d \beta _ { 1 } , d \beta _ { 2 } , \ldots , d \beta _ { n }$ is a basis for a free Z-submodule of ${ \mathcal { O } } _ { K }$ of rank n. Any basi of the $\mathbb { Z }$ -module ${ \mathcal { O } } _ { K }$ is also a basis for K as a vector space over Q.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.3; printed pp. 691–705; extraction line 24916
- **statement/data:** An integral basis for the number field K is a basis of the ring of integers in K considered as a free Z-module of rank $[ K : \mathbb { Q } ]$ If P is a nonzero prime ideal in the ring of integers $\mathcal { O } _ { K }$ of a number field K then $P \cap \mathbb { Z }$ is a prime ideal in $\mathbb { Z } .$ If a E P, then the constant term of the minimal polynomial for a over Q is then an element in $P \cap \mathbb { Z } ,$ , which shows that $P \cap \mathbb { Z } = p \mathbb { Z }$ is also a nonzero prime ideal in $\mathbb { Z } .$ . By Theorem 26, every prime ideal (p) in $\mathbb { Z }$ arises in this way. Since $p \mathbb { Z }$ is a maximal ideal, it also follows from (2) in Theorem 26 that nonzero prime ideals in ${ \mathcal { O } } _ { K }$ are maximal, and then by Corollary 27, there are finitely many prime ideals P in ${ \mathcal { O } } _ { K }$ with $P \cap \mathbb { Z } = p \mathbb { Z }$ . We shal see later (Corollary 16 in Section 16.3) that every nonzero ideal in the ring of integers $o f a$ number field can be written uniquely as the product of prime ideals, and in the case of the ideal $p { \mathcal { O } } _ { K }$ the distinct prime factors are precisely the finitely many ideals P in ${ \mathcal { O } } _ { K }$ with $P \cap \mathbb { Z } = p \mathbb { Z } .$ . This property replaces the unique factorization of elements in $O _ { K }$ into primes (which need not hold since $O _ { K }$ need not be a U.F.D.). …
- **dependencies:** FC01-C15-U049, FC01-C15-U050


- **kind:** Named example
- **source:** §15.3; printed pp. 691–705; extraction line 24920
- **statement/data:** The ring of integers in a quadratic number field is computed explicitly, with the usual distinction by the squarefree radicand modulo 4.
- **dependencies:** —


- **kind:** Named example
- **source:** §15.3; printed pp. 691–705; extraction line 24942
- **statement/data:** The ring of integers in cyclotomic fields is treated as the standard cyclotomic integer example.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.3; printed pp. 691–705; extraction line 24950
- **statement/data:** If k is a field the elements $y _ { 1 } , y _ { 2 } , \ldots , y _ { q }$ in some k-algebra are called algebraically independent over k if there is no nonzero polynomial $\pmb { p }$ in $\pmb q$ variables over k such that $p ( y _ { 1 } , y _ { 2 } , \ldots , y _ { q } ) = 0$ Thus $y _ { 1 } , y _ { 2 } , \ldots , y _ { q }$ are algebraically independent if and only ifthe k-algebra homomorphism from the polynomial ring $k [ x _ { 1 } , \ldots , x _ { q } ]$ to $k [ y _ { 1 } , \ldots , y _ { q } ]$ defined by $x _ { i } \mapsto y _ { i }$ is an isomorphism. Elements in a field extension of k are algebraically independent if and only if they are independent transcendentals over k.
- **dependencies:** —


- **kind:** Theorem 30 (Noether's Normalization Lemma)
- **source:** §15.3; printed pp. 691–705; extraction line 24954
- **statement/data:** (Noether's Normalization Lemma) Let k be a field and suppose that $A = k [ r _ { 1 } , r _ { 2 } , \ldots , r _ { m } ]$ is a finitely generated k-algebra. Then for some $q , 0 \leq q \leq m$ there are algebraically independent elements $y _ { 1 } , y _ { 2 } , \dotsc , y _ { q } \in A$ such that A is integral over $k [ y _ { 1 } , y _ { 2 } , \ldots , y _ { q } ]$
- **dependencies:** —


- **kind:** Theorem 31 (Hilbert's Nullstellensatz - Weak Form)
- **source:** §15.3; printed pp. 691–705; extraction line 24980
- **statement/data:** (Hilbert's Nullstellensatz - Weak Form) Let k be an algebraically closed field. Then M is a maximal ideal in the polynomial ring $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ if and only if $M = ( x _ { 1 } - a _ { 1 } , \ldots , x _ { n } - a _ { n } )$ for some $a _ { 1 } , \ldots , a _ { n } \in k .$ . Equivalently, the maps $\mathcal { Z }$ and $\boldsymbol { \tau }$ give a bijective corespondence $$ {\text { points in } \mathbb {A} ^ {n} } \xrightarrow [ \leftarrow ]{\mathcal {I}} {\text { maximal ideals in } k [ \mathbb {A} ^ {n} ] }. $$ Moreover, i f I i s any proper ideal i n $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ then $\mathcal { Z } ( I ) \neq \emptyset$
- **dependencies:** —


- **kind:** Theorem 32 (Hilbert's Nullstellensatz)
- **source:** §15.3; printed pp. 691–705; extraction line 24990
- **statement/data:** (Hilbert's Nullstellensatz) Let k be an algebraically closed field. Then $\boldsymbol { \mathcal { T } } ( \mathcal { Z } ( I ) ) = \mathop { \Gamma \mathrm { a d } } I$ for every ideal I of $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ . Moreover, the maps Z and I define inverse bijections $$ {\text { affine algebraic sets } } \xrightarrow [ \leftarrow_ {\mathcal {Z}} ]{\mathcal {I}} {\text { radical ideals } }. $$
- **dependencies:** —


- **kind:** Corollary 33 (Variant of Hilbert's Nullstellensatz)
- **source:** §15.3; printed pp. 691–705; extraction line 25018
- **statement/data:** (Variant of Hilbert's Nullstellensatz) If k is any field with algebraic closure $\bar { k }$ and I is an ideal in $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ] _ { }$ . then $\mathcal { T } _ { k } ( \mathcal { Z } _ { \bar { k } } ( I ) ) = \operatorname { r a d } I$ , where $\mathcal { Z } _ { \bar { \pmb { k } } } ( I )$ is the zero set in $\bar { k } ^ { n }$ of the polynomials in I and $\mathcal { T } _ { k } ( \mathcal { Z } _ { \bar { k } } ( I ) )$ is the ideal of polynomials in $k [ x _ { 1 } , x _ { 2 } , \ldots , x _ { n } ]$ vanishing at all the points in $\mathcal { Z } _ { \bar { \pmb { k } } } ( I )$ . In particular, $I = ( 1 )$ if and only if there are no common zeros in $\bar { k } ^ { n }$ of the polynomials in I .
- **dependencies:** —


- **kind:** Proposition 34
- **source:** §15.3; printed pp. 691–705; extraction line 25038
- **statement/data:** Suppose k is any field. If $\boldsymbol { I } ~ = ~ ( f _ { 1 } , \ldots , f _ { s } )$ is a proper ideal in $k [ x _ { 1 } , \dots , x _ { n } ]$ , then $f \in { \bf { r a d } } I$ if and only if $( f _ { 1 } , \dots , f _ { s } , 1 - y f ) = k [ x _ { 1 } , \dots , x _ { n } , y ]$
- **dependencies:** —


- **kind:** Corollary 35
- **source:** §15.3; printed pp. 691–705; extraction line 25050
- **statement/data:** Suppose $\boldsymbol { I } = ( f _ { 1 } , \ldots , f _ { s } )$ in $k [ x _ { 1 } , \ldots , x _ { n } ]$ . Then f E rad I if and only if { 1 } is the reduced Grobner basis for the ideal $( f _ { 1 } , \dots , f _ { s } , 1 - y f ) \mathrm { i n } k [ x _ { 1 } , \dots , x _ { n } , y ]$ with respect to any monomial ordering.
- **dependencies:** —


- **kind:** Theorem 36
- **source:** §15.4; printed pp. 706–730; extraction line 25206
- **statement/data:** Let R be a comutative ring with 1 and let D be a multiplicatively closed subset of R containing 1 . Then there is a commutative ring $D ^ { - 1 } R$ and a ring homomorphism $\pi : R \to D ^ { - 1 } R$ satisfying the following universal property: for any homomorphism $\psi : R S$ of comutative rings that sends 1 to 1 such that $\psi ( d )$ is a unit in S for every $d \in D ,$ , there is a unique homomorphism $\Psi : D ^ { - 1 } R S$ such that $\Psi \circ \pi = \psi$
- **dependencies:** —


- **kind:** Corollary 37
- **source:** §15.4; printed pp. 706–730; extraction line 25234
- **statement/data:** In the notation of Theorem 36, (1) ker $\pi = { r \in R \mid x r = 0$ for some $x \in D }$ ; in particular, $\pi : R \to D ^ { - 1 } R$ is an injection .if and only if D contains no zero divisors of $R ,$ , and (2) $\bar { D ^ { - 1 } } R = 0$ if and only if $0 \in D ,$ , hence if and only if $D$ contains nilpotent elements.
- **dependencies:** FC01-C15-U064


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25242
- **statement/data:** The ring $D ^ { - 1 } R$ is called the ring of fractions of R with respect to D or the localization of R at D.
- **dependencies:** —


- **kind:** Construction
- **source:** §15.4; printed pp. 706–730; extraction line 25256
- **statement/data:** For a prime ideal P, localization at D=R\P is denoted R_P; every element outside P becomes a unit.
- **dependencies:** FC01-C15-U066


- **kind:** Convention
- **source:** §15.4; printed pp. 706–730; extraction line 25272
- **statement/data:** For π:R→D^{-1}R, extension of I is ^eI=D^{-1}I and contraction of J is ^cJ=π^{-1}(J).
- **dependencies:** —


- **kind:** Proposition 38
- **source:** §15.4; printed pp. 706–730; extraction line 25276
- **statement/data:** In the preceding notation we have (1) For any ideal J of $D ^ { - 1 } R$ we have $J = ^ { e } ( ^ { c } J )$ . In particular, every ideal of $D ^ { - 1 } R$ is the extension of some ideal of R, and distinct ideals of $D ^ { - 1 } R$ have distinct contractions in R. (2) For any ideal I of R we have $$ ^ c (^ {e} I) = {r \in R \mid d r \in I \text { for some } d \in D }. $$ Also, ${ } ^ { e } I = D ^ { - 1 } R$ if and only if $I \cap D \neq \emptyset .$ (3) Extension and contraction give a bijective correspondence $$ \left{ \begin{array}{c} \text {prime ideals P of R} \ \text {with P\cap D = \emptyset} \end{array} \right} \quad \xrightarrow [ c ]{e} \quad \left{\text {prime ideals of D^{-1} R} \right}. $$ (4) If R is Noetherian (or Artinian) then $D ^ { - 1 } R$ is Noetherian (Artinian, respectively).
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25306
- **statement/data:** Suppose R is a comutative ring with 1 and D is a multiplicatively closed subset containing 1 . The saturation of the ideal l in R with respect to D is the idea $\vert ^ { c } ( ^ { e } I )$ in R, where contraction and extension are computed with respect to $\pi : R \mapsto D ^ { - 1 } R$ If $I = ^ { c } ( ^ { e } I )$ then I is said to be saturated with respect to $D .$ Loosely speaking, (2) of Proposition 38 shows that the saturation of I consists of elements of R that would lie in I if we allowed denominators from D. The ideal is saturated with respect to if we don't obtain any additional elements even if we allow denominators from D.
- **dependencies:** FC01-C15-U069


- **kind:** Proposition 39
- **source:** §15.4; printed pp. 706–730; extraction line 25320
- **statement/data:** Suppose R is a comutative ring with 1 and I is an ideal in $R [ x ]$ Then I is a prime ideal in $R [ x ]$ if and only if i. $J = I \cap R$ is a prime ideal in $R , \mathrm { i } . \mathbf { e } . , S = R / J$ is an integral domain, and ii. if $\overline { I }$ is the image of I in $s [ x ]$ then $\overline { { I } } F [ x ]$ is a prime ideal in $F [ x ]$ satisfying $\overline { { I } } F [ x ] \cap S [ x ] = \overline { { I } } .$
- **dependencies:** —


- **kind:** Proposition 40
- **source:** §15.4; printed pp. 706–730; extraction line 25332
- **statement/data:** Let S be an integral domain with fraction field F and let A be a nonzero ideal in $s [ x ]$ . Suppose $A F [ x ] = ( h ( x ) )$ where $h ( x )$ is a polynomial in $s [ x ]$ with leading coeficient $a \in S$ . Let $s _ { a }$ be the localization of S with respect to the powers of a. Then (1) $A F [ x ] \cap S [ x ] = A S _ { a } [ x ] \cap S [ x ]$ , and (2) if A denotes the ideal generated by A and $1 - a t$ in the polynomial ring $s [ x , t ] ,$ then $A S _ { a } [ x ] \cap S [ x ] = A \cap S [ x ]$
- **dependencies:** —


- **kind:** Construction
- **source:** §15.4; printed pp. 706–730; extraction line 25396
- **statement/data:** For an R-module M and multiplicatively closed D⊆R containing 1, D^{-1}M is formed from D×M by (d,m)∼(e,n) iff x(dn−em)=0 for some x∈D, with the usual fraction addition and D^{-1}R-action.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25410
- **statement/data:** The $D ^ { - 1 } R { \mathrm { - m o d u l e } }$ $D ^ { - 1 } M$ is called the module of fractions of M with respect to D or the localization of M at D. Note that the localization $D ^ { - 1 } M$ is also an R-module (since each $r \in R$ acts by r/1 on $D ^ { - 1 } M )$ , and there is an R-module homomorphism $$ \pi : M \to D ^ {- 1} M \quad \text { defined by } \quad \pi (m) = \frac {m}{1}. $$ It follows directly from the definition of the equivalence relation that $$ \ker \pi = {m \in M \mid d m = 0 \text { for some } d \in D }. $$ The homomorphism 1r has a universal property analogous to that in Theorem 36. Suppose N is an R -module with the property that left multiplication on N by d is a bijection of N for every d $\in D .$ $\mathbf { I f } \psi : M \to N$ is any R-module homomorphism then there is a unique R-module homomorphism $\Psi : D ^ { - 1 } M \to N$ such that $\Psi \circ \pi = \psi$ If M and N are R-modules and $\varphi : M \to N$ is an R-module homomorphism, then for any multiplicative set D in R it is easy to check that there is an induced $D ^ { - 1 } R$ -module homomorphism from $D ^ { - 1 } M$ to $D ^ { - 1 } N$ defined by mapping $m / d$ to $\varphi ( m ) / d .$
- **dependencies:** FC01-C15-U064


- **kind:** Proposition 41
- **source:** §15.4; printed pp. 706–730; extraction line 25430
- **statement/data:** Let D be a multiplicatively closed subset of R containing 1 and let M be an R-module. Then $D ^ { - 1 } M \cong D ^ { - 1 } R \ \tilde { \otimes _ { R } }$ M as $D ^ { - 1 } R { \mathrm { - m o d u l e s } } ,$ , i.e., $\mathsf { \bar { D } } ^ { - 1 } M$ is the $D ^ { - 1 } R { \mathrm { - m o d u l e } }$ obtained by extension of scalars from the R-module M.
- **dependencies:** —


- **kind:** Proposition 42
- **source:** §15.4; printed pp. 706–730; extraction line 25436
- **statement/data:** Let R be a comutative ring with I and let $D ^ { - 1 } R$ be its localization with respect to the multiplicatively closed subset D of R containing 1 . (1) Localization comutes with finite sums and intersections of ideals: If I and J are ideals of $R ,$ , then $$ D ^ {- 1} (I + J) = D ^ {- 1} (I) + D ^ {- 1} (J) \quad \text { and } \quad D ^ {- 1} (\dot {I} \cap J) = D ^ {- 1} (I) \cap D ^ {- 1} (J). $$ Localization comutes with quotients: $$ D ^ {- 1} R / D ^ {- 1} I \cong D ^ {- 1} (R / I), $$ (where the localization on the right is with respect to the image of D in the quotient $R / I )$ {2) Localization comutes with taking radicals: If N is the nilradical of R, then $D ^ { - 1 } N$ is the nilradical of $D ^ { - 1 } R$ . If I is an ideal in R , then $\operatorname { r a d } ( D ^ { - 1 } I )$ is $D ^ { - 1 } ( { \bf r a d } I )$ (3) Primary ideals correspond to primary ideals in the correspondence (3) of Proposition 38. More precisely, suppose Q is a P-primary ideal in R. If $D \cap P \neq \emptyset$ then $D ^ { - 1 } Q = \dot { D ^ { - 1 } R }$ . If $D \cap P = \emptyset$ then $D ^ { - 1 } P$ is a prime ideal, the extension $D ^ { - 1 } Q$ of Q is a $D ^ { - 1 } P$ -primary ideal in $D ^ { - 1 } R$ , and the contraction back to R of $D ^ { - 1 } Q$ is $Q$ (4) Localization comutes with finite sums, intersections and quotients of modules: If L and N submodules of the R-module M, then {a) $D ^ { - 1 } ( L + N ) = D ^ { - 1 } L + D ^ { - 1 } N$ and $D ^ { - 1 } ( L \cap N ) = D ^ { - 1 } L \cap D ^ { - 1 } N . …
- **dependencies:** FC01-C15-U069


- **kind:** Proposition 43
- **source:** §15.4; printed pp. 706–730; extraction line 25480
- **statement/data:** Let R be a Noetherian ring and let $$ I = Q _ {1} \cap \dots \cap Q _ {m} $$ be a minimal primary decomposition of the proper ideal /, where $Q _ { i }$ is a P;-primary ideal. Suppose D is a multiplicatively closed set of R containing 1 and the primary ideals $Q _ { 1 } , \ldots , Q _ { m }$ are numbered so that $D \cap P _ { i } = \emptyset$ for $1 \leq i \leq t$ and $D \cap P _ { i } \neq \emptyset$ for $t + 1 \leq i \leq m$ . Then $$ D ^ {- 1} I = D ^ {- 1} Q _ {1} \cap \dots \cap D ^ {- 1} Q _ {t} $$ is a minimal primary decomposition of $D ^ { - 1 } I$ $D ^ { - 1 } R$ and $D ^ { - 1 } Q _ { i }$ is a $D ^ { - 1 } P _ { i } { \mathrm { - p r i m a r y } }$ ideal. Further, the contraction of $D ^ { - 1 } Q _ { i }$ back to R is $Q _ { i }$ for $1 \leq i \leq t$ and $$ { } ^ { c } ( D ^ { - 1 } I ) = Q _ { 1 } \cap \cdots \cap Q _ { t } $$ is a minimal primary decomposition of the contraction of $D ^ { - 1 } I$ back to R.
- **dependencies:** —


- **kind:** Corollary 44 [source OCR: Corollary 4]
- **source:** §15.4; printed pp. 706–730; extraction line 25504
- **statement/data:** The primary ideals belonging to the isolated primes in a minimal primary decomposition of I are uniquely defined by I.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25510
- **statement/data:** A conuutative ring with 1 that has a unique maximal ideal is called a local ring.
- **dependencies:** —


- **kind:** Proposition 45
- **source:** §15.4; printed pp. 706–730; extraction line 25512
- **statement/data:** Let R be a conuutative ring with 1 . Then the following are equivalent: (1) R is a local ring with unique maximal ideal M (2) if M is the set of elements of R that are not units, then M is an ideal (3) there is a maximal ideal M of R such that every element $1 + m$ with $m \in M$ is a unit in R .
- **dependencies:** —


- **kind:** Proposition 46
- **source:** §15.4; printed pp. 706–730; extraction line 25524
- **statement/data:** For any commutative ring R with 1 , let $R _ { P }$ be the localization of R at the prime ideal P and let $^ { e } P$ be the extension of P to $R _ { P }$ (1) The ring $R _ { P }$ i s a local ring with unique maximal ideal $^ { e } P$ . The contraction of $^ { e } P$ to R is $P , \operatorname { i . e . , } { } ^ { c } ( { } ^ { e } P ) = P$ , and the map from R to $R _ { P }$ induces an injection of the integral domain $R / P$ into $R _ { P } / { } ^ { e } P$ . The quotient $R _ { P } / { } ^ { e } P$ is a field and is isomorphic to the fraction field of the integral domain $R / P$ (2) I f R is an integral domain, then $R _ { P }$ i s an integral domain. The ring R injects into the local ring $R _ { P } ,$ , and, identifying R with its image in $R _ { P }$ , the unique maximal ideal of $R _ { P }$ is $P R _ { P }$ (3) The prime ideals in $R _ { P }$ are i n bijective correspondence with the prime ideals of R contained in $P .$ . (4) If P is a minimal nonzero prime ideal of R then $R _ { P }$ has a unique nonzero prime ideal. (5) If $P \ = \ M$ is a maximal ideal and I is any M -primary ideal of R then $R _ { M } / { } ^ { e } I \cong R / I$ . In particular, $R _ { M } / { } ^ { e } M \cong R / M$ and $( ^ { e } M ) / ( ^ { e } M ) ^ { n } \cong M / M ^ { n }$ for all $n \geq 1$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25550
- **statement/data:** Let M be an R -module, let P be a prime ideal of R and set $D = R - P$ The $R _ { P }$ -module $D ^ { - 1 } M$ i s called the localization of M a t P , and i s denoted by $M _ { P }$ By Proposition 41, $M _ { P }$ can also be identified with the tensor product $R _ { P } \otimes _ { R } M$ When R is an integral domain and $P = ( \mathbf { 0 } )$ , then $M _ { ( 0 ) }$ is a module over the field of fractions F of R, i.e., is a vector space over F. The element $m / 1$ is zero in $M _ { P }$ if and only if $r m = 0$ for some $r \in R - P$ , so localizing at P anihilates the $P ^ { \prime } .$ -torsion elements of M for primes $P ^ { \prime }$ not contained in P. In particular, localizing at (0) over an integral domain annihilates the torsion subgroup of M.
- **dependencies:** FC01-C15-U075


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25556
- **statement/data:** If R is an integral domain, then the rank of the R-module M is the dimension of the localization $M _ { ( 0 ) }$ as a vector space over the field of fractions of R . It i s easy to see that this definition of rank agrees with the notion o f rank introduced in Chapter 1 2.
- **dependencies:** —


- **kind:** Proposition 47
- **source:** §15.4; printed pp. 706–730; extraction line 25566
- **statement/data:** Let M be an R-module. Then the following are equivalent: (1) $M = 0 ;$ (2) $M _ { P } = \mathbf { 0 }$ for all prime ideals P of R, and (3) $M _ { \mathfrak { m } } = \mathbf { 0 }$ for al maximal ideals of R.
- **dependencies:** —


- **kind:** Proposition 48
- **source:** §15.4; printed pp. 706–730; extraction line 25578
- **statement/data:** Let R be an integral domain. Then R is the intersection of the localizations of R: $R = \cap _ { P } R _ { P }$ . In fact, $R = \cap _ { \mathfrak { m } } R _ { \mathfrak { m } }$ is the intersection of the localizations of R at the maximal ideals m of R.
- **dependencies:** —


- **kind:** Proposition 49
- **source:** §15.4; printed pp. 706–730; extraction line 25590
- **statement/data:** Let R be an integral domain. Then the following are equivalent: (1) R is normal, i.e., R is integrally closed (in its field of fractions) (2) $R _ { P }$ is normal for all prime ideals P of R (3) $R _ { \mathfrak { m } }$ is normal for all maximal ideals m of R.
- **dependencies:** —


- **kind:** Corollary 50
- **source:** §15.4; printed pp. 706–730; extraction line 25604
- **statement/data:** Let R be a subring of the comutative ring S with $1 \in R .$ , and assume that S is integral over R. If P is a prime ideal in R, then there is a prime ideal Q of S with $P = Q \cap R$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25626
- **statement/data:** We say $f / g$ is regular at v or defined at the point $v \in V$ if there is some $f _ { 1 } , g _ { 1 } \in k [ V ]$ with $f / g = f _ { 1 } / g _ { 1 }$ and $g _ { 1 } ( v ) \neq 0$ If $f _ { 2 } , g _ { 2 }$ is another such pair with $g _ { 2 } ( v ) \neq 0 ;$ , then $f _ { 1 } ( v ) / g _ { 1 } ( v ) = f _ { 2 } ( v ) / g _ { 2 } ( v )$ as elements of $k ,$ so whenever $f / g$ is regular at v there is a well defined way of specifying its value in k at v .
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25638
- **statement/data:** For each point $v \in V$ the collection of rational functions on V that are defined at $v ,$ $$ \mathcal {O} _ {v, V} = {f / g \in k (V) \mid f / g \text { is regular at } v }, $$ is called the local ring of V at v. Equivalently, the local ring of V at v is the localization of $k [ V ]$ at the maximal ideal $\boldsymbol { \mathcal { T } } ( \boldsymbol { \upsilon } )$ In particular, $\mathcal { O } _ { v , V }$ is a local ring with unique maximal ideal ${ \mathfrak { m } } _ { v , V }$ , where $$ \mathfrak {m} _ {v, V} = {f / g \in \mathcal {O} _ {v, V} \mid f / g = f _ {1} / g _ {1} \text { with } f _ {1} (v) = 0, g _ {1} (v) \neq 0 } $$ is the set of rational functions on V that are defined and equal to 0 at Since $\mathcal { O } _ { v , V }$ is a localization of the Noetherian integral domain k[V] at a prime ideal, $\mathcal { O } _ { v , V }$ is also a Noetherian integral domain. Note also that $\mathcal { O } _ { \upsilon . V } / \mathfrak { m } _ { \upsilon . V } \cong k [ V ] / \mathcal { T } ( \upsilon ) \cong k$ by Proposition 46(5).
- **dependencies:** FC01-C15-U081


- **kind:** Proposition 51
- **source:** §15.4; printed pp. 706–730; extraction line 25656
- **statement/data:** If V is an afine variety over an algebraically closed field k then the rational functions on V that are regular at all points of V are precisely the polynomial functions $k [ V ]$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25668
- **statement/data:** A homomorphism of local rings is local when the inverse image of the target maximal ideal is the source maximal ideal.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25690
- **statement/data:** Define the tangent space to V at v to be the linear variety $$ \mathbb {T} _ {v, V} = \mathcal {Z} ({D _ {v} (f) (x _ {1}, \dots , x _ {n}) \mid f \in \mathcal {I} (V) }). $$ The formal partial derivatives are k-linear and obey the usual product rule for derivatives, so the tangent space may be computed from the generators for $\boldsymbol { \mathcal { T } } ( V )$ ) : $$ \text { if } \quad \mathcal {I} (V) = (f _ {1}, f _ {2}, \dots , f _ {m}) \qquad \text { then } \quad \mathbb {T} _ {v, V} = \bigcap_ {i = 1} ^ {m} \mathcal {Z} (D _ {v} (f _ {i})). $$
- **dependencies:** —


- **kind:** Proposition 52
- **source:** §15.4; printed pp. 706–730; extraction line 25706
- **statement/data:** Let V be an afine variety over the algebraically closed field k and let v be a point on V with local ring $\mathcal { O } _ { v , V }$ and coresponding maximal ideal ${ \mathfrak { m } } _ { v , V } .$ . Then there is a k-vector space isomorphism $$ (\mathbb {T} _ {v, V}) ^ {*} \cong \mathfrak {m} _ {v, V} / \mathfrak {m} _ {v, V} ^ {2} $$ where $( \mathbb { T } _ { \boldsymbol { v } , \boldsymbol { V } } ) ^ { * }$ denotes the vector space dual ( cf. Section 1 1 .3) of the tangent space $\mathbb { T } _ { \boldsymbol { v } , \boldsymbol { V } }$ to $V$ at v .
- **dependencies:** —


- **kind:** Definition
- **source:** §15.4; printed pp. 706–730; extraction line 25738
- **statement/data:** We say V is nonsingular at the point $v \in V$ (or v is a nonsingular point of V) if the dimension of the k-vector space $\mathbb { T } _ { v , V }$ is dim V. Equivalently (by Proposition 52), v is a nonsingular point of V if dim $\smash { { \varepsilon } ( \mathfrak { m } _ { v , V } / \mathfrak { m } _ { v , V } ^ { 2 } ) = \dim V }$ . Otherwise the point v is called a singular point. The variety V is nonsingular or smooth if it is nonsingular at every point. The geometric picture is that at a nonsingular point v there are as many independent tangents as one would expect: a tangent line on a curve, a tangent plane on a surface, etc. Whether a variety V is nonsingular at a point v can be determined from properties of the local ring $\mathcal { O } _ { v , V }$ . namely whether dim $\mathsf { \Pi } _ { k } ( \bar { \mathfrak { m } } _ { v , V } / \mathfrak { m } _ { v , V } ^ { 2 } ) = \dim \mathcal { O } _ { v , V }$ · A local ring having this property is said to be a regular local ring. In particular, the notion of singularity does not depend on the embedding of V in a specific affine space. This algebraic interpretation can be used to define smoothness for abstract algebraic varieties, where the geometric intuition of tangent planes to surfaces (for example) is not as obvious If $f _ { 1 } , \ldots , f _ { m }$ are generators for $\mathcal { T } ( V )$ defining V in $\mathbb { A } ^ { n }$ , then the dimension of V can be determined from a Grobner basis for $\mathcal { T } ( V )$ (cf. Exercise 29). …
- **dependencies:** FC01-C15-U093


- **kind:** Construction
- **source:** §15.4; printed pp. 706–730; extraction line 25764
- **statement/data:** For an irreducible affine curve, the integral closure of its coordinate ring in its function field gives its normalization/nonsingular model, finite over the original curve.
- **dependencies:** FC01-C15-U047


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 25958
- **statement/data:** Let R be a comutative ring with I . The spectrum or prime spectrum of R, denoted Spec R, is the set of all prime ideals of R. The set of all maximal ideals of R, denoted mSpec R, is called the maximal spectrum of R.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 25980
- **statement/data:** For $f\in R$ and $P\in\operatorname{Spec}R$, the value of $f$ at $P$ is $f(P)=\bar f\in R/P$.
- **dependencies:** FC01-C15-U096


- **kind:** Proposition 53
- **source:** §15.5; printed pp. 731–749; extraction line 26000
- **statement/data:** Let R be a commutative ring with 1 . The maps $\mathcal { Z }$ and I between R and Spec R defined above satisfy (1) for any ideal I of $R , { \mathcal { Z } } ( I ) = { \mathcal { Z } } ( \operatorname { r a d } ( I ) ) = { \mathcal { Z } } ( { \mathcal { Z } } ( I ) ) )$ , and $\boldsymbol { \mathcal { T } } ( \mathcal { Z } ( I ) ) = \mathop { \mathrm { r a d } } I$ (2) for any ideals $I , J$ of $R , \mathcal Z ( I \cap J ) = \mathcal Z ( I J ) = \mathcal Z ( I ) \cup \mathcal Z ( J )$ , and (3) if ${ I _ { j } }$ is an arbitrary collection of ideals of R, then $\mathcal { Z } ( \cup I _ { j } ) = \cap \mathcal { Z } ( I _ { j } )$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26026
- **statement/data:** The topology on Spec R defined by the closed sets $\mathcal { Z } ( I )$ for the ideals I of R is called the Zariski topology on Spec R. By definition, the closure in the Zariski topology of the singleton set ${ P }$ in Spec R consists of all the prime ideals of R that contain P. In particular, a point P in Spec R is closed in the Zariski topology if and only if the prime ideal P is not contained in any other prime ideals of $R ,$ i.e., if and only if $\bar { P }$ is a maximal ideal (so the Zariski topology on Spec R is not generally Hausdorf). These points are given a name:
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26030
- **statement/data:** The maximal ideals of R are called the closed points in Spec R. In terms of the terminology above, the points in Spec R that are closed in the Zariski topology are precisely the points in mSpec R. A closed subset of a topological space is irreducible if it is not the union of two proper closed subsets, or, equivalently, if every nonempty open set is dense. Arguments similar to those used to prove Proposition 17 show that the closed subset $Y = \mathcal { Z } ( I )$ in Spec R is ireducible if and only if $\boldsymbol { \mathcal { T } } ( \boldsymbol { Y } ) = \mathbf { r a d } \boldsymbol { I }$ is prime (cf. Exercise 16). The following proposition sumarizes some of these results:
- **dependencies:** FC01-C15-U032


- **kind:** Proposition 54
- **source:** §15.5; printed pp. 731–749; extraction line 26038
- **statement/data:** The maps Z and I define inverse bijections $$ {\text { Zariski closed subsets of } \operatorname{Spec} R } \xrightarrow [ \leftarrow_ {\mathcal {Z}} ]{\mathcal {I}} {\text { radical ideals of } R }. $$ Under this correspondence the closed points in Spec R corespond to the maximal ideals in R, and the ireducible subsets of Spec R correspond to the prime ideals in R.
- **dependencies:** —


- **kind:** Named example
- **source:** §15.5; printed pp. 731–749; extraction line 26048
- **statement/data:** In Spec Z the point (0) is dense (a generic point), while the nonzero prime ideals are closed points.
- **dependencies:** —


- **kind:** Named example
- **source:** §15.5; printed pp. 731–749; extraction line 26052
- **statement/data:** Affine k-algebras are compared with affine algebraic sets via maximal spectra; the source calls (mSpec R,R) the canonical model of an affine k-algebra.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26056
- **statement/data:** A finitely generated algebra over an algebraically closed field k having no nonzero nilpotent elements is called an afine k-algebra. If R is an afine k-algebra, then by Corollary 5 there is a surjective k-algebrahomomorphism $\pi : k [ x _ { 1 } , \ldots , x _ { n } ] \to R$ whose kernel / = ker n must be a radical ideal since R has no nonzero nilpotent elements. Let $V = \mathcal { Z } ( I ) \subseteq \mathbb { A } ^ { n }$ • Then $R \cong k [ x _ { 1 } , \ldots , x _ { n } ] / I = k [ V ]$ is the coordinate ring of an afine algebraic set over k. Hence afine k-algebras are precisely the rings arising as the rings of functions on afine algebraic sets over algebraically closed fields. By the Nullstellensatz, the points of mSpec R are in bijective corespondence with V, and the points of Spee R are in bijective corespondence with the subvarieties of V. By Theorem 6, morphisrns between two afine algebraic sets corespond bijectively with (kalgebra) homomorphisms of afine k-algebras. In the language of categories these results show that over an algebraically closed field k there is an equivalence of categories $$ \left{ \begin{array}{c} \text { affine algebraic sets } \ \text { morphisms of algebraic sets } \end{array} \right} \longleftrightarrow \left{ \begin{array}{c} \text { affine k -algebras } \ k \text {-algebra homomorphisms } \end{array} \right}. $$ The map from left to right sends the afine algebraic set V to its coordinate ring k[V]. The map from right to left sends the afine k-algebra R to mSpec R. …
- **dependencies:** FC01-C15-U007, FC01-C15-U013


- **kind:** Proposition 55
- **source:** §15.5; printed pp. 731–749; extraction line 26072
- **statement/data:** Every ring homomorphism $\varphi : R s$ mapping $1 _ { R }$ to $1 _ { S }$ induces a map $\varphi ^ { * }$ : Spec S ? Spec R that is continuous with respect to the Zariski topologies on Spec R and Spec S. While the generalization from afine algebraic sets to Spec R for general rings R has made matters slightly more complicated, there are (at least) two very important benefits gained by this more general setting. The first is that Spec R can be considered even for comutative rings R containing nilpotent elements; the second is that Spec R need not be a k-algebra for any field k, and even when it is, the field k need not be algebraically closed. The fact that many of the properties found in the situation of afine k-algebras hold in more general settings then allows the application of "geometric" ideas to these situations (for example, to Spec R when R is finite).
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26120
- **statement/data:** For any $f \in R$ let $X _ { f }$ denote the collection of prime ideals in $X = \operatorname { S p e c } R$ that do not contain $f .$ . Equivalently, $X _ { f }$ is the set of points of Spec R at which the value of $f \in R$ is nonzero. The set $X _ { f }$ is called a principal (or basic) open set in Spec R. Since $X _ { f }$ is the complement of the Zariski closed set ${ \mathcal { Z } } ( f )$ ) it is indeed an open set in Spec R as the name implies. Some basic properties of the principal open sets are indicated in the next proposition. Recall that a map between topological spaces is a homeomorphism if it is continuous and bijective with continuous inverse.
- **dependencies:** —


- **kind:** Proposition 56
- **source:** §15.5; printed pp. 731–749; extraction line 26124
- **statement/data:** Let $f \in R$ and let $X _ { f }$ be the coresponding principal open set in $X = { \mathsf { S p e c } } R .$ Then (1) $X _ { f } = X$ if and only if f is a unit, and $X _ { f } = \theta$ if and only if f is nilpotent, (2) $X _ { f } \cap X _ { g } = X _ { f g } ,$ (3) $X _ { f } \subseteq X _ { g _ { 1 } } \cup \dots \cup X _ { g _ { n } }$ , if and only if $f \in \operatorname { r a d } ( g _ { 1 } , \dotsc , g _ { n } )$ ; in particular $X _ { f } = X _ { g }$ if and only if rad(f) = rad(g ), (4) the principal open sets form a basis for the Zariski topology on Spec R, i.e., every Zariski open set in X is the union of some collection of principal open sets $X _ { f }$ (5) the natural map from R to $R _ { f }$ induces a homeomorphism from Spec $R _ { f }$ to $X _ { f }$ , where $R _ { f }$ i s the localization o f R at $f$ , (6) the spectrum of any ring i s quasicompact $( \mathrm { i . e . , }$ , every open cover has a finite subcover); in particular, $X _ { f }$ is quasicompact, and (7) if $\varphi : R s$ is any homomorphism of rings (with $\varphi ( 1 _ { R } ) = 1 _ { S } )$ then under the induced map $\varphi ^ { * } : Y = { \mathfrak { S p e c } } S \to$ Spec R the full preimage of the principal open set $X _ { f }$ in X is the principal open set $Y _ { \varphi ( f ) }$ in $Y$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26152
- **statement/data:** Suppose U is a Zariski open subset of Spec R. If $U = \varnothing ,$ , define $\mathcal { O } ( U ) = \mathbf { 0 } .$ Otherwise, define ${ \mathcal { O } } ( U )$ to be the set of functions s : $U \to \bigcup _ { Q \in U } R _ { Q }$ from U to the disjoint union of the localizations $R _ { Q }$ for $Q \in U$ with the following two properties: (1) $s ( Q ) \in R _ { Q }$ for every $Q \in U ,$ , and (2) for every $P \in U$ there is an open neighborhood $X _ { f } \subseteq U$ of P in U and an element $a / f ^ { n }$ in the localization $R _ { f }$ defining s on $X _ { f } , \mathrm { i . e . , } s ( Q ) = a / f ^ { n } \in R _ { Q }$ for every $Q \in X _ { f }$ If s , t are elements in $\mathcal { O } ( U )$ then $s + t$ and st are also elements in $\mathcal { O } ( U )$ (cf. Exercise 1 8), so each $\mathcal { O } ( U )$ is a ring. Also, every $a \in R$ gives an element in $\mathcal { O } ( U )$ defined by $s ( Q ) = a \in R _ { Q }$ . and in particular $1 \in R$ gives an identity for the ring ${ \mathcal { O } } ( U )$ If $U ^ { \prime }$ is an open subset of $\pmb { U }$ , then there is a natural restriction map from ${ \mathcal { O } } ( U )$ to $\mathcal { O } ( U ^ { \prime } )$ which is a homomorphism of rings ( cf. Exercise 19).
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26162
- **statement/data:** Let R be a commutative ring with 1, and let $X = \operatorname { S p e c } R .$ (1) The collection of rings $\mathcal { O } ( U )$ for the Zariski open sets of X together with the restriction maps $\mathcal { O } ( U ) \to \mathcal { O } ( U ^ { \prime } )$ ) for $U ^ { \prime } \subseteq U$ is called the structure sheaf on $X ,$ and is denoted simply by $\mathcal { O } \left( \mathbf { o r } \mathcal { O } _ { X } \right)$ (2) The elements s of $\mathcal { O } ( U )$ are called the sections of 0 over $\boldsymbol { U }$ . The elements of ${ \mathcal { O } } ( X )$ are called the global sections of 0.
- **dependencies:** —


- **kind:** Proposition 57
- **source:** §15.5; printed pp. 731–749; extraction line 26170
- **statement/data:** Let $X = { \mathsf { S p e c } } R$ and let $\mathcal { O } = \mathcal { O } _ { X }$ be its structure sheaf. The global sections of 0 are the elements of $R , \operatorname { i . e . , } { \mathcal { O } } ( X ) \cong R$ . More generally, if $X _ { f }$ is a principal open set in X for some $f \in R$ , then $\mathcal { O } ( X _ { f } )$ is isomorphic to the localization $R _ { f }$
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26194
- **statement/data:** If $P \in X = \mathbf { S } \mathbf { p } \mathbf { e } \mathbf { c } R ,$ , then the direct limit, $\mathcal { O } ( U )$ , of the rings ${ \mathcal { O } } ( U )$ for the open sets U of X containing P is called the stalk of the structure sheaf at $P _ { i }$ , and is denoted $\mathcal { O } _ { P }$
- **dependencies:** —


- **kind:** Proposition 58
- **source:** §15.5; printed pp. 731–749; extraction line 26196
- **statement/data:** Let $X = { \mathsf { S p e c } } R$ and let $\mathcal { O } = \mathcal { O } _ { X }$ be its structure sheaf. The stalk of 0 at the point $P \in X$ is isomorphic to the localization $R _ { P }$ of R at $P \colon { \mathcal { O } } _ { P } \cong R _ { P }$ . In particular, the stalk $\mathcal { O } _ { P }$ is a local ring.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26202
- **statement/data:** A point P∈Spec R is nonsingular/smooth when the local ring R_P is a regular local ring.
- **dependencies:** FC01-C15-U079


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26208
- **statement/data:** Let R be a commutative ring with 1 . The pair (Spec R, $\mathcal { O } _ { \mathtt { S p e c } R } )$ , consisting of the space Spec R with the Zariski topology together with the structure sheaf $\mathcal { O } _ { \tt S p e c R }$ is called an afine scheme. The notion of an afine scheme gives a completely algebraic generalization of the geometry of afine algebraic sets valid for arbitrary commutative rings, and is the starting point for modem algebraic geometry.
- **dependencies:** —


- **kind:** Definition
- **source:** §15.5; printed pp. 731–749; extraction line 26252
- **statement/data:** Suppose (Spec $R , { \mathcal { O } } _ { \mathsf { s p e c } R } )$ and (Spec S, $\mathcal { O } _ { \mathtt { S p e c } S } )$ are two afine schemes. A morphism of afine schemes from (Spec S, $\mathcal { O } _ { \tt S p e c } s )$ to (Spec $R , { \mathcal { O } } _ { \operatorname { s p e c } R } )$ is a pair $( \varphi ^ { * } , \varphi ^ { # } )$ such that (1) $\varphi ^ { * } : \mathbb { S } \mathrm { p e c } S $ Spec R is Zariski continuous, (2) there are ring homomorphisms $\varphi ^ { # } : \mathcal { O } ( U ) \to \mathcal { O } ( \varphi ^ { * - 1 } ( U ) )$ for every Zariski open subset U in Spec R that comute with the restriction maps, and (3) if $P ^ { \prime } \in \mathsf { S p e c } S$ with coresponding point $P = \varphi ^ { * } ( P ) \in { \mathrm { S p e c } } R ,$ , then under the induced homomorphism on stalks $\varphi ^ { # } : \mathcal { O } _ { \operatorname { S p e c } R , P } \to \mathcal { O } _ { \operatorname { S p e c } S , P ^ { \prime } }$ the preimage of the maximal ideal of $\mathcal { O } _ { \tt S p e c } \thinspace s , P ^ { \prime }$ is the maximal ideal of $\mathcal { O } _ { \mathtt { S p e c } R , P }$ A homomorphism $\psi : A B$ from the local ring A to the local ring B with the property that the preimage of the maximal ideal of B is the maximal ideal of A is called a local homomorphism of local rings. The third condition in the definition is then the statement that the induced homomorphism on stalks is required to be a local homomorphism. …
- **dependencies:** —


- **kind:** Theorem 59
- **source:** §15.5; printed pp. 731–749; extraction line 26274
- **statement/data:** Every ring homomorphism $\varphi : R S$ induces a morphism $$ \left(\varphi^ {*}, \varphi^ {#}\right): \left(\operatorname{Spec} S, \mathcal {O} _ {\operatorname{Spec} S}\right)\rightarrow \left(\operatorname{Spec} R, \mathcal {O} _ {\operatorname{Spec} R}\right) $$ of afine schemes. Conversely, every morphism of afine schemes arises from such a ring homomorphism $\varphi$ . Theorem 59 is the analogue for Spec R of Theorem 6, which converted geometric questions relating to afine algebraic sets to algebraic questions for their coordinate rings. The condition that the homomorphism on stalks be a local homomorphism in the definition of a morphism of afine schemes is necessary: a continuous map on the spectra together with a set of compatible ring homomorphisms on sections (hence also on stalks) is not suficient to force these maps to come from a ring homomorphism
- **dependencies:** FC01-C15-U013



- **kind:** Definition
- **source:** §16.1; printed pp. 750–754; extraction line 26455
- **statement/data:** For any commutative ring R the Krul dimension (or simply the dimension) of R is the maximum possible length of a chain $P _ { 0 } \subset P _ { 1 } \subset P _ { 2 } \subset \cdots \subset P _ { n }$ of distinct prime ideals in R . The dimension of R is said to be infinite if R has arbitrarily long chains of distinct prime ideals. A ring with finite dimension must satisfy both the ascending and descending chain conditions on prime ideals (although not necessarily on all ideals). A field has dimension 0 and a Principal Ideal Domain that is not a field has dimension 1.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.1; printed pp. 750–754; extraction line 26461
- **statement/data:** Jacobson radical R R and is denoted by Jac R . The Jacobson radical is analogous to the Frattini subgroup of a group, and it enjoys some coresponding properties (cf. Exercise 24 in Section 6. 1):
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §16.1; printed pp. 750–754; extraction line 26465
- **statement/data:** Let $\mathcal { I }$ be the Jacobson radical of the conuutative ring R. (1) If I is a proper ideal of R, then so is $( I , { \mathcal { I } } )$ , the ideal generated by I and $\mathcal { I }$ (2) The Jacobson radical contains the nilradical of R: rad ${ \mathbf 0 } \subseteq$ Jac R. (3) An element x belongs to :J if and only if $1 - r x$ is a unit for all $r \in R$ (4) (Nakayama 's Lemma) If M is any finitely generated R-module and ${ \mathcal { I } } M = M ,$ then $M = 0$
- **dependencies:** —


- **kind:** Definition
- **source:** §16.1; printed pp. 750–754; extraction line 26489
- **statement/data:** A conuutative ring R is said to be Artinian or to satisfy the descending chain condition on ideals (or $_ { D . C . C . }$ on ideals) if there is no infinite decreasing chain of ideals in $R ,$ i.e., whenever $I _ { 1 } \supseteq I _ { 2 } \supseteq I _ { 3 } \supseteq \cdots$ is a decreasing chain of ideals of $R ,$ then there is a positive integer m such that $I _ { k } = I _ { m }$ for all $k \geq m$ . Similarly, an R-module M is said to be Artinian if it satisfies D.C.C. on submodules. It is inuediate from the Lattice Isomorphism Theorem that every quotient $R / I$ of an Artinian ring R by an ideal I is again an Artinian ring. The following result for Artinian rings is parallel to results in Theorem 15.2. The proof is completely analogous, and so is left as an exercise.
- **dependencies:** —


- **kind:** Proposition 2
- **source:** §16.1; printed pp. 750–754; extraction line 26495
- **statement/data:** The following are equivalent: (1) R is an Artinian ring. (2) Every nonempty set of ideals of R contains a minimal element under inclusion. The next result gives the main structure theorem for Artinian rings.
- **dependencies:** —


- **kind:** Theorem 3
- **source:** §16.1; printed pp. 750–754; extraction line 26503
- **statement/data:** Let R be an Artinian ring. (1) There are only finitely many maximal ideals in R. (2) The quotient $R / ( \operatorname { J a c } R )$ is a direct product of a finite number of fields. More precisely, if $M _ { 1 } , \ldots , M _ { n }$ are the finitely many maximal ideals in R then $$ R / (\operatorname{Jac} R) \cong k _ {1} \times \dots \times k _ {n}, $$ where $k _ { i }$ is the field $R / M _ { i }$ for $1 \leq i \leq n$ (3) Every prime ideal of R is maximal, i.e., R has Krull dimension 0. The Jacobson radical of R equals the nilradical of R and is a nilpotent ideal: (Jac $R ) ^ { m } = 0$ for some $m \geq 1$ (4) The ring R is isomorphic to the direct product of a finite number of Artinian local rings. (5) Every Artinian ring is Noetherian.
- **dependencies:** —


- **kind:** Corollary 4
- **source:** §16.1; printed pp. 750–754; extraction line 26553
- **statement/data:** The ring R is Artinian if and only if R is Noetherian and has Krull dimension 0.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26629
- **statement/data:** (1) A discrete valuation on a field K is a function $\nu : K ^ { \times } \to \mathbb { Z }$ satisfying (i) v is surjective, (ii) $\nu ( x y ) = \nu ( x ) + \nu ( y ) \quad { \mathrm { ~ f o r ~ a l l ~ } } x , y \in K ^ { \times }$ (iii) $\nu ( x + y ) \geq \operatorname* { m i n } { \nu ( x ) , \nu ( y ) }$ for all $x , y \in K ^ { \times }$ with $x + y \neq 0$ The subring ${ x \in K \mid \nu ( x ) \geq 0 } \cup$ {0} is called the valuation ring of v. (2) An integral domain R is called a Discrete Valuation Ring (D.V.R.) if R is the valuation ring of a discrete valuation v on the field of fractions of R. The valuation v is often extended to all of K by defining $\nu ( 0 ) = + \infty ,$ , in which case (ii) and (iii) hold for all a, $b \in K$
- **dependencies:** —


- **kind:** Proposition 5
- **source:** §16.2; printed pp. 755–763; extraction line 26673
- **statement/data:** Suppose R is a Discrete Valuation Ring with respect to the valuation $\nu ,$ and let t be any element of R with $\nu ( t ) = 1$ . Then (1) A nonzero element $u \in R$ is a unit if and only if $\nu ( u ) = 0 .$ (2) Every nonzero element $r \in R$ can be writen in the form $r = u t ^ { n }$ for some unit $u \in R$ and some ${ \pmb n } \ge { \bf 0 }$ . Every nonzero element x in the field of fractions of R can be written in the form $x = u t ^ { n }$ for some unit $u \in R$ and some $n \in \mathbb { Z } .$ (3) Every nonzero ideal of R is a principal ideal of the form $( t ^ { n } )$ for some $\begin{array} { r } { n \geq 0 . } \end{array}$ In particular, R is a Noetherian ring.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26687
- **statement/data:** If R is a D.V.R. with valuation v, then an element t of R with $\nu ( t ) = 1$ is called a unifonizing (or local) parameter for R.
- **dependencies:** —


- **kind:** Corollary 6
- **source:** §16.2; printed pp. 755–763; extraction line 26689
- **statement/data:** Let R be a Discrete Valuation Ring. (1) The ring R is an integrally closed local ring with unique maximal ideal given by the elements with strictly positive valuation: $M = { r \in R \mid \nu ( r ) > 0 }$ . Every nonzero ideal in R is of the form $M ^ { n }$ for some integer ${ \pmb n } \geq { \bf 0 }$ (2) The only prime ideals of R are M and 0, i.e., Spec $R = { 0 , M }$ . In particular, a D.V.R. has Krull dimension 1 .
- **dependencies:** —


- **kind:** Theorem 7
- **source:** §16.2; printed pp. 755–763; extraction line 26699
- **statement/data:** The following properties of a ring R are equivalent: (1) R is a Discrete Valuation Ring, (2) R is a P.I.D. with a unique maximal ideal $P \neq 0 ,$ (3) R is a U.F.D. with a unique (up to associates) irreducible element t, ( 4) R is a Noetherian integral domain that is also a local ring whose unique maximal ideal is nonzero and principal, (5) R is a Noetherian, integrally closed, integral domain that is also a local ring of Krull dimension 1 i.e., R has a unique nonzero prime ideal: Spec $R = { 0 , M }$
- **dependencies:** —


- **kind:** Corollary 8
- **source:** §16.2; printed pp. 755–763; extraction line 26721
- **statement/data:** If R is any Noetherian, integrally closed, integral domain and P is a minimal nonzero prime ideal of R, then the localization $R _ { P }$ of R at P is a Discrete Valuation Ring.
- **dependencies:** —


- **kind:** Named example
- **source:** §16.2; printed pp. 755–763; extraction line 26735
- **statement/data:** The p-adic integers Z_p form a DVR with uniformizer p; their fraction field is the p-adic field Q_p, and every nonzero element is uniquely p^n u with n∈Z and u∈Z_p^×.
- **dependencies:** —


- **kind:** Construction
- **source:** §16.2; printed pp. 755–763; extraction line 26757
- **statement/data:** A discrete valuation ν on K defines an ultrametric d_ν(x,y)=c^{ν(x−y)} (0<c<1); the completion K_ν inherits the valuation.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26787
- **statement/data:** For any integral domain R with fraction field K, a fractional ideal of R is an R-submodule A of K such that $d A \subseteq R$ for some nonzero d $\in R$ (equivalently, a submodule of the form $d ^ { - 1 } I$ for some nonzero d $\in R$ and ideal I of R). The equivalence of these two defintions follows from the observation that d A is an R-submodule (i.e., an ideal) of R. The notion of a fractional ideal in K depends on the ring R. Loosely speaking, a fractional ideal is an ideal of R up to a fixed "denominator" d. The ideals of R are also fractional ideals of R (with denominator $d = 1 )$ ) and are the fractional ideals that are contained in R. For clarity these are occasionally called the integral ideals of R. When R is a Noetherian integral domain, a fractional ideal of R is the same as a finitely generated R-submodule of K (cf. Exercise 6). For any $x \in K$ the (cyclic) R-module $R x = { r x \mid r \in R }$ is called the principal fractional ideal generated by x. If A and B are fractional ideals, their product, AB, is defined to be the set of all finite sums of elements of the form ab where $a \in A$ and $b \in B .$ . If $A = d ^ { - 1 } I$ and $B = ( d ^ { \prime } ) ^ { - 1 } J$ for ideals I, J in R and nonzero d, $d ^ { \prime } \in R ,$ , then $A B = ( d d ^ { \prime } ) ^ { - 1 } I J$ where I J is the usual product ideal. In particular, this shows that the product of two fractiona ideals is a fractional ideal.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26793
- **statement/data:** For x∈K×, the fractional ideal Rx is the principal fractional ideal generated by x.
- **dependencies:** FC01-C16-U016


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26797
- **statement/data:** The fractional ideal A is said to be invertible if there exists a fractional ideal B with $\begin{array} { r } { A B = R , } \end{array}$ , in which case B is called the inverse of A and denoted $A ^ { - 1 }$ If A is an invertible fractional ideal, the fractional ideal B with $A B = R$ is unique: $A B = A C = R$ implies $B = B ( A C ) = ( B A ) C = C$
- **dependencies:** —


- **kind:** Proposition 9
- **source:** §16.2; printed pp. 755–763; extraction line 26801
- **statement/data:** Let R be an integral domain and let A be a fractional ideal of R. (1) If A is a nonzero principal fractional ideal then A is invertible. (2) If A is nonzero then the set $A ^ { \prime } = { x \in K \mid x A \subseteq R }$ is a fractional ideal of R. In general we have $A A ^ { \prime } \subseteq R$ and $\boldsymbol { A } \boldsymbol { A } ^ { \prime } = \boldsymbol { R }$ if and only if A is invertible, in which case $\pmb { A } ^ { - 1 } = \pmb { A } ^ { \prime }$ (3) If A is an invertible fractional ideal of R then A is finitely generated (4) The set of invertible fractional ideals is an abelian group under multiplication with identity R. The set of nonzero principal fractional ideals is a subgroup of the invertible fractional ideals.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26819
- **statement/data:** If R is an integral domain, then the quotient of the group of invertible fractional ideals of R by the subgroup of nonzero principal fractional ideals of R is called the class group of R. The order of the class group of R is called the class number of R. The class group of R is the trivial group and the class number of R is 1 if and only if R is a P.I.D. The class group of R measures how close the ideals of R are to being principal. Whether a fractional ideal A of R is invertible is also related to whether A is projective as an R-module. Recall that an R-module M is projective over R if and only if M is a direct sumand of a free module (Proposition 30, Section 1 0.5). Equivalently, M is projective if and only if there is a free R-module F and R -module homomorphisms $f : F \to M$ and $g : M \to F$ with $f \circ g = 1$ (Proposition 25, Section 1 0.5).
- **dependencies:** —


- **kind:** Proposition 10
- **source:** §16.2; printed pp. 755–763; extraction line 26825
- **statement/data:** Let R be an integral domain with fraction field K and let A be a nonzero fractional ideal of R. Then A is invertible if and only if A is a projective R-module
- **dependencies:** —


- **kind:** Proposition 11
- **source:** §16.2; printed pp. 755–763; extraction line 26851
- **statement/data:** Suppose the integral domain R is a local ring that is not a field. Then R is a Discrete Valuation Ring if and only if every nonzero fractional ideal of R is invertible.
- **dependencies:** —


- **kind:** Proposition 12
- **source:** §16.2; printed pp. 755–763; extraction line 26865
- **statement/data:** Let v be a point on the irreducible affine curve C over k. Then C is nonsingular at v if and only if the local ring $\mathcal { O } _ { v , c }$ is a Discrete Valuation Ring.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.2; printed pp. 755–763; extraction line 26869
- **statement/data:** If v is a nonsingular point on C with coresponding discrete valuation $\nu _ { v }$ defined on k(C), then $\nu _ { v } ( f ) = n$ for $f \in k ( V )$ is the order of zero of f at v (if $n \geq 0 )$ or the order of the pole of f at v (if n < 0). Using the criterion for nonsingularity for points on curves in Proposition 12 we can prove a result first mentioned in Section 15.4:
- **dependencies:** —


- **kind:** Corollary 13
- **source:** §16.2; printed pp. 755–763; extraction line 26873
- **statement/data:** An ireducible affine curve C over an algebraically closed field k is smooth if and only if its coordinate ring k[ C] is integrally closed.
- **dependencies:** —


- **kind:** Definition
- **source:** §16.3; printed pp. 764–775; extraction line 26905
- **statement/data:** A Dedekind Domain is a Noetherian, integrally closed, integral domain of Krull dimension 1 . Equivalently, R is a Dedekind Domain i f R i s a Noetherian, integraly closed, integral domain that is not a field in which every nonzero prime ideal is maximal. The first result shows that Dedekind Domains are a generalization of the class of Principal Ideal Domains. We shall see later (Theorem 22) that there is a structure theorem for finitely generated modules over a Dedekind Domain extending the corresponding result for P.I.D.s proved in Section 1 2. 1 .
- **dependencies:** —


- **kind:** Proposition 14
- **source:** §16.3; printed pp. 764–775; extraction line 26911
- **statement/data:** (1) Every Principal Ideal Domain is a Dedekind Domain (2) The ring of integers in an algebraic number field is a Dedekind Domain
- **dependencies:** —


- **kind:** Theorem 15
- **source:** §16.3; printed pp. 764–775; extraction line 26921
- **statement/data:** Suppose R is an integral domain with fraction field $K \neq R$ . The following are equivalent conditions for R to be a Dedekind Domain: (1) The ring R is Noetherian, integrally closed, and every nonzero prime ideal is maximal. (2) The ring R is Noetherian and for each nonzero prime P of R the localization $R _ { P }$ is a Discrete Valuation Ring. (3) Every nonzero fractional ideal of R in K is invertible. (4) Every nonzero fractional ideal of R in K is a projective R-module. (5) Every nonzero proper ideal I of R can be writen as a finite product of prime ideals: $I = P _ { 1 } P _ { 2 } \dotsm P _ { n }$ (not necessarily distinct). When the condition in (5) holds, the set of primes ${ P _ { 1 } , \ldots , P _ { n } }$ is uniquely determined and so every nonzero proper ideal I of R can be written uniquely (up to order) as a product of powers of prime ideals.
- **dependencies:** —


- **kind:** Corollary 16
- **source:** §16.3; printed pp. 764–775; extraction line 26955
- **statement/data:** If $O _ { K }$ is the ring of integers in an algebraic number field K then every nonzero ideal I in ${ \mathcal { O } } _ { K }$ can be written uniquely as the product of powers of distinct prime ideals: $$ I = P _ {1} ^ {e _ {1}} P _ {2} ^ {e _ {2}} \dots P _ {n} ^ {e _ {n}}, $$ where $P _ { 1 } , \ldots , P _ { n }$ are distinct prime ideals and $e _ { i } \geq 1$ for $i = 1 , \ldots , n$
- **dependencies:** —


- **kind:** Definition
- **source:** §16.3; printed pp. 764–775; extraction line 26967
- **statement/data:** If A and B are ideals in the integral domain R then B is said to divide A (and A is divisible by B) if there is an ideal C in R with $A = B C$ If B divides A then certainly $A \subseteq B$ . If R is a Dedekind Domain, the converse is true: $A \subseteq B$ implies $C = A B ^ { - 1 } \subseteq B B ^ { - 1 } = R$ so C is an ideal in R with $B C = A$
- **dependencies:** —


- **kind:** Construction
- **source:** §16.3; printed pp. 764–775; extraction line 26971
- **statement/data:** For nonzero ideals in a Dedekind domain, gcd(A,B) is the ideal dividing both and divisible by every common ideal divisor; prime-ideal exponents are coordinatewise minima.
- **dependencies:** FC01-C16-U026


- **kind:** Proposition 17
- **source:** §16.3; printed pp. 764–775; extraction line 26973
- **statement/data:** Suppose R is a Dedekind Domain and A, B are two nonzero ideals in R, with prime ideal factorizations $A = P _ { 1 } ^ { e _ { 1 } } \cdots P _ { n } ^ { e _ { n } }$ and $B = P _ { 1 } ^ { f _ { 1 } } \cdot \cdot \cdot P _ { n } ^ { f _ { n } }$ (where $e _ { i } , f _ { i } \ge 0$ for $i = 1 , \ldots , n )$ . Then ( 1) $A \subseteq B$ if and only if B divides A (i.e., "to contain is to divide") if and only if $f _ { i } \leq e _ { i } { \mathrm { ~ f o r ~ } } i = 1 , \ldots , n ,$ (2) $A + B = ( A , B ) = P _ { 1 } ^ { \mathrm { m i n } ( e _ { 1 } , f _ { 1 } ) } \cdot \cdot \cdot P _ { n } ^ { \mathrm { m i n } ( e _ { n } , f _ { n } ) }$ , so in particular A and B are relatively prime, $A + B = R ,$ if and only if they have no prime ideal factors in common.
- **dependencies:** —


- **kind:** Proposition 18 (Chinese Remainder Theorem)
- **source:** §16.3; printed pp. 764–775; extraction line 26981
- **statement/data:** (Chinese Remainder Theorem) Suppose R is a Dedekind Domain, $P _ { 1 } , P _ { 2 } , \ldots , P _ { n }$ are distinct prime ideals in R and $a _ { i } \geq 0$ are integers, $i = 1 , \ldots , n .$ Then $$ R / P _ {1} ^ {a _ {1}} \dots P _ {n} ^ {a _ {n}} \cong R / P _ {1} ^ {a _ {1}} \times R / P _ {2} ^ {a _ {2}} \times \dots \times R / P _ {n} ^ {a _ {n}}. $$ Equivalently, for any elements $r _ { 1 } , r _ { 2 } , \ldots , r _ { n } \in R$ there exists an element $r \in R ,$ , unique up to an element in $P _ { 1 } ^ { a _ { 1 } } \cdots P _ { n } ^ { a _ { n } }$ , with $$ r \equiv r _ {1} \bmod P _ {1} ^ {a _ {1}}, \quad r \equiv r _ {2} \bmod P _ {2} ^ {a _ {2}}, \quad \dots , \quad r \equiv r _ {n} \bmod P _ {n} ^ {a _ {n}}. $$
- **dependencies:** —


- **kind:** Corollary 19
- **source:** §16.3; printed pp. 764–775; extraction line 26995
- **statement/data:** Supose I is an ideal in the Dedekind Domain R. Then (1) there is an ideal J of R relatively prime to I such that the product $I J = ( a )$ is a principal ideal, (2) if I is nonzero then every ideal in the quotient Rl I is principal; equivalently, if $I _ { 1 }$ is an ideal of R containing I then $I _ { 1 } = I + R b$ for some $b \in R ,$ , and (3) every ideal in R can be generated by two elements; in fact if I is nonzero and 0 $\neq a \in I$ then $I = R a + R b$ for some $b \in I$
- **dependencies:** —


- **kind:** Corollary 20
- **source:** §16.3; printed pp. 764–775; extraction line 27013
- **statement/data:** If R is a Dedekind Domain then R is a P.I.D. (i.e., R has class number 1) if and only if R is a U.F.D.
- **dependencies:** —


- **kind:** Proposition 21
- **source:** §16.3; printed pp. 764–775; extraction line 27023
- **statement/data:** Let R be a Dedekind Domain with fraction field K. (1) Suppose I and I are two fractional ideals of R. Then $I \cong J$ as R-modules if and only if I and I difer by a nonzero principal ideal: $\pmb { I } = ( \pmb { a } ) \pmb { J }$ for some $0 \neq a \in K$ (2) More generally, suppose $I _ { 1 } , I _ { 2 } , \ldots , I _ { n }$ and $J _ { 1 } , J _ { 2 } , \ldots , J _ { m }$ are nonzero fractional ideals in the fraction field K of the Dedekind Domain R. Then $$ I _ {1} \oplus I _ {2} \oplus \dots \oplus I _ {n} \cong J _ {1} \oplus J _ {2} \oplus \dots \oplus J _ {m} $$ as R-modules if and only if $n = m$ and the product ideals $I _ { 1 } I _ { 2 } \cdots I _ { n }$ and $J _ { 1 } J _ { 2 } \cdots J _ { n }$ difer by a principal ideal: $$ I _ {1} I _ {2} \dots I _ {n} = (a) J _ {1} J _ {2} \dots J _ {n} $$ for some $0 \neq a \in K .$ (3) In particular, $$ I _ {1} \oplus I _ {2} \oplus \dots \oplus I _ {n} \cong \underbrace {R \oplus \cdots \oplus R} _ {n - 1 \text { factors }} \oplus (I _ {1} I _ {2} \dots I _ {n}) $$ and $R ^ { n } \oplus I \cong R ^ { n }$ ED I if and only if I and I difer by a principal ideal: $\pmb { I } = ( a ) \pmb { J }$ $a \in K .$
- **dependencies:** —


- **kind:** Theorem 22
- **source:** §16.3; printed pp. 764–775; extraction line 27105
- **statement/data:** Suppose M is a finitely generated module over the Dedekind Domain R. Let ${ \pmb n } \ge { \bf 0 }$ denote the rank of M and let Tor(M) be the torsion submodule of M. Then $$ M \cong \underbrace {R \oplus R \oplus \cdots \oplus R \oplus I} _ {n \text { factors }} \oplus \operatorname{Tor} (M) $$ for some ideal I of $R ,$ and $$ \operatorname{Tor} (M) \cong R / P _ {1} ^ {e _ {1}} \times R / P _ {2} ^ {e _ {2}} \times \dots \times R / P _ {s} ^ {e _ {s}} $$ for some ${ \pmb s } \geq { \bf 0 }$ and powers $P _ { i } ^ { e _ { i } } , e _ { 1 } \geq 1$ , of (not necessarily distinct) prime ideals. The ideals $P _ { i } ^ { e _ { i } }$ for $i = 1 , \ldots , s$ are unique and the ideal I is unique up to multiplication by a principal ideal.
- **dependencies:** —


- **kind:** Corollary 23
- **source:** §16.3; printed pp. 764–775; extraction line 27191
- **statement/data:** A finitely generated module over a Dedekind Domain is projective if and only if it is torsion free.
- **dependencies:** —



- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27319
- **statement/data:** Let C be a sequence of abelian group homomorphisms: $$ 0 \longrightarrow C ^ {0} \stackrel {d _ {1}} {\longrightarrow} C ^ {1} \longrightarrow \dots \longrightarrow C ^ {n - 1} \stackrel {d _ {n}} {\longrightarrow} C ^ {n} \stackrel {d _ {n + 1}} {\longrightarrow} \dots .\tag{17.3} $$ (1) The sequence C is called a cochain complex if the composition of any two successive maps is zero: $d _ { n + 1 } \circ d _ { n } = 0$ for all n. (2) If C is a cochain complex, its $n ^ { \mathrm { t h } }$ cohomology group is the quotient group ker $d _ { n + 1 } / \operatorname { i m a g e } d _ { n }$ . and is denoted by $H ^ { n } ( { \cal { C } } )$ There is a completely analogous "dual" version in which the homomorphisms are between groups in decreasing order, in which case the sequence coresponding to (3) is • wnten $\dotsb { \overset { d _ { n + 1 } } { } } C _ { n } { \overset { d _ { n } } { } } \dotsb { \overset { d _ { 1 } } { } } C _ { 0 } \to 0$ Th "f th . f . en 1 e composttlon o any two successtve homomorphisms is zero, the complex is called a chain complex, and its homology groups are defined as $H _ { n } ( C ) = \ker d _ { n } /$ image $d _ { n + 1 }$ · For chain complexes the notation is often chosen so that the indices appear as subscripts and are decreasing, whereas for cochain complexes the indices are superscripts and are increasing. We shall instead use a uniform notation for the maps on both, since it will be clear from the context whether we are dealing with a chain or a cochain complex. …
- **dependencies:** —


- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27335
- **statement/data:** Let $\pmb { \mathcal { A } } = { A ^ { n } }$ and $\pmb { { \cal B } } = { { \pmb { B } } ^ { n } }$ be cochain complexes. A homomorphism of complexes $\alpha : A B$ is a set of homomorphisms $\alpha _ { n } : A ^ { n } \to B ^ { n }$ such that for every n the following diagram commutes: ( 1 7 .4)
- **dependencies:** —


- **kind:** Proposition 1
- **source:** §17.1; printed pp. 777–797; extraction line 27341
- **statement/data:** A homomorphism $\alpha : { \mathcal { A } } B$ of cochain complexes induces group homomorphisms from $H ^ { n } \left( { \cal { A } } \right)$ to $H ^ { n } ( B )$ for $n \geq 0$ on their respective cohomology groups.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27345
- **statement/data:** Let $\mathcal { A } = { A ^ { n } } , B = { B ^ { n } }$ and ${ \mathcal { C } } = { C ^ { n } }$ be cochain complexes. A shor exact sequence of complexes $0 \to A { \overset { \alpha } { \to } } B { \overset { \beta } { \to } } C \to 0$ is a sequence of homomorphisms of complexes such that $0 \to A ^ { n } { \overset { \alpha _ { n } } { \to } } B ^ { n } { \overset { \beta _ { n } } { \to } } C ^ { n } \to 0$ is short exact for every n. One of the main features of cochain complexes is that they lead to long exact sequences in cohomology, which is our first main result:
- **dependencies:** —


- **kind:** Theorem 2 (The Long Exact Sequence in Cohomology)
- **source:** §17.1; printed pp. 777–797; extraction line 27349
- **statement/data:** (The Long Exact Sequence in Cohomology) Let $0 \to A { \overset { \alpha } { \to } } B { \overset { \beta } { \to } } C \to 0$ be a short exact sequence of cochain complexes. Then there is a long exact sequence of cohomology groups: $$ \begin{array}{r l} & 0 \to H ^ {0} (\mathcal {A}) \to H ^ {0} (\mathcal {B}) \to H ^ {0} (\mathcal {C}) \xrightarrow {\delta_ {0}} H ^ {1} (\mathcal {A}) \ & \qquad \to H ^ {1} (\mathcal {B}) \to H ^ {1} (\mathcal {C}) \xrightarrow {\delta_ {1}} H ^ {2} (\mathcal {A}) \to \dots . \end{array}\tag{17.5} $$ where the maps between cohomology groups at each level are those in Proposition 1 . The maps $\delta _ { n }$ are called connecting homomorphisms.
- **dependencies:** FC01-C17-U003


- **kind:** Construction
- **source:** §17.1; printed pp. 777–797; extraction line 27355
- **statement/data:** The long exact sequence in cohomology contains connecting homomorphisms δ_n:H^n(C)→H^{n+1}(A).
- **dependencies:** —


- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27365
- **statement/data:** Let A be any R-module. A projective resolution of A is an exact sequence $$ \dots \longrightarrow P _ {n} \stackrel {d _ {n}} {\longrightarrow} P _ {n - 1} \longrightarrow \dots \stackrel {d _ {1}} {\longrightarrow} P _ {0} \stackrel {\epsilon} {\longrightarrow} A \longrightarrow 0\tag{17.6} $$ such that each $P _ { i }$ is a projective R-module. Every R-module has a projective resolution: Let $P _ { 0 }$ be any free (hence projective) R-module on a set of generators of A and define an R-module homomorphism E from $P _ { 0 }$ onto A by Theorem 6 in Chapter 10. This begins the resolution $\epsilon : { \cal P } _ { 0 } A 0 .$ The smjectivity of E ensures that this sequence is exact. Next let $K _ { 0 } = \ker \epsilon$ and let $P _ { 1 }$ be any free module maping onto the submodule $K _ { 0 }$ of $P _ { 0 } ;$ ; this gives the second stage $P _ { 1 } P _ { 0 } A$ which, by construction, is also exact. We can continue this way, taking at the $n ^ { \mathrm { t h } }$ stage a free R-module $P _ { n + 1 }$ that maps sutjectively onto the submodule ker $\pmb { d } _ { n }$ of $P _ { n } ,$ , obtaining in fact a free resolution of A. One of the reasons that projective modules are used in the resolution of A is that this makes it possible to lift various maps ( cf. the proof of Proposition 4 following, for instance).
- **dependencies:** —


- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27387
- **statement/data:** Let A and D be a R-modules. For any projective resolution of A as in (6) let $d _ { n } : { \mathrm { H o m } } _ { R } ( P _ { n - 1 } , D ) \to { \mathrm { H o m } } _ { R } ( P _ { n } , D )$ for all $n \geq 1$ as in (7). Define $$ \operatorname{Ext} _ {R} ^ {n} (A, D) = \ker d _ {n + 1} / \operatorname{image} d _ {n} $$ where $\mathbf { E x t } _ { R } ^ { 0 } ( A , D ) = \mathbf { k e r } d _ { 1 }$ . The group $\mathbf { E x t } _ { R } ^ { n } ( A , D )$ is called the $n ^ { \mathrm { t h } }$ cohomology group derivedfrom the functor Hom $_ R ( _ , D )$ . When $R = \mathbb { Z }$ the group $\mathbf { E x t } _ { \mathbb { Z } } ^ { n } ( A , D )$ is also denoted simply $\mathbf { E x t } ^ { n } ( A , D )$
- **dependencies:** —


- **kind:** Proposition 3
- **source:** §17.1; printed pp. 777–797; extraction line 27399
- **statement/data:** For any R-module A we have $\mathbf { E x t } _ { R } ^ { 0 } ( A , D ) \cong \mathbf { H o m } _ { R } ( A , D )$
- **dependencies:** —


- **kind:** Proposition 4
- **source:** §17.1; printed pp. 777–797; extraction line 27445
- **statement/data:** Let $f : A A ^ { \prime }$ be any homomorphism of R-modules and take projective resolutions of A and $A ^ { \prime } ,$ , respectively. Then for each $n \geq 0$ there is lift $f _ { n }$ of $f$ such that the following diagram commutes: ( 17.8) where the rows are the projective resolutions of A and $A ^ { \prime } ,$ , respectively.
- **dependencies:** —


- **kind:** Proposition 5
- **source:** §17.1; printed pp. 777–797; extraction line 27463
- **statement/data:** Let $f : A A ^ { \prime }$ be a homomorphism of R -modules and take projective resolutions of A and A' as in Proposition 4. Then for every n there is an induced group homomorphism $\varphi _ { n } : \mathbf { E x t } _ { R } ^ { n } ( A ^ { \prime } , D ) \to \mathbf { E x t } _ { R } ^ { n } ( A , D )$ on the cohomology groups obtained via these resolutions, and the maps $\varphi _ { n }$ depend only on $f ,$ , not on the choice of lifts $f _ { n }$ in Proposition 4.
- **dependencies:** FC01-C17-U010


- **kind:** Theorem 6
- **source:** §17.1; printed pp. 777–797; extraction line 27475
- **statement/data:** The groups $\mathbf { E x t } _ { R } ^ { n } ( A , D )$ depend only on A and D, i.e., they are independent of the choice of projective resolution of A .
- **dependencies:** —


- **kind:** Proposition 7 (Simultaneous Resolution)
- **source:** §17.1; printed pp. 777–797; extraction line 27483
- **statement/data:** (Simultaneous Resolution) Let $0 \to L \to M \to N \to 0$ be a short exact sequence of R-modules, let $L = A$ have a projective resolution as in (6) above, and let N have a similar projective resolution where the projective modules are denoted by ${ \overrightarrow { P } } _ { n }$ · Then there is a resolution of M by the projective modules $P _ { n }$ EB ${ \overline { { P } } } _ { n }$ such that the following diagram commutes: Moreover, the rows and columns of this diagram are exact and the rows are split ( 1 7. 1 1 )
- **dependencies:** —


- **kind:** Theorem 8
- **source:** §17.1; printed pp. 777–797; extraction line 27494
- **statement/data:** Let $0 \to L \to M \to N \to 0$ be a short exact sequence of R-modules. Then there is a long exact sequence of abelian groups $$ \begin{array}{r l} & 0 \to \mathrm{Hom} _ {R} (N, D) \to \mathrm{Hom} _ {R} (M, D) \to \mathrm{Hom} _ {R} (L, D) \xrightarrow {\delta_ {0}} \mathrm{Ext} _ {R} ^ {1} (N, D) \ & \qquad \to \mathrm{Ext} _ {R} ^ {1} (M, D) \to \mathrm{Ext} _ {R} ^ {1} (L, D) \xrightarrow {\delta_ {1}} \mathrm{Ext} _ {R} ^ {2} (N, D) \to \dots \end{array}\tag{17.12} $$ where the maps between groups at the same level n are as in Proposition 5 and the connecting homomorphisms $\delta _ { n }$ are given by Theorem 2.
- **dependencies:** FC01-C17-U011, FC01-C17-U005


- **kind:** Proposition 9
- **source:** §17.1; printed pp. 777–797; extraction line 27512
- **statement/data:** For an R-module $Q$ the following are equivalent: (1) $Q$ is injective, (2) $\mathbf { E x t } _ { R } ^ { 1 } ( A , Q ) = 0$ for all R-modules A, and (3) $\mathbf { E x t } _ { R } ^ { n } ( A , Q ) = 0$ for all R -modules A and all $n \geq 1$
- **dependencies:** —


- **kind:** Convention
- **source:** §17.1; printed pp. 777–797; extraction line 27534
- **statement/data:** Ext_R^n(−,D) and Ext_R^n(D,−) are the right derived functors of the corresponding left-exact Hom functors.
- **dependencies:** FC01-C17-U008


- **kind:** Theorem 10
- **source:** §17.1; printed pp. 777–797; extraction line 27538
- **statement/data:** Let $0 \to L \to M \to N \to 0$ be a short exact sequence of R-modules. Then there is a long exact sequence of abelian groups $$ \begin{array}{c} 0 \to \operatorname{Hom} _ {R} (D, L) \to \operatorname{Hom} _ {R} (D, M) \to \operatorname{Hom} _ {R} (D, N) \xrightarrow {\gamma_ {0}} \operatorname{Ext} _ {R} ^ {1} (D, L) \ \to \operatorname{Ext} _ {R} ^ {1} (D, M) \to \operatorname{Ext} _ {R} ^ {1} (D, N) \xrightarrow {\gamma_ {1}} \operatorname{Ext} _ {R} ^ {2} (D, L) \to \dots . \end{array}\tag{17.14} $$
- **dependencies:** —


- **kind:** Proposition 11
- **source:** §17.1; printed pp. 777–797; extraction line 27554
- **statement/data:** For an R-module P the following are equivalent: (1) P is projective, (2) $\mathbf { E x t } _ { R } ^ { 1 } ( P , B ) = 0$ for all R-modules B, and (3) $\mathbf { E x t } _ { R } ^ { \tilde { n } } ( P , B ) = 0$ for all R-modules B and all $n \geq 1$
- **dependencies:** —


- **kind:** Named comparison
- **source:** §17.1; printed pp. 777–797; extraction line 27588
- **statement/data:** The same Ext_R^n(A,B) groups may be computed from a projective resolution of A or an injective resolution of B.
- **dependencies:** FC01-C17-U008


- **kind:** Theorem 12
- **source:** §17.1; printed pp. 777–797; extraction line 27636
- **statement/data:** For any R-modules N and L there is a bijection between $\mathbf { E x t } _ { R } ^ { 1 } ( N , L )$ and the set of equivalence classes of extensions of N by L. Although we shall not prove this result, in Section 4 we establish a similar bijection between equivalence classes of group extensions of G by A and elements of a certain cohomology group, where G is any finite group and A is any ZG-module.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.1; printed pp. 777–797; extraction line 27674
- **statement/data:** Let D be a right R -module and let B be a left R -module. For any projective resolution of B by left R-modules as above let 1 ® $d _ { n } : D \otimes P _ { n } \to D \otimes P _ { n - 1 }$ for all $n \geq 1$ as in ( 1 5). Then $$ \operatorname{Tor} _ {n} ^ {R} (D, B) = \ker (1 \otimes d _ {n}) / \operatorname{image} (1 \otimes d _ {n + 1}) $$ where $\mathbf { T o r } _ { 0 } ^ { R } ( D , B ) = ( D \otimes P _ { 0 } ) / \operatorname* { i m a g e } ( 1 \otimes d _ { 1 } )$ . The group $\mathrm { T o r } _ { n } ^ { R } ( D , B )$ is called the $n ^ { \mathrm { t h } }$ homology group derived from the functor $D \otimes _ { - }$ . When $R = \mathbb { Z }$ the group $\mathrm { T o r } _ { n } ^ { \mathbb { Z } } ( D , B )$ is also denoted simply ${ \mathrm { T o r } } _ { n } ( D , B )$ . Thus $\mathrm { T o r } _ { n } ^ { R } ( D , B )$ i s the $n ^ { \mathrm { t h } }$ homology group of the chain complex obtained from (15) by removing the term $D \otimes B$ A completely analogous proof to Proposition 3 (but relying on Theorem 39 in Section 1 0.5) implies the following:
- **dependencies:** —


- **kind:** Proposition 13
- **source:** §17.1; printed pp. 777–797; extraction line 27686
- **statement/data:** For any left R -module B we have To ${ \mathfrak { c } } _ { 0 } ^ { R } ( D , B ) \cong D \otimes B$
- **dependencies:** —


- **kind:** Proposition 14
- **source:** §17.1; printed pp. 777–797; extraction line 27712
- **statement/data:** (1) The homology groups $\mathrm { T o r } _ { n } ^ { R } ( D , B )$ are independent of the choice of projective resolution of B, and (2) for every R-module homomorphism $f : B B ^ { \prime } $ there are induced maps $\psi _ { n } : \mathrm { T o r } _ { n } ^ { R } ( D , B ) \to \mathrm { T o r } _ { n } ^ { R } ( D , B ^ { \prime } )$ on homology groups (depending only on $f )$ There is a Long Exact Sequence in Homology analogous to Theorem 2, except that all the arows are reversed, whose proof follows mutatis mutandis from the argument for cohomology. This together with Simultaneous Resolution gives:
- **dependencies:** FC01-C17-U005


- **kind:** Theorem 15
- **source:** §17.1; printed pp. 777–797; extraction line 27720
- **statement/data:** Le $0 \to L \to M \to N \to 0$ be a short exact sequence ofleft R -modules. Then there is a long exact sequence of abelian groups $$ \begin{array}{c} \dots \to \operatorname{Tor} _ {2} ^ {R} (D, N) \xrightarrow {\delta_ {1}} \operatorname{Tor} _ {1} ^ {R} (D, L) \to \operatorname{Tor} _ {1} ^ {R} (D, M) \to \ \operatorname{Tor} _ {1} ^ {R} (D, N) \xrightarrow {\delta_ {0}} D \otimes L \to D \otimes M \to D \otimes N \to 0 \end{array} $$ where the maps between groups at the same level n are as in Proposition 14 (and the maps $\delta _ { n }$ are called connecting homomorphisms). There is a characterization of fiat modules corresponding to Propositions 9 and 1 1 whose proof is very similar and is left as an exercise.
- **dependencies:** FC01-C17-U023


- **kind:** Proposition 16
- **source:** §17.1; printed pp. 777–797; extraction line 27730
- **statement/data:** For a right R-module D the following are equivalent: (1) D is a flat R-module, (2) $\mathrm { T o r } _ { 1 } ^ { R } ( D , B ) = 0$ for all left R-modules B, and (3) $\mathrm { T o r } _ { n } ^ { R } ( D , B ) = 0$ for all left R-modules B and all $n \geq 1$
- **dependencies:** —


- **kind:** Named comparison
- **source:** §17.1; printed pp. 777–797; extraction line 27738
- **statement/data:** Tor_n^R(A,B) may be computed by projectively resolving either variable; it is the left derived functor of tensor product.
- **dependencies:** FC01-C17-U021


- **kind:** Proposition 17
- **source:** §17.1; printed pp. 777–797; extraction line 27772
- **statement/data:** Let A and B be ;z>modules and let $t ( A )$ and t (B) denote their respective torsion submodules. Then $\operatorname { T o r } _ { 1 } ( A , B ) \cong \operatorname { T o r } _ { 1 } ( t ( A ) , t ( B ) )$
- **dependencies:** —


- **kind:** Corollary 18
- **source:** §17.1; printed pp. 777–797; extraction line 27776
- **statement/data:** If A is an abelian group then A is torsion free if and only $\mathrm { i f } \mathrm { T o r } _ { 1 } ( A , B ) = 0$ for every abelian group B (in which case A is fiat as a Z-module).
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28036
- **statement/data:** An abelian group A on which G acts (on the left) as automorphisms is called a G-module. Note that a G-module is the same as an abelian group A and a homomorphism $\varphi : G \to \mathbf { A u t } ( A )$ of G into the group of automorphisms of A . Since an abelian group is the same as a module over $\mathbb { Z } ,$ it is also easy to see that a G-module A is the same as a module over the integral group ring,ZG, of G with coeficients in Z. When G is an infinite group the ring $\pmb { \mathbb { Z } } \pmb { G }$ consists of all the finite formal sums of elements of G with coeficients in $\mathbb { Z } .$ As usual we shall often use multiplicative notation and write ga in place of $_ { g \cdot a }$ for the action of the element $g \in G$ on the element $a \in A$
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28042
- **statement/data:** If A is a G-module, let $A ^ { G } = { a \in A \mid g a = a$ for all $g \in G }$ } be the elements of A fixed by all the elements of $\pmb { G }$
- **dependencies:** —


- **kind:** Lemma 19
- **source:** §17.2; printed pp. 798–813; extraction line 28070
- **statement/data:** Suppose A is a G-modu1e and ${ \bf H o m z } _ { G } ( \mathbb { Z } , A )$ is the group of all ZG-modu1e homomorphisms from $\mathbb { Z }$ (with trivial G-action) to A. Then $A ^ { G } \cong \operatorname { H o m } _ { \mathbb { Z } G } ( \mathbb { Z } , A )$
- **dependencies:** —


- **kind:** Construction
- **source:** §17.2; printed pp. 798–813; extraction line 28074
- **statement/data:** The standard (bar) resolution of the trivial ZG-module Z has F_n=(ZG)^{⊗_Z(n+1)}, augmentation F_0→Z, and d_1(1⊗g)=g−1; it is a free ZG-resolution.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28092
- **statement/data:** If G is a finite group and A is a G-module, define $C ^ { 0 } ( G , A ) = A$ and for $n \geq 1$ define $C ^ { n } ( G , A )$ to be the collection of all maps from $G ^ { n } = G \times \cdots \times G$ (n copies) to A. The elements of $C ^ { n } ( G , A )$ are called n-cochains $( o f G$ with values in A). Each $C ^ { n } ( G , A )$ is an additive abelian group: for $C ^ { 0 } ( G , A ) = A$ given by the group structure on $A ;$ for $n \geq 1$ given by the usual pointwise addition of functions: $( f _ { 1 } + f _ { 2 } ) ( g _ { 1 } , g _ { 2 } , \ldots , g _ { n } ) = f _ { 1 } ( g _ { 1 } , g _ { 2 } , \ldots , g _ { n } ) + f _ { 2 } ( g _ { 1 } , g _ { 2 } , \ldots , g _ { n } )$ . Under the identification of ${ \mathrm { H o m } } _ { \mathbb { Z } G } ( F _ { n } , A )$ with $C ^ { n } ( G , A )$ the cochain maps $d _ { n }$ in (17) can be given very explicitly (cf. also Exercise 3 and the folowing coment):
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28096
- **statement/data:** For ${ n \geq 0 } .$ , define the $n ^ { \mathrm { t h } }$ coboundary homomorphism from $C ^ { n } ( G , A )$ to $C ^ { n + 1 } ( G , A )$ by $$ \begin{array}{l} d _ {n} (f) \left(g _ {1}, \dots , g _ {n + 1}\right) = g _ {1} \cdot f \left(g _ {2}, \dots , g _ {n + 1}\right) \ \quad + \sum_ {i = 1} ^ {n} (- 1) ^ {i} f \left(g _ {1}, \dots , g _ {i - 1}, g _ {i} g _ {i + 1}, g _ {i + 2}, \dots , g _ {n + 1}\right) \ \quad + (- 1) ^ {n + 1} f \left(g _ {1}, \dots , g _ {n}\right) \end{array} \tag {1}\tag{17.18} $$ where the product $g _ { i } g _ { i + 1 }$ occupying the $i ^ { \mathrm { t h } }$ position of f is taken in the group $\pmb { G }$ .
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28106
- **statement/data:** (1) Let $Z ^ { n } ( G , { \cal A } ) = \ker d _ { n } \mathrm { ~ f o r ~ } n \ge 0 .$ . The elements of $Z ^ { n } ( G , A )$ are called $\pmb { n } -$ cocycles. (2) Let $B ^ { n } ( G , A ) = \operatorname { i m a g e } d _ { n - 1 } { \mathrm { ~ f o r } } n \geq 1$ and let $B ^ { 0 } ( G , A ) = 1$ . The elements of $B ^ { n } ( G , A )$ are called n-coboundaries. Since $d _ { n } \circ d _ { n - 1 } = 0$ for $n \geq 1$ we have image $d _ { n - 1 } \subseteq \ker d _ { n } ,$ , so that $B ^ { n } ( G , A )$ is always a subgroup of $Z ^ { n } ( G , A )$
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28114
- **statement/data:** For any G-module A the quotient group $Z ^ { n } ( G , A ) / B ^ { n } ( G , A )$ is called the $n ^ { \mathrm { t h } }$ cohomology group of G with coeficients in A and is denoted by $H ^ { n } ( G , A ) , n \geq 0$ The defintion of the cohomology group $H ^ { n } ( G , A )$ in terms of cochains will be particularly useful in the following two sections when we examine the low dimensional groups $H ^ { 1 } ( G , A )$ and $H ^ { 2 } ( G , A )$ and their application in a variety of settings It should be remembered, however, that $H ^ { n } ( G , A ) \cong \operatorname { E x t } ^ { n } ( \mathbb { Z } , A )$ for all $\pmb { n } \geq \mathbf { 0 }$ . In particular these groups can be computed using any projective resolution of $\mathbb { Z } .$ Examples (1) For $f = a \in C ^ { 0 } ( G , A )$ have $d _ { 0 } ( f ) ( g ) = g \cdot a - a$ and so ker $d _ { 0 }$ is the set {a $\in A \mid g \cdot a = a$ for all $g \in G } , { \mathrm { i . e . , } } Z ^ { 0 } ( G , A ) = A ^ { G }$ and so $$ H ^ {0} (G, A) = A ^ {G}, $$ for any group G and G-module A. (2) Suppose $G = 1$ is the trivial group. Then $G ^ { n } = { ( 1 , 1 , \ldots , 1 ) }$ } is also the trivial group, so $f \in C ^ { n } ( G , A )$ is completely determined by $f ( 1 , 1 , \dots , 1 ) = a \in A$ . Identifying $\pmb { f } = \pmb { a }$ we obtain $C ^ { n } ( G , A ) = A$ for all $n \geq 0$ . …
- **dependencies:** —


- **kind:** Named example
- **source:** §17.2; printed pp. 798–813; extraction line 28144
- **statement/data:** (Cohomology of a Finite Cyclic Group)
- **dependencies:** —


- **kind:** Proposition 20
- **source:** §17.2; printed pp. 798–813; extraction line 28168
- **statement/data:** Suppose m $A = 0$ for some integer $m \geq 1 \left( \mathrm { i . e . } \right.$ ., the e-module A has exponent dividing m as an abelian group). Then $$ m Z ^ {n} (G, A) = m B ^ {n} (G, A) = m H ^ {n} (G, A) = 0 \quad \text { for all } n \geq 0. $$ In particular, if A has exponent p for some prime p then the abelian groups $Z ^ { n } ( G , A )$ $B ^ { n } ( G , A )$ and $H ^ { n } ( G , A )$ have exponent dividing p and so these groups are all vector spaces over the finite field $\mathbb { F } _ { p } = \mathbb { Z } / p \mathbb { Z }$
- **dependencies:** —


- **kind:** Theorem 21 (Long Exact Sequence in Group Cohomology)
- **source:** §17.2; printed pp. 798–813; extraction line 28180
- **statement/data:** (Long Exact Sequence in Group Cohomology) Suppose $$ 0 \longrightarrow A \longrightarrow B \longrightarrow C \longrightarrow 0 $$ is a short exact sequence of G-modules. Then there is a long exact sequence: $$ \begin{array}{l} 0 \longrightarrow A ^ {G} \longrightarrow B ^ {G} \longrightarrow C ^ {G} \stackrel {\delta_ {0}} {\longrightarrow} H ^ {1} (G, A) \longrightarrow H ^ {1} (G, B) \longrightarrow H ^ {1} (G, C) \stackrel {\delta_ {1}} {\longrightarrow} \dots \ \dots \stackrel {\delta_ {n - 1}} {\longrightarrow} H ^ {n} (G, A) \longrightarrow H ^ {n} (G, B) \longrightarrow H ^ {n} (G, C) \stackrel {\delta_ {n}} {\longrightarrow} H ^ {n + 1} (G, A) \longrightarrow \dots \end{array} $$ of abelian groups. Among many other uses of the long exact sequence in Theorem 21 is a technique called dimension shifting which makes it possible to analyze the cohomology group $H ^ { n + 1 } ( G , A )$ of dimension n + 1 for A by instead considering a cohomology group of dimension n for a diferent G-module. The technique is based on finding a G-module almost all of whose cohomology groups are zero. Such modules are given a name:
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28196
- **statement/data:** A G-module M is called cohomologically trivial for G if $H ^ { n } ( G , M ) = 0$ for all $n \geq 1$
- **dependencies:** —


- **kind:** Corollary 22 (Dimension Shifting)
- **source:** §17.2; printed pp. 798–813; extraction line 28198
- **statement/data:** (Dimension Shifting) Suppose $0 \to A \to M \to C \to 0$ i s a short exact sequence of G-modules and that M is cohomologically trivial for G. Then there is an exact sequence $$ 0 \longrightarrow A ^ {G} \longrightarrow M ^ {G} \longrightarrow C ^ {G} \longrightarrow H ^ {1} (G, A) \longrightarrow 0 $$ and $$ H ^ {n + 1} (G, A) \cong H ^ {n} (G, C) \text { for all } n \geq 1. $$
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28226
- **statement/data:** If H is a subgroup of G and A is an H -module, define the induced $G \mathrm { - }$ module $M _ { H } ^ { G } ( A )$ to be ${ \bf H o m } _ { \mathbb { Z } H } ( \mathbb { Z } G , A )$ In other words, $M _ { H } ^ { G } ( A )$ is the set of maps f from G to A satisfying $f ( h x ) = h f ( x )$ for every $x \in G$ and $h \in H$ The action of an element $g \in G$ on $f \in M _ { H } ^ { G } ( A )$ is given by $( g \cdot f ) ( x ) = f ( x g )$ ) for $x \in G$ ( cf. Exercise 1 0 in Section 1 0.5).
- **dependencies:** —


- **kind:** Proposition 23 (Shapiro 's Lemma)
- **source:** §17.2; printed pp. 798–813; extraction line 28256
- **statement/data:** (Shapiro 's Lemma) For any subgroup H of $G$ and any H-module A we have $H ^ { n } ( G , M _ { H } ^ { G } ( A ) ) \cong H ^ { n } ( H , A )$ for $n \geq 0 .$
- **dependencies:** —


- **kind:** Corollary 24
- **source:** §17.2; printed pp. 798–813; extraction line 28266
- **statement/data:** For any G-module A the module $M _ { 1 } ^ { G } ( A )$ is cohomologically trivial for $G , { \mathrm { i . e . , } } H ^ { n } ( G , M _ { 1 } ^ { G } ( A ) ) = 0$ for all $n \geq 1$
- **dependencies:** —


- **kind:** Corollary 25
- **source:** §17.2; printed pp. 798–813; extraction line 28278
- **statement/data:** For any G-module A we have $H ^ { n + 1 } ( G , A ) \cong H ^ { n } ( G , M _ { 1 } ^ { G } ( A ) / A )$ for all $n \geq 1$ We next consider several important maps relating various cohomology groups Some applications of the use of these homomorphisms appear in the following two sections.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28284
- **statement/data:** Suppose A is a G-module and $A ^ { \prime }$ is a $G ^ { \prime } { \mathrm { - m o d u l e } } .$ . The group homomorphisms $\varphi : G ^ { \prime } \to G$ and $\psi : A \to A ^ { \prime }$ are said to be compatible if $\psi$ is a G' -module homomorphism when A is made into a $\pmb { G } ^ { \prime }$ -module by means of $\varphi , \mathrm { i . e . , }$ if $\psi ( \varphi ( g ^ { \prime } ) a ) = g ^ { \prime } \psi ( a )$ for all $g ^ { \prime } \in G ^ { \prime }$ and $a \in A$ The point of compatible homomorphisms is that they induce group homomorphisms on associated cohomology groups, as follows. If $\varphi : G ^ { \prime } \to G$ and $\psi : A \to A ^ { \prime }$ are homomorphisms, then $\varphi$ induces a homomorphism $\varphi ^ { n } : ( G ^ { \prime } ) ^ { n } \to G ^ { n }$ , and so a homomorphism from $C ^ { n } ( G , A )$ to $C ^ { n } ( G ^ { \prime } , A )$ that maps f to $f \circ \varphi ^ { n }$ . The map 1/ induces a homomorphism from $C ^ { n } ( G ^ { \prime } , A )$ to $C ^ { n } ( G ^ { \prime } , A ^ { \prime } )$ that maps f to $\psi \circ f$ . Taken together we obtain an induced homomorphism $$ \begin{array}{c} \lambda_ {n}: C ^ {n} (G, A) \longrightarrow C ^ {n} (G ^ {\prime}, A ^ {\prime}) \ f \longmapsto \psi \circ f \circ \varphi^ {n}. \end{array} $$ If in addition q; and $\psi$ are compatible homomorphisms, then it is easy to check that the induced maps $\lambda _ { n }$ comute with the coboundary operator: $$ \lambda_ {n + 1} \circ d _ {n} = d _ {n} \circ \lambda_ {n} $$ for all $\textbf { \em n } \geq \textbf { 0 }$ . …
- **dependencies:** —


- **kind:** Construction
- **source:** §17.2; printed pp. 798–813; extraction line 28320
- **statement/data:** For H≤G and a G-module A, restriction is Res:H^n(G,A)→H^n(H,A), induced by H↪G and id_A.
- **dependencies:** FC01-C17-U046


- **kind:** Construction
- **source:** §17.2; printed pp. 798–813; extraction line 28328
- **statement/data:** For H◁G, inflation is Inf:H^n(G/H,A^H)→H^n(G,A), induced by G→G/H and A^H↪A.
- **dependencies:** FC01-C17-U046


- **kind:** Construction
- **source:** §17.2; printed pp. 798–813; extraction line 28340
- **statement/data:** Corestriction/transfer in cohomology is induced by the coset-sum module map and satisfies Cor∘Res=[G:H].
- **dependencies:** FC01-C17-U046


- **kind:** Proposition 26
- **source:** §17.2; printed pp. 798–813; extraction line 28360
- **statement/data:** Suppose H is a subgroup of G of index m. Then Cor $\circ \mathbf { R e s } = m ,$ , i.e., if e is a cohomology class in $H ^ { n } ( G , A )$ for some G-module A, then $$ \operatorname{Cor} (\operatorname{Res} (c)) = m c \in H ^ {n} (G, A) \quad \text { for all } n \geq 0. $$
- **dependencies:** —


- **kind:** Corollary 27
- **source:** §17.2; printed pp. 798–813; extraction line 28374
- **statement/data:** Suppose the finite group G has order m. Then m $H ^ { n } ( G , A ) = 0$ for all $n \geq 1$ and any G-module A.
- **dependencies:** —


- **kind:** Corollary 28
- **source:** §17.2; printed pp. 798–813; extraction line 28378
- **statement/data:** If G is a finite group then $H ^ { n } ( G , A )$ is a torsion abelian group for all $n \geq 1$ and all G-modules A.
- **dependencies:** —


- **kind:** Corollary 29
- **source:** §17.2; printed pp. 798–813; extraction line 28382
- **statement/data:** Suppose G is a finite group whose order is relatively prime to the exponent of the G-module A. Then $H ^ { n } ( G , A ) = 0$ for all $n \geq 1$ . In particular, if A is a finite abelian group with $( | G | , | A | ) = 1$ then $H ^ { n } ( G , A ) = 0$ for all $n \geq 1$
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28400
- **statement/data:** If G is a profinite group then a discrete G-module A is a G-module with the discrete topology such that the action of $\pmb { G }$ on A is continuous, i.e., the map $G \times A \to A$ mapping $( g , a )$ to ${ \pmb g } \cdot { \pmb a }$ is continuous. Since A is given the discrete topology, every subset of A is open, and in particular every element $a \in A$ is open. The continuity of the action of $\pmb { G }$ on is then equivalent to the statement that the stabilizer $G _ { \alpha }$ of $^ { a }$ in $\pmb { G }$ is an open subgroup of $G ,$ hence is of finite index since G is compact (cf. Exercise 22). This in tum is equivalent to the statement that $A = \cup A ^ { H }$ where the union is over the open subgroups H of $\pmb { G }$ Some care must be taken in defining the cohomology groups $H ^ { n } ( G , A )$ of a profinite group G acting on a discrete G-module A since there are not enough projectives in this category. For example, when $\pmb { G }$ is infinite, the free G-module ZG is not a discrete G-module ( G does not act continuously, cf. Exercise 25). Nevertheless, the explicit description of $H ^ { n } ( G , A )$ given in this section (occasionally referred to as the discrete cohomology groups) can be easily modified - it is only necessary to require the cochains $C ^ { n } ( G , A )$ to be continuous maps from $G ^ { n }$ to A. The definition of the coboundary maps $d _ { n }$ in equation (18) is precisely the same, as is the definition of the groups of cocycles, coboundaries, and the coresponding cohomology groups. …
- **dependencies:** —


- **kind:** Definition
- **source:** §17.2; printed pp. 798–813; extraction line 28406
- **statement/data:** If G is a profinite group and A is a discrete G-module, the cohomology groups $H ^ { n } ( G , A )$ computed using continuous cochains are called the profinite or continuous cohomology groups. When $G \doteq \operatorname { G a l } ( K / F )$ is the Galois group of a field extension $K / F$ then the Galois cohomology groups $H ^ { n } ( G , A )$ will always mean the cohomology groups computed using continuous cochains. When G is a finite group, every G-module is a discrete G-module so the discrete and continuous cohomology groups of G are the same. When G is infinite, this need not be the case as shown by the example mentioned previously of the free G-module $\mathbb { Z } G$ when $\pmb { G }$ is an infinite profinite group. All the major results in this section remain valid for the continuous cohomology ' groups when "G-module" is replaced by "discrete G-module" and "subgroup" is replaced by "closed subgroup." For example, the Long Exact Sequence in Group Cohomology remains true as stated, the restriction homomorphism requires the subgroup H of $\pmb { G }$ to be a closed subgroup (so that the restriction of a continuous map on $G ^ { n }$ to $H ^ { n }$ remains continuous), Proposition 26 requires H to be closed, etc.
- **dependencies:** FC01-C17-U050


- **kind:** Definition
- **source:** §17.3; printed pp. 814–823; extraction line 28638
- **statement/data:** A 1-coboundary is a principal crossed homomorphism; hence H^1(G,A) is crossed homomorphisms modulo principal crossed homomorphisms.
- **dependencies:** FC01-C17-U035


- **kind:** Named example
- **source:** §17.3; printed pp. 814–823; extraction line 28640
- **statement/data:** Hilbert’s Theorem 90 is interpreted cohomologically as H^1(G,K×)=0 for a finite Galois extension K/F with group G.
- **dependencies:** —


- **kind:** Proposition 30
- **source:** §17.3; printed pp. 814–823; extraction line 28666
- **statement/data:** If A is a G-module on which G acts trivially then $H ^ { 1 } ( G , A ) =$ Hom(G, A), the group of all group homomorphisms from G to $H$ If G is a profinite group, then the same result holds for the continuous cohomology group $H ^ { 1 } ( G , A )$ provided one takes the group of continuous homomorphisms from G into A .
- **dependencies:** —


- **kind:** Named example
- **source:** §17.3; printed pp. 814–823; extraction line 28700
- **statement/data:** Kummer theory is reformulated in group-cohomological terms using roots of unity and power classes.
- **dependencies:** —


- **kind:** Named example
- **source:** §17.3; printed pp. 814–823; extraction line 28738
- **statement/data:** The transfer homomorphism is compared with cohomological corestriction.
- **dependencies:** —


- **kind:** Convention
- **source:** §17.3; printed pp. 814–823; extraction line 28808
- **statement/data:** The notation (a/p) denotes the Legendre symbol, also called the quadratic-residue symbol.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.3; printed pp. 814–823; extraction line 28824
- **statement/data:** Let X be any group and let Y be a normal subgroup of X. The stability group of the series $1 \leq Y \leq X$ is the group of all automorphisms of X that map Y to itself and act as the identity on both of the factors Y and $X / Y , \mathrm { i . e . }$ $$ \begin{array}{r l} \operatorname{Stab} (1 \trianglelefteq Y \trianglelefteq X) & = {\sigma \in \operatorname{Aut} (X) \mid \sigma (y) = y \text { for all } y \in Y, \ & \quad \text { and } \sigma (x) \equiv x \bmod Y \text { for all } x \in X }. \end{array} $$ In the special case where Y is an abelian normal subgroup of X, conjugation by elements of Y induce (inner) automorphisms of X that stabilze the series $1 \leq Y \leq X$ and in this case $Y / C _ { Y } ( X )$ is isomorphic to a subgroup of Stab $( 1 \leq Y \leq X )$ (where $C _ { Y } ( X )$ is the elements of Y in the center of X).
- **dependencies:** —


- **kind:** Proposition 31
- **source:** §17.3; printed pp. 814–823; extraction line 28832
- **statement/data:** Let A be a G-module and let E be the semidirect product $\pmb { A } \rtimes \pmb { G }$ . For each cocycle $f \in Z ^ { 1 } ( G , A )$ define $\sigma _ { f } : E \to E$ by $$ \sigma_ {f} ((a, g)) = (a + f (g), g). $$ Then the map $f \sigma _ { f }$ is a group isomorphism from $Z ^ { 1 } ( G , A )$ onto $\mathbf { S t a b } ( 1 \leq A \leq E )$ Under this isomorphism the subgroup $B ^ { 1 } ( G , A )$ of coboundaries maps onto the sub group $A / C _ { A } ( E )$ of the stability group.
- **dependencies:** —


- **kind:** Corollary 32
- **source:** §17.3; printed pp. 814–823; extraction line 28852
- **statement/data:** In the notation of Proposition 3 1 let $\varphi _ { \alpha }$ denote the automorphism of E given by conjugation by a for any $a \in A$ . Then the cocycles $f _ { 1 }$ and $f _ { 2 }$ are in the same cohomology class in ${ \dot { H ^ { 1 } } } ( G , A )$ if and only if $\sigma _ { f _ { 1 } } = \varphi _ { a } \circ \sigma _ { f _ { 2 } }$ ' for some $a \in A$ The proposition and corollary show that 1-cocycles may be computed by finding automorphisms of E that stabilize the series $1 \leq A \leq E ,$ , and vice versa. The first cohomology group is then given by taking these automorphisms modulo inner auto morphisms, i.e., is the group of "outer stability automorphisms" of this series.
- **dependencies:** FC01-C17-U009


- **kind:** Proposition 33
- **source:** §17.3; printed pp. 814–823; extraction line 28862
- **statement/data:** Let A be a G-module and let E be the semidirect product $A \rtimes G$ . For each 1 -cocycle f let $$ G _ {f} = {(f (g), g) \mid g \in G }. $$ Then $G _ { f }$ is a subgroup complement to A in E. The map $f \mapsto G _ { f }$ is a bijection from $Z ^ { 1 } ( G , { \cal A } )$ to the set of complements to A in E. Two complements are conjugate in E if and only if their coresponding 1-cocycles are in the same cohomology class in $H ^ { 1 } ( G , A )$ , so there is a bijection between ${ \dot { H } } ^ { 1 } ( G , A )$ and the set of £-conjugacy classes of complements to A.
- **dependencies:** —


- **kind:** Corollary 34
- **source:** §17.3; printed pp. 814–823; extraction line 28888
- **statement/data:** Under the notation of Proposition 33, all complements to A are conjugate in E if and only if $H ^ { 1 } ( G , A ) = 0$
- **dependencies:** FC01-C17-U065


- **kind:** Corollary 35
- **source:** §17.3; printed pp. 814–823; extraction line 28890
- **statement/data:** If A is a finite abelian group whose order is relatively prime to I G I then all complements to A in any semidirect product $E = A \rtimes G$ are conjugate in E.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29024
- **statement/data:** A map $\mu : G \to E$ with $\pi \circ \mu ( g ) = g$ and $\pmb { \mu } ( 1 ) = \mathbf { 0 } ,$ , i.e., so that for each $g \in G , \mu ( g )$ is a representative of the coset $_ { A g }$ of E and the identity of E (which is the zero of A) represents the identity coset, is called a normalized section of $\pi$ . Fix a section $\pmb { \mu }$ of $\pi$ in (28). Each element of E may be written uniquely in the form $\mathbf { \boldsymbol { a } } \mu ( \mathbf { \boldsymbol { g } } )$ , where $a \in A$ and $g \in G$ . For $g , h \in G$ the product $\mu ( g ) \mu ( h )$ in $E$ lies in the coset $A g h ,$ so there is a unique element $f ( g , h )$ in A such tha $$ \mu (g) \mu (h) = f (g, h) \mu (g h) \quad \text { for all } g, h \in G.\tag{17.30} $$ If in addition $\pmb { \mu }$ is normalized at the identity we also have $$ f (g, 1) = 0 = f (1, g) \quad \text { for all } g \in G.\tag{17.31} $$
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29038
- **statement/data:** The function $f$ defined by equation (30) is called the factor set for the extension E associated to the section $\pmb { \mu }$ . If $f$ also satisfies (3 1 ) then $f$ is called a normalized factor set.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29110
- **statement/data:** A 2-cocycle f such that $f ( g , 1 ) = 0 = f ( 1 , g )$ for all $g \in G$ is called a nonalized 2-cocycle. The construction of $E _ { f }$ is a little simpler when f is a normalized cocycle and for simplicity we indicate the construction in this case (the minor modifications necessary when $f$ is not normalized are indicated in Exercise $^ { 4 ) }$ We first see that any 2-cocycle $f$ lies in the same cohomology class as a normalized 2-cocycle. Let $d _ { 1 } f _ { 1 }$ be the 2-coboundary of the constant function $f _ { 1 }$ on $\pmb { G }$ whose value is $f ( 1 , 1 )$ . Then $f ( 1 , 1 ) = d _ { 1 } f _ { 1 } ( 1 , 1 )$ , and one easily checks from the 2-cocycle condition that $f - d _ { 1 } f _ { 1 }$ is normalized. We may therefore assume that our cohomology class in $H ^ { 2 } ( G , A )$ is represented by the normalized 2-cocycle $f .$ Let $E _ { f }$ be the set $A \times G ,$ , and define a binary operation on $E _ { f }$ by $$ (a _ {1}, g) (a _ {2}, h) = (a _ {1} + g \cdot a _ {2} + f (g, h), g h)\tag{17.34} $$ where, as usual, $g \cdot a _ { 2 }$ denotes the module action of $\pmb { G }$ on A. It is straightforward to check that the group axioms hold: Since $f$ is normalized, the identity element is (0, 1 ) and inverses are given by $$ (a, g) ^ {- 1} = (- g ^ {- 1} \cdot a - f (g ^ {- 1}, g), g ^ {- 1}).\tag{17.35} $$ The cocycle condition implies the associative law by calculations similar to (32) and (33) earlier - the details are left as exercises. …
- **dependencies:** —


- **kind:** Theorem 36
- **source:** §17.4; printed pp. 824–839; extraction line 29162
- **statement/data:** Let A be a G-mod;Jle. Then (1) A function $f : G \times G \to A$ is a normalized factor set of some extension E of G by A (with conjugation given by the G-module action on $A )$ if and only if $f$ is a normalized 2-cocycle in $Z ^ { 2 } ( { \dot { G } } , A )$ (2) There is a bijection between the equivalence classes of extensions E as in ( 1 ) and the cohomology classes in $H ^ { 2 } ( G , A )$ . The bijection takes an extension E into the class of a normalized factor set $f$ for E associated to any normalized section $\pmb { \mu }$ of $G$ into $\mathbf { { \mathit { E } } , }$ and takes a cohomology class $\pmb { c }$ in $H ^ { 2 } ( G , A )$ to the extension $E _ { f }$ defined by the extension (37) for any normalized cocycle $f$ in the class c. (3) Under the bijection in (2), split extensions correspond to the trivial cohomology class.
- **dependencies:** —


- **kind:** Corollary 37
- **source:** §17.4; printed pp. 824–839; extraction line 29170
- **statement/data:** Every extension of G by the abelian group A splits if and only if $H ^ { 2 } ( G , A ) = 0$
- **dependencies:** —


- **kind:** Corollary 38
- **source:** §17.4; printed pp. 824–839; extraction line 29172
- **statement/data:** If A is a finite abelian group and $( | A | , | G | ) = 1$ then every extension of G by A splits.
- **dependencies:** —


- **kind:** Theorem 39 (Schur's Theorem)
- **source:** §17.4; printed pp. 824–839; extraction line 29178
- **statement/data:** (Schur's Theorem) If E is any finite group containing a normal subgroup N whose order and index are relatively prime, then N has a complement in E.
- **dependencies:** —


- **kind:** Named example
- **source:** §17.4; printed pp. 824–839; extraction line 29200
- **statement/data:** Groups of order 8 are compared via H^2(C_2×C_2,Z/2Z) and the corresponding extension classes.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29288
- **statement/data:** A n F -algebra A is said to be simple i f A contains no nontrivial proper (two sided) ideals. A central simple F -algebra A is a simple F -algebra whose center is F . Among the easiest central simple F-algebras are the matrix algebras $M _ { n } ( F )$ of matrices with coeficients in F. If $K / F$ is a finite Galois extension of fields with Galois group $G = \operatorname { G a l } ( K / F )$ then we can use the normalized 2-cocycles in $Z ^ { 2 } ( G , K ^ { \times } )$ to construct certain central simple K -algebras. The construction of these algebras from 2-cocycles and their classification in terms of $H ^ { 2 } ( G , K ^ { \times } )$ (cf. Theorem 42 below) are important applications of cohomological methods in number theory. Their construction in the case when G is cyclic was one of the precursors leading to the development of abstract cohomology. Suppose $f = { a _ { \sigma , \tau } } _ { \sigma , \tau \in G }$ is a normalized 2-cocycle in $Z ^ { 2 } ( G , K ^ { \times } )$ . Let $B _ { f }$ be the vector space over L having basis $\pmb { u } _ { \sigma }$ for $\sigma \in G$ $$ B _ {f} = \left{\sum_ {\sigma \in G} \alpha_ {\sigma} u _ {\sigma} | \alpha_ {\sigma} \in K \right}.\tag{17.39} $$ Define a multiplication on $B _ { f }$ by $$ u _ {\sigma} \alpha = \sigma (\alpha) u _ {\sigma} \qquad u _ {\sigma} u _ {\tau} = a _ {\sigma , \tau} u _ {\sigma \tau}\tag{17.40} $$ for $\alpha \in L$ and $\sigma , \tau \in G$ . …
- **dependencies:** —


- **kind:** Proposition 40
- **source:** §17.4; printed pp. 824–839; extraction line 29316
- **statement/data:** The F -algebra $B _ { f }$ with K -vector space basis $u _ { \sigma }$ in (39) and multiplication defined by (40) is a central simple F -algebra.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29328
- **statement/data:** The central simple F-algebra $B _ { f }$ defined by (39) and (40) is called the crossed product algebra for the factor set ${ a _ { \sigma , \tau } }$ If $f ^ { \prime } = a _ { \sigma , \tau } ^ { \prime }$ is a normalized cocycle in the same cohomology class in $H ^ { 2 } ( G , K ^ { \times } )$ a s ${ a } _ { \sigma , \mathrm { ~ } }$ r then there are elements $b _ { \sigma } \in K ^ { \times }$ with $$ a _ {\sigma , \tau} ^ {\prime} = a _ {\sigma , \tau} (\sigma (b _ {\tau}) b _ {\sigma \tau} ^ {- 1} b _ {\sigma}) $$ (the multiplicative form of the coboundary condition (27)). If $B _ { f ^ { \prime } }$ is the F-algebra with K -basis $v _ { \sigma }$ defined from this cocycle as in (39) and ( 40), then the K -vector space homomorphism $\varphi$ defined by mapping ${ \pmb u } _ { \sigma } ^ { \prime }$ to ${ b } _ { \sigma } \boldsymbol { u } _ { \sigma }$ satisfies $$ \begin{array}{r} \varphi (u _ {\sigma} ^ {\prime} u _ {\tau} ^ {\prime}) = \varphi (a _ {\sigma , \tau} ^ {\prime} u _ {\sigma \tau} ^ {\prime}) = a _ {\sigma , \tau} ^ {\prime} b _ {\sigma \tau} u _ {\sigma \tau} = b _ {\sigma} \sigma (b _ {\tau}) u _ {\sigma} u _ {\tau} \ = (b _ {\sigma} u _ {\sigma}) (b _ {\tau} u _ {\tau}) = \varphi (u _ {\sigma} ^ {\prime}) \varphi (u _ {\tau} ^ {\prime}). \end{array} $$ It follows that $\varphi$ i s an F -algebra isomorphism from $B _ { f ^ { \prime } }$ to $B _ { f }$ .
- **dependencies:** —


- **kind:** Proposition 41
- **source:** §17.4; printed pp. 824–839; extraction line 29346
- **statement/data:** The crossed product algeb for the trivial cohomology class in $H ^ { 2 } ( G , K ^ { \times } )$ is isomorphic to the matrix algebra $M _ { n } ( F )$ where $n = \left[ K : F \right]$
- **dependencies:** —


- **kind:** Construction
- **source:** §17.4; printed pp. 824–839; extraction line 29374
- **statement/data:** For F⊆B⊆A, the centralizer B^c is the subalgebra commuting with B; B^op is the opposite algebra with multiplication reversed.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29388
- **statement/data:** If A is a central simple F -algebra then a field L containing F is said to split A if $A \otimes _ { F } L \cong M _ { m } ( L )$ for some $m \geq 1$ It follows from (II) that every maximal comutative subalgebra of $\pmb { \triangle }$ is a field E with $E = E ^ { c } = { E ^ { o p p } } ; { \mathrm { i f } } [ E : F ] = m$ we obtain dim $_ { F } \Delta = m ^ { 2 }$ . Applying (II) to $A = \Delta$ and $B = E$ we also see that $\Delta \otimes _ { F } E \cong M _ { m } ( E )$ ) . It can also be shown that a maximal subfield E of the central simple F -algebra A also satisfies $E = E ^ { c } = E ^ { o p p }$ and so again by (II) it follows that $A \otimes _ { F } E \cong M _ { r } ( E ) ( r ^ { 2 } = \dim _ { F } A )$ If $A = M _ { r } ( \Delta )$ then the field L splits A if and only if L splits $\Delta .$ , as follows. If $\Delta \otimes _ { F } L \cong M _ { n } ( L )$ then $$ A \otimes_ {F} L \cong M _ {r} (\Delta) \otimes_ {F} L \cong M _ {r} (\Delta \otimes_ {F} L) \cong M _ {r} (M _ {n} (L)) \cong M _ {r n} (L). $$ Conversely if $A \otimes _ { F } L \cong M _ { n } ( L )$ then $$ M _ {n} (L) \cong M _ {r} (\Delta) \otimes_ {F} L \cong M _ {r} (\Delta \otimes_ {F} L). $$ By (Il) and (III), $\Delta \otimes _ { F } L \cong M _ { s } ( \Delta ^ { \prime } )$ for some division ring $\Delta ^ { \prime } .$ . …
- **dependencies:** —


- **kind:** Convention
- **source:** §17.4; printed pp. 824–839; extraction line 29420
- **statement/data:** By Wedderburn structure a central simple F-algebra is M_r(Δ) for a division algebra Δ unique up to F-isomorphism; Δ is its division-ring part.
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29422
- **statement/data:** Two central simple F-algebras A and B are similar if $A \cong M _ { r } ( \Delta )$ and $B \cong M _ { s } ( \Delta )$ for the same division ring f".., i.e., if A and B have the same division ring parts. Let [A] denote the similarity class of A . By (II), if A and B are central simple F-algebras then $\boldsymbol { A } \otimes _ { \boldsymbol { F } } \boldsymbol { B }$ is again a central simple F -algebra, so we may define a multiplication on similarity classes by $[ A ] [ B ] = [ A \otimes _ { F } B ]$ . The class $[ F ]$ is an identity for this multiplication and associativity of the tensor product shows that the multiplication is associative. By (lb) applied with $B = A$ (so then $B ^ { c } = F$ since A is central) we have $[ A ] [ A ^ { o p p } ] = [ F ]$ , so inverses exist with this multiplication
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29426
- **statement/data:** The group of similarity classes of central simple F -algebras with multi plication $[ A ] [ B ] = \left[ A \otimes _ { F } B \right]$ is called the Brauer group of F and is denoted $B r ( F )$ ) . If L is any extension field of F then by (II) the algebra $A \otimes _ { F } L$ is a central simple $L \mathbf { - a l g e b r a . }$ . It is easy to check that the map $[ A ] [ A \otimes _ { F } L ]$ is a wel defined homomorphism from $B r ( F )$ to $B r ( L )$ . The kernel of this homomorphism consists of the classes of the algebras A with $A \otimes _ { F } L \cong M _ { m } ( L )$ for some $m \geq 1 , \mathrm { i . e . }$ ., the algebras A that are split by L .
- **dependencies:** —


- **kind:** Definition
- **source:** §17.4; printed pp. 824–839; extraction line 29430
- **statement/data:** If $L / F$ is a field extension then the relative Brauer group $B r ( L / F )$ is the group of similarity classes of central simple F -algebras that are split by L. Equivalently, $B r ( L / F )$ is the kernel of the homomorphism $[ A ] [ A \otimes _ { F } L ]$ from $B r ( F )$ to $B r ( L )$ ) . The following theorem summarizes some major results in this area and shows the fundamental connection between Brauer groups and the crossed product algebras constructed above.
- **dependencies:** —


- **kind:** Theorem 42
- **source:** §17.4; printed pp. 824–839; extraction line 29434
- **statement/data:** Suppose $K / F$ is a Galois extension of degree n with $G = { \mathrm { G a l } } ( K / F )$ (1) The central simple F -algebra A with dim $\scriptstyle { F A = n ^ { 2 } }$ is split b y K i f and only i $A \otimes _ { F } K \cong M _ { n } ( K )$ if and only if A is isomorphic to a crossed product algebra $B _ { f }$ as in (39) and ( 40). (2) There is a bijection between the F -isomorphism classes of central simple $F \mathrm { - }$ algebras A with $A \otimes _ { F } K \cong M _ { n } ( K )$ and the elements of $H ^ { 2 } ( G , K ^ { \times } )$ . Under this bijection the class $c \in H ^ { 2 } ( G , K ^ { \times } )$ containing the normalized cocycle $f$ corresponds to the isomorphism class of the crossed product algebra $B _ { f }$ defined in (39) and (40), and the trivial cohomology class corresponds to $M _ { n } ( F )$ (3) Every central simple F -algebra of finite dimension over $F$ and split by K is similar to one of dimension $n ^ { 2 }$ split by K . The bijection in (2) also establishes a bijection between $B r ( K / F )$ and $\bar { H ^ { 2 } } ( G , K ^ { \times } )$ which is also an isomorphism of groups. (4) There is a bijection between the collection of F -isomorphism classes of central simple division algebras over F that are split by K and $H ^ { 2 } ( G , K ^ { \times } )$ As previously mentioned, every central simple F -algebra of finite dimension over F can be split by some finite Galois extension of $F .$ , and it follows that $$ B r (F) = \bigcup_ {K} B r (K / F) $$ where the union is over all finite Galois extensions of F. …
- **dependencies:** —



- **kind:** Definition
- **source:** §18.1; printed pp. 840–853; extraction line 29538
- **statement/data:** Let G be a finite group, let F be a field and let V be a vector space over F. (1) A linear representation of G is any homomorphism from G into $G L ( V )$ ) . The degree of the representation is the dimension of V. (2) Let $n \in \mathbb { Z } ^ { + }$ . A matrix representation of G is any homomorphism from G into $G L _ { n } ( F )$ (3) A linear or matrix representation is faithful if it is injective (4) The group ring of G over F is the set of all formal sums of the form $$ \sum_ {g \in G} \alpha_ {g} g, \quad \alpha_ {g} \in F $$ with componentwise addition and multiplication $( \alpha g ) ( \beta h ) = ( \alpha \beta ) ( g h )$ (where and $\beta$ are multiplied in F and gh is the product in G) extended to sums via the distributive law (cf. Section 7.2). Unless we are specifically discussing permutation representations the term "representation" will always mean "linear representation." When we wish to emphasize the field F we shall say F -representation, or representation of G on V over F.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §18.1; printed pp. 840–853; extraction line 29630
- **statement/data:** Representations G→GL(V) over F are equivalent to left FG-module structures on V by g·v=φ(g)v and linear extension to FG.
- **dependencies:** —


- **kind:** Definition
- **source:** §18.1; printed pp. 840–853; extraction line 29658
- **statement/data:** A subspace U≤V is G-invariant/G-stable iff gU⊆U for every g∈G; these are exactly the FG-submodules.
- **dependencies:** FC01-C18-U001


- **kind:** Named example
- **source:** §18.1; printed pp. 840–853; extraction line 29672
- **statement/data:** The regular representation is the left-multiplication action on the basis indexed by G; it is faithful.
- **dependencies:** FC01-C18-U001


- **kind:** Named example
- **source:** §18.1; printed pp. 840–853; extraction line 29742
- **statement/data:** In the natural permutation FS_n-module, the one-dimensional stable subspace of vectors with all coordinates equal affords the trivial representation and is called the trace submodule.
- **dependencies:** —


- **kind:** Construction
- **source:** §18.1; printed pp. 840–853; extraction line 29750
- **statement/data:** The augmentation map on the natural permutation module sends a vector to the sum of its coordinates; its kernel is the augmentation submodule.
- **dependencies:** —


- **kind:** Definition
- **source:** §18.1; printed pp. 840–853; extraction line 29762
- **statement/data:** In FG, the augmentation ideal is the kernel of augmentation and the trace ideal is generated by the sum of all group elements.
- **dependencies:** —


- **kind:** Definition
- **source:** §18.1; printed pp. 840–853; extraction line 29766
- **statement/data:** Two representations of G are equivalent (or similar) if the FG-modules afording them are isomorphic modules. Representations which are not equivalent are called inequivalent. Suppose $\varphi : G \to G L ( V )$ and $\psi : G G L ( W )$ are eq ivalent representations (here V and W must be vector spaces over the same field F). Let $T : V \to W$ be an FG-module isomorphism between them. Since T is, in particular, an F -module isomorphism, T is a vector space isomorphism, so V and W must have the same dimension. Furthermore, for all $g \in G , v \in V$ we have $T ( g \cdot v ) = g \cdot ( T ( v ) )$ , since ${ \pmb T }$ is an isomorphism of F G-modules. By definition of the action of ring elements this means $T ( \varphi ( g ) v ) = \psi ( g ) ( T ( v ) )$ , that is $$ T \circ \varphi (g) = \psi (g) \circ T \quad \text { for all } g \in G. $$ In particular, if we identify V and $W$ as vector spaces, then two representations $\varphi$ and l/t of G on a vector space V are equivalent if and only if there is some $T \in G L ( V )$ such that $T \circ \varphi ( g ) \circ T ^ { - 1 } = \psi ( g )$ for all $g \in G .$ . This $\boldsymbol { \tau }$ is a simultaneous change of basis for all $\varphi ( g ) , g \in G$ In matrix terminology, two representations $\varphi$ and $\psi$ are equivalent if there is a fixed invertible matrix P such that $$ P \varphi (g) P ^ {- 1} = \psi (g) \quad \text { for all } g \in G. …
- **dependencies:** —


- **kind:** Definition
- **source:** §18.1; printed pp. 840–853; extraction line 29786
- **statement/data:** Let R be a ring and let M be a nonzero R-module. (1) The module M is said to be irreducible (or simple) if its only submodules are 0 and $M ;$ otherwise M is called reducible (2) The module M is said to be indecomposable if M cannot be written as $M _ { 1 }$ El1 $M _ { 2 }$ for any nonzero submodules $M _ { 1 }$ and $M _ { 2 } ;$ ; otherwise M is called decomposable (3) The module M is said to be completely reducible if it is a direct sum of irreducible submodules. (4) A representation is called irreducible, reducible, indecomposable, decomposable or completely reducible according to whether the FG-module afording it has the corresponding property. (5) If M is a completely reducible R-module, any direct sumand of M is called a constituent of M (i.e., N is a constituent of M if there is a submodule $N ^ { \prime }$ of M such that $M = N \oplus N ^ { \prime } )$ . An irreducible module is, by definition, both indecomposable and completely reducible. We shall shortly give examples of indecomposable modules that are not ireducible. If $R = F G ,$ an irreducible F G-module V is a nonzero F -vector space with no nontrivial, proper G-invariant subspaces. For example, if dimF V = 1 then V is necessarily irreducible (its only subspaces are 0 and V). Suppose V is a finite dimensional F G-module and V is reducible. Let U be a G-invariant subspace. Form a basis of V by taking a basis of U and enlarging it to a basis of V . …
- **dependencies:** —


- **kind:** Theorem 1 (Maschke 's Theorem)
- **source:** §18.1; printed pp. 840–853; extraction line 29848
- **statement/data:** (Maschke 's Theorem) Let G be a finite group and let F be a field whose characteristic does not divide J G J . If V is any FG-module and U is any submodule of V, then V has a submodule W such that $V = U \oplus W$ (i.e., every submodule is a direct sumand).
- **dependencies:** —


- **kind:** Corollary 2
- **source:** §18.1; printed pp. 840–853; extraction line 29922
- **statement/data:** If G is a finite group and F is a field whose characteristic does not divide $| G |$ , then every finitely generated FG-module is completely reducible (equivalently every F -representation of G of finite degree is completely reducible)
- **dependencies:** —


- **kind:** Corollary 3
- **source:** §18.1; printed pp. 840–853; extraction line 29926
- **statement/data:** Let $\pmb { G }$ be a finite group, let F be a field whose characteristic does not divide $| G |$ and let $\varphi : G \to G L ( V )$ be a representation of $\pmb { G }$ of finite degree. Then there is a basis of V such that for each $g \in G$ the matrix of $\varphi ( g )$ with respect to this basis is block diagonal: $$ \left( \begin{array}{c c c c} \varphi_ {1} (g) & & & \ & \varphi_ {2} (g) & & \ & & \ddots & \ & & & \varphi_ {m} (g) \end{array} \right) $$ where $\varphi _ { i }$ is an irreducible matrix representation of $G , 1 \leq i \leq m$
- **dependencies:** —


- **kind:** Theorem 4 (Wedderburn 's Theorem)
- **source:** §18.2; printed pp. 854–863; extraction line 30028
- **statement/data:** (Wedderburn 's Theorem) Let R be a nonzero ring with l (not necessarily commutative). Then the following are equivalent: (1) every R-module is projective (2) every R-module is injective (3) every R-module is completely reducible (4) the ring R considered as a left R-module is a direct sum: $$ R = L _ {1} \oplus L _ {2} \oplus \dots \oplus L _ {n}, $$ where each $L _ { i }$ is a simple module (i.e., a simple left ideal) with $L _ { i } = R e _ { i }$ , for some $e _ { i } \in R$ with (i) $e _ { i } e _ { j } = \mathbf { 0 } { \mathrm { i f } } i \neq j$ (ii) $e _ { i } ^ { 2 } = e _ { i } { \mathrm { ~ f o r ~ a l l } } i$ (ii) $\begin{array} { r } { \sum _ { i = 1 } ^ { n } e _ { i } = 1 } \end{array}$ (5) as rings, R is isomorphic to a direct product of matrix rings over division rings i . e . , $R = R _ { 1 } \times R _ { 2 } \times \cdot \cdot \cdot \times R _ { r }$ where $R _ { j }$ is a two-sided ideal of R and $R _ { j }$ is isomorphic to the ring of all ${ n } _ { j } \times { n } _ { j }$ matrices with entries in a division ring $\Delta _ { j }$ , $j = 1 , 2 , \dots , r$ . The integer r , the integers $n _ { j }$ , and the division rings $\Delta _ { j }$ (up to isomorphism) are uniquely determined by R.
- **dependencies:** —


- **kind:** Definition
- **source:** §18.2; printed pp. 854–863; extraction line 30054
- **statement/data:** A ring R satisfying any of the (equivalent) properties in Theorem 4 is called semisimple with minimwn condition. Rings R satisfying any of the equivalent conditions of Theorem 4 also satisfy the minimum condition or descending chain condition $\pmb { ( D . C . C ) }$ on left ideals: $$ \text { if } I _ {1} \supseteq I _ {2} \supseteq \dots \text { is a descending chain of left ideals of } R $$ $$ \text { then there is an } N \in \mathbb {Z} ^ {+} \text { such that } I _ {k} = I _ {N} \text { for all } k \geq N $$ (which explains the use of this term in the definition above). The rings we deal with will all have this minimum condition. For example, group algebras always have this property since in any strictly descending chain of ideals the vector space dimensions of the ideals (which are F -subspaces of $F G )$ are strictly decreasing, hence the length of a strictly descending chain is at most the dimension of $F G ( = | G | )$ ). We shall therefore use the term "semisimple" to mean "semisimple with minimum condition." The rings $R _ { i }$ in conclusion (5) of Wedderburn's Theorem are called the Wedderburn components of R and the direct product decomposition of R is called its Wederburn decomposition. Note that Wedderburn's Theorem for comutative rings is a consequence of the classification of Artinian rings in Section 16. 1 . A comutative semisimple ring with minimum condition is an Artinian ring with Jacobson radical equal to zero and so is a direct product of fields (which are its Wedderburn components). …
- **dependencies:** FC01-C18-U013


- **kind:** Convention
- **source:** §18.2; printed pp. 854–863; extraction line 30066
- **statement/data:** In this chapter “semisimple” means semisimple with the minimum condition; the simple factors R_i in Wedderburn’s direct-product decomposition are the Wedderburn components, and the product is the Wedderburn decomposition.
- **dependencies:** —


- **kind:** Corollary 5
- **source:** §18.2; printed pp. 854–863; extraction line 30078
- **statement/data:** If G is a finite group and F is a field whose characteristic does not divide I G I , then the group algebra F G is a semisimple ring. Before obtaining more precise information about how the invariants $n , r , \triangle _ { j }$ , etc. , relate to invariants in group rings F G for certain fields F, we first study the structure of matrix rings (i.e , the rings described in conclusions (4) and (5) of Wedderburn s Theorem). We introduce some terminology which is used extensively in ring theory. Recall that the center of the ring R is the subring of elements commuting with al elements in $R ;$ it will be denoted by $Z ( R )$ (the center will contain I if the ring has a 1).
- **dependencies:** —


- **kind:** Definition
- **source:** §18.2; printed pp. 854–863; extraction line 30082
- **statement/data:** (1) A nonzero element e in a ring R is called an idempotent if $e ^ { 2 } = e$ (2) Idempotents $e _ { 1 }$ and $_ { e _ { 2 } }$ are said to be orthogonal if $e _ { 1 } e _ { 2 } = e _ { 2 } e _ { 1 } = 0 .$ (3) An idempotent e is said to be primitive if it cannot be written as a sum of two (commuting) orthogonal idempotents. (4) The idempotent e is called a primitive central idempotent if $e \in Z ( R )$ and e cannot be written as a sum of two orthogonal idempotents in the ring Z (R). Proposition 6 describes the ideal structure of a matrix ring and Proposition 8 extends these results to direct products of matrix rings.
- **dependencies:** —


- **kind:** Proposition 6
- **source:** §18.2; printed pp. 854–863; extraction line 30094
- **statement/data:** Let $\pmb { \triangle }$ be a division ring, let $n \in \mathbb { Z } ^ { + }$ , let R be the ring of al $n \times n$ matrices with entries from $\pmb { \triangle }$ . and let I be the identity matrix (= the 1 of R). (1) The only two-sided ideals of R are 0 and R. (2) The center of R consists of the scalar matrices a I, where a is in the center of $\pmb { \triangle } \mathbf { i }$ : ${ \cal Z } ( R ) = { \alpha I \mid \alpha \in { \cal Z } ( \Delta ) }$ , and this is a field isomorphic to $Z ( \Delta )$ . In particular, if $\pmb { \triangle }$ is a field, the center of R is the subring of all scalar matrices. The only central idempotent in R is I (in particular, I is primitive). (3) Let $e _ { i }$ be the matrix with a 1 in position i, i and zeros elsewhere. Then $e _ { 1 } , \ldots , e _ { n }$ are orthogonal primitive idempotents and $\textstyle \sum _ { i = 1 } ^ { n } e _ { i } = I$ (4) $L _ { i } = R e _ { i }$ i s the left ideal consisting of arbitrary entries i n column i and zeros in all other columns. $L _ { i }$ is a simple left R-module. Every simple left R-module is isomorphic to $L _ { 1 }$ (in particular, all $L _ { i }$ are isomorphic R-modules) and as a left R-module we have $R = L _ { 1 } \oplus \cdot \cdot \cdot \oplus L _ { n }$
- **dependencies:** —


- **kind:** Lemma 7
- **source:** §18.2; printed pp. 854–863; extraction line 30106
- **statement/data:** Let R be an arbitrary nonzero ring. (1) If M and N are simple R-modules and $\varphi : { \cal M } { \cal N }$ is a nonzero R-module homomorphism, then $\varphi$ is an isomorphism. (2) (Schur's Lemma) If M is a simple R-module, then ${ \bf H o m } _ { R } ( M , M )$ is a division ring.
- **dependencies:** —


- **kind:** Proposition 8
- **source:** §18.2; printed pp. 854–863; extraction line 30154
- **statement/data:** Let $R = R _ { 1 } \times R _ { 2 } \times \cdot \cdot \cdot \times R _ { r }$ , where $R _ { i }$ is the ring of $n _ { i } \times n _ { i }$ matrices over the division ring $\Delta _ { i }$ , for $i = 1 , 2 , \ldots , r$ (1) Identify $R _ { i }$ with the $i ^ { \mathrm { t h } }$ component of the direct product. Let $z _ { i }$ ; be the r-tuple with the identity of $R _ { i }$ in position i and zero in all other positions. Then $R _ { i } = z _ { i } R$ and for any $a \in R _ { i } , z _ { i } a = a$ and $z _ { j } a = 0$ for all $j \neq i$ . The elements $z _ { 1 } , \ldots , z _ { r }$ are all of the primitive central idempotents of R. They are pairwise orthogonal and $\begin{array} { r } { \sum _ { i = 1 } ^ { r } z _ { i } = 1 } \end{array}$ (2) Let N be any left R-module and let $z _ { i } N = { z _ { i } x \mid x \in N } , 1 \leq i \leq r$ . Then $z _ { i } N$ is a left R-submodule of $N$ , each $z _ { i } N$ is an $R _ { i }$ -module on which $R _ { j }$ acts trivially for al $j \neq i$ , and $$ N = z _ {1} N \oplus z _ {2} N \oplus \dots \oplus z _ {r} N. $$ (3) The simple R-modules are the simple $R _ { i }$ -modules on which $R _ { j }$ acts trivially for $j \neq i$ in the following sense. Let $M _ { i }$ be the unique simple $R _ { i }$ -module (cf. Proposition 6). We may consider $M _ { i }$ as an R-module by letting $R _ { j }$ act trivially for all $j \neq i$ . Then $M _ { 1 } , \ldots , M _ { r }$ are pairwise nonisomorphic simple R -modules and any simple R -module is isomorphic to one of $M _ { 1 } , \ldots , M _ { r }$ . …
- **dependencies:** FC01-C18-U018


- **kind:** Proposition 9
- **source:** §18.2; printed pp. 854–863; extraction line 30208
- **statement/data:** If $\pmb { \triangle }$ is a division ring that is a finite dimensional vector space over an algebraically closed field F and $F \subseteq Z ( \Delta )$ , then $\Delta = F$
- **dependencies:** —


- **kind:** Theorem 10
- **source:** §18.2; printed pp. 854–863; extraction line 30250
- **statement/data:** Let G be a finte group. (1) $\mathbb { C } G \cong M _ { n _ { 1 } } ( \mathbb { C } ) \times M _ { n _ { 2 } } ( \mathbb { C } ) \times \cdot \cdot \cdot \times M _ { n _ { r } } ( \mathbb { C } ) .$ (2) CG has exactly r distinct isomorphism types of irreducible modules and these have complex dimensions $n _ { 1 } , n _ { 2 } , \ldots , n _ { r }$ (and so G has exactly r inequivalent irreducible complex representations of the coresponding degrees). (3) $\textstyle \sum _ { i = 1 } ^ { r } n _ { i } ^ { 2 } = | G |$ (4) r equals the number of conjugacy classes in $\pmb { G }$ .
- **dependencies:** —


- **kind:** Corollary 11
- **source:** §18.2; printed pp. 854–863; extraction line 30260
- **statement/data:** (1) Let A be a finite abelian group. Every ireducible complex representation of A is 1 -dimensional (i.e., is a homomorphism from A into $\mathbb { C } ^ { \times } )$ and A has $| A |$ inequivalent ireducible complex representations. Furthermore, every finite dimensional complex matrix representation of A is equivalent to a representation into a group of diagonal matrices. (2) The number of inequivalent (ireducible) degree 1 complex representations of any finite group G equals $| G / G ^ { \prime } |$
- **dependencies:** —


- **kind:** Theorem 12
- **source:** §18.2; printed pp. 854–863; extraction line 30302
- **statement/data:** The degree of each complex irreducible representation of a finite group G divides the order of $G ,$ i.e., in the notation of Theorem 10, each ${ \pmb n } _ { i }$ divides I G I for $i = 1 , 2 , \ldots , r .$ In the next section we shall describe the primitive central idempotents of $\mathbb { C } G$ in terms of the group elements
- **dependencies:** FC01-C18-U022


- **kind:** Definition
- **source:** §18.3; printed pp. 864–879; extraction line 30384
- **statement/data:** (1) A class .function is any function from G into F which is constant on the conjugacy classes of $G ,$ , i . e . , $f : G \to F$ such that $f ( g ^ { - 1 } x g ) = f ( x )$ for all $g , x \in G$ (2) If $\varphi$ is a representation of G aforded by the F G-module V , the character of $\varphi$ is the function $$ \chi : G \to F \quad \text { defined by } \quad \chi (g) = \operatorname{tr} \varphi (g), $$ where tr $\varphi ( \pmb { g } )$ is the trace of the matrix of $\varphi ( \pmb { g } )$ with respect to some basis of V (i.e., the sum of the diagonal entries of that matrix). The character is called irreducible or reducible according to whether the representation is ireducible or reducible, respectively. The degree of a character is the degree of any representation afording it. In the notation of the second part of this definition we shall also refer to $\pmb { \chi }$ as the character aforded by the F G-module V . In general, a character is not a homomorphism from a group into either the aditive or multiplicative group of the field.
- **dependencies:** —


- **kind:** Named example
- **source:** §18.3; printed pp. 864–879; extraction line 30400
- **statement/data:** The character of the trivial representation is the principal character χ_1(g)=1.
- **dependencies:** FC01-C18-U025


- **kind:** Named example
- **source:** §18.3; printed pp. 864–879; extraction line 30416
- **statement/data:** The character of the permutation representation on left cosets of H is the corresponding permutation character.
- **dependencies:** FC01-C18-U025


- **kind:** Named example
- **source:** §18.3; printed pp. 864–879; extraction line 30424
- **statement/data:** The character of the regular representation is the regular character.
- **dependencies:** FC01-C18-U025


- **kind:** Proposition 13
- **source:** §18.3; printed pp. 864–879; extraction line 30564
- **statement/data:** Let $z _ { 1 } , \ldots , z _ { r }$ be the orthogonal primitive central idempotents in CG labelled in such a way that $z _ { i }$ acts as the identity on the irreducible CG-module $M _ { i }$ , and let $\pmb { \chi } _ { i }$ be the character aforded by $M _ { i }$ . Then $$ z _ {i} = \frac {\chi_ {i} (1)}{| G |} \sum_ {g \in G} \chi_ {i} (g ^ {- 1}) g. $$
- **dependencies:** —


- **kind:** Proposition 14
- **source:** §18.3; printed pp. 864–879; extraction line 30634
- **statement/data:** If $\psi$ is any character of $G$ then $\psi ( x )$ is a sum of roots of l in $\mathbb { C }$ and $\psi ( x ^ { - 1 } ) = { \overline { { \psi ( x ) } } }$ for all $x \in G$
- **dependencies:** —


- **kind:** Theorem 15 (The First Orthogonality Relation for Group Characters)
- **source:** §18.3; printed pp. 864–879; extraction line 30642
- **statement/data:** (The First Orthogonality Relation for Group Characters) Let $G$ be a finite group and let $\chi _ { 1 } , \ldots , \chi _ { r }$ be the ireducible characters of $G$ over $\mathbb { C } .$ . Then with respect to the inner product $( ~ , ~ )$ above we have $$ \left(\chi_ {i}, \chi_ {j}\right) = \delta_ {i j} $$ and the ireducible characters are an orthonormal basis for the space of class functions In particular, if $\theta$ is any class function then $$ \theta = \sum_ {i = 1} ^ {r} (\theta , \chi_ {i}) \chi_ {i}. $$
- **dependencies:** —


- **kind:** Theorem 16
- **source:** §18.3; printed pp. 864–879; extraction line 30658
- **statement/data:** {The Second Orthogonality Relation for Group Characters) Under the notation above, for any $x , y \in G$ $$ \sum_ {i = 1} ^ {r} \chi_ {i} (x) \overline {{\chi_ {i} (y)}} = \left{ \begin{array}{l l} | C _ {G} (x) | & \text { if } x \text { and } y \text { are conjugate in } G \ 0 & \text { otherwise. } \end{array} \right. $$
- **dependencies:** —


- **kind:** Definition
- **source:** §18.3; printed pp. 864–879; extraction line 30664
- **statement/data:** For 8 any class function on G the norm of $\overleftrightarrow { \theta }$ is $( \theta , \theta ) ^ { 1 / 2 }$ and will be denoted by $| | \theta | |$ When a class function is written in terms of the ireducible characters, $\theta = \sum \alpha _ { i } \chi _ { i }$ its norm is easily calculated as $\textstyle | | \theta | | = ( \sum \alpha _ { i } ^ { 2 } ) ^ { 1 / 2 }$ . It follows that ## a character has norm 1 if and only if it is irreducible Finally, observe that computations of the iner product of characters 0 and 1/r may be simplifed as follows. $\mathbf { I f } \kappa _ { 1 } , \ldots , \kappa _ { r }$ are the conjugacy classes of G with sizes $d _ { 1 } , \ldots , d _ { r }$ and representatives $g _ { 1 } , \ldots , g _ { r }$ respectively, then the value $\theta ( g _ { i } ) \overline { { \psi ( g _ { i } ) } }$ appears $d _ { i }$ times in the sum for $( \theta , \psi )$ , once for each element of $\kappa _ { i }$ . Collecting these terms gives $$ (\theta , \psi) = \frac {1}{| G |} \sum_ {i = 1} ^ {r} d _ {i} \theta (g _ {i}) \overline {{\psi (g _ {i})}}, $$ a sum only over representatives of the conjugacy classes of G. In particular, the norm of 0 is given by $$ \left| \left| \theta \right| \right| ^ {2} = (\theta , \theta) = \frac {1}{| G |} \sum_ {i = 1} ^ {r} d _ {i} \left| \theta \left(g _ {i}\right) \right| ^ {2}. $$
- **dependencies:** —


- **kind:** Proposition 17
- **source:** §18.3; printed pp. 864–879; extraction line 30734
- **statement/data:** If $\psi _ { 1 }$ and $\psi _ { 2 }$ are characters, then so is their product $\psi _ { 1 } \psi _ { 2 }$
- **dependencies:** —



- **kind:** Definition
- **source:** §19.1; printed pp. 880–885; extraction line 30918
- **statement/data:** The character table of a finite group is the square table of irreducible character values on conjugacy-class representatives, unique up to permuting rows and columns.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30932
- **statement/data:** Character table of C_2.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30940
- **statement/data:** Character table of C_3.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30946
- **statement/data:** Character table of S_3.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30952
- **statement/data:** Character table of D_8.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30976
- **statement/data:** Character table of Q_8.
- **dependencies:** —


- **kind:** Named comparison
- **source:** §19.1; printed pp. 880–885; extraction line 30978
- **statement/data:** D_8 and Q_8 are nonisomorphic groups with the same character table, although their degree-2 representations differ over R.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 30997
- **statement/data:** Character table of S_4.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 31003
- **statement/data:** Character table of A_4.
- **dependencies:** —


- **kind:** Named example
- **source:** §19.1; printed pp. 880–885; extraction line 31011
- **statement/data:** Character table of S_5.
- **dependencies:** —


- **kind:** Theorem 1 (Burnside)
- **source:** §19.2; printed pp. 886–891; extraction line 31109
- **statement/data:** (Burnside) For p and $\pmb q$ primes, every group of order $p ^ { a } q ^ { b }$ is solvable. Before undertaking the prof of Burnside's Theorem itself we establish some results of a general nature. An easy consequence of these preliminary propositions is that the degrees of the irreducible characters of any finite group divide its order. The particular results that lead directly to the proof of Burnside's Theorem appear in Lemas 6 and 7. It follows quite easily that a counterexample to Burnside's Theorem of minimal order is a non-abelian simple group, and it is these two character-theoretic lemmas that give the contradiction by proving the existence of a normal subgroup. We first recall from Section 1 5.3 the definition of algebraic integers.
- **dependencies:** —


- **kind:** Definition
- **source:** §19.2; printed pp. 886–891; extraction line 31117
- **statement/data:** An element ${ \pmb { \alpha } } \in \mathbb { C }$ is caled an algebraic integer if it is a root of a monic polynomial with coeficients from $\mathbb { Z } .$ The basic results needed for the proof of Burnside's Theorem are:
- **dependencies:** —


- **kind:** Proposition 2
- **source:** §19.2; printed pp. 886–891; extraction line 31121
- **statement/data:** Let $\pmb { \alpha } \in \mathbb { C } .$ (1) The folowing are equivalent: (i) a is an algebraic integer, (ii) a is algebraic over Q and the minimal polynomial of $\pmb { \alpha }$ over $\mathbb { Q }$ has integer coefficients, and (ii) /Z[a] is a finitely generated /Z-module (where /Z[a] is the subring of C generated by $\mathbb { Z }$ and ${ \pmb { \alpha } } , \mathrm { i . e . } ,$ , is the ring of all /Z-linear combinations of nonnegative powers of a). (2) The algebraic integers in C form a ring and the algebraic integers in $\mathbb { Q }$ are the elements of $\mathbb { Z } .$
- **dependencies:** —


- **kind:** Corollary 3
- **source:** §19.2; printed pp. 886–891; extraction line 31135
- **statement/data:** For every character 1/ of the finite group $G , \psi ( x )$ is an algebraic integer for all $x \in G$
- **dependencies:** —


- **kind:** Proposition 4
- **source:** §19.2; printed pp. 886–891; extraction line 31141
- **statement/data:** Define the complex valued function $\omega _ { i }$ on ${ \mathcal { K } _ { 1 } , \ldots , \mathcal { K } _ { r } }$ for each i by $$ \omega_ {i} (\mathcal {K} _ {j}) = \frac {| \mathcal {K} _ {j} | \chi_ {i} (g)}{\chi_ {i} (1)} $$ where $_ { g }$ is any element of $\kappa _ { j }$ . Then $\omega _ { i } ( \boldsymbol { K } _ { j } )$ is an algebraic integer for all i and $j .$ .
- **dependencies:** —


- **kind:** Corollary 5
- **source:** §19.2; printed pp. 886–891; extraction line 31187
- **statement/data:** The degree of each complex irreducible representation of a finite group G divides the order of $G , { \mathrm { i . e . , } } \chi _ { i } ( 1 ) \mid | G | { \mathrm { f o r } } i = 1 , 2 , \ldots , r .$
- **dependencies:** —


- **kind:** Lemma 6
- **source:** §19.2; printed pp. 886–891; extraction line 31199
- **statement/data:** If G is any group that has a conjugacy class K and an ireducible matrix representation $\varphi$ with character $\pmb { \chi }$ such that $( | K | , \chi ( 1 ) ) = 1$ , then for $g \in \mathcal { K }$ either $\chi ( g ) = 0 \mathrm { o r } \varphi ( g )$ is a scalar matrix.
- **dependencies:** —


- **kind:** Lemma 7
- **source:** §19.2; printed pp. 886–891; extraction line 31223
- **statement/data:** If IICI is a power of a prime for some nonidentity conjugacy class $\kappa$ of $G .$ , then G is not a non-abelian simple group
- **dependencies:** —


- **kind:** Definition
- **source:** §19.2; printed pp. 886–891; extraction line 31243
- **statement/data:** A Hall subgroup has order relatively prime to its index; a complement to H≤G is K≤G with G=HK and H∩K=1.
- **dependencies:** —


- **kind:** Theorem 8 (P. Hall)
- **source:** §19.2; printed pp. 886–891; extraction line 31245
- **statement/data:** (P. Hall) Let $\pmb { G }$ be a group of order $p _ { 1 } ^ { \alpha _ { 1 } } p _ { 2 } ^ { \alpha _ { 2 } } \cdots p _ { t } ^ { \alpha _ { t } }$ where $p _ { 1 } , \ldots , p _ { t }$ are distinct primes. If for each $i \in { 1 , \ldots , t }$ there exists a subgroup $H _ { i }$ of $\pmb { G }$ with $| G : H _ { i } | = p _ { i } ^ { \alpha _ { i } }$ , then $\pmb { G }$ is solvable. Hall's Theorem can also be phrased: iffor each $\dot { \mathbf { \sigma } } \in \left{ 1 , \ldots , t \right}$ a Sylow $p _ { i } – \mathbf { s u b g r o u p }$ of G has a complement, then $\pmb { G }$ is solvable. The converse to Hall's Theorem is also true - this was Exercise 33 in Section 6. 1 . We shal first need some elementary lemas
- **dependencies:** —


- **kind:** Lemma 9
- **source:** §19.2; printed pp. 886–891; extraction line 31251
- **statement/data:** If G is solvable of order > 1 , then there exists $P \leq G$ with P a nontrivial p-group for some prime p.
- **dependencies:** —


- **kind:** Lemma 10
- **source:** §19.2; printed pp. 886–891; extraction line 31255
- **statement/data:** Let G be a group of order $p _ { 1 } ^ { \alpha _ { 1 } } p _ { 2 } ^ { \alpha _ { 2 } } \cdots p _ { t } ^ { \alpha _ { t } }$ where $p _ { 1 } , \ldots , p _ { t }$ are distinct primes. Supose there are subgroups H and K of G such that for each $i \in { 1 , \ldots , t }$ either $p _ { i } ^ { \alpha _ { i } }$ divides I H I or $p _ { i } ^ { \alpha _ { i } }$ divides I K I . Then $G = H K$ and $| H \cap K | = ( | H | , | K | )$
- **dependencies:** —


- **kind:** Definition
- **source:** §19.3; printed pp. 892–904; extraction line 31321
- **statement/data:** Let H be a subgroup of the finite group G and let V be an F H -module afording the representation $\varphi$ of H. The F G-module $F G \otimes _ { F H }$ induced module of $V$ and the representation of G it afords is called the induced representation of $\varphi .$ If $\psi$ is the character of $\varphi$ then the character of the induced representation is called the induced character and is denoted by ${ \bf I n d } _ { H } ^ { G } ( \psi )$
- **dependencies:** —


- **kind:** Theorem 11
- **source:** §19.3; printed pp. 892–904; extraction line 31323
- **statement/data:** Let H be a subgroup of the finite group $G$ and let $g _ { 1 } , \ldots , g _ { m }$ be representatives for the distinct left cosets of H in $\pmb { G }$ Let V be an F H -module afording the matrix representation $\varphi$ of H of degree n. The FG-module $W = F G \otimes _ { F H }$ V has dimension nm over $F$ and there is a basis of $W$ such that W afords the matrix representation $\Phi$ defined for each $g \in G$ by $$ \varPhi (g) = \left( \begin{array}{c c c} \varphi (g _ {1} ^ {- 1} g g _ {1}) & \dots & \varphi (g _ {1} ^ {- 1} g g _ {m}) \ \vdots & \vdots & \vdots \ \varphi (g _ {m} ^ {- 1} g g _ {1}) & \dots & \varphi (g _ {m} ^ {- 1} g g _ {m}) \end{array} \right) $$ where each $\varphi ( { \pmb g } _ { i } ^ { - 1 } { \pmb g } _ { j } )$ is an $n \times n$ block appearing in the $i , j$ block position of $\Phi ( g )$ ) , and where $\varphi ( { g } _ { i } ^ { - 1 } { g } { g } _ { j } )$ is defined to be the zero block whenever ${ { g } _ { i } ^ { - 1 } } { { g } } { { g } _ { j } } \notin { { H } }$
- **dependencies:** —


- **kind:** Corollary 12
- **source:** §19.3; printed pp. 892–904; extraction line 31357
- **statement/data:** In the notation of Theorem 1 1 (1) if $\psi$ is the character aforded by V then the induced character is given by $$ \operatorname{Ind} _ {H} ^ {G} (\psi) (g) = \sum_ {i = 1} ^ {m} \psi (g _ {i} ^ {- 1} g g _ {i}) $$ where $\psi ( g _ { i } ^ { - 1 } g g _ { i } )$ is defined to be O if $g _ { i } ^ { - 1 } g g _ { i } \notin H ,$ , and (2) $\mathbf { I n d } _ { H } ^ { G } ( \psi ) ( g ) = 0$ if g is not conjugate in G to some element of H. In particular, if H is a normal subgroup of G then ${ \mathbf { I n d } } _ { H } ^ { G } ( \psi )$ is zero on all elements of $G - H$
- **dependencies:** FC01-C19-U011


- **kind:** Definition
- **source:** §19.3; printed pp. 892–904; extraction line 31413
- **statement/data:** A finite group $\pmb { G }$ is called a Frobenius group with Frobenius kernel $Q$ if $Q$ is a proper, nontrivial normal subgroup of $\pmb { G }$ and $C _ { G } ( x ) \le Q$ for all nonidentity elements x of $Q$ In view of the application to simple groups mentioned at the beginning of this section we shall restrict attention to Frobenius groups $\pmb { G }$ of order $q ^ { a } p ,$ , where $\pmb { p }$ and $\pmb q$ are distinct primes, such that the Frobenius kernel $Q$ is an elementary abelian q-group of order $q ^ { a }$ and the cyclic group $G / Q$ acts irreducibly by conjugation on $Q$ . In other words, we shall assume $Q$ is a direct product of cyclic groups of order $\pmb q$ and the only normal subgroups of $\pmb { G }$ that are contained in $Q$ are I and $Q ,$ i.e. , $Q$ is a minimal normal subgroup of $G .$ For example, $A _ { 4 }$ is a Frobenius group of this type with Frobenius kernel $V _ { 4 }$ , its Sylow 2-subgroup. Also, if $\pmb { p }$ and $\pmb q$ are distinct primes with $\boldsymbol { p } < \boldsymbol { q }$ and $\pmb { G }$ is a non-abelian group of order $_ { p q }$ (one always exists if $p \mid q - 1 )$ then $\pmb { G }$ is a Frobenius group whose Frobenius kernel is its Sylow q-subgroup (which is normal by Sylow's Theorem). We essentially determine the character table of these Frobenius groups. Analogous results on more general Frobenius groups appear in the exercises.
- **dependencies:** —


- **kind:** Proposition 13
- **source:** §19.3; printed pp. 892–904; extraction line 31417
- **statement/data:** Let $\pmb { G }$ be a Frobenius group of order $\pmb q ^ { a } \pmb p .$ , where $\pmb { p }$ and $\pmb q$ are distinct primes, such that the Frobenius kernel $Q$ is an elementary abelian q-group of order $q ^ { a }$ and the cyclic group $G / Q$ acts irreducibly by conjugation on $Q .$ Then the following hold: (1) $G = Q P$ where P is a Sylow p-subgroup of $G .$ . Every nonidentity element of $\pmb { G }$ has order $\pmb { p }$ or $\pmb q .$ Every element of order $\pmb { p }$ is conjugate to an element of $P$ and every element of order $\pmb q$ belongs to $Q .$ The nonidentity elements of $P$ represent the $p - 1$ distinct conjugacy classes of elements of order $\pmb { p }$ and each of these classes has size $q ^ { a }$ . There are $( q ^ { a } - 1 ) / p$ distinct conjugacy classes of elements of order $\pmb q$ and each of these classes has size $\pmb { p } .$ (2) $\pmb { G } ^ { \prime } = \pmb { Q }$ so the number of degree 1 characters of $\pmb { G }$ is $\pmb { p }$ and every degree 1 character contains $Q$ in its kernel. (3) If $\psi$ is any nonprincipal irreducible character of $Q ,$ , then ${ \mathbf { I n d } } _ { Q } ^ { G } ( \psi )$ is an irreducible character of $G .$ . Moreover, every irreducible character of $\pmb { G }$ of degree $> 1$ is equal to ${ \bf I n d } _ { Q } ^ { G } ( \psi )$ for some nonprincipal irreducible character $\psi$ of $Q$ . Every irreducible character of $\pmb { G }$ has degree either 1 or $\pmb { p }$ and the number of irreducible characters of degree $\pmb { p }$ is $( q ^ { a } - 1 ) / p$
- **dependencies:** —


- **kind:** Proposition 14
- **source:** §19.3; printed pp. 892–904; extraction line 31453
- **statement/data:** Let G be a group, let H be a subgroup of G and let $\psi$ and $\psi ^ { \prime }$ be characters of H. (1) (Induction of characters is additive) I $\mathbf { n d } _ { H } ^ { G } ( \psi + \psi ^ { \prime } ) = . \mathbf { I n d } _ { H } ^ { G } ( \psi ) + \mathbf { I n d } _ { H } ^ { G } ( \psi ^ { \prime } )$ (2) (Induction of characters is transitive) If $H \leq K \leq G$ then $$ \operatorname{Ind} _ {K} ^ {G} \left(\operatorname{Ind} _ {H} ^ {K} (\psi)\right) = \operatorname{Ind} _ {H} ^ {G} (\psi). $$ It folows from part ( 1 ) of Proposition 14 that if $\textstyle \sum _ { i = 1 } ^ { s } n _ { i } \psi _ { i }$ is any integral linear combination of characters of H with $n _ { i } \geq 0$ for all i then $$ \operatorname{Ind} _ {H} ^ {G} \left(\sum_ {i = 1} ^ {s} n _ {i} \psi_ {i}\right) = \sum_ {i = 1} ^ {s} n _ {i} \operatorname{Ind} _ {H} ^ {G} (\psi_ {i}).\tag{*} $$ A class function of H of the form $\textstyle \sum _ { i = 1 } ^ { s } n _ { i } \psi _ { i }$ , where the coeficients are any integers (not necessarily nonnegative) is called a generalized character or virtual character of H. For a generalized character of H we define its induced generalized character of $G$ by equation ( * ), allowing now negative coefficients $n _ { i }$ as well. In this way the function $\mathbf { I n d } _ { H } ^ { G }$ becomes a group homomorphism from the additive group of generalized characters of H to the additive group of generalized characters of G (which maps characters to characters). …
- **dependencies:** —


- **kind:** Definition
- **source:** §19.3; printed pp. 892–904; extraction line 31469
- **statement/data:** A generalized (virtual) character is an integral linear combination of irreducible characters; induction extends additively to generalized characters.
- **dependencies:** FC01-C19-U028


- **kind:** Convention
- **source:** §19.3; printed pp. 892–904; extraction line 31503
- **statement/data:** For H≤G and generalized character μ of H, μ*=Ind_H^G(μ) denotes its induced generalized character in the final application.
- **dependencies:** FC01-C19-U029


- **kind:** Lemma 15
- **source:** §19.3; printed pp. 892–904; extraction line 31513
- **statement/data:** For any $i \in { 1 , 2 , 3 , 4 }$ let $q = q _ { i }$ , let $Q = Q _ { i }$ , let $N = N _ { i }$ and let $p = | N : Q |$ . Let $\psi _ { 1 } , \ldots , \psi _ { 4 }$ be any ireducible characters of N of degree $\pmb { p }$ (not necessarily distinct) and let $\alpha = \psi _ { 1 } - \psi _ { 2 }$ and $\beta = \psi _ { 3 } - \psi _ { 4 }$ . Then a and $\beta$ are generalized characters of $N$ which are zero on every element of $N$ of order not equal to $q$ . Furthermore, $\alpha ^ { * }$ and $\beta ^ { * }$ are generalized characters of $\pmb { G }$ which are zero on every element of G of order not equal to $q$ and $$ (\alpha^ {*}, \beta^ {*}) _ {G} = (\alpha , \beta) _ {N} $$ (where $( ~ , ~ ) _ { H }$ denotes the usual Hermitian product of class functions computed in the group H). In other words, induction from N to $G$ is an inner product preserving map on such generalized characters $\alpha , \beta$ of N.
- **dependencies:** —


- **kind:** Lemma 16
- **source:** §19.3; printed pp. 892–904; extraction line 31535
- **statement/data:** For any $i \in { 1 , 2 , 3 , 4 }$ let $q = q _ { i }$ , let $Q = Q _ { i }$ , let $N = N _ { i }$ and let $p = | N : \ell |$ - Let $\psi _ { 1 } , \ldots , \psi _ { k }$ be the distinct ireducible characters of N of degree $\pmb { p } .$ . Then there are distinct ireducible characters $\chi _ { 1 } , \ldots , \chi _ { k }$ of $G ,$ all of which have the same degree, and a fixed sign $\epsilon = \pm 1$ such that $\psi _ { 1 } ^ { * } - \psi _ { j } ^ { * } = \epsilon ( \chi _ { 1 } - \chi _ { j } )$ for all $j = 2 , 3 , \dots , k .$
- **dependencies:** —


- **kind:** Definition
- **source:** §19.3; printed pp. 892–904; extraction line 31571
- **statement/data:** The irreducible characters constructed from Lemma 16 are called the exceptional characters associated to the corresponding subgroup Q.
- **dependencies:** FC01-C19-U032


- **kind:** Lemma 17
- **source:** §19.3; printed pp. 892–904; extraction line 31573
- **statement/data:** The exceptional characters associated to $Q _ { i }$ are all distinct from the exceptional characters associated to $Q _ { j }$ for i and $j$ distinct elements of { 1 , 2, 3 , 4}
- **dependencies:** —


- The extraction has no individual printed-page boundaries. The exact section page interval and exact extraction line are therefore the strongest page localization supported by the frozen source; no approximate unit page is asserted.
- Source labels repeatedly contain OCR spellings such as `Defintion`, `Corolary`, and `Lema`; these are normalized to Definition/Corollary/Lemma in the catalogue metadata.
- Chapter 11, extraction line 15698 prints `Proposition 2`; it lies between Corollary 21 and Proposition 23 and is evidently Proposition 22.
- Chapter 16, extraction line 26553 encodes `Corollary 4` entirely in HTML `<sub>` tags. After tag normalization it is recovered as Corollary 4; a plain-text label scan misses it.
- Chapter 15, extraction line 25504 prints `Corollary 4` between Proposition 43 and Proposition 45; the intended label is evidently Corollary 44.
- Several formulas contain replacement characters (`�`), broken arrows, or split digits/letters, especially in Chapters 13–15 and 19. Where the mathematical object remains unambiguous, the catalogue uses concise normalized notation; the extraction line is retained as the authoritative locator.
- Chapter 19, line 31535 prints `Lema 16` and corrupts the subgroup-index notation in the hypotheses; comparison with adjacent Lemma 15 makes the intended index notation recognizable.
- Appendix I begins at extraction line 31689 (`Cartesian Products and Zorn's Lemma`); no material at or after that line is catalogued as Chapter 19.

**13 source units** across 1 chapters and appendices.

| Chapter | Units | In Lean | Not in Lean | Swept |
| --- | ---: | ---: | ---: | :-: |
| [FC01 Appendix I — Cartesian Products and Zorn's Lemma](ai.html) | 13 | — | — | no |

- [Foundational corpus mapping FC01 Dummit Foote](mapping.html)
