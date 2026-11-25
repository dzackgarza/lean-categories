# Research: decisions of the algebraic categories

Each decision settles a point that #55 or #101–#108 leaves open, and names its source.

## D1. Position in the work order

**Decision**: The feature is catalogue work and runs in its own document order beside features 001
and 005 (constitution M11). A task of feature 001 that needs one of its categories names the task
here as an input and, when it reaches it, does that task at once (constitution M9): 001 T068 takes
T001.

**Source**: constitution M9, M11; feature 001 FR-036.

## D2. The divisibility tower

**Decision**: Integral domains are the property classifier on commutative rings; UFDs and PIDs are
property classifiers on integral domains (UFD-hood is stated under cancellation); a normalization
(Mathlib `NormalizationMonoid`) and a Euclidean structure (Mathlib `EuclideanDomain`) are chosen
structure, with ring homomorphisms as morphisms. $\mathbf{PID} \to \mathbf{UFD}$ is realized by
Mathlib's derivation of unique factorization from principal ideals. No one-object subcategory
records the coverage of an implementation.

**Source**: #55, body and its subordination note; the correction of 2026-10-28 on #55 (leaf
coverage is not a registry row; kernel constitution C2); [FOUNDATIONS.md](../../FOUNDATIONS.md)
Rem. 6.6, Conv. 64.14.

## D3. Free-plus-torsion modules

**Decision**: The base is an integral domain; torsion is annihilation by a nonzero element. A
certified module is $(M, F, T, \varphi)$ with $F$ finite free, $T$ torsion and $\varphi$ a chosen
isomorphism $F \oplus T \cong M$; morphisms are the $R$-linear maps of the underlying modules. The
property category is the essential image of the forgetful functor. The certificate data are chosen
structure; no decomposition is presented as canonical.

**Source**: #101, the owner ruling of 2026-07-11 (first milestone over integral domains) and
research rounds 1–2; [FOUNDATIONS.md](../../FOUNDATIONS.md) Conv. 64.14. **Supersedes**: the
"arbitrary commutative rings" of the #101 title and story.

## D4. Finite abelian groups

**Decision**: The invariant factors $d_1 \mid \cdots \mid d_k$ of a finite abelian group are an
invariant on $\operatorname{Core}(\mathbf{FinAb})$; the isomorphism with $\bigoplus_i \mathbb Z/d_i$
is chosen structure. The elementary-divisor form is a comparison theorem.

**Source**: Mathlib `AddCommGroup.equiv_directSum_zmod_of_finite`; #103, story (readable
decompositions); [FOUNDATIONS.md](../../FOUNDATIONS.md) Conv. 64.14.

## D5. Group actions on modules

**Decision**: A $G$-module over $R$ is a functor $BG \to \operatorname{Mod}(R)$ (Mathlib `Rep`);
$M^G$ and $M_G$ are the right and left adjoints of the trivial-action functor. Over $\mathbb Z$ the
integral invariants are saturated: $M^G = M \cap (M \otimes \mathbb Q)^G$.

**Source**: #104, story and requirements (integral invariants need saturation); feature 003 D9 and
N10 for lattices.

## D6. Chain complexes and cohomology

**Decision**: Complexes are Mathlib `HomologicalComplex` with the grading stated; the intrinsic
object of a homological construction is its derived category and complexes are its presentations.
The realizations of the FC05 units are the owners; every registered cohomology theory (singular,
group, sheaf, de Rham) is registered as a composite through complexes and the homology functors.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) §77, Conv. 64.16; #107, maximal intended
capability; feature 002 (FC05 Definitions ticked).

## D7. Algebras

**Decision**: A differential graded algebra is a graded algebra with a degree-one differential
satisfying the Leibniz rule with the Koszul sign; Clifford and exterior algebras are functors from
quadratic and plain modules with their universal properties (Mathlib `CliffordAlgebra`,
`ExteriorAlgebra`); tensor and symmetric algebras are the rows of feature 005 T017.

**Source**: #108, maximal intended capability; [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 13.9 and
Addendum §10.

## D8. Sage audits

**Decision**: The audits of Sage's interfaces in #102–#108 and their parity counterparts are
`lean-cas-dsl` work; this repository registers the mathematics.

**Source**: #4, comment of 2026-07-30; kernel constitution C1.
