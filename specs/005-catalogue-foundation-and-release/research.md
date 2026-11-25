# Research: decisions of the classifier foundation, registry and release

Each decision settles a point that #4, #28, #29, #30, #31, #41, #50, #53, #54 or #59 leaves open,
or that their comments answer twice. Each names its source. The tasks cite decisions by number.
The issue comments named here are records; their requirements are carried below, and their
corrections of 2026-10-28 are applied.

## D1. The ambient model

**Decision**: The classifier, reindexing and expression interfaces are stated over an ambient
higher category given as a model-independent interface (objects, 1-morphisms, 2-cells,
homotopy pullbacks, arrow and diagram objects). The strict 2-category of Mathlib categories
(`CategoryTheory.Cat` with its bicategory) is the first realization and the test model. No
interface type fixes `Cat`.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Conv. 64.1, Rem. 65.1 ("choose one or provide
a sufficiently model-independent interface"); #1, decision record 4, R1.

## D2. Repleteness of a property classifier

**Decision**: A property classifier is the abbreviation of a classifier whose forgetful functor
is fully faithful and whose essential image satisfies Mathlib's
`ObjectProperty.IsClosedUnderIsomorphisms`. `Classifier.ofProperty P` is a property classifier by
a theorem, not by a field.

**Source**: #30, Mathlib reuse comment (`IsClosedUnderIsomorphisms`, `Functor.essImage`);
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 4.5, 6.2.

## D3. The host of the inverse classifier

**Decision**: The inverse classifier is hosted on monoids: groups are monoids with an inverse
operation and the two inverse diagrams, and $\mathbf{Grp} \to \mathbf{Mon}$ is fully faithful
because inverses in a monoid are unique. Over unital magmas the inverse is structure: the
forgetful functor is faithful and not full.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 12.1; the counterexamples on #30
(2026-10-28) and #1 (2026-10-28): $A = \{1, x\}$, $B = \{1, y, z\}$ with $x \mapsto y$.

**Supersedes**: the #30 body ("the inverse classifier over unital magmas is proved fully
faithful").

## D4. The operad model of the matching hook

**Decision**: The cellular matching presentation of associative algebras uses the
Stasheff associahedra, the cofibrant $A_\infty$ model, and records it as data of the hook. The
grounding coherence is associativity with its pentagon.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 10.2, Rem. 10.4, Rem. 65.3; #30,
foundations-compliance amendment.

## D5. The 1-morphisms of the monoidal grounding

**Decision**: The categorical grounding case is pseudomonoids in the strict 2-category of
categories, with strong monoidal functors as 1-morphisms; Mathlib's `Mon C` and
`monTypeEquivalenceMon : Mon (Type u) ≌ MonCat` supply the set case. No global monoidal
1-morphism class is fixed.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Ex. 11.3, Rem. 65.2; #30, Mathlib reuse comment.

## D6. Conventions of the module families

**Decision**: $\operatorname{Modules}(R)$ is the left $R$-modules. $\operatorname{Bimodules}(R, S)$
is the category of commuting left $R$- and right $S$-actions, equivalent to left modules over
$R \otimes_{\mathbb Z} S^{\mathrm{op}}$. $\operatorname{VectorSpaces}(K)$ is the left modules over
the field $K$. The comparison of a left $R$-module with $\operatorname{Bimodules}(R, \mathbb Z)$ is
a registered functor. The separating fixture for vector spaces and bimodules is $K = \mathbb C$.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 13.8, §§83, 85, 92; #54, §2 and its
correction of 2026-10-28 ($\mathbb Q \otimes_{\mathbb Z} \mathbb Q \cong \mathbb Q$).

## D7. Families are fibred categories with a stated variance

**Decision**: A parameterized family is a Grothendieck construction over its parameter category.
Its variance is part of its declaration: the total module family over rings uses restriction of
scalars (`cat.modules_total`); the family over commutative rings with extension of scalars is a
separate declaration (`cat.modules_over_rings_ext`) related by a registered functor (feature 001
FR-028).

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 4.6, 13.2, §84, Rem. 65.4; #54, the
fibred-category ruling recorded on 2026-08-06.

## D8. Method inheritance and parallel routes

**Decision**: A method is inherited only along registered structural functors
(`FunctorEntry.structural`). A left adjoint or another construction functor grants no method.
The routes from a receiver to a method's source are compared by registered 2-cells; a display
groups the routes that registered cells relate, and execution applies the component of the
cell that the selected route names. A cell is a declaration of this repository or one that the
kernel derives generically; a leaf supplies none. Only schema-level rules are precomputed; an
application is resolved when it is elaborated.

**Source**: #53, §8 and its corrections of 2026-10-28; kernel constitution C2, C6;
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 45.1, Conv. 64.2.

## D9. The remaining design questions of #53

**Decision**:

| #53 §16 question | Decision |
| --- | --- |
| 1. Target of a method presentation | any checked normalized `FunctorExpr`; `FunctorEntry` stays the authority of each primitive functor |
| 2. Core, Disc, Elements, Arr | ordinary values of `CategoryExpr.construct` with constructor roles (feature 001 FR-016) |
| 3. Receiver schemas | category expressions built by registered constructors (elements, arrows, products, bundling categories); no second type system |
| 4. Native wrappers | none in this repository |
| 5. Display of trusted assertions | `lean-cas-dsl` |
| 6. Approximation of reals | the `choice` operation of feature 001 FR-034; the effective interface is `lean-cas-dsl`'s |
| 7. Backend caches | `lean-cas-dsl` |
| 8. Form of route coherence | a registered natural isomorphism between the routes; an equality only inside a strict presentation after a comparison theorem |
| 9. Finite cardinality output | `card` is cardinal-valued; the natural-number value is the restriction along the finite cardinals with the comparison to `Nat.card` |
| 10. Scope of a bound generator | `lean-cas-dsl` |

**Source**: #53, §16; [FOUNDATIONS.md](../../FOUNDATIONS.md) Conv. 64.2; kernel constitution C1,
C22; README, "Consuming the registry".

## D10. Stable identifiers

**Decision**: A stable ID names one meaning. A change of meaning takes a new ID and deletes the
old one in the same release; the release notes name the removal. An alias is a spelling of an ID
and never a migration. No deprecated ID survives.

**Source**: constitution M7; `AGENTS.md`, no backward compatibility; #4, question 20.

## D11. The export and its views

**Decision**: The release exports, from `RegistrySnapshot.snapshot`, one JSON document with the
schema version, the release tag, the source revision and every row in canonical order (by kind,
then by stable ID), and one semantic DOT file whose edges carry the kinds `structural`,
`classifier_leg`, `composite`, `cell`, `equivalence`, `construction` and `parameter`. Layout and
colour carry no meaning. The hand-authored DOT of the earlier programme is not an input.

**Source**: #4, burdens 3, 6 and questions 19, 26–28; #1, decision record 3, §5; constitution M7.

## D12. The query interface

**Decision**: Consumers query the Lean API of `CasCatalogue.RegistrySnapshot` (`snapshot`,
`findEntry?`, `hasEntry`, `declarationNames?`, `idsWithPrefix`, `validateDerived`) at a pinned
revision, and the JSON export of D11. No serialized constructibility certificate is a release
artifact.

**Source**: README, "Consuming the registry (#49)"; #4, questions 21–22; kernel constitution C1.

## D13. The release contents

**Decision**: Foundation 0.1 holds the classifier foundation, the proof-carrying registry, the
typed constructors and families, the operation and method rows, the standard vocabulary and the
inputs of feature 001. Lattice arithmetic 0.2 holds the duals, discriminant forms and functors,
overlattices and gluing and the named lattices of feature 003 (rows N04, N05, N09, N21). Each
release is a tag of `main` at which `just test` passes.

**Source**: #1, decision record 3, §13; #50, #51; #6, gate comment of 2026-07-23.

## D14. Completeness of the catalogue

**Decision**: The catalogue is complete when an inclusion-minimal generating diagram with its
closure operations (domains, codomains, classifier totals and legs, pullback legs, parameter
categories, induced and comparison functors) contains every category that FOUNDATIONS and the
specifications of features 001, 003, 005, 006, 007, 008 and 009 require. Certification checks
enumeration from the reflected registry; it does not certify semantic correctness. It is the
last task before publication and does not gate a release.

**Source**: #4, comment of 2026-07-22 ("Completeness") and decision record 2 (blueprint union);
#1, decision record 3, §4; #32 (closed).

## D15. Publication to Prove2Me

**Decision**: Each definition module publishes as one definition with its definitions,
instances and structural lemmas; each theorem referenced from another module publishes as a
card whose statement is copied and whose proof is delegated to the original declaration. The
recipe reads `GET /api/v1/environments` at publication time, builds the payloads in a scratch
checkout against that environment, guards axioms with the axiom audit, applies the name rule
`LeanCategories.A.B ↦ LeanCategories_A_B`, publishes privately first and skips published names.
The repository pin follows the research image and is not moved for publication. The credential
is the owner's `PROVE2ME_API_KEY`.

**Source**: #59, body decisions 1–3 and comments of 2026-11-06 and 2026-11-21; #118.

## D16. Sage observation and the research repository

**Decision**: The 179-row Sage correspondence, the research requirement manifest, bridge records
and Sage parity are not requirements of this repository. Sage functionality is evidence for a
demanded declaration only.

**Source**: #4, comment of 2026-07-30; #1, comment of 2026-07-30; kernel constitution C1.

## D17. The public theory

**Decision**: The public mathematical theory is [FOUNDATIONS.md](../../FOUNDATIONS.md) and the
corpus site of this repository. The research Pages requirement of #1 is superseded.

**Source**: #1, ownership amendment of 2026-07-30; constitution M1 and Governance.
