# Feature Specification: Classifier foundation, proof-carrying registry and catalogue release

**Feature Branch**: `005-catalogue-foundation-and-release` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The roadmap of the normalized catalogue and its release (#4) and its open work units:
the higher classifier foundation (#30), proof-carrying expressions and the registry (#31), typed
constructors and parameterized families (#54), the operation registry (#28), functorial method
resolution (#53), the standard categorical vocabulary (#41), the vertical slice over
$\mathbb F_2$ (#29), publication to Prove2Me (#59) and the milestone Foundation 0.1 (#50). Every
open point of these records is settled in [research.md](research.md).

Read with the [constitution](../../.specify/memory/constitution.md), the [plan](plan.md) and the
[tasks](tasks.md). Paths are relative to `LeanCategories/`. `Reg/` is `Catalogue/Registry/`.
`Sem/` is `Catalogue/Semantics/`.

The registry of this repository is the one semantic source that every consumer projects
(constitution M7). This feature makes the registry's foundation mathematical: a classifier is a
functor with a reindexing universal property; a row carries its denotation and the equivalence
that identifies it with the declared category; a constructor and a family are typed
declarations; an operation and a method name checked functors; the standard vocabulary of
adjunctions, free objects and localizations exists as rows. It then releases the registry at a
pinned, versioned revision, certifies the complete catalogue and publishes the definitions.

## User Scenarios & Testing *(mandatory)*

The readers are the kernel of `lean-cas-dsl`, a downstream Lake package that pins a release, and
the mathematician who inspects a definition.

### User Story 1 - A mathematician reads a classifier and its reindexing (Priority: P1)

A mathematician takes a classifier $p_A : \mathcal C.A \to \mathcal C$ and a functor
$F : \mathcal D \to \mathcal C$. The reindexed classifier
$F^{*}p_A : \mathcal D \times_{\mathcal C} \mathcal C.A \to \mathcal D$ has the universal
property of the categorical pullback, with identity, composition and pasting equivalences that
are proved theorems. Property, structure and stuff are read from the classifying fibres.

**Why this priority**: every category of the catalogue is a classifier total or a reindexing of
one ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 5.1, 7.1).

**Independent Test**: elaborate the classifier test module; the universal property and the three
coherence equivalences are theorems; a property classifier is fully faithful with a replete
essential image; the inverse classifier over unital magmas is refused as a property.

**Acceptance Scenarios**:

1. **Given** the commutativity classifier of magmas and the forgetful functor from groups,
   **When** it is reindexed, **Then** the total is equivalent to commutative groups by a proved
   equivalence, and the comparison square carries its actual natural isomorphism.
2. **Given** $\mathbf{Mon}(\mathbf{Set})$ as the algebras of the $E_1$ operad in sets, **When** it
   is compared with $\mathbf{MonCat}$, **Then** a proved equivalence identifies them.
3. **Given** the magma $A = \{1, x\}$ with $x^2 = 1$, $x^{-1} = x$ and the magma
   $B = \{1, y, z\}$ with all products of $y, z$ equal to $1$ and $y^{-1} = z$, **When** the map
   $x \mapsto y$ is offered as a morphism of unital magmas with inverse, **Then** it preserves
   the multiplication and the unit but not the inverse, so the inverse classifier over unital
   magmas is not full.

---

### User Story 2 - Every registry row carries its denotation (Priority: P1)

A consumer reads a row $(\mathrm{id}, \mathcal C, e, \mathrm{eval}(e) \simeq \mathcal C)$: the
declared category, the expression that names it and the equivalence between them. Evaluation is
generic over the expression language; no row is evaluated by an identifier test.

**Why this priority**: a consumer that reads an identifier and a string has no mathematics to
trust (constitution M7, M13).

**Independent Test**: evaluate every registered category and functor expression of the snapshot;
each returns its denotation and equivalence witness; a dangling reference and an alias cycle are
refused at registration.

**Acceptance Scenarios**:

1. **Given** the expression of graded finite rings, **When** it is evaluated, **Then** it returns
   the category with its equivalence witness.
2. **Given** a classifier row, **When** a consumer reads it, **Then** it finds the total, the leg
   and the host, and can rebuild the pullback that a refinement names.

---

### User Story 3 - Constructors and families are typed declarations (Priority: P1)

A consumer forms $\operatorname{Subobjects}(\mathbf{Set})$, a slice $\mathcal C_{/Y}$, the left
modules over $R$ or the bimodules over $(R, S)$. Each is the application of a typed constructor or
family: its parameters are mathematical objects with their categories and variance; its identity
includes its parameters.

**Why this priority**: the kernel distinguishes $\operatorname{Mod}(\mathbb Q)$ from
$\operatorname{Mod}(\mathbb Z/2)$ and from schemes over $\mathbb Q$ only through typed
applications (#54).

**Independent Test**: the constructor test module elaborates each required example through the
generic constructor; two applications with different parameters are different rows; the five
exact-host fixtures resolve at their stated host or report the missing declaration.

**Acceptance Scenarios**:

1. **Given** the field $\mathbb C$, **When** a reader compares $\operatorname{VectorSpaces}(\mathbb C)$
   with $\operatorname{Bimodules}(\mathbb C, \mathbb C)$, **Then** they are different
   applications, because $\mathbb C \otimes_{\mathbb Z} \mathbb C$ is not $\mathbb C$.
2. **Given** a refined head with a classifier on a refined host, **When** it is resolved,
   **Then** the classifier is pulled back to that exact host or a named missing declaration is
   reported.

---

### User Story 4 - Operations and methods name checked functors (Priority: P2)

A consumer asks for the cardinality of a lattice, whether a group is abelian, or the domain
automorphism that transports one isomorphism to another. Each answer is a registered functor or a
composite along registered structural functors.

**Why this priority**: a method that is not a functor of this repository has no meaning
(constitution M1).

**Independent Test**: the operation test module resolves one set-level cardinality on finite
sets, modules, formed modules and lattices; `is_abelian` is the commutativity of the
multiplicative operation on cores; a method row whose functor does not typecheck is refused.

**Acceptance Scenarios**:

1. **Given** $L = (\mathbb Z/2)^4$ in $\operatorname{Mod}(\mathbb Z/2)$, **When** a reader asks for
   its cardinality, **Then** the row is the one cardinality functor on $\operatorname{Core}(\mathbf{Set})$
   composed with the underlying-set route, with value $16$.
2. **Given** isomorphisms $\sigma, \tau : X \cong Y$, **When** a reader asks for the domain
   transporter, **Then** it is $\sigma^{-1} \circ \tau \in \operatorname{Aut}(X)$ with
   $\sigma \circ (\sigma^{-1} \circ \tau) = \tau$.
3. **Given** the free functor $\mathbf{Set} \to \mathbf{CRing}$, **When** a reader asks whether a
   set inherits `factor`, **Then** it does not: inheritance runs only along registered structural
   functors.

---

### User Story 5 - The standard categorical vocabulary exists as declarations (Priority: P2)

A mathematician uses an adjunction with its unit, counit and triangle identities, a free object,
an essential image, a reflective localization, a free algebra, a monoid algebra with its
group-like adjunction, or sheafification as a reflective localization.

**Why this priority**: the language cannot state these constructions without them (#41;
[FOUNDATIONS.md](../../FOUNDATIONS.md) Addendum, Parts I–VII).

**Independent Test**: the vocabulary test module instantiates each construction at a real example
and exercises its law; an essential image is replete; a reflective localization is recognized by
its unit.

**Acceptance Scenarios**:

1. **Given** the monoid algebra functor $R[-] : \mathbf{Mon} \to \mathbf{Bialg}_R$, **When** it is
   compared with the group-like functor, **Then** the adjunction and the recognition theorem of
   its essential image hold.

---

### User Story 6 - The vertical slices read the registry (Priority: P2)

A consumer reads the coordinatized finite symmetric bilinear space $M = \mathbb F_2^2$ with Gram
matrix $G$, and the root lattice $A_2$ over $\mathbb Z$, through registered rows only.

**Why this priority**: these slices exercise inherited computation through the registry (#29).

**Independent Test**: the slice test module obtains $|M| = 4$, the numbering of $M$, $\det G$, the
radical and the isotropic vectors, and for $A_2$ the determinant $3$ and $|A_{A_2}| = 3$.

**Acceptance Scenarios**:

1. **Given** $G$ over $\mathbb F_2$, **When** a reader asks for $\det G$, **Then** the registry
   gives the value at the chosen frame, an invariant of the isometry class only modulo squares of
   units.

---

### User Story 7 - A consumer pins a release; the catalogue is certified and published (Priority: P3)

A downstream package pins a release tag. Its JSON and semantic DOT views are generated from the
reflected registry. The complete catalogue is certified against the categories that the
foundations and the feature specifications require. Each definition module is published as an
importable Prove2Me definition.

**Why this priority**: consumers need a fixed revision; certification and publication follow the
content.

**Independent Test**: a clean checkout reproduces the export of a release tag byte for byte; the
coverage report lists every required category with its row; the publisher's dry run lists every
module and card.

**Acceptance Scenarios**:

1. **Given** a release tag, **When** `Integration/RegistryConsumer/` builds against it, **Then**
   every row it needs resolves by stable ID.

---

### Edge Cases

- Inverses in a unital magma are not unique without associativity; the inverse classifier is
  hosted on monoids.
- $\mathbb Q \otimes_{\mathbb Z} \mathbb Q \cong \mathbb Q$, so $\operatorname{Bimodules}(\mathbb Q, \mathbb Q)$
  is equivalent to $\operatorname{VectorSpaces}(\mathbb Q)$; the separating fixture uses
  $\mathbb C$.
- $\mathbb Z/16$ is not an $\mathbb F_2$-module; the cardinality contrast for
  $(\mathbb Z/2)^4$ is $\mathbb Z/4 \times \mathbb Z/4$ as abelian groups.
- A predicate is not a functor on $\mathbf{Mag}$ into $\operatorname{Disc}(\mathbf{Bool})$: a
  map from the trivial magma into a noncommutative magma sends true to false. Predicates are
  functors on cores.
- A registered left adjoint into a category with a method grants that method to nothing.
- Category expressions are infinite ($\operatorname{Arr}(\operatorname{Arr}(\mathcal C))$,
  $\operatorname{Mod}(R)$ for every $R$); only schema-level rules are precomputed.

## Requirements *(mandatory)*

### Functional Requirements

**Classifiers (#30)**

- **FR-001**: A classifier MUST be a bare 1-morphism $p_A : \mathcal C.A \to \mathcal C$ of an
  ambient higher category given by a model-independent interface; the strict 2-category of
  Mathlib categories MUST be its first realization (research D1). Property, structure and stuff
  MUST be read from the truncation of the classifying fibres, cumulatively; full faithfulness and
  faithfulness are their strict shadows ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 5.1, 6.1–6.4,
  Conv. 64.4).
- **FR-002**: A property classifier MUST be a definitional abbreviation over a classifier whose
  forgetful functor is fully faithful with an essential image closed under isomorphisms
  (research D2). No parallel primitive MUST exist.
- **FR-003**: Reindexing MUST be the categorical pullback, with its universal property, the
  identity and composition equivalences and pullback pasting proved. A comparison square MUST
  carry its actual natural isomorphism; composition MUST compose it
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 7.1, Conv. 64.5).
- **FR-004**: The arrow and diagram objects, the operation classifier
  $\operatorname{Op}_n(\mathcal E) = \mathcal E \times^h_{\mathcal E \times \mathcal E} \operatorname{Ar}(\mathcal E)$
  and the diagram-extension classifier
  $\mathcal B.A = \mathcal B \times^h_{\operatorname{Fun}(\partial K, \mathcal E)} \operatorname{Fun}(K, \mathcal E)$
  MUST be declared; the operadic matching hook MUST name its cofibrant operad model and MUST be
  instantiated by the associativity-to-pentagon coherence ([FOUNDATIONS.md](../../FOUNDATIONS.md)
  Def. 8.1, 9.2, 10.2, Rem. 65.3; research D4).
- **FR-005**: The algebraic testbed MUST prove $\operatorname{Alg}_{E_1}(\mathbf{Set}) \simeq \mathbf{Mon}$
  and its categorical case (pseudomonoids with strong monoidal 1-morphisms); the role components
  $\mathbf{AddMag}$, $\mathbf{MulMag}$ MUST be equivalent to $\mathbf{MagmaCat}$ by proved
  equivalences; the two-operation category MUST be the pullback of two magma structures over
  $\mathbf{Set}$, and rings its iterated refinement; the inverse classifier MUST be hosted on
  monoids with $\mathbf{Grp} \to \mathbf{Mon}$ fully faithful ([FOUNDATIONS.md](../../FOUNDATIONS.md)
  Def. 12.1–12.3, Ex. 11.1, 11.3; research D3, D5).
- **FR-006**: Each classifier MUST have one semantic identity at its generating host; a second
  row with the same classifier and host MUST be refused; spellings are aliases. The fourteen
  historical collisions of #30 MUST be regression fixtures.

**Proof-carrying registry (#31, #4)**

- **FR-007**: Every category and functor row MUST carry $(\mathrm{id}, \mathcal C, e, \mathrm{eval}(e) \simeq \mathcal C)$.
  Evaluation MUST be generic over the expression language: no identifier case split, constructor
  expressions evaluate, endpoints are compared by equivalence.
- **FR-008**: `canonicalize` MUST return a normal form with a rewrite certificate only where
  termination and confluence are proved, and a non-committal result otherwise
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Prop. 53.5). A chosen host MUST be the initial object of
  the canonicalization diagram, stated contractible, or a named section of a noncontractible
  fibre. Alias cycles and dangling references MUST be refused at registration.
- **FR-009**: The expression language MUST express category objects, 1-morphisms, 2-cells,
  diagrams, fillers, equivalences and operadic algebras, evaluated relative to a selected
  realization.
- **FR-010**: Registration MUST validate declaration existence, hosts, family parameters and
  variance, functor endpoints, transport policy, aliases and presentation equivalences. A
  classifier row MUST record its total and its leg. The snapshot MUST include the presentation
  equivalences. The export MUST come from the reflected registry only.

**Constructors and families (#54)**

- **FR-011**: A constructor declaration MUST state its arity, parameter categories, domain,
  codomain, hypotheses, object and morphism actions, coherences, evaluator, equivalence witness
  and export data. $\operatorname{Subobjects}(\mathbf{Set})$, slices, coslices, arrow categories
  and categories of elements MUST be generic constructor values; a value of a generic assignment
  such as $\operatorname{Aut}_{\mathcal C}(X)$ MUST stay distinct from a constructed category.
- **FR-012**: A family MUST be a fibred category over its parameter category with typed
  parameters and variance. $\operatorname{LeftModules}(R)$, $\operatorname{RightModules}(R)$,
  $\operatorname{Bimodules}(R, S)$, $\operatorname{GradedModules}(R)$,
  $\operatorname{VectorSpaces}(K)$, $\operatorname{AlgebraIdeals}(A)$,
  $\operatorname{RingIdeals}(R)$ and $\operatorname{CommutativeRingIdeals}(R)$ MUST be typed
  families; the spelling $\operatorname{Modules}(R)$ MUST state its convention (research D6, D7).
  The identity of an application MUST include all its parameters.
- **FR-013**: A composed or refined head MUST resolve to its exact host without parsing a dotted
  name. The five historical exact-host fixtures of #54 MUST resolve at their host or report a
  named missing declaration; a weaker host MUST NOT pass.

**Operations and methods (#28, #53)**

- **FR-014**: The registry MUST hold one cardinality,
  $\operatorname{card} : \operatorname{Core}(\mathbf{Set}) \to \operatorname{Disc}(\mathbf{Card})$,
  inherited along underlying-set functors; finite cardinality MUST be its restriction. Index MUST
  be an operation on the arrow-category objects that carry the needed cokernel, cardinal-valued.
  $\operatorname{Isom}_{\mathcal C}(X, Y)$ MUST carry its $\operatorname{Aut}(Y)$–$\operatorname{Aut}(X)$
  bitorsor structure with the domain transporter $\sigma^{-1} \circ \tau$ and the codomain
  transporter $\tau \circ \sigma^{-1}$. A predicate such as commutativity MUST be a functor on a
  core; `is_abelian` MUST be the commutativity of the multiplicative operation composed with
  $\operatorname{Core}(\mathbf{Grp}) \to \operatorname{Core}(\mathbf{MulMag})$.
- **FR-015**: A method row MUST name a checked functor or a normalized composite of registered
  functors; a row whose source, target or declaration does not typecheck MUST be refused.
  Inheritance MUST run only along registered structural functors. Parallel routes MUST be
  identified only by registered cells; a display may group routes by the cells that relate them,
  and execution applies the component of the selected cell (research D8).

**Standard vocabulary (#41)**

- **FR-016**: Adjunctions with unit, counit and triangle identities, free objects as initial
  objects of comma categories, essential-image factorizations, restriction and corestriction,
  mates, reflective and coreflective localizations recognized by their unit, the free-algebra
  catalogue, monoid and group algebras with the group-like adjunction and the recognition theorem
  of its essential image, the free-module functor as a strong symmetric monoidal functor,
  sheafification as a reflective localization and stackification MUST be registered
  declarations ([FOUNDATIONS.md](../../FOUNDATIONS.md) Addendum, Parts I–VII).
- **FR-017**: [FOUNDATIONS.md](../../FOUNDATIONS.md) MUST carry Amendments 18.1–18.6 of its first
  addendum at the places they name.

**Slices, release, certification, publication**

- **FR-018**: The $\mathbb F_2^2$ slice and the $A_2$ slice MUST read their values through
  registered rows: $|M| = 4$, the numbering and `nth` of the enumerated finite set, $\det G$ at
  the chosen frame, the radical, the isotropic vectors; $\det G = 3$ and $|A_{A_2}| = 3$ for
  $G = \begin{pmatrix} 2 & -1 \\ -1 & 2 \end{pmatrix}$.
- **FR-019**: A release MUST fix the schema version, the canonical ordering, the stable-ID policy
  (research D10), the expression encoding and a command that reproduces its JSON and semantic DOT
  from a clean checkout. DOT edges MUST carry typed kinds (research D11). The query interface MUST
  be the Lean API of `RegistrySnapshot` and the JSON export (research D12).
- **FR-020**: The README source tree and the paths of #53 §17 MUST name the current registry
  modules; the README MUST name the Spec Kit task lists as the work order (constitution M11).
- **FR-021**: The Foundation 0.1 release MUST hold FR-001–FR-016 and feature 001; the Lattice
  arithmetic 0.2 release MUST hold the duality, discriminant, gluing and named-lattice rows of
  feature 003 (research D13).
- **FR-022**: The complete catalogue MUST be certified: an inclusion-minimal generating diagram
  and its closure operations whose closure holds every category that FOUNDATIONS and features 001,
  003 and 005–009 require, with a coverage report from the reflected registry. The report MUST
  certify enumeration, not semantic correctness (research D14).
- **FR-023**: Every definition module MUST be published to Prove2Me as an importable definition,
  with every cross-module theorem as a card, through a re-runnable recipe (research D15).
- **FR-024 (process)**: Every requirement MUST pass constitution M2, M3, M8 and E1: a search
  record in its issue, a clause-by-clause source comparison, tier-1 elaboration and the full gate
  at the milestone.

### Key Entities

- **Classifier**: a 1-morphism $p_A : \mathcal C.A \to \mathcal C$ with its classifying fibres.
- **Proof-carrying row**: $(\mathrm{id}, \mathcal C, e, \mathrm{eval}(e) \simeq \mathcal C)$.
- **Constructor declaration** and **family declaration**: typed signatures with their actions.
- **Method row**: a name and a checked functor or composite.
- **Release**: a tag with its schema version, export and reproduction command.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| ID | Outcome | Measure |
| --- | --- | --- |
| SC-001 | Reindexing laws proved | 4 of 4 (universal property, identity, composition, pasting) |
| SC-002 | Rows with an equivalence witness | every category and functor row of the snapshot |
| SC-003 | Identifier case splits in evaluation | 0 |
| SC-004 | Typed families of FR-012 | 8 of 8 |
| SC-005 | Cardinality declarations | 1 |
| SC-006 | Vocabulary constructions of FR-016 registered | all |
| SC-007 | Releases cut | Foundation 0.1 and Lattice arithmetic 0.2 |
| SC-008 | Required categories without a row in the coverage report | 0 |
| SC-009 | Published modules and cards | every module outside the axiom guard; every cross-module theorem |
| SC-010 | `sorry` and project axioms | 0 |

## Assumptions

- Feature 001 owns the schema additions that the kernel consumes (computation references, result
  kinds, notation, constructor roles, reading rules); this feature extends the same schema and
  adds no second field for a meaning that 001 adds (constitution M7).
- `lean-cas-dsl` owns the resolver, method names, realization records and their evidence
  (kernel constitution C2, C22); this repository owns the functors that the methods name.
- The Sage observation, its 179-row correspondence and the research requirement manifest are not
  inputs of this repository (research D16).
