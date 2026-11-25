# Feature Specification: Catalogue inputs for the computer-algebra roadmap

**Feature Branch**: `001-catalogue-inputs-for-the-cas` (work lands on `main`)
**Created**: 2026-11-25
**Status**: Draft
**Input**: The 30 lean-categories issues #182 to #211. Each is a mathematical declaration that a
task of the lean-cas-dsl task list consumes and that `main` (`443fba9`; `f009120` for #201 to
#211) does not have.

Read with the [constitution](../../.specify/memory/constitution.md), the [plan](plan.md) and the
[tasks](tasks.md). Paths are relative to `LeanCategories/`. `Sem/` is `Catalogue/Semantics/`.
`Reg/` is `Catalogue/Registry/`.

## User Scenarios & Testing *(mandatory)*

The reader of the registry is the consumer. Three readers occur:

- the **kernel**, which reads a written statement and selects its meaning from the registry;
- the **leaf author**, who reads the published catalogue and implements its operations;
- the **mathematician**, who inspects a definition against its source.

### User Story 1 - The kernel reads arithmetic through one owner of each operation (Priority: P1)

The kernel reads `2 * 3 = 6 in ℤ`, `0` in `ℚⁿ`, `7` in `ℤ/12` and `{1, 3, …}`. Each symbol
must reach exactly one declared operation or numeral family, at its generating category, along
a structural route with a registered comparison for every parallel route.

**Why this priority**: the first kernel consumers (T055, T056, T034, T068) read these forms.
Without one owner, the reading of `·` on a ring has competing routes and the kernel must choose
by order, which constitution M6 forbids.

**Independent Test**: elaborate the registry test modules; each written form resolves to one
row, and each competing route has its cell.

**Acceptance Scenarios**:

1. **Given** the ring $\mathbb{Z}$, **When** a reader looks up `·`, **Then** it finds the
   multiplication of magmas at $U_\times(\mathbb{Z})$ and the ring row as its restriction, and no
   route gives `·` the meaning of `+`.
2. **Given** the additive monoid $\mathbb{Q}^n$, **When** a reader reads `0`, **Then** it finds
   the numeral row of additive monoids and the zero vector.
3. **Given** a ring $R$ and $k \in \mathbb{N}$, **When** a reader compares the numeral $k$ of
   $R$ with the numeral $k$ of its underlying semiring, **Then** a registered theorem states
   their equality for the whole family.
4. **Given** the written set `{1, 3, …}` in $\mathbb{N}$, **When** a reader asks for its meaning,
   **Then** it finds the progression $\{1 + 2k \mid k \in \mathbb{N}\}$, its enumeration
   $k \mapsto 1 + 2k$, and the procedure that settled the constant difference.
5. **Given** a set $X$, **When** the route family from $X$ to `Sets` passes through
   `Subobjects(Sets)` any number of times, **Then** one registered cell identifies every such
   route with the identity.

### User Story 2 - The kernel and the leaf author name every computation by one reference (Priority: P1)

The kernel prepares a request with an operation address. The leaf author implements the family
at that address. Every computation that a statement can need must have such an address:
application of an object of maps, binder operations, power-object maps, proof procedures of
literal obligations, choice-producing operations with their fibres.

**Why this priority**: T032, T037, T113, T035 and T115 cannot prepare a request for a family that
has no reference.

**Independent Test**: a checked computation derivation names each new reference as target or
prerequisite and passes the registry validator; the registry snapshot lists the reference.

**Acceptance Scenarios**:

1. **Given** `obj.sets.polynomials`, **When** a derivation names its application, **Then** the
   validator accepts it and the snapshot lists the application as a family.
2. **Given** the binder `∫`, **When** a derivation states `sumOver_eq_sum` or `limit_eq`, **Then**
   the binder operation is its named target.
3. **Given** a set $X$, **When** a reader asks for membership $X \times \mathcal{P}X \to \Omega$,
   the transpose at a stage $Y$, the extent, the image or the inverse image, **Then** each is a
   named family.
4. **Given** the closed statements `7 < 12`, a graph literal on `Fin 3`, and `2 + 3 = 5` after
   literal evaluation, **When** the kernel asks for the registered procedure, **Then** the
   procedure proves or refutes each, and an instance that it does not settle stays unsettled.
5. **Given** a finitely generated module $M$, **When** a reader asks for its generating family,
   **Then** the row states kind `choice`, the fibre of surjections $R^n \twoheadrightarrow M$, and
   the type of each later construction as a family over that fibre.

### User Story 3 - The kernel reads written forms, readings and constructions from declarations (Priority: P2)

The kernel reads `|X|`, `p / q`, `Spec A`, `X ∖ 0`, `X in C/Y`, `K.leg(left)`, `p(a)` and a named
set used as a subset. Each written form and each change of reading must come from a declaration.

**Why this priority**: T035, T036, T048, T059 and T075 otherwise keep private tables of
notation and readings, a second source of meaning (constitution M7).

**Independent Test**: for each written form, a registry query from the form returns the one row
that it denotes.

**Acceptance Scenarios**:

1. **Given** the written form `|x|` at the reals, **When** a reader queries the notation index,
   **Then** it finds the absolute value row; `|X|` at finite sets gives the cardinality row.
2. **Given** `Spec A` for a commutative ring $A$, **When** a reader asks for its meaning,
   **Then** it finds the value of the registered functor $\operatorname{Spec}$ at $A$.
3. **Given** the walking cospan, **When** a reader asks for the leg at `one`, **Then** it finds
   the leg at the object `WalkingCospan.one`.
4. **Given** the one-point set $X$ and $Y = \{0, 1\}$, **When** $X$ is written where a subset of
   $Y$ is needed and no inclusion is declared, **Then** no reading applies; with the inclusion
   $i_0$ declared, the reading gives $\{0\}$.
5. **Given** $p \in R[x]$ and $a \in R$, **When** a reader reads `p(a)`, **Then** it finds the
   evaluation at the algebra $(R, \mathrm{id}_R)$ and `evaluation_own` as its identification.

### User Story 4 - The kernel continues through lifts, refinements and constructors (Priority: P2)

The kernel continues a computation through change of values, the refinement of an object along a
classifier, and the arrow and core constructors (T046, T057, T061).

**Why this priority**: these continuations need the morphism of the parameter, the refined
object, and the universal data of the constructor.

**Independent Test**: the test module of each mechanism elaborates a continuation from the
declarations only.

**Acceptance Scenarios**:

1. **Given** a linear map $f : W \to W'$ of $R$-modules with its proof of linearity, **When** it
   is admitted as an element of $\operatorname{Hom}_{\mathbf{Mod}_R}(W, W')$, **Then** change of
   values of bilinear modules, quadratic modules and lattices accepts it.
2. **Given** a ring $X$ and a proof that it is commutative, **When** a reader refines $X$, **Then**
   it obtains the commutative ring $\tilde{X}$ with the comparison $p(\tilde{X}) = X$.
3. **Given** a structure classifier and a proof that its fibre over $X$ is inhabited, **When** a
   reader asks for a point, **Then** no declaration supplies one.
4. **Given** the row `ctor.core`, **When** the validator or a consumer looks for the core
   constructor, **Then** it finds it by its declared role and universal data, not by a name.

### User Story 5 - The leaf author reads one category for each kind of order (Priority: P3)

The leaf author implements the order categories of the computational milestone "Orders" (kernel T202). Each kind
of order must be registered once, with its forgetful functors and operations.

**Why this priority**: the consumer is after the kernel functionality.

**Independent Test**: the snapshot holds one row for each of preorders, partial orders, linear
orders, join- and meet-semilattices, order lattices, bounded order lattices and Boolean algebras,
and every pair of parallel routes has its cell.

**Acceptance Scenarios**:

1. **Given** `0 ≤ 1 in FinOrder(5)`, **When** a reader reads `≤`, **Then** it finds the relation
   of preorders and its restriction to linear orders.
2. **Given** $(\mathbb{Z}, \max)$, **When** a reader asks whether it is a join-semilattice,
   **Then** it is an object of the registered category, with no bottom element required.

### User Story 7 - The leaf author reaches every category from sets (Priority: P3)

The leaf authors of the computational milestones of M4 (kernel T217, T221 to T224) implement a
category after the categories that its structural functors reach. A category whose objects are
objects of another category with more data needs the structural functor that forgets the data.

**Why this priority**: the consumers are the M4 milestones, after the V1 delivery.

**Independent Test**: following the structural edges of the snapshot, each category of the
scaffolding table reaches `cat.sets`, or the table states why it needs no such functor.

**Acceptance Scenarios**:

1. **Given** `cat.lattices_over_rings`, a refinement of `cat.bilin_forms_over_rings`, **When** a
   reader follows its structural edges, **Then** it reaches the forms, their underlying modules,
   the modules over rings and `cat.sets`.
2. **Given** a cusp $(L, \Gamma)$, **When** a reader applies the structural functor, **Then** the
   result is the integral lattice $L$.
3. **Given** a scheme, **When** a reader follows its structural edges, **Then** it reaches the
   underlying topological space and then the set of points.

### User Story 6 - The mathematician inspects each definition against its source (Priority: P1)

The mathematician opens any declaration of this feature and finds its source, its generality and
its search record.

**Why this priority**: constitution M2 and M8 apply to every requirement.

**Independent Test**: for each new declaration, the docstring cites the source and the owning
issue holds the search record.

**Acceptance Scenarios**:

1. **Given** any new declaration, **When** the mathematician follows its citation, **Then** the
   cited statement matches the declaration clause by clause.

### Edge Cases

- The numeral `7` of $\mathbb{Z}/7$ is the class $0$; the position `7` of `Fin 7` is invalid.
  The numeral procedure must accept the first and refute the second.
- `whole ∘ dom` on `Subobjects(Sets)` sends $A \subseteq X$ to $A \subseteq A$; it is not the
  identity, and no cell may say so.
- The subtraction `2 - 5` in $\mathbb{N}$ is outside the domain $b \le a$; it has no value.
- Two refinements of one object along two property classifiers both exist, and their images
  agree.
- An ellipsis `{1, 2, 4, …}` has no constant difference; it denotes no progression.

## Requirements *(mandatory)*

### Functional Requirements

Each requirement states the declaration, its generality and its standard source. The plan gives
files, rows, searches and checks. Order: the order of the first consumers in the kernel task list.

- **FR-001 (#193)**: The binary operation $\mu_X : X \times X \to X$, natural in magma
  homomorphisms, MUST be declared once at `cat.magmas`, and the addition once at
  `cat.additive_magmas`. The unit MUST be declared at `cat.monoids`, zero at
  `cat.additive_monoids`, the inverse at `cat.groups`, negation at `cat.additive_groups`, and
  $x \mapsto x^k$ at `cat.monoids`. Each operation row of semigroups, monoids, groups,
  semirings, rings and modules MUST be the restriction of its owner along a stated structural
  functor, with the equality of the whole families proved. The structural chain
  $\mathbf{AddMon} \to \mathbf{AddSemigrp} \to \mathbf{AddMag} \to \mathbf{Set}$ and the
  functor $\mathbf{SemiRing} \to \mathbf{AddCommMon}$ MUST be registered, with a cell for the two
  routes $\mathbf{Ring} \to \mathbf{AddMon}$. The functor $\mathbf{AddGrp} \to \mathbf{Grp}$ that
  reads addition as multiplication MUST NOT be structural. The two magmas of a set with two
  operations (`cat.magmaswithtwooperations`) MUST be its structural functors to
  `cat.magmas` and `cat.additive_magmas`. Sources: `FOUNDATIONS.md` Def. 12.1-12.3; Bourbaki,
  *Algebra I*, I.1; Mathlib `MagmaCat`, `Semigrp`, `MonCat`, `AddMagmaCat`, `AddSemigrp`,
  `AddMonCat`, `forget₂`.
- **FR-002 (#200)**: The natural isomorphism $\mathrm{dom} \circ \mathrm{whole} \cong
  1_{\mathbf{Set}}$ with identity components MUST be a registered invertible cell. The registry
  MUST state that $\mathrm{whole} \circ \mathrm{dom}$ on $\operatorname{Sub}(\mathbf{Set})$ is
  not the identity. The registry validator MUST refuse a structural cycle whose composite has no
  registered cell to the identity. Sources: `Foundation/Subsets.lean` (`wholeSubset`,
  `subsetCarrier`); Mathlib `Subobject`, `MonoOver`.
- **FR-003 (#185)**: The application declared by `ObjectEntry.application` MUST be a
  computation that `ComputationRef` names by its object row, with no second row. A checked
  derivation MUST accept it as target or prerequisite. Source: the evaluation map
  $\mathrm{ev} : Y^X \times X \to Y$ of a cartesian closed category (Mac Lane, *CWM*, IV.6).
- **FR-004 (#183)**: The registry MUST name a proof procedure for: (a) each explicit proposition
  parameter of a numeral declaration (for example $k < n$ of `finPoint`); (b) totality and
  distinct arguments of a graph literal on a finite domain; (c) the closed statement between
  literals that a literal evaluation leaves. A ring numeral has no domain condition: the numeral
  $k$ of $\mathbb{Z}/n$ is total. A procedure that does not settle an instance leaves it
  unsettled. Sources: Mathlib `ZMod.natCast_self`, `Fin`, `Decidable`; audit LC-183-F01 on #183.
- **FR-005 (#191)**: For every set $X$: membership $\in_X : X \times \mathcal{P}X \to \Omega$,
  natural in $X$; for every stage $Y$ the bijection $\operatorname{Hom}(Y \times X, \Omega)
  \cong \operatorname{Hom}(Y, \mathcal{P}X)$ with its two inverse laws, of which the present
  global transpose is the case $Y = 1$; the extent with its inclusion into $X$; the image of
  $f : X \to Y$ as the direct image of the whole of $X$; the inverse image $f^{-1} :
  \mathcal{P}Y \to \mathcal{P}X$ with the adjunction $\exists_f \dashv f^{-1}$ — each MUST be a
  named family. A theorem MUST relate $\in_X$ to `fun.subsets.contains`. Sources: Mac Lane and
  Moerdijk, *Sheaves in Geometry and Logic*, IV.1; Mathlib `Set.image`, `Set.preimage`,
  `Set.range`, `Set.image_subset_iff`.
- **FR-006 (#186)**: An additive monoid $A$ MUST have exactly one numeral, `0`, the image of the
  unique map from the initial (zero) additive monoid, read through a registered numeral row.
  Sources: `CONTRIBUTING.md` LC-15; Mathlib `AddMonCat`, `Zero`.
- **FR-007 (#194)**: The numerals $k \in \mathbb{N}$ MUST be generated at the coslice
  $\mathbb{N}/\mathbf{AddMon}$ (an additive monoid with a chosen element $1$, Mathlib
  `AddMonoidWithOne`), as the image of $k$ under the unique map from $\mathbb{N}$. The numerals of
  semirings MUST be their restriction along $S \mapsto (U_+(S), 1)$, and the numerals $k \in
  \mathbb{N}$ of rings the restriction along $\mathbf{Ring} \to \mathbf{SemiRing}$, with the
  theorems $\iota_R(k) = \iota_{U(R)}(k)$, $\iota(0) = 0$, $\iota(1) = 1$. Sources: Mathlib
  `Nat.cast`, `Int.cast_natCast`, `Nat.cast_zero`, `Nat.cast_one`; `FOUNDATIONS.md`, initial
  objects of rings.
- **FR-008 (#184)**: The `name` of a morphism or method row MUST stay the one authority for its
  function-call form. A row whose written form is not a function call (delimited `|x|`, infix
  `/`, postfix) MUST declare that form in one structured notation field. The registry MUST
  project an index from written form to rows and MUST refuse two rows with one written form at
  one owner. Source: audit LC-184-F01 on #184.
- **FR-009 (#189)**: For a commutative ring $R$ and an index type $\sigma$, $R[x_s : s \in
  \sigma]$ MUST be an object of `cat.commutative_rings`, with its comparisons to
  `obj.rings.mv_polynomials` and `obj.algebras.mv_polynomials`, so that Krull dimension applies.
  Sources: `FOUNDATIONS.md` Def. 10.3; Mathlib `MvPolynomial`, `MvPolynomial.instCommRing`,
  `ringKrullDim`.
- **FR-010 (#198)**: The constructor $C \mapsto C^{\mathrm{op}}$ MUST be registered.
  $\operatorname{Spec} : \mathbf{CRing}^{\mathrm{op}} \to \mathbf{Sch}$ and its relative form
  $\mathbf{Alg}_K^{\mathrm{op}} \to \mathbf{Sch}/\operatorname{Spec} K$ MUST be registered
  functors, and each registered spectrum MUST be presented as a value of them. The nonzero
  elements $X \setminus \{0\}$ of an object with a zero MUST be one construction with its
  inclusion and admission. An object of a slice $C/Y$ MUST be formed from $X$ and $X \to Y$,
  retaining both, with the forgetful functor $C/Y \to C$ structural. Each written form (`X ∖ 0`,
  `Spec A`, `X in C/Y`) MUST be declared on its construction. Sources: Hartshorne, *Algebraic
  Geometry*, II.2; Mathlib `Opposite`, `AlgebraicGeometry.Scheme.Spec`, `Spec.map`, `Over.mk`,
  `Over.forget`.
- **FR-011 (#188)**: A reading of one written term as a related one MUST be a declared rule
  with typed source, typed target and the selected map or route: (a) a global element $1 \to X$
  as its point; (b) an object as its carrier along the selected structural route; (c) a named set
  as a subset of $Y$, only with a declared inclusion $X \hookrightarrow Y$, as its image; (d)
  $p(a)$ for $p \in R[x]$, $a \in R$, as the evaluation at $(R, \mathrm{id}_R)$ with
  `evaluation_own`. No reading exists without its data. Sources: `FOUNDATIONS.md` Def. 1.4,
  Def. 45.2; audit LC-188-F01 and the comment of 2026-11-25 on #188; Mathlib `Polynomial.eval`.
- **FR-012 (#190)**: The operation of each of the eight binder rows MUST be a family that
  `ComputationRef` names by the binder row, with its parameters and its object of maps. The sum
  and product over a finite subset $A$ MUST be the values at $A$ of $\sum$ and $\prod$; the real
  and complex series the sum of a summable family in a Hausdorff commutative topological monoid;
  the power-series sum that sum in $R[[t]]$; the limit with its uniqueness. The identities
  `sumOver_eq_sum`, `prodOver_eq_prod`, `realSeriesSum_eq`, `complexSeriesSum_eq`,
  `powerSeriesSum_eq`, `limit_eq` MUST be registered derivations. Sources: Bourbaki, *Algebra I*,
  I.2.1; Bourbaki, *General Topology*, III.5; Mathlib `Finset.sum`, `tsum`, `intervalIntegral`,
  `Filter.Tendsto`, `tendsto_nhds_unique`.
- **FR-013 (#192)**: For a commutative ring $R$, the parameter of change of values MUST be an
  element of $\operatorname{Hom}_{\mathbf{Mod}_R}(W, W')$ (through $\mathbf{CRing} \to
  \mathbf{Ring}$), admitted by the existing linearity procedure. $W \mapsto \mathrm{Bil}_R(W)$,
  $W \mapsto \mathrm{Quad}_R(W)$ and the lattice categories MUST be declared functors
  $\mathbf{Mod}_R \to \mathbf{Cat}$ with the proved identity and composition laws, and the lift
  of subobjects stated at the same morphism. Sources: `FOUNDATIONS.md` Def. 15.5, Prop. 31.2;
  Mathlib `ModuleCat.ofHom`, `ModuleCat.Hom.hom`, `LinearMap.compr₂`.
- **FR-014 (#187)**: Each registered limit and colimit shape with finitely many objects MUST
  declare a name for each object; the leg at a written name MUST be the leg at that object. The
  names are those of Mathlib: `left`, `right` (walking pair); `left`, `right`, `one` (walking
  cospan); `zero`, `left`, `right` (walking span); `zero`, `one` (walking parallel pair);
  $0, \dots, n-1$ for `Fin n`. Source: Mathlib `WalkingPair`, `WalkingCospan`, `WalkingSpan`,
  `WalkingParallelPair`.
- **FR-015 (#197)**: For each registered property classifier $p : A \to C$ and object $X$ with
  a proof of `Holds`, the refined object $\tilde{X}$ with $p(\tilde{X}) = X$, unique up to unique
  isomorphism, MUST be declared. A structure classifier MUST have no such declaration. Two
  refinements of one object MUST both exist, with the comparison of their images. Each property
  row (`is_finite`, `is_commutative`, `is_abelian`, `is_lattice`, `is_alternating`) MUST name the
  procedure that proves or refutes it for a closed object. Sources: `FOUNDATIONS.md` Def. 46.3,
  Def. 46.4; Mathlib `ObjectProperty.FullSubcategory`, `Functor.Fiber`.
- **FR-016 (#196)**: Each registered constructor MUST declare the universal data that identify
  it: arrow ($\mathrm{dom}$, $\mathrm{cod}$, $\operatorname{Mor}(C) \cong \operatorname{Ob}(
  \operatorname{Arr} C)$); core (the inclusion $\operatorname{Core}(C) \to C$, structural, and
  $\operatorname{Iso}_C(X, Y) \cong \operatorname{Hom}_{\operatorname{Core} C}(X, Y)$); slice
  and coslice (forget, structure map); elements (projection, point); subobjects (domain,
  inclusion); functor category (evaluation); opposite ($\mathrm{op}$, $\mathrm{unop}$). Each
  datum MUST be natural in $C$. A constructor row MUST state its role by these data, and the
  validator MUST find a constructor by its role. Sources: Mac Lane, *CWM*, II.4; Mathlib `Arrow`,
  `Core`, `Over`, `Under`, `CategoryOfElements`, `Subobject`, `evaluation`, `Opposite`.
- **FR-017 (#182)**: Each registered operation MUST state its kind, `fixed` or `choice`. A
  `choice` operation MUST declare its fibre over each input, the admissibility of a candidate,
  and the type of each later construction as a family over the fibre. The declarations MUST
  cover the generating family of a finitely generated $R$-module (fibre $\coprod_n$ of
  surjections $R^n \twoheadrightarrow M$), the basis of a finite free module (fibre of bases), the
  free cover, and one `fixed` operation whose definition uses `Classical.choice` (the rank,
  `fun.modules.rank`). The fibre inclusions of `fam.based_module`, `fam.free_cover` and
  `fam.coord_indexed` MUST be structural. Sources: `FOUNDATIONS.md` Def. 46.3, Def. 73.2-73.6;
  kernel constitution C5; Mathlib `Basis`, `Module.Finite`, `Module.rank`.
- **FR-018 (#199)**: The progression with first term $a$ and difference $d$ in an additive monoid
  MUST be the image of $\mathbb{N}$ under $k \mapsto a + k \cdot d$, with its finite sections and
  that map as its selected enumeration. The proposition that written terms begin exactly one
  progression (constant difference) MUST have a procedure that settles it for closed terms.
  Subtraction $a - b = a + (-b)$ MUST be declared at `cat.additive_groups`, and the subtraction
  of $\mathbb{N}$ on its domain $b \le a$. Sources: Mathlib `nsmul`, `sub_eq_add_neg`,
  `Nat.sub`, `Set.range`; `CONTRIBUTING.md` LC-14.
- **FR-019 (#195)**: Each kind of order MUST be registered once: preorders, partial orders
  (`cat.partial_orders`), linear orders (`cat.linear_orders`), join-semilattices and
  meet-semilattices without bounds, order lattices, bounded order lattices and Boolean algebras,
  with the forgetful functors $\mathbf{LinOrd} \to \mathbf{Lat} \to \mathbf{SemiLat}_\vee,
  \mathbf{SemiLat}_\wedge \to \mathbf{PartOrd} \to \mathbf{Preord} \to \mathbf{Set}$ and
  $\mathbf{BoolAlg} \to \mathbf{BddLat} \to \mathbf{Lat}$ structural and a cell for every pair of
  parallel routes. `≤` and `<` MUST be declared at preorders; join and meet at the
  semilattices; $\min$, $\max$ of a linear order as its meet and join; $\bot$, $\top$ at bounded
  lattices; `⊆`, `∪`, `∩` of a Boolean algebra as restrictions. The well-order classifier MUST be
  hosted by `cat.linear_orders`. `cat.partially_ordered_sets` and `cat.totally_ordered_sets` MUST
  be removed. Sources: Davey and Priestley, *Introduction to Lattices and Order*, ch. 1-2;
  Mathlib `Order/Category/{Preord,PartOrd,LinOrd,Semilat,Lat,BddLat,BoolAlg}`.
- **FR-020 (scaffolding)**: Each of the 51 categories with no structural chain to `cat.sets` at
  `443fba9` MUST either receive its missing structural functor from the requirement that owns it
  (table below) or need none for the stated reason.
- **FR-022 (#201)**: `cat.crystals` MUST be a registered category that is not opaque, with its
  underlying-set functor $\mathbf{Crys} \to \mathbf{Set}$ as a structural functor row; the opaque
  port `oport.crystals.sets` MUST be deleted when the row replaces it. Sources: Kashiwara, *On
  crystal bases* (1995); Hong and Kang, *Introduction to Quantum Groups and Crystal Bases*, ch. 4.
- **FR-023 (#202)**: The category of topological spaces MUST be registered with its structural
  forget to `cat.sets`, and $\mathbf{Sch} \to \mathbf{Top}$, $X \mapsto |X|$, MUST be a structural
  functor row. Sources: Hartshorne, *Algebraic Geometry*, II.2; Mathlib
  `AlgebraicGeometry.Scheme.forgetToTop`.
- **FR-024 (#203)**: The inclusion $I \mapsto (I \hookrightarrow R)$ of the ideals of $R$ into the
  submodules of the regular module MUST be a structural functor row from `cat.ideals_r` to
  `cat.subobjects_modules_r`. Sources: Atiyah and Macdonald, ch. 1-2; Mathlib
  `Ideal R = Submodule R R`.
- **FR-025 (#204)**: For each category row whose expression is $\mathrm{refine}(B, c)$, the registry
  MUST derive the structural edge $\mathrm{refine}(B, c) \to B$ that forgets the evidence, as it
  derives the forget of a classifier total, and MUST refuse a structural functor row equal to such
  an edge. Sources: Mac Lane, *Categories for the Working Mathematician*, I.3; Mathlib
  `ObjectProperty.ι`.
- **FR-026 (#205)**: The functor $(R, M, W, b) \mapsto (R, M)$ from `cat.bilin_forms_over_rings` to
  `cat.modules_over_rings_ext` MUST be a structural functor row, distinct from the fibration
  projection `fun.bilin_forms.values`. Source: Bourbaki, *Algèbre*, ch. IX, §1.
- **FR-027 (#206)**: The functor from `cat.quad_forms_over_rings` to `cat.modules_over_rings_ext`
  that sends a quadratic form to its module MUST be a structural functor row. Source: Bourbaki,
  *Algèbre*, ch. IX, §3.
- **FR-028 (#207)**: The functor $(R, M) \mapsto (R, M)$ from `cat.modules_over_rings_ext`
  ($\int \mathbf{Mod}$ over $\mathbf{CRing}$, extension of scalars) to `cat.modules_total`
  ($\int^{c} \mathbf{Mod}$ over $\mathbf{Ring}$, restriction of scalars) over
  $\mathbf{CRing} \to \mathbf{Ring}$, acting on maps by the transpose of
  $S \otimes_R - \dashv f^{*}$, MUST be a structural functor row with the theorem that it commutes
  with the two projections. Sources: Bourbaki, *Algèbre*, ch. II, §5; Mathlib
  `ModuleCat.extendRestrictScalarsAdj`.
- **FR-029 (#208)**: The functor $(L, \Gamma) \mapsto L$ from `cat.cusps` to `cat.integral_lattice`
  MUST be a structural functor row. Source: the declaration `CuspObject`
  (`LeanCategories/Lattices/Valued/Cusps.lean`).
- **FR-030 (#209)**: The inclusions of `cat.definite_lattice` and `cat.indefinite_lattice` into
  `cat.finite_projective_lattice` at $R = W = \mathbb{Z}$ MUST be structural functor rows,
  declared by `definiteForget` and `indefiniteForget`. Source: Serre, *A Course in Arithmetic*,
  ch. V.
- **FR-031 (#210)**: The full-subcategory inclusions $\mathrm{FinFreeLat}_{R,W} \to \mathrm{Lat}_{R,W}$,
  $\mathrm{EvenLat}_{R} \to \mathrm{IntLat}_{R}$ and $\mathrm{UnimodLat}_{R} \to$ the fraction-field
  perfect finite projective lattices MUST be structural functor rows at the parameters of each
  family. Source: Milnor and Husemoller, *Symmetric Bilinear Forms*, ch. I-II.
- **FR-032 (#211)**: The ring operations `+`, `·`, negation and powers MUST be declared for
  $R : \mathbf{Rings}_u$ at every universe $u$, and the scalar action for $R : \mathbf{Ring}_u$ and
  $M : \mathbf{Mod}_v(R)$ in independent universes; the universe-0 uses are instances. Sources:
  Mathlib `RingCat`, `ModuleCat.{v} R`; Bourbaki, *Algèbre*, ch. I, §8, ch. II, §1.
- **FR-021 (process)**: Every requirement MUST pass the checks of constitution M2, M3, M8 and
  E1: a search record in its issue, a clause-by-clause source comparison, tier-1 elaboration of
  its modules and test modules, and the full gate `just test` at the milestone.

### Structural scaffolding of the 51 categories with no chain to `cat.sets`

Source: `scaffolding.md` of the planning research, computed from `443fba9`. "Structural" means a
functor that sends an object to its underlying object (`Reg/Entry.lean`, `FunctorEntry.structural`).

| Categories | Count | Owner | Missing structural functor or reason for none |
| --- | --- | --- | --- |
| `cat.additive_magmas`, `cat.additive_semigroups` | 2 | FR-001 (#193) | $\mathbf{AddSemigrp} \to \mathbf{AddMag} \to \mathbf{Set}$ |
| `cat.magmaswithtwooperations` | 1 | FR-001 (#193) | its two magmas, to `cat.magmas` and `cat.additive_magmas` |
| `cat.coslice_sets` | 1 | FR-007 (#194) | the coslice forget $X/\mathbf{C} \to \mathbf{C}$, declared for the constructor |
| `cat.schemes_over`, `cat.schemes_over_ring` | 2 | FR-010 (#198) | slice forget to `cat.schemes`; fibre inclusion of `family.schemes_over_ring` |
| `cat.core_groups`, `cat.core_modules_r`, `cat.core_pointed_sets`, `cat.core_sets`, `cat.core_subobjects_modules_r`, `cat.core_subobjects_sets` | 6 | FR-016 (#196) | the inclusion $\operatorname{Core}(C) \to C$ |
| `cat.core_well_ordered_sets` | 1 | FR-016 (#196), FR-019 (#195) | the core inclusion, and the host of the well-order classifier on `cat.linear_orders` |
| `cat.based_module`, `cat.free_cover`, `cat.coord_indexed` | 3 | FR-017 (#182) | the fibre inclusion of each choice fibre |
| `cat.partially_ordered_sets`, `cat.totally_ordered_sets` | 2 | FR-019 (#195) | removed; `cat.partial_orders`, `cat.linear_orders` have the chain |
| `cat.well_ordered_sets` | 1 | FR-019 (#195) | the forget of the classifier, once its host is `cat.linear_orders` |
| `cat.enumerated_monotone_sets` | 1 | FR-019 (#195) | its functors to `cat.enumerated_sets` and `cat.well_ordered_sets` as structural, with their cell |
| `cat.arrows_bilin_module`, `cat.arrows_groups`, `cat.arrows_modules_r`, `cat.arrows_sets` | 4 | none needed | an object of $\operatorname{Arr}(C)$ is a morphism, not a structured object; $\mathrm{dom}$ and $\mathrm{cod}$ are universal data (FR-016), not underlying objects |
| `cat.endofunctors_sets`, `cat.sets.pair_diagrams` | 2 | none needed | functor categories; evaluation is universal data (FR-016), not an underlying object |
| `cat.subsets.point_predicates`, `cat.subsets.subset_predicates` | 2 | none needed | categories of elements; the projection is the projection of a fibration, which `FunctorEntry.structural` excludes |
| `cat.walking_pair` | 1 | none needed | an index shape; FR-014 names its objects |
| `cat.cardinals`, `cat.cardinalities`, `cat.ordinals` | 3 | none needed | codomains of invariants; an object is a value, not a structured set |
| the refinements `cat.even_integral_lattices`, `cat.finite_free_lattices_over_rings`, `cat.finite_projective_lattices_over_rings`, `cat.integral_forms`, `cat.integral_lattices`, `cat.lattices_over_rings`, `cat.unimodular_lattices_over_rings` | 7 | FR-025 (#204); FR-026 (#205) and FR-028 (#207) for their bases | the inclusion $\mathrm{refine}(B, c) \to B$ |
| `cat.bilin_forms_over_rings` | 1 | FR-026 (#205), FR-028 (#207) | the underlying module, then modules over rings |
| `cat.quad_forms_over_rings` | 1 | FR-027 (#206), FR-028 (#207) | the underlying module, then modules over rings |
| `cat.modules_over_rings_ext` | 1 | FR-028 (#207) | $(R, M) \mapsto (R, M)$ to `cat.modules_total` |
| `cat.ideals_r` | 1 | FR-024 (#203) | an ideal as a submodule of the regular module |
| `cat.definite_lattice`, `cat.indefinite_lattice` | 2 | FR-030 (#209) | the inclusion into `cat.finite_projective_lattice` |
| `cat.schemes` | 1 | FR-023 (#202) | $\mathbf{Sch} \to \mathbf{Top} \to \mathbf{Set}$ |
| `cat.cusps` | 1 | FR-029 (#208) | $(L, \Gamma) \mapsto L$ to `cat.integral_lattice` |
| `cat.crystals` | 1 | FR-022 (#201) | the underlying set |
| the fibres `cat.even_lattice`, `cat.finite_free_lattice`, `cat.unimodular_lattice` | 3 | FR-031 (#210) | the full-subcategory inclusion of each family |
| **Total** | **51** | | |

### Key Entities

- **Registry row**: an entry of `normalized_registry` (category, functor, operation, numeral,
  binder, morphism, method, object, limit, constructor, classifier, property, cell, derivation).
- **Computation reference** (`ComputationRef`): the address of a computation family that a
  derivation and a consumer name.
- **Structural route**: a path of structural functors, classifier forgets and derived images; two
  parallel routes need a cell (M6).
- **Choice fibre**: the type of admissible answers of a `choice` operation over an input.
- **Proof procedure**: a registered `meta` procedure of this library that proves or refutes a
  closed proposition (LC-18).
- **Reading rule**: a declared change of reading of a written term, with its typed data.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| ID | Outcome | Measure |
| --- | --- | --- |
| SC-001 | Every issue #182 to #211 closes on its own acceptance | 30 of 30 issues closed |
| SC-002 | Each kernel task T118 to T125, T128 to T138, T146 and T225 to T234 has its input on `main` | 30 of 30 inputs present |
| SC-003 | No new `sorry`, axiom or `native_decide` | axiom audit and `lean-no-sorry` report 0 new sites |
| SC-004 | One owner per operation symbol | 0 symbols with two unrestricted rows on one structural route |
| SC-005 | Every pair of parallel structural routes has a cell | 0 uncompared pairs among the routes that this feature adds |
| SC-006 | Categories with no chain to `cat.sets` | 51 at `443fba9`; 0 with an owner in the scaffolding table left without its functor; 0 without an owner or a stated reason |
| SC-007 | Tier-1 loop of each task | each loop completes in under 300 s on the research image |
| SC-008 | Search records | 30 of 30 issues hold a reproducible search record |
| SC-009 | Source fidelity | each new declaration cites a source checked clause by clause |

## Assumptions

- The consumer reads lean-categories at a pinned revision. A declaration on `main` reaches the
  kernel when the kernel pins a revision that contains it; the pin and the toolchain port belong
  to kernel issue #90.
- `main` at `443fba9` is the base. Open pull requests #77, #79, #81 and #111 touch rows of
  FR-012, FR-014 and FR-005. A task extends the row as it is on `main`; a merged pull request
  changes that row, not the requirement.
- The present Lean toolchain (`lean-toolchain`) and Mathlib `master` of `lakefile.toml` are the
  build environment.
