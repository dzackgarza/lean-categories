# Feature Specification: Scheme and stack geometry

**Feature Branch**: `007-scheme-and-stack-geometry` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The roadmap of scheme, stack and compactification geometry (#9), the scheme and
relative-geometry foundation (#38) and fibred categories, stacks and KSBA moduli (#39), with every
open choice of their bodies settled in [research.md](research.md). The general-base relative Spec
and Proj (#22) are on `main`; the period and compactification layer is feature 008.

The feature delivers the language of algebraic geometry that the research programme states its
results in: schemes over a base with their morphism properties; varieties, curves and surfaces;
coherent and reflexive sheaves, divisors and dualizing data; relative constructions with their
universal properties; fibred categories, stacks, algebraic spaces and algebraic stacks; group
actions and quotient stacks; moduli problems; deformation theory; log pairs, singularity classes,
stable pairs and the KSBA moduli stack; stable curves and their boundary stratification. The
requirement is definitional: every object exists with its morphisms and at least one proved
theorem; deep theorems (algebraicity, properness and separatedness of moduli, the minimal model
programme) are not requirements (research D2).

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician works with schemes over a base (Priority: P1)

The mathematician forms a scheme over $S$, base-changes it, asks whether a morphism is proper,
flat or finite, forms a variety, a curve or a surface, a coherent or reflexive sheaf, a divisor
and its class, the canonical sheaf, a blowup, a cyclic cover or a finite quotient.

**Why this priority**: every later object of the feature is a scheme or a family of schemes.

**Independent Test**: each construction elaborates at a standard example with its universal
property or defining theorem; a morphism property is stable under composition and base change.

**Acceptance Scenarios**:

1. **Given** the blowup of $\mathbb A^2_k$ at the origin, **When** the mathematician tests its
   universal property, **Then** a morphism along which the ideal becomes invertible factors
   uniquely through it.
2. **Given** a normal surface, **When** the mathematician forms $\omega^{[m]}$, **Then** it is the
   reflexive hull of $\omega^{\otimes m}$.

---

### User Story 2 - A mathematician works with stacks (Priority: P1)

The mathematician forms a category fibred in groupoids over $(\mathbf{Sch}_{/S})_{\mathrm{fppf}}$,
tests the stack condition, forms an algebraic space, an algebraic or Deligne–Mumford stack, a
classifying stack $BG$ and a quotient stack $[X/G]$, and a moduli problem with its fine or coarse
moduli.

**Why this priority**: moduli of stable pairs and the period quotients are stacks (#39, #40).

**Independent Test**: $BG$ and $[X/G]$ are stacks by proved descent; a scheme is an algebraic
space by the fully faithful embedding; a coarse moduli space is not automatically a variety.

---

### User Story 3 - A mathematician states the KSBA moduli problem (Priority: P2)

The mathematician forms a log pair, its discrepancies and singularity class, a stable pair and a
stable family over $T$, and the KSBA moduli fibred category with fixed dimension, coefficient set
and volume, and uses the theorem that it is a stack. The Coble instance is a named predicate on
this general object.

**Why this priority**: the research programme identifies the KSBA compactification of the Coble
moduli with a semitoroidal one (#39, stage 3).

**Independent Test**: the stack condition of the KSBA fibred category is a theorem; a pair that
is not slc is refused as stable.

---

### User Story 4 - A mathematician places stable curves and their boundary (Priority: P3)

The mathematician forms stable marked graphs with contractions, the specialization poset, and the
moduli fibred category $\overline{\mathcal M}_{g,n}$ of stable $n$-pointed curves of genus $g$ with
its stack condition.

**Why this priority**: the boundary stratification is the standard example of the language
(#39, absorbed record).

**Independent Test**: the stable graphs of $\overline{\mathcal M}_{0,4}$ and their contraction
poset elaborate; the stack condition is a theorem.

---

### Edge Cases

- A coarse moduli space truncates automorphisms; it is not the stack.
- An arbitrary stack is not Deligne–Mumford; a constructor does not make an object proper.
- A singularity class needs its complete geometric hypotheses; a pair whose $K_X + \Delta$ is not
  $\mathbb Q$-Cartier has no discrepancies.
- Lifting a point through a square-zero extension and deforming an object are two problems; their
  Ext groups differ by a shift (research D9).
- The name `AnticanonicalQuotient` has no standard referent; no declaration carries it.

## Requirements *(mandatory)*

### Functional Requirements

**Schemes (#38)**

- **FR-001**: Schemes over $S$ MUST be the slice $\mathbf{Sch}_{/S}$ with base change; proper,
  flat, finite, separated, smooth, étale, unramified and locally of finite presentation MUST be
  morphism properties on arrow categories with their stability under composition and base change,
  from Mathlib ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 32.2, 33.1).
- **FR-002**: A variety over a field $k$ MUST be an integral scheme separated and of finite type
  over $k$ (research D3); curves and surfaces MUST be the values at dimension $1$ and $2$ of one
  dimension-parameterized family of proper varieties, dimension being that of the underlying
  space.
- **FR-003**: Coherent sheaves, reflexive sheaves (the isomorphism locus of $F \to F^{\vee\vee}$),
  reflexive powers, Weil and Cartier divisors, $\mathbb Q$-divisors, the divisor class group, the
  Picard group and the canonical and dualizing sheaves MUST be declared, using the corpus owners of
  the Hartshorne units where they exist (research D4).
- **FR-004**: Blowups MUST carry their universal property; cyclic covers MUST carry their
  governing algebra $\bigoplus_i L^{-i}$ and root datum; finite quotients MUST carry their action;
  minimal resolutions of rational double points MUST carry their minimality; covers and families
  MUST be arrow-category loci of the morphism properties $\mathrm{finite} \wedge \mathrm{flat}$ and
  $\mathrm{flat} \wedge \mathrm{proper}$.

**Stacks (#39)**

- **FR-005**: Fibred categories, cartesian morphisms, categories fibred in groupoids over
  $\mathbf{Sch}_{/S}$, descent data, prestacks and stacks for the fppf topology MUST be declared
  over Mathlib (`Functor.IsFibered`, `IsStack`, `fppfTopology`) ([FOUNDATIONS.md](../../FOUNDATIONS.md)
  Def. 31.1–31.6; research D5).
- **FR-006**: Algebraic spaces, algebraic stacks and Deligne–Mumford stacks, representable
  morphisms, diagonals and atlases MUST be declared, with the fully faithful functors
  $\mathbf{Sch}_{/S} \to \mathbf{AlgSp}_{/S} \to \mathbf{DM}_{/S} \to \mathbf{AlgSt}_{/S}$
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 32.1, 33.2–33.4; research D6).
- **FR-007**: Group objects and actions, torsors, $BG$ and $[X/G]$ MUST be declared with the stack
  condition of $BG$ and $[X/G]$ proved ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 34.1–34.4).
- **FR-008**: Moduli problems as pseudofunctors into groupoids, fine moduli objects and coarse
  moduli spaces MUST be declared ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 35.1–35.3).
- **FR-009**: Square-zero extensions, deformation groupoids, the cotangent complex by its universal
  property with Mathlib's ring-level model, and the tangent and obstruction groups of both the
  lifting problem and the deformation of an object MUST be declared through the transitivity
  triangle ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 37.1–37.4, Rem. 37.5; research D9).

**Pairs and KSBA moduli (#39, #9)**

- **FR-010**: Log pairs $(X, \Delta)$, the discrepancy as a function on divisorial valuations with
  the log pullback relation, and the classes klt, plt, lc, dlt, slc, demi-normal and
  $\mathbb Q$-Gorenstein with index MUST be declared from their sources (research D7;
  [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.3, 62.4).
- **FR-011**: A stable pair MUST be a projective slc pair with $K_X + \Delta$ ample; a stable family
  over $T$ MUST be flat and proper with Kollár's condition on the reflexive powers (research D7).
- **FR-012**: The KSBA moduli fibred category with fixed dimension, coefficient set and volume MUST
  be declared over $(\mathbf{Sch}_{/k})_{\mathrm{fppf}}$, and its stack condition MUST be proved
  (research D2, D8).
- **FR-013**: The Coble instance MUST be a predicate on stable pairs: the stable object is the
  singular quotient carrying its $\tfrac14(1,1)$ point, with $2K_S + C \sim 0$ and $C^2 = -4$, and
  the invariants of arXiv:2312.03638 §§5, 7 (research D8).

**Stable curves (#39)**

- **FR-014**: Stable marked graphs, their isomorphisms and contractions, and the specialization
  poset of the boundary MUST be declared; the moduli fibred category $\overline{\mathcal M}_{g,n}$
  of stable curves MUST be declared with its stack condition proved
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 35.4, §38).

**Registry, process**

- **FR-015**: Each category of this feature MUST have its registry row with its structural
  functors; the structural functor $\mathbf{Sch} \to \mathbf{Top}$ is feature 001 FR-023.
- **FR-016 (process)**: Every requirement MUST pass constitution M2, M3, M8 and E1.

### Key Entities

- **Scheme over a base**, **variety**, **divisor**, **reflexive sheaf**.
- **Stack**, **algebraic space**, **algebraic stack**, **quotient stack**, **moduli problem**.
- **Log pair**, **stable pair**, **stable family**, **KSBA moduli fibred category**.
- **Stable marked graph**, **specialization poset**.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| ID | Outcome | Measure |
| --- | --- | --- |
| SC-001 | Universal properties of FR-004 proved | 4 of 4 |
| SC-002 | Stack conditions proved | $BG$, $[X/G]$, KSBA, $\overline{\mathcal M}_{g,n}$ |
| SC-003 | Placeholder fields standing for a property | 0 |
| SC-004 | Categories without a registry row | 0 |
| SC-005 | `sorry` and project axioms | 0 |

## Assumptions

- Feature 002 owns the Hartshorne units (divisors 002 T029, T030; relative Proj T031; projective
  bundles T032; relative differentials T033); this feature consumes their owners.
- Feature 001 owns the registry rows of `cat.schemes`, `cat.schemes_over` and $\mathbf{Sch} \to \mathbf{Top}$.
- This feature is a consumer intake (research D1).
