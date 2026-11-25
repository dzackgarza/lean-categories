# Feature Specification: Manifolds, Hodge theory and period constructions

**Feature Branch**: `008-manifolds-hodge-and-periods` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The epic of manifolds, Hodge theory and period constructions (#40) and the
construction of lattices from varieties (#109), with the period and compactification rulings of
#9, and every open choice settled in [research.md](research.md).

The feature delivers the analytic and Hodge-theoretic language over the lattice and scheme
foundations: the complex-manifold structure of Type-IV domains with their arithmetic groups;
quotient stacks and coarse quotients; local systems, monodromy, markings and variations of Hodge
structure; period maps as morphisms of stacks; Heegner divisors; Baily–Borel, toroidal and
semitoroidal compactifications; Kulikov degenerations and their integral-affine dual complexes;
the integral lattices of a surface (cohomology, Néron–Severi, transcendental and Mordell–Weil
lattices) with their Hodge data. The categories of manifolds (002 T124), complex analytic spaces
(002 T125), Hodge structures (003 T036) and the set-level Type-IV domains (003 T037) are owned by
those tasks; this feature consumes them.

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician forms a period domain and its quotient (Priority: P1)

For an integral lattice $T$ of signature $(2, n)$, the mathematician uses $\Omega_T$ as a complex
manifold with the holomorphic action of $O^+(T)$, an arithmetic subgroup $\Gamma$, the quotient
stack $[\Omega_T/\Gamma]$, its coarse quotient and its Heegner divisors.

**Why this priority**: $[\Omega_{T_{\mathrm{Co}}}/\Gamma_{\mathrm{Co}}]$ is the target of the
period construction of the Coble family (#40, stage 1).

**Independent Test**: $\Omega_T$ is an open subset of the quadric in $\mathbb P(T_{\mathbb C})$
with two components; $\Gamma$ acts properly discontinuously; the quotient stack retains the
stabilizers that the coarse quotient forgets.

---

### User Story 2 - A mathematician forms the period map of a family (Priority: P1)

For a family of polarized varieties whose second cohomology has lattice $T$, the mathematician
forms the local system, its monodromy, the variation of Hodge structure and the period map to
$[\Omega_T/\Gamma]$ (to $\Omega_T$ for a marked family), functorial in base change.

**Why this priority**: the period map is the definitional object of the research programme's
Torelli-type questions; Torelli itself is a theorem about it (#9).

**Independent Test**: the period map of a pulled-back family is the composite of the period map
with the base map.

---

### User Story 3 - A mathematician forms the compactifications (Priority: P2)

The mathematician forms the rational boundary components and the cusp poset of $\Gamma\backslash\Omega_T$,
the Baily–Borel compactification, a toroidal compactification datum and a semitoroidal
compactification from a semifan.

**Why this priority**: the KSBA compactification of the Coble moduli is compared with a
semitoroidal one (#9, stage 3).

**Independent Test**: for $T = U \perp U \perp E_8$ the $0$-dimensional cusps are the
$\Gamma$-orbits of primitive isotropic lines; a semifan satisfies the axiom list of its source.

---

### User Story 4 - A mathematician forms a Kulikov degeneration (Priority: P3)

The mathematician forms a Kulikov degeneration of K3 surfaces over a disc, its monodromy and its
type, and for Type III the integral-affine structure on the dual complex.

**Independent Test**: a Type III monodromy logarithm $N(x) = (x, \lambda)e - (x, e)\lambda$ with
$e$ isotropic, $\lambda \in e^\perp$ and $\lambda^2 \neq 0$ satisfies $N^3 = 0 \neq N^2$.

---

### User Story 5 - A mathematician extracts the lattices of a surface (Priority: P2)

For a smooth projective complex surface $X$ given by equations, the mathematician obtains
$H^2(X, \mathbb Z)/\mathrm{torsion}$ with its cup form, $\operatorname{NS}(X)$ and
$\operatorname{Pic}(X)$ with the intersection form and the cycle class map, the transcendental
lattice, the Hodge decomposition of $H^2(X, \mathbb C)$, the Hodge isometry of an automorphism,
and the Mordell–Weil lattice of an elliptic surface.

**Why this priority**: geometric lattices are the inputs of the lattice programme (#109).

**Independent Test**: $\mathbb P^1 \times \mathbb P^1$ gives the even lattice $U$ and its factor
swap acts by exchanging the two isotropic generators; the blowup of $\mathbb P^2$ at $k$ points
gives the odd lattice $I_{1,k}$.

---

### Edge Cases

- $\Omega_T$ has two components; a choice of component is data, preserved by $O^+(T)$.
- The coarse quotient $\Gamma\backslash\Omega_T$ is in general an orbifold, not a manifold.
- A semifan is not a fan; its axioms are those of its source.
- The restriction of a semitoroidal compactification to a Heegner divisor is not in general the
  semitoroidal compactification of the divisor; no declaration identifies them.
- $\mathbb P^2$ gives the odd unimodular lattice $\langle 1 \rangle$; $\mathbb P^1 \times \mathbb P^1$
  gives the even lattice $U$.

## Requirements *(mandatory)*

### Functional Requirements

**Period domains and quotients (#40)**

- **FR-001**: $\Omega_T$ MUST be a complex manifold, an open subset of the quadric
  $\{(\omega, \omega) = 0\} \subset \mathbb P(T_{\mathbb C})$, with its two components, the
  holomorphic action of $O(T_{\mathbb R})$ and the subgroup $O^+(T)$ preserving a component
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.3; research D2).
- **FR-002**: For an arithmetic subgroup $\Gamma \subseteq O^+(T)$, the quotient stack
  $[\Omega_T/\Gamma]$ over complex analytic spaces MUST be declared as the primary quotient, and
  the coarse quotient $\Gamma\backslash\Omega_T$ as the locally ringed space of $\Gamma$-invariant
  holomorphic functions ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.4; research D3).
- **FR-003**: Heegner divisors MUST be declared with their norm, divisibility and orbit labels
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.6).

**Variations and period maps (#40, #9)**

- **FR-004**: Local systems, the monodromy representation of a local system on a connected,
  locally simply connected space, and markings of a family MUST be declared.
- **FR-005**: A polarized variation of Hodge structure on a complex manifold MUST be a local
  system with a holomorphic Hodge filtration satisfying Griffiths transversality and a flat
  polarization (research D4).
- **FR-006**: The period map of a family MUST be a morphism of stacks from the moduli stack of the
  family to $[\Omega_T/\Gamma]$ induced by the Hodge filtration, with $\Omega_T$ as target for a
  marked family, functorial under base change ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.5;
  research D5).
- **FR-007**: The lattice $T_{\mathrm{Co}}$, the monodromy group $\Gamma_{\mathrm{Co}}$ and
  $[\Omega_{T_{\mathrm{Co}}}/\Gamma_{\mathrm{Co}}]$ as the target of the period map of the Coble
  family MUST be declared from their source (research D6).

**Compactifications (#40, #9)**

- **FR-008**: The rational boundary components (primitive isotropic lines and planes), the cusp
  poset and the Baily–Borel compactification as the Proj of the graded ring of $\Gamma$-modular
  forms MUST be declared ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.1; research D7).
- **FR-009**: A toroidal compactification datum MUST be an admissible $\Gamma$-invariant rational
  polyhedral decomposition at every $0$-dimensional cusp, compatible under incidence
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.2).
- **FR-010**: Semifans and the semitoroidal compactification MUST be declared with the axiom list
  of their source (research D8; [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.5, Rem. 62.7).

**Degenerations (#40, #9)**

- **FR-011**: Kulikov degenerations of K3 surfaces over a disc, their monodromy, its logarithm and
  their type by nilpotency MUST be declared ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.5).
- **FR-012**: The dual complex of a Type III degeneration with its integral-affine structure with
  singularities MUST be declared, using the integral-affine owners of feature 002 T124
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.6).

**Lattices from varieties (#109)**

- **FR-013**: For a smooth projective complex surface: $H^2(X, \mathbb Z)/\mathrm{torsion}$ with
  the cup form, $\operatorname{NS}(X)$ and $\operatorname{Pic}(X)$ with the intersection form and
  the cycle class map, the transcendental lattice $\operatorname{NS}(X)^\perp$, the Hodge
  decomposition of $H^2(X, \mathbb C)$ as a polarized Hodge structure of weight $2$, and the
  Hodge isometry induced by an automorphism MUST be declared, with the examples of research D9.
- **FR-014**: The Mordell–Weil lattice of an elliptic surface with a section MUST be declared by
  Shioda's height pairing, with the example of research D9.

**Registry, process**

- **FR-015**: Each category of this feature MUST have its registry row.
- **FR-016 (process)**: Every requirement MUST pass constitution M2, M3, M8 and E1.

### Key Entities

- **Type-IV domain**, **arithmetic quotient stack**, **Heegner divisor**.
- **Local system**, **marking**, **polarized variation of Hodge structure**, **period map**.
- **Cusp**, **Baily–Borel compactification**, **toroidal datum**, **semifan**.
- **Kulikov degeneration**, **integral-affine dual complex**.
- **Néron–Severi lattice**, **transcendental lattice**, **Mordell–Weil lattice**.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| ID | Outcome | Measure |
| --- | --- | --- |
| SC-001 | Period maps defined as morphisms of stacks | general and Coble |
| SC-002 | Compactification constructions declared | Baily–Borel, toroidal datum, semitoroidal |
| SC-003 | Surface examples of FR-013 | 2 of 2 |
| SC-004 | Categories without a registry row | 0 |
| SC-005 | Deep theorems stated as axioms | 0 |
| SC-006 | `sorry` and project axioms | 0 |

## Assumptions

- Feature 002 T124 (manifold categories, integral-affine atlases), T125 (complex analytic spaces),
  T043 (FC11-C19-U030, variation of Hodge structure over $D(\Lambda)$), T044 (FC11-B-U016, the
  class of a divisor) and T049 (FC12-C01-U008, intersection product), feature 003 T036 and T037
  and features 006 and 007 supply the inputs that the tasks name.
- The requirement is definitional (research D1); Torelli, surjectivity of the period map,
  finite generation of the ring of modular forms, extension of period maps and the comparison of
  arXiv:2312.03638 Thm. 1.1 are not requirements.
