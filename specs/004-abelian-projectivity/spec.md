# Feature Specification: Abelian projectivity for polarized complex tori

**Feature Branch**: `004-abelian-projectivity` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The vault plan PLAN-ABELIAN-PROJECTIVITY (feature FEATURE-normalized-category-catalogue),
planned only in Spec Kit, with every open point settled in [research.md](research.md).

A complex torus $T = V/\Gamma$ with a Riemann form is an abelian variety in the repository's analytic
sense (`ComplexTorus`, `IsAbelianVariety`, `Lattices/Valued/ComplexTorus.lean`). The feature proves
that such a torus has the intended projective algebraic realization: its positive line bundle has a
power whose theta sections give a closed holomorphic embedding $T \hookrightarrow \mathbb P^N(\mathbb C)$,
and the image is the complex points of a projective variety over $\mathbb C$
(`IsProjectiveVariety`, `Schemes/Varieties.lean`). The chain is: holomorphic line bundles and their
Picard data; the Appell–Humbert classification; theta sections and very ampleness; the Chow
comparison from the analytic embedding to the algebraic variety.

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician uses line bundles and Picard data on a complex manifold (Priority: P1)

A mathematician takes a complex manifold $X$, a holomorphic line bundle $L$ on it, its space of
global sections $H^0(X, L)$, tensor products and duals, and the Picard group $\operatorname{Pic}(X)$
of isomorphism classes. For a complex projective space the hyperplane bundle $\mathcal O(1)$ has the
linear forms as its sections. A closed holomorphic embedding is a holomorphic immersion that is a
homeomorphism onto a closed image.

**Why this priority**: Every later statement of the feature is about these objects.

**Independent Test**: The declarations exist at their owners with their category structure; the
Picard group is the group of isomorphism classes under tensor product; $H^0(\mathbb P^N, \mathcal O(1))$
is identified with the dual of $\mathbb C^{N+1}$ by a theorem.

**Acceptance Scenarios**:

1. **Given** two isomorphic line bundles, **When** their classes in $\operatorname{Pic}(X)$ are compared,
   **Then** they are equal, and the group law is the tensor product.

---

### User Story 2 - A mathematician classifies line bundles on a complex torus (Priority: P1)

A mathematician describes a line bundle on $T = V/\Gamma$ by a hermitian form $H$ on $V$ with
$\operatorname{Im} H$ integral on $\Gamma$ and a semicharacter $\alpha$ for $H$. The Appell–Humbert
theorem identifies the group of pairs $(H, \alpha)$ with $\operatorname{Pic}(T)$.

**Why this priority**: The polarization, the theta functions and the embedding are all read from
$(H, \alpha)$.

**Independent Test**: The map $(H, \alpha) \mapsto L(H, \alpha)$ is a group isomorphism onto
$\operatorname{Pic}(T)$; its composite with the first Chern class gives the Néron–Severi group of
hermitian forms with integral imaginary part.

**Acceptance Scenarios**:

1. **Given** a Riemann form $E$ of the torus (the `IsAbelianVariety` predicate), **When** the
   mathematician forms $H(x, y) = E(ix, y) + iE(x, y)$, **Then** $H$ is positive definite and gives a
   line bundle by Appell–Humbert.

---

### User Story 3 - A mathematician embeds a polarized torus in projective space (Priority: P2)

For a positive definite $H$, the mathematician forms the canonical theta functions, which are the
sections of $L(H, \alpha)$, and proves that the sections of $L^{\otimes 3}$ define a closed
holomorphic embedding into $\mathbb P^N(\mathbb C)$.

**Why this priority**: This is the projective-embedding theorem that the plan exists for.

**Independent Test**: $\dim H^0(T, L(H, \alpha))$ is the Pfaffian of $E$ on $\Gamma$; the map
$T \to \mathbb P(H^0(T, L^{\otimes 3})^\vee)$ is a closed holomorphic embedding.

**Acceptance Scenarios**:

1. **Given** a principal polarization, **When** the mathematician counts sections, **Then**
   $h^0(L) = 1$ and $h^0(L^{\otimes 3}) = 3^g$.

---

### User Story 4 - A mathematician obtains the algebraic variety (Priority: P2)

The mathematician applies Chow's theorem to the image of the embedding and obtains a projective
variety $X$ over $\mathbb C$ with $X(\mathbb C) \cong T$ as complex manifolds.

**Why this priority**: The plan's last criterion: any algebraic-variety conclusion names and proves
its comparison.

**Independent Test**: The theorem states the projective variety, the isomorphism of complex
manifolds and the hypotheses of Chow's theorem.

**Acceptance Scenarios**:

1. **Given** a torus with a Riemann form, **When** the final theorem is applied, **Then** it returns
   an `IsProjectiveVariety` scheme with the stated comparison, and no stack, KSBA, period-map or
   moduli construction is an input.

---

### Edge Cases

- $H$ is positive semidefinite and not definite: the line bundle is not ample; the embedding theorem
  does not apply, and Appell–Humbert still classifies the bundle.
- $\dim V = 1$: every complex torus is an elliptic curve and has a Riemann form; the theorem gives a
  plane cubic model for $L^{\otimes 3}$ of degree 3.
- A complex torus with no Riemann form: the feature makes no projectivity claim; such tori exist for
  $\dim V \ge 2$.

## Requirements *(mandatory)*

### Functional Requirements

- **FR-001**: Holomorphic line bundles on a complex manifold MUST have an owner with morphisms,
  tensor product, dual, pullback along holomorphic maps and the space of holomorphic sections as a
  $\mathbb C$-vector space; the Picard group MUST be the group of isomorphism classes.
- **FR-002**: Complex projective space MUST be a complex manifold with its hyperplane bundle
  $\mathcal O(1)$; closed holomorphic embeddings MUST be defined; a base-point-free line bundle MUST
  give a holomorphic map to $\mathbb P(H^0(X, L)^\vee)$.
- **FR-003**: On $T = V/\Gamma$, the group $\mathcal P(\Gamma)$ of pairs $(H, \alpha)$ (hermitian $H$
  with $\operatorname{Im} H(\Gamma, \Gamma) \subseteq \mathbb Z$, semicharacter $\alpha$ for $H$) and
  the line bundle $L(H, \alpha)$ from its canonical factor of automorphy MUST be constructed; the
  Appell–Humbert theorem MUST be proved with its exact hypotheses, with the exact sequence
  $0 \to \operatorname{Pic}^0(T) \to \operatorname{Pic}(T) \to \operatorname{NS}(T) \to 0$.
- **FR-004**: A theorem MUST compare `IsAbelianVariety` (a Riemann form integral on the period
  lattice) with the existence of a positive definite $H$ in $\operatorname{NS}(T)$, and with the
  weight-one polarized Hodge structure of feature 003 T036.
- **FR-005**: The canonical theta functions MUST be identified with $H^0(T, L(H, \alpha))$, and
  $h^0 = \operatorname{Pf}(E)$ MUST be proved for positive definite $H$.
- **FR-006**: The Lefschetz theorem MUST be proved: for positive definite $H$, $L^{\otimes 3}$ is very
  ample, and its sections define a closed holomorphic embedding $T \hookrightarrow \mathbb P^N(\mathbb C)$.
- **FR-007**: Chow's theorem MUST be proved for closed analytic subsets of $\mathbb P^N(\mathbb C)$,
  and the final theorem MUST give a projective variety $X$ over $\mathbb C$ with an isomorphism of
  complex manifolds $X(\mathbb C) \cong T$.
- **FR-008**: The feature MUST consume the corpus units at their feature 002 owners where they
  deliver a construction of this chain: Peters–Sterk Chapter 16 (FC11-C16-U026 to U032: Jacobian,
  quasi-periodic functions, Riemann theta, theta characteristics) and Beauville Chapter V
  (FC12-C05-U009 to U011: complex tori, projective complex tori as abelian varieties, the Albanese
  property); no second declaration of these objects.
- **FR-009**: Each definition and proof obligation MUST be searched before it is written
  (constitution M8); the library MUST hold no `sorry` and no project axiom (M3).

### Key Entities

- **Complex torus**: `ComplexTorus` of `Lattices/Valued/ComplexTorus.lean`, $V/\Gamma$ with its Lie
  group structure.
- **Appell–Humbert datum**: $(H, \alpha)$ with $H$ hermitian, $\operatorname{Im} H$ integral on
  $\Gamma$, $\alpha$ a semicharacter.
- **Polarization**: a positive definite $H$; principal when $\operatorname{Pf}(E) = 1$.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| Outcome | Start (`533e9259`) | Target |
| --- | --- | --- |
| Success criteria of PLAN-ABELIAN-PROJECTIVITY proved | 0 of 4 | 4 of 4 |
| Inputs of the final theorem that are stack, KSBA, period-map or moduli constructions | 0 | 0 |
| `sorry` and project axioms | 0 | 0 |

- **SC-001**: A mathematician applies one theorem to a complex torus with a Riemann form and obtains
  the projective variety and the comparison of complex manifolds.
- **SC-002**: Each object of the chain has one owner; the FC11 and FC12 units of FR-008 are used at
  their owners.

## Assumptions

- Feature 003 T036 and T037 (Hodge categories, complex tori) are delivered first; this feature runs
  as feature 002 T111 (research D2).
- The complex analytic spaces of feature 002 T125 supply the closed analytic subsets that Chow's
  theorem uses.
- The live library holds the sources of research D4; a source a worker cannot reach leaves its task
  open.
