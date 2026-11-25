# Feature Specification: Reflection, fan and toric geometry

**Feature Branch**: `006-reflection-and-toric-geometry` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The roadmap of reflection, fan and toric geometry (#8), Wythoff coarsening and toric
realization (#24) and the folding of a Lorentzian chamber (#116), with every open point settled
in [research.md](research.md). The chambers, walls and Coxeter diagrams (#23), the positive cone
and the reflection group (#36) and rational cones and fans (#37) are on `main`; this feature
builds on them.

The geometric passage from lattices to toric varieties runs: reflections and chambers of a
Lorentzian lattice; the folding of a chamber along a diagram involution; the Wythoff coarsening
of the Coxeter fan along its folding data; the toric scheme of a fan. Each step is a principled
construction with a proved theorem, stated at its natural generality
([FOUNDATIONS.md](../../FOUNDATIONS.md) §§58–60).

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician folds a Lorentzian chamber (Priority: P1)

For an even lattice $M$ of signature $(1, n)$ and an involution $\sigma$ of $M$ that preserves a
chamber of $W(M)$, the mathematician names the fixed sublattice $M^\sigma$, the folded root set
and its Coxeter diagram, and uses the theorem that relates the folded set to the walls of a
chamber of the reflection group of $M^\sigma$.

**Why this priority**: the research programme obtains the diagrams of its fixed lattices from
folding (#116, stage 5).

**Independent Test**: the folding test module elaborates the construction and the theorem at a
published folded diagram.

**Acceptance Scenarios**:

1. **Given** a folded diagram of Alexeev–Engel–Garza–Schaffler (arXiv:2312.03638), **When** the
   mathematician applies the construction, **Then** the folded root set and its diagram are the
   published ones.

---

### User Story 2 - A mathematician runs Vinberg's algorithm with a certificate (Priority: P2)

The mathematician supplies a Lorentzian reflection datum and a bound. The computation returns a
walled fundamental chamber with its proof, or no answer.

**Why this priority**: chamber computations feed the Coxeter fans; termination is not a theorem
that the foundation owes (#8).

**Independent Test**: at the datum of $E_{10}$ the computation returns the chamber of the source;
at a bound that is too small it returns no answer.

---

### User Story 3 - A mathematician coarsens a Coxeter fan along folding data (Priority: P2)

The mathematician forms the Wythoff coarsening of the Coxeter fan of a chamber along its folding
data: a rational fan, invariant under the group and locally finite.

**Why this priority**: the research programme needs refinements and coarsenings of the Coxeter
fans at the Baily–Borel cusps (#24, stage 3).

**Independent Test**: the coarsening is a functor from folded chamber data to fans; its
invariance and local finiteness are theorems.

---

### User Story 4 - A mathematician realizes a fan as a toric scheme (Priority: P2)

The mathematician forms the affine toric scheme $U_\sigma = \operatorname{Spec} k[\sigma^\vee \cap M]$
of a cone, the toric scheme $X_\Sigma$ of a fan as the colimit of its affine pieces, and the toric
morphism of a morphism of fans.

**Why this priority**: the toric realization of the coarsened fans is the last step of the
passage (#24).

**Independent Test**: a face inclusion gives an open immersion; the fan of $\mathbb P^2$ gives
$\mathbb P^2_k$; a fan morphism gives a toric morphism and composition is preserved.

---

### Edge Cases

- The Gram matrix $\begin{pmatrix} -2 & 0 & 2 \\ 0 & -2 & 1 \\ 2 & 1 & -2 \end{pmatrix}$ has
  determinant $2$ and signature $(1, 2)$; under the negative-definite convention it is
  $U \perp A_1$, not $U \perp A_1(-1)$.
- An all-$(-2)$ diagram with an edge of label $4$ is not realizable; root norms differ.
- The ample cone is open and omits $0$; it is not a pointed cone.
- A semifan is not a primitive of this feature ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.5).

## Requirements *(mandatory)*

### Functional Requirements

- **FR-001 (#116)**: For an even lattice $M$ of signature $(1, n)$ and an involution $\sigma$ of
  $M$ preserving a chamber of $W(M)$, the fixed sublattice $M^\sigma$ (research D1), the folded
  root set, its Coxeter diagram and the theorem of the source that identifies the folded set with
  the walls of a chamber of the reflection group of $M^\sigma$ MUST be declared, with the
  statement read from the source (constitution M2).
- **FR-002 (#116)**: One worked declaration MUST reproduce a published folded diagram of
  arXiv:2312.03638.
- **FR-003 (#8)**: Vinberg's algorithm MUST be a total computation on a Lorentzian reflection
  datum with a bound, returning a walled fundamental chamber with its proof or no answer; no
  termination claim MUST be made ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 60.5; research D2).
- **FR-004 (#8)**: The correspondence of elliptic subdiagrams of order $k$ with $k$-faces and of
  parabolic subdiagrams with ideal vertices MUST be a theorem about the chambers of #23.
- **FR-005 (#24)**: The Wythoff coarsening MUST be a functor from folded chamber data to rational
  fans, with group invariance and local finiteness as theorems, and its referent fixed by
  research D3.
- **FR-006 (#24)**: For a rational polyhedral cone $\sigma$, $U_\sigma = \operatorname{Spec} k[\sigma^\vee \cap M]$
  MUST be declared with the open immersion $U_\tau \hookrightarrow U_\sigma$ of a face
  $\tau \preceq \sigma$ ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 59.1).
- **FR-007 (#24)**: The toric scheme $X_\Sigma = \operatorname{colim}_{\sigma \in \Sigma} U_\sigma$
  MUST be the colimit over the face diagram, and $\Sigma \mapsto X_\Sigma$ MUST be a covariant
  functor from fans to schemes over $k$ (research D4; [FOUNDATIONS.md](../../FOUNDATIONS.md)
  Def. 59.2).
- **FR-008 (#8)**: For a Looijenga pair $(Y, D)$ with $n$ components, the charge
  $Q(Y, D) = 12 - D^2 - n$ MUST be defined, with the theorems that a corner blowup preserves it
  and an interior blowup raises it by one (research D6).
- **FR-009**: Each category of this feature (folded chamber data, fans, toric schemes, Looijenga
  pairs) MUST have its registry row with its structural functors (constitution M7).
- **FR-010 (process)**: Every requirement MUST pass constitution M2, M3, M8 and E1.

### Key Entities

- **Folded chamber datum**: $(M, \sigma, C)$ with $\sigma$ preserving the chamber $C$.
- **Walled fundamental chamber**: a chamber with its walls and the proof that they bound it.
- **Fan**, **toric scheme**, **Looijenga pair**: as in FOUNDATIONS §§58–59 and research D6.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| ID | Outcome | Measure |
| --- | --- | --- |
| SC-001 | Folding theorem and worked example | both elaborate in the full build |
| SC-002 | Vinberg results without a proof | 0 |
| SC-003 | Wythoff coarsening laws proved | invariance and local finiteness |
| SC-004 | Toric functor laws proved | identity and composition |
| SC-005 | Categories of this feature without a registry row | 0 |
| SC-006 | `sorry` and project axioms | 0 |

## Assumptions

- Feature 002 task T121 delivers the comparison of the AET families and the Wythoff coarsened
  family (#180, #181); this feature consumes it and builds no second coarsened family.
- This feature is a consumer intake of the research programme (constitution M9); it runs in its
  own document order and does a declaration it needs that another feature's task owns by that task, at once (research D7).
