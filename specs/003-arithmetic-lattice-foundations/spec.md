# Feature Specification: Arithmetic lattice foundations at their natural generality

**Feature Branch**: `003-arithmetic-lattice-foundations` (work lands on `main`)

**Created**: 2026-11-25

**Status**: Planned

**Input**: The vault feature FEATURE-ARITHMETIC-LATTICE-FOUNDATIONS: the plan
PLAN-ARITHMETIC-LATTICE-FOUNDATIONS (8 phases, 27 tasks) and its four theorem programmes
PLAN-ADE-REALIZATION-UNIQUENESS, PLAN-INDEFINITE-LATTICE-CLASSIFICATION, PLAN-SIEGEL-MASS-FORMULA
and PLAN-THETA-SERIES-MODULARITY; the open lattice issues: the roadmap of lattice algebra and
discriminant theory (#7), form categories and intrinsic lattices (#33), duals and discriminant
forms (#34), named lattices and arithmetic invariants (#35), the milestone Lattice arithmetic 0.2
(#51), finite projective modules over Dedekind domains (#105) and the lattice part of finitely
generated groups (#106). Planned only in Spec Kit, with every open point settled in
[research.md](research.md).

Let $R$ be an arithmetic base with fraction field $K$ ([FOUNDATIONS.md](../../FOUNDATIONS.md)
Def. 29.9; research D3). The feature delivers the arithmetic theory of formed modules and lattices
over $R$ at the generality at which this research programme uses it. Each public notion has one
owner. Each specialization (to $\mathbb Z$, to $\mathbb Z_p$, to a basis, to a coordinate
presentation) has a proved comparison with that owner. No definition is weakened to fit a familiar
special case. The theorem programmes (ADE realization, indefinite classification, the mass formula,
theta modularity) consume this one theory and add no second lattice notion.

The common layer is the category of finite projective formed $R$-modules and its value module
[@MH73, §I.1]. A hypothesis (finite projective, integral, fraction-field nondegenerate, Dedekind,
global) enters a construction only where the construction uses it.

## User Scenarios & Testing *(mandatory)*

### User Story 1 - A mathematician uses one owner for each arithmetic lattice notion (Priority: P1)

A mathematician needs a notion of lattice arithmetic: separation and perfection of a form, the
metric $I$-dual $L^{\# I}$, $I$-modularity, the relative discriminant $A_L^I$ with its $K/I$ form,
the determinant line and Steinitz class, the discriminant ideal, a primitive embedding, an
overlattice, a $G$-lattice and its invariant lattice. The mathematician finds one Lean declaration
for the notion, at its general owner, and the theorems that compare it with every specialized form
(the integral ideal dual, the ordinary metric dual, the Gram determinant ideal after a basis is
chosen).

**Why this priority**: Every later construction of this feature (completions, adeles, genus,
invariants, classification, theta series) is built from these owners. Two owners of one notion
force every consumer to choose between them.

**Independent Test**: Take a notion from the owner table of [data-model.md](data-model.md). Its
row names one declaration and one module. Each specialization in the row has a theorem that
identifies it with the owner under its stated hypotheses. The axiom audit admits only the standard
axioms.

**Acceptance Scenarios**:

1. **Given** a $W$-valued bilinear form that is not symmetric, **When** the mathematician asks
   whether it is nondegenerate, **Then** the answer uses both correlation maps $\lambda_b$ and
   $\rho_b$, and the one-radical form is a theorem for symmetric forms.
2. **Given** an integral lattice $L$ and $I = R$, **When** the mathematician forms $L^{\# I}$,
   **Then** a theorem identifies it with the metric dual $L^{\#}$, and unimodularity is
   $L^{\# R} = L$; its equivalence with perfection of $L \to L^*$ is a separate theorem with the
   finite projective hypothesis.
3. **Given** a free lattice with a chosen basis, **When** the mathematician compares the intrinsic
   discriminant ideal with the Gram determinant ideal, **Then** a theorem gives the equality.

---

### User Story 2 - A mathematician works with completions, adeles and genus (Priority: P1)

A mathematician localizes and completes a lattice at a height-one place, forms its ring-adelic
realization $L_{\mathbb A_R} = L \otimes_R \mathbb A_R$, and asks whether two lattices are in one
genus. Genus is isometry after base change to $\mathbb A_R$. The placewise criterion, the
real-plus-$p$-adic criterion over $\mathbb Z$ and the orthogonal double-coset description are
theorems about that definition, not other definitions.

**Why this priority**: Genus, spinor genus, mass and the local classification all start from the
ring-adelic genus. A placewise definition would make each of them a theorem about a different
object.

**Independent Test**: For $R = \mathbb Z$, the comparison theorem identifies the ring-adelic genus
with isometry over $\mathbb R$ and over every $\mathbb Z_p$. For a general arithmetic base, the
componentwise characterization holds under the finite projective hypothesis. The double-coset
theorem identifies the classes in a genus with
$O(V)(K)\backslash O(V)(\mathbb A_{K,f})/K_L$.

**Acceptance Scenarios**:

1. **Given** a lattice over $\mathbb Z$, **When** its genus is computed, **Then** the definition
   is the ring-adelic one and the $\mathbb R \times \prod_p \mathbb Z_p$ formula is a theorem.
2. **Given** a finite place $v$, **When** the mathematician completes $L$, **Then** the result is
   an $R_v$-lattice with the comparison maps $R \to R_{\mathfrak p} \to R_v$ and
   $K \to K_v$, and the $\mathbb Z_p$ construction is its specialization.

---

### User Story 3 - A mathematician uses canonical local invariants and the local classification (Priority: P2)

A mathematician needs the Hasse invariant, the spinor norm, the spinor genus, Jordan
decompositions and the dyadic invariants. Each invariant belongs to the isometry class or to the
quadratic space. A diagonal formula, a reflection formula or a witness structure is a theorem about
the canonical invariant.

**Why this priority**: Chosen diagonalizations and chosen homomorphisms make every consumer depend
on a choice. The canonical owner removes the choice.

**Independent Test**: The Hasse invariant of an isometry class does not depend on a
diagonalization, and the diagonal formula $\prod_{i<j}(a_i,a_j)$ is a theorem. The spinor norm is a
homomorphism $O(V,q) \to K^\times/(K^\times)^2$ with its reflection formula proved. A dyadic local
lattice has a Jordan decomposition with its Type I and Type II constituents.

**Acceptance Scenarios**:

1. **Given** two diagonalizations of one quadratic space, **When** the Hasse invariant is read
   from each, **Then** the two values agree by a theorem.
2. **Given** a local lattice at a place of residual characteristic 2, **When** the mathematician
   asks for its classification data, **Then** the scale, norm, Jordan constituents and dyadic
   invariants exist at their owners, and the $\mathbb Z_2$ declarations are their special cases.

---

### User Story 4 - A mathematician uses signature loci and the analytic realization (Priority: P2)

A mathematician restricts to definite, indefinite, totally definite or Lorentzian lattices, uses
reflections and root systems, embeds a lattice in its real span, and builds a complex torus or a
period domain from a lattice with Hodge data. Each locus is a full subcategory of the one lattice
category. The quotient $V_{\mathbb C}/L$ exists only after complex or Hodge data is supplied; the
torsion module $L_K/L$ is a different object.

**Why this priority**: The geometric consumers (K3 lattices, period domains, abelian varieties) and
the theorem programmes need these loci and realizations. A second lattice notion for any of them
would split the theory.

**Independent Test**: Every locus is an `ObjectProperty.FullSubcategory` of the lattice category
with its sign convention stated. The named lattices $U$, $E_8$ (negative definite), $U^{\perp n}$
and $\Lambda_{K3} = U^{\perp 3} \perp E_8^{\perp 2}$ come from generic constructions, and their
rank, signature, parity and discriminant follow from generic theorems.

**Acceptance Scenarios**:

1. **Given** a lattice over a number ring with real places, **When** the mathematician asks for
   its signature, **Then** a signature $(r_v, s_v)$ exists at each real place $v$.
2. **Given** an integral lattice with a positive definite real form, **When** the mathematician
   forms its theta series, **Then** each coefficient is a finite count, and a theorem compares the
   series with Mathlib's analytic theta function.

---

### User Story 5 - A mathematician uses the theorem programmes on the common layer (Priority: P3)

A mathematician cites a theorem of the four programmes: realization independence and uniqueness of
the ADE lattices; strong approximation, spinor genera and the Eichler criterion for indefinite
lattices; the Smith–Minkowski–Siegel mass formula; the modular transformation laws of theta series.
Each theorem is stated about the definitions of User Stories 1–4.

**Why this priority**: These programmes consume the foundation. They do not change it.

**Independent Test**: Each theorem's statement uses only declarations from the owner table, and
its hypotheses are explicit.

**Acceptance Scenarios**:

1. **Given** two cited root realizations of one ADE type, **When** their root lattices are
   compared, **Then** a theorem gives an isometry after the project's negative sign convention.

---

### Edge Cases

- $R$ is a Dedekind domain that is not a principal ideal domain. A finite projective lattice need
  not be free; no statement assumes a global basis. Its Steinitz class can be nontrivial.
- A place has residual characteristic 2. Bilinear and quadratic structures differ there; no
  definition divides by 2 without an invertibility hypothesis.
- A residue ring is infinite (for example over a function field with infinite constant field). A
  statement about cardinality, a finite automorphism group or an enumeration carries the finiteness
  hypothesis on the residue rings ([FOUNDATIONS.md](../../FOUNDATIONS.md) Rem. 65.7).
- An arithmetic base has no real place (a function field). The full ring adeles have no
  archimedean factor; signature statements do not apply.
- The integral correlation map $L \to L^*$ becomes an isomorphism over $K$. It has torsion
  cokernel, so it is a full-rank embedding; it is primitive only when it is an isomorphism.
- A consumer needs one of these notions before this feature's position in the work order. The
  consumer does the task of this feature that owns it at once, under constitution M9 (research D2).

## Requirements *(mandatory)*

### Functional Requirements

**Formed modules and separation**

- **FR-001**: A $W$-valued bilinear form MUST have a left correlation map $\lambda_b$ and a right
  correlation map $\rho_b$, a left and a right radical, and left and right separation predicates.
  Nondegeneracy MUST mean that both radicals vanish. For a symmetric form a theorem MUST identify
  the two conditions before one radical represents them.
- **FR-002**: Perfection MUST mean that the correlation maps are isomorphisms. Fraction-field
  nondegeneracy and fraction-field perfection MUST be separate predicates; their equivalence for
  scalar-valued symmetric forms on finite projective modules over a domain MUST be a theorem.
  Radical-freeness, perfection and the defect module MUST be positions in the defect package
  $0 \to \operatorname{rad} \to M \to \operatorname{Hom}(M, W) \to \operatorname{Def} \to 0$
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 54.2, Ex. 54.3, Conv. 64.12).
- **FR-003**: The category of intrinsic $R$-lattices MUST be the locus of finite projectivity,
  integrality, symmetry and fraction-field nondegeneracy in the formed-module category
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 19.2). The fixed-value category, the variable-value
  category, the framed, coordinate, arbitrary-index, symmetric-matrix and Gram presentations MUST
  each have an explicit fibre, forgetful or comparison functor to it.

**Duality, discriminants and determinants**

- **FR-004**: For a fractional ideal $I$ of $R$, the metric $I$-dual
  $L^{\# I} = \{x \in L_K \mid b_K(x, L) \subseteq I\}$ MUST be one construction, a specialization
  of the value-lattice dual $L^{\#}_{b,W}$; the ordinary metric dual MUST be the case $I = R$ and the
  integral ideal dual the case of an integral ideal, each by a theorem.
- **FR-005**: $I$-modularity MUST be $L^{\# I} = L$, and unimodularity MUST be $R$-modularity. Any
  comparison with perfection of $L \to L^*$ MUST be a theorem with its finite projective and
  fraction-field hypotheses.
- **FR-006**: For $L \subseteq L^{\# I}$, the relative discriminant $A_L^I = L^{\# I}/L$ MUST carry
  a bilinear form with values in $K/I$, and under the evenness and integrality hypotheses a
  quadratic refinement with values in $K/2I$. The two structures MUST stay distinct at residual
  characteristic 2. The comparison of $A_L^R$ with the adjoint defect
  $\operatorname{coker}(L \to L^*)$ MUST be a theorem with the Riesz and finite projective
  hypotheses.
- **FR-007**: The determinant line $\det_R L = \bigwedge^n_R L$, the Steinitz class in
  $\operatorname{Cl}(R)$, the discriminant ideal and the zeroth Fitting ideal of the discriminant
  module MUST have intrinsic owners. Theorems MUST give their localization, orthogonal-sum
  behaviour, the comparison of the class group with the Picard group, and the recovery of the Gram
  determinant ideal after a basis is chosen. The Steinitz classification MUST be stated with its
  hypotheses [@Rot15, Thm. 11.117], with the Steinitz form $P \cong R^{n-1} \oplus I$, the class laws
  of direct sum, dual, tensor product, Hom and base change, and a witness with a nonprincipal
  ideal class (research D30).
- **FR-008**: The PID structure theorem, Smith normal form and Dedekind torsion primary
  decomposition MUST stay with their Mathlib owners; theorems MUST connect them to lattice rank,
  elementary divisors and discriminant modules. No statement MUST assert a global basis of a
  projective nonfree lattice.

**Embeddings, gluing and equivariance**

- **FR-009**: A primitive formed embedding MUST be an injective formed morphism with torsion-free
  cokernel. Orthogonal complements, saturation, isotropic subgroups, overlattices and gluing MUST
  be one formed-module theory, with construction and recovery in both directions and the extension
  criterion for isometries [@Nik80, §§4°–6°].
- **FR-010**: A $G$-lattice MUST be a functor $BG \to \mathbf{Lat}_R^{\simeq}$; for a fixed lattice
  it MUST be equivalent to a homomorphism $G \to O(L)$. Invariant and coinvariant lattices,
  centralizers, normalizers, stabilizers and discriminant actions MUST derive from the generic
  group-action and stabilizer constructions; involutions MUST be the case $G = C_2$.
- **FR-011**: Rational isotypic components MUST use Mathlib's `isotypicComponent`. Under explicit
  semisimplicity hypotheses the integral constituents $L_\lambda = L \cap V_\lambda$ and the finite
  defect of $\bigoplus_\lambda L_\lambda \to L$ MUST be expressed through the gluing theory of
  FR-009, with no integral isotypic decomposition as a primitive.

**Places, completions and adeles**

- **FR-012**: Height-one points of $\operatorname{Spec} R$ MUST index the nonarchimedean places;
  the distinguished places of the arithmetic base MUST be a separate index. Localization, residue
  and completion MUST satisfy the comparison diagram $R \to R_{\mathfrak p} \to R_v$,
  $K \to K_v$; $K_v$ at a distinguished place MUST not be called a completion of $R$.
- **FR-013**: Scalar extension of lattices to $R_v$ and of formed spaces to $K_v$ MUST commute with
  orthogonal sums, ideal duals, discriminant forms, equivariant actions and orthogonal groups under
  stated hypotheses. The $\mathbb Z_p$ and $\mathbb Q_p$ constructions MUST be specializations by
  theorem.
- **FR-014**: Elementary torsion modules MUST be owned by the annihilator condition $IA = 0$ with
  the induced $R/I$-module; a dyadic place MUST be one with $\operatorname{char}(R/\mathfrak p) = 2$.
- **FR-015**: The integral finite adeles $\widehat R = \prod_{v} R_v$ and the full ring adeles
  $\mathbb A_R$ (the local coefficient rings of the distinguished places times $\widehat R$) MUST
  be constructed for an arithmetic base, with the formed module, orthogonal group and lattice
  stabilizer over them, and comparison maps to the field adeles $\mathbb A_K$. For $R = \mathbb Z$
  a theorem MUST give $\mathbb A_{\mathbb Z} \cong \mathbb R \times \prod_p \mathbb Z_p$.

**Genus**

- **FR-016**: Genus MUST be isometry after base change to $\mathbb A_R$; the genus of $L$ MUST be
  the set of global isometry classes, not a homotopy fibre. The placewise, real-plus-$p$-adic and
  double-coset descriptions MUST be theorems. The lattice stabilizer of a projective nonfree lattice
  MUST be compared with local integral bases.

**Canonical invariants and local classification**

- **FR-017**: The Hasse invariant MUST belong to the isometry class of a nondegenerate quadratic
  space over a field with a Hilbert symbol, with values in $\{\pm 1\}$; the diagonal formula
  $\prod_{i<j}(a_i, a_j)$, isometry invariance, orthogonal-sum behaviour and scalar-extension
  comparisons MUST be theorems [@Jac85, §9.9].
- **FR-018**: The spinor norm MUST be the canonical Clifford-theoretic homomorphism
  $\theta : O(V, q) \to K^\times/(K^\times)^2$ [@Cas08a, §10.3]; its kernel and exact-sequence
  statements, reflection formula and local and adelic forms MUST be theorems; no chosen homomorphism
  MUST own it. The spinor genus MUST be defined from the canonical spinorial data over the
  ring-adelic genus, with its equivalence-relation laws proved.
- **FR-019**: Over a discrete valuation ring, scale and norm ideals, modularity, Jordan
  constituents and Jordan decompositions MUST exist with the uniqueness data that survive isometry,
  including the dyadic case (unit square classes, Type I and Type II constituents, oddity-type
  invariants, finite quadratic modules) [@Ger08, §§6.7, 8.1–8.2]. The $\mathbb Z_2$ declarations
  MUST be special cases.

**Signature loci, reflections and named lattices**

- **FR-020**: Each real place $v$ MUST give a signature $(r_v, s_v)$. Positive definite, negative
  definite, totally definite, indefinite and Lorentzian lattices MUST be full subcategories with
  explicit sign conventions; no property defines a second lattice object.
- **FR-021**: Reflections, reflective vectors and reflection subgroups MUST be defined on the
  general lattice category with no definiteness hypothesis. Root bases, Weyl chambers and ADE
  classification MUST be restricted to the definite root-lattice locus, with the project's
  negative-definite convention (research D4).
- **FR-022**: The hyperbolic plane $U$, finite orthogonal powers $U^{\perp n}$, $E_8$ (negative
  definite), $E_8^{\perp n}$, $\Lambda_{K3} = U^{\perp 3} \perp E_8^{\perp 2}$ and the even unimodular
  lattices $\mathrm{II}_{s,t}$ for $s, t \geq 1$, $s \equiv t \pmod 8$ MUST be built by the generic
  operations; their rank, signature, parity and discriminant MUST follow from generic theorems, and
  an even unimodular lattice of signature $(s, t)$ MUST be proved to have $s \equiv t \pmod 8$
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 23.3; research D26). Named ADE lattices MUST come from
  cited root realizations in the order of [FOUNDATIONS.md](../../FOUNDATIONS.md) Conv. 72.3.
- **FR-023**: The comparison $(L, b) \mapsto L \hookrightarrow L_{\mathbb R}$ MUST state its
  finite-rank, embedding and positivity hypotheses and relate determinant ideals to covolumes. The
  quotient $V_{\mathbb C}/L$ MUST be constructed only from complex or Hodge data, and MUST stay
  distinct from the torsion module $L_K/L$.
- **FR-024**: Filtered objects of an abelian category, pure and mixed Hodge structures over
  $\mathbb R$, $\mathbb Q$ and $\mathbb Z$, their tensor, dual, internal Hom and Tate objects,
  polarizations and Hodge isometries MUST have categorical owners (COMPLAINTS.md, "Hodge structures
  need filtered-module categories and their comparison maps"). Type IV period domains MUST be built
  from signature $(2, n)$ lattices with the positive-isotropic-line convention of the source
  ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.3).

**Definite theory and theorem programmes**

- **FR-025**: For a definite genus, the set of classes MUST be proved finite and every lattice
  automorphism group finite; the class number and the mass
  $\sum_{[M]} 1/|O(M)|$ MUST then be defined and compared with the finite adelic double coset.
- **FR-026**: Representation numbers $r_L(n)$ and the theta series $\Theta_L$ of a positive
  definite lattice MUST be compared with Mathlib's analytic theta and Poisson-summation interfaces;
  the modular transformation laws MUST be proved with explicit weight, level and character.
- **FR-027**: The Smith–Minkowski–Siegel mass formula MUST identify the mass with the normalized
  product of local densities under explicit hypotheses, after the real-place factor and the
  fundamental-domain and volume comparison are proved.
- **FR-028**: Isotropic vectors, hyperbolic planes, Witt index, arithmetic orthogonal groups,
  strong approximation (with its group, topology, place set and hypotheses), the Eichler criterion
  and symmetric domains MUST be developed on the indefinite full subcategories, using the canonical
  spinor kernel.
- **FR-029**: Each named ADE lattice MUST have an ordered simple-root basis from diagram
  enumeration, a derived Gram comparison, and realization independence and uniqueness up to
  isometry from the finite root-system classification.

**Form invariants, discriminant functors and Nikulin theory (#33, #34, #35, #105, #106)**

- **FR-034**: The scale $\mathfrak s(b)$, the norm $\mathfrak n(b)$ and the volume $\mathfrak v(L)$
  MUST be functors into the submodules of $W$ (ideals of $R$ for $\mathfrak v$), with the theorems
  $2\mathfrak s \subseteq \mathfrak n \subseteq \mathfrak s$, isometry invariance, integrality as
  $\mathfrak s \subseteq R$, evenness of an integral form as $\mathfrak n \subseteq 2R$, and
  $\mathfrak a$-modularity as $\mathfrak a L^{\#} = L$; the twist $L(a)$ and the ideal multiple
  $\mathfrak a L$ MUST be distinct operations with $\mathfrak s(L(a)) = a\,\mathfrak s(L)$,
  $\mathfrak s(\mathfrak a L) = \mathfrak a^2 \mathfrak s(L)$, $(\mathfrak a L)^{\#} = \mathfrak a^{-1} L^{\#}$ and
  $L \otimes_R \mathfrak a \cong \mathfrak a L$ for invertible $\mathfrak a$ (research D27).
- **FR-035**: The diagonal $D(b)(x) = b(x, x)$ and the polarization $P(q) = \partial q$ MUST be
  natural in the value module with $P \circ D = 2$ on symmetric forms and $D \circ P = 2$; the even
  forms MUST be $\operatorname{im}(P)$ with the refinement fibre $\operatorname{Ref}(b) = P^{-1}(b)$
  and the theorem $\operatorname{im}(P) \subseteq \{b : b(x, x) \in 2W\}$ with equality for
  2-torsion-free $W$; skew-symmetric, alternating and symmetric forms MUST be separate classifiers
  with the implications that depend on the 2-torsion of $W$ ([FOUNDATIONS.md](../../FOUNDATIONS.md)
  §§16–17).
- **FR-036**: The invariant $\ell(A) = \max_{\mathfrak p} \dim_{R/\mathfrak p} A/\mathfrak p A$ of a
  finite-length torsion module MUST be declared with $\ell(A) = \max_{\mathfrak p} \ell(A_{\mathfrak p})$,
  its subadditivity, and its monotonicity along monomorphisms and epimorphisms; the invariant
  $(r, a, \delta)$ MUST be declared on even $p$-elementary lattices (research D28).
- **FR-037**: The discriminant functors $\operatorname{disc}_b : \operatorname{Core}(\mathbf{Lat}_{\mathbb Z}) \to \operatorname{Core}(\mathbf{DiscBil})$
  and $\operatorname{disc}_q : \operatorname{Core}(\mathbf{EvenLat}_{\mathbb Z}) \to \operatorname{Core}(\mathbf{DiscQuad})$,
  the polarization $\mathbf{DiscQuad} \to \mathbf{DiscBil}$ through $\mathbb Q/2\mathbb Z \cong \mathbb Q/\mathbb Z$
  and the commuting square MUST be declared; the embedding $\langle 2 \rangle \hookrightarrow
  \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ MUST be a test that no covariant map of discriminant
  groups exists ([FOUNDATIONS.md](../../FOUNDATIONS.md) §26).
- **FR-038**: Nikulin's results MUST be proved as read from [@Nik80]: Cor. 1.9.4 (signature and
  discriminant quadratic form determine the genus of an even lattice), Thm. 1.10.1 and Cor. 1.10.2
  (existence), Thm. 1.13.2, Cor. 1.13.3 and Cor. 1.13.4 (uniqueness in the genus), Thm. 1.14.2
  ($O(L) \to O(q_L)$ surjective for an even indefinite $L$ with $\operatorname{rk} L \geq \ell(A_L) + 2$),
  with signature and discriminant form as monoid homomorphisms on genera under $\perp$
  (research D29).
- **FR-039**: The subgroups $SO(L)$, $\widetilde O(L) = \ker(O(L) \to O(A_L, q_L))$ with the image of
  that map, $O^+(L)$ by the real spinor norm, $SO^+(L)$, $\widetilde{SO}(L)$ and $\widetilde{SO}^+(L)$
  MUST be declared from the generic constructions; the positive-cone description of $O^+(L)$ MUST
  be a theorem under its hyperbolic hypotheses; generators of a subgroup MUST be given only when
  constructed (#106).

**Surface, records and checks**

- **FR-030**: The root import module MUST expose only canonical owners, precisely named
  specializations with comparison theorems, or neither. Task T038 proves the comparison theorem of
  each root-imported declaration with its canonical owner, after the tasks T001–T037 that construct
  those owners; a declaration with no comparison theorem and no name that states its restricted
  meaning MUST be outside the root surface.
- **FR-031**: Every definition and proof obligation MUST be searched before it is written
  (constitution M8), with the reference ports of research D24; every workaround MUST carry the
  five fields of LC-12, and every missing theorem MUST be filed under LC-11.
- **FR-032**: Each change MUST pass tier 1; each phase MUST end with `just test`; the library MUST
  hold no `sorry` and no project axiom (constitution M3, E1).
- **FR-033**: The open lattice and form items of research D25 MUST be closed at their owners:
  the orthogonal-sum symmetric monoidal structure on quadratic modules, the $\Gamma_2$
  representability of quadratic maps and Roby's base change, the characterization of cocartesian
  morphisms in a Grothendieck construction by invertible fibre parts, the argument half of Milgram's
  formula, the transport of $O(L)$ along the sign twist $L \mapsto L(-1)$, the coordinate-free
  Lorentz cone, and the infinitude of $O(L)$ for indefinite lattices from a read source (research
  D21).

### Key Entities

- **Arithmetic base**: an integral model $R \subset K$ with distinguished places and their local
  coefficient rings (FOUNDATIONS Def. 29.9).
- **Formed module**: $(M, W, b)$ with $b : M \otimes_R M \to W$; the lattice category is a locus in
  the formed-module category.
- **Owner row**: a notion, its owning declaration and module, its generality, its specializations
  and their comparison theorems ([data-model.md](data-model.md)).
- **Place**: a height-one point of $\operatorname{Spec} R$ or a distinguished place, with its local
  ring or field.
- **Genus class set**: the set of global isometry classes of lattices adelically isometric to $L$.

## Success Criteria *(mandatory)*

### Measurable Outcomes

| Outcome | Start (`533e9259`) | Target |
| --- | --- | --- |
| Notions of the owner table with one owner and every comparison proved | see [plan.md](plan.md#current-source-state) | all |
| Public root-imported lattice declarations without owner or comparison | not counted | 0 |
| Chosen-data owners of invariants (diagonal Hasse value, chosen spinor norm) | 2 | 0 |
| Theorem programmes with their success criteria met | 0 of 4 | 4 of 4 |
| Nikulin results of FR-038 proved | not counted | 7 of 7 |
| `sorry` and project axioms in the library | 0 | 0 |

- **SC-001**: For every notion of the owner table, a mathematician finds its owner and every
  specialization's comparison theorem from the table alone.
- **SC-002**: No definition of this feature divides by 2 without an invertibility hypothesis.
- **SC-003**: Genus, spinor genus, mass and local classification are stated about the ring-adelic
  genus.
- **SC-004**: Every named lattice's rank, signature, parity and discriminant is a consequence of
  generic theorems, not a computation stored in its definition.

## Assumptions

- Feature 002 reaches Milestone 2 (002 T086) before the first task of this feature; this feature
  then runs as 002 T107 (research D2).
- Feature 001 registers the semantic-registry rows of the lattice loci (001 T057–T062); this
  feature owns their mathematics and registers no row that 001 owns.
- The live library holds the cited sources ([@MH73], [@Nik80], [@Rot15], [@Wei82], [@Ger08],
  [@Jac85], [@Cas08a], [@Hum90], [@Bou08], [@Sch21], [@Mor19], [@LZ16], [@PK16], [@CS88], [@Ros21],
  [@Tel22]) and the sources that tasks T036, T043 and T046 name; a source that a worker cannot
  reach is made reachable, or added to the library, first (002 research D16), then read.
