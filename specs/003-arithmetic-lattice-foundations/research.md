# Research: decisions of the arithmetic lattice feature

Each decision settles an open point of the vault plans of FEATURE-ARITHMETIC-LATTICE-FOUNDATIONS
or a conflict between them and the repository's governing documents. Each names its source. The
tasks cite decisions by number. The vault records are cited by card ID; they are superseded by
this feature and kept as provenance.

## D1. One feature for the foundation and the four theorem programmes

**Decision**: This feature carries PLAN-ARITHMETIC-LATTICE-FOUNDATIONS and the four plans that
depend on it (ADE realization uniqueness, indefinite classification, Siegel mass formula, theta
modularity). The theorem programmes are the last phases. Their order among themselves is
scheduling precedence only: ADE uniqueness does not imply indefinite classification, and so on.

**Source**: FEATURE-ARITHMETIC-LATTICE-FOUNDATIONS ("one common prerequisite spine and four
downstream theorem branches"; the `plans` order is "scheduling precedence, not a claim that ...
implies"); the programme rule that all planning is in Spec Kit.

## D2. Position in the work order and consumer intake

**Decision**: The tasks of this feature are executed as task T107 of feature 002, in document
order (constitution M11). Their mathematical inputs are Milestone 2 (002 T086) and the exact theorem
units that a task names; completion of Sweep IV is not an input, only an earlier position in the
work order (002 D11). A consumer that needs a notion of this feature does the task of this feature
that owns it at once, out of document order (constitution M9); the task keeps its place and ID, and
no second task is written for it. A consumer request that no task of this feature holds is a task
of 002 Phase 2.

**Source**: 002 research D11 and D22; constitution M9, M11; the vault plan's description
("consume only the specific theorem units each construction actually needs rather than blocking on
the entire foundational theorem sweep").

**Supersedes**: the vault cards' statement that `TODO.md` owns the execution order.

## D3. The base ring

**Decision**: Module-theoretic and finite-place constructions take a Dedekind domain $R$ with
fraction field $K$ ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 19.1). Constructions that need all
places (the full ring adeles, signatures at real places, the mass) take an arithmetic base: an
integral model $R \subset K$ with distinguished places and their local coefficient rings (FOUNDATIONS
Def. 29.9, `ArithmeticBase.lean`). Number rings, rings of $S$-integers and coordinate rings of
affine curves are instances. The plan's "number-field and global-function-field formulations kept
separate where their infinite-place theories differ" is the distinguished-place datum of the base,
not a second owner.

**Source**: FOUNDATIONS Def. 19.1, Def. 29.9; the vault plan ("A bare Dedekind domain does not
supply the required archimedean place data; the full formula requires a specified global or
number-ring context"); TASK-FULL-ADELIC-NUMBER-FIELD-REALIZATION.

## D4. Sign convention of the named lattices

**Decision**: All ADE lattices are negative definite. $E_8$ is the negative definite even
unimodular lattice of rank 8, and $\Lambda_{K3} = U^{\perp 3} \perp E_8^{\perp 2}$. The positive
definite copy is $-E_8 = E_8(-1)$. Root classification uses norm $-2$ roots; positive definite
statements of a source are compared through $L \mapsto L(-1)$.

**Source**: FOUNDATIONS Def. 23.2, Conv. 23.4, Conv. 64.9, Conv. 71.5; the vault trap
"agents keep shoehorning positive-definite ADE conventions back in: E8 is always negative definite
here".

**Supersedes**: TASK-STANDARD-LATTICES-GENERIC-CONSTRUCTIONS ("Build $E_8(-1)^n$", "Define
$L_{K3} = U^3 \perp E_8(-1)^2$"); the wording
"positive-definite root-lattice locus" of TASK-REFLECTION-ROOT-CLASSIFICATION, which becomes "the
definite root-lattice locus".

## D5. Separation, perfection and the lattice category

**Decision**: A $W$-valued form has two correlation maps and two radicals; nondegenerate means
both vanish, perfect means both correlation maps are isomorphisms (FR-001, FR-002). The lattice
category requires fraction-field nondegeneracy (FOUNDATIONS Def. 19.2). The present Lean predicate
`IsFractionFieldPerfect` is fraction-field perfection; its equivalence with fraction-field
nondegeneracy for scalar-valued symmetric forms on finite projective modules over a domain is a
theorem (the scalar extension is a finite-dimensional $K$-vector space). The earlier name
`IsGenericallyNondegenerate` is absent from the source at `533e9259`, so no rename task remains.

**Source**: the vault plan, "Separation, perfection, and the generic fiber"; FOUNDATIONS Def. 18.1–18.4,
19.2, Conv. 64.8; `Lattices/Valued/MetricDual.lean`.

## D6. FOUNDATIONS already states the corrected owners

**Decision**: FOUNDATIONS states unimodularity as $L^{\# R} = L$ (Def. 18.3, 19.5), genus by
ring-adelic isometry (Def. 29.2) and the value-lattice dual (Def. 24.3). The plan's instruction to
revise FOUNDATIONS is therefore met in content. Tasks of this feature update only the "Lean
realization status" paragraphs that their work changes. A change of mathematical content in
FOUNDATIONS goes to the mathematician (constitution M10; FOUNDATIONS is the content owner,
constitution "Governance").

**Source**: FOUNDATIONS at `533e9259`; TASK-CANONICAL-PUBLIC-LATTICE-SURFACE; constitution M10 and
Governance.

## D7. The metric $I$-dual owner

**Decision**: $I$ ranges over the fractional ideals of the Dedekind domain $R$. Over a Dedekind
domain the nonzero finitely generated $R$-submodules of $K$ are exactly the invertible fractional
ideals, so this is the plan's "admissible projective $R$-submodule of $R$ or $K$". The owner is
`fractionalIdealDual` (`Lattices/Valued/IdealDual.lean`); `idealDual` is the integral-ideal case and
`metricDual` the case $I = R$, each by a theorem. The Mathlib `dualSubmodule` generalization with a
variable $I$ is an upstream candidate, not a private fork.

**Source**: the vault plan, "Metric $I$-duality and modularity"; TASK-IDEAL-DUAL-DISCRIMINANT-COMPARISON
(Mathlib `LinearAlgebra/BilinearForm/DualLattice.lean`, verified 2026-08-14); FOUNDATIONS Def. 24.3;
`IdealDual.lean` at `533e9259`.

## D8. Bilinear and quadratic discriminant structures

**Decision**: The bilinear form on $A_L^I$ takes values in $K/I$. The quadratic refinement takes
values in $K/2I$ and exists when $b(x, x) \in 2I$ for $x \in L$ and $L$ is $I$-integral; then
$q(x + L) = b_K(x, x) \bmod 2I$ is independent of the lift. No definition divides by 2. The
$I = R$ case recovers $\mathbb Q/\mathbb Z$ and $\mathbb Q/2\mathbb Z$ over $\mathbb Z$ (FOUNDATIONS
Conv. 64.10).

**Source**: the vault plan; FOUNDATIONS Def. 17.5–17.6, 25.4–25.6, Conv. 64.10.

## D9. Primitive and full-rank embeddings

**Decision**: An embedding is primitive when its cokernel is torsion-free (FOUNDATIONS Def. 28.1).
An embedding that becomes an isomorphism over $K$ has torsion cokernel; if its cokernel is both
torsion and torsion-free it is zero, so the pairing is perfect.

**Source**: the vault plan; FOUNDATIONS Def. 28.1, Prop. 19.4.

## D10. Determinant lines, Steinitz classes and Fitting ideals

**Decision**: `DeterminantLine.lean` owns the determinant line and the Steinitz class (the Picard
class of the determinant line, isometry-invariant); `FittingIdeal.lean` owns the zeroth Fitting
ideal of the discriminant module as the ideal of the determinant of the adjoint. The remaining
work is the comparison $\operatorname{Cl}(R) \cong \operatorname{Pic}(R)$ for a Dedekind domain,
invertibility of $\bigwedge^n P$ for $P$ projective of constant rank $n$, the Steinitz
classification theorem, localization and orthogonal-sum behaviour, and recovery of the Gram ideal.

**Source**: TASK-DETERMINANT-STEINITZ-DISCRIMINANT-IDEAL (upstream gaps verified 2026-08-14: no
Fitting ideals, no Steinitz class, no `ClassGroup`–`Pic` comparison in Mathlib); the two source files
at `533e9259`.

## D11. Ring adeles over an arithmetic base

**Decision**: $\mathbb A_R$ is the product of the local coefficient rings of the distinguished places
with $\widehat R = \prod_{v \in \operatorname{Ht}_1(R)} R_v$. For a number ring this is FOUNDATIONS
Def. 29.1 and the present `IntegralAdeleRing`; the general base is a generalization of that owner
with a comparison theorem at $\mathcal O_K$, not a second construction. The integral finite adeles
are the image subring in the field adeles with the restricted-product topology comparison.

**Source**: FOUNDATIONS Def. 29.1, 29.9; TASK-FINITE-ADELIC-LATTICE-REALIZATION (FLT
`integralAdeles`, `tensorPiEquivPiTensor'`, Apache 2.0, port with attribution, no dependency);
FOUNDATIONS Lean realization status of §29.

## D12. Genus is a set of classes

**Decision**: The genus of $L$ is the pointed set of global isometry classes of lattices adelically
isometric to $L$. It is not $\pi_0$ of a homotopy fibre (FOUNDATIONS Prop. 29.3). The placewise and
double-coset descriptions are theorems.

**Source**: FOUNDATIONS Def. 29.2, Prop. 29.3, Rem. 56.3; docs/agents/mathematical-simplicity.md
§2.4 (the genus example of truncation).

## D13. The Hasse invariant

**Decision**: The invariant takes values in $\{\pm 1\}$ with the normalization
$\epsilon(q) = \prod_{i<j}(a_i, a_j)$ for a diagonalization $\langle a_1, \ldots, a_n\rangle$. It is
defined on the isometry class through the existence of a diagonalization and the invariance theorem
of `HasseInvariance.lean` (Cassels, Lemma 2.2). A selected diagonal list does not own it. Reference
implementations: `mariainesdff/HassePrinciple` (Apache 2.0; copy with attribution) and
`roed-math/gq2-lean` (Apache 2.0; port) for the dyadic evaluation.

**Source**: TASK-INTRINSIC-HASSE-INVARIANT; `Hasse.lean`, `HasseInvariance.lean` at `533e9259`;
[@Jac85, §9.9]; [@Cas08a, p. 56].

## D14. The spinor norm and the spinor genus

**Decision**: The canonical spinor norm of `CanonicalSpinorNorm.lean` is the owner. `Spinor.lean`'s
`SpinorNorm` (a chosen homomorphism satisfying the reflection rule) becomes the characterization
theorem of the canonical map and leaves the owner role. The spinor kernel without a chosen norm
(`SpinorGenusAdelic.lean`) stays. The open obligation of FOUNDATIONS Def. 29b.3, symmetry and
transitivity of the spinor-genus relation, needs functorial base change of isometries and is a task.

**Source**: TASK-CANONICAL-CLIFFORD-SPINOR-NORM; FOUNDATIONS Thm. 29b.2, 29b.2b, Def. 29b.3.

## D15. The local classification

**Decision**: Jordan existence for 2 invertible is present (`JordanRecursion.lean`). The remaining
work is the uniqueness data, the Witt and Hasse relation of the generic space, and the dyadic layer
(Type I and Type II, unit square-class filtrations, oddity-type invariants, finite quadratic modules).
`DyadicSquares.lean` and the `roed-math/gq2-lean` dyadic Hilbert symbol are the reusable inputs.

**Source**: TASK-JORDAN-WITT-DYADIC-CLASSIFICATION; FOUNDATIONS Thm. 29b.6, Def. 29b.5.

## D16. Signatures and loci

**Decision**: Signatures are indexed by the real places of the arithmetic base; the integer case is
`Signature.lean`. Loci are full subcategories (`DefiniteIndefinite.lean` for $\mathbb Z$). Feature 001
(T057–T062) owns their registry rows; this feature owns the mathematics and adds no duplicate row.

**Source**: TASK-SIGNATURE-FULL-SUBCATEGORIES; FOUNDATIONS Def. 20.1, §29b; feature 001 tasks.md.

## D17. Reflections and roots

**Decision**: Integral reflection vectors and reflection subgroups live on the general lattice
category (FOUNDATIONS Def. 60.1, 60.3). A prescribed root norm belongs to the selected root
classifier (Def. 60.1, last paragraph). Finite root systems, root bases, Weyl chambers and ADE
classification live on the definite root-lattice locus with norm $-2$ roots (D4).

**Source**: TASK-REFLECTION-ROOT-CLASSIFICATION; FOUNDATIONS Def. 60.1–60.3, 68.1–68.3.

## D18. Named ADE lattices

**Decision**: Construction order is FOUNDATIONS Conv. 72.3: cited root realization, integral span,
restricted form, simple-root basis, derived Gram matrix, optional Cartan comparison. Cartan matrices
have no role in the primary construction (Conv. 70.4). Realization independence is FOUNDATIONS
Thm. 68.7, to be proved. The commits `1cc6ce1`, `5bd6943` and `62a440d` are partial representation
work to reuse.

**Source**: PLAN-ADE-REALIZATION-UNIQUENESS; FOUNDATIONS Part XIV.

## D19. Theta series

**Decision**: The arithmetic series (`Theta.lean`) is compared with Mathlib's analytic lattice,
Jacobi theta and Gaussian Poisson-summation interfaces first; modularity follows with explicit
weight, level and character, and its analytic form is compared with the formal $q$-series.

**Source**: TASK-DEFINITE-THETA-SERIES; PLAN-THETA-SERIES-MODULARITY; FOUNDATIONS Def. 29b.1.

## D20. Class sets, mass and the Siegel formula

**Decision**: `Mass.lean` defines the mass of an explicit finite family and proves finiteness of
the orthogonal group of a definite lattice; finiteness of a definite genus is not proved at
`533e9259` and is task T040 (the Hermite bound of `ClassFiniteness.lean` is its input). The mass of a genus is defined
after that theorem. `DensityProduct.lean` supplies the finite adelic Haar factorization; the
Siegel formula needs the real-place factor, a measurable fundamental domain for the rational
orthogonal quotient and the global volume comparison.

**Source**: TASK-DEFINITE-CLASS-NUMBER-MASS; PLAN-SIEGEL-MASS-FORMULA; FOUNDATIONS Def. 29b.1, 29b.4;
the docstrings of `Mass.lean`, `DensityProduct.lean`, `ClassFiniteness.lean`.

## D21. Indefinite lattices

**Decision**: Strong approximation is stated for the spin group with a named group, topology, place
set and hypotheses, through the canonical spinor kernel; the Eichler criterion is stated for its
correct lattice class and rank and signature hypotheses. Both statements are read from a library
source before they are written (constitution M2); [@Cas08a, ch. 10] is the first source to open,
and a source that the library does not hold is added to it first (002 research D16). The rank-two
converse of #87 ($O(L)$ infinite for indefinite binary $L$ with $-\det G$ not a square) follows
from Pell existence (O'Sullivan, arXiv:2408.14405v3, §8.1). The rank-at-least-three infinitude
statement is stated only from a statement read in a library source (constitution M2); the task
records the search that finds the source, and adds the source to the library first when the
library lacks it (FR-033).

**Source**: PLAN-INDEFINITE-LATTICE-CLASSIFICATION; TASK-INDEFINITE-ISOTROPIC-APPROXIMATION;
COMPLAINTS.md, "The Pell converse for a split binary lattice is not formalized".

## D22. Complex tori, Hodge data and period domains

**Decision**: The analytic comparison comes first (FR-023); then the Hodge categories of FR-024;
then complex tori $V_{\mathbb C}/L$ and Type IV period domains. The period domain uses positive
isotropic lines for the intersection form, not the full Hodge–Riemann polarization predicate
(COMPLAINTS.md, "FC11 period-domain mapping conflated two polarization conventions"). Feature 004
consumes the weight-one polarized structures of this phase.

**Source**: TASK-ALGEBRAIC-ANALYTIC-LATTICE-COMPARISON; TASK-COMPLEX-TORUS-PERIOD-REALIZATION;
COMPLAINTS.md entries named; FOUNDATIONS §61.

## D23. The public lattice surface

**Decision**: For each root-imported file named by the plan (genus, completion, dyadic, Hasse,
spinor, spinor genus, involution), exactly one outcome: a comparison theorem with the canonical
owner, which T038 proves after the owner tasks T001–T037; a name that states the restricted
meaning; or removal from the root surface. Compilation does not establish the condition.

**Source**: TASK-CANONICAL-PUBLIC-LATTICE-SURFACE; docs/agents/mathematical-simplicity.md, "Keep the
root surface coherent" and "Resolve parallel presentations".

## D24. Reference implementations

| Need | Reference | Licence | Use |
| --- | --- | --- | --- |
| integral finite adeles, tensor–product comparison | ImperialCollegeLondon/FLT `integralAdeles`, `tensorPiEquivPiTensor'` | Apache 2.0 | port with attribution |
| Hasse invariant by choice on a diagonalization | mariainesdff/HassePrinciple | Apache 2.0 | copy with attribution |
| dyadic unit squares, dyadic Hilbert symbol | roed-math/gq2-lean | Apache 2.0 | port |
| $R_v$, $K_v$, uniformizers | mariainesdff/LocalClassFieldTheory | none | proof strategy only |
| adelic double-coset finiteness | FLT `finiteDoubleCoset` | Apache 2.0 | template only |
| $E_8$ comparison | Sphere-Packing-Lean `E8Lattice` | as recorded | done (`e8LatticeSpherePackingIso`) |

**Source**: the "Sources verified 2026-08-14" notes of the vault task cards. Each reuse still
passes the search of constitution M8 at its task revision.

## D25. Open formalization requests in this scope

**Decision**: The lattice and form items that COMPLAINTS.md records as open and that belong to the
foundation, not to a consumer request, are tasks of this feature: Milgram's formula (argument half),
the orthogonal-sum symmetric monoidal structure on quadratic modules, the coordinate-free Lorentz
cone, the $\Gamma_2$ representability and Roby base change, the converse characterization of
cocartesian morphisms in a Grothendieck construction, and transport of $O(L)$ along the sign twist.
Consumer-requested items (#26, #27, #88, #91, #162, #167) are 002 Phase 2 tasks (D2).

**Source**: COMPLAINTS.md entries "Missing theorem: Milgram's formula (argument half)", "Missing
construction: the orthogonal-sum symmetric monoidal structure on quadratic modules", "Missing theorem:
the Lorentzian negative cone, coordinate-free", "Missing theorems: Γ₂ represents quadratic maps",
"Missing theorem: invertible fibre part implies cocartesian", "The sign twist does not transport the
orthogonal group definitionally"; FOUNDATIONS Def. 15.6.

## D26. The even unimodular indefinite lattices

**Decision**: For $s, t \geq 1$ with $s \equiv t \pmod 8$, $\mathrm{II}_{s,t}$ is
$U^{\perp t} \perp E_8(-1)^{\perp (s-t)/8}$ when $s \geq t$ and $U^{\perp s} \perp E_8^{\perp (t-s)/8}$
when $t \geq s$, under the negative-definite convention (D4). The congruence $s \equiv t \pmod 8$ for
every even unimodular lattice of signature $(s, t)$ is a theorem (Serre, *A Course in Arithmetic*,
ch. V), read by task T034. The congruence is not a condition for $p^r$-modular lattices with $p$
odd ($A_2$ is even, $3$-modular, of signature $(2, 0)$).

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 23.3; #35, later release items; the
correction of 2026-10-28 on #7.

## D27. Scale, norm, volume, twist and ideal multiple

**Decision**: $\mathfrak s(b) = \langle b(x, y) \rangle_R$ and $\mathfrak n(b) = \langle b(x, x) \rangle_R$
are functors from forms to the submodule poset of $W$; $\mathfrak v(L)$ is the ideal generated by the
Gram determinants. An integral form is even when $\mathfrak n \subseteq 2R$; integrality is the
separate condition $\mathfrak s \subseteq R$ (the criterion $\mathfrak n = 2\mathfrak s$ calls $A_1$ odd
and is not used). $\mathfrak a$-modularity, the twist and the ideal multiple and their laws are those
of O'Meara, *Introduction to Quadratic Forms*, §82 (82:12, 82:14), read by task T050.

**Source**: #33, comments of 2026-08-07 and their corrections of 2026-10-28;
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 22.3.

## D28. The invariants $\ell$ and $(r, a, \delta)$

**Decision**: $\ell(A)$ is the minimal number of generators of a finite-length torsion module,
$\max_{\mathfrak p} \dim_{R/\mathfrak p} A/\mathfrak p A$; it is monotone along monomorphisms and
epimorphisms into $(\mathbb N, \leq)$ and is not additive. On even $p$-elementary lattices,
$(r, a, \delta)$ is rank, the exponent $a$ with $A_L \cong (\mathbb Z/p)^a$, and at $p = 2$ the parity
$\delta$ of $q_L$. The genus of an even 2-elementary lattice needs the signature with
$(r, a, \delta)$ ($E_8$ and $U^{\perp 4}$ share $(8, 0, 0)$).

**Source**: #33, comment of 2026-08-07 (16:42) and its corrections; #35, comment of 2026-08-07 and
its correction.

## D29. Nikulin's existence and uniqueness theorems

**Decision**: The statements are those of [@Nik80] as transcribed on #35 (Cor. 1.9.4 is
completeness of the invariants; Thm. 1.10.1 is existence with its four conditions; Cor. 1.10.2
needs $\operatorname{rk} > \ell(A_q)$; Cor. 1.13.3 needs $\operatorname{rk} \geq 2 + \ell(A_q)$ and
$t_\pm \geq 1$; Cor. 1.13.4 is stability under $U \perp -$), and Thm. 1.14.2 with indefiniteness and
$\operatorname{rk} L \geq \ell(A_L) + 2$ and no 2-elementary hypothesis. Each statement is read again
from the library before it is written (constitution M2). The class number is a cardinal-valued
functor on genera; its finiteness is a theorem.

**Source**: #35, comments of 2026-08-07; #7 and #1, corrections of 2026-10-28 (Thm. 1.14.2).

## D30. Steinitz classes under the module operations

**Decision**: For finite projective $P$, $Q$ of ranks $p$, $q$ over a Dedekind domain:
$[P \oplus Q] = [P][Q]$, $[P^\vee] = [P]^{-1}$, $[P \otimes Q] = [P]^{q}[Q]^{p}$,
$[\operatorname{Hom}(P, Q)] = [P]^{-q}[Q]^{p}$, and base change along $R \to R'$ is the map of class
groups; $P \cong R^{p-1} \oplus I$ with $[I] = [P]$. The witness is $\mathbb Z[\sqrt{-5}]$ with the
ideal $(2, 1 + \sqrt{-5})$ of class of order two. Pseudo-bases and pseudo-matrix computation are
`lean-cas-dsl` leaf work.

**Source**: #105, research rounds 1–2; [@Rot15, Thm. 11.117]; kernel constitution C22.

## D31. The subgroup tower of $O(L)$

**Decision**: $O^+(L)$ is the kernel of the real spinor norm (D14); for a Lorentzian lattice it
equals the subgroup preserving the positive cone (#36) by a theorem; $\widetilde O(L)$ is the kernel of
the discriminant action (N10). Finite generation of $O(L)$ for indefinite $L$ (Borel–Harish-Chandra)
is not a requirement; finiteness for definite $L$ is in `Mass.lean`.

**Source**: #106, the prior-art comment of 2026-07-08; #1, north star (decision record 2, R1).
