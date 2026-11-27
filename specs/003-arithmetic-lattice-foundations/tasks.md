# Tasks: Arithmetic lattice foundations at their natural generality

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[data-model.md](data-model.md), [quickstart.md](quickstart.md)

**Tests**: each task's check is the tier-1 elaboration of its modules and the comparison theorems
it names (plan.md Contract O); each phase ends with `just test`.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours (other files, no open input). Lean
checks still run one at a time (constitution E10). Each task applies plan.md Contract O to the owner
rows it names, starting from the source at its own revision. "Vault" names the superseded card that
the task carries.

## Execution order

This task list supplies the obligations of task T107 of feature 002 (research D2).
Select issues in definition-first native tree order and execute their actual prerequisites
first (constitution M11); do not wait for independent proofs. Inside a phase, a task follows the tasks whose results it uses; the workstream does each input task first, in the feature or repository that owns it, and then returns (constitution M11). Inputs from feature 002 are cited as
"002 Tnnn".

## Phase 1: Projective formed arithmetic (US1)

- [ ] T001 [US1] N01, N02: give the $W$-valued form both correlation maps $\lambda_b$, $\rho_b$, the
  left and right radicals and the separation predicates; prove that symmetry identifies the two
  conditions; define perfection by the correlation isomorphisms; prove the equivalence of
  fraction-field nondegeneracy and fraction-field perfection for scalar-valued symmetric forms on
  finite projective modules over a domain, and compare `IsFractionFieldPerfect` with it. Files:
  `LeanCategories/Modules/Bilinear/Valued/{Fixed,Total}.lean`,
  `LeanCategories/Lattices/Valued/MetricDual.lean`. Source: [@MH73, §I.1]. Decision: D5. Vault:
  TASK-ARITHMETIC-FORMED-LATTICE-INTERFACES. Separating example: a nonsymmetric form with zero left
  and nonzero right radical.
- [ ] T002 [US1] N01–N05: state each comparison among nondegeneracy, fraction-field perfection, the
  integral correlation map, primitive embedding, perfectness and unimodularity with its exact
  hypotheses; unify integrality, ideal-integrality, scale ideals, diagonal-value ideals, finite
  projective and finite free formed modules, formed submodules, saturation, primitive closure,
  orthogonal sums and finite orthogonal powers on the existing form, tensor, base-change and
  orthogonal-sum operations. Inputs: T001. Decisions: D5, D9. Vault:
  TASK-ARITHMETIC-FORMED-LATTICE-INTERFACES.
- [ ] T050 [US1] N28 (FR-034): the scale, norm and volume functors with their theorems, the twist
  and the ideal multiple with the laws of D27, and $L \otimes_R \mathfrak a \cong \mathfrak a L$.
  Files: `Lattices/Valued/{Constructions,Arithmetic}.lean`. Inputs: T002. Source: O'Meara §82.
  Decision: D27. Separating example: $A_1 = \langle 2 \rangle$ is even with $\mathfrak n = \mathfrak s = 2\mathbb Z$;
  $U(\tfrac12)$ is not integral.
- [ ] T051 [P] [US1] N29 (FR-035): $D$ and $P$ natural in the value module with $P \circ D = 2$ on
  symmetric forms and $D \circ P = 2$, $\operatorname{im}(P)$ and $\operatorname{Ref}(b)$, the
  comparison with $b(x, x) \in 2W$, and the symmetric, alternating and skew-symmetric classifiers
  with their implications. Files: `Modules/{Bilinear,Quadratic}/Valued/`. Inputs: T001.
  Source: [FOUNDATIONS.md](../../FOUNDATIONS.md) §§16–17. Separating example: $b(x, y) = x_1 y_2$ on
  $R^2$ has $P(D(b)) \neq 2b$; at $W = \mathbb Q/\mathbb Z$ the form with $b(x, x) = \tfrac12$ is
  skew-symmetric and not alternating.
- [ ] T003 [P] [US1] N03: construct the fibre comparison between the fixed-value category
  $(M, b : M \otimes M \to W)$ and the variable-value category $(M, W, b)$, the scalar-extension and
  value-change functors and their composition laws; the arithmetic lattice locus; the framed and
  coordinate presentations, the generating-frame and basis-frame lattice pullbacks of FOUNDATIONS
  Def. 21.1, the arbitrary-index coordinate lattice category, $\mathbf{SymMat}_n(R)$, the Gram
  constructor $\operatorname{Gram}_n$ and the equivalence theorem of FOUNDATIONS Def. 21.3, and the
  symmetry of the form induced by a finite basis (`Basis.toDual`, if Mathlib lacks it; #33). Files:
  `Lattices/Valued/{Basic,Arithmetic,Based}.lean`, `Modules/TruncatedResolutions.lean`. Source:
  [@MH73, §§I.1–I.2]. Vault: TASK-CANONICAL-FORMED-CATEGORY-COMPARISONS.
- [ ] T004 [P] [US1] N08: connect Mathlib's PID structure theorem, `Basis.SmithNormalForm` and the
  Dedekind torsion primary decomposition to lattice rank, elementary divisors, discriminant modules
  and the free Gram-determinant formulas; relate local freeness and height-one ranks to the
  determinant line and Steinitz class. Files: `Lattices/Valued/{SmithNormalForm,Arithmetic}.lean`.
  Source: [@Rot15, Thm. 11.117]. Vault: TASK-PID-DEDEKIND-MODULE-STRUCTURE.
- [ ] T005 [US1] N06, N07: prove $\operatorname{Cl}(R) \cong \operatorname{Pic}(R)$ for a Dedekind
  domain, invertibility of $\bigwedge^n P$ for $P$ projective of constant rank $n$, the Steinitz
  classification with its hypotheses, the comparison of the discriminant ideal through the
  determinant map with $\operatorname{Fitt}_0(\operatorname{coker} \operatorname{ad}_b)$, localization,
  orthogonal-sum behaviour and recovery of the Gram determinant ideal after a basis; the Steinitz
  form $P \cong R^{n-1} \oplus I$ and the class laws of D30 with the witness
  $(2, 1 + \sqrt{-5}) \subset \mathbb Z[\sqrt{-5}]$ (#105). Files:
  `Lattices/Valued/{DeterminantLine,FittingIdeal}.lean`. Inputs: T004. Source: [@Rot15, Thm. 11.117];
  [@MH73, §I.2]. Decisions: D10, D30. Vault: TASK-DETERMINANT-STEINITZ-DISCRIMINANT-IDEAL.
- [ ] T006 [US1] N04, N05: prove that `metricDual` is `fractionalIdealDual` at $I = R$ and
  `idealDual` its integral-ideal case, with membership and equality at arbitrary points of the
  rational span; attach the $K/I$-valued bilinear form to $A_L^I$ and, under the evenness and
  integrality hypotheses of D8, its $K/2I$-valued quadratic refinement; prove the comparison of
  $A_L^R$ with the adjoint defect with the Riesz and finite projective hypotheses and of their
  Fitting and discriminant ideals. Files: `Lattices/Valued/{IdealDual,Discriminant,DiscriminantQuadratic}.lean`.
  Inputs: T002, T005. Source: [@MH73, §I.1]; [@Nik80, §§2°–4°]. Decisions: D7, D8. Vault:
  TASK-IDEAL-DUAL-DISCRIMINANT-COMPARISON.
- [ ] T052 [US1] N30 (FR-036): $\ell$ with $\ell(A) = \max_{\mathfrak p} \ell(A_{\mathfrak p})$, its
  subadditivity and monotonicity, and $(r, a, \delta)$ on even $p$-elementary lattices. Files:
  `Lattices/Valued/Discriminant.lean`. Inputs: T006. Decision: D28. Separating example:
  $\ell(\mathbb Z/2 \oplus \mathbb Z/3) = 1$; $E_8$ and $U^{\perp 4}$ share $(8, 0, 0)$ and differ in signature.
- [ ] T053 [US1] N31 (FR-037): $\operatorname{disc}_b$ and $\operatorname{disc}_q$ on isometry cores, the
  polarization $\mathbf{DiscQuad} \to \mathbf{DiscBil}$ and the commuting square, with the
  $\langle 2 \rangle \hookrightarrow \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ test. Files:
  `Lattices/Valued/DiscriminantFunctor.lean`. Inputs: T006. Source: [FOUNDATIONS.md](../../FOUNDATIONS.md)
  §26.
- [ ] T007 [US1] N09: one formed-module theory of primitive embeddings, orthogonal complements,
  saturation, discriminant forms, isotropic subgroups and overlattices: construction and recovery in
  both directions and the extension criterion for isometries; the equivariant and nonequivariant
  integral defects consume these constructions. Files: `Lattices/Valued/{Gluing,GluingAction,Overlattice*,Cusps}.lean`.
  Inputs: T006, 002 T112. Source: [@Nik80, §§4°–6°]. Decision: D9. Vault:
  TASK-COMMON-EMBEDDING-GLUING-THEORY.
- [ ] T008 [P] [US1] D25, forms: make orthogonal sum a symmetric monoidal structure on
  `QuadModuleCat R W` and `IsometryClass R W` its skeleton monoid; prove the degree-2 representability
  of quadratic maps by $\Gamma_2$ and Roby's base change of $\Gamma$ in degree 2 (port of
  DividedPowers4, with provenance) and compare with `QuadraticMap.baseChange'`; prove
  `IsStronglyCocartesian (forget F) f φ ↔ IsIso φ.fiber` for both Grothendieck constructions. Files:
  `Modules/Quadratic/Valued/IsometryClasses.lean`, `ForMathlib/QuadraticBaseChange.lean`,
  `ForMathlib/GrothendieckCocartesian.lean`. Source: FOUNDATIONS Def. 15.6; Roby 1963, Thm. III.3.
  Each closes its COMPLAINTS.md entry and its `TODO(LC-12)`.
- [ ] T009 Phase gate: `just test` passes; rows N01–N09 and N28–N31 have every comparison named in
  data-model.md.

## Phase 2: Equivariant lattice arithmetic (US1)

- [ ] T010 [US1] N10: prove the equivalence of $G$-objects on a fixed lattice with homomorphisms
  $G \to O(L)$; obtain stabilizers, centralizers and normalizers from the generic group-action,
  stabilizer and normalizer constructions (INTENT.md, "O(L) := Aut"); construct the discriminant
  action and equivariant scalar change; recover `Involution.lean` from $G = C_2$ by a comparison.
  Files: `Lattices/Valued/{Equivariant,Involution,FamilyStabilizer}.lean`. Inputs: T009. Source:
  [@Sch21, Def. 2.4.1]. Vault: TASK-EQUIVARIANT-LATTICE-CATEGORY.
- [ ] T011 [US1] N11: rational isotypic components through Mathlib's `isotypicComponent`; under
  Maschke or other explicit semisimplicity hypotheses the constituents $L_\lambda = L \cap V_\lambda$,
  the finite defect of $\bigoplus_\lambda L_\lambda \to L$, its primary parts and its gluing data
  through T007. Inputs: T010, T007. Source: [@Mor19, §I.1.7]; FOUNDATIONS Rem. 28.6. Vault:
  TASK-RATIONAL-ISOTYPIC-INTEGRAL-GLUE.
- [ ] T012 Phase gate: `just test`; rows N10, N11 closed.

## Phase 3: Places and completions (US2)

- [ ] T013 [P] [US2] N12: the place-indexed realization interface over an arithmetic base:
  height-one points as nonarchimedean indices, the distinguished places as a separate index, the
  comparison diagram $R \to R_{\mathfrak p} \to R_v$, $K \to K_v$; no new prime spectrum. Files:
  `Lattices/Valued/{ArithmeticPlace,ArithmeticBase,Localization,Residue}.lean`. Inputs: T009.
  Source: [@Wei82, Ch. I]. Decision: D3. Vault: TASK-ARITHMETIC-PLACES-REALIZATIONS.
- [ ] T014 [US2] N12: lattice scalar extension to $R_v$ and formed-space extension to $K_v$ from
  `HeightOneSpectrum.adicCompletionIntegers`; compatibility with orthogonal sums, ideal duals,
  discriminant forms, equivariant actions and orthogonal groups; the $\mathbb Z_p$ and $\mathbb Q_p$
  constructions as specialization theorems. Files: `Lattices/Valued/Completion.lean`. Inputs: T013,
  T006, T010. Source: [@Wei82, Ch. I]. Vault: TASK-GENERAL-HEIGHT-ONE-COMPLETION.
- [ ] T015 [P] [US2] N13: prove that the natural-prime and $\mathbb Z_2$ statements in the source are
  specializations of `IsIElementary` and `IsDyadic`. Files: `Lattices/Valued/{Elementary,Dyadic}.lean`
  and their $\mathbb Z_2$ consumers. Inputs: T006. Source: [@Ger08, §§3.1, 8.1–8.2]. Vault:
  TASK-ANNIHILATOR-ELEMENTARY-DYADIC.
- [ ] T016 Phase gate: `just test`; rows N12, N13 closed.

## Phase 4: Canonical local invariants (US3)

- [ ] T017 [P] [US3] N16: define the Hasse invariant on the isometry class of a nondegenerate
  quadratic space over a field with a bilinear Hilbert symbol, values $\{\pm 1\}$, normalization of
  D13; prove the diagonal formula, isometry invariance, orthogonal-sum behaviour and the
  scalar-extension comparisons. Files: `Lattices/Valued/{Hasse,HasseInvariance}.lean`. Inputs: T009.
  Source: [@Jac85, §9.9]; [@Cas08a, Lemma 2.2]. Decision: D13. Vault: TASK-INTRINSIC-HASSE-INVARIANT.
- [ ] T018 [P] [US3] N17: make the canonical spinor norm the owner; prove its kernel and
  exact-sequence statements, the reflection formula, the comparison with reflection products and its
  local and adelic forms; turn `Spinor.lean`'s `SpinorNorm` into the characterization theorem of the
  canonical map. Files: `Lattices/Valued/{CanonicalSpinorNorm,Spinor,AdelicSpinorNorm}.lean`. Inputs:
  T009. Source: [@Cas08a, §10.3]. Decision: D14. Vault: TASK-CANONICAL-CLIFFORD-SPINOR-NORM.
- [ ] T054 [US3] N32 (FR-039): $SO(L)$, $\widetilde O(L)$ with the image of $O(L) \to O(A_L, q_L)$,
  $O^+(L)$ by the real spinor norm, $SO^+(L)$, $\widetilde{SO}(L)$, $\widetilde{SO}^+(L)$, and the theorem
  that $O^+$ of a Lorentzian lattice is the subgroup preserving the positive cone. Files:
  `Lattices/Valued/{OrthogonalGroup,CanonicalSpinorNorm}.lean`. Inputs: T018, T010. Decision: D31.
- [ ] T019 Phase gate: `just test`; rows N16, N17 (except the spinor-genus laws of T025) and the
  subgroup tower of N32 closed.

## Phase 5: Ring and field adeles (US2)

- [ ] T020 [US2] N14: construct $\widehat R = \prod_{v<\infty} R_v$ and
  $\widehat L = \prod_v (L \otimes_R R_v)$ over an arithmetic base; prove the comparison with
  $L \otimes_R \widehat R$ for finite projective $L$ (port of FLT `tensorPiEquivPiTensor'`); construct
  the integral finite adelic formed module, orthogonal group and lattice stabilizer, and the
  intersection statements for $R$ and $L$ in their generic realizations; compare with
  `FiniteAdeleRing R K` only as field adeles. Files: `Lattices/Valued/{Adele,AdelicClass}.lean`,
  `IntegralAdeleRing.lean`, `Modules/TensorProduct/Pi.lean`. Inputs: T014. Source: [@Wei82, Ch. I].
  Decisions: D11, D24. Vault: TASK-FINITE-ADELIC-LATTICE-REALIZATION.
- [ ] T021 [US2] N14: $\mathbb A_R$ for an arithmetic base, the comparison with FOUNDATIONS Def. 29.1
  at $\mathcal O_K$, $\mathbb A_{\mathbb Z} \cong \mathbb R \times \prod_p \mathbb Z_p$,
  $L_{\mathbb A_R}$ with its componentwise description, the form and orthogonal action, and the
  comparison with $\mathbb A_K$. Inputs: T020. Source: [@Wei82, Ch. I]. Decision: D11. Vault:
  TASK-FULL-ADELIC-NUMBER-FIELD-REALIZATION.
- [ ] T022 Phase gate: `just test`; row N14 closed.

## Phase 6: Genus (US2)

- [ ] T023 [US2] N15: prove the componentwise characterization of the ring-adelic genus over an
  arithmetic base; for $R = \mathbb Z$ delete the definition `SameGenus` and keep
  `sameGenus_iff_sameAdeleGenus` as the characterization theorem of the ring-adelic owner, with its
  consumers moved to the owner. Files: `Lattices/Valued/{Adele,LocalGlobal,GenusInvariants}.lean`.
  Inputs: T021. Source: [@Nik80, §1.9, Cor. 1.9.4]. Decision: D12. Vault: TASK-GENERAL-DEDEKIND-GENUS.
- [ ] T024 [US2] N15: prove the classification of the global isometry classes in a genus by
  $O(V)(K)\backslash O(V)(\mathbb A_{K,f})/K_L$, with the relation between the field-adelic group and
  the integral adelic stabilizer, and the comparison of $K_L$ with local integral bases for a
  projective nonfree $L$ (FOUNDATIONS Def. 29.5). Files: `Lattices/Valued/AdelicClass.lean`. Inputs:
  T023. Source: [@Wei82, Ch. II]; [@Cas08a, ch. 10]. Vault: TASK-GENUS-ADELIC-DOUBLE-COSET.
- [ ] T025 [US3] N17: functorial base change of isometries, and with it symmetry and transitivity of
  the spinor-genus relation over the ring-adelic genus (FOUNDATIONS Def. 29b.3). Files:
  `Lattices/Valued/{SpinorGenusAdelic,BaseChangeIsometry}.lean`. Inputs: T018, T023. Decision: D14.
- [ ] T026 Phase gate: `just test`; rows N15, N17 closed.

## Phase 7: Local classification (US3)

- [ ] T027 [US3] N18: over a discrete valuation ring, scale and norm ideals, modularity,
  unimodularity and Jordan constituents; existence and orthogonality of Jordan decompositions in
  every residual characteristic; the uniqueness and classification data that survive isometry; the
  Witt decomposition, determinant square class and Hasse invariant of the generic space; the primary
  discriminant form; at dyadic places the unit square-class filtrations, Type I and Type II
  constituents, oddity-type invariants and finite quadratic modules, with the $\mathbb Z_2$
  declarations as special cases. Files: `Lattices/Valued/{Jordan*,Witt,Dyadic*,PadicMixedSymbol}.lean`.
  Inputs: T006, T014, T015, T017. Source: [@Ger08, §§6.7, 8.1–8.2]; [@Jac85, §9.9]. Decisions: D15,
  D24. Vault: TASK-JORDAN-WITT-DYADIC-CLASSIFICATION.
- [ ] T028 [US3] D25: the argument half of Milgram's formula,
  $G(q) = \sqrt{|A_L|}\, e^{2\pi i \sigma/8}$, through the $p$-adic Jordan components, with the
  character on the value group of `discriminantSymBilWQuadraticMap`. Files:
  `Algebra/QuadraticGaussSum.lean`, `Lattices/Valued/Discriminant.lean`. Inputs: T027. Closes the
  COMPLAINTS.md entry "Missing theorem: Milgram's formula (argument half)".
- [ ] T029 Phase gate: `just test`; row N18 closed.

## Phase 8: Signatures, reflections, named lattices, realizations and the surface (US4)

- [ ] T030 [P] [US4] N19: $\operatorname{sig}_v(L) = (r_v, s_v)$ at each real place of an arithmetic
  base; positive definite, negative definite, totally definite, indefinite and Lorentzian properties
  with explicit sign conventions and their full subcategories; `Signature.lean` as the $\mathbb Z$
  specialization. Files: `Lattices/Valued/{Signature,DefiniteIndefinite}.lean`. Inputs: T021. Source:
  [@MH73, §I.1]. Decision: D16. Vault: TASK-SIGNATURE-FULL-SUBCATEGORIES.
- [ ] T031 [P] [US4] D25: express the orthogonal subgroup of a scaled lattice so that the sign twist
  transports $O(L) = O(L(-1))$; replace the direct negative definite proof in `Mass.lean` by the
  transport. Files: `Lattices/Valued/{Constructions,Mass}.lean`. Inputs: T002. Closes the COMPLAINTS.md
  entry "The sign twist does not transport the orthogonal group definitionally".
- [ ] T032 [P] [US4] D25: transport `negativeCone_two_components` along Sylvester's normal form to an
  arbitrary real quadratic form of negative index one. Files: `Topology/LorentzCone.lean`. Closes
  the COMPLAINTS.md entry "Missing theorem: the Lorentzian negative cone, coordinate-free".
- [ ] T033 [US4] N20: reflective vectors, reflections and reflection subgroups on the general
  lattice category with no definiteness hypothesis, compared with the root-pairing realization;
  finiteness, root bases, Weyl chambers and ADE classification on the definite root-lattice locus.
  Files: `Lattices/Valued/{Reflection,RootSystem,RootBase,WeylChambers}.lean`. Inputs: T030. Source:
  [@Hum90, §§1.1–1.3, 1.9, 1.12]. Decisions: D4, D17. Vault: TASK-REFLECTION-ROOT-CLASSIFICATION.
- [ ] T034 [US4] N21: the hyperbolic plane from its form, $U^{\perp n}$ by finite orthogonal powers,
  $E_8^{\perp n}$ and $\Lambda_{K3} = U^{\perp 3} \perp E_8^{\perp 2}$ by the generic operations; rank,
  signature, parity and discriminant from generic theorems; no matrix-first hierarchy. Files:
  `Lattices/Valued/{Standard,U2Lattice,Constructions}.lean`; $\mathrm{II}_{s,t}$ by D26 and the
  theorem $s \equiv t \pmod 8$ for even unimodular lattices. Inputs: T030. Source: [@Nik80, §1°];
  [@Tel22, §2.1]; [@LZ16, §1.3]; Serre, *A Course in Arithmetic*, ch. V. Decisions: D4, D26. Vault:
  TASK-STANDARD-LATTICES-GENERIC-CONSTRUCTIONS.
- [ ] T035 [P] [US4] N22: the comparison $(L, b) \mapsto L \hookrightarrow L_{\mathbb R}$ with its
  finite-rank, embedding and positivity hypotheses, compared with Mathlib `ZLattice` and
  `ZLattice.covolume`, relating determinant ideals to covolumes. Files: `Lattices/Valued/{Topological,RealTorus}.lean`.
  Inputs: T005. Source: [@MH73, §I.2]; [@LZ16, §1.3]. Vault: TASK-ALGEBRAIC-ANALYTIC-LATTICE-COMPARISON.
- [ ] T036 [US4] N23: the categories $\mathrm{Fil}^{\mathrm{fin}}_{\uparrow}(C)$,
  $\mathrm{Fil}^{\mathrm{fin}}_{\downarrow}(C)$ and $\mathrm{BiFil}^{\mathrm{fin}}(C)$ of an abelian
  category with induced, strict and graded constructions; scalar extension
  $\mathbb Z \to \mathbb Q \to \mathbb R \to \mathbb C$ with conjugation from the real form; the pure
  categories $\mathrm{HS}_{\mathbb R}(n)$, $\mathrm{HS}_{\mathbb Q}(n)$, $\mathrm{HS}_{\mathbb Z}(n)$ and
  the filtration–decomposition equivalence; the mixed categories with graded purity and strictness;
  tensor, dual, internal Hom, Tate objects and twists; polarizations and Hodge isometries, with the
  Hodge-isometry subgroup of $O(L)$. Files: new owners under `LeanCategories/Homological/` and
  `Lattices/Valued/` (M4). Source: Deligne, *Théorie de Hodge II*, §§1.1, 2.1, 2.3; Huybrechts,
  *Lectures on K3 Surfaces*, Ch. 3 §1. Closes the COMPLAINTS.md entry "Hodge structures need
  filtered-module categories and their comparison maps".
- [ ] T037 [US4] N23: construct $V_{\mathbb C}/L$ only from complex or Hodge data, keep $L_K/L$ a
  distinct torsion module, and build Type IV period domains from signature $(2, n)$ lattices with the
  positive-isotropic-line convention. Files: `Lattices/Valued/{ComplexStructure,ComplexTorus,PeriodDomainData,K3PeriodDomainData}.lean`.
  Inputs: T035, T036, T030. Source: [@LZ16, §§1.3, 2.1, 3.1.2]; [@PK16, Def. 1.3]. Decision: D22. Vault:
  TASK-COMPLEX-TORUS-PERIOD-REALIZATION.
- [ ] T038 [US4] FR-030: for each root-imported file named by D23 (genus, completion, dyadic, Hasse,
  spinor, spinor genus, involution) record its outcome (a comparison theorem with its canonical owner, which this task proves after
  the owner tasks T001–T037; a restricted name; or removal from `LeanCategories/All.lean`) and apply it; retain the general owners the
  vault card lists (formed-module categories, scalar and value change, localization and residue,
  metric discriminant forms, orthogonal groups, discriminant actions, stable kernels, square classes,
  height-one primary decomposition). Inputs: T001–T037. Decision: D23. Vault:
  TASK-CANONICAL-PUBLIC-LATTICE-SURFACE.
- [ ] T039 Phase gate: `just test`; rows N19–N23 closed.

## Phase 9: Definite theory (US4)

- [ ] T040 [US4] N24: prove that the class set of a definite genus is finite (input: the Hermite
  bound of `ClassFiniteness.lean`); define the class number and the mass of the genus
  $\sum_{[M]} 1/|O(M)|$; relate the class set to the finite adelic double coset; express the
  explicit-family mass of `Mass.lean` as its comparison. Files: `Lattices/Valued/{Mass,ClassFiniteness,AdelicClass}.lean`.
  Inputs: T024, T030. Source: [@Nik80, §1.9]; [@CS88, §1]. Decision: D20. Vault:
  TASK-DEFINITE-CLASS-NUMBER-MASS.
- [ ] T041 [P] [US4] N25: compare $\Theta_L$ of `Theta.lean` with Mathlib's analytic lattice, Jacobi
  theta and Gaussian Poisson-summation interfaces. Files: `Lattices/Valued/Theta.lean`. Inputs: T035.
  Source: [@Ros21, §7.1.10]. Decision: D19. Vault: TASK-DEFINITE-THETA-SERIES.
- [ ] T042 Phase gate: `just test`; rows N24, N25 closed.

## Phase 10: ADE realization and uniqueness (US5)

- [ ] T043 [US5] For each finite ADE type: the named lattice from a cited root realization (not from
  a Cartan or Gram matrix); diagram enumeration giving an ordered simple-root basis and the derived
  Gram comparison (FOUNDATIONS Thm. 72.2); realization independence and uniqueness up to isometry
  from the finite root-system classification (FOUNDATIONS Thm. 68.7). Files:
  `Lattices/Valued/{ADERealization,RootLattice,DRootLattice,SimplyLaced,RootBaseExists}.lean`.
  Inputs: T033, T034. Source: [@Hum90, ch. 1]; [@Bou08, chs. IV–VI]. Decision: D18. Vault:
  PLAN-ADE-REALIZATION-UNIQUENESS.

## Phase 11: Indefinite lattices (US5)

- [ ] T044 [US5] N27: isotropic vectors and subspaces, hyperbolic planes, Witt index and arithmetic
  orthogonal groups on the indefinite full subcategories; symmetric domains from the real-place
  signatures. Files: `Lattices/Valued/{IsotropicReduction*,PositiveCone*,Witt}.lean`. Inputs: T030,
  T037. Source: [@Nik80, §§4°–6°]; [@LZ16, §§1.3, 3.1]. Vault: TASK-INDEFINITE-ISOTROPIC-APPROXIMATION.
- [ ] T045 [US5] N27: strong approximation with its group, topology, place set and hypotheses,
  through the canonical spinor kernel; the Eichler criterion for its lattice class and rank and
  signature hypotheses; the comparison of genus, spinor genus and global isometry classes. Inputs:
  T044, T025. Decision: D21. Vault: PLAN-INDEFINITE-LATTICE-CLASSIFICATION.
- [ ] T046 [US5] N27: $O(L)$ infinite for an indefinite rank-two $\mathbb Z$-lattice with $-\det G$
  not a square, from Pell existence; then read a library source for the rank-at-least-three
  statement and state and prove it from that source (FR-033); the search that finds the source is
  recorded in the commit, and a source that the library lacks is added to it first (002 research
  D16). Files:
  `Lattices/Valued/SplitBinaryLattice.lean`. Inputs: T044. Source: O'Sullivan, arXiv:2408.14405v3,
  §8.1. Decision: D21.

- [ ] T055 [US5] N32 (FR-038): Nikulin's Cor. 1.9.4, Thm. 1.10.1 and Cor. 1.10.2, with signature and
  discriminant form as monoid homomorphisms on genera. Files: `Lattices/Valued/GenusInvariants.lean`.
  Inputs: T023, T027, T052. Source: [@Nik80, §§1.9–1.10]. Decision: D29.
- [ ] T056 [US5] N32 (FR-038): Nikulin's Thm. 1.13.2, Cor. 1.13.3, Cor. 1.13.4 and Thm. 1.14.2.
  Files: `Lattices/Valued/{GenusInvariants,OrthogonalGroup}.lean`. Inputs: T055, T045. Source:
  [@Nik80, §§1.13–1.14]. Decision: D29. Check: $U \perp U \perp E_8$ is unique in its genus.

## Phase 12: The Siegel mass formula (US5)

- [ ] T047 [US5] N26: define the real-place factor and compare it with the finite adelic density
  product (`DensityProduct.lean`); prove the measurable fundamental-domain theorem for the rational
  orthogonal quotient that the counting comparison needs; prove the identification of the mass of the
  genus with the normalized product of local densities under explicit hypotheses. Inputs: T040, T024.
  Decision: D20. Vault: PLAN-SIEGEL-MASS-FORMULA.

## Phase 13: Theta-series modularity (US5)

- [ ] T048 [US5] N25: Poisson summation for the real realization of a $\mathbb Z$-lattice with its
  measure normalization; the generator transformation laws of $\Theta_L$ with explicit weight, level
  and character hypotheses; the comparison of the analytic modular form with the formal $q$-series.
  Inputs: T041. Decision: D19. Vault: PLAN-THETA-SERIES-MODULARITY.
- [ ] T049 Milestone: every row of data-model.md is closed, the spec's success-criteria table is
  measured at the milestone revision, and `just test` passes. Performs no other work.

## Dependencies & Execution Order

- Phase 1 comes before every later phase. Phases 2 and 4 need only Phase 1; Phase 3 needs Phase 1 and
  T010 (T014).
- Phase 5 needs T014; Phase 6 needs Phase 5 and T018; Phase 7 needs T006, T014, T015, T017.
- Phase 8 needs T021 (T030) and T005 (T035); T038 needs T001–T037.
- Phase 9 needs Phase 6 and T030, T035; Phases 10–13 follow Phase 9 in document order (D1).
- T050 and T051 follow T002 and T001; T052 and T053 follow T006; T054 follows T018 and T010;
  T055 follows T023, T027, T052; T056 follows T055 and T045.
- External inputs: 002 T086 (Milestone 2) before T001; 002 T112 before T007.

## Implementation Strategy

1. Phase 1: one owner and its comparisons for every notion of the projective formed layer (MVP for
   US1).
2. Phases 2–7: equivariance, places, invariants, adeles, genus, local classification (US2, US3).
3. Phases 8–9: loci, named lattices, realizations, the public surface, the definite theory (US4).
4. Phases 10–13: the theorem programmes (US5).

Each task is committed by explicit pathspec; a commit carries mathematics, not only a record
update.
