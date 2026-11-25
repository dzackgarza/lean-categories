# Tasks: The foundational corpus programme

**Input**: [spec.md](spec.md), [plan.md](plan.md), [research.md](research.md),
[data-model.md](data-model.md), [units.md](units.md), [quickstart.md](quickstart.md)

**Tests**: each task's check is the selector command or the tier-1 elaboration that it names, and
the review of plan.md Contract R. Paths are relative to the repository root.

## Format: `[ID] [P?] [Story] Description`

`[P]` marks a task whose drafting can run beside its neighbours (other files, no open input). Lean
checks still run one at a time (constitution E10). Each task names its files, its inputs (earlier
tasks or units), its check and its decisions. The contracts S, D, C, R, M and T are in
[plan.md](plan.md#unit-contracts). A unit population is the live selector when the task starts;
[units.md](units.md) lists it at `fc549baa`.

## Execution order

Tasks are executed in document order (constitution M11, research D1). Inside a phase, a task is
ready when its inputs are delivered; a blocked task does not hold back a later ready task of the
same phase (D12). Before each new unit, run `python3 scripts/output_check.py`
(corpus-execution.md, "Check output before choosing more work").

## Open nodes of `TODO.md`, open COMPLAINTS.md items and their tasks

| `TODO.md` node | Tasks |
| --- | --- |
| `realization-stub-audit` | T009–T028 |
| `small-reference-ports` (continuation) | T029, T030, T045 (D7) |
| `lower-ramification-owner` (TauCeti route) | T099, T100 (D7) |
| `fc05-definitions`, `fc07-definitions` (ledger ticked) | T009, T013 (D6) |
| `fc06-definitions`, `fc08-definitions` … `fc17-definitions` and the source workstreams | T010–T067 |
| `audit-authored-definitions` | T068 |
| `definition-source-conformance` | T069–T085 |
| `definition-realization-convergence`, `definitions` | T086 |
| Sweep II remainder (`mapping` for FC16, FC17) | T087–T089 |
| `theorems` | T090–T106 |
| `orthogonal-group-direct-sum-structure` | T004–T008 (D9) |
| `arithmetic-lattice-foundations` | T107: feature 003 T001–T049 (D22) |
| `refactor-audit` | T108 |
| `lint-paydown` | T109 |
| `bloat-audit-loop` | T110 |
| `abelian-projectivity` | T111: feature 004 T001–T010 (D22) |
| Open formalization requests of COMPLAINTS.md | T112–T125 (D23) |
| Gate, contribution-rule and tooling defects of COMPLAINTS.md | T126–T129 (D23) |
| `computational-core` | none: feature 001 and `lean-cas-dsl` (D10) |
| §4a items (tiers, root set, granularity, statement/proof split) | none: settled by D13, D14, D15 |

## Phase 1: Setup (the record and the sources)

- [ ] T001 Repair the three mapping rows that stop the frontier generator (units.md, "Scheduler
  defects"): restore the State-1 evidence and `[residue-search-audited]` of `FC06-C04-U081`
  before its `[realized]` in `corpus/chapter-4-curves-fc06.md`, or run its residue audit if the
  row's history holds none; rewrite the `Construction prerequisites:` clauses of `FC15-C06-U009`
  and `FC15-C06-U012` in `corpus/chapter-6-special-cases-fc15.md` in the parsed form
  (data-model.md `MappingRow.construction_prerequisites`). Regenerate `FOUNDATIONAL_FRONTIER.md`
  and `FOUNDATIONAL_DEFINITIONS.tsv` in the same commit. Decision: D18. Check: `just
  foundational-frontier` and `python3 scripts/foundational_definition_index.py` exit 0; the three
  units keep their routes and `[realized]`. Unblocks: every later task.
- [ ] T002 [P] Record for each source its Zotero item key and the key of its extraction
  attachment in `corpus/foundational-source-corpus.md` (data-model.md `Source.item_key`), read
  through the live library (the `zotero` skill, `health()` first); for FC17 name
  `corpus/kerodon-source-units.json`. Record a source that the library does not hold under LC-05.
  Decision: D16. Check: each key resolves to the admitted edition's extraction. Unblocks: the
  source comparisons of every Contract D, R and T.
- [ ] T003 [P] Correct the texts that state "no proof work in Sweep III" to state the boundary of
  D2: `CONTRIBUTING.md` LC-03 and LC-20 (each with a defective contribution beside its
  replacement, constitution E3); `docs/agents/corpus-execution.md`, "Start here", step 4, and the
  last paragraphs of "Sweep III construction boundary"; `docs/agents/corpus-acceptance.md`, the
  paragraph "Descent, closure, representative-independence"; `TODO.md`, the sentence of
  "Execution DAG" that calls the no-proof boundary superseding, and step 4 of "Begin each
  continuation here". Decision: D2. Check: each text read against D2 states the same boundary.
- [ ] T129 Run `just test` on `main` and repair each red step before more authoring (LC-07): the
  axiom audit's `native_decide` proofs in `LeanCategories/Catalogue/Registry/PresentationProbes.lean`
  and `ComparisonProbes.lean` (COMPLAINTS.md, "`native_decide` in the registry probes"; the registry
  part is feature 001's owner surface, the green gate is this task's), and any vacuity-audit failure
  that COMPLAINTS.md, "V1 mathematical source reconciliation", records and the run still shows.
  Decision: D23. Check: `just test` exits 0 with its log (constitution E6).
- [ ] T126 [P] Correct `CONTRIBUTING.md` LC-06 (it names a prose-only commit route that does not
  exist; the commit hook runs `just test-commit`, which runs no check) and LC-07 (its blocker record
  needs the red gate to pass), and add the lesson of COMPLAINTS.md, "#95 — a completed unit's commits
  were force-rewritten off `main`" (fetch before a whole-file commit of a shared file; push against
  the tip that a fetch has just returned); each policy shows a defective contribution beside its
  replacement (constitution E3). Decision: D23. Check: each policy names an existing command.
- [ ] T127 [P] Make `scripts/output_check.py` distinguish an explicit catalogue-interface or
  consumer-intake commit from corpus unit selection, with its regression test in `tests/` on the
  20-commit population of COMPLAINTS.md, "The corpus output check does not classify explicit
  catalogue-interface work" (FR-019). Decision: D23. Check: the test passes and the script's
  verdict on that population is the corrected one.
- [ ] T128 [P] Give the long recipes (`just test`, `just cache`, `scripts/cache-get.sh`) an early
  free-space preflight that compares the free space with the size of the artefacts the step writes,
  and an explicit report of `ENOSPC` (COMPLAINTS.md, "Full host volume can kill Lean gates and strand
  otherwise-green staged work"; GitHub #150). Decision: D23. Check: a run below the threshold stops
  before the step with the diagnostic.

## Phase 2: Consumer intake (US5, constitution M9)

Each consumer request is taken in at once (D9, D23). A task of this phase first compares its
COMPLAINTS.md entry with the source at its own revision; a repair that has landed closes the entry
with its evidence (LC-05, "On resolution"). The task then delivers what remains, with the search of
plan.md "Search before authoring", the source statements read from the library, Contract D for a
definition and Contract T for a theorem.

- [ ] T004 [US5] Search and source the request of COMPLAINTS.md, "Orthogonal groups of orthogonal
  direct sums need their structure theorem": run the search of plan.md "Search before authoring"
  (wreath products, symmetric groups, semidirect products, decomposition uniqueness, lattice
  indecomposability; the FC11 catalogue for a matching unit); open Milnor–Husemoller (6.3)–(6.5),
  Eichler 1952, O'Meara 1963 and Conway–Sloane Chapter 4 through the library and transcribe each
  statement with its item key and locator. Files: the COMPLAINTS.md entry (search record and
  statements). Decision: D9. Check: the entry names each query, surface, hit and locator.
- [ ] T005 [US5] Construct the decomposition of a positive definite integral lattice into
  orthogonally indecomposable summands at the lattice owner (`LeanCategories/Lattices/Valued/Basic.lean`
  `IntegralLatticeCat`, or the owner that M4 selects), as the source states it. Inputs: T004.
  Contract D. Check: tier 1 on the changed modules; Contract R.
- [ ] T006 [US5] Prove Eichler's uniqueness of that decomposition, with the isometry invariance of
  the canonical splitting, in the form transcribed in T004. Inputs: T005. Contract T. Check: tier 1;
  Contract R.
- [ ] T007 [US5] Prove the structure of the orthogonal group of an orthogonal direct sum of
  indecomposables (the summands' orthogonal groups and the component permutations, with the order
  statements of the sources) at `LeanCategories/Lattices/Valued/OrthogonalGroup.lean`
  (`LatticeAutomorphismGroup`, `latticeAutEquivOrthogonalGroup`). Inputs: T006. Contract T.
  Check: tier 1; Contract R.
- [ ] T008 [US5] Prove the checked instance: $\Gamma_{4m}$ is indecomposable for $m \ge 2$
  (Milnor–Husemoller (6.5)). Inputs: T005. Contract T. Check: tier 1; the COMPLAINTS.md entry
  names the proving declarations and stays as the upstream record (LC-11).
- [ ] T112 [US5] #26: $A_M \cong \Gamma^\perp/\Gamma$ for the overlattice $M$ of the graph
  $\Gamma_\gamma$ as one linear equivalence (repair the `HasQuotient` instance path on the
  dual-submodule subtype, or present $M^\vee/M$ through a quotient whose instance path matches); the
  quadratic refinement of $D^\perp/D$ for an arbitrary isotropic subgroup $D$ of $A_L$; $K = S^\perp$
  in $M$ (the primitivity half is `OverlatticePrimitive.lean`). Files:
  `Lattices/Valued/{OverlatticeDiscriminant,OverlatticePrimitive,QuadraticSubquotient}.lean`.
  Source: Nikulin 1980, Prop. 1.5.1, p. 111. Entries: "An overlattice had no lattice object ...",
  "The quadratic refinement of an orthogonal sum's discriminant form ...". Consumer: 003 T007.
- [ ] T113 [US5] #88: the discriminant transport $\alpha_g(L) : A_L \to A_{gL}$ as a functor on the
  translation groupoid of a valued bilinear space, with $\alpha_{\mathrm{id}} = \mathrm{id}$, the
  composition law and $\alpha_g(L) = \rho_L(g)$ when $gL = L$; restate
  `discriminantRangeImage_eq_closure_schreier` as the composite of transports. Files:
  `Lattices/Valued/{DiscriminantFunctor,CuspSchreierImage}.lean`. Entry: "No discriminant transport
  along a translate of an integral lattice".
- [ ] T114 [US5] #88, #171: the per-plane line count of `sec-descent-flags`: the coordinate transport
  of $\Delta$ into $GL(2, \mathbb Z)$ in a chosen basis of $P$, the correspondence of `PlaneLines` with
  $\mathbb P^1(\mathbb Q)$, the index 8 and the parabolic subgroup of $T_{\mathrm{Co}}$, then the count
  (`natCard_cuspOrbits_le_index_GL2` is a bound, not the count); restate `toLine_toSubmodule` at
  `cobleLine` with its instance. Files: `Lattices/Valued/{CuspPlaneIncidence,CuspPlaneLineCorrespondence,CuspPlaneOrbitCount,CobleCusps}.lean`,
  `ForMathlib/ModularCuspsGL2.lean`. Entries: "The per-plane line count of `#88` has no formal
  chain", "`toLine_toSubmodule` at `cobleLine` ...".
- [ ] T115 [US5] #91: define the structure $C$ of the #91 request and its preservation condition at
  $C$'s owner, then $\operatorname{Sym}_C(I)$ as a subgroup of `Equiv.Perm I` and the stabilizer
  under $O(L) \times \operatorname{Sym}_C(I)$ through `Subgroup.comap` of `familyStabilizer`. Files:
  `Lattices/Valued/FamilyStabilizer.lean`. Entry: "Missing definition: `Sym_C(I)`". The registry row
  `lim.groups.product` of the neighbouring entry is feature 001's.
- [ ] T116 [US5] #27: `primitiveEmbeddingLocus.IsClosedUnderIsomorphisms` from `Comma.isIso_left` and
  `Comma.isIso_right` (proved in `ForMathlib/` as upstream candidates); an `IsRegular (2 : ℤ)`
  instance from `IsDomain`, and `negIso_ne_refl` without its hypothesis `h2`. Files:
  `Lattices/Valued/ArrowLoci.lean`, `ForMathlib/`. Entry: "#27 — the arrow-category locus closure
  ...".
- [ ] T117 [US5] #162: the correspondence of the walls of $\mathcal H$ through $I$ with the
  $\mathbb Q$-hyperplanes of $I^\perp/I$, built from the reduced-lattice quotient of the normals, so
  that `semifanArrangement_isLocallyRational_of_traces` takes no correspondence hypothesis; the
  selection of the smallest containing member of Lemma 6.6; $I(C_{J,+}) \subseteq J$ from the bound
  $\dim \le 2$ of real isotropic subspaces; the ambient counting lemma at a conical fibre in
  signature $(2, n)$ in the form the entry states. Files:
  `Lattices/Valued/{SemifanArrangement,ConicalMember,ConicalLocus,LocallyRationalDecomposition}.lean`.
  Source: Looijenga, math/0201218v2, §1B, Def. 6.1, Ex. 6.4, Lemma 6.6. Entries: "The ambient
  counting lemma of Example 4.3 (b) ...", "The common member type exists, but the trace
  correspondence ...".
- [ ] T118 [US5] #167: `StabilizerTransitiveOnWallsThroughLine` for $O(I_{2,9})$ on the
  $\mathbb Q$-hyperplanes through one primitive isotropic line, then `TraceOrbitCover` and the
  hypothesis `hsub` of `semifanArrangement_arithmetic_fibre` from `fibreTrace_comp`,
  `fibreTrace_map_fibreInducedEquiv` and `exists_orbitFamily_of_traceOrbitCover`. Files:
  `Lattices/Valued/{FibreArithmetic,CobleCusps}.lean`. Entry: "The transfer of the ambient orbit count
  ... (#167)".
- [ ] T119 [P] [US5] #37: an order on `FractionRing R` for an ordered domain (`ForMathlib/`, upstream
  candidate); restate `IsLatticeRational` over `RationalSpan ℤ L` and delete the second carrier
  `TensorProduct ℤ ℚ L.obj.carrier`. Files: `Lattices/Valued/RationalPolyhedralCone.lean`. Entry: "No
  order on `FractionRing ℤ` blocks `PointedCone` ...".
- [ ] T120 [P] [US5] #141: `faceBarycenterCoordinates` at a general `N` at its owner, with the
  `Fin (n + 1)` statements by specialization; delete `BarySubdiv.baryWeight`, `baryWeight_mem` and
  their `TODO(LC-12)`. Files: `Topology/{BarycentricSubdivision,BarycentricSubdivisionChainData,BarySubdiv}.lean`.
  Entry: "`faceBarycenterCoordinates` is `Fin (n + 1)`-indexed ...".
- [ ] T121 [US5] #180, #181: compare the family of AET Prop. 4.17(4) with the facial completion of
  Def. 4.16 (derive the relevant-face family from AET's hypotheses, or state the $A_3$ counterexample
  against AET's data); give `coarsenedFamily` the codomain `Set (PointedCone ℝ M)` through
  `maximalConePointed`, with the set-level statements as its comparison; confirm the gallery bridge at
  `ForMathlib/RootSystem/WythoffAscent.lean`. Files:
  `Lattices/Valued/{WythoffSemifan,WythoffCoarsenedFamily}.lean`. Source: Alexeev–Engel–Thompson,
  arXiv:1903.09742v3, Def. 4.16, Prop. 4.17; Maxwell, *Wythoff's Construction for Coxeter Groups*,
  Props. 5.1–5.5. Entries: the four Wythoff and AET entries.
- [ ] T122 [US5] #86: the transport `IsAdmissiblePair.smul` for $\sigma$ in
  `diagramAutomorphismGroup A` (finite type, $\tau|_{\sigma X} = -w_{\sigma X}$ with the uniqueness of
  the longest element, the parabolic Weyl vector coefficients) and the equivalence laws of
  `SameDiagramOrbit`; then the Araki correspondence from the appendix of Kolb, arXiv:1207.6036v2,
  pp. 55–58, with Kac–Wang's classification of involutions of the second kind. Files:
  `Algebra/{RealFormData,SatakeDiagramData}.lean`. Source: Bourbaki, *Lie Groups and Lie Algebras*,
  Ch. IV–VI, V §6.2; Araki 1962. Entries: the two #86 entries.
- [ ] T123 [US5] Research P1, polytopes: finite graded posets with rank-preserving maps and the
  abstract-polytope locus with its automorphisms and forgetful functor; placed convex polytopes with
  their face inclusions, incidence order and map category; polytopal complexes and selected
  triangulations with their categories, face posets, realizations and cocones, compared with
  `Topology/{DeltaComplex,SurfaceTriangulation}.lean`. Entries: "Abstract polytopes need a graded
  incidence category", "Placed convex polytopes need their face inclusions and map category",
  "Polyhedral complexes and selected triangulations need common categorical maps".
- [ ] T124 [US5] Research P1, manifolds: the categories of topological, $C^k$, smooth and complex
  manifolds with their map classes, the dimension predicates and the realification functor; the
  integral-affine group $GL(\Lambda) \ltimes V$, integral-affine atlases and maps, and singular
  integral-affine objects with their regular-locus inclusion (FOUNDATIONS Def. 62.6). Entries:
  "Manifold categories need fixed dimension, degree and realification maps", "Integral-affine atlases
  and singular integral-affine spaces need category owners".
- [ ] T125 [US5] Complex analytic spaces: the structure sheaf of an analytic subset as a sheaf of
  local rings, analytic spaces as locally ringed spaces locally isomorphic to it, the germ ring as
  its stalk, and normality; compare with `Analytic/LocalModel.lean` and delete
  `IsLocallyAnalyticSpace` once its consumers use the owner. Entry: "Missing definitions: complex
  analytic spaces". Consumers: the Baily–Borel stratification of the entry, feature 004 T008.

## Phase 3: Sweep III, the realization-stub audit (US1)

Each stub task applies Contract S to every row of its source in units.md, "Sweep III:
realization-stub-audit population", and writes the marker in data-model.md `MappingRow.verdict`.
Files: the mapping records named there and the Lean files of each row. Check:
`python3 scripts/stub_population.py` lists no row of the source. A closure task applies Contract C
to the source's Definitions cell (data-model.md `LedgerCell.ticked`).

- [ ] T009 [US1] FC05 stub rows (6). Decision: D6 (FC05 Definitions is ticked).
- [ ] T010 [P] [US1] FC13 stub rows (3).
- [ ] T011 [US1] Close FC13 Definitions (244 definitional units). Inputs: T010.
- [ ] T012 [P] [US1] FC06 stub rows (9). FC06 closes in T037.
- [ ] T013 [P] [US1] FC07 stub rows (16). Decision: D6 (FC07 Definitions is ticked).
- [ ] T014 [P] [US1] FC08 stub rows (8).
- [ ] T015 [US1] Close FC08 Definitions (621 definitional units). Inputs: T014.
- [ ] T016 [P] [US1] FC09 stub rows (16).
- [ ] T017 [US1] Close FC09 Definitions (356 definitional units). Inputs: T016.
- [ ] T018 [P] [US1] FC10 stub rows (6).
- [ ] T019 [US1] Close FC10 Definitions (229 definitional units). Inputs: T018.
- [ ] T020 [P] [US1] FC11 stub rows (20). FC11 closes in T048.
- [ ] T021 [P] [US1] FC12 stub rows (4). FC12 closes in T065.
- [ ] T022 [P] [US1] FC14 stub rows (20).
- [ ] T023 [US1] Close FC14 Definitions (175 definitional units). Inputs: T022.
- [ ] T024 [P] [US1] FC15 stub rows (2: `FC15-C06-U009`, `FC15-C06-U012`). Inputs: T001.
- [ ] T025 [US1] Close FC15 Definitions (115 definitional units). Inputs: T024.
- [ ] T026 [P] [US1] FC16 stub rows (12). FC16 closes in T067.
- [ ] T027 [P] [US1] FC17 stub rows (3: `FC17-KER-U00385`, `FC17-KER-U00387`, `FC17-KER-U02683`).
- [ ] T028 [US1] Close FC17 Definitions (861 definitional units). Inputs: T027.

## Phase 4: Sweep III, the pending definition units (US1)

Each task applies Contract D to one unit of units.md, "Sweep III: pending definition units", and
appends `[realized]` in data-model.md `MappingRow.verdict` with the route unchanged
(`MappingRow.route`). Files: the unit's mapping record and its Lean file (named in the row, or the owner that M4
selects in the directory named). Check: tier 1 on the changed modules; `just foundational-frontier`
exits 0 and the unit leaves the pending population; Contract R.

### FC06 Hartshorne (`corpus/chapter-2-schemes-fc06.md`, `chapter-3-cohomology-fc06.md`, `chapter-4-curves-fc06.md`)

- [ ] T029 [US1] `FC06-C02-U156` the divisor $(f) = \sum_Y v_Y(f)\,Y$ of a rational function and the
  principal divisors; `reference-port`. Lean: `LeanCategories/Schemes/Divisors.lean`,
  `LeanCategories/Schemes/PrincipalDivisorData.lean`. Decisions: D3 (re-encode the result-layer
  blocker), D7.
- [ ] T030 [US1] `FC06-C02-U157` linear equivalence and the class group
  $\operatorname{Cl} X = \operatorname{Div} X / \text{principal divisors}$; `reference-port`. Lean:
  `LeanCategories/Schemes/WeilDivisorClassGroupData.lean`. Inputs: T029. Decision: D7.
- [ ] T031 [P] [US1] `FC06-C02-U231` relative $\operatorname{Proj}$ and $\mathcal O(1)$, glued from
  $\operatorname{Proj} \Gamma(U, \mathcal S)$ over affine opens; author. Lean:
  `LeanCategories/Schemes/RelativeProjData.lean` (owner `relativeProjData`, `TODO.md`
  `relative-proj-owner`).
- [ ] T032 [US1] `FC06-C02-U236` the projective bundle $\mathbb P(\mathcal E) = \operatorname{Proj}
  \operatorname{Sym}(\mathcal E)$; author. Lean: `LeanCategories/Schemes/ProjectiveBundleData.lean`.
  Inputs: T031.
- [ ] T033 [P] [US1] `FC06-C02-U265` the sheaf of relative differentials $\Omega_{X/Y}$ from the
  diagonal; author. Lean: `LeanCategories/Schemes/RelativeDifferentialsData.lean`.
- [ ] T034 [P] [US1] `FC06-C03-U107` the duality trace from the sum of residues; author. Lean:
  `LeanCategories/Homological/ResidueTraceData.lean`. Decision: D3.
- [ ] T035 [P] [US1] `FC06-C03-U175` the comparison map from the completion to formal cohomology;
  author. Lean: `LeanCategories/Homological/FormalCohomologyComparisonData.lean`. Decision: D3.
- [ ] T036 [P] [US1] `FC06-C04-U047` secant and tangent lines of $X \subset \mathbb P^n$; author.
  Lean: `LeanCategories/Schemes/ProjectiveCurveLineData.lean`.
- [ ] T037 [US1] Close FC06 Definitions (249 definitional units), Contract C. Inputs: T012,
  T029–T036.

### FC11 Peters–Sterk (records named in units.md)

- [ ] T038 [US1] `FC11-C09-U005` the reduced discriminant $\delta(b)$ of a non-degenerate
  symmetric torsion form; author. Lean:
  `LeanCategories/Modules/Bilinear/Valued/ReducedDiscriminantData.lean`. Decisions: D3, D16 (the
  catalogue omits formula (9.2); read it from the source).
- [ ] T039 [US1] `FC11-C09-U006` the reduced discriminant $\delta(q)$ of a quadratic torsion form;
  author. Lean: `LeanCategories/Modules/Quadratic/Valued/Torsion.lean`. Inputs: T038.
- [ ] T040 [US1] `FC11-C09-U013` the reduced discriminant in
  $\mathsf D(\mathbb Z / p^k \mathbb Z)$; author. Lean:
  `LeanCategories/Modules/Bilinear/Valued/ReducedDiscriminantData.lean`,
  `LeanCategories/Modules/Bilinear/Valued/ResidueFormData.lean`. Inputs: T038, T039.
- [ ] T041 [P] [US1] `FC11-C18-U036` the Milnor fibre and its homology lattice; author; owner under
  M4 in `LeanCategories/Geometry/`. Decision: D3.
- [ ] T042 [US1] `FC11-C18-U043` the construction on the parameter space $\mathbb P_{n,d}$ of
  hypersurfaces through a generic line; author. Inputs: T041.
- [ ] T043 [P] [US1] `FC11-C19-U030` the variation of Hodge structure over the period domain
  $D(\Lambda)$; author; owner under M4. Decision: D3.
- [ ] T044 [P] [US1] `FC11-B-U016` the class $[D] \in H^2(X, \mathbb Z)$ of a divisor and
  homological equivalence; author; owner under M4 in `LeanCategories/Geometry/`.
- [ ] T045 [US1] `FC11-C20-U037` the period domain $\mathring D(M_G^\perp)$; `reference-port`.
  Inputs: T044. Decision: D7.
- [ ] T046 [P] [US1] `FC11-C20-U064` the Shioda–Inose structure; author. Decision: D3.
- [ ] T047 [P] [US1] `FC11-B-U042` the canonical bundle $K_X$ from $\Omega_X^n$; author. Lean:
  `LeanCategories/Geometry/HolomorphicFormSheafData.lean`.
- [ ] T048 [US1] Close FC11 Definitions (388 definitional units), Contract C. Inputs: T020,
  T038–T047.

### FC12 Beauville (records named in units.md)

- [ ] T049 [P] [US1] `FC12-C01-U008` the intersection product $D \cdot D'$ of divisors on a surface;
  author. Decision: D3.
- [ ] T050 [P] [US1] `FC12-C01-U012` the topological interpretation I.10 of the exponential
  sequence; author (definitional clause only).
- [ ] T051 [P] [US1] `FC12-C02-U006` the linear system of a rational map $S \dashrightarrow
  \mathbb P^n$ (II.6); author (definitional clause only; the bijection is Sweep IV).
- [ ] T052 [P] [US1] `FC12-C03-U015` the extension class in $H^1(C, L \otimes M^{-1})$ (III.14);
  author. Lean: `LeanCategories/Homological/SheafExtData.lean`.
- [ ] T053 [US1] `FC12-C03-U018` the tautological bundle $\mathcal O_S(1)$ of
  $S = \mathbb P_C(E)$ (III.17); author. Lean: `LeanCategories/Schemes/ProjectiveBundleData.lean`.
  Inputs: T032.
- [ ] T054 [P] [US1] `FC12-C04-U003` the plane linear system of a birational presentation by
  $\mathbb P^2$ (IV.2(1)); author.
- [ ] T055 [US1] `FC12-C04-U005` the morphism of the resolved linear system after blowing up its
  base points (IV.2(2)); author. Inputs: T054.
- [ ] T056 [US1] `FC12-C04-U006` the resolved linear system as a map of the blow-up (IV.2(3));
  author (definitional clause only; the embedding criterion is Sweep IV). Inputs: T055.
- [ ] T057 [US1] `FC12-C04-U007` the hyperplane class of an embedded blow-up of $\mathbb P^2$ in
  the basis $L, E_i$ (IV.2(4)); author. Inputs: T055.
- [ ] T058 [US1] `FC12-C04-U008` the projection away from a point and the subsystem of curves
  through it (IV.2(5)); author. Inputs: T055.
- [ ] T059 [P] [US1] `FC12-C04-U011` the Veronese surface, the image of $\mathbb P^2$ in
  $\mathbb P^5$ by the complete conic system; author.
- [ ] T060 [US1] `FC12-C04-U013` the Steiner surface, a generic projection of the projected
  Veronese surface to $\mathbb P^3$; author. Inputs: T059.
- [ ] T061 [US1] `FC12-C04-U014` the embedding of $\mathbb F_1$ in $\mathbb P^4$ by $|h + f|$,
  projection of the Veronese surface from a point on it; author. Inputs: T059.
- [ ] T062 [P] [US1] `FC12-C08-U024` the étale double cover of an order-two line bundle with a
  chosen trivialization $L^{\otimes 2} \simeq \mathcal O_X$; author.
- [ ] T063 [P] [US1] `FC12-B-U006` the primary Kodaira surface $L^*/q^{\mathbb Z}$; author; owner
  under M4 in `LeanCategories/Geometry/`.
- [ ] T064 [US1] `FC12-B-U007` the secondary Kodaira surface, a finite free quotient of a primary
  one; author. Inputs: T063.
- [ ] T065 [US1] Close FC12 Definitions (44 definitional units), Contract C. Inputs: T021,
  T049–T064.

### FC16 Humphreys, linear algebraic groups

- [ ] T066 [US1] `FC16-C11-U034` the coroot cocharacters $\alpha^\vee$ of the simple roots and the
  dual root system $\Phi^\vee$; author. Record:
  `corpus/chapter-11-representations-and-classification-of-semisimple-groups-fc16.md`. Decision:
  D3.
- [ ] T067 [US1] Close FC16 Definitions (162 definitional units), Contract C. Inputs: T026, T066.

## Phase 5: Sweep III, the ownership audit (US3)

- [ ] T068 [US3] `audit-authored-definitions`: regenerate the definition index; select the rows
  with an external route (`mathlib`, `package-import`, `reference-port`) whose realization
  introduces a project-local mathematical owner; replace each duplicate with the checked owner,
  keeping a local declaration only where the source interface requires it, with that argument in
  the row. Inputs: every Definitions cell ticked (T009, T011, T013, T015, T017, T019, T023, T025,
  T028, T037, T048, T065, T067). Decision: D19. Check: a final source-ordered pass over the
  selection finds no duplicate owner; tier 1 on each changed module.

## Phase 6: Sweep III, the source-conformance pass and Milestone 2 (US3)

Each task applies Contract R to every definitional unit of its source and records the comparison
in the unit's row; a mismatch reopens the owner and its dependents. Decision: D20. Check: every
definitional row of the source holds a comparison with the declaration at the conformance
revision.

- [ ] T069 [US3] FC01 (519 units). Inputs: T068.
- [ ] T070 [P] [US3] FC02 (203 units). Inputs: T068.
- [ ] T071 [P] [US3] FC03 (130 units). Inputs: T068.
- [ ] T072 [P] [US3] FC04 (184 units). Inputs: T068.
- [ ] T073 [P] [US3] FC05 (377 units). Inputs: T068.
- [ ] T074 [P] [US3] FC13 (244 units). Inputs: T068.
- [ ] T075 [P] [US3] FC06 (249 units). Inputs: T068.
- [ ] T076 [P] [US3] FC07 (197 units). Inputs: T068.
- [ ] T077 [P] [US3] FC08 (621 units). Inputs: T068.
- [ ] T078 [P] [US3] FC09 (356 units). Inputs: T068.
- [ ] T079 [P] [US3] FC10 (229 units). Inputs: T068.
- [ ] T080 [P] [US3] FC11 (388 units). Inputs: T068.
- [ ] T081 [P] [US3] FC12 (44 units). Inputs: T068.
- [ ] T082 [P] [US3] FC14 (175 units). Inputs: T068.
- [ ] T083 [P] [US3] FC15 (115 units). Inputs: T068.
- [ ] T084 [P] [US3] FC16 (162 units). Inputs: T068.
- [ ] T085 [P] [US3] FC17 (861 units). Inputs: T068.
- [ ] T086 [US3] Milestone 2 (`definition-realization-convergence`): every Definitions cell is
  ticked, T069–T085 found no plausible, partial, weakened or over-specialized row, and `just test`
  passes on that revision. Files: `corpus/foundational-corpus-status.md` (unchanged if all
  ticks hold). Performs no other work.

## Phase 7: Sweep II remainder (US2)

- [ ] T087 [US2] Close FC16 Mapping by Contract C for Mapping: every FC16 unit has a parsed row
  (none is missing at `fc549baa`). Decision: D5. Check: the generator exits 0 and reports no
  missing FC16 row.
- [ ] T088 [US2] Write the mapping rows of the 6,812 FC17 units without a row (units.md, "FC17",
  route `missing`), Contract M, in `corpus/foundational-corpus-mapping-fc17-kerodon.md` and its
  chapter records, by Kerodon tag order, each with data-model.md `MappingRow.route`,
  `MappingRow.provenance` and `MappingRow.verdict`. Search in corpus-wide batches
  (`python scripts/formalization_corpus.py batch`), adjudicate per unit. Inputs: T086 (D11).
  Check: the generator reports 0 FC17 units of route `missing`.
- [ ] T089 [US2] Close FC17 Mapping, Contract C for Mapping. Inputs: T088.

## Phase 8: Sweep IV, the theorem units (US4)

Each task applies Contract T to every pending theorem unit of its source (units.md, "Sweep IV:
pending theorem units"), in dependency order with source order as the tie-break, and ends with
Contract C for the source's Theorems cell (data-model.md `LedgerCell.ticked`); each unit's search
record and `[realized]` go in data-model.md `MappingRow.verdict`. Files: the source's mapping
records and the Lean owners of its definitions. Inputs: T086; per source, its ticked Mapping cell. Decisions: D4, D12,
D13. Check: tier 1 per unit; the source leaves the pending population; `just test` at the cell's
closure.

- [ ] T090 [US4] FC01 (420 units).
- [ ] T091 [US4] FC02 (162 units).
- [ ] T092 [US4] FC03 (126 units).
- [ ] T093 [US4] FC04 (83 units).
- [ ] T094 [US4] FC05 (655 units).
- [ ] T095 [US4] FC13 (405 units).
- [ ] T096 [US4] FC06 (646 units).
- [ ] T097 [US4] FC07 (434 units).
- [ ] T098 [US4] FC08 (569 units).
- [ ] T099 [US4] FC09 (346 units), with the TauCeti lower-ramification route for the subgroup,
  antitonicity, normality and initial-term results of `FC09-C02-U125`. Decision: D7.
- [ ] T100 [US4] FC10 (397 units), with the same TauCeti route for `FC10-C04-U005`. Decision: D7.
- [ ] T101 [US4] FC11 (763 units).
- [ ] T102 [US4] FC12 (194 units).
- [ ] T103 [US4] FC14 (267 units).
- [ ] T104 [US4] FC15 (276 units).
- [ ] T105 [US4] FC16 (353 units). Inputs: T087.
- [ ] T106 [US4] FC17 (6,856 units, exercises included). Inputs: T089.

## Phase 9: Continuations of the corpus

- [ ] T107 [US5] `arithmetic-lattice-foundations`: execute the tasks T001–T049 of feature
  [003](../003-arithmetic-lattice-foundations/tasks.md) in their document order. Acceptance: 003
  T049 (every owner row of 003 data-model.md closed, the four theorem programmes' success criteria
  met, `just test` green). Inputs: T086 and the exact theorem units that a 003 task names (D11,
  D22).
- [ ] T108 `refactor-audit`: one corpus-wide pass for duplicated Lean, parallel near-definitions,
  local restatements and misplaced owners; repair each finding at its owner, keeping the realized
  mathematics. Inputs: T107. Decision: D19. Check: a final read finds no identified duplicate or
  ownership defect.
- [ ] T109 `lint-paydown`: pay down the `#lint` suite, unused arguments, simp-normal form, vacuity
  and axiom audits only where the change makes the statement easier to read and to check against
  its source; record the argument in each commit. Inputs: T108.
- [ ] T110 `bloat-audit-loop`: one source-aware pass over reuse, duplicate statements, ownership,
  imports, typeclass and universe design, proof size, rewriting surfaces, test integrity, dead
  bridges and module cohesion; search Mathlib, open upstream work and Reservoir before improving a
  local mechanism. Inputs: T109. Check: every finding repaired or recorded with its blocker.
- [ ] T111 [US5] `abelian-projectivity`: execute the tasks T001–T010 of feature
  [004](../004-abelian-projectivity/tasks.md) in their document order, reusing the FC11 and FC12
  results at their owners. Acceptance: 004 T010 (the four success criteria of the plan, `just test`
  green). Inputs: T110, T125 and 003 T036, T037 (D11, D22).

## Dependencies & Execution Order

- Phase 1 blocks every later phase (T001: the selector; T002: the source locators; T003: the
  acceptance rules that reviewers apply; T129: a green full gate). T126–T128 block nothing.
- Phase 2 (M9 intake) depends only on Phase 1. T113 and T114 share `Cusp*.lean` with T112 and run
  after it; the other intake tasks are independent.
- Phases 3 and 4 produce the Definitions cells; Phase 5 needs all of them; Phase 6 needs Phase 5;
  T086 closes Sweep III.
- Phase 7 follows T086 by scheduling precedence (D11); T105 needs T087 and T106 needs T089.
- Phase 8 needs T086 (D12).
- Phase 9 follows the `Needs` of the `TODO.md` DAG: T107 after Phase 8, then T108, T109, T110,
  T111 (D11). T107 is feature 003 and T111 is feature 004 (D22); 003 T007 needs T112 and 004 T008
  needs T125.

## Parallel Example: Phase 4, FC06

```text
T031 relative Proj        T033 relative differentials
T034 residue trace        T035 formal-cohomology comparison
T036 secant and tangent lines
```

These drafts touch different files and have no open input. Their Lean checks run one at a time
under `flock .tmp/lean.lock`. T032 waits for T031; T030 waits for T029.

## Implementation Strategy

1. Phase 1, then Phase 2: the selector regenerates, the sources resolve, and the consumer request
   is served (MVP for US5).
2. Phases 3 and 4 source by source: each closed Definitions cell is an increment of US1 that a
   mathematician can use.
3. Phases 5 and 6: US3 holds for the whole definitional layer at Milestone 2.
4. Phases 7 and 8: US2 for every unit, then US4 source by source.
5. Phase 9: the continuations.

Each task is committed by explicit pathspec with its record updates; a commit carries
mathematics, not only a marker (corpus-execution.md, "A record update is not a unit of work").
