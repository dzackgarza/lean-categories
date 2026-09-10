---
title: "Ambiguity resolution source map for issues 1 and 4"
---

Survey date: 2026-07-22.

Epistemic status: this is a reference record of a three-agent source survey. Two agents explored transcripts. One explored Downloads. Together they mapped the mathematically underspecified items in lean-lattices issues #1 and #4 to the sources that resolve them.

The rulings quoted below are the *final* settled answers of adversarial ChatGPT threads. Those threads often retract their earlier answers. Coverage caveats are at the end.

## Scope: the underspecified items (letter codes)

From issue #1 (lattice/geometry contract):

- A. Research-theorem trust boundary / axiom retention policy (human-decision blocker 1)
- B. Adjudication of genuine source conflicts (human-decision blocker 2)
- C. Named lattices Dn/E6/E7/II_{p,q}: Gram/sign conventions
- D. Even/quadratic refinement via exact divisibility + polarization
- E. Overlattice <-> isotropic subgroup gluing equivalence
- F. Discriminant forms: lift-based constructions, functoriality on isometry cores
- G. Hyperbolic signature / inertia connection
- H. Coxeter-Vinberg chambers, termination/finiteness, reflections
- I. Folding / Wythoff coarsening
- J. Intrinsic rational cone/fan model in L tensor Q
- K. Toric functor (semigroup algebras, fan-to-scheme)
- L. Type-IV domain from lattice complexification
- M. Period map functor + Torelli
- N. Relative Spec/Proj universal properties; structure sheaf functor
- O. KSBA/MMP (log pairs, discrepancies, dlt, surface MMP, properness)
- P. Stacks/deformation theory (cotangent complex, obstruction spaces)
- Q. Kulikov degenerations, monodromy, integral-affine structures
- R. Semitoroidal compactification, divisor recognition
- S. Exact bibliography/theorem locations

From issue #4 (CategoryGraph):

- T. Classifier fibration over Cat
- U. Inverse classifier equations; role-decorated add/mul magmas; two-operation pullback host; rings as iterated refinement
- V. Registry expression language, generic structural projection, pullback path coherence
- W. Complete Lean normalized category catalogue (Sage 179-row mapping stays research-side)

## Primary authorities

1. Geometric items C to R. The source is Alexeev, Engel, Garza and Schaffler, "Compact Moduli of Enriques Surfaces with a Numerical Polarization of Degree 2", arXiv:2312.03638v2. The PDF is at `~/Downloads/2312.03638v2.pdf`. A faithful 4065-line digest is at `~/Downloads/enriques_degree_2_compact_moduli_study_notes.md`. The digest states every convention explicitly:
   - E8 is negative definite.
   - L = II_{3,19} = U^3 + E8^2, with an explicit basis.
   - Eigenlattices: S_dP = U(2); L_Nik^+ = U^3 + E8(2); L_Nik^- = E8(2).
   - Cusp invariants (r,a,delta): (18,0,0)_1, (18,2,0)_1, (10,10,0)_1, (10,8,0)_1, (8,8,0)_0.
   - Thm 1.1: the normalization of the KSBA closure is semitoroidal, with 5 semifans. The Coxeter toroidal one dominates them.
2. CategoryGraph items T to W. The source is the DSL cluster in `~/Downloads`:
   - `Axioms-in-Magma-Opfibrations.md`.
   - [`DSLDiscussion.zip`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DSLDiscussion.zip#doc). It holds `axiom-classifiers-framework.md`; `Categorical-Foundations.md`, which carries the F.1 citation and Mathlib-anchor table; `sage-conversion-framework.md`; and `mathematical-language-style-guide.md`.
   - `sagecats/`. This is the 179-row normalized mapping ledger. Of those rows, 174 are high-confidence, 3 are medium, and 2 need review. It hosts MagmasWithTwoOperations and GroupsWithSimpleReflections.
   - `sagemath-10.9-category-inventory.zip`, pinned at commit 686dc1a8. It holds 222 category entries, 51 axioms including the test-only Flying and Blue, 17 functorial constructions, and 444 feature declarations.
   - [`category_parent_graph.dot`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=category_parent_graph.dot#doc).
   - [`catdsl_poc.zip`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=catdsl_poc.zip#doc). This is a Lean 4 registry and preferred-functor-path prototype, on lean4:v4.32.0.

## Transcript rulings (paths under ~/agent-transcripts/chatgpt-browser/conversations/)

### C — named lattices/conventions [DEFINITIVE]

- `2026/06/20260615-150743--lattice-embedding-in-k3`. This holds the master S/T table.

  - F_2d: S = <2d>; T = <-2d> + U^2 + E8^2.
  - F_ell: S = U; T = II_{2,18}.
  - F_(2,2,0): S = U(2); T = U + U(2) + E8^2; (r,a,delta) = (20,2,0).
  - F_En: S = U(2) + E8(2); T = U + U(2) + E8(2); (12,10,0).

  STORED PERMANENT RULING: in algebraic geometry, E8 and ADE are always negative definite. And Num(Enriques) = U + E8(-1) = II_{1,9}. It is even, not I_{1,9}.

- `2026/05/20260506-153404--degree-2-enriques-surfaces`.

  - L = II_{3,19} = U^3 + E8^2.
  - Involutions: I_En(v,u,u',e,e') = (-v,u',u,e',e); I_dP = (-v,u',u,-e,-e'); I_Nik = I_dP . I_En.
  - S_En = U(2) + E8(2), of signature (1,9).
  - T_En = U + U(2) + E8(2), of signature (2,10).
  - h = e + f in U(2). Then h^2 = 4 upstairs, and l^2 = 2 downstairs.
  - Scaling: (x, ±x)^2 = 2x^2.

- 2026/05/20260509-135659--ksba-compactification-and-coble + 2026/06/20260619-112614--git-quotient-moduli-space: T_Co=I_{2,9}(2)=<2>+E10(2)=delta-perp in T_En (delta=e-f, delta^2=-2), S_Co=I_{1,9}(2); cusp lattices e-perp/e = I_{1,8}(2), J-perp/J = A1(-1)^7. delta-perp = T_Co is an ISOMETRY not equality (choice of phi matters on quotients).

- 2026/06/20260618-030805--p-r-modular-lattices:

  - two p^r-modular conventions adjudicated (local Z_p Jordan convention standard).
  - I_{s,t}(p^r) always exists, II_{s,t}(p^r) iff s-t = 0 mod 8.
  - genus is the right global invariant.
  - naive "sum of twists of unimodulars" false (A2 counterexample q=2/3).

- 2026/06/20260616-144013--coxeter-vinberg-diagram-d4: all-(-2) D4-shape with m=4 edges NOT integrally realizable; I_{1,3} realization Gram [[-2,-2,-2,-2],[-2,-4,0,0],[-2,0,-4,0],[-2,0,0,-4]].

- GAP: explicit Dn/E6/E7/II_{p,q} Gram matrices not tabulated anywhere; fall back to Conway-Sloane SPLAG ch.15 (cited in Categorical-Foundations F.1).

### D — even/quadratic refinement [DEFINITIVE]

- 2026/06/20260629-073524--lattice-and-discriminant-groups-spec: q(alpha)=alpha^T G^{-1} alpha mod 2Z in the even case; A_L=coker(G); evenness axiom b(x,x) in 2Z.
- 2026/07/20260717-133300--graph-simplification-request:
  - polar(q_B)=2B, diag(polar Q)=2Q, polar.diag=diag.polar=2.
  - q <-> (1/2)polar only when 2 invertible on value module W.
  - EvenLat_Z = Lat_Z x_SymBil Even.
- 2026/07/20260703-181541--sagemath-lattice-theory-issues: Sage factor-of-2 traps (quadratic_form() returns (x,x); Hessian=2*Gram; bilinear_map doc sign trap).
- p-r-modular transcript: parity of L vs parity of rescaled U distinct (I_{s,t}(2^r) even though U odd).

### E — overlattice/gluing [DEFINITIVE]

- lattice-and-discriminant-groups-spec:
  - Nikulin gluing both directions — even overlattices L in L' in L-dual <-> isotropic H in A_L with A_{L'}=H-perp/H.
  - metabolizer/Lagrangian H=H-perp <-> unimodular overlattice.
  - API: isotropic_subgroups, orthogonal_quotient, overlattice_from_isotropic_subgroup, metabolizers.
- ksba-compactification-and-coble: Heegner normalization F_Co,2 = disjoint union over Gamma_En,2-orbit reps of D(r_a-perp)/Gamma_a.
- study notes: D16+ overlattice construction as worked example.

### F — discriminant forms / functoriality [DEFINITIVE]

- graph-simplification-request:
  - DiscBil_Z = Bil_{Z,Q/Z}[Symmetric&Nondegenerate&Finite].
  - DiscQuad_Z = Quad_{Z,Q/2Z} x_SymBil DiscBil_Z (NOT an "Even cut").
  - Disc functors on CORES only (Disc_bil: Core(Lat_Z)->Core(DiscBil_Z)) with explicit counterexample: <2> embedded in [[2,1],[1,2]] admits no covariant map of discriminant groups.
  - O(L)->O(q_L) by applying Aut.
  - genus = pi_0 of local-profile isofiber over Core(Lat_Z)->prod_v Core(Lat_{R_v}).
- lattice-moduli-spaces (2026/06/20260614-222911): Gamma_En=O(T_En) because Nikulin surjectivity O(S)->>O(q_S) holds for INDEFINITE 2-elementary with rank/length hypotheses — 2-elementarity alone insufficient. Degree-2 shrinks to O(S_En,h); div(h)=1, index-4 gluing of <h>+h-perp.

### G — signature/inertia [PARTIAL]

- Conventions fixed (signature pairs, sig(2,n) domains); mirror ruling dim F_S + dim F_S-hat = 20 for 2-elementary mirrors (coxeter-diagram-example). No single inertia-theorem source; Sage signature_pair caveats in sagemath-lattice-theory-issues.

### H — Coxeter-Vinberg [DEFINITIVE on design; theorem statement from AEGS]

- 2026/06/20260608-000807--coxeter-diagram-example:
  - face<->subdiagram dictionary (elliptic order-k subdiagram <-> k-face; parabolic <-> ideal vertex).
  - (2,3,inf) triangle realized in U+A1(-1) with Gram [[-2,0,2],[0,-2,1],[2,1,-2]].
  - Gauss-Bonnet area from Gram.
- 2026/07/20260708-161616--designing-mathematical-dsl:
  - RULING — Vinberg's algorithm must NOT be a primitive.
  - it is a user program in a typed algorithmic calculus (Lattice n, Cone L, RootCandidate L; primitives inner/normSq/enumerateBall/isPrimitive?/asRoot?).
  - termination via repeatUntilFuel, not termination proofs.
- 2026/07/20260713-180633--category-theoretic-lattice-design:
  - computations as TOTAL Lean definitions on the exact subcategory where defined (vinberg on a VinbergInput category carrying cone/root-norm/termination-bound data; no Except, no runtime invalid object).
  - correctness an optional later vinberg_spec theorem. Naming: avoid ZLattice (mathlib collision).
  - use IntegralBilinearLattice.
- 2026/07/20260720-164838--2-category-equivalence-check: three-valued decision honesty (True/False/Unknown; bounded search returns verifiable witnesses; no fabricated negatives) — the termination/finiteness discipline.

### I — folding/Wythoff [from AEGS]

- AEGS §4.1, §6 + study notes: ADE->BC foldings via involutions; ABCDE surfaces.
- ksba-compactification-and-coble RULING:
  - Coble Coxeter diagrams are hyperplane sections of folded Enriques diagrams (not new foldings).
  - Coble semifan = TRACE of Enriques ramification semifan on delta-perp.
- coxeter-vinberg-diagram-d4: Symington IAS polytope conventions for A3/A4-/D4/E6/E8-tilde.

### J — rational cone/fan model [PARTIAL — design still open]

- Face<->subdiagram correspondence + AEGS semifans give the math; NO standalone intrinsic-cone-category proposal exists anywhere. Remaining design decision.

### K — toric functor [DEFINITIVE building blocks]

- coxeter-diagram-example:
  - toric anticanonical pairs.
  - Looijenga charge Q=12-D^2-n, corner blowup preserves Q, interior blowup +1.
  - convention ruling: interior blowup strict transform stays anticanonical, total transform does not.
  - F2 fan rays (0,1),(1,0),(0,-1),(-1,2), moment trapezoid Conv{(0,0),(1,0),(3,1),(0,1)}, polarized Delta_{a,b}.
- Semigroup-algebra universal property: standard theory, no bespoke ruling needed.

### L — Type-IV domain [DEFINITIVE]

- degree-2-enriques-surfaces:
  - D(Lambda)={[x] in P(Lambda tensor C): x^2=0, x.xbar>0} for sig (2,n).
  - D(T_En) dim 10.
  - coxeter-diagram-example: Sym^2 worked example (K=U+<2>, SO+(K)\D_K = PSL2(Z)\H, vol=zeta*(2)).

### M — period map/Torelli [DEFINITIVE]

- degree-2-enriques-surfaces:
  - Enriques Torelli via canonical-cover ANTI-invariant Hodge structure (Mukai twisted H^2(Y,Z^omega), Hodge numbers (1,10,1)).
  - h cuts the ARITHMETIC GROUP not the domain: Gamma_En,2 = im{g in O(L): g commutes with I_En, g(h)=h} -> O(T_En) = Gamma_En intersect Gamma_dP.
- lattice-moduli-spaces:
  - monodromy owned by the VHS, not by T.
  - the clean D(T')/O(T') reformulation of F_En,2 provably does not exist (Gamma_En,2 proper discriminant-congruence subgroup; degree 27.17.31 over F_(10,10,0)).
- lattice-embedding-in-k3:
  - stable orthogonal group formalism O-tilde(L)=ker(O(L)->O(A_L)), GHS §2.5.
  - Gamma_S = {g in O+(T): gbar in im(O(S)->O(A_S))} via Nikulin gluing anti-isometry.
  - = O-tilde+(T) only for pointwise-marked polarizations.
- git-quotient-moduli-space: Dolgachev-Kondo Prop 3.2 (M_Co iso open in D(N)/O(N)) NOT proved by the cited K3-Torelli argument (missing reconstruction/descent) — flagged trust-boundary case.

### N — relative Spec/Proj, structure sheaf [UNRESOLVED]

- No resolving source anywhere in corpus. Only: Spec functor-of-points mention (categorical-spike-vs-dsl mathlib inventory), AEGS uses relative Proj of ramification algebra for the stable model. EGA-standard material; Lean-level design undetermined.

### O — KSBA/MMP [DEFINITIVE rulings]

- ksba-compactification-and-coble:
  - stable pair = (Sbar, eps R) with the SINGULAR quotient carrying one 1/4(1,1) point, not the resolution.
  - K_S = pi* K_Sbar - (1/2)C, 2K_S+C~0, C^2=-4.
  - ampleness descent chain (R_X ~ rho* O(2,2) ample -> descends Q-Cartier -> finite surjective descent).
  - slc via Kollar (du Val -> canonical -> lc; normal lc=slc).
  - branch model (4,4)-curves in P1xP1 invariant under (x,y)->(-x,-y), GIT P^12//(D4 x (C*)^2) (Horikawa/Shah).
- git-quotient-moduli-space:
  - canonical map is contraction kappa: Y->Ybar of B_Y in |-2K_Y|, B^2=-4 -> 1/4(1,1).
  - dimension table |O(6)|=27, Severi 17, /PGL3 = 9, 10-pt quotient 12 (Coble locus codim>=3, NOT open in DK's claimed sense).
- AEGS §5, §7 for the surface theory.

### P — stacks/deformation theory [UNRESOLVED]

- Only a mathlib coverage inventory (categorical-spike-vs-dsl): Bicategory, Pseudofunctor, Grothendieck construction, IsStack, sites/sheaves, schemes, derived category, quasicategories exist upstream. Cotangent complex / obstruction spaces modeling untouched.

### Q — Kulikov/integral-affine [DEFINITIVE]

- coxeter-diagram-example:
  - Type III monodromy N(x)=(x,lambda)e-(x,e)lambda.
  - on <e,lambda,f> matrix [[0,lambda^2,0],[0,0,-1],[0,0,0]].
  - N^3=0, N^2 != 0.
  - IAS shear [[1,1],[0,1]] at singular points (Symington). AEGS §4 for IAS^2/disk/RP^2 and dlt models.

### R — semitoroidal compactification [DEFINITIVE theorem; recognition pitfall flagged]

- AEGS Thm 1.1: 5 semifans; semitoroidal normalization dominated by Coxeter toroidal.
- ~/Downloads/aegs-heegner-prompt.md PITFALL (bears on divisor recognition + B): restriction of a semitoroidal compactification to a Heegner divisor is NOT in general the semitoroidal compactification of the divisor. Two distinct Heegner divisors (Coble (-2)-vector, unigonal) in F_En,2.
- ksba-compactification-and-coble: Coble cusp counts and subdiagram tables explicitly left to-be-computed.

### S — bibliography [PARTIAL-GOOD]

- DSLDiscussion.zip Categorical-Foundations.md §F.1: canonical citation + Mathlib anchor per construction (nLab, Stacks tags 003S/0040/001D/09SE, Riehl, Mac Lane-Moerdijk, Breen Bitorseurs, Cassels, Conway-Sloane SPLAG ch.15).
- AEGS bibliography: [AT21],[AE22],[AE23],[Ste91],[Kol23],[KM98 Def 2.37 dlt],[GHK15a],[Eng18],[EF21],[Cos83],[CD89],[CDL24],[GH16].
- Dolgachev-Kondo arXiv:1201.6093; Dolgachev-Zhang AJM 123 (2001); GHS §2.5; Nikulin Thm 1.1.1.

### T — classifier fibration [DEFINITIVE, corrected]

- 2026/07/20260720-051004--axioms-in-magma-opfibrations (+ ~/Downloads/Axioms-in-Magma-Opfibrations.md): CORRECTED RULING — U: Magmas->Set is NOT an opfibration over arbitrary maps (explicit counterexamples)
  - binary-op classifier E.Op2 := E x_{ExE} Ar(E).
  - axiom classifier = boundary-extension homotopy pullback B.A := B x_{Fun(K_A-boundary,E)} Fun(K_A,E).
  - fibrational only over the core E-iso (moduli of algebra structures).
  - pentagon/A_n/E_n via operad matching diagrams (Lurie HA).
- 2026/07/20260715-121100--infty-categorical-inclusions:
  - Cat_infinity has NO subobject classifier (composition obstruction proof).
  - what exists is the OBJECT classifier = universal (co)cartesian fibration.
  - inclusion = mono = (-1)-truncated functor.
  - full inclusion = ff functor.
- DSLDiscussion axiom-classifiers-framework.md: property/structure/stuff = truncation of classifying fibers (Def 2.1/2.2); coincidence with Alg_O(M) (Result 6.3).

### U — inverse classifier / roles / two-op host [DEFINITIVE]

- axioms-in-magma-opfibrations: conjunction B.(A&A') = B.A x_B B.A' — the two-operation pullback host and rings-as-iterated-refinement pattern.
- sage-category-framework-overview (2026/07/20260720-182224):
  - semantic (not nominal) bijection Sage<->normalized graph.
  - least-host rule (classifier declared once at least natural host, transported by pullback D.A := D x_C C.A).
  - named composites are definitional aliases.
  - three naming layers.
- sagemath-as-dsl (2026/07/20260718-160732):
  - indexed doctrine Mod: Th^op->CAT / Alg: Th->CAT.
  - axiom<->replete subcategory.
  - data<->fibred category.
  - construction<->functor.
  - algorithm<->effective lift through realization rho: C_eff->C.
- sagecats ledger: hosts MagmasWithTwoOperations, GroupsWithSimpleReflections; DivisionRings := Rings.Division; Modules(R) left / Modules(R-op) right.

### V — registry expression language [DEFINITIVE]

- graph-simplification-request:
  - transported classifier C.P := C x_D D.P (= ObjectProperty.inverseImage).
  - property vs structure = replete full subcategory vs forgetful 2-functor (conflating them named the most consequential error).
  - full vocabulary translation table.
  - minimal generating graph with Lat_R = Bil_{R,R}[Symmetric & Nondegenerate & pi*(FinGen & Free)], Unimod via Perfect.
  - form categories are El^op (variance correction vs mathlib covariant Elements).
- lattice-and-discriminant-groups-spec:
  - objects are based free modules (L,e,b).
  - EQUALITY != ISOMETRY (G'=P^T G P is an isometry morphism).
  - no ambient vector space.
  - Sage is a reference implementation to port, not to wrap.
- category-theoretic-lattice-design:
  - category graph = functor I->Cat.
  - axioms = mathlib ObjectProperty->FullSubcategory.
  - chosen data = InducedCategory.
  - heterogeneous Hom via least common supercategory.
- catdsl_poc.zip: working Lean prototype of registry + preferred-functor BFS path resolution.

### W — normalized catalogue [DEFINITIVE Sage side]

- sagemath-categories-and-axioms (2026/07/20260717-153756) + inventory zip:
  - pinned Sage 10.9 commit 686dc1a8.
  - 173 public + 6 wrappers + 38 helpers + 4 test + 1 example = 222.
  - 51 axioms (2 test-only).
  - 17 constructions (covariant/regressive/specialized taxonomy).
  - axiom is locally defined on a category, C.axioms() is runtime closure.
- sage-category-framework-overview:
  - runtime adds 209 axiom-generated + 200 construction-generated + 130 imported (84 joins).
  - named upstream Sage defects (missing PID->Dedekind, PID->Noetherian edges; incomplete Topological/Metric; missing Countable/Uncountable; test axioms in production).
- sagecats/_ledger: the completed 179-row mapping (review-required rows: Groupoid FIXME, FunctionFields, noncommutative Modules).
- mathematical-goal-for-lattice (2026/06/20260605-102740): feasibility encoded by category membership, not annotation layer; jargon renaming without solving the math is laundering.

### A — trust boundary [POLICY SCAFFOLDING DEFINITIVE; final decision = user's]

- categorical-spike-vs-dsl (2026/07/20260716-075259) RULING:
  - Lean/Mathlib owns the lexicon and proof status NOW.
  - Sage = computational backend only.
  - one-way dependency lexicon->contracts->backends. Proof-status model: proved / explicit axiom / assumption / draft sorry / certified mode rejecting unapproved sorryAx.
  - external results enter via certificate-checking or independent recomputation, never a trusted Boolean.
- sage-category-framework-overview:
  - axiom draining-queue policy — use Mathlib.
  - else contribute ForMathlib.
  - else isolated provisional axiomatization only as explicitly approved draining queue.
- designing-mathematical-dsl + category-theoretic-lattice-design: hypotheses/domains in types, algorithmic correctness in optional certificates, not in types.
- git-quotient-moduli-space: concrete precedent — DK Prop 3.2 is a research theorem to axiom-tag with a gap note, not to trust.
- mathematical-goal-for-lattice: category membership = computability contract (claiming gens() = claiming finite generation; f in O(L) checkable even when generators uncomputable for indefinite L).

### B — source conflicts [FOUR PRECEDENTS; no general policy]

1. E8 sign / even II_{1,9} vs odd I_{1,9} (lattice-embedding-in-k3, stored ruling).
2. p^r-modular conventions: local Jordan standard (p-r-modular-lattices).
3. Namikawa orbit-uniqueness holds mod Gamma_En=O(T_En), NOT mod Gamma_En,2 — finite-index subgroups split orbits; discriminant-form orbit counts are candidates only; actual counts need Sterk/Eichler arguments (ksba-compactification-and-coble).
4. Heegner-restriction semitoroidal pitfall (aegs-heegner-prompt.md). Plus: El^op variance sign-slip fix documented in Categorical-Foundations F.4; six unproven Dolgachev-Kondo claims enumerated in git-quotient-moduli-space.

## Genuinely unresolved residue after full sweep

1. N — relative Spec/Proj universal properties + structure-sheaf functor: no source.
2. P — stacks/deformation theory (cotangent complex, obstruction spaces): only mathlib inventory.
3. J — intrinsic rational-cone/fan CATEGORY design: building blocks only.
4. Explicit Dn/E6/E7/II_{p,q} Gram tabulations (conventions settled; use Conway-Sloane).
5. Coble cusp counts / subdiagram tables: explicitly to-be-computed.
6. A and B final sign-off: policy scaffolding exists; issue #1 requires recorded human decisions.

## Coverage caveats

- Explorers read all listed sources at least through conclusions
  - skipped superseded middle drafts of the largest transcripts (graph-simplification ~lines 246-8500 superseded corpus tables; mathematical-goal ~80% doc-audit middle; dsl-for-homotopy-type-theory and sage-based-dm-boundary intermediate drafts).
- AEGS PDF: first pages only; the study-notes digest covers the rest.
- cursor_chat_github_issue_categories_list.json (30MB): identified as raw #251 chat export, not parsed.
- 20260720-170816--study-notes-request transcript contains only a download link + question; content lives in the study-notes file.
- Transcripts irrelevant to items: moduli-spaces-of-sextics (curve moduli), mathematical-bridge-expansion (Oscar/Nemo coercion), sage-based-dm-boundary-modeling (curve boundary, tangential), GitHub-Qual-Review-Repos.md, pr18_implementation_plan.md.

## Historical pending action (2026-07-22)

Externalize this mapping onto the lean-lattices GitHub issues (which are being rearranged) as comments, so every scoped ambiguity is addressed in writing on its owning issue.

## Later disposition (2026-08-11)

The mapping was externalized into the reorganized issue tree. Issue #21 owns conjecture quarantine. Issue #22 owns relative Spec and Proj. Issue #37 owns intrinsic cones and fans. Issue #39 owns stacks and deformation theory. Issue #35 and current [`Standard.lean`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Standard.lean#doc) own ADE and K3 conventions.

Coble cusp counts remain research computations, not a current foundation task. This map is evidence for the 2026-07-22 survey. It is not a live task list.
