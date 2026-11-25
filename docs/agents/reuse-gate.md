## Reuse before you write — the operational gate

Sections 4.3–4.4 and 10.2 give the *principle* (novelty bias, false gaps, mathematical home); this is the *procedure*, and it is a hard gate. **Do not author a new definition, structure, class, or instance until you have searched for an existing one, and if you still write your own, related it to what exists.** The measure of good foundational work is accidental freedom removed (§0); the cheapest way to remove it is to not re-derive what Mathlib or a prior formalization already owns. Minimal reinvention, maximal integration-compatibility with Mathlib, is the standing default — reinvention is the failure mode, never the first move.

Before writing any **foundational-corpus** construct, in order:

1. **Require a Sweep-I source unit.** The mathematical unit must already belong to the frozen
   corpus catalogue with a stable ID, source location, kind, hypotheses/data, and dependencies.
   Do not invent scope from implementation searches or downstream demand.

2. **Require its Sweep-II mapping.** Search pinned Mathlib first, then current upstream Mathlib
   and open work. Query the live [`formalization-corpus`](https://github.com/dzackgarza/formalization-corpus)
   index through its [browser search](https://dzackgarza.github.io/formalization-corpus/) and the
   API described by its [API page](https://dzackgarza.github.io/formalization-corpus/api.html)
   and authoritative live OpenAPI document. For systematic
   work use `python scripts/formalization_corpus.py search '<query>'` (or a generated OpenAPI
   client); the API is required, not merely preferred.
   Search several formulations: standard names, source theorem names, synonyms, characteristic
   type/declaration fragments, and nearby constructions; use `repo:`/`file:` filters only to refine,
   never to shrink the initial search domain. Then use Loogle/LeanSearch/docs, Reservoir, open PRs,
   and broad GitHub search for material not yet indexed or for revision history. Open candidate code
   and compare mathematical generality and hypotheses.
   Apply the [mapping acceptance boundary](corpus-acceptance.md#accept-a-mapping-against-the-whole-source-obligation)
   to the actual declarations; a completed mapping row is not its own semantic evidence.

3. **Reuse before authorship.** A Mathlib or existing project route is used directly. An
   importable external package is imported. A non-importable Lean implementation is preserved
   with exact repository/commit/path/license provenance and ported/adapted from that reference.
   A source-local `unmatched [negative-search-complete]` row is still provisional. Only a unit
   that also survived the corpus-wide open-ended residue audit and carries
   `[residue-search-audited]` is eligible for genuinely new Lean mathematics.

4. **Then realize the definition at its mathematical owner.** A new construct with no stated
   relationship to the standard/source notion is a red flag. Reuse Mathlib's typeclasses,
   category conventions, and morphism classes so the result composes with the library instead of
   shadowing it. Do not create project-local aliases merely to rename dependency declarations.
   Establish the source comparison before exporting the definition or allowing another
   construction to consume it. Apply the
   [construction boundary](corpus-execution.md#sweep-iii-construction-boundary) before any proof work.

5. **Keep search evidence in the mapping record.** The corpus catalogue owns mathematical
   source content; Sweep II owns implementation provenance. Do not create separate ad hoc route
   notes or a residue ledger per downstream consumer. `unmatched` is a dated scoped negative
   search result, never a timeless claim that no formalization exists anywhere. A final
   greenfield-eligible negative row must also contain the reproducible open-ended residue-audit
   evidence required above and the `[residue-search-audited]` marker.

For genuinely new work outside the admitted corpus, the same reuse search applies, but first make
an explicit source/corpus-scope decision rather than silently extending the in-force corpus.

The failure this gate prevents is §4.3 and §4.4: writing a plausible new definition is faster and *feels* more productive than finding the three-line composition of existing constructions that already says it. That is not progress — it is a new maintenance surface and an avoidable comparison theorem later.

---

## External formalization corpus and programme-specific annotations

**The highest priority of this programme is minimizing the lines of Lean owned by this repository.** Re-defining or re-proving mathematics that is already formalized anywhere online is the primary failure mode: every re-derived line is a permanent maintenance surface and an avoidable comparison theorem later.

The canonical evolving external registry is [`dzackgarza/formalization-corpus`](https://github.com/dzackgarza/formalization-corpus), especially its [`SOURCES.md`](https://github.com/dzackgarza/formalization-corpus/blob/main/SOURCES.md). Its [GitHub Pages site](https://dzackgarza.github.io/formalization-corpus/) searches the actual indexed source corpus, and its [API documentation](https://dzackgarza.github.io/formalization-corpus/api.html) links the live OpenAPI contract. **The OpenAPI document is the sole authority for API paths, HTTP methods, request/response schemas, and supported options; do not duplicate those facts in repository policy.** Use the live API as a first-class required discovery surface for every Mapping pass and before recording `unmatched`. The corpus indexes Mathlib, registered Lean repositories, Reservoir packages, and Rocq/Agda/Isabelle/other proof-assistant sources together, so a non-Lean hit can still discharge the obligation to find a reference implementation even when it cannot discharge the Lean import route.

The domain tables below are only programme-specific annotations that may explain why a known source is especially relevant, unsuitable, stale, unlicensed, or already integrated. They are not exhaustive, are not a second source registry, and cannot support a negative search result. When they disagree with `formalization-corpus/SOURCES.md` about what sources exist, update or delete the local annotation rather than forking the registry here.

Strict preference order:

1. **Use the pinned Mathlib declaration** (`.lake/packages/mathlib`) whenever it is at least as general.
2. **Import a packaged library** as a Lake dependency (via Reservoir or a direct git dependency) when the construction lives in an active Lean 4 library.
3. **Copy or port the reference implementation** when the source is unpackaged, toolchain-incompatible, Lean 3, or in another proof assistant. Cite the origin at the ported site: repository, file, and commit or tag.
4. **Author new Lean only after 1–3 fail**, under step 3 of the reuse gate, relating the new construct to what exists in the same PR.

The annotations below were originally assembled as a local registry and therefore contain dated repository/toolchain observations. Treat those observations as hints to recheck, not as current inventory. Any Lean 4 repository, archived or not, is a legitimate pinned dependency exactly when it builds against this repository's toolchain and pinned Mathlib. Lake resolves one version of every package for the whole build graph from the root manifest, so a dependency compiles against this project's Mathlib — the dependency's own older Mathlib pin does not travel with it. A dormant repository often fails that test and then enters as a port with citation; when it passes, prefer the import — it is fewer owned lines. An unmaintained dependency does assign its upkeep here: the Mathlib bump that breaks it converts it to a fork-or-port at that time. GitHub also hosts autogenerated repository farms; provenance of authors/history/license must still be checked before a hit becomes a route.

The hosted corpus is a **discovery index, not final mapping provenance**: its external repositories are current snapshots rather than commit-pinned evidence. After a hit, open the upstream repository and record the exact repository, commit/tag, path, declaration, license, toolchain compatibility, and mathematical comparison in the mapping row. An API hit never substitutes for checking the declaration, and an API outage never counts as evidence for `unmatched`.

The repository client is the normal agent-facing entry point. It loads the live
OpenAPI document on every run, resolves operations from that document, and decodes
base64 chunk matches:

```sh
python scripts/formalization_corpus.py search 'Hasse invariant file:\.lean$'
python scripts/formalization_corpus.py list 'repo:mathlib4'
```

The website exposes direct `curl` examples and generated-client snippets from the live
OpenAPI document. Prefer those upstream instructions over copying their API contract
into this repository.

For mapping work, vary the query rather than treating one zero-result string as exhaustion. The linked API documentation and OpenAPI contract are authoritative for query syntax and options. Search the full corpus first; narrowing filters refine a candidate family and must not prematurely shrink discovery.

### Indexes and search surfaces

| Surface | Use |
| --- | --- |
| [`formalization-corpus` source registry](https://github.com/dzackgarza/formalization-corpus/blob/main/SOURCES.md) | Canonical evolving inventory of indexed formalization repositories, domains, and trust/provenance notes. Do not duplicate this inventory locally. |
| [`formalization-corpus` browser](https://dzackgarza.github.io/formalization-corpus/) | Interactive Zoekt search over the live cross-repository corpus. |
| [`formalization-corpus` API](https://dzackgarza.github.io/formalization-corpus/api.html) | First-class required systematic discovery surface. Use `python scripts/formalization_corpus.py search '<query>'` or a client generated from the live OpenAPI document. The OpenAPI contract, not this repository, owns paths/methods/schemas. Use multiple semantic spellings before a negative verdict. |
| [Lean Reservoir](https://reservoir.lean-lang.org/) | Index of public Lake packages and supplementary package metadata; the formalization corpus also indexes hydrated Reservoir sources. |
| [Loogle](https://loogle.lean-lang.org/) ([`nomeata/loogle`](https://github.com/nomeata/loogle)) | Type-pattern search over Mathlib; also the `lean_loogle` MCP tool. |
| [LeanSearch](https://leansearch.net/) | Natural-language search over Mathlib; also the `lean_leansearch` MCP tool. |
| [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) | Declaration-level documentation for current Mathlib. |
| [100 theorems](https://leanprover-community.github.io/100.html), [1000+ theorems](https://leanprover-community.github.io/1000.html) ([`1000-plus/1000-plus.github.io`](https://github.com/1000-plus/1000-plus.github.io)) | Which named theorems already have a formalization, in which system, and where. |
| [Undergrad math in Mathlib](https://leanprover-community.github.io/undergrad.html) | Coverage map of standard undergraduate material. |
| [Lean community projects page](https://leanprover-community.github.io/lean_projects.html) | Curated list of active formalization projects. |
| [Lean Zulip](https://leanprover.zulipchat.com/) | Search it before concluding nonexistence; in-progress formalizations are announced and discussed there. |
| [`CBirkbeck/LeanBridge`](https://github.com/CBirkbeck/LeanBridge) | Links LMFDB objects to Lean declarations. |

### Mathlib subtrees closest to this programme

The pinned checkout owns these; search them by path before any external source.

| Path | Content |
| --- | --- |
| `Mathlib/CategoryTheory/` | 1-categories, limits, adjunctions, monads, comma and elements constructions, abelian categories, monoidal and enriched categories, bicategories, sites, sheaves, topoi, localization, triangulated categories. |
| `Mathlib/AlgebraicTopology/` | Simplicial sets, nerves, quasicategories, simplicial homotopy theory. |
| `Mathlib/Condensed/` | Condensed sets and condensed abelian groups. |
| `Mathlib/AlgebraicGeometry/` | Schemes, morphism classes, gluing, Spec and Proj. |
| `Mathlib/LinearAlgebra/QuadraticForm/`, `Mathlib/LinearAlgebra/BilinearForm/` | Quadratic and bilinear forms, isometries, orthogonality. |
| `Mathlib/LinearAlgebra/RootSystem/` | Root pairings, root systems, Weyl groups. |
| `Mathlib/NumberTheory/`, `Mathlib/RepresentationTheory/` | Number fields, modular forms, L-series, group representations. |

### Category theory, higher structures, type-theory semantics

| Repository | Content |
| --- | --- |
| [`emilyriehl/infinity-cosmos`](https://github.com/emilyriehl/infinity-cosmos) | ∞-cosmos theory over Mathlib's quasicategories; formal ∞-category theory. |
| [`sinhp/HoTTLean`](https://github.com/sinhp/HoTTLean) | Groupoid and natural models of HoTT; semantics of type theory. `Groupoids/ClovenIsofibration.lean` holds a complete split-classifier story for groupoids: cloven isofibrations, fiber reindexing, `Γ ⥤ Grpd`, Grothendieck reconstruction. |
| [`sinhp/Poly`](https://github.com/sinhp/Poly) | Polynomial functors and locally cartesian closed categories. |
| [`sinhp/LeanFibredCategories`](https://github.com/sinhp/LeanFibredCategories) | Fibred categories *(stale; superseded by Mathlib's `FiberedCategory` tree and `displayed_categories`)*. |
| [`sinhp/displayed_categories`](https://github.com/sinhp/displayed_categories) | Displayed categories — the algebraic presentation of structure over a base; iso-level fibers (`EFiber`), cartesian lifts, Street fibrations *(stale; no LICENSE file — reference only, do not copy)*. |
| [`kim-em/lean-category-theory`](https://github.com/kim-em/lean-category-theory) | Early category-theory experiments, upstreamed into Mathlib *(archived)*. |
| [`rzrn/ground_zero`](https://github.com/rzrn/ground_zero) | HoTT library in Lean 4 *(archived)*. |
| [`gebner/hott3`](https://github.com/gebner/hott3) | HoTT *(Lean 3)*. |

### Algebra, number theory, algebraic geometry

| Repository | Content |
| --- | --- |
| [`ImperialCollegeLondon/FLT`](https://github.com/ImperialCollegeLondon/FLT) | Ongoing Fermat's Last Theorem formalization; substantial reusable commutative algebra, dimension theory, and number theory beyond the headline target. Its `FLT/Mathlib/` staging tree holds small upstream-bound files (integral adeles, tensor-versus-restricted-product equivalences); toolchain and Mathlib pin run ahead of this repo, so port those files rather than depend. Contains no quadratic-form or lattice theory. |
| [`leanprover-community/flt-regular`](https://github.com/leanprover-community/flt-regular) | FLT for regular primes; cyclotomic-field material. |
| [`kbuzzard/ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) | 2025 Clay Summer School project on class field theory. Consumes Mathlib's local-field classes rather than building completion infrastructure; no higher unit groups. |
| [`mariainesdff/LocalClassFieldTheory`](https://github.com/mariainesdff/LocalClassFieldTheory) | Local fields, toward local class field theory. Best external DVR/uniformizer API for completions at height-one primes, but *(no LICENSE file — proof-strategy reference only)*, stale toolchain, and a `sorry` inside its `isDiscrete` instance. |
| [`AntoineChambert-Loir/DividedPowers4`](https://github.com/AntoineChambert-Loir/DividedPowers4) | Divided power structures and the divided-power algebra. The core construction is upstreamed in Mathlib `RingTheory/DividedPowerAlgebra/Init`; the grading and polynomial-law layers are not. No LICENSE file and a partially built source tree: reference only, do not copy code from it. |
| [`YaelDillies/toric`](https://github.com/YaelDillies/toric) | Toric varieties over Mathlib's schemes. |
| [`MichaelStollBayreuth/EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts) | Euler products and L-series. |
| [`MichaelStollBayreuth/Heights`](https://github.com/MichaelStollBayreuth/Heights) | Theory of heights. |
| [`CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB) | Atlas of formalized number theory. |
| [`ANR-FALSE/PadicModForms`](https://github.com/ANR-FALSE/PadicModForms) | p-adic modular forms. |
| [`loefflerd/ModularFormDimensions`](https://github.com/loefflerd/ModularFormDimensions) | Finite-dimensionality of modular-form spaces. |
| [`CBirkbeck/ModularForms_Lean4`](https://github.com/CBirkbeck/ModularForms_Lean4) | Modular forms, largely upstreamed into Mathlib *(stale)*. |
| [`CBirkbeck/DirichletNonvanishing`](https://github.com/CBirkbeck/DirichletNonvanishing) | Nonvanishing of Dirichlet L-functions *(archived)*. |
| [`CBirkbeck/WeilConverse`](https://github.com/CBirkbeck/WeilConverse) | Weil converse theorem. |
| [`AlexKontorovich/PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | Prime Number Theorem and related analytic number theory. |
| [`math-inc/strongpnt`](https://github.com/math-inc/strongpnt) | Strong PNT with complex-analysis infrastructure; AI-generated, human-reviewed. |
| [`teorth/expdb`](https://github.com/teorth/expdb) | Exponent-pair database for analytic number theory. |
| [`b-mehta/ABC-Exceptions`](https://github.com/b-mehta/ABC-Exceptions) | Exceptions to the ABC conjecture. |

### Quadratic forms, lattices, sphere packing

| Repository | Content |
| --- | --- |
| [`thefundamentaltheor3m/Sphere-Packing-Lean`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | Viazovska's dimension-8 sphere packing; E8 lattice. Already integrated here under `Integration/SpherePacking` and `LeanCategoriesSpherePacking/E8`. |
| [`mariainesdff/HassePrinciple`](https://github.com/mariainesdff/HassePrinciple) | Hilbert symbols and the Hasse–Minkowski invariant over general fields (Women in Numbers 7). Definitions in place; the key choice-independence proofs are still `sorry`. Apache 2.0, but the team accepts no outside contributions — copy with attribution. |
| [`roed-math/gq2-lean`](https://github.com/roed-math/gq2-lean) | Dyadic Hilbert symbol over ℚ₂ with Serre's evaluation formula and 2-adic square-class facts, sorry-free and self-contained inside a profinite `G_{ℚ₂}` presentation. Apache 2.0. |
| [`MichaelStollBayreuth/LegendreQF`](https://github.com/MichaelStollBayreuth/LegendreQF) | Legendre's theorem on diagonal ternary quadratic forms; complete but defines no Hilbert symbol, Hasse invariant, or lattice notion. |
| [`jonhanke/quadratic_forms_in_lean`](https://github.com/jonhanke/quadratic_forms_in_lean) | Skeleton only: the library files carry reference comments (Cassels) and a few thin definitions, no theorems; no LICENSE file. Do not mine. |

### Analysis, probability, geometry, dynamics

| Repository | Content |
| --- | --- |
| [`teorth/analysis`](https://github.com/teorth/analysis) | Lean companion to Tao's *Analysis I*. |
| [`fpvandoorn/carleson`](https://github.com/fpvandoorn/carleson) | Carleson's theorem. |
| [`fpvandoorn/BonnAnalysis`](https://github.com/fpvandoorn/BonnAnalysis) | Bonn collaborative analysis seminar (distributions, duality). |
| [`leanprover-community/sphere-eversion`](https://github.com/leanprover-community/sphere-eversion) | Sphere eversion via convex integration; h-principle. |
| [`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion) | Construction of Brownian motion. |
| [`RemyDegenne/testing-lower-bounds`](https://github.com/RemyDegenne/testing-lower-bounds) | Information theory and hypothesis-testing bounds. |
| [`oliver-butterley/SpectralThm`](https://github.com/oliver-butterley/SpectralThm) | Spectral theorem. |
| [`girving/ray`](https://github.com/girving/ray) | Mandelbrot-set results. |
| [`girving/interval`](https://github.com/girving/interval) | Verified floating-point interval arithmetic. |
| [`leanprover-community/lean-liquid`](https://github.com/leanprover-community/lean-liquid) | Liquid Tensor Experiment *(Lean 3; condensed foundations now in Mathlib)*. |
| [`leanprover-community/lean-perfectoid-spaces`](https://github.com/leanprover-community/lean-perfectoid-spaces) | Perfectoid spaces *(Lean 3)*. |
| [`dagurtomas/lean-solid`](https://github.com/dagurtomas/lean-solid) | Solid abelian groups *(stale)*. |
| [`ImperialCollegeLondon/condensed-sets`](https://github.com/ImperialCollegeLondon/condensed-sets) | Early condensed mathematics *(Lean 3)*. |

### Combinatorics, discrete mathematics, logic, foundations

| Repository | Content |
| --- | --- |
| [`teorth/equational_theories`](https://github.com/teorth/equational_theories) | Implication graph between magma equational laws. |
| [`teorth/pfr`](https://github.com/teorth/pfr) | Polynomial Freiman–Ruzsa conjecture and related additive combinatorics. |
| [`YaelDillies/cam-combi`](https://github.com/YaelDillies/cam-combi) (formerly `LeanCamCombi`) | Cambridge graph theory and combinatorics courses. |
| [`YaelDillies/apap`](https://github.com/YaelDillies/apap) (formerly `LeanAPAP`) | Kelley–Meka bound on Roth numbers. |
| [`apnelson1/Matroid`](https://github.com/apnelson1/Matroid) | Matroid theory over Mathlib. |
| [`Ivan-Sergeyev/seymour`](https://github.com/Ivan-Sergeyev/seymour) | Seymour's decomposition theorem for regular matroids. |
| [`madvorak/vcsp`](https://github.com/madvorak/vcsp) | General-valued constraint satisfaction. |
| [`madvorak/duality`](https://github.com/madvorak/duality) | Linear-programming duality. |
| [`siddhartha-gadgil/Polylean`](https://github.com/siddhartha-gadgil/Polylean) | Group extensions and torsion-freeness with computational proofs. |
| [`leanprover-community/con-nf`](https://github.com/leanprover-community/con-nf) | Consistency of Quine's New Foundations. |
| [`flypitch/flypitch`](https://github.com/flypitch/flypitch) | Independence of the continuum hypothesis *(Lean 3)*. |
| [`FormalizedFormalLogic/Foundation`](https://github.com/FormalizedFormalLogic/Foundation) | Mathematical logic: completeness, incompleteness, provability logic. |
| [`avigad/lamr`](https://github.com/avigad/lamr) | *Logic and Mechanized Reasoning* textbook and code. |

### Computational and applied mathematics

| Repository | Content |
| --- | --- |
| [`lecopivo/SciLean`](https://github.com/lecopivo/SciLean) | Scientific computing. |
| [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib) (formerly PhysLean/HepLean) | Physics results in Lean. |
| [`Timeroot/Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo) | Quantum information theory. |
| [`optsuite/optlib`](https://github.com/optsuite/optlib) | Optimization algorithms and convergence proofs. |
| [`verified-optimization/CvxLean`](https://github.com/verified-optimization/CvxLean) | Convex optimization modeling *(stale)*. |
| [`ufmg-smite/lean-smt`](https://github.com/ufmg-smite/lean-smt) | SMT-solver tactics. |
| [`eric-wieser/lean-matrix-cookbook`](https://github.com/eric-wieser/lean-matrix-cookbook) | The Matrix Cookbook, proved. |
| [`leanprover/cslib`](https://github.com/leanprover/cslib) | Computer science library. |
| [`leanprover-community/iris-lean`](https://github.com/leanprover-community/iris-lean) | Iris separation logic port. |
| [`or4nge19/NeuralNetworks`](https://github.com/or4nge19/NeuralNetworks) | Neural networks. |
| [`shetzl/autth`](https://github.com/shetzl/autth) | Automata theory. |

### Statement banks and generated corpora — always search these

| Repository | Content |
| --- | --- |
| [`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) | Formalized conjecture statements. When it has a relevant one, import, reuse, or extend it — never restate it from scratch. Sanctioned home for genuinely-unproved deep statements (conjecture ledger, issue #21). |
| [`facebookresearch/atlas-lean`](https://github.com/facebookresearch/atlas-lean) | ATLAS Autoformalized Textbook Library At Scale. Search for textbook definitions, statements, and dependency chains before reconstructing standard mathematics from prose. |
| [`facebookresearch/algebraic-combinatorics`](https://github.com/facebookresearch/algebraic-combinatorics) | Automatic formalization of Grinberg's *Algebraic Combinatorics*. |
| [`facebookresearch/autoform-bot`](https://github.com/facebookresearch/autoform-bot), [`facebookresearch/repoprover`](https://github.com/facebookresearch/repoprover) | ATLAS formalization pipeline and textbook-formalization research code; use to locate generated corpora and source projects. |
| [`facebookresearch/LeanUniverse`](https://github.com/facebookresearch/LeanUniverse) | Index and manager of Lean libraries and datasets. |
| [`facebookresearch/abel`](https://github.com/facebookresearch/abel), [`facebookresearch/Evariste`](https://github.com/facebookresearch/Evariste) | Proof-search systems and their corpora. |
| [`dwrensha/compfiles`](https://github.com/dwrensha/compfiles) | Catalog of formalized competition problems. |
| [`ShouqiaoW/erdos`](https://github.com/ShouqiaoW/erdos) | Erdős problems: checked proofs, partially formalized in Lean. |
| [`trishullab/PutnamBench`](https://github.com/trishullab/PutnamBench) | Putnam problems in Lean 4, Isabelle, and Coq. |
| [`google-deepmind/alphaproof-nexus-results`](https://github.com/google-deepmind/alphaproof-nexus-results) | AlphaProof-generated Lean proofs with prose companions. |
| [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti) | AI-implemented, human-directed library downstream of Mathlib. |
| [`mo271/FormalBook`](https://github.com/mo271/FormalBook) | Aigner–Ziegler, *Proofs from THE BOOK*. |

### Textbook companions and worked proof corpora

| Repository | Content |
| --- | --- |
| [`leanprover-community/mathematics_in_lean`](https://github.com/leanprover-community/mathematics_in_lean) | *Mathematics in Lean* tutorial. |
| [`hrmacbeth/math2001`](https://github.com/hrmacbeth/math2001) | Proof-writing course, paper and Lean. |
| [`djvelleman/HTPILeanPackage`](https://github.com/djvelleman/HTPILeanPackage) | *How To Prove It* companion. |
| [`PatrickMassot/GlimpseOfLean`](https://github.com/PatrickMassot/GlimpseOfLean) | Fast introduction to theorem proving. |
| [`leanprover-community/NNG4`](https://github.com/leanprover-community/NNG4) | Natural Number Game. |

### Core libraries and infrastructure

| Repository | Content |
| --- | --- |
| [`leanprover-community/batteries`](https://github.com/leanprover-community/batteries) | Extended standard library. |
| [`leanprover-community/aesop`](https://github.com/leanprover-community/aesop) | White-box proof automation. |
| [`leanprover-community/duper`](https://github.com/leanprover-community/duper), [`leanprover-community/lean-auto`](https://github.com/leanprover-community/lean-auto) | Automated theorem proving in Lean. |
| [`leanprover-community/plausible`](https://github.com/leanprover-community/plausible) | Property-based counterexample search. |
| [`leanprover-community/repl`](https://github.com/leanprover-community/repl) | Programmatic proof checking. |
| [`PatrickMassot/leanblueprint`](https://github.com/PatrickMassot/leanblueprint) | Formalization blueprint infrastructure. |
| [`siddhartha-gadgil/LeanAide`](https://github.com/siddhartha-gadgil/LeanAide) | AI aids for autoformalization. |

### Other proof assistants — porting sources only

| Repository | Content |
| --- | --- |
| [`UniMath/UniMath`](https://github.com/UniMath/UniMath) | Univalent mathematics in Rocq/Coq; large formal category-theory corpus. |
| [`HoTT/Coq-HoTT`](https://github.com/HoTT/Coq-HoTT) | Homotopy type theory in Rocq/Coq. |
| [`math-comp/math-comp`](https://github.com/math-comp/math-comp), [`math-comp/odd-order`](https://github.com/math-comp/odd-order) | Mathematical Components; the Odd Order Theorem. |
| [`rocq-community/corn`](https://github.com/rocq-community/corn) | Constructive mathematics repository at Nijmegen. |
| [`UniMath/agda-unimath`](https://github.com/UniMath/agda-unimath) | Univalent mathematics in Agda, including extensive category theory. |
| [`agda/cubical`](https://github.com/agda/cubical) | Cubical Agda library. |
| [`the1lab/1lab`](https://github.com/the1lab/1lab) | Cross-linked HoTT reference in cubical Agda. |
| [`martinescardo/TypeTopology`](https://github.com/martinescardo/TypeTopology) | Topology and logic from the univalent point of view, in Agda. |
| [Isabelle Archive of Formal Proofs](https://www.isa-afp.org/) | Searchable archive of Isabelle developments by topic. |

---
