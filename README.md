# lean-categories

The centralized Lean baseline of categorical constructions. Downstream projects require
this package and import the trees they need; no construction is duplicated downstream.

The repository owns as little Lean as possible. It uses Mathlib directly, imports packaged
libraries as Lake dependencies, and ports reference implementations with provenance when no
package exists. It authors new Lean only for mathematics that a documented search has shown to
exist nowhere else. A shorter repository that imports more is the better repository.
[AGENTS.md](AGENTS.md) owns the reuse gate and the formalization source registry.

`LeanCategories` is one category-theory library and one Lean namespace. The source tree
uses mathematical owners and support roles:

```text
LeanCategories/
  Algebra/
  Modules/
  Lattices/
  Core/
  ForMathlib/
  Model/
  Names/
  Presentation/
  Realization/
  Registry/
  Specimen/
  Tools/
  Util/
```

This repository is the single mathematical authority of the programme. It owns all mathematics
that the computer algebra language
[`lean-cas-dsl`](https://github.com/dzackgarza/lean-cas-dsl) means: categories, functors,
classifiers, operations (every user-facing method), coherences, and typed constructors and
families. It also owns their registration as the language's semantics.

`lean-cas-dsl` requires this package and derives the language from a pinned release. It owns
resolution, the registration of opaque implementations (over Sage, GAP, Julia and other engines)
for catalogue operations, the leaf API and the notebook, and it owns no mathematics. Nothing an
implementation supplies is consulted for meaning; its answers are judged only by the
`lean-cas-dsl` acceptance suite. The semantic registry it reads, the catalogue, is here
(`LeanCategories/Catalogue/`, namespace `CasCatalogue`). The contract is
[`lean-cas-dsl/specs/architecture.md`](https://github.com/dzackgarza/lean-cas-dsl/blob/main/specs/architecture.md).

The support directories describe the same mathematical library. They do not define a
second category system. `Core` and `Model` define the common language. `Realization`
connects it to Mathlib. `Registry`, `Specimen`, and `Tools` inspect and export that
language.

The core module foundation includes truncated free resolutions — free covers and bases — and
coordinatized modules with arbitrary index types: `FreeCover R I`, `BasedModule R I`, and
`Coord R I`.
These declarations use `Finsupp`, not a finite-only representation. The lattice foundation
includes even integral lattices as a full subcategory. It also includes coordinatized
integral lattices as a categorical pullback. The comparison functor forgets the selected
coordinates and returns the intrinsic lattice.

The current finite catalogue rows remain the `I := Fin n` specializations. The catalogue
also registers the arbitrary-index `FreeCover(R, I)`, `BasedModule(R, I)`, and `Coord(R, I)`
families, categories, and forgetful functors. The arbitrary-index lattice-coordinate
category remains open. No matrix, Gram, or determinant comparison is claimed complete.

Scheme theory, stacks, manifolds, and period constructions remain roadmap targets.
Issues #38, #39, and #40 own their prerequisite order. No placeholder source represents
those domains. The foundational corpus is dependency-ordered, with its frozen v1 base and
explicit v2/v3 amendments, and is developed
in four separate passes: catalogue every formal source unit; exhaustively map every unit against
Mathlib and the broader formalization ecosystem; realize the remaining definitional layer at its correct
categorical owners; then formalize the remaining source lemmas and theorems. Only units that
survive the mapping sweep as genuinely unmatched are greenfield formalization. The theorem pass
is deliberately independent so long proof programmes do not freeze growth of the mathematical
DSL. [`TODO.md`](TODO.md), the
[source/snapshot manifest](corpus/foundational-source-corpus.md), the
[central four-phase status ledger](corpus/foundational-corpus-status.md), and
[FEATURE-FOUNDATIONAL-CORPUS](.agents/plans/features/FEATURE-FOUNDATIONAL-CORPUS/FEATURE-FOUNDATIONAL-CORPUS.md)
own the current corpus execution state.

Definition-layer ecosystem discovery is deliberately bulk rather than source-serial. The generated
[`FOUNDATIONAL_DEFINITIONS.tsv`](FOUNDATIONAL_DEFINITIONS.tsv) joins every Sweep-III definition,
construction, notation, and convention to its source data and current mapping. Refresh and search it
with:

```bash
python scripts/foundational_definition_index.py
python scripts/foundational_definition_candidates.py
```

The second command uses the live Formalization Corpus batch operation resolved from its OpenAPI
document and writes resumable candidate checkpoints under `.tmp/`. Candidate hits are discovery
evidence only; canonical semantic routes remain in `corpus/` mapping records. A greenfield
`unmatched` disposition requires the finite negative-search gate recorded in `AGENTS.md`.

Method exposure, backend routing and the execution of registered implementations belong to
[`dzackgarza/lean-cas-dsl`](https://github.com/dzackgarza/lean-cas-dsl). Sage labels, category
graphs and implementation details do not define this library.

```bash
just cache
just build
```

## The foundational corpus

<https://dzackgarza.github.io/lean-categories/> publishes the survey behind the reuse
gate: 16 graduate textbooks read unit by unit, each definition and theorem routed to the
Lean declaration that owns it or recorded as having no owner, at a pinned Mathlib commit.
Its unmatched rows are this repository's formalization roadmap.

`site/` holds the pages. They are generated from the project's reference notes by
`just site-build`, previewed with `just site-preview`, and deployed by
[`.github/workflows/site.yml`](.github/workflows/site.yml) on every push that touches them.

## Mathematical design

This repository builds one higher-categorical mathematical language and its Lean
formalization. The broader programme has three coupled outputs with explicit ownership:

1. **A mathematical foundation in this repository, assembled in Lean from existing formalizations,** in which categories,
   higher categories, classifiers, functors, higher cells, limits, operations, and
   categories of structured objects have principled definitions.
2. **Opaque implementations registered in `lean-cas-dsl`** for the semantic operations
   declared here, over Sage and other engines. An implementation holds no semantic
   authority: nothing it supplies about its values is consulted, and its answers are judged
   only by the `lean-cas-dsl` acceptance suite.
3. **A computational mathematics DSL in `lean-cas-dsl`** in which a mathematician
   introduces and interrogates objects by ordinary membership and notation, while
   formalization and backend routing remain invisible.

The conceptual compression: structures and axioms are **classifier morphisms**; an
assertion of structure is a **lift**; transport is **(homotopy) pullback**; compatible
structures are imposed by a **limit**; comparisons are **higher cells**; equations and
coherence come from **operation-built diagrams and fillers**; a named special object is
usually a **value of a generic functor**; a theorem is a **factorization, lift, or
comparison** — never data baked into a definition; computation is inherited along the
same functorial structure. The current code is a 1-/2-truncated *realization* of that
foundation, never the foundation itself.

Work is aligned when it is stated at the lowest level at which it is generated, in
standard mathematics auditable by a working mathematician, such that later domains
(monoidal categories, stacks, spectra, derived objects, general limits) become instances
rather than refactors.

The full orientation — including the anatomy of agent drift and the alignment lens every
task should pass through — is [AGENTS.md](AGENTS.md). The **mathematical constitution** —
the definitions, variance conventions, truncations, exact sequences, and settled
conventions this repository formalizes — is [FOUNDATIONS.md](FOUNDATIONS.md)
("Mathematical Foundations of the Categorical Research Language", 66 sections: the
(∞,2)-ambient, classifiers and lifts, operation and diagram-extension classifiers, forms
and intrinsic lattices, discriminant theory, sites/stacks/deformation theory, full diagrams
of categories and their limits and colimits, the computational-language semantics, categorical presentations,
exact packages, and convex/reflection/period/degeneration geometry). AGENTS.md governs
*how* agents work; FOUNDATIONS.md governs *what* the mathematics is. The governing
execution state is the issue ledger
([#1](https://github.com/dzackgarza/lean-categories/issues/1): north star, decision
records) and the consolidated work units (#30–#40, #21–#29, #49, #53–#54).
