---
title: "Lean formalization source atlas and research log"
---

## Purpose

This log routes future formalization work to prior implementations.

The unit of record is a mathematical subject area or construction family.

Direct import is only one form of reuse. Old code can supply definitions, theorem statements, proof plans, and dependency decompositions.

Lean versions and licenses do not decide research value. Check them only when direct dependency or public distribution becomes relevant.

Before new work, use this order:

1. Search the pinned Mathlib source.
2. Search the source areas in this log.
3. Inspect exact declarations and proofs.
4. Write new code only after these checks.

A negative result applies only to the inspected source and commit.

## Source index

- [Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean), commit `bad3de916074748eb88b7d1ee6dbf9494361ad17`
- [atlas-lean](https://github.com/facebookresearch/atlas-lean), commit `34ffed396f376454c1a9b297f3fd74c5c801fb50`
- [riemann-roch-function-fields](https://github.com/vaca22/riemann-roch-function-fields), commit `dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`
- [LeanFibredCategories](https://github.com/sinhp/LeanFibredCategories), commit `a58604a389544523aa171daf890386fb8317568b`
- [formal-conjectures](https://github.com/google-deepmind/formal-conjectures), commit `b123bb89b5978ae6b648159e430c4e4dce161b97`
- [FLT](https://github.com/ImperialCollegeLondon/FLT), commit `d18b563029f32a6855f46cdd0edaab39ccc5b8f5`
- [lean-liquid](https://github.com/leanprover-community/lean-liquid), commit `087fffad55dc1dd8d54ab35c9816926a45b8c0fd`
- [lean-stacks-project](https://github.com/kbuzzard/lean-stacks-project), commit `b57be17aa917f1c3a23c59db5ee37b1aa21112c2`
- [lean-scheme](https://github.com/ramonfmir/lean-scheme), commit `6d3ec18fecfd174b79d0ce5c85a783f326dd50f6`
- [Prove2Me](https://prove2.me), live API corpus, no commit pin
- [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem), commit `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`

Pinned Mathlib is commit `db584cd6d46c92f209a44c0f1c829460d327499d`, the `v4.33.0` tag, on Lean 4.33.0.

## Domain routing map

### Bilinear forms, quadratic forms, and lattices

Search these sources:

- pinned Mathlib form theory and `QuadraticModuleCat`
- `SpherePacking/Basic/E8.lean`
- `SpherePacking/ForMathlib/ZLattice.lean`
- Atlas `AlgebraNotes`, `ArithmeticGeometry`, and `Buildings`
- FLT linear algebra, tensor product, norm, valuation, and quadratic-extension additions

Use Sphere-Packing-Lean for concrete integral E8 constructions and proofs.

Use Atlas as a large theorem and definition index. Check each target declaration before reuse.

No inspected source yet supplies the full general classification of formed lattices or discriminant torsion modules.

### Categories, fibrations, sites, sheaves, descent, and homological algebra

Search these sources:

- pinned Mathlib `CategoryTheory`, `CategoryTheory/Sites`, and ringed-space modules
- LeanFibredCategories
- lean-liquid `for_mathlib`, `condensed`, and homological directories
- Atlas `TensorCategories` and `AlgebraicTopologyI`
- FLT category, homology, topological module, and continuous representation additions

LeanFibredCategories covers cartesian lifts, fibred structures, fibers, total categories, Grothendieck fibrations, codomain fibrations, discrete fibrations, and strictification.

Lean-liquid covers abelian sheaves, derived categories, Cech constructions, universal delta functors, simplicial objects, Ext, and systems of complexes.

### Presheaves, sheaves, locally ringed spaces, spectra, and schemes

Search these sources:

- pinned Mathlib `Topology/Sheaves`
- pinned Mathlib `Geometry/RingedSpace`
- pinned Mathlib `AlgebraicGeometry`
- lean-scheme `sheaves`, `spectrum_of_a_ring`, `scheme.lean`, and `instances`
- lean-stacks-project Stacks-tag files
- formal-conjectures `FormalConjecturesForMathlib/AlgebraicGeometry`

Pinned Mathlib supplies the current category-theoretic public foundation.

Lean-scheme and lean-stacks-project remain reference implementations for concrete constructions and proof decomposition.

### Commutative algebra and localization

Search these sources:

- pinned Mathlib ring theory
- lean-scheme `to_mathlib`
- lean-stacks-project localization and commutative-algebra files
- FLT `Mathlib/RingTheory`
- Riemann-Roch divisor and localization support

The old scheme projects give explicit universal-property proofs, localization-away maps, ideal transport, and local-ring arguments.

FLT adds large families around local rings, valuation rings, Dedekind domains, tensor products, completions, and base change.

### Number fields, valuations, adeles, Galois theory, and deformations

Search FLT first.

Its project-owned classes include:

- inverse limits of topological algebras
- pro-Artinian and residue algebras
- deformation and lift functors
- framed and unframed Galois representations
- base change, determinant, trace, flatness, and ramification conditions
- absolute Galois groups, inertia, and Frobenius
- finite and infinite completions
- finite and infinite adeles
- restricted products
- infinite places and their extensions
- discriminant bounds

Its `Mathlib` directory also contains 126 support modules.

Those modules cover algebra, topology, measure theory, field theory, local algebra, valuations, representation theory, and elliptic curves.

Search anthropics/fermats-last-theorem second. It carries completed proofs of the Frey-Serre-Ribet-Wiles route, including adic completions, patching data, Hecke operators, and Galois actions.

### Function fields, divisors, curves, and Riemann-Roch

Search riemann-roch-function-fields first.

It covers:

- intrinsic places
- coordinate and place equivalences
- Dedekind-domain divisors
- fractional ideals and divisor groups
- adele spaces
- Riemann-Roch spaces
- genus and ramification
- Weil differentials
- canonical divisors
- duality and Clifford
- Riemann-Roch and its corollaries
- elliptic-curve genus and Picard-torsor applications

This is a full theorem development, not only a statement catalogue.

### Elliptic curves and arithmetic geometry

Search these sources:

- pinned Mathlib elliptic-curve modules
- FLT `Mathlib/AlgebraicGeometry/EllipticCurve`
- riemann-roch-function-fields `RiemannRoch/EllipticCurve`
- Atlas `EllipticCurves` and `ArithmeticGeometry`

The sources cover Weierstrass models, affine points, automorphisms, variable changes, reduction, Galois descent, genus, places, and Picard data.

### Topology, manifolds, Lie theory, and differential geometry

Search Atlas subject areas:

- `GeometryOfManifolds`
- `DifferentialGeometry`
- `DifferentialAnalysis`
- `LieGroups`
- `AlgebraicTopologyI`
- `RealAnalysis`
- `ComplexVariables`
- `FourierAnalysis`

Search FLT for topological algebra, module topology, restricted products, and locally compact arithmetic spaces.

### Modular forms, Fourier analysis, and sphere packing

Search Sphere-Packing-Lean first.

It covers:

- sphere packings and periodic packings
- E8
- the Cohn-Elkies linear-programming bound
- upper half-plane and cusp infrastructure
- modular and cusp forms
- slash actions
- Eisenstein series
- Jacobi theta functions
- Ramanujan identities
- q-expansions
- Fourier analysis and Schwartz functions
- radial Schwartz functions
- the magic-function construction
- the dimension-eight sphere-packing theorem

### Condensed mathematics and controlled homological algebra

Search lean-liquid first.

Its subject areas include:

- condensed objects
- profinite objects
- abelian sheaves
- derived and homological constructions
- Cech complexes
- pseudo-normed groups
- polyhedral lattices
- rescaling and filtrations
- locally constant functions
- Laurent and real measures
- Breen-Deligne complexes
- Ext vanishing and the liquid tensor theorem

Lean 3 prevents direct import. It does not reduce the source's value as a formalization blueprint.

### Broad theorem and conjecture statements

Search formal-conjectures for statement forms, auxiliary definitions, and missing vocabulary.

Its `FormalConjecturesForMathlib` tree contains reusable support definitions.

Relevant current files include:

- `AlgebraicGeometry/ProjectiveSpace.lean`
- `AlgebraicGeometry/VectorBundle.lean`
- number-theory divisor support
- linear and special linear groups
- topology, manifolds, geometry, and combinatorics support

Most files state results rather than prove foundational theories. Treat them as vocabulary and interface leads.

## Source-area records

### lean-scheme

The inspected source has 65 Lean files and no `sorry` or `admit` matches.

The source contains these construction families:

- open covers and covers on bases
- presheaves of types and rings
- morphisms and isomorphisms of presheaves
- pushforward and pullback operations
- sheaf locality and gluing
- presheaves and sheaves on topological bases
- extension from a basis to all open sets
- stalks and stalks on bases
- sheaves of rings and local stalks
- locally ringed spaces and their morphisms
- prime spectra and Zariski topology
- basic open sets and induced spectrum maps
- compactness of spectra and basic opens
- structure presheaves on standard opens
- localization descriptions of sections and stalks
- structure-sheaf locality and gluing proofs
- affine schemes and the empty scheme
- restrictions and gluing of sheaves and locally ringed spaces
- experimental categorical sites and sheaves
- an explicit two-chart projective-line construction

The `to_mathlib` area contains support families for ideals, local rings, localizations, ring maps, finite sums, opens, and topology.

Pinned Mathlib now owns general forms of most public foundations.

Keep lean-scheme as a concrete proof and dependency reference. Do not reduce it to one isolated example.

### lean-stacks-project

The source organizes much of the scheme foundation by Stacks Project tags.

Its main tag groups are:

- `006E`, `006N`, `006T`, and `0072`: presheaves and sheaves
- `0078` and `007N`: stalks
- `009H` through `009P`: presheaves and sheaves on bases
- `00BV` through `00CD`: localization support
- `00DY` through `00EJ`: spectra, Zariski topology, standard opens, and compactness
- `01HR` and `01HS`: the structure sheaf and its local descriptions

Other source families include:

- direct limits
- ideal lattices and operations
- maximal and minimal prime ideals
- exact sequences
- tensor products
- localization universal properties
- canonical localization isomorphisms
- the scheme structure

Lean-scheme refactors many of these constructions.

Keep lean-stacks-project for its tag-indexed theorem order and alternate proof decomposition.

### FLT

The prior audit inspected only one finite-flat group-scheme file. That slice did not represent the repository.

The repository has 153 Lean files in the inspected checkout.

Its project-owned areas include `Deformations`, `NumberField`, `GroupScheme`, and the final proof.

Its 126 `Mathlib` support files form a large reusable extension library.

High-value classes include:

- deformation theory and representability
- continuous and framed Galois representations
- Frobenius and inertia
- pro-Artinian algebras and inverse limits
- number-field completions and adeles
- restricted products and Haar-measure support
- valuation and local-ring theory
- Dedekind-domain theory
- tensor-product and finite-free linear algebra
- topological modules and continuous algebra maps
- continuous representation theory and cohomology
- elliptic curves, reduction, automorphisms, and Galois descent

This source requires class-level searches before any new work in these areas.

### Sphere-Packing-Lean

The repository has 78 Lean files at the inspected commit.

Its value is much broader than E8.

Use it for concrete lattice data, sphere-packing geometry, modular forms, Fourier analysis, radial Schwartz functions, and analytic bound machinery.

`SpherePacking/Basic/E8.lean` supplies concrete E8 data and proofs.

Named declarations include `Submodule.E8`, `E8Matrix`, `E8Basis`, `E8Lattice`, and `E8_ℤBasis`.

The surrounding files show how E8 interacts with periodic packings and the analytic proof.

### riemann-roch-function-fields

The repository has 37 Lean files at the inspected commit.

It gives a coordinated development from places and divisors through Riemann-Roch.

Its coordinate-free public API and coordinate comparison are both useful patterns.

Use it as the primary source for function-field curve theory until equivalent work enters Mathlib.

### LeanFibredCategories

The repository supplies reference implementations for:

- cartesian morphisms and cartesian lifts
- fibers
- total categories
- Grothendieck fibrations
- codomain fibrations
- discrete fibrations
- vertical lifts
- Chevalley criteria
- strictification

Pinned Mathlib has newer related infrastructure.

Use both sources when a current Mathlib construction is difficult to locate or understand.

### lean-liquid

The repository has 412 Lean files.

Its 196 `for_mathlib` files alone cover many category, homological, profinite, and analytic prerequisites.

The remaining project areas give complete examples of large dependency graphs built from those foundations.

Use the source by subject directory. Do not dismiss it because it uses Lean 3.

### atlas-lean

The repository has 2,654 Lean files across complete textbook-scale subject areas.

Its major areas include:

- algebra and tensor categories
- algebraic geometry and arithmetic geometry
- buildings
- elliptic curves and number theory
- algebraic topology
- manifolds and differential geometry
- Lie groups
- real, complex, Fourier, and functional analysis
- probability
- combinatorics and optimization

This is a source atlas, not one uniform-quality formalization.

Search the relevant textbook area before greenfield work. Then inspect the exact declaration and its mathematical content.

### formal-conjectures

The repository has 1,143 Lean files at the inspected commit.

It is a large index of formal statement shapes and supporting definitions.

Use its source and citation structure when a later theorem needs an accepted formal interface.

Inspect proof holes and auxiliary definitions per file. Do not infer maturity from repository size.

### Prove2Me

Prove2Me is a live platform of Lean 4 missions, one paper or textbook each. Agents submit proofs that a server type-checks. Completed missions carry accepted Lean solutions.

The corpus covers optimization, probability, Markov chains, bandit algorithms, control theory, optimal transport, number theory, and algebraic topology. Coverage of category theory and homological algebra is not yet inspected.

Public web pages show only the statement, the preamble, and the status. The proof code needs the API.

Read access:

```bash
direnv allow                       # PROVE2ME_API_KEY lives in ~/.envrc
TOK=$(curl -s -X POST https://prove2.me/api/v1/agent/refresh \
  -H "Content-Type: application/json" \
  -d "{\"api_key\": \"$PROVE2ME_API_KEY\"}" | jq -r .access_token)
curl -s "https://prove2.me/api/v1/theorems?q=KEYWORD" -H "Authorization: Bearer $TOK"
curl -s "https://prove2.me/api/v1/theorems/THEOREM_ID/submissions?status=ACCEPTED,SKETCH_ACCEPTED" -H "Authorization: Bearer $TOK"
curl -s "https://prove2.me/api/v1/submissions/SUBMISSION_ID/solution" -H "Authorization: Bearer $TOK"
```

The last call returns the exact `solution.lean` of any submission, accepted or failed. `GET /theorems/:id/graph` returns a mission's full decomposition tree. `GET /theorems/:id/decompositions` returns recorded reductions, which give proof plans as well as code.

The API key is valid 30 days. The access token is valid one hour.

Each theorem belongs to a platform environment that pins its own Mathlib commit. Check that commit against the local pin before direct reuse.

The full skill document is at https://prove2.me/skill.md.

### anthropics/fermats-last-theorem, and other whole-proof agent corpora

The repository holds a complete machine-checked proof of Fermat's Last Theorem: 29,511 theorems and 1,450 definition modules, all kernel-checked on the three standard axioms. It uses Lean 4.33.1 and Mathlib `v4.33.0`. The local project pins the same Mathlib tag on Lean 4.33.0, so its statements and proofs read directly against the local Mathlib.

The layout is the Prove2Me workspace layout: flat `Theorems/Thm_*.lean` and `Definitions/Def_*.lean`, plus a `P2M/` solution tree. File names carry the Mathlib namespace and the statement shape, so `rg` over the file list finds a target fast.

The mathematical range is much wider than the title: absolute values and completions, adic completions, algebraic curves and divisors, Galois actions, Hecke operators, patching and descent, torsion in abelian groups, and the homological and category-theoretic machinery under them.

`PROOF-PATH.md` maps each classical step to the Lean theorem that carries it. The `html/` directory (about 390 MB) gives a per-theorem browser with dependency graphs; use it for decomposition plans without a clone.

Treat this as the first entry of a class: whole-proof corpora produced by agent pipelines and published as a frozen artifact. They are large, unmaintained, and uneven in naming. Use them as statement and decomposition references. Check the exact declaration before reuse, as with atlas-lean.

## Current findings

The external source landscape already covers large classes of prerequisites.

The project must not treat all missing local vocabulary as missing Lean mathematics.

The main process is source routing:

- use current Mathlib when it already owns the construction
- use external implementations as theorem and proof references
- port or adapt only the parts that remain absent locally and in Mathlib

No inspected source yet gives a complete general formed-lattice classification layer.

This conclusion is limited to the sources and commits listed above.

## Coverage status

The scheme repositories received complete file-tree and declaration-family inspection.

FLT received complete domain inspection. Its deformation and number-field declarations received detailed inspection.

Sphere-Packing-Lean received complete domain inspection and detailed E8 inspection.

Riemann-Roch received complete domain and public-result inspection.

LeanFibredCategories received complete file-level inspection.

Lean-liquid, Atlas, and formal-conjectures received class-level inspection.

Their thousands of declarations did not receive individual review.

## Freshness check (2026-09-05)

The repository pins Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` (`v4.33.0`) on Lean 4.33.0, matching this atlas. The earlier pin was `81a5d257c8e410db227a6665ed08f64fea08e997` on Lean 4.32.0.

External entries are commit-bounded snapshots. This audit did not refresh them. Their claims remain limited to the listed commits and coverage.
