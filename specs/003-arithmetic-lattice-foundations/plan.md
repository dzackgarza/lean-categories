# Implementation Plan: Arithmetic lattice foundations at their natural generality

**Branch**: `003-arithmetic-lattice-foundations` (work lands on `main`) | **Date**: 2026-11-25 | **Spec**: [spec.md](spec.md)
**Input**: Feature specification from `specs/003-arithmetic-lattice-foundations/spec.md`

Revision of record: `533e9259`; rows N28–N32 and decisions D26–D31 at `a3a66fba`. Decisions D1–D31
are in [research.md](research.md); the owner table N01–N32 in [data-model.md](data-model.md); the validation runs in [quickstart.md](quickstart.md).

## Summary

The feature completes the arithmetic theory of formed modules and lattices over a Dedekind domain
and over an arithmetic base: one owner for each notion of the owner table, and a proved comparison
for each specialization. Much of the theory is in the source at `533e9259` (fractional-ideal duals,
determinant lines and Steinitz classes, Fitting ideals, equivariant lattices, elementary and dyadic
notions, ring adeles and the adelic genus for number rings, the canonical spinor norm, Jordan
existence for 2 invertible, definite and indefinite loci, theta series and local densities). The
remaining work, in task order: the separation and perfection vocabulary and the presentation
comparisons; the discriminant refinements and determinant comparisons; gluing and equivariant
comparisons; places, completions and adeles over an arithmetic base; the genus theorems; the
canonical Hasse invariant and spinor theory; the dyadic classification; signatures, reflections,
named lattices, the analytic realization and the Hodge categories; the public surface; then the
four theorem programmes.

## Technical Context

**Language/Version**: Lean 4, toolchain of `lean-toolchain`
**Primary Dependencies**: Mathlib (locked in `lake-manifest.json`); reference ports of research D24
**Storage**: Lean source under `LeanCategories/` (lattice owners mainly under `Lattices/Valued/` and
`Modules/{Bilinear,Quadratic}/Valued/`)
**Testing**: tier-1 elaboration of each changed module and of the test modules of the changed
owner; `just test` at the end of each phase; CI `just test-ci`
**Target Platform**: Linux, research image `ghcr.io/dzackgarza/sage:develop` (constitution E5)
**Project Type**: Lean library (formal mathematics)
**Performance Goals**: tier-1 loop of each change under 300 s (constitution E1, E4)
**Constraints**: one Lean process under `flock .tmp/lean.lock` (E10); no `sorry`, no project axiom
(M3); source statements read from the live library (002 research D16)
**Scale/Scope**: 32 owner rows; 9 foundation phases and 4 theorem programmes

## Constitution Check

| Article | Check for this feature | Status |
| --- | --- | --- |
| M1 | All mathematics is declared here, from the cited sources | pass |
| M2 | Each statement is read from its source; no easier statement replaces a requested one | Contract O; D21 |
| M3 | No `sorry`, no project axiom | Contract O; phase gates |
| M4 | One owner per notion at its generating category; specializations by comparison | data-model.md; Contract O |
| M5 | Total operations; no division by 2 without invertibility | FR-006; D8 |
| M6 | Chosen structures (bases, frames, diagonalizations, homomorphisms) are data, never owners of invariants | FR-017, FR-018; D13, D14 |
| M7 | Registry rows of lattice loci are feature 001's; no duplicate row | D16 |
| M8 | Search before authoring; reference ports with provenance | Contract O; D24 |
| M9 | A consumer does the owning task of this feature at once; other requests are 002 Phase 2 tasks | D2 |
| M10 | FOUNDATIONS content changes go to the mathematician | D6 |
| M11 | Executed as 002 T107, in document order | D2 |
| M12 | Missing theorems and workarounds recorded under LC-05, LC-11, LC-12 | FR-031 |
| M13 | No artifact certifies itself; review is independent | Contract O review step |
| E1, E4 | Tier 1 per change; `just test` per phase | Checks |
| E2 | Mathematical assertions at the owners: positive and separating examples | Contract O |
| E5 | One platform: Linux and the research image | Technical Context |
| E3 | No policy change in this feature | none |
| E6, E7 | Durable logs and timing records | feature 001 T002, T003 |
| E8 | No optimization in this feature without a triage table | none |
| E9 | Construction of a lattice object close to instant | Contract O |
| E10 | One Lean process; forward history | Checks |

Gate result: pass. No violation is justified in Complexity Tracking.

## Checks of this repository

The tiers, commands and preconditions are those of feature 002
([plan.md](../002-foundational-corpus-sweeps/plan.md#checks-of-this-repository)): tier 1 is
`just loop <modules>` for each changed module and each changed test module, the recipe of
feature 001 T001, which comes first and builds the imports of each module before it elaborates
the module; the full gate is
`just test`.

## Current source state

The subtraction of the vault plan from the source at `533e9259`. Evidence is the named file.

| Plan item | In the source | Remaining |
| --- | --- | --- |
| metric $I$-duality, $I$-modularity | `IdealDual.lean`: fractional ideals, `IsFractionalIModular`, `FractionalIModularLatticeCat`; `idealDual` as integral case | comparisons with `metricDual`; $K/I$ and $K/2I$ forms on $A_L^I$ |
| determinant line, Steinitz, discriminant ideal | `DeterminantLine.lean` (Steinitz class as Picard class), `FittingIdeal.lean` | $\operatorname{Cl} \cong \operatorname{Pic}$; invertibility of $\bigwedge^n P$; classification; Gram recovery |
| equivariant lattices | `Equivariant.lean` (invariants, coinvariants, centralizer, normalizer) | $G \to O(L)$ equivalence; discriminant action; equivariant scalar change; $C_2$ comparison with `Involution.lean` |
| elementary and dyadic | `Elementary.lean`, `Dyadic.lean` | none at the owner; dyadic classification in N18 |
| ring adeles, adelic genus | number rings: `IntegralAdeleRing.lean`, `Adele.lean`, `AdelicClass.lean`, `IdeleGroup.lean`; $\mathbb Z$ comparison `LocalGlobal.lean` | arithmetic base; placewise theorem in general; double-coset classification; nonfree stabilizer |
| Hasse invariant | `Hasse.lean` (Hilbert symbol), `HasseInvariance.lean` (diagonal value invariant) | invariant on the isometry class; orthogonal sums; scalar change |
| spinor theory | `CanonicalSpinorNorm.lean`, `SpinorGenusAdelic.lean`, `AdelicSpinorNorm.lean`; `Spinor.lean` chosen norm | owner change; exact sequences; spinor-genus relation laws |
| Jordan, Witt, dyadic classification | `JordanRecursion.lean` (2 invertible), `Witt.lean`, `DyadicSquares.lean` | uniqueness data; dyadic layer |
| signatures and loci | `Signature.lean` ($\mathbb Z$), `DefiniteIndefinite.lean` | real places of an arithmetic base; totally definite, Lorentzian |
| analytic comparison, complex tori | `Topological.lean`, `ComplexStructure.lean`, `ComplexTorus.lean` | covolume relation; Hodge categories; period domains |
| class sets, mass, densities | `Mass.lean` (explicit family), `ClassFiniteness.lean` (Hermite bound), `LocalDensity.lean`, `DensityProduct.lean` | genus finiteness; mass of a genus; Siegel formula |
| theta series | `Theta.lean` | Mathlib analytic comparison; modularity |
| named lattices | `Standard.lean`, `RootLattice.lean`, `ADERealization.lean`; $E_8$ comparison `LeanCategoriesSpherePacking/E8/Comparison.lean` | generic-construction derivations of invariants; realization independence |
| presentations | `CoordLatticeCat`, `TruncatedResolutions.lean` | $\mathbf{SymMat}_n$, $\operatorname{Gram}_n$ and their equivalence; arbitrary-index coordinate lattices; framed lattice pullbacks |

## Phases and order

| Phase of tasks.md | Content | Owner rows | Gate to leave |
| --- | --- | --- | --- |
| 1 | projective formed arithmetic | N01–N09, N28–N31 | every comparison of the rows proved; `just test` |
| 2 | equivariant arithmetic | N10, N11 | same |
| 3 | places and completions | N12, N13 | same |
| 4 | canonical local invariants | N16, N17, N32 (subgroup tower) | same |
| 5 | ring and field adeles | N14 | same |
| 6 | genus | N15 | same |
| 7 | local classification | N18 | same |
| 8 | signatures, reflections, named lattices, analytic and Hodge realization, surface | N19–N23 | same |
| 9 | definite theory | N24, N25 | same |
| 10–13 | theorem programmes: ADE, indefinite with Nikulin theory, Siegel, theta modularity | N20, N21, N24–N27, N32 | each programme's success criteria |

Phase order follows the vault dependency spine (formed and projective semantics; duality; completions
and equivariance; adeles; genus; Hasse and spinor; classification; consumers). Phases 2 and 4 need only
Phase 1, and Phase 3 needs Phase 1 and T010; inside a phase, a task follows only the tasks whose results it uses (constitution M11).

## Unit contract

**Contract O (owner and comparisons).** Read the row of data-model.md and the source at the task
revision; record which comparisons are present (by declaration) and which are not. For each missing
owner or comparison:

1. Read the defining statement from its source in the library (002 research D16) and record, in
   the commit, the item key, the locator and the source record of mathematical-simplicity.md,
   "Source the definition before proving its theorems" (authority, exact definition, defining data
   and axioms, ambient category, morphisms, hypotheses, later results, Lean representation,
   comparison with existing formalizations).
2. Search under constitution M8 (Mathlib, the formalization corpus, the references of D24); record
   the queries in the commit or the owning COMPLAINTS.md entry.
3. Write the owner at its generating category (M4), with only the hypotheses the construction uses;
   take the object in the category that carries its structure (LC-13); no division by 2 without an
   invertibility hypothesis (D8).
4. Prove each comparison theorem with its exact hypotheses. A specialization keeps its old name
   only when a comparison theorem identifies it with the owner; otherwise it is renamed to state its
   restricted meaning or removed from the root surface (D23).
5. Add one positive example and one separating example at the owner, and apply the wrong-model,
   target-exclusion, theorem-survival and unfolding tests of mathematical-simplicity.md to each new
   theorem; a theorem that only unfolds its definitions is named as an interface lemma.
6. Update the "Lean realization status" paragraph of FOUNDATIONS that the work changes (D6). When a
   declaration realizes a corpus unit, add the unit's mapping row with `[realized]` and regenerate
   the definition index and the frontier in the same commit (constitution M11; 002 Contract D).
7. Check: tier 1 on the changed modules; the row's comparisons named in the commit; the axiom
   audit admits only the standard axioms at the phase gate.
8. Review: a reviewer who did not write the change compares the statements with the sources
   (002 plan.md Contract R).

## Project Structure

### Documentation (this feature)

```text
specs/003-arithmetic-lattice-foundations/
├── spec.md              # requirements, user stories, success criteria
├── plan.md              # this file
├── research.md          # decisions D1–D31 with their sources
├── data-model.md        # owner table N01–N32
├── quickstart.md        # validation runs
├── checklists/
│   └── requirements.md  # spec quality checklist
└── tasks.md             # the work order
```

### Source Code (repository root)

```text
LeanCategories/Modules/Bilinear/Valued/   # formed modules, radicals, separation
LeanCategories/Modules/Quadratic/Valued/  # quadratic modules
LeanCategories/Lattices/Valued/           # lattice owners of N03–N27
LeanCategories/ForMathlib/                # upstream candidates
```

**Structure Decision**: no new directory. Each owner goes where data-model.md names it, or to the
owner that M4 selects.

## Complexity Tracking

No constitution violation needs justification.
