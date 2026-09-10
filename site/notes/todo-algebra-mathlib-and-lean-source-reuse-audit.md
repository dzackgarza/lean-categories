---
title: "TODO-ALGEBRA Mathlib and Lean source reuse audit"
---

This is an ownership audit, not a current remaining-work list. Many project-owned layers were implemented later. GitHub issues and source own current execution state.

The project-owned boundary at audit time was smaller:

- Project-specific formed categories.
- Arithmetic predicates for integral forms.
- Discriminant modules and forms.
- Primitive embedding and gluing theory.
- Local classification and genus theory.
- Comparison functors between existing constructions.

**Current disposition (2026-08-11).** Commit `fb312de` adds the even-lattice full subcategory. Commit `6d42343` adds fixed-rank frame categories and the comparison from coordinatized lattices to intrinsic lattices. Arbitrary-index frames, matrix realization, and other named comparisons remain separate work.

## Remove as independent work

| TODO section                 | Existing source                                                                                           | Conclusion                                         |
| ---------------------------- | --------------------------------------------------------------------------------------------------------- | -------------------------------------------------- |
| Basic rings and algebras     | Mathlib `RingTheory`, `Ideal`, `Localization`, `IntegralClosure`, `DedekindDomain`, and `FractionalIdeal` | Do not rebuild this layer.                         |
| Basic module theory          | Mathlib `Module`, `Submodule`, tensor products, exactness, bases, rank, and matrices                      | Do not rebuild this layer.                         |
| Torsion submodules           | `torsionOf`, `torsionBy`, `torsionBySet`, and `Module.IsTorsion`                                          | Do not define new torsion machinery.               |
| Primary decomposition        | `Ideal.primaryComponent`, `iSup_primaryComponent_eq_top`, and `iSupIndep_primaryComponent`                | Remove primary decomposition as new work.          |
| Smith normal form            | `Module.Basis.SmithNormalForm` and `Submodule.smithNormalForm`                                            | Do not implement Smith normal form.                |
| Module scalar restriction    | `ModuleCat.restrictScalars`                                                                               | Direct reuse.                                      |
| Module scalar extension      | `ModuleCat.extendScalars`                                                                                 | Direct reuse.                                      |
| Scalar adjunction            | `ModuleCat.extendRestrictScalarsAdj`                                                                      | Direct reuse.                                      |
| Scalar coherence             | `extendScalarsId` and `extendScalarsComp`                                                                 | Direct reuse.                                      |
| Module-valued bilinear maps  | `LinearMap.BilinMap R M W`                                                                                | This is already the required object.               |
| Module-valued quadratic maps | `QuadraticMap R M W`                                                                                      | This is already the required object.               |
| Form base change             | `BilinMap.baseChange` and quadratic tensor-product machinery                                              | Do not write another base-change operation.        |
| Form properties              | Symmetry, alternation, radicals, nondegeneracy, and orthogonality                                         | Reuse Mathlib predicates.                          |
| Form morphisms               | Bilinear and quadratic isometries and isometry equivalences                                               | Reuse Mathlib structures.                          |
| Signatures                   | `QuadraticMap.sigPos` and `sigNeg`                                                                        | Do not create another signature definition.        |
| Metric dual lattice          | `BilinForm.dualSubmodule` and `dualSubmoduleToDual`                                                       | Reuse these definitions.                           |
| Root-system foundations      | Mathlib `LinearAlgebra/RootSystem`                                                                        | Do not rebuild roots, reflections, or Weyl groups. |
| Generic group actions        | Mathlib group actions, orbits, stabilizers, conjugacy, and automorphisms                                  | Do not rebuild general action theory.              |
| Local ring foundations       | Mathlib localizations, completions, DVRs, residue fields, and valuations                                  | Reuse these before local lattice work.             |

The main scalar-change declarations are in [ChangeOfRings.lean](home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:85).

Primary decomposition is in [PrimaryComponent.lean](home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean:50).

Smith normal form is in [PID.lean](home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean:408).

The metric dual is in [DualLattice.lean](home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/DualLattice.lean:37).

## Keep only as assembly or comparison work

These TODO items use existing foundations. They are not greenfield mathematical layers.

- **Finite torsion classification:** derive the required public theorem from Smith normal form and primary components.
- **Algebra scalar extension:** Mathlib has algebra tensor products and `AlgCat.restrictScalars`. A categorical extension adapter can remain.
- **Form scalar extension:** lift the existing module and form operations into the project categories.
- **The total formed category:** use Mathlib’s Grothendieck construction or category-of-elements machinery.
- **Perfect forms:** relate project predicates to `toDual` and `dualSubmoduleToDual`.
- **Orthogonal groups:** define them from existing isometry automorphisms. Do not create separate group theory.
- **Root actions:** connect project lattices to Mathlib root systems.
- **Concrete E8:** port or compare with Sphere-Packing-Lean. It already has `Submodule.E8`, `E8Lattice`, and `E8_ℤBasis`. [Sphere-Packing-Lean E8 source](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/Basic/E8.lean)

The Atlas textbook project mostly confirms Mathlib reuse here. Its bilinear-form and orthogonal-group files largely wrap existing declarations. It is a useful theorem index, not a replacement foundation. [Atlas bilinear forms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/AlgebraNotes/code/BilinearForms.lean), [Atlas orthogonal groups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/AlgebraNotes/code/OrthogonalGroup.lean)

## Work that still appears real

The following items remain project mathematics:

- The canonical variable-value formed category and its public interface.
- Scale and value ideals.
- Perfect and unimodular arithmetic forms.
- Saturated submodules and primitive embeddings.
- Discriminant modules, pairings, and quadratic forms.
- Exact sequences connecting algebraic, metric, and discriminant duals.
- Orthogonal sums at the formed-object level.
- Gluing and overlattice correspondence.
- Intrinsic orthogonal-group actions on discriminant data.
- Extension criteria for lattice isometries.
- Jordan decomposition of local lattices.
- Hasse invariants and local classification.
- Genus and spinor genus.
- Global classification and existence theorems.

## Search limits

**Result:** I found no ready Mathlib layer for scale ideals, value ideals, primitive embeddings, or discriminant torsion forms.

**Scope:** I searched the pinned Mathlib form, module, lattice, root-system, and arithmetic file families.

**Evidence:** Searches found the underlying maps, dual lattices, torsion modules, Smith normal form, and root systems.

**Confidence:** High for the pinned Mathlib revision. Medium for all external projects.

**Unchecked:** Atlas and formal-conjectures received class-level inspection. Their full declaration sets were not individually audited.

Thus, `TODO-ALGEBRA.md` should not describe sections 1–5 as missing foundations. They are mostly a reuse and integration inventory. The new theory starts near the arithmetic formed-lattice and discriminant layers.

## Disposition on current `main` (2026-08-11)

The reuse rulings remain current. The project now implements much of the project-owned layer under `Modules/*/Valued` and `Lattices/Valued`.

The deduplication pass uses `Grothendieck.ι`, `cancelBaseChange`, and `BilinForm.dualSubmodule`. It removed tautological lattice integrality and redundant K3 rank endpoints. `IsIntegralSubmodule` remains only as a thin lattice-specific predicate over Mathlib's relation.

Current `main` contains no `axiom`, `sorry`, or `admit` under `LeanCategories`. This does not prove the historical classification theorems. Current files often provide definitions, comparisons, predicates, and witness structures only. Issues #7 and #33 through #36 own public remaining work.

## Definition-catalogue stale-path disposition (2026-08-16)

A path-existence audit of the textbook definition catalogues against the pinned `.lake/packages/mathlib` tree flagged 56 `Mathlib/...lean` paths that no longer exist. All were resolved in the three catalogues (`dummit-and-foote`, `atiyah-and-macdonald`, `folland-real-analysis`):

- Most stale paths moved: Mathlib relocated or renamed files, or the canonical declaration lives in a different file than the catalogue cited. Each entry now carries the verified declaration name and `file.lean:line` against the pinned checkout. Declaration-name updates are marked inline (e.g. `Subgroup.IsNormal` → `Subgroup.Normal`, `IsTranscendental` → `Transcendental`, `MvPolynomial.Order` → `MonomialOrder`, `Homology` → `ShortComplex.homology`, `GroupCohomology` → `groupCohomology`, `TemperedDistribution.fourierTransformCLM` → non-deprecated `FourierTransform.fourierCLM`).
- Six textbook terms have no Mathlib declaration. Each catalogue entry now says so in place and names the closest declaration where one exists:
  - `conjugacyClass` (Dummit) — closest `IsConj` (`Mathlib/Algebra/Group/Conj.lean:32`).
  - `DirectProduct` (Dummit) — the product group is `G × H` with `Prod.instGroup` (`Mathlib/Algebra/Group/Prod.lean:123`).
  - `Subgroup.internalDirectProduct` (Dummit) — closest `Subgroup.prod` (`Mathlib/Algebra/Group/Subgroup/Basic.lean:91`).
  - `Matrix.Similar` (Dummit) — no matrix-similarity declaration (`Similar` in `Topology/MetricSpace/Similarity.lean:42` is metric similarity, a different concept).
  - `IsConstructible` (Dummit) — no declaration for constructible field elements.
  - `IsRadical` (Dummit) — closest `solvableByRad` (`Mathlib/FieldTheory/AbelRuffini.lean:196`).
  - `Scheme.O` (Dummit) — closest `structureSheafInType` (`Mathlib/AlgebraicGeometry/StructureSheaf.lean:171`).
  - `ModuleCat.Tor` (Dummit) — closest `CategoryTheory.Tor` (`Mathlib/CategoryTheory/Monoidal/Tor.lean:44`).
  - `DifferentialForm` (Folland) — no declaration for differential forms.
- `Submodule.sup` / `Submodule.inf` are operations of the `CompleteLattice` instance (`Mathlib/Algebra/Module/Submodule/Lattice.lean:197`), not standalone defs.
- `dvd` is `Dvd.dvd` in Lean core (`Init/Prelude.lean:1560`), not Mathlib.
- A re-scan of all `Mathlib/...lean` and `LeanCategories/...lean` paths in the three catalogues reports zero missing paths.

## Definition-catalogue scan follow-up (2026-08-16)

The remaining flagged classes from the same scan were re-checked with the correct resolution roots:

- `LeanCategories/...lean` flags (8 paths across atiyah, shafarevich, hartshorne, dummit) were false positives: every cited project file exists in the repo.
- `reservoir-sources/...lean` flags (6 citations across ahlfors, hatcher, whitehead) were false positives from checking the wrong root: the checkout lives in `lean-reference-corpus/reservoir-sources`, and every cited file exists there with the cited declaration (verified: `GeneralizedResidueTheory.meromorphicPrincipalPart` at `MeromorphicPrincipalPart.lean:87`; `Rado.exists_harmonic_extension` at `Rado/Complex/Poisson.lean:385`; `PeriodPair.weierstrassSigma`/`weierstrassZeta` at `Chudnovsky/SigmaZeta.lean:47/52`; `SeibergWitten.Physics.modularLambdaFn` at `SeibergWitten/Physics/ThetaLambda.lean:76`; `HasHomotopyExtensionProperty` at `WhiteheadTheorem/HEP/Cofibration.lean:26`).
- Two ahlfors entries cited the external `AlexKontorovich/PrimeNumberTheoremAnd` package in inconsistent formats. Both were re-verified against the live repo (`main`) and unified to `Owner/Repo:path:line`: `Complex.canonicalProduct` — `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CanonicalProduct.lean:33`; `Complex.Hadamard.EntireOfOrderAtMost` — `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/HadamardFactorization/Order.lean:78`. The package is not vendored in `reservoir-sources`, so the citation stays a GitHub path.
- Full re-scan of all 23 catalogue files against pinned mathlib, the repo, and the reservoir checkout: zero missing paths of any class.

## External-repository citation verification (2026-08-16)

The "permanent" class of the original scan (shafarevich 5, hartshorne 4) is external-repository citations kept by design. All 19 citations were re-verified against the live upstream repos on `main`:

- 17 `Atlas/...` paths in `facebookresearch/atlas-lean` (AlgebraicGeometryI and ArithmeticGeometry code trees) — all exist.
- 1 `TauCeti/AlgebraicGeometry/TangentSpace/Basic.lean` in `TauCetiProject/TauCeti` — exists.
- 2 `RiemannRoch/Divisor.lean` citations in hartshorne named only the repo short name; owner resolved to `vaca22/riemann-roch-function-fields` and both entries updated to the `Owner/Repo:path` form. Declarations verified: `IsDedekindDomain.Divisor` (abbrev, `:35`), `FractionalIdeal.principalDivisor` (def, `:112`).
