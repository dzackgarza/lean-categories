# Repository reorganization

This file owns the remaining architecture work from the accepted reorganization plan.

## Completion conditions

- [x] Put the ordinary-category foundation under `CategoryTheory/OneCat`.
- [x] Put catalogue syntax, normalization, registry, and presentation code under `Catalogue`.
- [x] Keep `LeanCategories.lean` limited to the ordinary-category foundation.
- [x] Keep broad domain imports in `LeanCategories.All`.
- [x] Replace the valued-lattice umbrella import with direct foundation imports.
- [x] Generalize family parameters, operations, kinds, and variance identifiers.
- [x] Move the Sphere Packing comparison into a separate Lake package.
- [x] Keep only generic identifier types in `Catalogue/Id.lean`.
- [x] Put concrete identifiers and registrations beside their mathematical owners.
- [x] Replace `AtomicModel` and its central dispatchers with typed realization entries.
- [x] Let a domain register category, classifier, family, and functor semantics locally.
- [x] Make algebra paths own mathematical categories, not only catalogue expressions.
- [x] Remove `aiReviewCiLean` from the main package and use the global QC owner.
- [x] Build the main root, the broad root, the catalogue tools, and each optional package.

## Invariants

- Mathematics does not import catalogue code.
- General foundations do not import domain umbrellas.
- Domain modules extend semantics without changes to a central structure or evaluator.
- Optional integrations do not enter the main package dependency closure.
- `LeanCategories.All` remains the explicit broad import.
- Existing module and lattice category constructions keep their mathematical definitions.

## Proof commands

Run focused builds while editing. The commit hook runs the full repository checks.

```text
just build
lake build LeanCategories.Tools.ExportFull LeanCategories.All
cd Integration/SpherePacking && lake build
```
