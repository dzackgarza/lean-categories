# Current work

This repository first completes the mathematical language required by GitHub issue
[#1](https://github.com/dzackgarza/lean-categories/issues/1). The requirement is
definitional. Hard classification, automorphic, and projectivity theorems do not control
the foundation queue.

GitHub issues own public requirements and execution state. The central agent-memory vault
owns private plans and prerequisite analysis. This file is a short entry point, not a
second tracker.

## Missing or incomplete definition layer

This is the declaration-level work queue. Each item states the current gap verbatim,
then states the mathematical result required to close it.

- **No general categories of projective, torsion, or torsion-free `R`-modules exist.**
  - Define each category as the appropriate full subcategory of `ModuleCat R`.
  - Define its inclusion into `ModuleCat R` and its change-of-scalars functors where
    the property is preserved.
  - Relate these categories to `FreeModules R`, `FinitelyGeneratedModules R`, and
    `FiniteRankModules R`.
  - Express projective lattices and finite torsion form modules through these module
    categories instead of repeating carrier predicates.

- **`RingAdeleRing K` is tied to `\mathcal O_K`. It is not the requested `AA_R` for a
  general number ring `R`.**
  - Define the ring adeles relative to an arithmetic base `(R, K)`.
  - Use the finite integral adeles of `R`, the archimedean completions of `K`, and the
    diagonal `R`-algebra map.
  - Recover the existing `RingAdeleRing K` when `R = \mathcal O_K`.
  - State the comparison with the full adele ring of `K`.

- **No class-number definition exists, despite the finite genus class set.**
  - Define the class number as the cardinality of the finite set of global isometry
    classes in a genus.
  - Prove invariance under replacement of the base lattice by a lattice in the same
    genus.
  - Relate class number one to uniqueness of the global isometry class in the genus.

- **`O(L)` is not defined as `Aut L` in the formed-module category.**
  - Make the categorical automorphism group the canonical definition of `O(L)`.
  - Prove its group equivalence with the existing subgroup of form-preserving linear
    equivalences.
  - Transport the actions on sublattices, duals, and discriminant forms through this
    equivalence.
  - Remove the duplicate orthogonal-group authority after dependent code uses the
    categorical definition.

- **No equivalence between the current `O(L)` and that categorical automorphism group
  exists.**
  - Construct the equivalence from formed-module morphisms and form-preserving linear
    equivalences.
  - Prove both composites are identities.
  - Prove compatibility with multiplication, inverse, and the action on the lattice.

- **No finite-generation theorem for `O(L)` exists.**
  - For positive-definite integral lattices, derive finite generation from finiteness of
    `O(L)`.
  - State the arithmetic hypotheses required for indefinite lattices over number rings.
  - Formalize a sourced finite-generation theorem only at that natural generality.
  - Keep finite generation separate from generation by reflections.

- **No Siegel mass formula exists. Only the mass itself exists.**
  - State the global mass formula for a positive-definite genus.
  - Define every archimedean factor, local density, measure normalization, and volume
    term used by the formula.
  - Compare the formula's mass with the existing finite sum over genus classes.
  - Prove the comparison after all normalization conventions agree.

- **No theta modularity theorem exists.**
  - Define the analytic theta function attached to a positive-definite integral
    lattice.
  - Compare its Fourier expansion with the existing formal power series.
  - State the exact evenness, level, character, weight, and congruence-subgroup
    hypotheses.
  - Prove the required transformation laws before claiming modularity.

- **No signed-discriminant definition exists.**
  - Define the signed discriminant from rank and Gram determinant with one explicit
    sign convention.
  - Prove independence from the chosen basis.
  - Prove compatibility with isometry, orthogonal sum, scalar extension, and the
    discriminant module.
  - Relate it to the existing determinant and signature invariants.

- **No named `\mathbb Q/\mathbb Z` module exists. Only the general fraction-field
  quotient machinery exists.**
  - Define `Frac(R) / R` as the standard value module for a domain `R`.
  - Define `\mathbb Q/\mathbb Z` as its specialization at `R = \mathbb Z`.
  - Register both objects in the module family and formed-module value families.
  - Compare them with the existing fractional-ideal quotient at the unit ideal.

- **No quadratic-form interpretation through a divided-power algebra exists.**
  - Define or reuse the degree-two divided-power object `\Gamma^2_R(M)`.
  - State quadratic maps `M \to N` as linear morphisms `\Gamma^2_R(M) \to N`.
  - Prove the universal correspondence and its naturality in `M` and `N`.
  - Compare this representation with the current `QuadraticMap` category.

- **No repository-level category of `R`-algebras exists.**
  - Expose Mathlib's `AlgCat R` as the category of `R`-algebras.
  - Define the family of algebra categories over commutative rings.
  - Register restriction and extension of scalars, underlying rings, and underlying
    modules.
  - Record the relevant adjunctions and comparison isomorphisms.

- **Tensor, symmetric, exterior, polynomial, power-series, Laurent-series, and graded
  algebras are not exposed as the required categorical constructions.**
  - Reuse the Mathlib constructions and expose their functors at the correct source and
    target categories.
  - Record the tensor, symmetric, exterior, and polynomial universal properties.
  - Define power-series and Laurent-series rings as `R`-algebras with their coefficient
    and substitution morphisms.
  - Expose graded algebras and the gradings carried by the free algebra constructions.
  - Register all structural and forgetful functors without creating parallel algebra
    definitions.

- **Chain complexes of `R`-modules are not exposed through the project language.**
  - Expose chain and cochain complexes in `ModuleCat R`.
  - Register evaluation, shift, homology, forgetful, and scalar-change functors where
    Mathlib supplies them.
  - State the differential and square-zero condition through the standard Mathlib
    category.
  - Keep complexes distinct from graded modules with a chosen differential.

- **Mathlib owns many underlying constructions. The repository does not integrate their
  categories, functors, and universal properties.**
  - Build a declaration-level reuse inventory for every item above.
  - Import the Mathlib owner when its formulation has the required generality.
  - Add only the missing categorical family, classifier, realization, or comparison.
  - Record the universal property that identifies each exposed construction.

- **Localization, completion, local rings, and residue fields occur in specialized
  files.**
  - Expose localization of rings and modules at submonoids and prime ideals.
  - Expose adic completion with its canonical map and universal property.
  - Expose local rings, maximal ideals, residue fields, and induced local morphisms.
  - Relate the existing lattice-localization, completion, and residue constructions to
    these general owners.

- **The general local algebra needed for schemes is not present as a coherent definition
  layer.**
  - Complete the ring, algebra, module, localization, completion, and residue-field
    categories before the scheme layer depends on them.
  - Define the functors and natural transformations used by stalks and affine-local
    constructions.
  - State all base-change and comparison isomorphisms needed to pass between global,
    localized, completed, and residue objects.
  - Require the scheme foundation to reuse this layer rather than introduce local
    algebra inside geometric files.

## Foundation 0.1

GitHub issue [#50](https://github.com/dzackgarza/lean-categories/issues/50) owns the
ordered Foundation 0.1 work. The active vault plan is
`PLAN-DEFINITION-FIRST-FOUNDATION-EXECUTION`.

1. [#30 Higher classifier foundation and algebraic testbed](https://github.com/dzackgarza/lean-categories/issues/30)
   - Select the model-independent higher-categorical interface.
   - Make the current strict `Cat` code a realization of that interface.
   - Derive property, structure, and stuff from classifying fibers and truncation.
   - Prove reindexing universal properties and coherent comparison cells.

2. [#31 Proof-carrying expressions, registry, and generic interpretation](https://github.com/dzackgarza/lean-categories/issues/31)
   - Make expressions and interpretation relative to a selected realization.
   - Replace unconditional partial normalization with certified convergence boundaries.
   - Record actual equivalences and coherent comparisons between presentations.

3. [#28 Operation and section registry](https://github.com/dzackgarza/lean-categories/issues/28)
   and [#53 functorial method resolution](https://github.com/dzackgarza/lean-categories/issues/53)
   - Register mathematical operations, constructors, sections, and invariants on the one
     semantic diagram.
   - Derive inherited methods by composition along structural functors.
   - Keep backend realizations separate from mathematical ownership.

4. [#41 Standard categorical vocabulary](https://github.com/dzackgarza/lean-categories/issues/41)
   - Expose adjunctions, universal arrows, essential images, restrictions,
     corestrictions, mates, and reflective localizations through existing Mathlib owners.
   - Register the standard free-algebra constructions and their universal properties.

5. [#29 Coordinatized finite symmetric bilinear space over F2](https://github.com/dzackgarza/lean-categories/issues/29)
   - Exercise category definitions, structural projection, operation resolution, and
     computation in one end-to-end example.
   - Keep intrinsic invariants distinct from coordinate-dependent calculations.

6. [#33 Module-valued forms and intrinsic lattices](https://github.com/dzackgarza/lean-categories/issues/33)
   - Complete arbitrary-index frames, the matrix presentation category, and the Gram
     comparison functor at their general mathematical owners.

## Definition work after Foundation 0.1

The issue tree remains authoritative for later branches:

- [#38 Scheme and relative-geometry foundation](https://github.com/dzackgarza/lean-categories/issues/38)
- [#39 Fibred categories, stacks, and KSBA moduli](https://github.com/dzackgarza/lean-categories/issues/39)
- [#40 Manifolds, Hodge theory, and period constructions](https://github.com/dzackgarza/lean-categories/issues/40)
- [#54 Typed category constructors and parameterized family applications](https://github.com/dzackgarza/lean-categories/issues/54)
- [#56 Complete category surface required by the CAS DSL](https://github.com/dzackgarza/lean-categories/issues/56)

## Downstream theorem programmes

The former TODO items remain preserved as vault plans. They are not current foundation
work:

- `PLAN-SIEGEL-MASS-FORMULA`
- `PLAN-THETA-SERIES-MODULARITY`
- `PLAN-ADE-REALIZATION-UNIQUENESS`
- `PLAN-INDEFINITE-LATTICE-CLASSIFICATION`
- `PLAN-ABELIAN-PROJECTIVITY`

Promote one of these plans only after its definition layer exists and the project selects
that theorem programme for active work.
