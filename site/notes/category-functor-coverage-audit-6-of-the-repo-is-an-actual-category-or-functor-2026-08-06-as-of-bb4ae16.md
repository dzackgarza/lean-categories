---
title: "Category/functor coverage audit: ~6% of the repo is an actual category or functor (2026-08-06, as of bb4ae16)"
---

This audit read every file. Five parallel subagents did the work. There was no sampling and no grep-only proxy. It covered every `.lean` file under `CategoryGraph/` and `LeanCategories/` at commit `bb4ae16`, dated 2026-08-06.

It classified every top-level declaration into three classes.

- CATEGORY: a real `instance : Category X`, or the object-type of one.
- FUNCTOR: a real `C ⥤ D` term, or its obj/map/map_id/map_comp bundle.
- NEITHER: with a note on what it actually is. That is, a predicate, a data record, an unbuilt morphism structure, an axiom, a theorem, or tooling.

## Totals

| Subtree                                          | Declarations | CATEGORY | FUNCTOR | NEITHER  |
| ------------------------------------------------ | ------------ | -------- | ------- | -------- |
| `LeanCategories/Modules/`                        | 38           | 4        | 3       | 31       |
| `LeanCategories/Stacks,ComplexManifolds,Groups/` | 34           | 0        | 0       | 34       |
| `LeanCategories/Schemes/`                        | 35           | 0        | 2       | 33       |
| `LeanCategories/Lattices,Fans,Meta/` + root      | 148          | 4        | 5       | 139      |
| `CategoryGraph/`                                 | ~410         | 12       | 10      | ~388     |
| **Total**                                        | **~665**     | **~20**  | **~20** | **~625** |

About 6% of all declarations in the repository are a real category or functor.

Some struct and instance pairs are counted twice above. Collapse them and these are the hand-built categories:

- from LeanCategories: `SymmBilinModuleCat`, `ZLat`, `EvenLattice`, `FiniteQuadraticModule`;
- from CategoryGraph, hand-built: `ClassifiedCategory`, `UnitalMagma`, `UnitalMagmaWithInv`, `AdditiveMagma`, `MultiplicativeMagma`, `Crystal`;
- six `ObjectProperty.FullSubcategory` abbreviations inherited from Mathlib: `CommMagmaCat`, `FreeModuleCat`, `FinitelyGeneratedModuleCat`, `FiniteRankModuleCat`, `DistributiveTwoOpCat`, `DivisionTwoOpCat`.

That is about 10 distinct hand-authored categories in the whole repository.

The functors are `discriminantFunctor`, `forgetForm`, `rationalizationFunctor` and `realificationFunctor` from LeanCategories, plus `projection`, three pullback-pasting functors in `ForMathlib/CategoricalPullback.lean`, four forgetful functors in `Realization/Mathlib/Algebra.lean`, `magmaForget` and `Crystal.forgetFunctor` from CategoryGraph. That is about 14 distinct functors.

## The NEITHER 94% is not one verdict. It splits into different buckets.

**CategoryGraph's DSL, registry and tooling apparatus is a different kind of content by design. It is not a gap.** This is about 388 declarations. It covers the symbolic `CategoryExpr` and `FunctorExpr` AST, the normalizer, and the structural-projection algorithm, in `Core/Expr.lean`, `Core/Normalize.lean`, `Core/StructuralMap.lean` and `Model/Interpretation.lean`. It covers the `Classifier`, `ClassifiedCategory` and reindexing framework, in `Core/Classifier.lean`, `Core/CategoricalPullback.lean`, the non-category parts of `Core/AxiomOpfibration.lean`, and the coherence witnesses in `ForMathlib/CategoricalPullback.lean`. It covers stable-ID and registry plumbing: `Core/Ids.lean` has 65 declarations on its own, and `Registry/Entry.lean` and `Registry/Extension.lean` add 47 more. It covers JSON export in `Tools/ExportJson.lean` and similar files, the linters, and a specimen and integration-test layer in `Specimen/*` of about 78 declarations.

This is the meta-machinery that makes the DSL-registry goal reachable. It is not filler. But this pass did not check its proportion against the near-term DSL-consumption scope of issue `#56`. That question is open, not settled.

**One gap is systemic, with no exceptions: morphism-shaped structures with no `Category` instance.** Four whole LeanCategories subtrees have this problem: `Schemes/`, `Stacks/`, `ComplexManifolds/` and `Groups/Reflection/`. Between them, 69 declarations across about 38 files have zero `instance : Category` declarations. Two methods confirm this: the per-declaration read, and a repository-wide cross-check with `grep -rn '⥤\|Category\|instance '`, which found zero matches.

Two files are named `*Functor.lean` and contain no Mathlib functor: `ComplexManifolds/Functors/PeriodMapFunctor.lean` and `Groups/Reflection/Functors/FoldingFunctor.lean`. The second has no functor-shaped construct at all. Its `Folding` is a plain data record.

`Stacks/Morphisms/DeformationGroupoid.lean` is the closest near-miss. It is a record with `isomorphism`, `identities` and `composition` fields. They are shaped like Hom, id and comp. It proves no category laws. It is never attached as an `instance`.

`Lattices/` and `Fans/` show the same pattern for most of their content. They also hold the small set of real categories that do exist.

**A second bucket is more clear-cut: declarations that mislead, whatever the value of the underlying concept.**

- `Divisor/Functors/PositivityFunctor.lean` declares `PositivityFunctor`. It is a plain value-level `def`. It is not a functor.
- `Quadratic/Functors/DiscriminantFunctor.lean` is a bare `Type`-valued alias. It is not a functor either.
- `Surface/Enriques.lean` declares `EnriquesPeriodLatticeType`. Its own docstring admits it is a rank-4 placeholder. It stands in for the real rank-26 lattice.
- `Fans/Unbundled.lean` declares `generalizedCoxeterFan`. Its own docstring admits the implementation is broken. It returns one cone and claims an orbit union.

These four cost something as they stand. Future need and sequencing do not change that. They are the same failure class as the vacuous Nikulin theorem. See the `axiomatized-what-the-layer...` trap and its 2026-08-06 continuation. Here the failure takes `def` and type-alias form instead of `theorem` form. The `bb4ae16` cleanup pass touched none of the four. They are live.

**Predicates and small data records are legitimate. This audit did not touch them.** See the separate `properties-should-be-subcategories-not-bare-predicates` trap for the real gap in this bucket. The question is not "should these exist". The question is that nothing wraps them into the subcategory idiom that Mathlib provides, and that this repository already uses three times elsewhere.

## Scope and limits of this audit

This audit was read-only. It fixed, removed and renamed nothing. That was a separate, earlier, partly-finished pass. See `bb4ae16` and the axiom-cleanup trap above.

The job here was one question only: how much of the repository is actually a category or a functor. It was not to re-triage every NEITHER item.

At `bb4ae16`, two questions stayed open: the separate `CategoryGraph` tree's proportion, and the 69 geometry declarations without category instances.

## Later disposition (2026-08-11)

Commit `59b7813` merged valid support roles into `LeanCategories`. Commit `f73ec81` removed the premature geometry sketches. Current source now contains many real `FullSubcategory` constructions and functors.

The approximately 6 percent figure applies only to `bb4ae16`. It has not been recalculated for current `main`.
