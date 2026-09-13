---
type: reference
title: Provenance contract for FC05 CA
description: '# Provenance contract for FC05 CA'
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC05 CA

# Provenance contract for FC05 CA

## Provenance contract for FC05 CA

- Project-first search was performed at repository HEAD `f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`. No project declaration owns a complete Appendix-A source row under strict bundle semantics.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every P target promoted in the Appendix table was inspected at that exact revision. The generic category/functor/natural-transformation, skeleton, limits/colimits, filtered-category and adjunction interfaces substantially overlap FC03 (Riehl); the already-recorded FC03 Sweep-II audits were reused, while Weibel-specific bundled examples and Appendix-only clauses were checked independently.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`, Apache-2.0, Lean 4.34.0-rc2. Targeted H searches did not add a general arbitrary subcategory interface matching U017, the abelian-monoid translation category U045, the full AB5 directed-subobject-lattice equivalence U037, or the noncommutative tensor-Hom adjunctions required by U014/U049.
- U014 and U049 are deliberately not inferred from the pinned closed monoidal `ModuleCat` API. `Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean::monoidalClosedHomEquiv` is formulated over a commutative base ring. Open Mathlib PR #8495, audited at head `5b358de183c6084a8378e2d6418ce48cf2d7fb68`, develops a Hom-tensor adjunction but likewise assumes `[CommRing R]`. Weibel's rows use the general right/left module tensor-Hom adjunction over an arbitrary ring, so neither checked interface owns the whole source bundle.
- U017 asks for an arbitrary subcategory obtained by selecting both objects and a composition-closed subset of ambient morphisms, with faithful inclusion. P/H have full-subcategory and wide-subcategory infrastructure, but no checked declaration realizes that whole general source construction; a full or wide specialization is not credited.
- U033 is direct at P even though Mathlib does not use the labels AB3/AB3*: the source conditions are arbitrary coproducts/products, and `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean::has_colimits_of_hasCoequalizers_and_coproducts` and `has_limits_of_hasEqualizers_and_products`, together with the automatic (co)equalizers of an abelian category, give the stated equivalence with cocompleteness/completeness.
- U035 is direct at P. `Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean::AB4` and `AB4Star` define exact coproducts/products, while `hasExactColimitsOfShape_of_preservesMono` and `hasExactLimitsOfShape_of_preservesEpi` supply the converse from preservation of monomorphisms/epimorphisms. Thus the source direct-sum-of-monos/product-of-epis formulation is represented at the pinned revision.
- U037 is bundled more strongly than Mathlib's AB5 definition. P has `AB5`/`AB5Star` as exact filtered colimits/cofiltered limits, and `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Subobject.lean::subobjectMk_of_isColimit_eq_iSup` relates filtered colimits of subobjects to suprema. The audit found no declaration giving Weibel's full distributivity equivalence `B ∩ (sup A_i) = sup (B ∩ A_i)` together with its dual. Therefore U037 remains unmatched rather than receiving partial credit.
- U034, U036 and U038 are heterogeneous example rows that include both positive and negative assertions. Although P contains many positive AB3/AB4/AB5 instances for standard algebraic categories and sheaves, the complete source bundles also assert failures for finite/torsion abelian groups or sheaf categories. The checked P/H/open sources do not formalize every clause, so these rows remain unmatched.
- U045's translation category of an abelian monoid, with its proof of filteredness and localization role, was not found in P, H, TauCeti, indexed GitHub Lean search, or open Mathlib work. Generic `IsFiltered` and one-object/monoid categories are prerequisites only and do not own this example.
- U002 contains the metatheoretic assertion that the collection of all sets is a proper class; universe-polymorphic `Type u` supplies the set-category paradigm but does not formalize that proper-class clause as the source states it. U005, U024 and U025 likewise bundle several examples/comparisons beyond the adjacent exact definitions, and U010 includes the negative assertion that an opposite module category need not be a module category over another ring. Strict bundle semantics leave all of these rows unmatched.
- U052 is direct: `Mathlib/Algebra/Category/Grp/Adjunctions.lean::GrpCat.abelianizeAdj` gives abelianization as the reflector from groups to abelian groups, while `Mathlib/CategoryTheory/Sites/Sheafification.lean::sheafificationAdjunction` and `sheafification_reflective` give sheafification as the reflector from presheaves to sheaves.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, reuse of the FC03 recorded audits, TauCeti where relevant, indexed GitHub Lean search, open Mathlib PR search, and the targeted external checks above. A specialization, one clause/example of a bundled row, an unformalized negative assertion, or a theorem requiring reconstruction of a missing source clause is not credited as that row's route.
