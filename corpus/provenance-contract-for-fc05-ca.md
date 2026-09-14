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

- Source-local exact-route closure was refreshed on 2026-09-14 at project HEAD `02798a1488aa07fd945fa2286d64a7d29b6eac1c`. The audit is clause-wise: a row may be mapped from several checked owners, and an unmatched row records only the precise residual clauses. Previously delivered Appendix routes were reused rather than re-searched wholesale.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every P target promoted in the Appendix table was inspected at that exact revision. The generic category/functor/natural-transformation, skeleton, limits/colimits, filtered-category and adjunction interfaces substantially overlap FC03 (Riehl); the already-recorded FC03 Sweep-II audits were reused, while Weibel-specific bundled examples and Appendix-only clauses were checked independently.
- Current Mathlib was refreshed on 2026-09-14 at `H=2ff8073df352b7cb74638403c464ed5cd3f97ce2`. The live formalization-corpus `POST /api/search` index was queried for the remaining Appendix-A gaps (proper classes, opposite/right modules, torsion natural transformations, AB4*/AB5*, subobject distributivity, filtered action categories, and tensor-Hom adjunctions). No current/indexed result closes the residual clauses recorded in the table.
- U014 is no longer unmatched. Since the previous audit, `LeanCategories/Homological/NoncommutativeTensor.lean` has added `tensorLeftFunctor`/`tensorRightFunctor` for arbitrary associative rings; together with Mathlib's `preadditiveCoyoneda`, this gives both functors in Weibel A.2.1 exactly. U049 remains unmatched for a narrower reason: the arbitrary-ring tensor functor now exists and the free-module adjunction is native, but no checked arbitrary-ring tensor-Hom adjunction/right-adjoint equivalence was found. Mathlib's `monoidalClosedHomEquiv` still assumes a commutative base.
- U017 asks for an arbitrary subcategory obtained by selecting both objects and a composition-closed subset of ambient morphisms, with faithful inclusion. P/H have full-subcategory and wide-subcategory infrastructure, but no checked declaration realizes that whole general source construction; a full or wide specialization is not credited.
- U033 is direct at P even though Mathlib does not use the labels AB3/AB3*: the source conditions are arbitrary coproducts/products, and `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean::has_colimits_of_hasCoequalizers_and_coproducts` and `has_limits_of_hasEqualizers_and_products`, together with the automatic (co)equalizers of an abelian category, give the stated equivalence with cocompleteness/completeness.
- U035 is direct at P. `Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean::AB4` and `AB4Star` define exact coproducts/products, while `hasExactColimitsOfShape_of_preservesMono` and `hasExactLimitsOfShape_of_preservesEpi` supply the converse from preservation of monomorphisms/epimorphisms. Thus the source direct-sum-of-monos/product-of-epis formulation is represented at the pinned revision.
- U037's AB5/AB5* definitions are directly native, and `subobjectMk_of_isColimit_eq_iSup` supplies an important bridge to directed suprema. The exact residual is the full distributivity equivalence `B ∩ (sup A_i) = sup (B ∩ A_i)` and its dual; neither pinned/current Mathlib nor the refreshed index provides that iff.
- U034, U036 and U038 now record their positive and negative clauses separately. Mathlib supplies the standard AB3/AB4/AB4*/AB5 instances for abelian groups/modules. The project additionally proves `shrinkingCStarSheafAddCommGrp_not_AB4Star`, a genuine concrete sheaf counterexample. The rows remain unmatched only where the frozen source makes broader finite/torsion/sheaf or AB5* failure claims not established by those owners.
- U045's translation-category data are now recognized as a direct specialization of `CategoryTheory.ActionCategory`: the regular action of an abelian monoid on itself gives exactly morphisms `{m // m • i = j}`. What is still absent is the checked `IsFiltered` theorem/instance and the localization application. The live corpus index returned no `ActionCategory`/`IsFiltered` owner.
- U002's ordinary category-of-types clauses are native and Mathlib separately formalizes ZFC classes, but no checked bridge identifies Lean's universe-polymorphic `Type u` object collection with the single proper-class claim in the source. U010 likewise maps the opposite-ring/right-module clauses and retains only the negative module-category-classification assertion. U024 maps tensor/Hom naturality and leaves only the torsion-subgroup natural inclusion without an owner.
- U052 is direct: `Mathlib/Algebra/Category/Grp/Adjunctions.lean::GrpCat.abelianizeAdj` gives abelianization as the reflector from groups to abelian groups, while `Mathlib/CategoryTheory/Sites/Sheafification.lean::sheafificationAdjunction` and `sheafification_reflective` give sheafification as the reflector from presheaves to sheaves.
- The dated unmatched rows now carry their supplied declarations and residual clauses directly. Their negative evidence consists of the earlier project/P/current/open/external audit plus the 2026-09-14 current-Mathlib and live-index refresh for those residuals. No row is kept unmatched merely because its source sentence bundles several clauses.
