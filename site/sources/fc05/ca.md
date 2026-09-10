---
title: "Appendix A. Category Theory Language"
---

FC05 — Weibel, *An Introduction to Homological Algebra* — block `FC05-CA`.

52 units. 39 have a Lean owner; 13 do not.

| Route | Units | Share | Meaning |
| --- | ---: | ---: | --- |
| [`mathlib`]{.route-mathlib} | 39 | 75% | Mathlib owns the unit outright. |
| [`unmatched`]{.route-unmatched} | 13 | 25% | No checked Lean owner was found. |
| **total** | **52** | | |

::: {.callout-note collapse="true"}
## How this chapter was searched

- Project-first search was performed at repository HEAD [`f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5`](https://github.com/leanprover-community/mathlib4/commit/f90173886bc881c2d43c0a7eb2d9fe7f110ac9a5). No project declaration owns a complete Appendix-A source row under strict bundle semantics.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every P target promoted in the Appendix table was inspected at that exact revision. The generic category/functor/natural-transformation, skeleton, limits/colimits, filtered-category and adjunction interfaces substantially overlap FC03 (Riehl); the already-recorded FC03 Sweep-II audits were reused, while Weibel-specific bundled examples and Appendix-only clauses were checked independently.
- Current Mathlib was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`, Apache-2.0, Lean 4.34.0-rc2. Targeted H searches did not add a general arbitrary subcategory interface matching U017, the abelian-monoid translation category U045, the full AB5 directed-subobject-lattice equivalence U037, or the noncommutative tensor-Hom adjunctions required by U014/U049.
- U014 and U049 are deliberately not inferred from the pinned closed monoidal `ModuleCat` API. [`Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean::monoidalClosedHomEquiv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.html) is formulated over a commutative base ring. Open Mathlib PR [#8495](https://github.com/leanprover-community/mathlib4/pull/8495), audited at head [`5b358de183c6084a8378e2d6418ce48cf2d7fb68`](https://github.com/leanprover-community/mathlib4/commit/5b358de183c6084a8378e2d6418ce48cf2d7fb68), develops a Hom-tensor adjunction but likewise assumes `[CommRing R]`. Weibel's rows use the general right/left module tensor-Hom adjunction over an arbitrary ring, so neither checked interface owns the whole source bundle.
- U017 asks for an arbitrary subcategory obtained by selecting both objects and a composition-closed subset of ambient morphisms, with faithful inclusion. P/H have full-subcategory and wide-subcategory infrastructure, but no checked declaration realizes that whole general source construction; a full or wide specialization is not credited.
- U033 is direct at P even though Mathlib does not use the labels AB3/AB3*: the source conditions are arbitrary coproducts/products, and [`Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean::has_colimits_of_hasCoequalizers_and_coproducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.html) and `has_limits_of_hasEqualizers_and_products`, together with the automatic (co)equalizers of an abelian category, give the stated equivalence with cocompleteness/completeness.
- U035 is direct at P. [`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean::AB4`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.html) and `AB4Star` define exact coproducts/products, while `hasExactColimitsOfShape_of_preservesMono` and `hasExactLimitsOfShape_of_preservesEpi` supply the converse from preservation of monomorphisms/epimorphisms. Thus the source direct-sum-of-monos/product-of-epis formulation is represented at the pinned revision.
- U037 is bundled more strongly than Mathlib's AB5 definition. P has `AB5`/`AB5Star` as exact filtered colimits/cofiltered limits, and [`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Subobject.lean::subobjectMk_of_isColimit_eq_iSup`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Subobject.html) relates filtered colimits of subobjects to suprema. The audit found no declaration giving Weibel's full distributivity equivalence `B ∩ (sup A_i) = sup (B ∩ A_i)` together with its dual. Therefore U037 remains unmatched rather than receiving partial credit.
- U034, U036 and U038 are heterogeneous example rows that include both positive and negative assertions. Although P contains many positive AB3/AB4/AB5 instances for standard algebraic categories and sheaves, the complete source bundles also assert failures for finite/torsion abelian groups or sheaf categories. The checked P/H/open sources do not formalize every clause, so these rows remain unmatched.
- U045's translation category of an abelian monoid, with its proof of filteredness and localization role, was not found in P, H, TauCeti, indexed GitHub Lean search, or open Mathlib work. Generic `IsFiltered` and one-object/monoid categories are prerequisites only and do not own this example.
- U002 contains the metatheoretic assertion that the collection of all sets is a proper class; universe-polymorphic `Type u` supplies the set-category paradigm but does not formalize that proper-class clause as the source states it. U005, U024 and U025 likewise bundle several examples/comparisons beyond the adjacent exact definitions, and U010 includes the negative assertion that an opposite module category need not be a module category over another ring. Strict bundle semantics leave all of these rows unmatched.
- U052 is direct: [`Mathlib/Algebra/Category/Grp/Adjunctions.lean::GrpCat.abelianizeAdj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Adjunctions.html#GrpCat.abelianizeAdj) gives abelianization as the reflector from groups to abelian groups, while [`Mathlib/CategoryTheory/Sites/Sheafification.lean::sheafificationAdjunction`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Sheafification.html) and `sheafification_reflective` give sheafification as the reflector from presheaves to sheaves.
- `N` denotes dated 2026-09-06 negative evidence after project-first inspection, P, H/current Mathlib, reuse of the FC03 recorded audits, TauCeti where relevant, indexed GitHub Lean search, open Mathlib PR search, and the targeted external checks above. A specialization, one clause/example of a bundled row, an unformalized negative assertion, or a theorem requiring reconstruction of a missing source clause is not credited as that row's route.
:::

### **Definition A.1.1** {#fc05-ca-u001}

::: {.unit-meta}
`FC05-CA-U001` · §A.1 Categories; pp. 417–420; L11875 · [`mathlib`]{.route-mathlib}
:::

A category C consists of a class of objects, Hom sets, identity morphisms, and composition functions. The extraction ends with “subject to two axioms:” but the two axioms themselves are absent before A.1.2.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Category/Basic.lean::CategoryStruct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html), `Category` — Pinned Mathlib packages objects/Hom types, identities and composition in `CategoryStruct`/`Category`, including associativity and identity laws, exactly the source category definition.
:::

### **Paradigm A.1.2** {#fc05-ca-u002}

::: {.unit-meta}
`FC05-CA-U002` · §A.1 Categories; pp. 417–420; L11877 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`unmatched`]{.route-unmatched}
:::

Sets is the paradigm category: objects are sets, morphisms are functions, composition is ordinary composition, and identities are identity functions; the object collection is a proper class rather than a set.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: Sets is the paradigm category: objects are sets, morphisms are functions, composition is ordinary composition, and identities are identity functions; the object collection is a proper class rather than a set. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Examples A.1.3** {#fc05-ca-u003}

::: {.unit-meta}
`FC05-CA-U003` · §A.1 Categories; pp. 417–420; L11879–11885 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

Records Ab, Groups, Rings, left/right module categories, and discrete categories as standard examples; a discrete category has only identity morphisms.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Types.lean::instance : Category (Type u)`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Types.html); [`Mathlib/Algebra/Category/Grp/Basic.lean::AddCommGrpCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Basic.html), `GrpCat`; [`Mathlib/Algebra/Category/Ring/Basic.lean::RingCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Ring/Basic.html); [`Mathlib/Algebra/Category/ModuleCat/Basic.lean::ModuleCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Basic.html); [`Mathlib/CategoryTheory/Discrete/Basic.lean::Discrete`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Discrete/Basic.html) — Pinned Mathlib has the source's sets, abelian groups, groups, rings, module, and discrete-category paradigms as concrete category instances.
:::

### **Definition/comparison — Small categories A.1.4** {#fc05-ca-u004}

::: {.unit-meta}
`FC05-CA-U004` · §A.1 Categories; pp. 417–420; L11887–11891 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

A category is small when its objects form a set; a poset becomes a small category with at most one arrow p→q, and a one-object category is a monoid, hence a group is a one-object category.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Category/Basic.lean::SmallCategory`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html); [`Mathlib/CategoryTheory/Category/Preorder.lean::Preorder.smallCategory`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Preorder.html#Preorder.smallCategory); [`Mathlib/CategoryTheory/SingleObj.lean::SingleObj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/SingleObj.html) — These declarations give the small-category notion, the category attached to a preorder/poset, and the one-object category attached to a monoid (hence a group), matching the source examples.
:::

### **Definition — isomorphism** {#fc05-ca-u005}

::: {.unit-meta}
`FC05-CA-U005` · §A.1 Categories; pp. 417–420; L11895 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`unmatched`]{.route-unmatched}
:::

A morphism f:B→C is an isomorphism when it has a two-sided inverse, which is unique; the paragraph compares categorical isomorphisms with bijections, homeomorphisms, diffeomorphisms, and group elements.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: A morphism f:B→C is an isomorphism when it has a two-sided inverse, which is unique; the paragraph compares categorical isomorphisms with bijections, homeomorphisms, diffeomorphisms, and group elements. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **A.1.5 (monic, epi, subobject)** {#fc05-ca-u006}

::: {.unit-meta}
`FC05-CA-U006` · §A.1 Categories; pp. 417–420; L11897–11899 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

Defines monic by left cancellation and epi by right cancellation; in concrete algebraic categories these agree with injective/surjective maps in the stated cases. A subobject is represented by a monic, technically up to mutual factorization.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/EpiMono.lean::Mono`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/EpiMono.html), `Epi`; [`Mathlib/CategoryTheory/Subobject/Basic.lean::Subobject`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Subobject/Basic.html), [`Subobject.mk`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subobject.mk#doc), [`Subobject.mk_le_mk_of_comm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subobject.mk_le_mk_of_comm#doc); concrete mono/epi instances in [`Mathlib/Algebra/Category/Grp/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Basic.html) and [`Mathlib/Algebra/Category/ModuleCat/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Basic.html) — Pinned Mathlib formalizes categorical monomorphisms/epimorphisms and subobjects as isomorphism classes of monomorphisms ordered by factorization; the standard algebraic concrete categories identify these with the expected injective/surjective maps.
:::

### **A.1.6 (initial, terminal, zero objects)** {#fc05-ca-u007}

::: {.unit-meta}
`FC05-CA-U007` · §A.1 Categories; pp. 417–420; L11903 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

Defines initial and terminal objects by unique maps out of/into them and a zero object as both; gives Sets and module-category examples.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean::IsInitial`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.html), `IsTerminal`; [`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean::HasZeroObject`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.html), `IsZero`; standard instances for `Type` and `ModuleCat` — Pinned Mathlib has the source universal properties for initial, terminal and zero objects, with the standard sets/module examples.
:::

### **Definition — zero morphisms, kernels, and cokernels** {#fc05-ca-u008}

::: {.unit-meta}
`FC05-CA-U008` · §A.1 Categories; pp. 417–420; L11905 · after [`FC05-CA-U006`](#fc05-ca-u006), [`FC05-CA-U007`](#fc05-ca-u007) · [`mathlib`]{.route-mathlib}
:::

In a category with zero object, defines zero maps via B→0→C; defines kernels and cokernels by their universal factorization properties, noting kernels are monic and cokernels epi.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean::HasZeroMorphisms`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.html); [`Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean::kernel`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Kernels.html), `kernelIsKernel`, `cokernel`, `cokernelIsCokernel`, `instance : Mono (kernel.ι f)`, `instance : Epi (cokernel.π f)` — The pinned kernel/cokernel API is stated by the same zero-composite universal properties and records kernel arrows monic and cokernel arrows epic, exactly the source bundle.
:::

### **Definition/construction — Opposite Category A.1.7** {#fc05-ca-u009}

::: {.unit-meta}
`FC05-CA-U009` · §A.1 Categories; pp. 417–420; L11909 · after [`FC05-CA-U001`](#fc05-ca-u001), [`FC05-CA-U006`](#fc05-ca-u006), [`FC05-CA-U008`](#fc05-ca-u008) · [`mathlib`]{.route-mathlib}
:::

C^op has the same objects and reversed morphisms/composition; taking opposites interchanges monic/epi, kernel/cokernel, and initial/terminal objects.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Opposites.lean::Category.opposite`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Opposites.html#Category.opposite); [`Mathlib/CategoryTheory/EpiMono.lean::op_epi_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/EpiMono.html), `op_mono_of_epi`; [`Mathlib/CategoryTheory/Limits/Opposites.lean::hasLimitsOfShape_opposite_iff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Opposites.html), `hasColimitsOfShape_opposite_iff`; [`Mathlib/CategoryTheory/Abelian/Opposite.lean::kernelOpOp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Opposite.html), `cokernelOpOp` — Pinned Mathlib reverses arrows in the opposite category and explicitly exchanges mono/epi, limits/colimits (hence initial/terminal), and kernel/cokernel, matching the source duality statement.
:::

### **Example A.1.8** {#fc05-ca-u010}

::: {.unit-meta}
`FC05-CA-U010` · §A.1 Categories; pp. 417–420; L11911 · after [`FC05-CA-U004`](#fc05-ca-u004), [`FC05-CA-U009`](#fc05-ca-u009) · [`unmatched`]{.route-unmatched}
:::

For a ring R viewed as a one-object category, R^op reverses multiplication and `(R^op)-mod≅mod-R`; the opposite of R-mod need not itself be S-mod for a ring S.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: For a ring R viewed as a one-object category, R^op reverses multiplication and `(R^op)-mod≅mod-R`; the opposite of R-mod need not itself be S-mod for a ring S. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition — Products and Coproducts A.1.9** {#fc05-ca-u011}

::: {.unit-meta}
`FC05-CA-U011` · §A.1 Categories; pp. 417–420; L11915–11917 · after [`FC05-CA-U009`](#fc05-ca-u009) · [`mathlib`]{.route-mathlib}
:::

Defines arbitrary products by projections and their universal property and coproducts dually by injections; records uniqueness up to isomorphism and standard examples in Sets, Groups, and R-mod.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/Shapes/Products.lean::HasProduct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Products.html), `productIsProduct`, `HasCoproduct`, `coproductIsCoproduct` — Pinned Mathlib's product and coproduct cones/cocones carry the same universal properties and uniqueness up to unique isomorphism as the source definition.
:::

### **Definition — functor** {#fc05-ca-u012}

::: {.unit-meta}
`FC05-CA-U012` · §A.2 Functors; pp. 421–422; L11929–11935 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

A functor F:C→D maps objects and morphisms, preserves identities and composition, induces maps on Hom sets, and composes in the evident way.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/Basic.lean::Functor`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Basic.html) — Pinned Mathlib's `Functor` preserves identities and composition on the nose and supplies object/morphism maps, exactly the source definition.
:::

### **Construction — identity functor and Cat** {#fc05-ca-u013}

::: {.unit-meta}
`FC05-CA-U013` · §A.2 Functors; pp. 421–422; L11937 · after [`FC05-CA-U004`](#fc05-ca-u004), [`FC05-CA-U012`](#fc05-ca-u012) · [`mathlib`]{.route-mathlib}
:::

Defines id_C and forms Cat, the category of small categories and functors, avoiding the set-theoretic difficulty of a category of all categories.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/Basic.lean::Functor.id`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Basic.html#Functor.id); [`Mathlib/CategoryTheory/Category/Cat/Basic.lean::Cat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Cat/Basic.html) — Pinned Mathlib has the identity functor and the category whose objects are small categories and arrows are functors, matching the source examples.
:::

### **Example/comparison — Hom and Tensor Product A.2.1** {#fc05-ca-u014}

::: {.unit-meta}
`FC05-CA-U014` · §A.2 Functors; pp. 421–422; L11939 · after [`FC05-CA-U012`](#fc05-ca-u012), [`FC05-C02-U054`](c02.html#fc05-c02-u054) · [`unmatched`]{.route-unmatched}
:::

For a right R-module M, M⊗_R− is a functor R-mod→Ab and Hom_R(M,−) is a functor mod-R→Ab.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: For a right R-module M, M⊗_R− is a functor R-mod→Ab and Hom_R(M,−) is a functor mod-R→Ab. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition/example — Forgetful Functors A.2.2** {#fc05-ca-u015}

::: {.unit-meta}
`FC05-CA-U015` · §A.2 Functors; pp. 421–422; L11941 · after [`FC05-CA-U012`](#fc05-ca-u012) · [`mathlib`]{.route-mathlib}
:::

A forgetful functor discards specified structure; examples include R-mod→Ab→Sets and their composite.

::: {.unit-lean}
**In Lean.** [`Mathlib/Algebra/Category/ModuleCat/Basic.lean::forget₂ (ModuleCat R) AddCommGrpCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Basic.html); [`Mathlib/CategoryTheory/ConcreteCategory/Basic.lean::forget AddCommGrpCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/ConcreteCategory/Basic.html) — The pinned concrete-category forgetful functors realize the source chain from modules through additive groups to underlying types.
:::

### **Definition — Faithful Functors A.2.3** {#fc05-ca-u016}

::: {.unit-meta}
`FC05-CA-U016` · §A.2 Functors; pp. 421–422; L11943 · after [`FC05-CA-U012`](#fc05-ca-u012), [`FC05-CA-U015`](#fc05-ca-u015) · [`mathlib`]{.route-mathlib}
:::

F:C→D is faithful when every induced Hom-set map is injective; a category admitting a faithful underlying-set functor U:C→Sets is concrete.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/FullyFaithful.lean::Functor.Faithful`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/FullyFaithful.html#Functor.Faithful); [`Mathlib/CategoryTheory/ConcreteCategory/Basic.lean::ConcreteCategory`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/ConcreteCategory/Basic.html), `forget` — Pinned Mathlib defines faithful functors by injectivity on Hom maps and concrete categories by a faithful forgetful functor to types, exactly the source criterion.
:::

### **Definition — subcategory** {#fc05-ca-u017}

::: {.unit-meta}
`FC05-CA-U017` · §A.2 Functors; pp. 421–422; L11945 · after [`FC05-CA-U001`](#fc05-ca-u001), [`FC05-CA-U016`](#fc05-ca-u016) · [`unmatched`]{.route-unmatched}
:::

A subcategory selects objects and morphisms closed under identities and composition; its inclusion functor is faithful.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: A subcategory selects objects and morphisms closed under identities and composition; its inclusion functor is faithful. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition — full subcategory** {#fc05-ca-u018}

::: {.unit-meta}
`FC05-CA-U018` · §A.2 Functors; pp. 421–422; L11947 · after [`FC05-CA-U017`](#fc05-ca-u017) · [`mathlib`]{.route-mathlib}
:::

A subcategory B⊂C is full when Hom_B(B,B′)=Hom_C(B,B′) for all its objects, so it is determined by its object class.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/FullSubcategory.lean::ObjectProperty.FullSubcategory`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/FullSubcategory.html#ObjectProperty.FullSubcategory), `ObjectProperty.ι` — Pinned Mathlib constructs the full subcategory on any selected object property, with all ambient morphisms between selected objects, exactly the source full-subcategory definition.
:::

### **Definition — full and fully faithful functors** {#fc05-ca-u019}

::: {.unit-meta}
`FC05-CA-U019` · §A.2 Functors; pp. 421–422; L11949 · after [`FC05-CA-U016`](#fc05-ca-u016), [`FC05-CA-U018`](#fc05-ca-u018) · [`mathlib`]{.route-mathlib}
:::

A functor is full when each induced Hom map is surjective and fully faithful when it is both full and faithful; inclusions of full subcategories and the Yoneda embedding are examples.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/FullyFaithful.lean::Functor.Full`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/FullyFaithful.html#Functor.Full), [`Functor.Faithful`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.Faithful#doc), [`Functor.FullyFaithful`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.FullyFaithful#doc); [`Mathlib/CategoryTheory/Yoneda.lean::Yoneda.fullyFaithful`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html#Yoneda.fullyFaithful); [`Mathlib/CategoryTheory/FullSubcategory.lean::ObjectProperty.ι`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/FullSubcategory.html) — Pinned Mathlib defines full and faithful functors by surjectivity/injectivity on Hom maps; both the full-subcategory inclusion and Yoneda have the stated fully-faithful behavior.
:::

### **Definition — Skeletal Subcategories A.2.4** {#fc05-ca-u020}

::: {.unit-meta}
`FC05-CA-U020` · §A.2 Functors; pp. 421–422; L11951 · after [`FC05-CA-U005`](#fc05-ca-u005), [`FC05-CA-U018`](#fc05-ca-u018) · [`mathlib`]{.route-mathlib}
:::

A skeletal subcategory S⊂C is full and contains exactly one representative from each isomorphism class of objects of C.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Skeletal.lean::Skeletal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Skeletal.html), `IsSkeletonOf`, `Skeleton`, `skeleton_skeletal`, `skeleton_isSkeleton` — Pinned Mathlib chooses one object per isomorphism class via `Skeleton C` and proves the resulting category skeletal and a skeleton of C, exactly the source notion.
:::

### **Construction — reflection onto a skeletal subcategory** {#fc05-ca-u021}

::: {.unit-meta}
`FC05-CA-U021` · §A.2 Functors; pp. 421–422; L11953 · after [`FC05-CA-U020`](#fc05-ca-u020), [`FC05-CA-U019`](#fc05-ca-u019) · [`mathlib`]{.route-mathlib}
:::

Choosing representatives FC∈S and isomorphisms θ_C:C≅FC defines F(f)=θ_C f θ_B^{-1}; this reflection functor is fully faithful.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Skeletal.lean::toSkeletonFunctor`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Skeletal.html), `fromSkeleton`, `skeletonEquivalence`; instances `(fromSkeleton C).Full`, `(fromSkeleton C).Faithful` — Pinned Mathlib constructs the choice-based functor from C to its skeleton and the inverse inclusion, proves them an equivalence, and records the inclusion fully faithful; this is the source skeleton-reflection construction.
:::

### **Definition/example — Contravariant Functors A.2.5** {#fc05-ca-u022}

::: {.unit-meta}
`FC05-CA-U022` · §A.2 Functors; pp. 421–422; L11955–11957 · after [`FC05-CA-U009`](#fc05-ca-u009), [`FC05-CA-U012`](#fc05-ca-u012) · [`mathlib`]{.route-mathlib}
:::

A contravariant F:C→D is a covariant functor C^op→D, reversing arrows and composition; examples include Hom_R(−,N) and presheaves.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Opposites.lean::Category.opposite`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Opposites.html#Category.opposite); [`Mathlib/CategoryTheory/Yoneda.lean::yoneda`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html); presheaf abbreviations in [`Mathlib/CategoryTheory/Sites/Sheaf.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Sheaf.html) — A contravariant functor is represented exactly as a functor out of `Cᵒᵖ`; representable Hom and presheaf examples use that convention.
:::

### **Definition — natural transformation and natural isomorphism** {#fc05-ca-u023}

::: {.unit-meta}
`FC05-CA-U023` · §A.3 Natural Transformations; p. 423; L11961–11967 · after [`FC05-CA-U012`](#fc05-ca-u012), [`FC05-CA-U005`](#fc05-ca-u005) · [`mathlib`]{.route-mathlib}
:::

For F,G:C→D, a natural transformation η:F⇒G assigns η_C:F(C)→G(C) commuting with every morphism square; it is a natural isomorphism when every component is an isomorphism.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/NatTrans.lean::NatTrans`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/NatTrans.html); [`Mathlib/CategoryTheory/NatIso.lean::NatTrans.isIso_iff_isIso_app`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/NatIso.html#NatTrans.isIso_iff_isIso_app) — Pinned Mathlib packages the component maps and naturality squares of natural transformations and identifies natural isomorphisms with componentwise isomorphisms, matching the source definition.
:::

### **Examples A.3.1** {#fc05-ca-u024}

::: {.unit-meta}
`FC05-CA-U024` · §A.3 Natural Transformations; p. 423; L11969–11973 · after [`FC05-CA-U023`](#fc05-ca-u023), [`FC05-CA-U014`](#fc05-ca-u014) · [`unmatched`]{.route-unmatched}
:::

Gives the torsion-subgroup inclusion, tensor maps induced by a module homomorphism, and precomposition maps on Hom as natural transformations, with links to Tor/Ext and δ-functors.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: Gives the torsion-subgroup inclusion, tensor maps induced by a module homomorphism, and precomposition maps on Hom as natural transformations, with links to Tor/Ext and δ-functors. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition — Equivalence A.3.2** {#fc05-ca-u025}

::: {.unit-meta}
`FC05-CA-U025` · §A.3 Natural Transformations; p. 423; L11975 · after [`FC05-CA-U023`](#fc05-ca-u023), [`FC05-CA-U020`](#fc05-ca-u020) · [`unmatched`]{.route-unmatched}
:::

F:C→D is an equivalence when some G:D→C has natural isomorphisms id_C≅GF and id_D≅FG; skeletal inclusion and forgetting a chosen basis are examples.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: F:C→D is an equivalence when some G:D→C has natural isomorphisms id_C≅GF and id_D≅FG; skeletal inclusion and forgetting a chosen basis are examples. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition/construction — Functor Categories A.3.3** {#fc05-ca-u026}

::: {.unit-meta}
`FC05-CA-U026` · §A.3 Natural Transformations; p. 423; L11977 · after [`FC05-CA-U013`](#fc05-ca-u013), [`FC05-CA-U023`](#fc05-ca-u023) · [`mathlib`]{.route-mathlib}
:::

For small I and category A, A^I has functors I→A as objects and natural transformations as morphisms, composed componentwise; if A is abelian then A^I is abelian.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/Category.lean::Functor.category`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Category.html#Functor.category); [`Mathlib/CategoryTheory/Abelian/FunctorCategory.lean::functorCategoryAbelian`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/FunctorCategory.html) — Pinned Mathlib makes the diagram/functor category `I ⥤ A` a category and proves it abelian whenever A is abelian, exactly the source theorem.
:::

### **Example A.3.4 (Yoneda embedding)** {#fc05-ca-u027}

::: {.unit-meta}
`FC05-CA-U027` · §A.3 Natural Transformations; p. 423; L11979 · after [`FC05-CA-U019`](#fc05-ca-u019), [`FC05-CA-U022`](#fc05-ca-u022), [`FC05-CA-U026`](#fc05-ca-u026), [`FC05-C01-U062`](c01.html#fc05-c01-u062) · [`mathlib`]{.route-mathlib}
:::

The Yoneda functor h:I→Sets^{I^op}, i↦Hom_I(−,i), is fully faithful; for an Ab-category it lands in Ab^{I^op}, embedding additive categories as full subcategories of abelian categories.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean::preadditiveYoneda`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.html), full and faithful instances; [`Mathlib/CategoryTheory/Abelian/FunctorCategory.lean::functorCategoryAbelian`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/FunctorCategory.html) — Pinned Mathlib's preadditive Yoneda lands in additive-group-valued functors and is full and faithful; that functor category is abelian, giving precisely the source additive embedding into a full subcategory of an abelian category.
:::

### **A.4.1 (Ab-category)** {#fc05-ca-u028}

::: {.unit-meta}
`FC05-CA-U028` · §A.4 Abelian Categories; pp. 424–426; L11985–11993 · after [`FC05-CA-U001`](#fc05-ca-u001) · [`mathlib`]{.route-mathlib}
:::

An Ab-category has an abelian-group structure on every Hom set with composition bilinear; endomorphisms form rings, and R-mod is the basic example.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Preadditive/Basic.lean::Preadditive`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Basic.html), `instance {X : C} : Ring (End X)`; [`Mathlib/Algebra/Category/ModuleCat/Basic.lean::ModuleCat`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Basic.html) — Pinned Mathlib equips each Hom with an additive commutative group and composition with bilinearity, induces the endomorphism ring, and has the standard module-category example.
:::

### **Definition — additive category** {#fc05-ca-u029}

::: {.unit-meta}
`FC05-CA-U029` · §A.4 Abelian Categories; pp. 424–426; L11995 · after [`FC05-CA-U028`](#fc05-ca-u028), [`FC05-CA-U007`](#fc05-ca-u007), [`FC05-CA-U011`](#fc05-ca-u011) · [`mathlib`]{.route-mathlib}
:::

An additive category is an Ab-category with a zero object and all binary products; finite products then coincide with finite coproducts and are written A⊕B.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Preadditive/Basic.lean::Preadditive`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Basic.html); [`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean::HasZeroObject`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.html); [`Mathlib/CategoryTheory/Preadditive/Biproducts.lean::HasBinaryBiproducts.of_hasBinaryProducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Preadditive/Biproducts.html#HasBinaryBiproducts.of_hasBinaryProducts); [`Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean::HasBinaryBiproducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.html) — Pinned Mathlib expresses the source additive-category structure through preadditivity, a zero object and finite biproducts, and proves binary products in a preadditive setting induce biproducts, hence finite products and coproducts coincide as stated.
:::

### **Definition A.4.2** {#fc05-ca-u030}

::: {.unit-meta}
`FC05-CA-U030` · §A.4 Abelian Categories; pp. 424–426; L11997–12003 · after [`FC05-CA-U029`](#fc05-ca-u029), [`FC05-CA-U006`](#fc05-ca-u006), [`FC05-CA-U008`](#fc05-ca-u008) · [`mathlib`]{.route-mathlib}
:::

An abelian category is additive, every map has kernel and cokernel, every monic is the kernel of its cokernel, and every epi is the cokernel of its kernel.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Abelian/Basic.lean::Abelian`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Basic.html), [`Abelian.mk'`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.mk'#doc), [`Abelian.hasZeroObject`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.hasZeroObject#doc), [`Abelian.hasFiniteBiproducts`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.hasFiniteBiproducts#doc); normal mono/epi interfaces in [`Mathlib/CategoryTheory/Limits/Shapes/NormalMono/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/NormalMono/Basic.html) — Pinned Mathlib's `Abelian` is an equivalent packaged form of the source axioms: preadditivity/additivity together with kernels/cokernels and every mono/epi normal; [`Abelian.mk'`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.mk'#doc) supplies the standard constructor from kernel/cokernel data.
:::

### **Construction — image factorization in an abelian category** {#fc05-ca-u031}

::: {.unit-meta}
`FC05-CA-U031` · §A.4 Abelian Categories; pp. 424–426; L12014–12020 · after [`FC05-CA-U030`](#fc05-ca-u030), [`FC05-CA-U008`](#fc05-ca-u008) · [`mathlib`]{.route-mathlib}
:::

Every f:B→C factors as an epi B→im(f) followed by the monic im(f)=ker(coker f)→C; this defines the image subobject.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Abelian/Basic.lean::Abelian.image`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Basic.html#Abelian.image), `imageMonoFactorisation`, `imageFactorisation`, [`Abelian.factorThruImage`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.factorThruImage#doc) — Pinned Mathlib defines the abelian image through the kernel-of-cokernel construction and provides the canonical epi-mono factorization through it, exactly the source statement.
:::

### **Definition — exact sequence** {#fc05-ca-u032}

::: {.unit-meta}
`FC05-CA-U032` · §A.4 Abelian Categories; pp. 424–426; L12022 · after [`FC05-CA-U030`](#fc05-ca-u030), [`FC05-CA-U031`](#fc05-ca-u031) · [`mathlib`]{.route-mathlib}
:::

A sequence A→B→C in an abelian category is exact at B when ker(g)=im(f), which in particular forces gf=0.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Abelian/Exact.lean::exact_iff_image_eq_kernel`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Exact.html); [`Mathlib/Algebra/Homology/ShortComplex/Basic.lean::ShortComplex.Exact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/Basic.html#ShortComplex.Exact) — Pinned Mathlib characterizes exactness of a composable zero pair by equality of image and kernel subobjects, exactly Weibel's definition; the short-complex condition includes the required composite-zero relation.
:::

### **A.4.3 (AB3 and AB3*)** {#fc05-ca-u033}

::: {.unit-meta}
`FC05-CA-U033` · §A.4 Abelian Categories; pp. 424–426; L12024–12027 · after [`FC05-CA-U011`](#fc05-ca-u011), [`FC05-CA-U030`](#fc05-ca-u030) · [`mathlib`]{.route-mathlib}
:::

AB3 requires all set-indexed coproducts and is called cocompleteness; AB3* requires all set-indexed products and is called completeness.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/Shapes/Products.lean::HasCoproducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Products.html), `HasProducts`; [`Mathlib/CategoryTheory/Abelian/Basic.lean::Abelian.hasEqualizers`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Basic.html#Abelian.hasEqualizers), [`Abelian.hasCoequalizers`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Abelian.hasCoequalizers#doc); [`Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean::has_colimits_of_hasCoequalizers_and_coproducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.html), `has_limits_of_hasEqualizers_and_products` — Mathlib uses the underlying conditions rather than the names AB3/AB3*: arbitrary coproducts/products. In an abelian category the pinned construction theorems combine these with automatic coequalizers/equalizers to obtain all colimits/limits, matching the source cocomplete/complete equivalence.
:::

### **Example A.4.4** {#fc05-ca-u034}

::: {.unit-meta}
`FC05-CA-U034` · §A.4 Abelian Categories; pp. 424–426; L12029 · after [`FC05-CA-U033`](#fc05-ca-u033) · [`unmatched`]{.route-unmatched}
:::

Ab and R-mod satisfy AB3 and AB3*; finite abelian groups satisfy neither, torsion abelian groups satisfy AB3 but not AB3*, and countable products/coproducts already suffice for several homological constructions.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: Ab and R-mod satisfy AB3 and AB3*; finite abelian groups satisfy neither, torsion abelian groups satisfy AB3 but not AB3*, and countable products/coproducts already suffice for several homological constructions. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Definition — AB4 and AB4*** {#fc05-ca-u035}

::: {.unit-meta}
`FC05-CA-U035` · §A.4 Abelian Categories; pp. 424–426; L12033–12034 · after [`FC05-CA-U033`](#fc05-ca-u033), [`FC05-CA-U006`](#fc05-ca-u006) · [`mathlib`]{.route-mathlib}
:::

AB4 means cocomplete with direct sums of monics monic; AB4* means complete with products of epis epi. This main text resumes after Exercise A.4.4.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean::AB4`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.html), `AB4Star`, `hasExactColimitsOfShape_of_preservesMono`, `hasExactLimitsOfShape_of_preservesEpi` — Pinned Mathlib defines AB4/AB4* as exact coproducts/products. Exactness gives preservation of monos/epis, and the cited converse lemmas reconstruct exactness from preservation of monomorphisms/epimorphisms in an abelian category, matching the source direct-sum/product formulation.
:::

### **Example A.4.5** {#fc05-ca-u036}

::: {.unit-meta}
`FC05-CA-U036` · §A.4 Abelian Categories; pp. 424–426; L12036 · after [`FC05-CA-U035`](#fc05-ca-u035) · [`unmatched`]{.route-unmatched}
:::

Ab and R-mod satisfy AB4 and AB4*; Sheaves(X) is complete but does not satisfy AB4*.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: Ab and R-mod satisfy AB4 and AB4*; Sheaves(X) is complete but does not satisfy AB4*. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **A.4.6 (AB5 and AB5*)** {#fc05-ca-u037}

::: {.unit-meta}
`FC05-CA-U037` · §A.4 Abelian Categories; pp. 424–426; L12052–12063 · after [`FC05-CA-U032`](#fc05-ca-u032), [`FC05-CA-U033`](#fc05-ca-u033) · [`unmatched`]{.route-unmatched}
:::

AB5 means cocomplete with filtered colimits of exact sequences exact, equivalently the stated distributivity identity for directed lattices of subobjects; AB5* is the dual filtered-inverse-limit condition with its dual identity.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: AB5 means cocomplete with filtered colimits of exact sequences exact, equivalently the stated distributivity identity for directed lattices of subobjects; AB5* is the dual filtered-inverse-limit condition with its dual identity. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Examples A.4.7** {#fc05-ca-u038}

::: {.unit-meta}
`FC05-CA-U038` · §A.4 Abelian Categories; pp. 424–426; L12066–12068 · after [`FC05-CA-U037`](#fc05-ca-u037), [`FC05-C02-U070`](c02.html#fc05-c02-u070) · [`unmatched`]{.route-unmatched}
:::

Ab and R-mod satisfy AB5 but not AB5*; Sheaves(X) likewise satisfies AB5 but not AB5*.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: Ab and R-mod satisfy AB5 but not AB5*; Sheaves(X) likewise satisfies AB5 but not AB5*. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **A.5.1 (limit)** {#fc05-ca-u039}

::: {.unit-meta}
`FC05-CA-U039` · §A.5 Limits and Colimits; pp. 427–428; L12076 · after [`FC05-CA-U012`](#fc05-ca-u012), [`FC05-CA-U011`](#fc05-ca-u011) · [`mathlib`]{.route-mathlib}
:::

A limit of F:I→A is an object L with compatible maps L→F_i universal among compatible cones; it is unique up to isomorphism, and products are limits over discrete indexing categories.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/HasLimits.lean::limit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html), `limit.π`, [`limit.isLimit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=limit.isLimit#doc), [`limit.existsUnique`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=limit.existsUnique#doc); [`Mathlib/CategoryTheory/Limits/Shapes/Products.lean::productIsProduct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Products.html) — Pinned Mathlib gives limits by terminal cones with unique mediating maps and treats products as limits of discrete diagrams, exactly the source definition and example.
:::

### **Definition — complete category** {#fc05-ca-u040}

::: {.unit-meta}
`FC05-CA-U040` · §A.5 Limits and Colimits; pp. 427–428; L12078 · after [`FC05-CA-U039`](#fc05-ca-u039), [`FC05-CA-U004`](#fc05-ca-u004) · [`mathlib`]{.route-mathlib}
:::

A is complete when every functor F:I→A with small I has a limit; Sets, Ab, and R-mod are complete.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/HasLimits.lean::HasLimits`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html); [`Mathlib/CategoryTheory/Limits/Types/Limits.lean::Types.hasLimitsOfShape`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Types/Limits.html#Types.hasLimitsOfShape); [`Mathlib/Algebra/Category/Grp/Limits.lean::AddCommGrpCat.hasLimits`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Limits.html#AddCommGrpCat.hasLimits); [`Mathlib/Algebra/Category/ModuleCat/Limits.lean::ModuleCat.hasLimits`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Limits.html#ModuleCat.hasLimits) — Pinned Mathlib expresses completeness as existence of all small limits and supplies it for sets, abelian groups and module categories, matching the source examples.
:::

### **Definition — colimit (main text resumes after Exercise A.5.1)** {#fc05-ca-u041}

::: {.unit-meta}
`FC05-CA-U041` · §A.5 Limits and Colimits; pp. 427–428; L12082 · after [`FC05-CA-U039`](#fc05-ca-u039), [`FC05-CA-U009`](#fc05-ca-u009), [`FC05-CA-U011`](#fc05-ca-u011) · [`mathlib`]{.route-mathlib}
:::

Dually, a colimit of F:I→A is an object C with compatible maps F_i→C universal among cocones; coproducts are special colimits and colimits in A are limits in A^op.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/HasLimits.lean::colimit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html), `colimit.ι`, [`colimit.isColimit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=colimit.isColimit#doc); [`Mathlib/CategoryTheory/Limits/Opposites.lean::hasColimit_op_iff_hasLimit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Opposites.html); [`Mathlib/CategoryTheory/Limits/Shapes/Products.lean::coproductIsCoproduct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Products.html) — Pinned Mathlib gives the dual cocone universal property, coproducts as discrete colimits, and the equivalence between colimits in C and limits in the opposite category, exactly the source bundle.
:::

### **Definition — cocomplete category** {#fc05-ca-u042}

::: {.unit-meta}
`FC05-CA-U042` · §A.5 Limits and Colimits; pp. 427–428; L12084 · after [`FC05-CA-U041`](#fc05-ca-u041), [`FC05-CA-U004`](#fc05-ca-u004) · [`mathlib`]{.route-mathlib}
:::

A is cocomplete when every functor from a small indexing category has a colimit; Sets, Ab, and R-mod are cocomplete.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Limits/HasLimits.lean::HasColimits`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html); [`Mathlib/CategoryTheory/Limits/Types/Colimits.lean::Types.hasColimitsOfShape`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Types/Colimits.html#Types.hasColimitsOfShape); [`Mathlib/Algebra/Category/Grp/Colimits.lean::AddCommGrpCat.hasColimitsOfShape`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Colimits.html#AddCommGrpCat.hasColimitsOfShape); [`Mathlib/Algebra/Category/ModuleCat/Colimits.lean::ModuleCat.hasColimitsOfSize`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Colimits.html#ModuleCat.hasColimitsOfSize) — Pinned Mathlib expresses cocompleteness as existence of all small colimits and supplies it for sets, abelian groups and module categories, matching the source examples.
:::

### **Construction/comparison — As a Natural Transformation A.5.2** {#fc05-ca-u043}

::: {.unit-meta}
`FC05-CA-U043` · §A.5 Limits and Colimits; pp. 427–428; L12088 · after [`FC05-CA-U023`](#fc05-ca-u023), [`FC05-CA-U039`](#fc05-ca-u039), [`FC05-CA-U041`](#fc05-ca-u041) · [`mathlib`]{.route-mathlib}
:::

The diagonal Δ:A→A^I sends A to the constant diagram. The structure maps of a limit form Δ(lim F)⇒F and those of a colimit form F⇒Δ(colim F), anticipating the adjunctions with Δ.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Functor/Const.lean::Functor.const`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Const.html#Functor.const); [`Mathlib/CategoryTheory/Limits/HasLimits.lean::constLimAdj`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html), `colimConstAdj` — The constant/diagonal functor is the source diagonal functor into the diagram category; pinned Mathlib proves it left-adjoint to `lim` and right-adjoint to `colim`, so limit cones and colimit cocones are exactly the corresponding natural-transformation universal properties.
:::

### **Definition — Filtered Categories and Direct Limits A.5.3** {#fc05-ca-u044}

::: {.unit-meta}
`FC05-CA-U044` · §A.5 Limits and Colimits; pp. 427–428; L12090–12092 · after [`FC05-CA-U004`](#fc05-ca-u004) · [`mathlib`]{.route-mathlib}
:::

A small category I is filtered when any two objects admit a common successor and any two parallel arrows become equal after postcomposition; directed posets are the special poset case.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Filtered/Basic.lean::IsFilteredOrEmpty`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Filtered/Basic.html), `IsFiltered`, `isDirectedOrder` — Pinned Mathlib's filtered-category structure contains the common-target/common-equalizer axioms plus nonemptiness, and relates filtered preorders to directed orders, exactly the source definition/example.
:::

### **Example/comparison — translation category of an abelian monoid** {#fc05-ca-u045}

::: {.unit-meta}
`FC05-CA-U045` · §A.5 Limits and Colimits; pp. 427–428; L12094 · after [`FC05-CA-U044`](#fc05-ca-u044), [`FC05-C10-U027`](c10.html#fc05-c10-u027) · [`unmatched`]{.route-unmatched}
:::

For an abelian monoid M, the category with objects M and morphisms i→j given by multipliers m with mi=j is filtered; this is the translation-category example used for localization.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: For an abelian monoid M, the category with objects M and morphisms i→j given by multipliers m with mi=j is filtered; this is the translation-category example used for localization. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Convention/notation — filtered colimits and direct limits** {#fc05-ca-u046}

::: {.unit-meta}
`FC05-CA-U046` · §A.5 Limits and Colimits; pp. 427–428; L12096 · after [`FC05-CA-U041`](#fc05-ca-u041), [`FC05-CA-U044`](#fc05-ca-u044) · [`mathlib`]{.route-mathlib}
:::

A filtered colimit is the colimit of a functor from a filtered category; over a directed poset it is also called a direct limit. The paragraph records the colim/lim notation used in the book.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Filtered/Basic.lean::IsFiltered`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Filtered/Basic.html); [`Mathlib/CategoryTheory/Limits/HasLimits.lean::colimit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html), `colimit.ι`; [`Mathlib/CategoryTheory/Limits/FilteredColimitCommutesFiniteLimit.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/FilteredColimitCommutesFiniteLimit.html) — A filtered/direct limit is represented in pinned Mathlib literally as the colimit of a diagram whose index category carries `IsFiltered`; the generic colimit object and structure maps supply the source notation/interface.
:::

### **Example A.5.4** {#fc05-ca-u047}

::: {.unit-meta}
`FC05-CA-U047` · §A.5 Limits and Colimits; pp. 427–428; L12098 · after [`FC05-CA-U044`](#fc05-ca-u044), [`FC05-CA-U046`](#fc05-ca-u046) · [`mathlib`]{.route-mathlib}
:::

For I=N, a covariant diagram is a sequence A_0→A_1→⋯ with direct limit colim A_i; a contravariant diagram is an inverse tower with inverse limit.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Category/Preorder.lean::Preorder.smallCategory`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Preorder.html#Preorder.smallCategory); [`Mathlib/CategoryTheory/Limits/HasLimits.lean::limit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/HasLimits.html), `colimit` — The natural numbers and their opposite are categories via their preorder structures, so functors from them are precisely direct sequences and inverse towers; pinned generic limits/colimits give their inverse/direct limits as stated.
:::

### **A.6.1 (adjoint functors)** {#fc05-ca-u048}

::: {.unit-meta}
`FC05-CA-U048` · §A.6 Adjoint Functors; pp. 429–431; L12102–12114 · after [`FC05-CA-U012`](#fc05-ca-u012), [`FC05-CA-U023`](#fc05-ca-u023) · [`mathlib`]{.route-mathlib}
:::

L:A→B and R:B→A are adjoint when Hom_B(LA,B)≅Hom_A(A,RB) naturally in A and B; L is the left adjoint and R the right adjoint.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Adjunction/Basic.lean::Adjunction`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Basic.html), [`Adjunction.mkOfHomEquiv`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Adjunction.mkOfHomEquiv#doc), [`Adjunction.homEquiv`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Adjunction.homEquiv#doc) — Pinned Mathlib defines an adjunction by the same natural family of Hom-set equivalences (and equivalent unit/counit data), exactly the source definition.
:::

### **Example/comparison — standard adjunctions** {#fc05-ca-u049}

::: {.unit-meta}
`FC05-CA-U049` · §A.6 Adjoint Functors; pp. 429–431; L12116–12118 · after [`FC05-CA-U048`](#fc05-ca-u048), [`FC05-CA-U014`](#fc05-ca-u014), [`FC05-CA-U015`](#fc05-ca-u015) · [`unmatched`]{.route-unmatched}
:::

The free k-vector-space functor is left adjoint to the underlying-set functor; for an R-module B, −⊗_R B is left adjoint to Hom_Ab(B,−) with the indicated module structure.

::: {.unit-lean}
**Not in Lean.** none; only partial/specialized adjacent category-theory infrastructure was found — As of 2026-09-06, no checked A/P/H/open/external/indexed Lean declaration realizes the whole source bundle: The free k-vector-space functor is left adjoint to the underlying-set functor; for an R-module B, −⊗_R B is left adjoint to Hom_Ab(B,−) with the indicated module structure. Strict bundle semantics reject a specialization, one example among several, a metatheoretic comment, an unformalized negative clause, or a proper subset as the route for the row.
:::

[Searched: N]{.unit-provenance}

### **Theorem A.6.2** {#fc05-ca-u050}

::: {.unit-meta}
`FC05-CA-U050` · §A.6 Adjoint Functors; pp. 429–431; L12122–12132 · after [`FC05-CA-U048`](#fc05-ca-u048), [`FC05-CA-U023`](#fc05-ca-u023) · [`mathlib`]{.route-mathlib}
:::

An adjunction determines unit η:id_A⇒RL and counit ε:LR⇒id_B; transposition is expressed by R(f)η and εL(g), and the two triangle composites are identities.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Adjunction/Basic.lean::Adjunction.unit`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Basic.html#Adjunction.unit), [`Adjunction.counit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Adjunction.counit#doc), [`Adjunction.left_triangle_components`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Adjunction.left_triangle_components#doc), `right_triangle_components`, `homEquiv_id`, `homEquiv_symm_id` — Pinned Mathlib exposes unit/counit, triangle identities, and the Hom-equivalence transposition formulas, exactly the source construction.
:::

### **Definition — Reflective Subcategories A.6.3** {#fc05-ca-u051}

::: {.unit-meta}
`FC05-CA-U051` · §A.6 Adjoint Functors; pp. 429–431; L12142 · after [`FC05-CA-U017`](#fc05-ca-u017), [`FC05-CA-U048`](#fc05-ca-u048) · [`mathlib`]{.route-mathlib}
:::

A subcategory B⊂A is reflective when its inclusion has a left adjoint L:A→B, called the reflection; for full B the reflected B-objects are naturally isomorphic to themselves.

::: {.unit-lean}
**In Lean.** [`Mathlib/CategoryTheory/Adjunction/Reflective.lean::Reflective`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Reflective.html), `reflector`, `reflectorAdjunction`, [`Functor.fullyFaithfulOfReflective`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.fullyFaithfulOfReflective#doc), [`Functor.essImage.unit_isIso`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Functor.essImage.unit_isIso#doc) — Pinned Mathlib defines a reflective full subcategory by a fully faithful right adjoint with a left reflector and proves the unit is an isomorphism on reflected objects, exactly the source definition and self-reflection property.
:::

### **examples of reflective subcategories** {#fc05-ca-u052}

::: {.unit-meta}
`FC05-CA-U052` · §A.6 Adjoint Functors; pp. 429–431; L12144 · after [`FC05-CA-U051`](#fc05-ca-u051), [`FC05-C02-U058`](c02.html#fc05-c02-u058) · [`mathlib`]{.route-mathlib}
:::

Ab is reflective in Groups via abelianization G↦G/[G,G]; sheaves on X are reflective in presheaves via sheafification.

::: {.unit-lean}
**In Lean.** [`Mathlib/Algebra/Category/Grp/Adjunctions.lean::GrpCat.abelianize`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/Grp/Adjunctions.html#GrpCat.abelianize), [`GrpCat.abelianizeAdj`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=GrpCat.abelianizeAdj#doc); [`Mathlib/CategoryTheory/Sites/Sheafification.lean::presheafToSheaf`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Sheafification.html), `sheafificationAdjunction`, `sheafification_reflective` — Pinned Mathlib proves abelianization left adjoint to the inclusion/forgetful functor from abelian groups and sheafification left adjoint to inclusion of sheaves into presheaves, exactly the two reflective examples.
:::

