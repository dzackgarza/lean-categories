---
title: "2026-08-09T15:46:59+0800 Definition-first audit of lean-categories plans"
---

## Verdict

The plans do not yet give a coherent mathematical specification.

Some central categories are defined correctly. Several other names remain templates. A few stated definitions are false.

The main catalogue mixes four different things:

- definitions;
- theorem statements;
- Mathlib implementation notes;
- correction history.

These layers now contradict one another.

## Evidence boundary

I inspected:

- both managed vault plans;
- the declaration section of the [category catalogue plan](home/dzack/.agent-memory-vault/projects/github.com__dzackgarza__lean-categories/plans/features/FEATURE-normalized-category-catalogue/plans/PLAN-category-scope-catalogue/PLAN-category-scope-catalogue);
- the mathematical sections of the [integration roadmap](home/dzack/.agent-memory-vault/projects/github.com__dzackgarza__lean-categories/plans/features/FEATURE-casdsl-categorygraph-integration/plans/PLAN-casdsl-categorygraph-integration-roadmap/PLAN-casdsl-categorygraph-integration-roadmap);
- the definition-bearing issue bodies from #22 through #41;
- issues #54 through #56;
- the five promoted catalogue comments.

I did not inspect every historical comment or implementation PR.

## False definitions

### Evenness

- Searched: the catalogue declarations and issue #34.
- Found: `EvenBil` means both `im(P)` and `𝔫(b)=2𝔰(b)`.
- Conclusion: these definitions disagree.
- Confidence: High.
- Gaps: None.

Take (M=\mathbb Z) and (b(x,y)=2xy). Define (q(x)=x^2).

Then

[ q(x+y)-q(x)-q(y)=2xy=b(x,y). ]

Thus (b\in\operatorname{im}(P)). However,

[ \mathfrak n(b)=2\mathbb Z,\qquad \mathfrak s(b)=2\mathbb Z,\qquad 2\mathfrak s(b)=4\mathbb Z. ]

Therefore (\mathfrak n(b)\ne2\mathfrak s(b)).

The correct integral evenness condition is (b(x,x)\in2R) for all (x). More general value modules require a separate formulation.

### Subobjects

- Searched: issue [#54](https://github.com/dzackgarza/lean-categories/issues/54).
- Found: `Subobjects(C)` is identified with the full subcategory of `Arr(C)` on monomorphisms.
- Conclusion: this is the category of monomorphisms, not the usual subobject construction.
- Confidence: High.
- Gaps: The intended total subobject fibration is not stated.

For fixed (X), `Subobject X` identifies monomorphisms into (X) up to isomorphism.

The full subcategory of `Arr(C)` on all monomorphisms retains their codomains. It is a different category.

If a total category is intended, the plan should name the Grothendieck construction of (X\mapsto\operatorname{Subobject}(X)).

### Chambers

- Searched: issue [#23](https://github.com/dzackgarza/lean-categories/issues/23) and its [promoted comment](https://github.com/dzackgarza/lean-categories/issues/23#issuecomment-5215699525).
- Found: the comment calls every chamber a polytope.
- Conclusion: the statement is false.
- Confidence: High.
- Gaps: The issue body later gives a better arrangement-complement definition.

An intersection of half-spaces is a polyhedron. It need not be bounded.

Vinberg chambers can be noncompact. Therefore they are not generally polytopes.

## Categories that are mathematically fixed

### Module-valued forms

Issue [#33](https://github.com/dzackgarza/lean-categories/issues/33) gives a valid construction:

[ \operatorname{Bil}_{R,W}\colon(\operatorname{ModuleCat}R)^{\mathrm{op}} \longrightarrow \operatorname{ModuleCat}R. ]

The opposite of its category of elements gives the intended category of (W)-valued bilinear modules.

The following full subcategories are also mathematically clear:

- symmetric forms;
- radical-free symmetric forms;
- perfect symmetric forms;
- arithmetic lattices after the stated Dedekind and finite-projective restrictions.

### Framing loci

The comma-category loci in #33 are clear:

- `GenFrame_n(R)` is the surjective locus in (R^n\downarrow R\text{-Mod});
- `BasisFrame_n(R)` is the isomorphism locus.

These are standard categorical constructions.

### Discriminant forms

The body of issue [#34](https://github.com/dzackgarza/lean-categories/issues/34) gives the correct primary definition:

[ A_L=L^#/L. ]

It also correctly separates this quotient from the cokernel of the adjoint map.

The discriminant functors belong on the appropriate isometry cores. This restriction is mathematically necessary.

### Signature

Issue [#36](https://github.com/dzackgarza/lean-categories/issues/36) gives a coherent signature functor on the core of symmetric forms over an ordered field:

[ (M,b)\longmapsto(n_+,n_-,n_0). ]

Definiteness and Lorentzian signature then become predicates on this value.

### Rational cones

Issue [#37](https://github.com/dzackgarza/lean-categories/issues/37) identifies rational polyhedral cones as a predicate-cut in Mathlib’s `PointedCone`.

This part is sufficiently precise. The fan category is not.

## Categories that remain undefined

### Higher classifier foundation

- Searched: issue [#30](https://github.com/dzackgarza/lean-categories/issues/30).
- Found: the strict `Cat` realization is specified.
- Found: the ambient ((\infty,2))-category or infinity-cosmos is not selected.
- Conclusion: the higher classifier is not yet a fixed mathematical construction.
- Confidence: High.
- Gaps: A model may exist in `FOUNDATIONS.md`, but the issue does not select one.

Terms such as homotopy pullback, classifying fiber, and truncation depend on the chosen model.

The strict `Cat` test model is meaningful. It does not define the claimed higher foundation.

### Framed modules

The catalogue quotes the authored definition as a surjection

[ F_R(S)\twoheadrightarrow M. ]

It later replaces this with an arbitrary complex

[ F_k\to\cdots\to F_1\to M, ]

with projective positive terms and no surjectivity at (M).

The latter is a valid category. It is not the cited category of framed modules.

This requires a mathematical choice. It cannot be resolved by calling one construction a refinement of the other.

### Genera

- Searched: the catalogue declarations and promoted issue #34 comment.
- Found: `Genera` uses (G(\mathbb A_f))-orbits without fixing the global field.
- Found: the quadratic space (V), lattice class, and algebraic group (G) remain variable.
- Conclusion: `Genera` does not yet denote one category.
- Confidence: High.
- Gaps: A fixed-((K,V,G)) formulation could repair it.

The claimed functor

[ \operatorname{gen}_G:\operatorname{Lattices}(R)\longrightarrow\operatorname{Genera} ]

is therefore not defined.

The statement that discriminant fibers are genera also needs exact hypotheses. It is not part of the comma-category definition.

### Fans

Issue #37 defines individual cones and several predicates. It does not define the category of fans.

The missing definition must state:

- the ambient lattice;
- the family of cones;
- closure under faces;
- the intersection condition;
- the chosen morphisms of fans.

Without this, issue [#24](https://github.com/dzackgarza/lean-categories/issues/24) cannot define its fan-to-toric-scheme functor.

### Wythoff coarsening

Issue #24 admits that “Wythoff coarsening” has no pinned standard referent.

Therefore no functor has yet been defined under that name.

### Gluing

Issue [#26](https://github.com/dzackgarza/lean-categories/issues/26) explicitly leaves its source and target categories unstated.

The anti-isometry construction is clear:

[ \operatorname{Isom}(A,B^{(-1)}). ]

The proposed gluing functor is not yet defined.

### Stacks, deformation theory, and KSBA

- Searched: issue [#39](https://github.com/dzackgarza/lean-categories/issues/39).
- Found: many entries remain “interfaces,” “language,” or “general stability data.”
- Conclusion: the planned algebraic-stack and KSBA categories are not closed definitions.
- Confidence: High.
- Gaps: Mathlib’s current stack formalization may constrain the available version.

The following remain undefined:

- the category of algebraic spaces;
- the selected category of algebraic stacks;
- the deformation groupoid;
- the general stable-pair category;
- the exact category carrying discrepancies;
- the category containing dlt contractions.

The discrepancy equation is useful. It does not define the surrounding category by itself.

### Period maps and compactifications

Issue [#40](https://github.com/dzackgarza/lean-categories/issues/40) gives a recognizable set-level Type-IV domain.

The following remain incomplete:

- the source category of the period map;
- the symmetric space (G/K), because (G) and (K) are not fixed;
- the arithmetic quotient stack, pending #39;
- the Baily–Borel compactification;
- the semitoroidal category and its morphisms.

A set with named boundary strata is not the Baily–Borel compactification.

The Proj construction and the boundary description can be related by a theorem. They are not interchangeable definitions.

## Functoriality drift

### Discriminant functors

The promoted [#33 comment](https://github.com/dzackgarza/lean-categories/issues/33#issuecomment-5215686426) calls the adjoint maps a natural transformation.

They are not natural on all form-preserving maps.

For (f:L\to L'), the relation is

[ f^*\beta_{L'}f=\beta_L. ]

The later vault plan and issue #34 correctly restrict discriminant functors to isometry cores.

GitHub is declared authoritative. Its promoted comment is therefore stale.

### Class number

The catalogue declares

[ \operatorname{cl}:\operatorname{Genera}/!\cong\longrightarrow\operatorname{Cardinal}. ]

No map between cardinalities is induced by the stated genus morphisms.

Class number is an invariant on an appropriate groupoid or set of genera. The displayed functor is not defined.

### Refinement fibers

The catalogue writes

[ \operatorname{Ref}:\operatorname{BilinMod}(R,W)^\simeq\to\mathbf{Set}. ]

It does not decide whether the fiber of polarization is:

- a set of quadratic refinements;
- a groupoid of refinements;
- a homotopy fiber.

These are different mathematical objects.

### Reflection groups

The object assignment (L\mapsto W(L)) is clear.

The functor on the isometry core should use conjugation. The plan does not state this, but the repair is standard.

## Predicate drift

The catalogue places `root-generated` on general `BilinMod(R,W)`.

Reflections require a scalar-valued form and the relevant divisibility condition. The predicate belongs on a narrower lattice category.

The catalogue also calls ((r,a,\delta)) a complete invariant of the (p)-elementary subcategory.

That statement needs the precise Nikulin hypotheses. It is not true for every definite or arbitrary (p)-elementary lattice.

Issue #39 uses “slc” and ampleness inside `StablePair` without fixing the family category or equivalence notion.

Those words are standard predicates only after the ambient moduli problem is fixed.

## Overall disposition

The plans divide into three classes.

1. **Mathematically usable:** the core of #33, #34, #35, #36, and much of #41.
2. **Partly defined:** #22, #23, #25, #27, #37, #38, #54, and #55.
3. **Not yet definitions:** the higher part of #30, #24, #26, #39, and substantial parts of #40.

The catalogue plan cannot remain the approved mathematical authority.

Its first replacement must settle only this chain:

[ \operatorname{Bil}*{R,W} \longrightarrow \operatorname{SymBil}*{R,W} \longrightarrow \operatorname{Lat}_R \longrightarrow \operatorname{DiscBil},\operatorname{DiscQuad}. ]

That replacement must fix:

- the meaning of framing;
- integral versus perfect versus unimodular;
- evenness;
- metric dual versus module dual;
- the isometry cores;
- the two discriminant functors.

The later geometry plans depend on this chain. They should not proceed from the present catalogue.

## Later disposition (2026-08-11)

This is a historical audit of the plans and issue bodies inspected on 2026-08-09. Its verdict is not current status.

Current owners are issues #33 through #35 for frames, evenness, and discriminants, #54 and #56 for subobjects, and #23 for chambers. Commit `fb312de` added `EvenLatticeCat`. Commit `6d42343` added the fixed-rank frame categories, `CoordLatticeCat`, and `coordLatticeToIntegral`. Arbitrary-index frames, matrix realization, and the Gram comparison remain open under issue #33. Commit `f73ec81` removed advanced geometry placeholders. Issues #38, #39, and #40 own the prerequisite-first geometry program.

The legacy private catalogue plan is now a pointer. GitHub issue #4 and its children own direction and execution state.
