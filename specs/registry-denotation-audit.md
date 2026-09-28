# Registry denotation audit (`cc-p0-denotation-audit`)

Plan node: [`cc-p0-denotation-audit`](computational-core-plan.md). Requirements:
[CC-TRUE and CC-FIB](computational-core.md#cc-true--every-semantic-notion-is-standard-mathematics-from-step-0).
Revision audited: `eb00e55` (plus the documentation commit `07b4895`). Sources read:
`LeanCategories/Catalogue/{Syntax,Realization,Interpretation}.lean`,
`Catalogue/Registry/{Entry,Extension}.lean`,
`CategoryTheory/OneCat/{Classifier,CategoricalPullback}.lean`, every
`normalized_registry .categoryFamily` registration, and FOUNDATIONS §§5, 13, 15, 19.

Verdicts:

- **exact** — the Lean datum denotes the stated mathematics, and registration checks it;
- **exact, unchecked** — the intended denotation is standard, but registration does not force it;
- **wrong object** — the datum denotes standard mathematics, but not the object FOUNDATIONS
  defines;
- **no denotation** — no precise mathematical object is stated.

## 1. Entry kinds and syntax constructors

| Kind / constructor | Denotation | Source | Verdict |
| --- | --- | --- | --- |
| `NamedCategoryEntry` | a category \(\mathcal C\in\mathfrak{Cat}\), with `realization` a witness that the expression evaluates to the declared `ObjCat` | FOUNDATIONS §1 | exact |
| `CategoryExpr.atom` | a named category | §1 | exact |
| `CategoryExpr.opaque`, `OpaqueCategoryEntry`, `StructuralPortEntry`, `FunctorExpr.opaquePort` | a category supplied only through chosen functors ("ports") out of it; the category's own construction is withheld | none stated | **no denotation** as a mathematical notion. "Opaque" is an engineering status, not mathematics. Each opaque entry must state which category it is (by citation) and each port which functor; the `reason : String` field records neither |
| `ClassifierEntry`, `Classifier C` (`OneCat/Classifier.lean`) | a morphism \(p:\mathcal E\to\mathcal C\) in \(\mathfrak{Cat}\), an object of \(\mathfrak{Cat}_{/\mathcal C}\) | FOUNDATIONS Def. 5.1; [BS07, §2.4] | exact (Def. 5.1 deliberately imposes no fibration condition) |
| `PropertyClassifier` | full and faithful \(p\) | FOUNDATIONS §6; [BS07, §2.4] | exact, unchecked in one respect: the docstring says repleteness is required "when available", but no field requires it, so the type admits non-replete full subcategories. Whether §6 requires repleteness was not re-read for this audit. |
| `StructureClassifier` | faithful \(p\) | §6; [BS07, §2.4] | exact |
| `CategoryExpr.classifierTotal`, `FunctorExpr.classifierForget` | the total category \(\mathcal E\) and the projection \(p\) | Def. 5.1 | exact |
| `CategoryExpr.refine`, `RefinementRealization`, `Classifier.reindex` | the reindexing \(F^{*}\mathcal E=\mathcal D\times_{\mathcal C}\mathcal E\) of a classifier along \(F:\mathcal D\to\mathcal C\), realized by Mathlib's `CategoricalPullback` (the 2-categorical pullback) | Def. 5.2 last paragraph; FOUNDATIONS §7 | exact for the pullback (registration requires `Classifier.reindex`). **Unchecked:** `baseToHost` is an arbitrary functor; `validateRefinementDeclarationRealization` does not require it to be the structural route from the base expression to the classifier's host. A refinement can therefore denote the pullback along the wrong functor. |
| `Reindexed` (the structure type) | a 2-commutative square | — | the type admits any square, not only a pullback; safe only because registration demands `Classifier.reindex`. |
| `FunctorEntry`, `FunctorExpr.atomic` | a functor between the realized endpoints | §1 | exact for endpoints. `FunctorRealization` records the endpoint realizations and the functor, but not the functor's *identity* as the declared one. Whether registration ties the realized functor to `declaration` is checked in `validateFunctorDeclarationRealization` (`Extension.lean`, l. 849), which this audit did not read in full. |
| `FunctorExpr.identity`, `FunctorExpr.comp` | identity and composition in \(\mathfrak{Cat}\); `evalFunctor` composes with `⋙` after checking the middle category by equality | §1 | exact. Composite evaluation fails (returns `none`) when the two middle `ObjCat`s are not *equal*; an equivalence between them is not used. That is correct for strict composition, and it is where CC-COHERE comparisons will be needed. |
| `NatTransExpr` (`identity`, `atomic`, `vcomp`, `hcomp`) | natural transformations with vertical and horizontal composition | Mathlib `NatTrans` | exact |
| `CategoryFamilyEntry`, `CategoryFamilyRealization`, `CategoryExpr.familyApp` | a pseudofunctor \(\mathrm{LocallyDiscrete}(P^{\mathrm{op}})\to\mathbf{Cat}\), and `familyApp` its value at a parameter | Mathlib `Pseudofunctor`; FOUNDATIONS §13.2 | the *type* is exact: a pseudofunctor out of \(P^{\mathrm{op}}\) is a contravariant family, whose Grothendieck construction is a cartesian fibration over \(P\). The entry does not name that fibration, and "parameterized family" is the only name it has. **See §2 for the families.** |
| `CategoryFamilySchema`, `ParameterExpr`, `ParameterSort`, `ParameterKindId` | the parameter category \(P\) and a symbolic presentation of its objects | — | **no denotation** beyond \(P\): the schema is a closed enumeration of six parameter *types*. Its five discrete schemas fix \(P\) to a discrete category (§2), so the schema, not the mathematics, chooses the base. |
| `CategoryFamilyTransportSemantics` (`restrictionOfScalars`, `discrete`) | a label of the transport's variance | — | a tag, not mathematics; the variance is already determined by the pseudofunctor. |

## 2. Registered families

Exactly one registered family names a nondiscrete base. The other eighteen are
`discreteFamilyTransport` over `Discrete P`, the pseudofunctor induced by a *function*
\(P\to\mathbf{Cat}\). Its Grothendieck construction is the coproduct
\(\coprod_{p\in P}\mathcal C_p\) over the discrete category on \(P\). That is honest
mathematics, but it forgets every morphism of the base. So wherever FOUNDATIONS defines
functoriality in the base, these entries denote the **wrong object**.

| Family | Schema, base \(P\) | Fibre | Registered denotation | FOUNDATIONS object | Verdict |
| --- | --- | --- | --- | --- | --- |
| `modules` | `ring`: \(\mathbf{Ring}\) | \(R\text{-}\mathbf{Mod}\) | Mathlib `RingCat.moduleCatRestrictScalarsPseudofunctor`; its Grothendieck construction is the cartesian fibration \(\int_R R\text{-}\mathbf{Mod}\to\mathbf{Ring}\) | §13.2, restriction-of-scalars variance | **exact** |
| `bilinModule` | `commRingModule`: discrete on \(\{(R,W)\}\) | \(\mathbf{Bil}_{R,W}\) | \(\coprod_{(R,W)}\mathbf{Bil}_{R,W}\) | §15.2 fibres, with change of values \(u_*\) (§15.5) and base change \(S\otimes_R-\) (§15.6) | **wrong object**: both transports of §15.5–15.6 are absent |
| `quadModule` | as above | \(\mathbf{Quad}_{R,W}\) | coproduct | §15.4–15.6 | **wrong object**, as above |
| `bilWForm` | `commRing`: discrete on \(\{R\}\) | `BilWFormCat R` | coproduct over rings | §15 with a varying value module (fibre not read in full) | **wrong object** (no base change); fibre's exact definition to be confirmed |
| `quadWForm` | `commRing` | `QuadWFormCat R` | coproduct | §15 | **wrong object**, as above |
| `lattice`, `finiteProjectiveLattice`, `finiteFreeLattice` | `commRingModule` | lattices over \(R\) with values in \(W\) | coproduct | §19.2 (\(R\) Dedekind, values in \(R\)); valued generalizations in the lattice source files | **wrong object**, and **open base**: which ring maps preserve the lattice conditions (finite projectivity is preserved by extension of scalars; nondegeneracy over the fraction field needs \(K\to L\), so injective maps of domains) is a mathematical choice not yet made |
| `integralLattice`, `evenLattice` | `commRing` | \(\mathbf{Lat}\) variants | coproduct | §19.5: even lattices are *reindexings of the evenness classifier along* \(\mathbf{Lat}_{\mathbb Z}\to\mathbf{SymBil}_{\mathbb Z,\mathbb Z}\) | **wrong kind**: FOUNDATIONS makes even lattices a classifier refinement over \(\mathbb Z\), not a family over all commutative rings |
| `unimodularLattice`, `fractionFieldPerfectFiniteProjectiveLattice` | `domain`: discrete on \(\{(R,\ \mathrm{IsDomain}\ R)\}\) | lattice variants | coproduct over domains | §19.1–19.5 require a Dedekind domain; unimodularity is §19.5's perfectness classifier | **wrong base** (domain, not Dedekind) and **wrong kind** for unimodular (a refinement, per §19.5) |
| `coordLattice` | `commRingNat`: discrete on \(\{(R,n)\}\) | coordinatized lattices | coproduct | §21 (Gram descriptions) | **wrong object** if §21 defines base change (not read in full) |
| `genFrame`, `basisFrame` | `commRingNat` | \(\operatorname{GenFrame}_n(R)\), \(\operatorname{BasisFrame}_n(R)\) | coproduct | §13.5: loci in the comma category \((R^n\downarrow R\text{-}\mathbf{Mod})\). Extension of scalars preserves surjections (right exactness) and isomorphisms, so both vary covariantly in \(R\) | **wrong object**: the cocartesian transport exists and is absent. Discreteness in \(n\) is correct: a map \(R^n\to R^m\) does not carry frames to frames |
| `coord` | `commRingNat` | \(\operatorname{Coord}_n(R)\) | coproduct | §13.6 | **wrong object**, as for frames |
| `genFrameIndexed`, `basisFrameIndexed`, `coordIndexed` | `commRingIndexType`: discrete on \(\{(R,I)\}\), \(I\) a type | arbitrary-index versions | coproduct | §13.5–13.6 with index set \(I\) | **wrong object** in \(R\), as above. The index is a *type*, taken up to equality; the mathematically meaningful base is the groupoid of sets and bijections (a bijection \(I\cong J\) transports frames), so equality is also too coarse in \(I\) |

## 3. Findings

1. **One family out of nineteen names the fibration FOUNDATIONS defines.** `modules` is
   exact. The other eighteen are coproducts over a discrete set of parameters and cannot
   express change of rings, change of value module, or reindexing of an index set. By
   CC-FIB, "the lattices over \(R\) with values in \(W\)" must be the fibre of a stated
   fibration, and at present it is a component of a coproduct.
2. **The schema chooses the base, not the mathematics.** `CategoryFamilySchema` is a closed
   enumeration of parameter types, five of them wrapped in `Discrete`. A family cannot
   declare its correct base (e.g. the total module category with its morphisms) without
   adding a schema case.
3. **Two families are refinements registered as families.** FOUNDATIONS §19.5 defines even
   and unimodular lattices as reindexings of classifiers. As families over all commutative
   rings (`evenLattice`) or domains (`unimodularLattice`), they denote a different object.
4. **The lattice base is weaker than FOUNDATIONS.** `domain` requires `IsDomain`; §19.1
   requires a Dedekind domain.
5. **Refinement `baseToHost` is unchecked** (§1). A refinement's pullback can be taken along
   a functor other than the structural route.
6. **Opaque categories and ports have no denotation.** They must cite the category and
   functors they stand for, or be removed from the semantic catalogue.
7. **Property classifiers do not require repleteness.**

## 4. Decisions needed before `cc-fib` changes code

These are mathematical choices, not engineering ones; the sources state the transports but
not which one the registry should present.

- **Q1. Forms.** The base for \(\mathbf{Bil}_{R,W}\) and \(\mathbf{Quad}_{R,W}\): the
  proposal is the total module category over \(\mathbf{CommRing}\) with morphisms
  \((\varphi:R\to S,\ u:S\otimes_R W\to W')\), with transport \(u_*\circ(S\otimes_R-)\). By
  §15.5–15.6 that is a covariant pseudofunctor, hence a *cocartesian* fibration of forms.
  Confirm, or choose restriction of scalars (and which value module) instead.
- **Q2. Lattices.** Which morphisms of the base preserve the lattice conditions: all ring
  maps (then lattices are not closed under base change), injective maps of Dedekind
  domains, or only the core (isomorphisms of the base)?
- **Q3. Even and unimodular lattices.** Replace the two family entries by classifier
  refinements as §19.5 states, or retain families with a stated reason.
- **Q4. Index sets.** For the arbitrary-index frames, take the base to be the groupoid of
  types and equivalences (so bijections transport frames), or keep a discrete base with a
  stated reason.

Findings 5–7 need no decision; they become children of `cc-fib` and `cc-constructors`.

## 5. Coverage

Read in full: the files listed at the top, and every family registration. Not read in full:
`validateFunctorDeclarationRealization` and the other validators of `Extension.lean`
beyond the refinement validator; the fibre definitions of `BilWFormCat`, `QuadWFormCat`
and `CoordLatticeCat`; FOUNDATIONS §§17, 21, 83–86. Conclusions about those are marked in
the tables. Confidence in §2's structural finding (discrete versus nondiscrete bases) is
high: it is read directly from each registration's `P := Discrete …` and
`discreteFamilyTransport`.
