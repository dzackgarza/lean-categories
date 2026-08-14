# Active mathematical lexicon

This file orders the lexicon required by current repository work.

The linked textbook catalogues own standard term names and source locations. A catalogue
checkbox means: route every definition in the named chapters through Mathlib, this
repository, or another formalization, then expose the required route through the
`LeanCategories` catalogue and export surface. It does not request new definitions.

The vault plan `PLAN-MATHEMATICAL-LEXICON-ROUTING` owns exact package routes. Write new
theory only for the repository-specific or unmatched items stated below.

The vault plan `PLAN-LATER-THEOREM-PHASES` owns comparison, coherence, descent,
local-global, modularity, and formula theorems. These are later work. The active
milestones below establish the objects, categories, functors, and natural transformations
that those theorems use.

## 1. Foundation 0.1 and CAS DSL

Current work: `#50`, `#54`, `#55`, `#56`, and `#58`.

### Standard lexicon

- [ ] [Dummit and Foote, Preliminary Chapter and Chapters 1-12](.agents/references/dummit-and-foote-definition-catalogue.md)
  — sets, functions, groups, rings, ideals, factorization, polynomials, modules,
  vector spaces, tensor constructions, torsion modules, and matrices.
- [ ] [Atiyah and Macdonald, Chapters 1-3 and 5-10](.agents/references/atiyah-and-macdonald-definition-catalogue.md)
  — rings, ideals, modules, localization, integral dependence, valuations,
  finiteness conditions, graded objects, and completions.
- [ ] [Weibel, Appendix A](.agents/references/weibel-homological-algebra-definition-catalogue.md)
  — categories, functors, natural transformations, abelian categories, limits,
  colimits, and adjunctions.

### Repository-specific categorical surface

- [x] Categories of finite sets, countable sets, and enumerated sets
- [x] Categories of preorders, partial orders, linear orders, and lattices
- [x] Integral-domain refinement tower from fields to commutative rings
- [x] One-object category `{R}` and membership functor `{R} ⟶ C`
- [x] Categories of elements for element-level method attachment
- [ ] Fibred families of polynomial rings, power-series rings, matrices, vectors,
  ideals, modules, and algebras over commutative rings
- [ ] Prime-ideal and general-linear-group subfibrations
- [ ] Determinant, trace, characteristic polynomial, and derivative as natural
  transformations
- [ ] Cartesian lifts and base-change functors for each fibred family
- [ ] Category, functor, and natural-transformation expressions
- [ ] Evaluation of expressions in a selected realization
- [ ] Proof-carrying category and functor registry entries
- [ ] Stable exported identifiers for categories, functors, and standard objects
- [ ] Audit each file named `Functors`: define an honest functor or relocate it

## 2. Formed modules and lattice arithmetic

Current work: `#33` through `#36`, and milestone `#51`.

### Standard lexicon

- [ ] [Dummit and Foote, Chapters 10-12 and 16](.agents/references/dummit-and-foote-definition-catalogue.md)
  — modules, tensor products, exact sequences, bases, duals, determinants, torsion
  modules, discrete valuation rings, Dedekind domains, and fractional ideals.
- [ ] [Atiyah and Macdonald, Chapters 2-3, 5, and 9-10](.agents/references/atiyah-and-macdonald-definition-catalogue.md)
  — module finiteness conditions, localization, valuations, Dedekind domains,
  fractional ideals, filtrations, graded objects, and completions.

### Formed-module categories and functors

- [x] Categories of fixed-value and variable-value bilinear modules
- [x] Categories of fixed-value and variable-value quadratic modules
- [x] Carrier-module and value-module functors
- [x] Fixed-value fibers and change-of-value functors
- [x] Scalar-extension functors for bilinear and quadratic modules
- [x] Projective, finite-projective, free, finite-free, torsion-free, and finite-torsion
  formed-module subcategories
- [x] Left radical, right radical, adjoint map, defect module, nondegeneracy, and
  perfectness
- [x] Bilinear and quadratic forms on `Frac(R)/R` and `QQ/ZZ`

### Frames and presentations

- [ ] `GenFrame_n(R)`, `BasisFrame_n(R)`, and `Coord_n(R)`
- [ ] Framed, coordinatized, and presented module categories
- [ ] Framed and coordinatized bilinear and quadratic module categories
- [ ] Equivalence relation on matrices presenting the same module map
- [ ] Gram-matrix and quadratic Gram-data functors
- [ ] Change-of-frame and presentation-comparison functors

### Lattice categories and invariants

- [ ] Free, finite-free, finite-projective, generically nondegenerate, even,
  unimodular, definite, and indefinite lattice subcategories
- [ ] Algebraic dual, metric dual, and ideal dual
- [ ] Pairing map `L^{#I} → Hom_R(L,I)`
- [ ] Discriminant module `A_L = L^#/L` with its bilinear and quadratic forms
- [ ] Determinant, signed discriminant, level, scale, norm, and parity
- [ ] Exponent, elementary-divisor data, and `p`-elementary discriminant data
- [ ] Orthogonal group `O(L) = Aut(L)` in the lattice category
- [ ] Reflection, root, Weyl group, and `W(L) ⊆ O(L)`
- [ ] Local lattice, genus, genus class, class number, mass, representation number,
  and theta series
- [ ] Adele ring `𝔸_R`, integral finite adeles, diagonal map, and adelic scalar
  extension for a general number ring `R`

## 3. Affine algebra, varieties, and schemes

Current work: `#22`, `#38`, and the scheme part of `#56`.

### Standard lexicon

- [ ] [Atiyah and Macdonald, Chapters 1-11](.agents/references/atiyah-and-macdonald-definition-catalogue.md)
  — route the complete commutative-algebra catalogue.
- [ ] [Dummit and Foote, Chapters 15-16](.agents/references/dummit-and-foote-definition-catalogue.md)
  — affine algebraic sets, varieties, localization, spectra, local rings, discrete
  valuation rings, and Dedekind domains.
- [ ] [Shafarevich, all catalogued chapters](.agents/references/shafarevich-varieties-definition-catalogue.md)
  — route the complete varieties catalogue.
- [ ] [Hartshorne, Chapters I-III](.agents/references/hartshorne-schemes-definition-catalogue.md)
  — varieties, schemes, morphisms, divisors, differentials, and cohomology.

### Repository-specific geometric surface

- [ ] Schemes over a base as a standard slice or structured-arrow category
- [ ] Base-change functors and fibers of scheme morphisms
- [ ] Full replete subcategories of varieties, curves, surfaces, and algebraic surfaces
- [ ] Subcategories cut out by required scheme-morphism properties
- [ ] Quasi-coherent and coherent sheaf categories
- [ ] Divisor, dualizing, and reflexive-sheaf categories
- [ ] Relative spectrum of a quasi-coherent algebra
- [ ] Relative Proj of a graded quasi-coherent algebra

## 4. Homological algebra for geometry and topology

Current work: `#38`, `#39`, and `#40`.

### Standard lexicon

- [ ] [Weibel, Chapters 1-5 and Appendix A](.agents/references/weibel-homological-algebra-definition-catalogue.md)
  — chain complexes, homology, derived functors, `Tor`, `Ext`, spectral sequences,
  derived categories, and categorical foundations.
- [ ] [Dummit and Foote, Chapter 17](.agents/references/dummit-and-foote-definition-catalogue.md)
  — chain complexes, resolutions, `Ext`, `Tor`, and group cohomology.

### Repository-specific homological surface

- [ ] Categories of chain and cochain complexes over each required abelian category
- [ ] Homotopy and derived categories with their localization functors
- [ ] Derived tensor product and derived internal Hom
- [ ] Sheaf cohomology and derived pushforward
- [ ] Hypercohomology and spectral-sequence functors needed by geometry

## 5. Later textbook lexica

These catalogues follow the current foundation, lattice, and scheme work.

- [ ] [Folland, all catalogued chapters](.agents/references/folland-real-analysis-definition-catalogue.md)
  — real analysis and measure theory.
- [ ] [Ahlfors, all catalogued chapters](.agents/references/ahlfors-complex-analysis-definition-catalogue.md)
  — complex analysis and Riemann surfaces.
- [ ] [Hatcher, all catalogued chapters](.agents/references/hatcher-algebraic-topology-definition-catalogue.md)
  — algebraic topology.
- [ ] [Whitehead, all catalogued chapters](.agents/references/whitehead-homotopy-theory-definition-catalogue.md)
  — homotopy theory.
- [ ] [Apostol, all catalogued chapters](.agents/references/apostol-analytic-number-theory-definition-catalogue.md)
  — analytic number theory.

## 6. Unmatched foundational constructions

Run the full reuse search again before new authorship.

### Divided powers and quadratic maps

- [ ] Free divided-power algebra functor `Γ_R : ModuleCat R ⥤ CommAlgCat R`
- [ ] Degree-`n` divided power `Γ_R^n(M)`
- [ ] Grading `Γ_R(M) = ⨁_n Γ_R^n(M)`

### Variable-value quadratic formed modules

- [ ] Category of variable-value quadratic `R`-modules
- [ ] Carrier-module functor and value-module functor
- [ ] Fixed-value fiber over an `R`-module `W`
- [ ] Change-of-value functor
- [ ] Scalar-extension functor
- [ ] Quadratic defect module

### Higher classifier foundations

- [ ] Homotopy pullback in the selected higher-categorical model
- [ ] Classifier as a 1-morphism in the selected higher-categorical model
- [ ] Lift, fiber, reindexing, and truncation of classifier fibers
- [ ] Comparison 2-cell for classifier reindexing

## Later theorem plans

- `PLAN-LATER-THEOREM-PHASES` — comparison, coherence, descent, and base-change
  theorems arising from this lexicon
- `TASK-CANONICAL-FORMED-CATEGORY-COMPARISONS` — comparisons among formed-module
  presentations
- `TASK-IDEAL-DUAL-DISCRIMINANT-COMPARISON` — ideal-dual and discriminant comparisons
- `PHASE-LOCAL-GENUS-FOUNDATION` — local and double-coset presentations of genus
- `PLAN-SIEGEL-MASS-FORMULA` — the mass formula
- `PLAN-THETA-SERIES-MODULARITY` — modularity of lattice theta series
