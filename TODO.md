# Active mathematical lexicon

This file orders the mathematical terms that must be available through the
`LeanCategories` catalogue and export surface.

A checkbox does not request a new definition. Close an item when it has an exact route
to Mathlib, this repository, or another formalization, and when the repository exposes
that route to its current consumers. Write new theory only for the unmatched residue.

The vault plan `PLAN-MATHEMATICAL-LEXICON-ROUTING` owns package and source routing.
The linked catalogues give standard textbook locations for the terms below.

## 1. Foundation 0.1 and the CAS DSL

This section serves issues `#50`, `#54`, `#55`, `#56`, and `#58`.

### Sets, functions, relations, and orders

Source: [Folland real analysis catalogue](.agents/references/folland-real-analysis-definition-catalogue.md)
and [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md).

- [ ] Set, subset, and set membership
- [ ] Function, map, image, preimage, and function composition
- [ ] Relation and equivalence relation
- [ ] Equivalence class, partition, and quotient set
- [ ] Cartesian product, indexed product, and indexed coproduct
- [ ] Finite set, countable set, and cardinality
- [ ] Sequence and family indexed by a type
- [ ] Preorder, partial order, and linear order
- [ ] Order-preserving map and order isomorphism
- [ ] Upper bound, lower bound, supremum, and infimum
- [ ] Lattice, distributive lattice, complemented lattice, and Boolean algebra
- [ ] Category of sets and full subcategories of finite and countable sets
- [ ] Category of enumerated sets and its forgetful functor to countable sets
- [ ] Categories of preorders, partial orders, linear orders, and lattices
- [ ] Forgetful functors in the order-category tower
- [ ] Subobject category `Sub(X)` and its Boolean operations where defined

### Groups, rings, and the integral-domain tower

Source: [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md).

- [ ] Binary operation, magma, semigroup, monoid, and group
- [ ] Abelian group, cyclic group, finite group, and finitely generated group
- [ ] Group homomorphism, group isomorphism, and group automorphism
- [ ] Subgroup, normal subgroup, quotient group, and direct product
- [ ] Group action, orbit, stabilizer, and permutation representation
- [ ] Ring, ring with identity, commutative ring, and division ring
- [ ] Ring homomorphism, ring isomorphism, subring, and quotient ring
- [ ] Unit, zero divisor, nilpotent element, and idempotent element
- [ ] Integral domain and field
- [ ] Ideal, principal ideal, prime ideal, and maximal ideal
- [ ] Sum, product, intersection, radical, map, and comap of ideals
- [ ] Irreducible element, prime element, and associated elements
- [ ] Euclidean domain, principal ideal domain, and unique factorization domain
- [ ] Polynomial ring, multivariable polynomial ring, and polynomial evaluation
- [ ] Degree, leading term, monic polynomial, content, and primitive polynomial
- [ ] Matrix ring, group ring, monoid algebra, and Laurent polynomial ring
- [ ] Formal power series ring and Laurent series ring
- [ ] Categories of groups, abelian groups, rings, commutative rings, and fields
- [ ] Categories of integral domains, UFDs, PIDs, and Euclidean domains
- [ ] Structural functors `Fields ⟶ EuclideanDomains ⟶ PIDs ⟶ UFDs`
- [ ] Structural functor `UFDs ⟶ IntegralDomains ⟶ CommutativeRings`
- [ ] One-object full subcategory `{R}` for a named ring `R`
- [ ] Membership functor `{R} ⟶ C` for each certified ring structure on `R`
- [ ] Category of elements of the underlying-set functor on a ring category

### Modules, vector spaces, and algebras

Source: [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md)
and [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md).

- [ ] Left module, right module, and bimodule
- [ ] Linear map, linear equivalence, submodule, and quotient module
- [ ] Generated submodule, generating set, and finitely generated module
- [ ] Direct sum, direct product, kernel, image, cokernel, and exact sequence
- [ ] Free module, basis, rank, and invariant basis number property
- [ ] Projective module, injective module, flat module, and finitely presented module
- [ ] Torsion element, torsion submodule, torsion module, and torsion-free module
- [ ] Annihilator of an element and annihilator of a module
- [ ] Tensor product and tensor-Hom adjunction
- [ ] Algebra over a commutative ring and algebra homomorphism
- [ ] Tensor algebra, symmetric algebra, and exterior algebra
- [ ] Graded module, graded ring, graded algebra, and homogeneous component
- [ ] Chain complex and cochain complex of modules
- [ ] Restriction of scalars and extension of scalars
- [ ] Category `ModuleCat R` and category `AlgCat R`
- [ ] Full subcategories of free, projective, flat, torsion-free, and finite modules
- [ ] Forgetful functors from module-property subcategories to `ModuleCat R`
- [ ] Fibred category of modules over commutative rings
- [ ] Fibred category of algebras over commutative rings

### Polynomial, series, matrix, ideal, and module families

Source: [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md)
and [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md).

- [ ] Polynomial-ring family over commutative rings
- [ ] Multivariable-polynomial-ring family over commutative rings
- [ ] Power-series-ring family over commutative rings
- [ ] Matrix family `Mat_{m×n} → CRing`
- [ ] Vector family `Vec_n → CRing`
- [ ] General-linear-group subfamily `GL_n → CRing`
- [ ] Ideal family and prime-ideal subfamily over commutative rings
- [ ] Module family and module-property subfamilies over commutative rings
- [ ] Framed-module family and presented-module family
- [ ] Matrix application as a fiberwise operation
- [ ] Determinant and trace as natural transformations
- [ ] Characteristic polynomial as a polynomial-valued natural transformation
- [ ] Polynomial derivative as a natural transformation
- [ ] Grothendieck construction for each required family
- [ ] Cartesian lift and base-change functor for each required family
- [ ] Comparison between concrete subobjects and categorical subobjects
- [ ] Comparison between matrices and maps of framed free modules

### Categories, functors, and the registry surface

Current consumers: issues `#30`, `#31`, `#41`, `#49`, `#54`, `#56`, and `#58`.

- [ ] Category, object, morphism, identity, and composition
- [ ] Opposite category, product category, and functor category
- [ ] Functor, natural transformation, and natural isomorphism
- [ ] Full subcategory, replete subcategory, and essential image
- [ ] Slice category, coslice category, comma category, and category of elements
- [ ] Limit, colimit, pullback, pushout, equalizer, and coequalizer
- [ ] Adjoint functors, unit, counit, monad, and comonad
- [ ] Reflective subcategory and localization
- [ ] Grothendieck construction, fiber, cartesian morphism, and cartesian functor
- [ ] Category expression, functor expression, and natural-transformation expression
- [ ] Evaluation of expressions in a selected realization
- [ ] Registry entry for a category with its realization equivalence
- [ ] Registry entry for a functor with its realization equivalence
- [ ] Stable exported identifiers for categories, functors, and standard objects
- [ ] Exact audit of every file named `Functors`: honest functor or relocation

## 2. Formed modules and lattice arithmetic

This section serves issues `#33` through `#36` and milestone `#51`.

### Formed modules

Sources: [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md)
and [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md).

- [ ] Bilinear map, bilinear form, and symmetric bilinear form
- [ ] Alternating bilinear form and skew-symmetric bilinear form
- [ ] Quadratic map, quadratic form, and associated polar form
- [ ] Left radical, right radical, and radical of a symmetric form
- [ ] Adjoint map `M → Hom_R(M,W)`
- [ ] Radical-free, nondegenerate, perfect, and unimodular form
- [ ] Defect module of a formed module
- [ ] Category of `W`-valued bilinear `R`-modules
- [ ] Category of `W`-valued quadratic `R`-modules
- [ ] Carrier-module and value-module functors
- [ ] Fixed-value fiber over an `R`-module `W`
- [ ] Change-of-value functor
- [ ] Scalar-extension functor for bilinear formed modules
- [ ] Scalar-extension functor for quadratic formed modules
- [ ] Projective, finite-projective, free, finite-free, and torsion-free subcategories
- [ ] Forgetful functors from formed-module subcategories to module subcategories
- [ ] Finite torsion bilinear form and finite torsion quadratic form
- [ ] Bilinear and quadratic forms on `Frac(R)/R` and `QQ/ZZ`

### Frames, coordinates, and presentations

- [ ] Generating frame and category `GenFrame_n(R)`
- [ ] Basis frame and category `BasisFrame_n(R)`
- [ ] Coordinatized module and category `Coord_n(R)`
- [ ] Framed bilinear and quadratic formed modules
- [ ] Coordinatized bilinear and quadratic formed modules
- [ ] Presented module and relation module
- [ ] Matrix presentation of a module homomorphism
- [ ] Descent condition for a matrix between generated modules
- [ ] Equivalence relation on matrices presenting the same module map
- [ ] Gram-matrix functor on coordinatized bilinear forms
- [ ] Quadratic Gram-data functor on coordinatized quadratic forms
- [ ] Change-of-frame functor
- [ ] Comparison functor from framed objects to matrix presentations

### Lattices, duals, and discriminant data

Sources: [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md)
and [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md).

- [ ] Dedekind domain, fractional ideal, and ideal class group
- [ ] Integral lattice over a Dedekind domain
- [ ] Free, finite-free, projective, and finite-projective lattice
- [ ] Generically nondegenerate lattice
- [ ] Even, odd, unimodular, positive-definite, negative-definite, and indefinite lattice
- [ ] Inclusion and forgetful functors for lattice subcategories
- [ ] Algebraic dual, metric dual, and ideal dual lattice
- [ ] Pairing map `L^{#I} → Hom_R(L,I)`
- [ ] Discriminant module `A_L = L^#/L`
- [ ] Discriminant bilinear form and discriminant quadratic form
- [ ] Determinant, signed discriminant, level, scale, norm, and parity
- [ ] Exponent and elementary-divisor data of the discriminant module
- [ ] `p`-elementary lattice and `p`-primary discriminant form
- [ ] Orthogonal group `O(L) = Aut(L)` in the lattice category
- [ ] Comparison with form-preserving linear automorphisms
- [ ] Reflection, root, Weyl group, and reflection subgroup `W(L) ⊆ O(L)`
- [ ] Root as a vector whose reflection preserves the integral lattice
- [ ] Local lattice, genus, genus class, class number, and mass
- [ ] Representation number and theta series

### Number rings and adeles

Source: [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md).

- [ ] Number ring and its fractional ideals
- [ ] Localization and completion of a number ring at a prime
- [ ] Local field and valuation ring attached to a prime
- [ ] Adele ring `𝔸_R` of a number ring `R`
- [ ] Finite adele ring and integral finite-adele subring
- [ ] Diagonal map `R → 𝔸_R`
- [ ] Adelic scalar extension of an integral lattice
- [ ] Localizations of a lattice and their restricted product

## 3. Affine algebra, varieties, and schemes

This section serves issues `#22`, `#38`, and the scheme part of `#56`.

### Commutative algebra for geometry

Source: [Atiyah and Macdonald commutative algebra catalogue](.agents/references/atiyah-and-macdonald-definition-catalogue.md).

- [ ] Spectrum of prime ideals and Zariski topology
- [ ] Localization of rings and modules
- [ ] Localization at an element and at a prime ideal
- [ ] Fraction ring and total quotient ring
- [ ] Support of a module
- [ ] Local ring, maximal ideal, residue field, and local homomorphism
- [ ] Primary ideal, primary submodule, and associated prime
- [ ] Integral element, integral extension, and integral closure
- [ ] Valuation, valuation ring, and discrete valuation ring
- [ ] Noetherian ring, Noetherian module, Artinian ring, and Artinian module
- [ ] Finite type and finite presentation of an algebra
- [ ] Adic topology and adic completion of a ring or module
- [ ] Associated graded ring and associated graded module
- [ ] Krull dimension, height of a prime, and dimension of a module
- [ ] Regular local ring and system of parameters
- [ ] Kähler differentials and universal derivation

### Affine algebraic sets and varieties

Source: [Shafarevich varieties catalogue](.agents/references/shafarevich-varieties-definition-catalogue.md)
and [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md).

- [ ] Affine space, algebraic set, irreducible algebraic set, and affine variety
- [ ] Vanishing ideal and coordinate ring
- [ ] Zariski-closed set, Zariski-open set, and distinguished open set
- [ ] Regular function, rational function, and function field
- [ ] Regular map, rational map, and birational map
- [ ] Quasi-affine variety and projective variety
- [ ] Projective space, homogeneous ideal, and projective coordinate ring
- [ ] Dimension, codimension, and local dimension of a variety
- [ ] Nonsingular point, singular point, tangent space, and tangent cone
- [ ] Divisor, principal divisor, Cartier divisor, and Weil divisor
- [ ] Complete linear system and divisor class group

### Schemes and morphisms

Source: [Hartshorne schemes catalogue](.agents/references/hartshorne-schemes-definition-catalogue.md).

- [ ] Presheaf, sheaf, sheafification, restriction, and stalk
- [ ] Ringed space, locally ringed space, and morphism of locally ringed spaces
- [ ] Structure sheaf on `Spec R` and affine scheme
- [ ] Scheme, open subscheme, closed subscheme, and reduced subscheme
- [ ] Morphism of schemes and scheme over a base
- [ ] Fiber product, base change, and fiber of a scheme morphism
- [ ] Open immersion, closed immersion, monomorphism, and diagonal morphism
- [ ] Quasi-compact and quasi-separated morphism
- [ ] Locally finite type, finite type, and finite morphism
- [ ] Separated, proper, flat, smooth, etale, and unramified morphism
- [ ] Quasi-coherent sheaf, coherent sheaf, and locally free sheaf
- [ ] Pullback, pushforward, tensor product, and internal Hom of sheaves
- [ ] Relative spectrum of a quasi-coherent algebra
- [ ] Relative Proj of a graded quasi-coherent algebra
- [ ] Invertible sheaf, sheaf of ideals, and effective Cartier divisor
- [ ] Dimension of a scheme, curve, surface, and algebraic surface
- [ ] Full replete subcategories of varieties, curves, and surfaces

## 4. Homological algebra for geometry and topology

This section serves issues `#38`, `#39`, and `#40`.

Source: [Weibel homological algebra catalogue](.agents/references/weibel-homological-algebra-definition-catalogue.md)
and [Dummit and Foote abstract algebra catalogue](.agents/references/dummit-and-foote-definition-catalogue.md).

- [ ] Additive category, preadditive category, and abelian category
- [ ] Zero object, biproduct, kernel, cokernel, image, and coimage
- [ ] Chain complex, cochain complex, differential, cycle, and boundary
- [ ] Chain map, chain homotopy, quasi-isomorphism, and homotopy equivalence
- [ ] Homology object and cohomology object
- [ ] Exact complex, exact sequence, and short exact sequence
- [ ] Projective object, injective object, and flat object
- [ ] Projective resolution, injective resolution, and flat resolution
- [ ] Left-exact functor, right-exact functor, and exact functor
- [ ] Left-derived functor and right-derived functor
- [ ] `Tor`, `Ext`, and derived tensor product
- [ ] Homotopy category and derived category
- [ ] Shift functor, mapping cone, distinguished triangle, and triangulated category
- [ ] Double complex, total complex, filtration, and spectral sequence
- [ ] Exact couple and hypercohomology
- [ ] Sheaf cohomology and derived pushforward
- [ ] Group cohomology and group homology

## 5. Later lexica from the current textbook set

These terms follow the current foundation, lattice, and scheme work. Keep them routed now
so later research does not begin from isolated advanced declarations.

### Real analysis

Source: [Folland real analysis catalogue](.agents/references/folland-real-analysis-definition-catalogue.md).

- [ ] Metric space, complete metric space, compact set, and separable space
- [ ] Topological space, continuous map, product topology, and quotient topology
- [ ] Sigma-algebra, measurable space, measure, and outer measure
- [ ] Measurable function, simple function, integral, and almost-everywhere equality
- [ ] Product measure, signed measure, complex measure, and Radon-Nikodym derivative
- [ ] `L^p` space, normed space, Banach space, and Hilbert space
- [ ] Bounded linear map, dual space, weak topology, and weak-star topology
- [ ] Locally compact space, Radon measure, and regular Borel measure
- [ ] Distribution, Fourier transform, and convolution

### Complex analysis

Source: [Ahlfors complex analysis catalogue](.agents/references/ahlfors-complex-analysis-definition-catalogue.md).

- [ ] Complex derivative, holomorphic function, and analytic function
- [ ] Power series, radius of convergence, and analytic continuation
- [ ] Complex line integral, winding number, and primitive
- [ ] Zero, pole, isolated singularity, and residue
- [ ] Meromorphic function and divisor of a meromorphic function
- [ ] Conformal map, harmonic function, and subharmonic function
- [ ] Riemann surface, chart, atlas, and holomorphic map of Riemann surfaces

### Algebraic topology and homotopy theory

Source: [Hatcher algebraic topology catalogue](.agents/references/hatcher-algebraic-topology-definition-catalogue.md)
and [Whitehead homotopy theory catalogue](.agents/references/whitehead-homotopy-theory-definition-catalogue.md).

- [ ] Homotopy, homotopy equivalence, deformation retract, and contractible space
- [ ] CW complex, cell, skeleton, attaching map, and characteristic map
- [ ] Path, loop, fundamental group, and covering space
- [ ] Simplicial complex, singular complex, chain group, and boundary map
- [ ] Singular homology, relative homology, and cellular homology
- [ ] Cohomology, cup product, cohomology ring, and local coefficients
- [ ] Based space, suspension, loop space, smash product, and wedge sum
- [ ] Homotopy group, relative homotopy group, and weak homotopy equivalence
- [ ] Fibration, cofibration, fiber bundle, and lifting property
- [ ] Eilenberg-Mac Lane space, Postnikov system, and obstruction cocycle
- [ ] Spectrum, stable homotopy group, and generalized cohomology theory

### Analytic number theory

Source: [Apostol analytic number theory catalogue](.agents/references/apostol-analytic-number-theory-definition-catalogue.md).

- [ ] Arithmetic function, multiplicative function, and Dirichlet convolution
- [ ] Mobius function, Euler totient function, and von Mangoldt function
- [ ] Dirichlet character, primitive character, and conductor
- [ ] Quadratic residue, Legendre symbol, and Jacobi symbol
- [ ] Dirichlet series, Euler product, and abscissa of convergence
- [ ] Riemann zeta function, Hurwitz zeta function, and Dirichlet L-function
- [ ] Partition, partition function, and generating function

## 6. Unmatched foundational constructions

Run the full reuse search again before new authorship.

### Divided powers and quadratic maps

- [ ] Free divided-power algebra functor `Γ_R : ModuleCat R ⥤ CommAlgCat R`
- [ ] Degree-`n` divided power `Γ_R^n(M)`
- [ ] Grading `Γ_R(M) = ⨁_n Γ_R^n(M)`
- [ ] Natural comparison between quadratic maps and linear maps from `Γ_R^2(M)`

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
- [ ] Lift through a classifier
- [ ] Fiber of a classifier
- [ ] Reindexing of classifier fibers
- [ ] Truncation of a classifier fiber
- [ ] Comparison 2-cell for classifier reindexing
- [ ] Identity and composition coherence for classifier reindexing
