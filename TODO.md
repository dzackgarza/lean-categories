# Cleanup completion record

The consolidation is complete.

## Canonical mathematical owners

- [x] `BilinModuleCat R W` owns fixed-value bilinear forms.
- [x] `BilWFormCat R` owns forms with a variable value module.
- [x] Full subcategories own symmetric, skew-symmetric, and alternating forms.
- [x] `LatticeCat R W` owns projective modules with symmetric `W`-valued forms.
- [x] A lattice can have a radical and infinite rank.
- [x] `IntegralLatticeCat R` is the `R`-valued case.
- [x] Nondegeneracy is a separate predicate.

## Old lattice presentations

The old bundled type required a finite free carrier and an injective adjoint.
It described a strict subcategory of `IntegralLatticeCat ℤ`.

The old unbundled type fixed a finite free carrier before it selected a form.
It described the same extra conditions in one carrier fibre.

Neither old presentation remains. Thus, no comparison functor remains necessary.

The cleanup moved these proved constructions to the valued lattice owner:

- [x] form scaling and the opposite form;
- [x] isotropic vectors, roots, and divisibility ideals;
- [x] Gram matrices, determinants, and unimodularity;
- [x] orthogonal direct sums;
- [x] the integral hyperbolic plane;
- [x] root reflections and their isometry theorem; and
- [x] involutions with fixed and anti-fixed submodules.

The cleanup removed the obsolete bundled and unbundled trees.
It also removed their axiomatic or shallow downstream theories.

## Duals and discriminants

- [x] Ideal duals, metric duals, and module duals have different owners.
- [x] The formed metric dual requires a finite carrier.
- [x] It also requires a bijective rational adjoint.
- [x] It does not require nondegeneracy over the base ring.
- [x] The formed discriminant is a cokernel in `SymBilWFormCat`.
- [x] Its carrier map is the module quotient by the image of `L → L♯`.
- [x] The carrier sequence is exact through the formed-module forgetful map.
- [x] For a nondegenerate lattice, the sequence is
  `0 → rad(L) → L → L♯ → A(L) → 0`.
- [x] No lattice functor uses axiomatic identity or composition laws.

## Catalogue

- [x] The catalogue and mathematical categories use one `LeanCategories` tree.
- [x] Structural maps use indexed `FunctorExpr` values.
- [x] `StructuralMapExpr` and all its consumers are removed.
- [x] Each category registry row names a typed `CategoryRealization` proof.
- [x] Each functor registry row names a typed `FunctorRealization` proof.
- [x] Registration rejects rows without these proofs.
- [x] JSON export includes the proof declaration names.

## Workspace

- [x] The old `lean_lattices` repository was inspected.
- [x] It contained only a new-project template.
- [x] The template was sent to trash.

## Premature geometric sketches

- [x] Scheme targets were scavenged into issue #38.
- [x] Stack, log-pair, and KSBA targets were scavenged into issue #39.
- [x] Manifold, Hodge, and period targets were scavenged into issue #40.
- [x] The 33 placeholder source files were removed.
- [x] No axiom preserves a missing geometric construction.

## Verification

- [x] The canonical `LeanCategories` root builds.
- [x] The repository has one Lean library.
- [x] No old lattice import remains.
- [x] No `StructuralMapExpr` reference remains in Lean source.
- [x] No `sorry` or `admit` declaration remains.

# Missing prerequisite theory catalogue

The missing list is smaller at the bottom and much larger at the top.

I audited pinned Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997`.

This list covers roadmap #9, issues #22 and #38–#40, and all 33 removed geometry files.

“Partial” means that Mathlib has useful parts. It does not have the required assembled theory.

## Mathlib already supplies

These items are not missing:

- Schemes, scheme morphisms, pullbacks, fibers, and schemes over a base.
- Proper, separated, flat, smooth, étale, finite, and finite-type morphisms.
- Geometrically connected, reduced, irreducible, and integral morphisms.
- Zariski, étale, fppf, fpqc, and pro-étale sites.
- Sheaves, scheme modules, quasicoherent modules, and locally free modules.
- Absolute projective spectra and relative normalization.
- Groupoids, cartesian morphisms, fibered categories, and Grothendieck constructions.
- Descent data, prestacks, and the abstract stack condition.
- Topological, smooth, and complex manifold structures.
- Complex differentiable maps, which supply the basic holomorphic-map predicate.
- Basic singular homology and sheaf cohomology.
- Basic bicategories and early quasicategory theory.

Relevant sources include [Scheme.lean](/home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Scheme.lean), [Fibered.lean](/home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Fibered.lean), and [IsStack.lean](/home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Descent/IsStack.lean).

## 1. Scheme classes and dimensions

- **Missing:** The project’s exact definition of a variety.
- **Missing:** Full replete categories of varieties, curves, and surfaces.
- **Partial:** Global dimension and equidimensionality predicates for schemes.
- **Missing:** Relative dimension outside the existing smooth case.
- **Missing:** Scheme-level normality and regularity.
- **Missing:** Serre \(R_n\) and \(S_n\) conditions.
- **Missing:** Scheme-level Cohen–Macaulay and Gorenstein conditions.
- **Missing:** Seminormal and demi-normal schemes.
- **Missing:** Geometric versions of the new scheme properties.
- **Missing:** Algebraic surfaces as a controlled subcategory.
- **Missing:** Enriques surfaces and their defining invariants.
- **Missing:** Rational double points and ADE surface singularities.

Mathlib has local Krull-dimension tools. It does not assemble the required scheme subcategories.

## 2. Sheaves, divisors, and relative geometry

- **Missing:** Sheaves of \(\mathcal O_X\)-algebras.
- **Missing:** Quasicoherent sheaves of \(\mathcal O_X\)-algebras.
- **Missing:** Graded quasicoherent \(\mathcal O_X\)-algebras.
- **Missing:** General relative Spec and its adjunction.
- **Missing:** General relative Proj and its universal property.
- **Missing:** Projective morphisms.
- **Missing:** Ample and very ample invertible sheaves.
- **Partial:** Coherent sheaves on schemes.
- **Missing:** Scheme-level dual sheaves and internal Hom applications.
- **Missing:** Reflexive sheaves and reflexive powers.
- **Missing:** Base-change results for reflexive powers.
- **Missing:** Line bundles and the scheme Picard group.
- **Missing:** Cartier divisors.
- **Missing:** Weil divisors.
- **Missing:** Rational and real divisors.
- **Missing:** Principal divisors and linear equivalence.
- **Missing:** Divisor class groups.
- **Missing:** Pullback and pushforward of divisors.
- **Missing:** Intersection products and numerical equivalence.
- **Missing:** Nef, ample, big, and semiample divisor predicates.
- **Missing:** Divisor volume.
- **Missing:** Canonical sheaves and canonical divisors.
- **Missing:** Dualizing sheaves and dualizing complexes.
- **Missing:** Relative dualizing data.
- **Missing:** \(\mathbb Q\)-Cartier and \(\mathbb Q\)-Gorenstein conditions.
- **Partial:** Blowups. Mathlib has Rees algebras, but no scheme blowup.
- **Missing:** Quotient schemes and their universal properties.
- **Missing:** Cyclic covers.
- **Missing:** Index-one covers.
- **Missing:** Anticanonical models and quotients.
- **Missing:** Resolutions and minimal resolutions.
- **Missing:** Log resolutions.
- **Partial:** Hilbert polynomials. Mathlib only has a basic polynomial construction.
- **Missing:** Hilbert polynomials of polarized schemes and families.
- **Missing:** Positivity loci in families.

Issue #22 correctly owns the first relative-Spec and relative-Proj block.

## 3. Stacks and algebraic stacks

- **Partial:** A bundled theory of categories fibered in groupoids.
- **Partial:** Categories or bicategories of stacks, morphisms, and 2-morphisms.
- **Missing:** Algebraic spaces.
- **Partial:** Representable morphisms between stacks.
- **Missing:** Stack diagonals and their properties.
- **Missing:** Smooth, étale, and fppf atlases.
- **Missing:** Algebraic stacks.
- **Missing:** Deligne–Mumford stacks.
- **Missing:** Artin stacks.
- **Missing:** Properties of representable stack morphisms.
- **Missing:** Quotient stacks \([X/G]\).
- **Missing:** Coarse moduli spaces and their universal properties.
- **Missing:** Descent for divisors, pairs, and stable families.
- **Missing:** Stack-level pullbacks for these structured objects.

Mathlib has the abstract stack condition. It does not have algebraic spaces or algebraic stacks.

## 4. Deformation theory

- **Partial:** Kähler differentials and square-zero ring extensions.
- **Partial:** A presentation-based naive cotangent complex.
- **Missing:** The scheme cotangent complex.
- **Missing:** The stack cotangent complex.
- **Missing:** Deformation groupoids.
- **Missing:** First-order deformations of schemes and pairs.
- **Missing:** Tangent and obstruction spaces.
- **Missing:** Automorphisms of deformations.
- **Missing:** Base change for deformation data.
- **Missing:** Formal deformation problems for stable pairs.
- **Missing:** Algebraicity criteria for the resulting moduli problems.

The existing naive complex appears in [Cotangent/Basic.lean](/home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/RingTheory/Extension/Cotangent/Basic.lean).

## 5. Log pairs and KSBA theory

- **Missing:** Log pairs \((X,B)\) with actual divisor data.
- **Missing:** Effective boundaries with controlled coefficients.
- **Missing:** Divisorial valuations and their centers.
- **Missing:** Pullback formulas for \(K_X+B\).
- **Missing:** Discrepancies and log discrepancies.
- **Missing:** klt, plt, lc, dlt, and slc predicates.
- **Missing:** Normalization and conductor data for slc pairs.
- **Missing:** The different and adjunction for pairs.
- **Missing:** dlt boundaries and dlt modifications.
- **Missing:** dlt contractions.
- **Missing:** Stable pairs.
- **Missing:** Stable curves and semistable curves.
- **Missing:** Stable families of curves or pairs.
- **Missing:** Relative slc conditions.
- **Missing:** The family-level \(\mathbb Q\)-Gorenstein condition.
- **Missing:** Kollár’s condition for reflexive powers.
- **Missing:** Relative ampleness of \(K_{X/S}+B\).
- **Missing:** Fixed dimension data.
- **Missing:** Fixed boundary-coefficient data.
- **Missing:** Fixed volume data.
- **Missing:** Fixed Hilbert polynomial or Hilbert function data.
- **Missing:** Fixed Cartier-index data.
- **Missing:** The KSBA moduli fibred category.
- **Missing:** Its pullback functors and coherence.
- **Missing:** Its descent and stack condition.
- **Missing:** Boundedness, separatedness, stable reduction, and properness results.

The last line is not needed for the bare definition. It is needed for a useful compactified moduli stack.

## 6. Analytic and manifold categories

Mathlib has manifold structures. The missing part is the categorical and analytic layer.

- **Partial:** Categories of topological manifolds and continuous maps.
- **Partial:** Categories of smooth manifolds and smooth maps.
- **Partial:** Categories of complex manifolds and holomorphic maps.
- **Missing:** Holomorphic vector bundles and line bundles.
- **Missing:** Sheaves of holomorphic and meromorphic functions.
- **Missing:** Complex analytic spaces with singularities.
- **Missing:** Analytic stacks.
- **Missing:** Analytification of complex schemes.
- **Missing:** Analytification of algebraic stacks.
- **Missing:** Comparison results between algebraic and analytic objects.
- **Missing:** Complex orbifolds.
- **Missing:** Properly discontinuous holomorphic actions.
- **Missing:** Analytic quotient stacks and coarse quotients.

Mathlib’s current complex-manifold file states that its holomorphic bundle theory remains undeveloped. See [Complex.lean](/home/dzack/gitclones/lean-categories/.lake/packages/mathlib/Mathlib/Geometry/Manifold/Complex.lean).

## 7. Cohomology and Hodge theory

- **Missing:** Integral local systems on spaces and manifolds.
- **Missing:** Categories of local systems.
- **Missing:** Monodromy representations.
- **Missing:** Marked local systems.
- **Missing:** Integral cohomology as a functor suitable for families.
- **Missing:** Cup products.
- **Missing:** Poincaré duality.
- **Missing:** Primitive cohomology.
- **Missing:** Intersection polarizations.
- **Missing:** Algebraic de Rham cohomology.
- **Missing:** Betti and de Rham comparison.
- **Missing:** Pure integral Hodge structures.
- **Missing:** Rational Hodge structures.
- **Missing:** Polarized Hodge structures.
- **Missing:** Morphisms and categories of Hodge structures.
- **Missing:** Hodge filtrations and decompositions for geometric fibers.
- **Missing:** Variations of Hodge structure.
- **Missing:** Gauss–Manin connections.
- **Missing:** Griffiths transversality.
- **Missing:** Polarized variations.
- **Missing:** Smooth proper base change in the required form.
- **Missing:** The geometric construction from a family to its variation.

Generic sheaf cohomology exists. The geometric Hodge package does not exist.

## 8. Period domains and period morphisms

- **Missing:** Type-IV domains built from formed lattices.
- **Missing:** Their connected components and orientations.
- **Missing:** Their complex-manifold structure.
- **Missing:** Arithmetic subgroups and their actions.
- **Missing:** Marked period spaces.
- **Missing:** Quotient period stacks.
- **Missing:** Arithmetic coarse quotients.
- **Missing:** Period points from geometric fibers.
- **Missing:** Functoriality under fiber isomorphisms.
- **Missing:** A period functor on a family groupoid.
- **Missing:** Descent under changes of marking.
- **Missing:** A morphism from a moduli stack to a quotient period stack.
- **Missing:** A coarse period map after coarse-space construction.

Therefore, the period map does not yet have a valid source or target.

## 9. Degenerations and compactifications

- **Missing:** Baily–Borel compactifications.
- **Partial:** Rational polyhedral cone theory.
- **Missing:** A full theory of fans.
- **Missing:** Affine toric schemes from cones.
- **Missing:** The fan-to-scheme functor.
- **Missing:** Toroidal compactifications.
- **Missing:** Arithmetic fans and semifans.
- **Missing:** Wythoff coarsening.
- **Missing:** Semitoroidal compactifications.
- **Missing:** Coxeter, KSBA, and GIT semifan comparisons.
- **Missing:** Kulikov families and models.
- **Missing:** Semistable degenerations of surfaces.
- **Missing:** Monodromy types for Kulikov degenerations.
- **Missing:** Limiting mixed Hodge structures.
- **Missing:** Nilpotent-orbit data, if the extension uses it.
- **Missing:** Integral-affine manifolds.
- **Missing:** Integral-affine singularities.
- **Missing:** Focus-focus singularities.
- **Missing:** Extension of period morphisms across boundaries.
- **Missing:** Comparison between KSBA and period boundaries.

Mathlib supplies `PointedCone`, dual cones, and some finite cone results. It does not supply the assembled fan or toric theory.

## 10. The program-wide higher layer

This layer follows the repository’s stated long-term target.

- **Partial:** Quasicategories and simplicial sets.
- **Missing:** A usable category of infinity-categories.
- **Missing:** A usable \((\infty,2)\)-category of infinity-categories.
- **Missing:** Higher functors, transformations, and modifications at this level.
- **Missing:** Homotopy pullbacks and general higher limits.
- **Missing:** Higher categories of structured objects.
- **Missing:** Higher stacks and higher descent.
- **Missing:** Comparisons with the current strict and bicategorical models.

This layer does not block the first ordinary stack implementation. It does block the complete semantic target.

The dependency order is:

`schemes and divisors → algebraic stacks → KSBA families`

`analytic geometry and Hodge theory → period targets`

`both branches → period morphism → compactification comparison`

This inventory has high confidence at the theory-area level. It does not list every required lemma.

I did not audit open Mathlib pull requests or external Lean projects. Those require a separate reuse audit.
