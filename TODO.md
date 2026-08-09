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
