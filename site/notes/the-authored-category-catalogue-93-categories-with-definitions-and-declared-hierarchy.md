---
title: "The authored category catalogue: 93 categories with definitions and declared hierarchy"
---

Extracted from the author's own declarations. Each row: the authored definition (from the source docstring) and the declared parent categories (from `super_categories` / `extra_super_categories`). `→` means "declared parent of".

Sources:

- P = `~/research/src/dzack_research/preamble/categories/` (76)
- S = `~/research/computations/experiments/sage_lattice_category_spike/objects/categories.py` (20)
- 3 names appear in both (`IntegralLattices`, `HyperbolicLattices`, `DiscriminantForms`).

Lean status column: `A` = present at extraction on 2026-08-06; `—` = not found in that historical pass. The column predates the unified `LeanCategories` tree and is not current status. Mathlib realization was not filled in during extraction. Mathlib realization is NOT filled in — that requires per-item verified search and is the next pass, not something to guess here.

------------------------------------------------------------------------

## 1. Generic constructions (19, P)

Parameterized over an ambient category **C**.

| Category                 | Authored definition                                                                                                            | Parents                                 | Lean |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------- | ---- |
| `ArrowCategory`          | Ar(**C**): the morphisms of **C** as objects                                                                                   | `Objects()`                             | —    |
| `IsoArrowCategory`       | the subcategory of Ar(**C**) of isomorphisms                                                                                   | `ArrowCategory`                         | —    |
| `DiagramCategory`        | a diagram F: J → **C**: a family of objects and morphisms                                                                      | ambient **C**                           | —    |
| `DirectedSystem`         | (Xᵢ)ᵢ∈I with morphisms Xᵢ→Xⱼ for i ≤ j                                                                                         | `DiagramCategory`                       | —    |
| `InverseSystem`          | (Xᵢ)ᵢ∈I with morphisms Xⱼ→Xᵢ for i ≤ j                                                                                         | `DiagramCategory`                       | —    |
| `ConeCategory`           | an apex with structure morphisms over a system                                                                                 | `DiagramCategory`                       | —    |
| `CoconeCategory`         | a coapex with costructure morphisms under a system                                                                             | `DiagramCategory`                       | —    |
| `ProductCategory`        | a cone over a discrete diagram; parameterized by factors                                                                       | `ConeCategory`                          | —    |
| `CoproductCategory`      | a cocone under a discrete diagram; parameterized by cofactors                                                                  | `CoconeCategory`                        | —    |
| `BiproductCategory`      | simultaneously product and coproduct (additive): πⱼ∘ιᵢ = δᵢⱼ. Direct sum is the additive synonym                               | `ProductCategory` + `CoproductCategory` | —    |
| `TensorProductCategory`  | X₁⊗⋯⊗Xₙ. **A cocone — an object *under* something — and what it is under is the cartesian product M×N, not M or N separately** | (cocone)                                | —    |
| `SliceOverCategory`      | **C**/X: objects over X                                                                                                        | ambient **C**                           | —    |
| `CosliceUnderCategory`   | X∖**C**: objects under X                                                                                                       | ambient **C**                           | —    |
| `SubobjectCategory`      | subcategory of SliceOver(X) on monomorphisms A ↪ X                                                                             | `SliceOverCategory`                     | —    |
| `SuperobjectCategory`    | subcategory of CosliceUnder(X) on monomorphisms X ↪ B                                                                          | `CosliceUnderCategory`                  | —    |
| `CoveringObjectCategory` | subcategory of SliceOver(X) on epimorphisms A ↠ X                                                                              | `SliceOverCategory`                     | —    |
| `CoveredObjectCategory`  | subcategory of CosliceUnder(X) on epimorphisms X ↠ B                                                                           | `CosliceUnderCategory`                  | —    |
| `KernelCategory`         | subcategory of SubObject(dom f): ker(f) ↪ dom f                                                                                | `SubobjectCategory`                     | —    |
| `CokernelCategory`       | subcategory of CoveredObject(cod f): cod f ↠ coker(f)                                                                          | `CoveredObjectCategory`                 | —    |

Note the design: kernel and cokernel are **derived** as subcategories of subobject/covered-object, not primitive. Subobject is mono-over-X, matching #56's `Sub_C(X) := MonoOver X` ruling.

## 2. Groups (6, P)

| Category                       | Authored definition                                                                                                                                                           | Parents                            | Lean |
| ------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------- | ---- |
| `OwnedGroups`                  | groups whose notebook-facing methods are preamble-owned                                                                                                                       | Sage `Groups`                      | —    |
| `OwnedAbelianGroups`           | abelian groups. **Ab and ℤ-Mod are isomorphic categories — that is not the statement that a group parent already is a module: a ℤ-module is a pair (S,ρ) and ρ is structure** | `OwnedGroups`                      | —    |
| `OwnedFiniteGroups`            | finite groups                                                                                                                                                                 | `OwnedGroups`, Sage `FiniteGroups` | —    |
| `OwnedFinitelyGeneratedGroups` | groups admitting a surjection F(S) ↠ G, S finite. **Finite generation is a property of a *morphism* — the existence of that surjection — not of a stored list of elements**   | `OwnedGroups`                      | —    |
| `OwnedFinitelyPresentedGroups` | f.g. groups whose defining surjection has f.g. kernel. Strictly stronger than f.g.; strictly weaker than finite                                                               | `OwnedFinitelyGeneratedGroups`     | —    |
| `FinitelyPresentedGroups`      | finitely presented groups with compact multi-line LaTeX                                                                                                                       | `OwnedGroups`                      | —    |

## 3. Modules (11, P) — the load-bearing tower

| Category                          | Authored definition                                                                                                                                                               | Parents                                            | Lean                            |
| --------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------- | ------------------------------- |
| `FreeModules`                     | free modules, **without** a chosen generating set                                                                                                                                 | Sage `Modules(R)`                                  | —                               |
| `TorsionModules`                  | torsion modules over R                                                                                                                                                            | Sage `Modules(R)`                                  | —                               |
| `FramedModules`                   | modules carrying a specified surjection F_R(S) → M. **The morphism, not a cached list of its values, is the datum. No finiteness, countability, or orderability hypothesis on S** | axiom on Sage `Modules(R)` → `Modules(R).Framed()` | —                               |
| `FramedFreeModules`               | free modules equipped with the canonical map S → U(F_R(S))                                                                                                                        | `FreeModules`, `Modules(R).Framed()`               | —                               |
| `FinitelyGeneratedModules`        | f.g. modules over R                                                                                                                                                               | `Modules(R).Framed()`                              | —                               |
| `FinitelyGeneratedFreeModules`    | finite free modules whose framing set has a **chosen total order**                                                                                                                | `FramedFreeModules`, `FinitelyGeneratedModules`    | partial (`Modules/FiniteFreeZ`) |
| `FinitelyPresentedModules`        | finitely presented modules over R                                                                                                                                                 | `FinitelyGeneratedModules`                         | —                               |
| `FinitelyPresentedTorsionModules` | f.p. torsion modules with a chosen generating set                                                                                                                                 | `TorsionModules`, `FinitelyPresentedModules`       | —                               |
| `DirectSumObjects`                | pairs (M, (Mᵢ)ᵢ) with a **chosen ordered** direct-sum structure                                                                                                                   | `Sets()`                                           | —                               |
| `GroupModules`                    | the category of R[G]-modules for specified R and G                                                                                                                                | `FinitelyGeneratedFreeModules`                     | —                               |
| `GroupLattices`                   | **the pullback of G-modules and integral lattices**                                                                                                                               | `GroupModules(ℤ,G)`, `IntegralLattices`            | —                               |

`Modules(R).Framed()` is an **axiom the author adds to Sage's `Modules`**, not a new category — the framing sits at the base of everything downstream.

## 4. Forms on modules (8, P)

| Category                           | Authored definition                                                                                           | Parents                                                                           | Lean                |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------- | ------------------- |
| `FormModules`                      | modules over R equipped with a form                                                                           | **`Modules(R).Framed()`**                                                         | —                   |
| `BilinearFormModules`              | modules whose form is bilinear                                                                                | `FormModules`                                                                     | `Modules/Bilinear`  |
| `SymmetricBilinearFormModules`     | modules with a symmetric bilinear form                                                                        | `BilinearFormModules`                                                             | —                   |
| `QuadraticFormModules`             | modules whose form is quadratic                                                                               | `FormModules`                                                                     | `Modules/Quadratic` |
| `FreeFormModules`                  | form modules free after forgetting the form                                                                   | `FormModules`, `FramedFreeModules`                                                | —                   |
| `FinitelyGeneratedFormModules`     | form modules whose chosen framing set is finite                                                               | `FormModules`, `FinitelyGeneratedModules`                                         | —                   |
| `FinitelyGeneratedFreeFormModules` | finite free modules equipped with a form                                                                      | `FreeFormModules`, `FinitelyGeneratedFormModules`, `FinitelyGeneratedFreeModules` | —                   |
| `CokernelForms`                    | torsion forms constructed as coker(f) for f: L→M of finite index. **"A construction, not a kind of object."** | `TorsionModulesWithForm`                                                          | —                   |

**A form module is a framed module.** The framing is not incidental — every form category inherits it.

## 5. Lattices (6 P + 11 refinements S)

| Category                   | Authored definition                                                                                  | Parents                                                             | Lean                             |
| -------------------------- | ---------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------- | -------------------------------- |
| `IntegralLattices` (P)     | integral lattices with enriched methods: q/b/div, dual basis, isotropic quotients, isometry checking | `FinitelyGeneratedFreeFormModules` + `SymmetricBilinearFormModules` | `Lattices/Integral`              |
| `HyperbolicLattices` (P)   | hyperbolic integral lattices, signature (n,1); Vinberg root enumeration                              | `IntegralLattices`                                                  | —                                |
| `LatticeHomomorphisms` (P) | native form morphisms between integral lattices                                                      | `Sets()`                                                            | `Morphisms/Embedding`            |
| `LatticeIsometries` (P)    | invertible lattice homomorphisms                                                                     | `LatticeHomomorphisms`                                              | —                                |
| `Subobjects` (P)           | modules carrying a chosen monomorphism into an ambient module                                        | `Sets()`                                                            | —                                |
| `CoxeterDiagrams` (P)      | finite Coxeter diagrams and Coxeter-matrix-preserving maps                                           | `Sets().Finite()`                                                   | `Groups/Reflection/CoxeterDatum` |
| `Lattices` (S, root)       | **based** free R-modules with a symmetric K-valued form; base possibly degenerate                    | `FiniteFreeModules(R)`, `Modules(R).FiniteDimensional()`            | —                                |

Spike refinements, as an axiom lattice on `Lattices`:

| Refinement              | Declared over                           |
| ----------------------- | --------------------------------------- |
| `Nondegenerate`         | `Lattices`                              |
| `Integral`              | `Lattices`                              |
| `IntegralNondegenerate` | `Integral` ∧ `Nondegenerate`            |
| `Even`                  | `Lattices.Integral()`                   |
| `Unimodular`            | `Lattices.Integral()`                   |
| `RootGenerated`         | `Lattices`                              |
| `Definite`              | `Lattices`                              |
| `PositiveDefinite`      | `Lattices.Definite()`                   |
| `NegativeDefinite`      | `Lattices.Definite()`                   |
| `Indefinite`            | `Lattices`                              |
| `Hyperbolic`            | `Lattices.Indefinite().Nondegenerate()` |

**Source divergence to resolve:** the preamble says *framed* (a surjection is the datum); the spike root says *based*. Not the same notion.

## 6. Discriminant forms and genera (4 P + 7 S)

| Category                           | Authored definition                                                                                                                                               | Parents                                                  | Lean                          |
| ---------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- | ----------------------------- |
| `TorsionModulesWithForm` (P)       | finite torsion modules equipped with a form                                                                                                                       | `FinitelyGeneratedFormModules`, `TorsionModules`         | —                             |
| `DiscriminantForms` (P)            | the cokernels whose morphism is a correlation: A_L = coker(c: L→L^∨). **"A refinement, not a kind of object. A torsion bilinear form is (G,b) and nothing else"** | `CokernelForms`                                          | `Lattices/Discriminant/Basic` |
| `DiscriminantBilinearModules` (P)  | discriminant bilinear modules; `gram_matrix` is the bilinear Gram matrix                                                                                          | `TorsionModulesWithForm`, `SymmetricBilinearFormModules` | —                             |
| `DiscriminantQuadraticModules` (P) | objects carry q: A → ℚ/2ℤ; polarization b_q: A×A → ℚ/ℤ is reachable, not primitive                                                                                | `TorsionModulesWithForm`, `QuadraticFormModules`         | —                             |
| `DiscriminantForms` (S)            | finite abelian groups with a discriminant bilinear/quadratic form. **Typed as a finite abelian group, fixing Sage's "modules over ℤ" mis-typing**                 | `AdditiveGroups().AdditiveCommutative().Finite()`        | —                             |
| `Genera` (S)                       | **an object is the finite set of isometry classes sharing a signature and discriminant quadratic form** (Nikulin 1.10.1); its cardinality is the class number     | `Sets().Finite()`                                        | `Objects/Genus.lean`          |

Spike refinements: `Bilinear`, `Quadratic` (over `Bilinear`), `Nondegenerate`, `Even` (over `Quadratic`), `WithSourceLattice`; and `EvenGenera` over `Genera`.

**The two sources genuinely disagree here** — preamble types a discriminant form as a *cokernel refinement*; spike types it as *a finite abelian group with a form*. The preamble docstring argues explicitly against the construction-as-object reading.

## 7. Algebras (7, P) — parallel to §3, one level up

| Category                    | Authored definition                                                 | Parents                                               | Lean |
| --------------------------- | ------------------------------------------------------------------- | ----------------------------------------------------- | ---- |
| `Algebras`                  | associative unital algebras over R                                  | Sage `Algebras(R)`                                    | —    |
| `FreeAlgebras`              | free commutative algebras over R, without chosen generators         | `Algebras`, `FreeModules`                             | —    |
| `FramedAlgebras`            | R-algebras carrying a specified surjection FreeAlg_R(S) → A         | `Algebras`, `FramedModules`                           | —    |
| `FramedFreeAlgebras`        | free R-algebras with the canonical map S → U(FreeAlg_R(S))          | `FreeAlgebras`, `FramedAlgebras`, `FramedFreeModules` | —    |
| `FinitelyGeneratedAlgebras` | (axiom)                                                             | —                                                     | —    |
| `FinitelyPresentedAlgebras` | algebras presented as a free algebra modulo finitely many relations | `FramedFGAlgebras`                                    | —    |
| `FramedFGAlgebras`          | f.g. framed algebras presented as a free-algebra quotient           | `FinitelyPresentedAlgebras`, `FramedAlgebras`         | —    |

The free/framed/fg/fp pattern is **identical** to §3. This is one construction applied at two levels, not two designs.

## 8. Schemes (10, P)

| Category              | Authored definition                               | Parents                          | Lean              |
| --------------------- | ------------------------------------------------- | -------------------------------- | ----------------- |
| `RingedSpaces`        | ringed spaces                                     | `Sets()`                         | —                 |
| `LocallyRingedSpaces` | ringed spaces satisfying the LocallyRinged axiom  | `RingedSpaces().LocallyRinged()` | —                 |
| `Schemes`             | schemes over a base scheme or ring S              | `LocallyRingedSpaces`            | —                 |
| `AffineSpaces`        | 𝔸ⁿ over a base S                                  | `Schemes(S)`                     | —                 |
| `ProjectiveSpaces`    | ℙⁿ over a base S                                  | `Schemes(S)`                     | —                 |
| `OpenSubschemes`      | open subschemes U → X                             | `Schemes(S)`                     | —                 |
| `ClosedSubschemes`    | closed subschemes V → X                           | `Schemes(S)`                     | —                 |
| `Varieties`           | integral, separated schemes of finite type over S | `Schemes(S)`                     | —                 |
| `Curves`              | varieties of dimension 1                          | `Varieties(S)`                   | `Objects/Curve`   |
| `Surfaces`            | varieties of dimension 2                          | `Varieties(S)`                   | `Objects/Surface` |

## 9. Divisors (5, P)

| Category               | Authored definition                                 | Parents                | Lean                   |
| ---------------------- | --------------------------------------------------- | ---------------------- | ---------------------- |
| `DivisorGroups`        | free abelian groups on specified prime divisors     | `FramedFreeModules(ℤ)` | —                      |
| `WeilDivisorGroups`    | free abelian groups on codimension-one subvarieties | `DivisorGroups`        | —                      |
| `CartierDivisorGroups` | framed ℤ-modules of Cartier divisors                | `Modules(ℤ).Framed()`  | —                      |
| `ClassGroups`          | framed ℤ-modules of Weil divisor classes            | `Modules(ℤ).Framed()`  | —                      |
| `PicardGroups`         | framed ℤ-modules of line-bundle classes             | `Modules(ℤ).Framed()`  | `Objects/DivisorClass` |

All five are **framed ℤ-modules** — they land in §3's tower, not in a separate group theory.

## Current ownership and interpretation (2026-08-11)

This record preserves the author's raw Sage-side declaration surface. It is source evidence, not the current Lean catalogue and not an execution tracker.

Later adjudication resolved two source conflicts recorded above. Module-valued forms do not intrinsically require framing. Issue #33 owns framing and coordinate presentations as separate structure. Commit `6d42343` realizes the fixed-rank `GenFrame`, `BasisFrame`, and `Coord` categories. It also realizes `CoordLatticeCat` and its intrinsic comparison. This does not realize the arbitrary-index `FramedModules` row in this extraction. A discriminant form is a finite torsion form. Production from a source lattice is a functor-image relation owned by issue #34.

Commit `59b7813` removed the separate `CategoryGraph` owner. Current realization status belongs to `main` and issues #4, #33 through #41, #54, #55, and #56. Do not maintain this extraction as a second live status table.
