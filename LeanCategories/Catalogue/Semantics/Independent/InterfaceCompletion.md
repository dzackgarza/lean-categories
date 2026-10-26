# Complete comparison and automorphism interfaces

These additive interfaces publish existing mathematical constructions. Import
`LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions` to obtain
all three modules below. No object, selected form, original morphism, or existing
operation is changed. The rows use the existing morphism and presentation entries.

## Change of value module

Owner module:
`LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ChangeValueComparisons`.
The declarations remain in the namespace
`CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts`.

The complete parameter telescope is

```lean
(R : Type u) [CommRing R]
(W W' : Type u) [AddCommGroup W] [Module R W]
[AddCommGroup W'] [Module R W']
(a : W →ₗ[R] W') (X : BilinModuleCat R W)
{K : BilinModuleCat R W'} (i : K ⟶ (changeValue R W a).obj X)
```

Write `V = changeValue R W a` and
`P = pulledBack R W W' a X i`. The existing complete comparison is
`pulledBackIso R W W' a X i : V.obj P ≅ K`.

| Public name | Registry ID | Declaration and complete result |
| --- | --- | --- |
| `pulled_back_forward` | `mor.bilin_module.pulled_back_forward` | `pulledBackForward R W W' a X i : V.obj P ⟶ K` |
| `pulled_back_backward` | `mor.bilin_module.pulled_back_backward` | `pulledBackBackward R W W' a X i : K ⟶ V.obj P` |

These are exactly the `.hom` and `.inv` of that original comparison. Both
underlying linear maps are identities on `K.carrier`. The two inverse laws
are `pulledBackForward_backward` and `pulledBackBackward_forward`. The triangle
`pulledBackForward R W W' a X i ≫ i = V.map (pulledBackHom R W W' a X i)`
is `pulledBackForward_hom`. There is no `Mono i` argument or finiteness condition.

For the specified paired cone, the actual specialization is

```lean
pulledBackForward ℚ (ℚ × ℚ) ℚ (LinearMap.fst ℚ ℚ ℚ)
  DegeneratePlaneLifts.pairedSource DegeneratePlaneFactorization.cone
  : (changeValue ℚ (ℚ × ℚ) (LinearMap.fst ℚ ℚ ℚ)).obj
      DegeneratePlaneFactorization.pairedConeSource ⟶
    DegeneratePlaneFactorization.zeroSource
```

The backward arrow reverses these exact endpoints. For any first factor
`h₁ : zeroSource ⟶ firstObject`, the source-correct second-stage base map is
`pulledBackForward … ≫ h₁`. The source checks prove its compatibility whenever
`h₁ ≫ firstInclusion = cone`, and prove the whole-map comparison for every
second factor with its required defining-map equation. They use monicity of
the first inclusion, without requiring monicity of the cone.

## Complete inputs to the core of sets

Owner module: `LeanCategories.Catalogue.Semantics.Foundation.CoreIsomorphisms`.
Namespace: `CasCatalogue.Foundation.CoreIsomorphisms`.

| Public name | Registry ID | Complete signature |
| --- | --- | --- |
| `core_iso` | `mor.core_sets.specified_iso` | `setsIso (X Y : Type u) (e : X ≅ Y) : Core.mk X ⟶ Core.mk Y` |
| `fin_reversal` | `cmp.sets.fin_reversal` | `finRevIso (n : ℕ) : Objects.fin n ≅ Objects.fin n` |
| `core_rev` | `mor.core_sets.fin_rev` | `finRevCore (n : ℕ) : Core.mk (Objects.fin n) ⟶ Core.mk (Objects.fin n)` |

`core_iso` reuses Mathlib `CoreHom.mk`: it retains the complete supplied
isomorphism. `fin_reversal` reuses `Fin.revPerm.toIso`. Both its directions
are precisely the existing `Morphisms.finRev n`, proved by `finRevIso_hom`
and `finRevIso_inv`. `core_rev` is the same comparison inserted by `core_iso`.
All three are total at their stated domains; no inverse is guessed or extracted
from an unproved bijectivity claim. The reversal family includes `n = 0`.

Consequently `TwoSubsets.onCore.map (finRevCore 5)` has the original
`TwoSubsets.twoSubsets (Fin 5)` as both endpoints. The checked theorem
`twoSubsets_reversal_extent` gives direct image on every complete two-element
subset, and `twoSubsets_reversal_twice` gives the full inverse composite.
`fin_five_reversal_ne_identity` distinguishes the selected input from identity.
The original two-subset functor and its domain are unchanged.

## Arrows and application of automorphism elements

Owner module: `LeanCategories.Catalogue.Semantics.Algebra.AutomorphismArrows`.
Namespace: `CasCatalogue.Algebra.AutomorphismArrows`.

For every bundled category `C : Cat.{v,u}`, object `X : C`, and element
`a : Aut X`, the general formal declarations are

```lean
forward  (C : Cat.{v,u}) (X : C) (a : Aut X) : X ⟶ X
backward (C : Cat.{v,u}) (X : C) (a : Aut X) : X ⟶ X
```

They project `a.hom` and `a.inv`, respectively. The inverse equations,
compatibility with group multiplication and inversion, and both conjugation
equations are proved for arbitrary `C`. If `e : X ≅ Y`, the actual image under
`automorphismsConstruction C` has arrows
`e.inv ≫ a.hom ≫ e.hom` and `e.inv ≫ a.inv ≫ e.hom`.

The existing concrete `Aut` owners publish these whole callable arrows:

| Public name | Registered category | Declaration parameters | Registry ID |
| --- | --- | --- | --- |
| `automorphism_forward` | Sets | `setsForward (X : Type u) (a : Aut X)` | `mor.sets.automorphism_forward` |
| `automorphism_backward` | Sets | `setsBackward (X : Type u) (a : Aut X)` | `mor.sets.automorphism_backward` |
| `automorphism_forward` | Groups | `groupsForward (G : GrpCat.{u}) (a : Aut G)` | `mor.groups.automorphism_forward` |
| `automorphism_backward` | Groups | `groupsBackward (G : GrpCat.{u}) (a : Aut G)` | `mor.groups.automorphism_backward` |
| `automorphism_forward` | Modules | `modulesForward (R : RingCat.{u}) (M : ModuleCat.{u} R) (a : Aut M)` | `mor.modules.automorphism_forward` |
| `automorphism_backward` | Modules | `modulesBackward (R : RingCat.{u}) (M : ModuleCat.{u} R) (a : Aut M)` | `mor.modules.automorphism_backward` |

Each `a` parameter is explicitly the carrier of the existing automorphism
functor at the selected object. The category-sensitive results retain the
original group or module structure. Applying a projected arrow is ordinary
application of the complete map at an element of its original domain.

There are also two general registered evaluation families in Sets:

```lean
evaluation (C : Cat.{v,u}) (U : C ⥤ Type v) (X : C) :
  (Aut X × U.obj X : Type v) ⟶ U.obj X
inverseEvaluation (C : Cat.{v,u}) (U : C ⥤ Type v) (X : C) :
  (Aut X × U.obj X : Type v) ⟶ U.obj X
```

Their public names are `automorphism_evaluation` and
`automorphism_inverse_evaluation`, with IDs
`mor.sets.automorphism_evaluation` and
`mor.sets.automorphism_inverse_evaluation`. They send `(a,x)` to
`U.map a.hom x` and `U.map a.inv x`. The selected functor is an input; no
carrier or forgetful route is inferred from category membership. Their
identity, multiplication and two inverse laws are proved. These declarations
use the same universe `v` for morphisms and the selected set-valued functor;
the generic forward/backward projections have independent object universe `u`.

## Sources and verification scope

The mathematical source requirements were the independently fixed
`selected-lift-requirements.md` and `coverage-and-derivations.md`, specifically
their complete cone-source comparison, core-arrow input, and underlying
automorphism-arrow obligations. No implementation, leaf, execution output,
or altered assertion supplied a mathematical definition here.

Reuse inspection found all required constructions locally: Mathlib
`CategoryTheory/Core.lean`, `CategoryTheory/Endomorphism.lean`,
`CategoryTheory/Iso.lean`, and `Data/Fin/Rev.lean`, plus the original
`ChangeValueLifts.lean`, `TwoSubsets.lean`, `Automorphisms.lean`,
`CyclicQuotients.lean`, and two degenerate-plane modules. The pinned Mathlib
revision is `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0).
The external corpus search was not available under the no-network task
constraint; no absence claim or greenfield definition depends on that search.

`Independent.InterfaceCompletionTests` checks the whole two-subset image and
inverse composite, nonidentity on `Fin 5`, the complete forward and reciprocal
unit-coordinate actions for every natural modulus, the fixed tripling inverse
at modulus five, full conjugation, and the exact source-correct cone and factor
equations. These are source-level mathematical checks. They do not establish
downstream execution or release acceptance.
