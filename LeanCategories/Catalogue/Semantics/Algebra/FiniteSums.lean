/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import LeanCategories.Catalogue.Semantics.Foundation.Maps
public import LeanCategories.Catalogue.Semantics.Algebra.CommutativeMonoids
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Sums and products over finite subsets (SPEC.md, "A composed computation")

For `f : X → Y` into a commutative monoid `Y`, `∑_{a ∈ A} f(a)` and `∏_{a ∈ A} f(a)` are defined on
the finite subsets `A` of `X` (Mathlib `Finset.sum`, `Finset.prod`): maps `𝒫_fin(X) → Y`. The
codomain `Y` is an object of the category carrying the structure the fold uses (LC-13): of
additive commutative monoids for `∑` (Mathlib `AddCommMonCat`), of commutative monoids for `∏`
(Mathlib `CommMonCat`), whose addition, multiplication and units are `Y`'s
(`Algebra.CommutativeMonoids`). A ring reaches the first along `Ring → AddCommMon`, a commutative
ring the second along `CommRing → CommMon`.

## The binders `∑_{t ∈ A} e` and `∏_{t ∈ A} e` (`lean-cas-dsl/specs/binders.md`)

At a finite subset `A ∈ 𝒫_fin(X)` the sum is the map `Y^X → Y`, `f ↦ ∑_{a ∈ A} f(a)`, out of the
set `Y^X` of all maps `X → Y` (`Foundation.Maps`): it is total on every map, so its object of maps
admits every map, with no hypothesis. The bound variable ranges over `X`, not over the members of
`A`: the domain of the bound map is `X`.

That choice is made because the operation is then defined on all of `Y^X` and is the composite of
the restriction `Y^X → Y^A` with the fold `Y^A → Y` of the commutative monoid `Y` over the finite
set `A` (Bourbaki, *Algebra I*, I.2.1); the value depends on `f` only through `f|_A`. The body
`e` is then read with `t ∈ X`, where every operation of `X` applies to `t` with no inclusion of
`A` into `X`. A body defined only on `A` and not on `X` is not admitted by this row; it is an
element of `Y^A`, a sum over the extent of `A`, which would be a further row with domain `A`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.FiniteSums

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.FiniteSubsets
open CasCatalogue.Algebra.CommMonoids

/-- `A ↦ ∑_{a ∈ A} f(a)`. -/
def sum (X : Type) (Y : AdditiveCommutativeMonoids.{0})
    (f : (X : SetsCat.{0}) ⟶ (addCommMonoidCarrier Y : SetsCat.{0})) :
    finiteSubsets X ⟶ (addCommMonoidCarrier Y : SetsCat.{0}) :=
  TypeCat.ofHom fun A => ∑ a ∈ A, ConcreteCategory.hom (C := Type) f a

/-- `A ↦ ∏_{a ∈ A} f(a)`. -/
def prod (X : Type) (Y : CommutativeMonoids.{0})
    (f : (X : SetsCat.{0}) ⟶ (commMonoidCarrier Y : SetsCat.{0})) :
    finiteSubsets X ⟶ (commMonoidCarrier Y : SetsCat.{0}) :=
  TypeCat.ofHom fun A => ∏ a ∈ A, ConcreteCategory.hom (C := Type) f a

open CasCatalogue.Foundation.Maps CasCatalogue.Foundation.Objects in
/-- `f ↦ ∑_{a ∈ A} f(a)`, `Y^X → Y`, at the finite subset `A ∈ 𝒫_fin(X)` (Mathlib `Finset.sum`). The
binder `∑_{t ∈ A} e`: its argument is the point `A`; `X` and `Y` are read off `A` and the body. -/
def sumOver (X : Type) (Y : AdditiveCommutativeMonoids.{0}) (A : fin 1 ⟶ finiteSubsets X) :
    maps X (addCommMonoidCarrier Y) ⟶ (addCommMonoidCarrier Y : SetsCat.{0}) :=
  TypeCat.ofHom fun f => ∑ a ∈ ConcreteCategory.hom (C := Type) A 0, f a

open CasCatalogue.Foundation.Maps CasCatalogue.Foundation.Objects in
/-- `f ↦ ∏_{a ∈ A} f(a)`, `Y^X → Y`, at the finite subset `A ∈ 𝒫_fin(X)` (Mathlib `Finset.prod`). -/
def prodOver (X : Type) (Y : CommutativeMonoids.{0}) (A : fin 1 ⟶ finiteSubsets X) :
    maps X (commMonoidCarrier Y) ⟶ (commMonoidCarrier Y : SetsCat.{0}) :=
  TypeCat.ofHom fun f => ∏ a ∈ ConcreteCategory.hom (C := Type) A 0, f a

open CasCatalogue.Foundation.Objects in
/-- The bound variable of `∑_{t ∈ A}` and `∏_{t ∈ A}` ranges over `X`. -/
abbrev sumDomain (X : Type) (_ : AdditiveCommutativeMonoids.{0}) (_ : fin 1 ⟶ finiteSubsets X) :
    SetsCat.{0} :=
  X

open CasCatalogue.Foundation.Objects in
/-- The bound variable of `∏_{t ∈ A}` ranges over `X`. -/
abbrev prodDomain (X : Type) (_ : CommutativeMonoids.{0}) (_ : fin 1 ⟶ finiteSubsets X) :
    SetsCat.{0} :=
  X

open CasCatalogue.Foundation.Objects in
/-- The binder's sum is the registered `∑` along `f`: `∑_{t ∈ A} f(t)` is the image of `A` under
`A ↦ ∑_{a ∈ A} f(a)`. -/
theorem sumOver_eq_sum (X : Type) (Y : AdditiveCommutativeMonoids.{0})
    (A : fin 1 ⟶ finiteSubsets X)
    (f : (X : SetsCat.{0}) ⟶ (addCommMonoidCarrier Y : SetsCat.{0})) :
    ConcreteCategory.hom (C := Type) (sumOver X Y A)
        (fun x => ConcreteCategory.hom (C := Type) f x) =
      ConcreteCategory.hom (C := Type) (sum X Y f) (ConcreteCategory.hom (C := Type) A 0) :=
  rfl

open CasCatalogue.Foundation.Objects in
/-- The binder's product is the registered `∏` along `f`. -/
theorem prodOver_eq_prod (X : Type) (Y : CommutativeMonoids.{0})
    (A : fin 1 ⟶ finiteSubsets X)
    (f : (X : SetsCat.{0}) ⟶ (commMonoidCarrier Y : SetsCat.{0})) :
    ConcreteCategory.hom (C := Type) (prodOver X Y A)
        (fun x => ConcreteCategory.hom (C := Type) f x) =
      ConcreteCategory.hom (C := Type) (prod X Y f) (ConcreteCategory.hom (C := Type) A 0) :=
  rfl

end CasCatalogue.Algebra.FiniteSums

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_sum"⟩, category := CategoryId.sets, name := "∑"
    declaration := `CasCatalogue.Algebra.FiniteSums.sum }

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_product"⟩, category := CategoryId.sets, name := "∏"
    declaration := `CasCatalogue.Algebra.FiniteSums.prod }

normalized_registry .binder
  { id := ⟨"bind.sets.finite_sum"⟩, category := CategoryId.sets, token := "∑"
    operation := `CasCatalogue.Algebra.FiniteSums.sumOver
    domain := `CasCatalogue.Algebra.FiniteSums.sumDomain }

normalized_registry .binder
  { id := ⟨"bind.sets.finite_product"⟩, category := CategoryId.sets, token := "∏"
    operation := `CasCatalogue.Algebra.FiniteSums.prodOver
    domain := `CasCatalogue.Algebra.FiniteSums.prodDomain }

end CasCatalogue
