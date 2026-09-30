/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Sums and products over finite subsets (SPEC.md, "A composed computation")

For `f : X → Y` into a commutative monoid, `∑_{a ∈ A} f(a)` and `∏_{a ∈ A} f(a)` are defined on
the finite subsets `A` of `X` (Mathlib `Finset.sum`, `Finset.prod`): maps `𝒫_fin(X) → Y`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.FiniteSums

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.FiniteSubsets

/-- `A ↦ ∑_{a ∈ A} f(a)`. -/
def sum (X Y : Type) [AddCommMonoid Y] (f : (X : SetsCat.{0}) ⟶ (Y : SetsCat.{0})) :
    finiteSubsets X ⟶ (Y : SetsCat.{0}) :=
  TypeCat.ofHom fun A => ∑ a ∈ A, ConcreteCategory.hom (C := Type) f a

/-- `A ↦ ∏_{a ∈ A} f(a)`. -/
def prod (X Y : Type) [CommMonoid Y] (f : (X : SetsCat.{0}) ⟶ (Y : SetsCat.{0})) :
    finiteSubsets X ⟶ (Y : SetsCat.{0}) :=
  TypeCat.ofHom fun A => ∏ a ∈ A, ConcreteCategory.hom (C := Type) f a

end CasCatalogue.Algebra.FiniteSums

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_sum"⟩, category := CategoryId.sets, name := "∑"
    declaration := `CasCatalogue.Algebra.FiniteSums.sum }

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_product"⟩, category := CategoryId.sets, name := "∏"
    declaration := `CasCatalogue.Algebra.FiniteSums.prod }

end CasCatalogue
