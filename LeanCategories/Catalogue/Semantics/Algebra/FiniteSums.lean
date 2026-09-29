/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PartialMaps
public import Mathlib.Algebra.BigOperators.Finprod
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Sums and products over finite subsets (SPEC.md, "A composed computation")

For `f : X → Y` into a commutative monoid, `∑_{a ∈ A} f(a)` and `∏_{a ∈ A} f(a)` are defined for
finite `A ⊆ X` (Mathlib `finsum_mem`, `finprod_mem`) and undefined otherwise: partial maps
`𝒫(X) ⇀ Y`, maps `𝒫(X) → Y⊥`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.FiniteSums

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.PartialMaps

open Classical in
/-- `A ↦ ∑_{a ∈ A} f(a)`, defined for finite `A`. -/
noncomputable def sum (X Y : Type) [AddCommMonoid Y] (f : (X : SetsCat.{0}) ⟶ (Y : SetsCat.{0})) :
    powerSet X ⟶ partialValues Y :=
  TypeCat.ofHom fun A =>
    if A.Finite then some (∑ᶠ a ∈ A, ConcreteCategory.hom (C := Type) f a) else none

open Classical in
/-- `A ↦ ∏_{a ∈ A} f(a)`, defined for finite `A`. -/
noncomputable def prod (X Y : Type) [CommMonoid Y] (f : (X : SetsCat.{0}) ⟶ (Y : SetsCat.{0})) :
    powerSet X ⟶ partialValues Y :=
  TypeCat.ofHom fun A =>
    if A.Finite then some (∏ᶠ a ∈ A, ConcreteCategory.hom (C := Type) f a) else none

end CasCatalogue.Algebra.FiniteSums

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_sum"⟩, category := CategoryId.sets, name := "∑"
    declaration := `CasCatalogue.Algebra.FiniteSums.sum }

normalized_registry .morphism
  { id := ⟨"mor.sets.finite_product"⟩, category := CategoryId.sets, name := "∏"
    declaration := `CasCatalogue.Algebra.FiniteSums.prod }

end CasCatalogue
