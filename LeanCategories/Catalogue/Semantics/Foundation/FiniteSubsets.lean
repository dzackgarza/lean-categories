/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Data.Finset.Card
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Finite subsets

`𝒫_fin(X)` (Mathlib `Finset X`), the finite subsets of `X`, a subobject of `𝒫(X)` (`Finset.coe`,
injective); sums and products over a subset are defined on it, where they are defined at all.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteSubsets

open CasCatalogue.Foundation.PowerSets

/-- `𝒫_fin(X)`. -/
abbrev finiteSubsets (X : Type) : SetsCat.{0} := Finset X

/-- `𝒫_fin(X) ↪ 𝒫(X)`. -/
def inclusion (X : Type) : finiteSubsets X ⟶ powerSet X := TypeCat.ofHom fun A => (A : Set X)

end CasCatalogue.Foundation.FiniteSubsets

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.finite_subsets"⟩, category := CategoryId.sets, name := "𝒫_fin"
    declaration := `CasCatalogue.Foundation.FiniteSubsets.finiteSubsets
    inclusion := some `CasCatalogue.Foundation.FiniteSubsets.inclusion }

end CasCatalogue
