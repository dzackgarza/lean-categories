/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Sets
public meta import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration

/-!
# Ranked enumerated sets as catalogue objects (#96)

A selected `RankingData` enters the catalogue the way `FinOrder` does in
`Foundation/FiniteOrders.lean`: as a distinct object refining the plain set, not as an accessor row.
A ranking is selected structure, so two rankings of one carrier are two objects — the `Bool` pair in
`Foundation/RankingDataTests` is the control.

The ranked finite set carries index `Fin n`; the countably ranked set carries index `ℕ`.
-/

@[expose] public section

open CategoryTheory

namespace CasCatalogue.Foundation.Rankings

/-- The finite ranked set: an enumerated set whose carrier carries a selected ranking by `Fin n`.
The ranking is a parameter, so two rankings of one carrier are two distinct objects. -/
abbrev rankedFin (n : ℕ) (X : Type) [Encodable X]
    (r : LeanCategories.Foundation.RankingData X (Fin n)) :
    LeanCategories.Foundation.EnumeratedSetCat.{0} :=
  LeanCategories.Foundation.EnumeratedSetCat.of X

/-- The countably ranked set: an enumerated set whose carrier carries a selected ranking by `ℕ`. -/
abbrev rankedCountable (X : Type) [Encodable X]
    (r : LeanCategories.Foundation.RankingData X ℕ) :
    LeanCategories.Foundation.EnumeratedSetCat.{0} :=
  LeanCategories.Foundation.EnumeratedSetCat.of X

end CasCatalogue.Foundation.Rankings

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.ranked_fin"⟩, category := CategoryId.enumeratedSets
    name := "RankedFinSet"
    declaration := `CasCatalogue.Foundation.Rankings.rankedFin }

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.ranked_countable"⟩, category := CategoryId.enumeratedSets
    name := "RankedCountableSet"
    declaration := `CasCatalogue.Foundation.Rankings.rankedCountable }

end CasCatalogue
