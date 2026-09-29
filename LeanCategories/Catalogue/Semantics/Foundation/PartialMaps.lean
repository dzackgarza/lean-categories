/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Partial values (the partial map classifier of `Sets`)

`Y⊥ = Y ⊔ {⊥}` classifies partial maps into `Y` (Mac Lane–Moerdijk, *Sheaves in Geometry and
Logic*, IV.3, `Ỹ`): a partial map `X ⇀ Y` is a map `X → Y⊥`, undefined where it lands in `⊥`. Its
constants `Y ↪ Y⊥` (Lean `Option.some`) are the defined values, so an asserted `s = y` of a partial
value `s` states that `s` is defined and is `y`.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.PartialMaps

open CasCatalogue.Foundation.PowerSets

/-- `Y⊥`. -/
abbrev partialValues (Y : Type) : SetsCat.{0} := Option Y

/-- The defined values `Y ↪ Y⊥`. -/
def defined (Y : Type) : (Y : SetsCat.{0}) ⟶ partialValues Y := TypeCat.ofHom some

end CasCatalogue.Foundation.PartialMaps

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.partial_values"⟩, category := CategoryId.sets, name := "Partial"
    declaration := `CasCatalogue.Foundation.PartialMaps.partialValues
    constants := some `CasCatalogue.Foundation.PartialMaps.defined }

end CasCatalogue
