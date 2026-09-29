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

`(-)⊥` is a monad (Lean `Option`): a map applied to a partial value is defined where the value is
(`lift`, `liftLeft`, `liftRight`: its action on maps, with the strengths `X⊥ × Y → (X × Y)⊥` and
`X × Y⊥ → (X × Y)⊥` composed in), and a partial partial value is defined where both are (`join`).
-/

open CategoryTheory

namespace CasCatalogue.Foundation.PartialMaps

open CasCatalogue.Foundation.PowerSets

/-- `Y⊥`. -/
abbrev partialValues (Y : Type) : SetsCat.{0} := Option Y

/-- The defined values `Y ↪ Y⊥`. -/
def defined (Y : Type) : (Y : SetsCat.{0}) ⟶ partialValues Y := TypeCat.ofHom some

/-- `f⊥ : X⊥ → Z⊥`. -/
def lift (X Z : Type) (f : (X : SetsCat.{0}) ⟶ (Z : SetsCat.{0})) :
    partialValues X ⟶ partialValues Z :=
  TypeCat.ofHom fun x => x.map (ConcreteCategory.hom (C := Type) f)

/-- `f : X × Y → Z` on a partial first argument, `X⊥ × Y → Z⊥`. -/
def liftLeft (X Y Z : Type) (f : (X × Y : SetsCat.{0}) ⟶ (Z : SetsCat.{0})) :
    (partialValues X × Y : SetsCat.{0}) ⟶ partialValues Z :=
  TypeCat.ofHom fun p => p.1.map fun x => ConcreteCategory.hom (C := Type) f (x, p.2)

/-- `f : X × Y → Z` on a partial second argument, `X × Y⊥ → Z⊥`. -/
def liftRight (X Y Z : Type) (f : (X × Y : SetsCat.{0}) ⟶ (Z : SetsCat.{0})) :
    (X × partialValues Y : SetsCat.{0}) ⟶ partialValues Z :=
  TypeCat.ofHom fun p => p.2.map fun y => ConcreteCategory.hom (C := Type) f (p.1, y)

/-- `Z⊥⊥ → Z⊥`, defined where both are. -/
def join (Z : Type) : partialValues (Option Z) ⟶ partialValues Z :=
  TypeCat.ofHom fun z => z.bind id

end CasCatalogue.Foundation.PartialMaps

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.partial_values"⟩, category := CategoryId.sets, name := "Partial"
    declaration := `CasCatalogue.Foundation.PartialMaps.partialValues
    constants := some `CasCatalogue.Foundation.PartialMaps.defined }

normalized_registry .morphism
  { id := ⟨"mor.sets.partial_lift"⟩, category := CategoryId.sets, name := "lift ⊥"
    declaration := `CasCatalogue.Foundation.PartialMaps.lift }

normalized_registry .morphism
  { id := ⟨"mor.sets.partial_lift_left"⟩, category := CategoryId.sets, name := "lift ⊥ ×"
    declaration := `CasCatalogue.Foundation.PartialMaps.liftLeft }

normalized_registry .morphism
  { id := ⟨"mor.sets.partial_lift_right"⟩, category := CategoryId.sets, name := "lift × ⊥"
    declaration := `CasCatalogue.Foundation.PartialMaps.liftRight }

normalized_registry .morphism
  { id := ⟨"mor.sets.partial_join"⟩, category := CategoryId.sets, name := "join ⊥"
    declaration := `CasCatalogue.Foundation.PartialMaps.join }

end CasCatalogue
