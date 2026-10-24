/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import LeanCategories.ForMathlib.OrdinalNaturalSum
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Exponential
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

@[expose] public section

/-!
# Ordinals as an ordered category

Mathlib's preorder-category instance gives a unique arrow `α ⟶ β` exactly when `α ≤ β`.
The monotone map `Ordinal.card` sends each ordinal to its cardinality and each comparison
to the induced cardinal comparison. Ordinary ordinal arithmetic is supplied by Mathlib's
`Ordinal` operations; it does not preserve both order variables as a bifunctor.
-/

open CategoryTheory
open LeanCategories

namespace CasCatalogue

namespace CategoryId
def ordinals : CategoryId := ⟨"cat.ordinals"⟩
end CategoryId

namespace FunctorId
def ordinalsCard : FunctorId := ⟨"fun.ordinals.card"⟩
end FunctorId

namespace Foundation.Ordinals

universe u

def Ordinals : CategoryExpr := .atom CategoryId.ordinals
def OrdinalsCardExpr : FunctorExpr Ordinals Cardinality.Cardinalities :=
  .atomic FunctorId.ordinalsCard

/-- The thin category of ordinals and ordinal comparison. -/
abbrev ordinalsCategory : ObjCat.{u + 1, u + 1} := Cat.of Ordinal.{u}
noncomputable def ordinalsRealization : CategoryRealization Ordinals ordinalsCategory.{u} :=
  { familyFibre := none }

/-- An ordinal comparison arrow exists exactly for an ordinal inequality. -/
theorem ordinals_hom_iff (α β : Ordinal.{u}) : Nonempty (α ⟶ β) ↔ α ≤ β :=
  ⟨fun ⟨f⟩ => CategoryTheory.leOfHom f, fun h => ⟨CategoryTheory.homOfLE h⟩⟩

/-- Cardinality is monotone on ordinals, hence functorial for their thin categories. -/
def ordinalsCard : ordinalsCategory.{u} ⥤ Cardinality.cardinalitiesCategory.{u} :=
  (show Monotone (Ordinal.card : Ordinal.{u} → Cardinal.{u}) from
    fun _ _ h => Ordinal.card_le_card h).functor
noncomputable def ordinalsCardRealization :
    FunctorRealization OrdinalsCardExpr ordinalsCategory.{u}
      Cardinality.cardinalitiesCategory.{u} ordinalsCard :=
  { sourceRealization := ordinalsRealization
    targetRealization := Cardinality.cardinalitiesRealization }

/-- Ordinary ordinal sum, in the stated order of its operands. -/
def ordinalSum (α β : Ordinal.{u}) : ordinalsCategory.{u} := α + β

/-- Ordinary ordinal product, in the stated order of its operands. -/
def ordinalProduct (α β : Ordinal.{u}) : ordinalsCategory.{u} := α * β

/-- Ordinary ordinal exponentiation. -/
noncomputable def ordinalPower (α β : Ordinal.{u}) : ordinalsCategory.{u} := α ^ β

/-- Hessenberg natural sum, distinct from the ordinary `ordinal_sum`. -/
noncomputable def naturalSum (α β : Ordinal.{u}) : ordinalsCategory.{u} :=
  LeanCategories.ForMathlib.OrdinalNatural.naturalSum α β

/-- Hessenberg natural product, distinct from ordinary ordinal multiplication. -/
noncomputable def naturalProduct (α β : Ordinal.{u}) : ordinalsCategory.{u} :=
  LeanCategories.ForMathlib.OrdinalNatural.naturalProduct α β

/-- Natural sum carries a pair of ordinal comparisons to a comparison of their sums. -/
noncomputable def naturalSumMap {α α' β β' : Ordinal.{u}}
    (f : α ⟶ α') (g : β ⟶ β') : naturalSum α β ⟶ naturalSum α' β' := by
  change LeanCategories.ForMathlib.OrdinalNatural.naturalSum α β ⟶
    LeanCategories.ForMathlib.OrdinalNatural.naturalSum α' β'
  exact CategoryTheory.homOfLE
    (LeanCategories.ForMathlib.OrdinalNatural.naturalSum_mono
      (CategoryTheory.leOfHom f) (CategoryTheory.leOfHom g))

/-- Hessenberg sum is functorial jointly in its two ordinal arguments. -/
noncomputable def naturalSumFunctor :
    (ordinalsCategory.{u} × ordinalsCategory.{u}) ⥤ ordinalsCategory.{u} :=
  { obj := fun p => naturalSum p.1 p.2
    map := fun f => naturalSumMap f.1 f.2
    map_id := by intros; rfl
    map_comp := by intros; rfl }

end Foundation.Ordinals

normalized_registry .category
  { id := CategoryId.ordinals, name := "Ordinals"
    declaration := `CasCatalogue.Foundation.Ordinals.ordinalsCategory
    expression := Foundation.Ordinals.Ordinals
    realization := `CasCatalogue.Foundation.Ordinals.ordinalsRealization }
normalized_registry .functor
  { id := FunctorId.ordinalsCard, source := Foundation.Ordinals.Ordinals
    target := Foundation.Cardinality.Cardinalities
    declaration := `CasCatalogue.Foundation.Ordinals.ordinalsCard
    realization := `CasCatalogue.Foundation.Ordinals.ordinalsCardRealization
    expression := Foundation.Ordinals.OrdinalsCardExpr }
normalized_registry .object
  { id := ⟨"obj.ordinals.sum"⟩, category := CategoryId.ordinals, name := "ordinal_sum"
    declaration := `CasCatalogue.Foundation.Ordinals.ordinalSum }
normalized_registry .object
  { id := ⟨"obj.ordinals.product"⟩, category := CategoryId.ordinals, name := "ordinal_product"
    declaration := `CasCatalogue.Foundation.Ordinals.ordinalProduct }
normalized_registry .object
  { id := ⟨"obj.ordinals.power"⟩, category := CategoryId.ordinals, name := "ordinal_power"
    declaration := `CasCatalogue.Foundation.Ordinals.ordinalPower }
normalized_registry .object
  { id := ⟨"obj.ordinals.natural_sum"⟩, category := CategoryId.ordinals, name := "natural_sum"
    declaration := `CasCatalogue.Foundation.Ordinals.naturalSum }
normalized_registry .object
  { id := ⟨"obj.ordinals.natural_product"⟩, category := CategoryId.ordinals
    name := "natural_product"
    declaration := `CasCatalogue.Foundation.Ordinals.naturalProduct }
normalized_registry .morphism
  { id := ⟨"mor.ordinals.natural_sum_map"⟩, category := CategoryId.ordinals
    name := "natural_sum_map"
    declaration := `CasCatalogue.Foundation.Ordinals.naturalSumMap }

end CasCatalogue
