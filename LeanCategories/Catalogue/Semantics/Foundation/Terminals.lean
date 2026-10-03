/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Objects
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# The terminal set and its universal point relationship

The one-element set `PUnit` is terminal in each universe. Its empty-diagram
limit includes the unique map from every set. The public singleton `Fin 1`
is explicitly isomorphic to it; this comparison supplies the point-domain
transport for nullary operations without changing their selected values.
-/

open CategoryTheory CategoryTheory.Limits

namespace CasCatalogue.Foundation.Terminals
universe u

/-- The terminal set in the selected universe. -/
abbrev terminal : LeanCategories.Foundation.Mathlib.Sets.{u} := PUnit.{u + 1}

/-- The unique arrow into the terminal set. -/
def terminalArrow (X : LeanCategories.Foundation.Mathlib.Sets.{u}) : X ⟶ terminal :=
  TypeCat.ofHom fun _ => PUnit.unit

/-- Uniqueness is universal, independently of a concrete input presentation. -/
theorem terminalArrow_unique (X : LeanCategories.Foundation.Mathlib.Sets.{u})
    (f : X ⟶ terminal) : f = terminalArrow X :=
  ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _

/-- The terminal object's complete empty-diagram limit, with its unique mediator. -/
def terminalLimit : LimitCone (Functor.empty (Type u)) :=
  ⟨asEmptyCone terminal, IsTerminal.ofUniqueHom terminalArrow terminalArrow_unique⟩

/-- The public singleton and this terminal set have their actual point comparison. -/
def singletonComparison : Objects.fin 1 ≅ terminal.{0} where
  hom := TypeCat.ofHom fun _ => PUnit.unit
  inv := TypeCat.ofHom fun _ => (0 : Fin 1)
  hom_inv_id := ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _
  inv_hom_id := ConcreteCategory.hom_ext _ _ fun _ => Subsingleton.elim _ _

end CasCatalogue.Foundation.Terminals

namespace CasCatalogue
normalized_registry .object
  { id := ⟨"obj.sets.terminal"⟩, category := CategoryId.sets, name := "Terminal"
    declaration := `CasCatalogue.Foundation.Terminals.terminal }
normalized_registry .morphism
  { id := ⟨"mor.sets.terminal"⟩, category := CategoryId.sets, name := "terminalArrow"
    declaration := `CasCatalogue.Foundation.Terminals.terminalArrow }
normalized_registry .limit
  { id := ⟨"lim.sets.terminal"⟩, category := CategoryId.sets, shape := "terminal"
    declaration := `CasCatalogue.Foundation.Terminals.terminalLimit }
normalized_registry .presentation
  { id := ⟨"cmp.sets.singleton_terminal"⟩, name := "singletonTerminal"
    source := ⟨"obj.sets.fin"⟩, target := ⟨"obj.sets.terminal"⟩
    declaration := `CasCatalogue.Foundation.Terminals.singletonComparison }
end CasCatalogue
