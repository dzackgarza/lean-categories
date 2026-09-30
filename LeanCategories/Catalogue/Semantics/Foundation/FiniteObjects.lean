/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Morphisms
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

@[expose] public section

/-!
# Named finite sets

`Fin n` in `FiniteSets` (`FintypeCat.of (Fin n)`) is `Fin n` in `Sets` with its finiteness: it
refines `obj.sets.fin` along the forgetful functor of the finiteness classifier, whose image of it
is `Fin n` (`Iso.refl`). Its elements are those of `Fin n` (`elt.sets.fin`'s numerals), and the morphisms of `FiniteSets` are
given by their graphs as in `Sets` (`FintypeCat.homMk`).
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteObjects

open CasCatalogue.Foundation.Objects CasCatalogue.Foundation.Morphisms

universe u

/-- `Fin n` as a finite set. -/
abbrev finiteFin (n : ℕ) : LeanCategories.Foundation.Mathlib.FiniteSets.{0} := FintypeCat.of (Fin n)

/-- The underlying set of `Fin n` as a finite set is `Fin n`. -/
def finiteFinIdentification (n : ℕ) :
    LeanCategories.Foundation.Mathlib.finite.{0}.forget.toFunctor.obj (finiteFin n) ≅ fin n :=
  Iso.refl _

/-- The map of finite sets `X → Y` with graph `l`, which lists each element of `X` exactly once. -/
def finiteOfGraph {X Y : FintypeCat.{u}} [DecidableEq X]
    (l : List (X × Y)) (total : ∀ x, x ∈ l.map Prod.fst) (_nodup : (l.map Prod.fst).Nodup) :
    (X : LeanCategories.Foundation.Mathlib.FiniteSets.{u}) ⟶
      (Y : LeanCategories.Foundation.Mathlib.FiniteSets.{u}) :=
  FintypeCat.homMk fun x => graphValue l x (total x)

end CasCatalogue.Foundation.FiniteObjects

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.finite_sets.fin"⟩, category := CategoryId.finiteSets, name := "Fin"
    declaration := `CasCatalogue.Foundation.FiniteObjects.finiteFin
    refines := some
      { base := ⟨"obj.sets.fin"⟩, route := #[.classifierForget ClassifierId.setsFinite]
        identification := `CasCatalogue.Foundation.FiniteObjects.finiteFinIdentification } }

normalized_registry .graphLiteral
  { id := ⟨"graph.finite_sets"⟩, category := CategoryId.finiteSets
    denotation := `CasCatalogue.Foundation.FiniteObjects.finiteOfGraph }

end CasCatalogue
