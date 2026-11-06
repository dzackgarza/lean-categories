/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.Countable.Defs
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Category.LinOrd
public import LeanCategories.Foundation.Mathlib

@[expose] public section

/-!
# Finite, countable, and enumerated sets

This file uses Mathlib's `Finite`, `Countable`, and `Encodable` notions.
Countable sets form a full subcategory of types. An enumerated set retains a
chosen `Encodable` structure, while its morphisms are ordinary functions.
-/

open CategoryTheory

universe u

namespace LeanCategories.Foundation

/-- The category of countable types and all functions between them. -/
abbrev CountableSetCat :=
  ObjectProperty.FullSubcategory (C := Type u) Countable

namespace CountableSetCat

/-- Regard a type with a Mathlib `Countable` instance as a countable set. -/
abbrev of (X : Type u) [Countable X] : CountableSetCat.{u} :=
  ⟨X, inferInstance⟩

/-- The canonical inclusion of countable sets into sets. -/
abbrev incl : CountableSetCat.{u} ⥤ Type u :=
  ObjectProperty.ι _

end CountableSetCat

/-- A type equipped with a chosen Mathlib `Encodable` structure. -/
structure EnumeratedSetCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The chosen encoding into natural numbers. -/
  [enumeration : Encodable carrier]

attribute [instance] EnumeratedSetCat.enumeration

namespace EnumeratedSetCat

instance : CoeSort EnumeratedSetCat.{u} (Type u) :=
  ⟨carrier⟩

/-- Regard a type with a chosen Mathlib `Encodable` instance as an enumerated set. -/
abbrev of (X : Type u) [Encodable X] : EnumeratedSetCat.{u} :=
  ⟨X⟩

instance : Category EnumeratedSetCat.{u} :=
  inferInstanceAs (Category (InducedCategory (Type u) carrier))

/-- Forget the chosen enumeration. -/
def forget : EnumeratedSetCat.{u} ⥤ Type u where
  obj X := X.carrier
  map f := f.hom

end EnumeratedSetCat

/-- Selected standard ranking data on a type: the standard index `I` — a `Fin n` for a specified
`n`, or `ℕ` — together with the actual equivalence `rank : X ≃ I`, its inverse and the inverse laws.

This is the data research's ranking contract stores: iteration and indexing use `rank.symm`,
comparison uses the selected standard order transported through `rank`, and the order type is `n`
or `ω`. It is deliberately separate from a chosen `Encodable`: an encoding induces *an* order, but
only this structure records *which* ranking a consumer selected, and a different chosen encoding
need not preserve it. -/
structure RankingData (X : Type u) (I : Type v) [LinearOrder I] where
  /-- The selected equivalence to the standard index. -/
  rank : X ≃ I

/-- Selected ranking on the finite standard index `Fin n`. -/
abbrev FiniteRanking (X : Type u) (n : ℕ) : Type (max u 0) := RankingData X (Fin n)

/-- Selected ranking on the countably infinite standard index `ℕ`. -/
abbrev CountableRanking (X : Type u) : Type u := RankingData X ℕ

namespace RankingData

variable {X : Type u} {I : Type v} [LinearOrder I]

/-- The inverse ranking, from the standard index back to the carrier. -/
def unrank (r : RankingData X I) (i : I) : X := r.rank.symm i

/-- Iteration through the selected ranking: the element at index `i`. -/
def nth (r : RankingData X I) (i : I) : X := r.unrank i

/-- The index of an element under the selected ranking. -/
def indexOf (r : RankingData X I) (x : X) : I := r.rank x

/-- Reading back the index of an element returns the element. -/
theorem unrank_rank (r : RankingData X I) (x : X) : r.unrank (r.rank x) = x :=
  r.rank.symm_apply_apply x

/-- Reading back an element of the index returns the index. -/
theorem rank_unrank (r : RankingData X I) (i : I) : r.rank (r.unrank i) = i :=
  r.rank.apply_symm_apply i

/-- The selected order: `x ≤ y` when `rank x ≤ rank y` in the standard order of the index. -/
def le (r : RankingData X I) (x y : X) : Prop := r.rank x ≤ r.rank y

/-- The selected order is reflexive. -/
theorem le_refl (r : RankingData X I) (x : X) : r.le x x := _root_.le_rfl

/-- The selected order is transitive. -/
theorem le_trans (r : RankingData X I) {x y z : X} (h₁ : r.le x y) (h₂ : r.le y z) : r.le x z :=
  _root_.le_trans h₁ h₂

/-- The ranking-derived encoding of the carrier by its selected index, when the index is itself
encodable: an element is encoded by the encoding of its selected index. This preserves the selected
ranking, because it is read off that ranking. -/
def toEncodable (r : RankingData X I) [Encodable I] : Encodable X where
  encode x := Encodable.encode (r.rank x)
  decode n := (Encodable.decode n).map r.unrank
  encodek x := by
    simp only [Encodable.encodek]
    exact congrArg some (r.unrank_rank x)

/-- The ranking-derived encoding keeps the carrier's own selected ranking: decoding the encoding of
an element returns that element. -/
theorem toEncodable_encodek (r : RankingData X I) [Encodable I] (x : X) :
    r.toEncodable.decode (r.toEncodable.encode x) = some x :=
  r.toEncodable.encodek x

end RankingData


/-- Every finite set is countable. -/
def finiteToCountable : FintypeCat.{u} ⥤ CountableSetCat.{u} :=
  ObjectProperty.lift (Countable : ObjectProperty (Type u)) FintypeCat.incl fun X ↦ by
    change Countable X.obj
    exact @Finite.to_countable X.obj X.property

/-- Forget the chosen enumeration and retain the induced countability proof. -/
def enumeratedToCountable : EnumeratedSetCat.{u} ⥤ CountableSetCat.{u} :=
  ObjectProperty.lift (Countable : ObjectProperty (Type u)) EnumeratedSetCat.forget fun X ↦ by
    change Countable X.carrier
    exact @Encodable.countable X.carrier X.enumeration

/-- The category of countable sets and all functions, bundled for the semantic catalogue. -/
abbrev CountableSets : ObjCat.{u + 1, u} := Cat.of CountableSetCat.{u}

/-- The category of sets with a selected partial-inverse enumeration. -/
abbrev EnumeratedSets : ObjCat.{u + 1, u} := Cat.of EnumeratedSetCat.{u}

/-- Sets equipped with a selected partial order, with monotone maps as morphisms. -/
abbrev PartiallyOrderedSets : ObjCat.{u + 1, u} := Cat.of PartOrd.{u}

/-- Sets equipped with a selected linear order, with monotone maps as morphisms. -/
abbrev TotallyOrderedSets : ObjCat.{u + 1, u} := Cat.of LinOrd.{u}

/-- Forget the selected partial order, retaining the underlying set and monotone maps. -/
def partiallyOrderedToSets : PartOrd.{u} ⥤ Type u := forget PartOrd

/-- Forget the selected linear order, retaining the underlying set and monotone maps. -/
def totallyOrderedToSets : LinOrd.{u} ⥤ Type u := forget LinOrd

/-- Countability as a property classifier on sets: its total has all functions as morphisms. -/
def countableSets : Classifier Mathlib.Sets.{u} where
  total := CountableSets
  forget := CountableSetCat.incl.toCatHom

/-- A chosen partial-inverse enumeration as a structure classifier on sets. -/
def enumeratedSets : Classifier Mathlib.Sets.{u} where
  total := EnumeratedSets
  forget := EnumeratedSetCat.forget.toCatHom

end LeanCategories.Foundation
