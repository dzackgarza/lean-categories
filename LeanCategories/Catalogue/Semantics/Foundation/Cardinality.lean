/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import LeanCategories.Foundation.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.ZMod.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Cardinality: the one semantic cardinality method (#53 §11)

`card : Core(Sets) ⥤ Disc(Card)` (`LeanCategories.Foundation.cardinality`) is registered once, as
the functor `fun.sets.cardinality`, and presented as the iso-invariant method `cardinality` owned
by `Sets`. Every other category reaches it through structural functors; nothing else declares a
cardinality.

Its Lean-native action runs on presented sets: `ℤ⁰` has one element and `ℤⁿ⁺¹` is countably
infinite.
-/

open CategoryTheory
open LeanCategories
open CasCatalogue.Catalogue.ConstructorRegistration

namespace CasCatalogue

namespace CategoryId
def cardinals : CategoryId := ⟨"cat.cardinals"⟩
end CategoryId

namespace FunctorId
def setsCardinality : FunctorId := ⟨"fun.sets.cardinality"⟩
end FunctorId

namespace Foundation.Cardinality

universe u

def Cardinals : CategoryExpr := .atom CategoryId.cardinals
def SetsCardinalityExpr : FunctorExpr Constructed.CoreSets Cardinals :=
  .atomic FunctorId.setsCardinality

/-- Cardinal numbers, as a discrete category. -/
abbrev cardinalsCategory : ObjCat.{u + 1, u + 1} := Cat.of (Discrete Cardinal.{u})
noncomputable def cardinalsRealization : CategoryRealization Cardinals cardinalsCategory.{u} :=
  { familyFibre := none }

/-- `card : Core(Sets) ⥤ Disc(Card)`. -/
def setsCardinality : coreSetsCategory.{u} ⥤ cardinalsCategory.{u} :=
  LeanCategories.Foundation.cardinality
noncomputable def setsCardinalityRealization :
    FunctorRealization SetsCardinalityExpr coreSetsCategory.{u} cardinalsCategory.{u}
      setsCardinality :=
  { sourceRealization := coreSetsRealization, targetRealization := cardinalsRealization }

/-- A cardinal as the language writes it: a numeral or `ℵ₀`. -/
inductive CardinalLiteral
  | finite (n : ℕ)
  | aleph0
  deriving DecidableEq, Repr

/-- Numerals are finite cardinals. -/
instance (n : ℕ) : OfNat CardinalLiteral n := ⟨.finite n⟩

/-- `ℵ₀`, as the language spells it. -/
abbrev CardinalLiteral.«ℵ₀» : CardinalLiteral := .aleph0

/-- The cardinal a literal denotes, an object of `Card`. -/
noncomputable def CardinalLiteral.denote : CardinalLiteral → cardinalsCategory.{0}
  | .finite n => ⟨n⟩
  | .aleph0 => ⟨Cardinal.aleph0⟩

/-- Distinct literals denote distinct cardinals: `n ↦ n` is injective on `ℕ` and no natural
number is `ℵ₀` (`Nat.cast_injective`, `Cardinal.natCast_lt_aleph0`). So equality of the cardinals
two literals denote is equality of the literals. -/
theorem CardinalLiteral.denote_inj {a b : CardinalLiteral} : a.denote = b.denote ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have h := congrArg Discrete.as h
  cases a with
  | finite n => cases b with
    | finite m => exact congrArg _ (Nat.cast_injective h)
    | aleph0 => exact absurd h (Cardinal.natCast_lt_aleph0 (n := n)).ne
  | aleph0 => cases b with
    | finite m => exact absurd h.symm (Cardinal.natCast_lt_aleph0 (n := m)).ne
    | aleph0 => rfl

/-- Equality of the cardinals two literals denote is decided on the literals. -/
instance CardinalLiteral.decidableEqDenote (a b : CardinalLiteral) :
    Decidable (a.denote = b.denote) :=
  decidable_of_iff (a = b) denote_inj.symm

end Foundation.Cardinality

normalized_registry .category
  { id := CategoryId.cardinals, name := "Card",
    declaration := `CasCatalogue.Foundation.Cardinality.cardinalsCategory
    expression := Foundation.Cardinality.Cardinals
    realization := `CasCatalogue.Foundation.Cardinality.cardinalsRealization }
normalized_registry .functor
  { id := FunctorId.setsCardinality, source := Constructed.CoreSets
    target := Foundation.Cardinality.Cardinals
    declaration := `CasCatalogue.Foundation.Cardinality.setsCardinality
    realization := `CasCatalogue.Foundation.Cardinality.setsCardinalityRealization
    expression := Foundation.Cardinality.SetsCardinalityExpr }
normalized_registry .literal
  { id := ⟨"lit.cardinals"⟩, category := CategoryId.cardinals
    type := `CasCatalogue.Foundation.Cardinality.CardinalLiteral
    denotation := `CasCatalogue.Foundation.Cardinality.CardinalLiteral.denote }

normalized_registry .method
  { id := ⟨"meth.cardinality"⟩, name := "cardinality", owner := Foundation.Sets
    functor := FunctorId.setsCardinality, shape := .isoInvariant }

end CasCatalogue
