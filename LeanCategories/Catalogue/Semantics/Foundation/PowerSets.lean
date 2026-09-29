/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public import Mathlib.Order.Category.BoolAlg
public import Mathlib.Order.Category.LinOrd
public import Mathlib.Order.SymmDiff
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Set
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

/-!
# Power sets, truth values and orders (SPEC.md, "Finite sets", "Set comprehensions")

* `Ω = Prop`, the truth values of `Sets` (its subobject classifier), with `⊤ : 1 → Ω`.
* Equality `= : X × X → Ω`, the characteristic map of the diagonal `X ↪ X × X`.
* `𝒫(X) = Set X`, the power object of `X` (Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*,
  IV.1): membership `X × 𝒫 X → Ω`, the transpose of a predicate `X → Ω` (the subset it
  classifies), the extent of a subset (the set of its members), `∅`, singletons, the terminal maps
  `X → 1` and images `(X → Y) ↦ f(X) ∈ 𝒫 Y`. It is refined by the Boolean algebra `𝒫(X)` in
  `BooleanAlgebras` (Mathlib `BoolAlg`), whose operations are `∪ ∩ \ △` and whose order `⊆` lands
  in `Ω`.
* `LinearOrders` (Mathlib `LinOrd`) refine `ℕ, ℤ, ℚ, ℝ`, with the relations `≤` and `<` into `Ω`.

The families take their sets as types, ascribed to `Sets` at their boundary, so that the instances
of `Set X` and of the orders are found.
-/

open CategoryTheory

namespace CasCatalogue

namespace CategoryId
def booleanAlgebras : CategoryId := ⟨"cat.boolean_algebras"⟩
def linearOrders : CategoryId := ⟨"cat.linear_orders"⟩
end CategoryId

namespace FunctorId
def booleanAlgebrasForget : FunctorId := ⟨"fun.boolean_algebras.forget"⟩
def linearOrdersForget : FunctorId := ⟨"fun.linear_orders.forget"⟩
end FunctorId

namespace Foundation.PowerSets

open CasCatalogue.Foundation.Objects CasCatalogue.Algebra.NamedRings
open CasCatalogue.Algebra.NumberSystems

universe u

/-- The category of sets. -/
abbrev SetsCat := LeanCategories.Foundation.Mathlib.Sets

def BooleanAlgebrasExpr : CategoryExpr := .atom CategoryId.booleanAlgebras
def LinearOrdersExpr : CategoryExpr := .atom CategoryId.linearOrders

/-- Boolean algebras. -/
def BooleanAlgebras : LeanCategories.ObjCat.{u + 1, u} := Cat.of BoolAlg.{u}

/-- Linear orders. -/
def LinearOrders : LeanCategories.ObjCat.{u + 1, u} := Cat.of LinOrd.{u}

noncomputable def booleanAlgebrasRealization :
    CategoryRealization BooleanAlgebrasExpr BooleanAlgebras.{u} := {}
noncomputable def linearOrdersRealization :
    CategoryRealization LinearOrdersExpr LinearOrders.{u} := {}

/-- The underlying set of a Boolean algebra. -/
def booleanAlgebrasForget : BooleanAlgebras.{u} ⟶ SetsCat.{u} := (forget BoolAlg.{u}).toCatHom
/-- The underlying set of a linear order. -/
def linearOrdersForget : LinearOrders.{u} ⟶ SetsCat.{u} := (forget LinOrd.{u}).toCatHom

def BooleanAlgebrasForgetExpr : FunctorExpr BooleanAlgebrasExpr Foundation.Sets :=
  .atomic FunctorId.booleanAlgebrasForget
def LinearOrdersForgetExpr : FunctorExpr LinearOrdersExpr Foundation.Sets :=
  .atomic FunctorId.linearOrdersForget

noncomputable def booleanAlgebrasForgetRealization :
    FunctorRealization BooleanAlgebrasForgetExpr BooleanAlgebras.{u} SetsCat.{u}
      booleanAlgebrasForget.toFunctor :=
  { sourceRealization := booleanAlgebrasRealization
    targetRealization := CasCatalogue.Foundation.CatalogueRegistration.setsRealization }
noncomputable def linearOrdersForgetRealization :
    FunctorRealization LinearOrdersForgetExpr LinearOrders.{u} SetsCat.{u}
      linearOrdersForget.toFunctor :=
  { sourceRealization := linearOrdersRealization
    targetRealization := CasCatalogue.Foundation.CatalogueRegistration.setsRealization }

/-- `Ω`, the truth values. -/
abbrev omega : SetsCat.{0} := Prop

/-- `⊤ : 1 → Ω`. -/
def truth : fin 1 ⟶ omega := TypeCat.ofHom fun _ => True

/-- `𝒫(X)`. -/
abbrev powerSet (X : Type) : SetsCat.{0} := Set X

/-- Membership `X × 𝒫 X → Ω`. -/
def member (X : Type) : (X × powerSet X : SetsCat.{0}) ⟶ omega :=
  TypeCat.ofHom fun p => p.1 ∈ p.2

/-- Equality `X × X → Ω`, the characteristic map of the diagonal. -/
def equality (X : Type) : (X × X : SetsCat.{0}) ⟶ omega :=
  TypeCat.ofHom fun p => p.1 = p.2

/-- The subset a predicate `X → Ω` classifies, as an element of `𝒫 X`. -/
def transpose (X : Type) (P : (X : SetsCat.{0}) ⟶ omega) : fin 1 ⟶ powerSet X :=
  TypeCat.ofHom fun _ => {x | ConcreteCategory.hom (C := Type) P x}

/-- The members of a subset `A ∈ 𝒫 X`, as a set. -/
abbrev extent (X : Type) (A : fin 1 ⟶ powerSet X) : SetsCat.{0} :=
  {x : X // x ∈ ConcreteCategory.hom (C := Type) A 0}

/-- `∅ ∈ 𝒫 X`. -/
def empty (X : Type) : fin 1 ⟶ powerSet X := TypeCat.ofHom fun _ => ∅

/-- `x ↦ {x}`, `X → 𝒫 X`. -/
def singleton (X : Type) : (X : SetsCat.{0}) ⟶ powerSet X := TypeCat.ofHom fun x => {x}

/-- The terminal map `X → 1`. -/
def terminal (X : Type) : (X : SetsCat.{0}) ⟶ fin 1 := TypeCat.ofHom fun _ => 0

/-- The image `f(X) ∈ 𝒫 Y` of `f : X → Y`. -/
def image (X Y : Type) (f : (X : SetsCat.{0}) ⟶ (Y : SetsCat.{0})) : fin 1 ⟶ powerSet Y :=
  TypeCat.ofHom fun _ => Set.range (ConcreteCategory.hom (C := Type) f)

/-- `𝒫(X)` as a Boolean algebra. -/
abbrev boolPowerSet (X : Type) : BooleanAlgebras.{0} := BoolAlg.of (Set X)

/-- The underlying set of the Boolean algebra `𝒫(X)` is `𝒫(X)`. -/
def boolPowerSetIdentification (X : Type) : (powerSet X : SetsCat.{0}) ≅ powerSet X := Iso.refl _

/-- A Boolean algebra as a `BoolAlg`, and its underlying type. -/
abbrev asBool (B : BooleanAlgebras.{0}) : BoolAlg.{0} := B
abbrev boolCarrier (B : BooleanAlgebras.{0}) : Type := asBool B

/-- `∪`, the join. -/
def union (B : BooleanAlgebras.{0}) :
    (boolCarrier B × boolCarrier B : SetsCat.{0}) ⟶ (boolCarrier B : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 ⊔ p.2
/-- `∩`, the meet. -/
def inter (B : BooleanAlgebras.{0}) :
    (boolCarrier B × boolCarrier B : SetsCat.{0}) ⟶ (boolCarrier B : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 ⊓ p.2
/-- `\`, the difference. -/
def diff (B : BooleanAlgebras.{0}) :
    (boolCarrier B × boolCarrier B : SetsCat.{0}) ⟶ (boolCarrier B : SetsCat.{0}) :=
  TypeCat.ofHom fun p => p.1 \ p.2
/-- `△`, the symmetric difference. -/
def symmDiff (B : BooleanAlgebras.{0}) :
    (boolCarrier B × boolCarrier B : SetsCat.{0}) ⟶ (boolCarrier B : SetsCat.{0}) :=
  TypeCat.ofHom fun p => _root_.symmDiff p.1 p.2
/-- `⊆`, the order, into `Ω`. -/
def subset (B : BooleanAlgebras.{0}) : (boolCarrier B × boolCarrier B : SetsCat.{0}) ⟶ omega :=
  TypeCat.ofHom fun p => p.1 ≤ p.2

/-- A linear order as a `LinOrd`, and its underlying type. -/
abbrev asOrder (L : LinearOrders.{0}) : LinOrd.{0} := L
abbrev orderCarrier (L : LinearOrders.{0}) : Type := asOrder L

/-- `≤`, into `Ω`. -/
def le (L : LinearOrders.{0}) : (orderCarrier L × orderCarrier L : SetsCat.{0}) ⟶ omega :=
  TypeCat.ofHom fun p => p.1 ≤ p.2
/-- `<`, into `Ω`. -/
def lt (L : LinearOrders.{0}) : (orderCarrier L × orderCarrier L : SetsCat.{0}) ⟶ omega :=
  TypeCat.ofHom fun p => p.1 < p.2

/-- `ℕ, ℤ, ℚ, ℝ` as linear orders, and their underlying sets. -/
abbrev orderNaturals : LinearOrders.{0} := LinOrd.of ℕ
abbrev orderIntegers : LinearOrders.{0} := LinOrd.of ℤ
abbrev orderRationals : LinearOrders.{0} := LinOrd.of ℚ
noncomputable abbrev orderReals : LinearOrders.{0} := LinOrd.of ℝ
def orderNaturalsIdentification : (naturals : SetsCat.{0}) ≅ naturals := Iso.refl _
def orderIntegersIdentification : (integers : SetsCat.{0}) ≅ integers := Iso.refl _
def orderRationalsIdentification : (rationals : SetsCat.{0}) ≅ rationals := Iso.refl _
def orderRealsIdentification : (reals : SetsCat.{0}) ≅ reals := Iso.refl _

end Foundation.PowerSets

open Foundation.PowerSets

normalized_registry .category
  { id := CategoryId.booleanAlgebras, name := "BooleanAlgebras"
    declaration := `CasCatalogue.Foundation.PowerSets.BooleanAlgebras
    expression := BooleanAlgebrasExpr
    realization := `CasCatalogue.Foundation.PowerSets.booleanAlgebrasRealization }

normalized_registry .category
  { id := CategoryId.linearOrders, name := "LinearOrders"
    declaration := `CasCatalogue.Foundation.PowerSets.LinearOrders
    expression := LinearOrdersExpr
    realization := `CasCatalogue.Foundation.PowerSets.linearOrdersRealization }

normalized_registry .functor
  { id := FunctorId.booleanAlgebrasForget, source := BooleanAlgebrasExpr, target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.PowerSets.booleanAlgebrasForget
    realization := `CasCatalogue.Foundation.PowerSets.booleanAlgebrasForgetRealization
    expression := BooleanAlgebrasForgetExpr, structural := true }

normalized_registry .functor
  { id := FunctorId.linearOrdersForget, source := LinearOrdersExpr, target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.PowerSets.linearOrdersForget
    realization := `CasCatalogue.Foundation.PowerSets.linearOrdersForgetRealization
    expression := LinearOrdersForgetExpr, structural := true }

normalized_registry .object
  { id := ⟨"obj.sets.truth_values"⟩, category := CategoryId.sets, name := "Ω"
    declaration := `CasCatalogue.Foundation.PowerSets.omega }

normalized_registry .object
  { id := ⟨"obj.sets.power_set"⟩, category := CategoryId.sets, name := "𝒫"
    declaration := `CasCatalogue.Foundation.PowerSets.powerSet }

normalized_registry .object
  { id := ⟨"obj.boolean_algebras.power_set"⟩, category := CategoryId.booleanAlgebras, name := "𝒫"
    declaration := `CasCatalogue.Foundation.PowerSets.boolPowerSet
    refines := some
      { base := ⟨"obj.sets.power_set"⟩, route := #[.functor FunctorId.booleanAlgebrasForget]
        identification := `CasCatalogue.Foundation.PowerSets.boolPowerSetIdentification } }

normalized_registry .powerObject
  { id := ⟨"pow.sets"⟩, object := ⟨"obj.sets.power_set"⟩, omega := ⟨"obj.sets.truth_values"⟩
    truth := `CasCatalogue.Foundation.PowerSets.truth
    member := `CasCatalogue.Foundation.PowerSets.member
    transpose := `CasCatalogue.Foundation.PowerSets.transpose
    extent := `CasCatalogue.Foundation.PowerSets.extent
    empty := `CasCatalogue.Foundation.PowerSets.empty
    singleton := `CasCatalogue.Foundation.PowerSets.singleton
    terminal := `CasCatalogue.Foundation.PowerSets.terminal
    image := `CasCatalogue.Foundation.PowerSets.image
    union := "∪" }

normalized_registry .operation
  { id := ⟨"op.boolean_algebras.union"⟩, category := CategoryId.booleanAlgebras, name := "∪"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.union }
normalized_registry .operation
  { id := ⟨"op.boolean_algebras.inter"⟩, category := CategoryId.booleanAlgebras, name := "∩"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.inter }
normalized_registry .operation
  { id := ⟨"op.boolean_algebras.diff"⟩, category := CategoryId.booleanAlgebras, name := "\\"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.diff }
normalized_registry .operation
  { id := ⟨"op.boolean_algebras.symm_diff"⟩, category := CategoryId.booleanAlgebras, name := "△"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.symmDiff }
normalized_registry .operation
  { id := ⟨"op.boolean_algebras.subset"⟩, category := CategoryId.booleanAlgebras, name := "⊆"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.subset
    result := some ⟨"obj.sets.truth_values"⟩ }

normalized_registry .object
  { id := ⟨"obj.linear_orders.naturals"⟩, category := CategoryId.linearOrders, name := "ℕ"
    declaration := `CasCatalogue.Foundation.PowerSets.orderNaturals
    refines := some
      { base := ⟨"obj.sets.naturals"⟩, route := #[.functor FunctorId.linearOrdersForget]
        identification := `CasCatalogue.Foundation.PowerSets.orderNaturalsIdentification } }
normalized_registry .object
  { id := ⟨"obj.linear_orders.integers"⟩, category := CategoryId.linearOrders, name := "ℤ"
    declaration := `CasCatalogue.Foundation.PowerSets.orderIntegers
    refines := some
      { base := ⟨"obj.sets.integers"⟩, route := #[.functor FunctorId.linearOrdersForget]
        identification := `CasCatalogue.Foundation.PowerSets.orderIntegersIdentification } }
normalized_registry .object
  { id := ⟨"obj.linear_orders.rationals"⟩, category := CategoryId.linearOrders, name := "ℚ"
    declaration := `CasCatalogue.Foundation.PowerSets.orderRationals
    refines := some
      { base := ⟨"obj.sets.rationals"⟩, route := #[.functor FunctorId.linearOrdersForget]
        identification := `CasCatalogue.Foundation.PowerSets.orderRationalsIdentification } }
normalized_registry .object
  { id := ⟨"obj.linear_orders.reals"⟩, category := CategoryId.linearOrders, name := "ℝ"
    declaration := `CasCatalogue.Foundation.PowerSets.orderReals
    refines := some
      { base := ⟨"obj.sets.reals"⟩, route := #[.functor FunctorId.linearOrdersForget]
        identification := `CasCatalogue.Foundation.PowerSets.orderRealsIdentification } }

normalized_registry .operation
  { id := ⟨"op.linear_orders.le"⟩, category := CategoryId.linearOrders, name := "≤"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.le
    result := some ⟨"obj.sets.truth_values"⟩ }
normalized_registry .operation
  { id := ⟨"op.linear_orders.lt"⟩, category := CategoryId.linearOrders, name := "<"
    arity := 2, declaration := `CasCatalogue.Foundation.PowerSets.lt
    result := some ⟨"obj.sets.truth_values"⟩ }

normalized_registry .morphism
  { id := ⟨"mor.sets.equality"⟩, category := CategoryId.sets, name := "="
    declaration := `CasCatalogue.Foundation.PowerSets.equality }

end CasCatalogue
