/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.PowerSets

@[expose] public section

/-!
# Selected ordinary and reverse orders on finite ordinals

Mathlib's `LinOrd.of` and `OrderDual` supply the two actual linear orders.
Both are carried by the preexisting `Fin n`; the existing structural functor
`linearOrdersForget` forgets precisely the selected order. No cardinality or
order operation is redeclared here.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteOrders

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- The ordinary selected linear order on `Fin n`. -/
abbrev ordinary (n : ℕ) : LinearOrders.{0} := LinOrd.of (Fin n)

/-- The reverse selected linear order on the same ordinal carrier. -/
abbrev reverse (n : ℕ) : LinearOrders.{0} := LinOrd.of (OrderDual (Fin n))

/-- The actual forgetful functor retains the original finite ordinal. -/
def ordinaryCarrier (n : ℕ) : linearOrdersForget.toFunctor.obj (ordinary n) ≅ fin n :=
  Iso.refl _

/-- Reversing the order does not change the carrier. -/
def reverseCarrier (n : ℕ) : linearOrdersForget.toFunctor.obj (reverse n) ≅ fin n :=
  Iso.refl _

theorem ordinary_five_zero_le_one : (0 : orderCarrier (ordinary 5)) ≤ 1 := by decide

theorem reverse_five_not_zero_le_one : ¬ (0 : orderCarrier (reverse 5)) ≤ 1 := by decide

/-- The selected relations are distinct even though their carrier is identical. -/
theorem five_relations_distinct :
    (fun a b : Fin 5 => @LE.le (Fin 5) (inferInstance : LE (orderCarrier (ordinary 5))) a b) ≠
      (fun a b : Fin 5 => @LE.le (Fin 5) (inferInstance : LE (orderCarrier (reverse 5))) a b) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  exact reverse_five_not_zero_le_one (h01 ▸ ordinary_five_zero_le_one)

theorem ordinary_carrier_card (n : ℕ) :
    Cardinal.mk (linearOrdersForget.toFunctor.obj (ordinary n)) = n := by
  change Cardinal.mk (Fin n) = n
  simp

theorem reverse_carrier_card (n : ℕ) :
    Cardinal.mk (linearOrdersForget.toFunctor.obj (reverse n)) = n := by
  change Cardinal.mk (Fin n) = n
  simp

end CasCatalogue.Foundation.FiniteOrders

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.linear_orders.fin_ordinary"⟩, category := CategoryId.linearOrders
    name := "FinOrder", declaration := `CasCatalogue.Foundation.FiniteOrders.ordinary }

normalized_registry .object
  { id := ⟨"obj.linear_orders.fin_reverse"⟩, category := CategoryId.linearOrders
    name := "ReverseFinOrder", declaration := `CasCatalogue.Foundation.FiniteOrders.reverse }

end CasCatalogue
