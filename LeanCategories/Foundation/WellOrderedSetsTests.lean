/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.EnumeratedMonotone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Acceptance checks for #97, each on the smallest object that decides it

The five acceptance items of `lean-categories#97`, checked against the constructions in
`Foundation/WellOrderedSets.lean` and `Foundation/EnumeratedMonotone.lean`:

1. the selected well-order category, its monotone morphisms and the forgetful routes, into the
   existing `LinOrd`/`PartOrd`/`Type`, with `Ordinal` the order-type codomain;
2. the induced-order object and the `E_mon` functor, with the identity/composition laws and the
   underlying-carrier/map comparisons, `E`'s all-function morphisms untouched;
3. a selected ranking's inverse, its finite/`ω` order type and the counting-order data;
4. order type on general selected well-orders and its core-domain functor, with the witness that it
   cannot be functorial on all monotone maps;
5. the catalogue rows, checked against the registry in
   `Catalogue/Semantics/Foundation/WellOrderedSetsTests.lean`.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Foundation

/-! ## 1. The selected well-order category and its forgetful routes -/

/-- Every well-ordered set is a `LinOrd` object carrying its certificate, so `LinOrd`'s monotone
morphisms are the category's morphisms. -/
example : WellOrderedSetCat.{0} := WellOrderedSetCat.of (Fin 3)

/-- The identity of a well-ordered set is a morphism: monotone maps, not all functions, are the
morphisms. -/
example : WellOrderedSetCat.of (Fin 3) ⟶ WellOrderedSetCat.of (Fin 3) := 𝟙 _

/-- The forgetful route to sets keeps the carrier. -/
example : wellOrderedToSets.obj (WellOrderedSetCat.of (Fin 3)) = Fin 3 := rfl

/-- The route to sets is the composite through the partial orders, on the nose. -/
example : wellOrderedToSets = wellOrderedToPartialOrders ⋙ forget PartOrd := rfl

/-- The route through the linear orders keeps the selected order: its carrier is the `LinOrd`
object, not the bare type. -/
example : WellOrderedSetCat.toLinearOrder.obj (WellOrderedSetCat.of (Fin 3)) =
    LinOrd.of (Fin 3) := rfl

/-- The order-type functor's domain is the core and its codomain the ordinal category. -/
noncomputable example : Core WellOrderedSetCat.{0} ⥤ Ordinal.{0} :=
  WellOrderedSetCat.orderTypeFunctor

/-- Three points have order type three. -/
noncomputable example : WellOrderedSetCat.orderTypeFunctor.obj ⟨WellOrderedSetCat.of (Fin 3)⟩ = 3 :=
  WellOrderedSetCat.orderType_of_fin 3

/-! ## 2. The induced order and `E_mon` -/

/-- The induced well-order is available on an enumerated object. -/
noncomputable example : WellOrderedSetCat.{0} := twoPointEnumeratedSet.inducedWellOrder

/-- The induced order of the two-point set is the standard order of its ranking. -/
example (x y : Fin 2) :
    (@LE.le (Fin 2) twoPointEnumeratedSet.inducedLinearOrder.toLE x y) ↔ x ≤ y :=
  twoPointEnumeratedSet_le_iff x y

/-- Identities of `E` are monotone, so `E_mon` has the same objects and its identity. -/
example : enumeratedMonotoneProperty (𝟙 twoPointEnumeratedSet) :=
  enumeratedMonotoneProperty.id_mem _

/-- Composites of monotone maps are monotone. -/
example {X Y Z : EnumeratedSetCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : enumeratedMonotoneProperty f) (hg : enumeratedMonotoneProperty g) :
    enumeratedMonotoneProperty (f ≫ g) :=
  enumeratedMonotoneProperty.comp_mem f g hf hg

/-- The constant map on the two-point set is monotone for the selected order. -/
def twoPointConstant : twoPointEnumeratedSet ⟶ twoPointEnumeratedSet :=
  InducedCategory.homMk (TypeCat.ofHom fun _ => (0 : Fin 2))

theorem twoPointConstant_monotone : enumeratedMonotoneProperty twoPointConstant := by
  intro x x' _
  change twoPointEnumeration.encode 0 ≤ twoPointEnumeration.encode 0
  exact le_rfl

/-- The same function as a morphism of `E_mon`. -/
def twoPointConstantHom :
    (⟨twoPointEnumeratedSet⟩ : EnumeratedMonotoneSetCat.{0}) ⟶ ⟨twoPointEnumeratedSet⟩ :=
  ⟨twoPointConstant, twoPointConstant_monotone⟩

/-- `E_mon → E` retains the underlying function. -/
example : enumeratedMonotoneInclusion.map twoPointConstantHom = twoPointConstant := rfl

/-- `E_mon → WellOrderedSets` retains the underlying function of each morphism. -/
example (x : twoPointEnumeratedSet.carrier) :
    (enumeratedMonotoneToWellOrdered.map twoPointConstantHom).hom.hom x =
      twoPointConstantHom.hom.hom x :=
  enumeratedMonotoneToWellOrdered_map_apply twoPointConstantHom x

/-- The functor's composition law holds for that morphism. -/
example :
    enumeratedMonotoneToWellOrdered.map (twoPointConstantHom ≫ twoPointConstantHom) =
      enumeratedMonotoneToWellOrdered.map twoPointConstantHom ≫
        enumeratedMonotoneToWellOrdered.map twoPointConstantHom := by
  rw [Functor.map_comp]

/-- The two routes out of `E_mon` agree on the two-point object. -/
example :
    (enumeratedMonotoneInclusion ⋙ EnumeratedSetCat.forget).obj ⟨twoPointEnumeratedSet⟩ =
      (enumeratedMonotoneToWellOrdered ⋙ wellOrderedToSets).obj ⟨twoPointEnumeratedSet⟩ :=
  rfl

/-- The swap is a morphism of `E` whose square is the identity, and it is not monotone: `E_mon` is a
proper wide subcategory, and no ordered action is claimed for it. -/
example : twoPointSwap ≫ twoPointSwap = 𝟙 twoPointEnumeratedSet ∧
    ¬ enumeratedMonotoneProperty twoPointSwap :=
  ⟨twoPointSwap_comp_self, twoPointSwap_not_monotone⟩

/-! ## 3. The selected ranking, its inverse and the finite/`ω` order type -/

/-- The standard ranking of the two-point set: each point is its own index. -/
def testRanking : RankingData (Fin 2) (Fin 2) where
  rank := Equiv.refl (Fin 2)

/-- The ranking's inverse reads back the index. -/
example (i : Fin 2) :
    RankingData.rank testRanking (RankingData.unrank testRanking i) = i :=
  RankingData.rank_unrank _ i

/-- The ranking's index reads back the point. -/
example (x : Fin 2) :
    RankingData.unrank testRanking (RankingData.rank testRanking x) = x :=
  RankingData.unrank_rank _ x

/-- The ranking's iteration and indexing read through the same inverse and map. -/
example (i : Fin 2) : testRanking.nth i = testRanking.unrank i ∧
    testRanking.indexOf (testRanking.unrank i) = i := by
  constructor
  · rfl
  · exact RankingData.rank_unrank _ i

/-- A ranking by `Fin 2` gives order type `2`. -/
noncomputable example : (testRanking.wellOrderedSet).orderType = 2 :=
  testRanking.wellOrderedSet_orderType_fin

/-- The three-point ranking of the ordered-enumeration expectation has order type `3`. -/
noncomputable example :
    ((⟨Equiv.refl (Fin 3)⟩ : RankingData (Fin 3) (Fin 3)).wellOrderedSet).orderType = 3 :=
  RankingData.wellOrderedSet_orderType_fin _

/-- The counting well-order has the carrier's cardinality. -/
example : Cardinal.mk testRanking.countingWellOrder = Cardinal.mk (Fin 2) :=
  testRanking.countingWellOrder_card

/-- A ranking by `ℕ` gives order type `ω`. -/
noncomputable example :
    ((⟨Equiv.refl ℕ⟩ : RankingData ℕ ℕ).wellOrderedSet).orderType = Ordinal.omega0 :=
  RankingData.wellOrderedSet_orderType_nat _

/-- The counting well-order of a ranking by `ℕ` is `ℕ` itself. -/
example : (⟨Equiv.refl ℕ⟩ : RankingData ℕ ℕ).countingWellOrder = ℕ :=
  RankingData.countingWellOrder_nat _

/-! ## 4. Order type is not functorial on all monotone maps -/

/-- The constant map from the two-point order to the one-point order. -/
def twoPointToOnePointConstant :
    WellOrderedSetCat.of (Fin 2) ⟶ WellOrderedSetCat.of (Fin 1) :=
  InducedCategory.homMk (LinOrd.ofHom ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)

/-- So the monotone map above (`twoPointToOnePointConstant`, the constant map from the two-point
order to the one-point order) does not supply an arrow between the two order types: the order-type
functor's domain is the core, and nothing is claimed for all monotone maps. -/
theorem orderType_not_functorial_on_all_monotone :
    ¬ (WellOrderedSetCat.orderType (WellOrderedSetCat.of (Fin 2))
        ≤ WellOrderedSetCat.orderType (WellOrderedSetCat.of (Fin 1))) := by
  change ¬ (@Ordinal.type (Fin 2) (fun a b => a < b) isWellOrder_lt
      ≤ @Ordinal.type (Fin 1) (fun a b => a < b) isWellOrder_lt)
  intro h
  obtain ⟨g⟩ := Ordinal.type_le_iff'.1 h
  have hle : Fintype.card (Fin 2) ≤ Fintype.card (Fin 1) :=
    Fintype.card_le_of_injective g g.injective
  simp at hle

end LeanCategories.Foundation
