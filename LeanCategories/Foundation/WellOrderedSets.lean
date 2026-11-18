/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Sets
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Well-ordered sets, selected rankings, and order type

`WellOrderedSets` is the category of sets with a selected well-order and monotone maps: the objects
of `LinOrd` whose strict order is a well-order (`IsWellOrder`), carrying `LinOrd`'s morphisms. Its
forgetful routes are `WellOrderedSets → LinOrd → PartOrd → Sets`. The leg `LinOrd → PartOrd` is
supplied here because Mathlib has `PartOrd → Preord` and `LinOrd → Lat` but no forgetful functor
between the two ordered-set categories.

The order type of an object is `Ordinal.type` of its selected strict order. Order type is invariant
under order isomorphism only, so it is functorial on the core -- `Core WellOrderedSets ⥤ Ordinal` --
and not on all monotone maps: the constant monotone map from the two-point order to the one-point
order does not give `2 ≤ 1`.

`RankingData` is the selected ranking of an enumeration, `X ≃ Fin n` or `X ≃ ℕ`. Pulling the
standard order back along that ranking makes the very same map an order isomorphism, which fixes the
finite/`ω` order type of the ranked set and exposes the counting well-order the ranking uses.

## Source

sage-extensions `src/sage_extensions/categories/sets/set_categories.py`: `class WellOrderedSets`
("Well-ordered sets with order-preserving maps", `super_categories` the totally ordered sets, and
`ParentMethods.order_type` the ordinal the well-order represents) and `class EnumeratedSets`'s
`ParentMethods` (`ranking_map`, `le`, `order_type`, `__iter__`, `__getitem__`). The order-type
functor is `categories/functors/order_type.py`, `_OrderTypeFunctor`, whose domain is
`WellOrderedSets().Core()`, whose codomain is `Ordinals()`, and whose morphism part is
`unique_morphism`. Contract tests in `dzackgarza/research`: `test_well_ordered_sets_construct.sage`,
`test_well_order_order_type_functor_construct.sage`, `test_enumerated_sets_construct.sage`,
`test_ordered_enumerated_sets_construct.sage`, `test_sets_counting_well_order_construct.sage`.

## Search record (LC-09, LC-19)

`scripts/formalization_corpus.py search` for `WellOrderedSets`, `WellOrdered`, `well_order`,
`order_type_functor`, `wofun`, `woset ordinal`, `WellOrdering ordinal`, with whole-file reads of
`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v` and
`UniMath/CategoryTheory/Categories/Woset.v`. Nearest hits: UniMath's `wosetfuncat`, well-ordered
sets with maps "that preserve the ordering and initial segments" -- a strictly smaller morphism
class than monotone maps; its `WOSET`, "arbitrary set theoretic functions as morphisms", which this
unit's contract excludes; and cubical Agda `Cubical.Data.Ordinal.Base`, which identifies `Ord` with
`Woset` and carries no category or functor. No source supplies this category with monotone maps
or an order-type core functor, so both are built here on Mathlib's `IsWellOrder`, `Ordinal.type`,
`RelIso` and `CategoryTheory.Core`; nothing is ported.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace LeanCategories.Foundation

/-- An order isomorphism of linearly ordered types preserves the ordinal order type. This is
`Ordinal.type_eq` applied to `OrderIso.toRelIsoLT`. -/
theorem ordinal_type_congr {α β : Type u} [LinearOrder α] [LinearOrder β]
    [IsWellOrder α (· < ·)] [IsWellOrder β (· < ·)] (e : α ≃o β) :
    Ordinal.type (fun a b : α => a < b) = Ordinal.type (fun a b : β => a < b) :=
  Ordinal.type_eq.2 ⟨e.toRelIsoLT⟩

/-- An isomorphism of bundled linear orders, read as an order isomorphism: an isomorphism of
`LinOrd` is a bijective monotone map with monotone inverse. -/
noncomputable def orderIsoOfIso {X Y : LinOrd.{u}} (e : X ≅ Y) : X ≃o Y where
  toFun x := e.hom x
  invFun y := e.inv y
  left_inv x := LinOrd.inv_hom_apply e x
  right_inv y := LinOrd.hom_inv_apply e y
  map_rel_iff' {a b} := by
    change e.hom a ≤ e.hom b ↔ a ≤ b
    refine ⟨fun h => ?_, fun h => OrderHom.monotone (LinOrd.Hom.hom e.hom) h⟩
    have h' : e.inv (e.hom a) ≤ e.inv (e.hom b) :=
      OrderHom.monotone (LinOrd.Hom.hom e.inv) (by simpa using h)
    simpa using h'

/-- Well-orderedness, as a property of a bundled linear order: the strict order is a well-order. -/
abbrev IsWellOrderedLinearOrder : ObjectProperty LinOrd.{u} := fun X => IsWellOrder X (· < ·)

/-- The category of well-ordered sets: sets with a selected linear order whose strict order is a
well-order, with monotone maps. -/
abbrev WellOrderedSetCat : Type (u + 1) := IsWellOrderedLinearOrder.FullSubcategory

namespace WellOrderedSetCat

/-- The well-ordered set on a carrier with a selected linear order whose strict order is
well-founded. -/
def of (X : Type u) [LinearOrder X] [WellFoundedLT X] : WellOrderedSetCat.{u} :=
  ⟨LinOrd.of X, isWellOrder_lt⟩

/-- The carrier of a well-ordered set. -/
abbrev carrier (W : WellOrderedSetCat.{u}) : Type u := W.obj.carrier

/-- The selected strict order of a well-ordered set is a well-order. -/
theorem selected_isWellOrder (W : WellOrderedSetCat.{u}) :
    IsWellOrder W.carrier (· < ·) := W.property

/-- The forgetful functor to bundled linear orders, retaining the selected order and each monotone
map. -/
def toLinearOrder : WellOrderedSetCat.{u} ⥤ LinOrd.{u} := IsWellOrderedLinearOrder.ι

@[simp] theorem toLinearOrder_obj (W : WellOrderedSetCat.{u}) : toLinearOrder.obj W = W.obj := rfl

theorem toLinearOrder_map {W W' : WellOrderedSetCat.{u}} (f : W ⟶ W') :
    toLinearOrder.map f = f.hom := rfl

/-- The ordinal order type of the selected well-order. -/
noncomputable def orderType (W : WellOrderedSetCat.{u}) : Ordinal.{u} :=
  @Ordinal.type W.carrier (fun a b => a < b) W.property

/-- Order type is preserved by an isomorphism of well-ordered sets. -/
theorem orderType_eq_of_iso {W W' : WellOrderedSetCat.{u}} (e : W ≅ W') :
    orderType W = orderType W' := by
  have e' : W.obj ≅ W'.obj := toLinearOrder.mapIso e
  have h := @ordinal_type_congr W.carrier W'.carrier W.obj.str W'.obj.str W.property W'.property
    (orderIsoOfIso e')
  simpa [orderType, LinOrd.of] using h

/-- The order-type functor on the core of the well-ordered sets: each object is sent to the ordinal
order type of its selected well-order, and each order isomorphism to the unique comparison of the
two equal order types. -/
noncomputable def orderTypeFunctor : Core WellOrderedSetCat.{u} ⥤ Ordinal.{u} where
  obj W := orderType W.of
  map {_ _} f := homOfLE (le_of_eq (orderType_eq_of_iso f.iso))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem orderTypeFunctor_obj (W : Core WellOrderedSetCat.{u}) :
    orderTypeFunctor.obj W = orderType W.of := rfl

/-- A finite ordinal is a well-ordered set of order type `n`. -/
theorem orderType_of_fin (n : ℕ) : orderType (of (Fin n)) = n := by
  change Ordinal.type (fun a b : Fin n => a < b) = (n : Ordinal)
  exact Ordinal.type_fin n

end WellOrderedSetCat

/-- The forgetful functor from linear to partial orders, retaining the selected order and each
monotone map. Mathlib supplies `PartOrd ⥤ Preord` and `LinOrd ⥤ Lat`, so this is the missing leg of
`LinOrd → PartOrd → Sets`; it selects the same order on the same carrier, so no new mathematics is
introduced. -/
def linearOrdersToPartialOrders : LinOrd.{u} ⥤ PartOrd.{u} where
  obj X := PartOrd.of X
  map f := PartOrd.ofHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful route `WellOrderedSets → LinOrd → PartOrd`. -/
def wellOrderedToPartialOrders : WellOrderedSetCat.{u} ⥤ PartOrd.{u} :=
  WellOrderedSetCat.toLinearOrder ⋙ linearOrdersToPartialOrders

/-- The forgetful route `WellOrderedSets → LinOrd → PartOrd → Sets`: the underlying set and the
underlying function of each monotone map. -/
def wellOrderedToSets : WellOrderedSetCat.{u} ⥤ Type u :=
  wellOrderedToPartialOrders ⋙ forget PartOrd

@[simp] theorem wellOrderedToSets_obj (W : WellOrderedSetCat.{u}) :
    wellOrderedToSets.obj W = W.carrier := rfl

theorem wellOrderedToSets_map_apply {W W' : WellOrderedSetCat.{u}} (f : W ⟶ W')
    (x : W.carrier) : wellOrderedToSets.map f x = f.hom.hom x := rfl

/-- The category of well-ordered sets, bundled for the semantic catalogue. -/
abbrev WellOrderedSets : ObjCat.{u + 1, u} := Cat.of WellOrderedSetCat.{u}

/-! ## The selected order of a ranking

A `RankingData X I` is a selected equivalence to a standard index. Pulling the standard order of `I`
back along it gives the selected order, and the same map is an order isomorphism onto `I`. -/

namespace RankingData

variable {X : Type u} {I : Type v} [LinearOrder I]

/-- The order the selected ranking pulls back from the standard order on its index. -/
@[instance_reducible] noncomputable def selectedLinearOrder (r : RankingData X I) : LinearOrder X :=
  LinearOrder.lift' r.rank r.rank.injective

/-- The selected order is the ranking's pullback, on the nose. -/
theorem selectedLinearOrder_le_iff (r : RankingData X I) (x y : X) :
    @LE.le X r.selectedLinearOrder.toLE x y ↔ r.le x y := Iff.rfl

/-- The selected order has the same strict order as the ranking's pullback, on the nose. -/
theorem selectedLinearOrder_lt_iff (r : RankingData X I) (x y : X) :
    @LT.lt X r.selectedLinearOrder.toLT x y ↔ r.rank x < r.rank y := Iff.rfl

/-- A ranked set inherits well-foundedness of the index's strict order along the ranking. -/
theorem wellFoundedLT (r : RankingData X I) [WellFoundedLT I] :
    @WellFoundedLT X r.selectedLinearOrder.toLT :=
  @WellFounded.intro X (fun a b => r.selectedLinearOrder.lt a b)
    (InvImage.wf (⇑r.rank) (inferInstance : WellFoundedLT I)).apply

/-- The ranked set as a well-ordered set, with the ranking's selected order. -/
noncomputable def wellOrderedSet (r : RankingData X I) [WellFoundedLT I] :
    WellOrderedSetCat.{u} := by
  letI := r.selectedLinearOrder
  haveI := r.wellFoundedLT
  exact WellOrderedSetCat.of X

/-- The selected ranking is an order isomorphism onto the standard index, for the selected order it
induces on the carrier. This is the actual map and its relation to the chosen order: an order
isomorphism is not a bare bijection. -/
noncomputable def rankOrderIso (r : RankingData X I) :
    @OrderIso X I r.selectedLinearOrder.toLE _ where
  toFun := ⇑r.rank
  invFun := ⇑r.rank.symm
  left_inv := r.rank.left_inv
  right_inv := r.rank.right_inv
  map_rel_iff' := Iff.rfl

/-- The counting well-order of a ranking: the standard index the ranking counts with. -/
abbrev countingWellOrder (_r : RankingData X I) : Type v := I

/-- The counting well-order carries the carrier's points: the ranking is a bijection onto it. -/
def countingWellOrderEquiv (r : RankingData X I) : r.countingWellOrder ≃ X := r.rank.symm

/-- The counting well-order has the carrier's cardinality. -/
theorem countingWellOrder_card {X I : Type u} [LinearOrder I] (r : RankingData X I) :
    Cardinal.mk r.countingWellOrder = Cardinal.mk X :=
  Cardinal.mk_congr r.rank.symm

/-- The counting well-order of a ranking by `ℕ` is `ℕ` itself. -/
theorem countingWellOrder_nat (r : RankingData X ℕ) : r.countingWellOrder = ℕ := rfl

/-- The order type of a ranked set, for a ranking whose index lives in the carrier's universe, is
the order type of the counting well-order. -/
theorem wellOrderedSet_orderType {X I : Type u} [LinearOrder I] [WellFoundedLT I]
    (r : RankingData X I) :
    (r.wellOrderedSet).orderType = Ordinal.type (fun a b : I => a < b) := by
  let inst := r.selectedLinearOrder
  exact @ordinal_type_congr X I inst ‹LinearOrder I›
    (r.wellOrderedSet).property (isWellOrder_lt : IsWellOrder I (· < ·)) r.rankOrderIso

/-- A finite ranking gives order type `n`: the carrier is finite with `n` points. -/
theorem wellOrderedSet_orderType_fin {n : ℕ} (r : RankingData X (Fin n)) :
    (r.wellOrderedSet).orderType = n := by
  let inst := r.selectedLinearOrder
  have hX : Fintype X := r.fintypeCarrier ⟨inferInstance⟩
  have h : Ordinal.type (fun a b : X => a < b) = Fintype.card X :=
    @Ordinal.type_fintype X (fun a b : X => a < b) (r.wellOrderedSet).property hX
  exact h.trans (by rw [Fintype.card_congr r.rank, Fintype.card_fin])

end RankingData

/-- The well-ordered sets as the property subcategory of the linear orders: the classifier whose
total is the category of well-ordered sets and whose forgetful functor is `toLinearOrder`. This is
`Classifier.ofProperty` at the property that defines the objects, so the classifier, its total and
its forgetful functor are not restated here. -/
def wellOrderedSets : Classifier TotallyOrderedSets.{u} :=
  Classifier.ofProperty IsWellOrderedLinearOrder

@[simp] theorem wellOrderedSets_total : wellOrderedSets.total = WellOrderedSets.{u} := rfl

@[simp] theorem wellOrderedSets_forget :
    wellOrderedSets.forget = WellOrderedSetCat.toLinearOrder.toCatHom := rfl

end LeanCategories.Foundation
