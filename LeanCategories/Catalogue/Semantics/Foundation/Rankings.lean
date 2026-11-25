/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import LeanCategories.Foundation.Sets
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration

/-!
# Ranked enumerated sets as catalogue objects (#96)

A selected `RankingData` enters the catalogue the way `FinOrder` does in
`Foundation/FiniteOrders.lean`: as an object of the enumerated-set category whose *chosen encoding
is that ranking*, not as an accessor row. `rankedFin` is the object of
`RankingData.toEncodableFin` (encode by the value of the selected `Fin n` index, decode by the same
inverse with the bound checked); `rankedCountable` is the object of
`RankingData.toEncodableNat` (encode by `rank` itself, decode by its inverse). Two rankings of one
carrier are therefore two different selected encodings of two different objects, and
`Foundation/RankingDataTests.lean` separates them by `encode`.

The ranking contract has four operations, `rank`, `indexOf`, `nth` and the selected order `≤`, and
each is a row of this category, naming the `EnumeratedSetCat` morphism that reads the *selected*
encoding:

* `EnumeratedSetCat.indexMap` (`rank`, `indexOf`): `X ⟶ of ℕ`, the value of the selected index.
* `EnumeratedSetCat.nthMap` (`nth`): `of (realizedPositions X) ⟶ X`, the inverse of `indexMap` at a
  realized position. A chosen `Encodable` realizes only the positions its decoder returns, so the
  operand object is that position set (`obj.enumerated_sets.realized_positions`) and not all of
  `ℕ`: `nth` exists where its structure exists (LC-16) and is total there, holding the position's
  own evidence. On a ranking-derived object the realized positions are the index
  (`nthMap_rankedFin`, `nthMap_rankedNat`).
* `EnumeratedSetCat.leMap` (`≤`): `of (X × X) ⟶ of Prop`, the comparison of the two indices.

One row serves both ranked objects: the registry binds a surface name once per registered category
(`Registry/Semantic.lean`, `validateOperation`), while the finite and the countably ranked object
differ in their selected index, not in the name of their index map. The agreement data are the
theorems `indexMap_rankedFin`, `indexMap_rankedCountable`, `nthMap_rankedFin`, `nthMap_rankedNat`,
`indexMap_nthMap_rankedFin`, `indexMap_nthMap_rankedNat`, `leMap_rankedFin` and
`leMap_rankedCountable` below: on the finite object each map is the `Fin n` ranking's value or its
inverse, on the countable object the `ℕ` ranking itself, and each preserves the selected order by
`RankingData.toEncodableFin_le_iff` / `RankingData.toEncodableNat_le_iff`.

The order types of the two selected indices are the classification of
`RankingData.SelectedOrderType` (`orderType_rankedFin`, `orderType_rankedCountable`): `n` for the
finite object and `ω` for the countable one.
-/

@[expose] public section

open CategoryTheory

namespace CasCatalogue.Foundation.Rankings

open LeanCategories.Foundation

/-- The finite ranked set: the enumerated object whose chosen encoding *is* the selected finite
ranking, encoded by the value of the index with the bound checked on decoding. The ranking is a
parameter and reaches the object through its encoding, so two rankings of one carrier are two
objects. -/
noncomputable abbrev rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) :
    EnumeratedSetCat.{0} :=
  @EnumeratedSetCat.mk X r.toEncodableFin

/-- The countably ranked set: the enumerated object whose chosen encoding *is* the selected
countable ranking, encoded by `rank` and decoded by its inverse. -/
noncomputable abbrev rankedCountable (X : Type) (r : RankingData X ℕ) : EnumeratedSetCat.{0} :=
  @EnumeratedSetCat.mk X r.toEncodableNat

/-- The standard index `ℕ` as an enumerated object: the target of the index map. -/
noncomputable abbrev naturalsObj : EnumeratedSetCat.{0} := EnumeratedSetCat.of ℕ

/-- The positions a chosen encoding realizes, as an object of the category: the operand of `nth`.
`nth` is total on this object and nowhere else, because a chosen encoding realizes only the
positions its decoder returns. -/
noncomputable abbrev positionsObj (X : EnumeratedSetCat.{0}) : EnumeratedSetCat.{0} :=
  EnumeratedSetCat.of (EnumeratedSetCat.realizedPositions X)

/-- On the finite ranked object the index row is the value of the selected `Fin n` ranking. -/
theorem indexMap_rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) (x : X) :
    (EnumeratedSetCat.indexMap (rankedFin n X r)).hom x = (r.rank x).val := rfl

/-- On the countably ranked object the index row is the selected `ℕ` ranking itself. -/
theorem indexMap_rankedCountable (X : Type) (r : RankingData X ℕ) (x : X) :
    (EnumeratedSetCat.indexMap (rankedCountable X r)).hom x = r.rank x := rfl

/-- On the finite ranked object, `nth` at a position below the bound is the ranking's inverse: the
realized positions are exactly the index `Fin n`. -/
theorem nthMap_rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) {m : ℕ} (h : m < n) :
    (EnumeratedSetCat.nthMap (rankedFin n X r)).hom
        ⟨m, RankingData.toEncodableFin_decode_isSome r h⟩ = r.unrank ⟨m, h⟩ := by
  rw [EnumeratedSetCat.nthMap_apply]
  exact Option.get_of_eq_some _ (RankingData.toEncodableFin_decode_of_lt r h)

/-- On the countably ranked object, `nth` at every position is the ranking's inverse: every position
is realized. -/
theorem nthMap_rankedNat (X : Type) (r : RankingData X ℕ) (m : ℕ) :
    (EnumeratedSetCat.nthMap (rankedCountable X r)).hom
        ⟨m, by rw [RankingData.toEncodableNat_decode]; rfl⟩ = r.unrank m := by
  rw [EnumeratedSetCat.nthMap_apply]
  exact Option.get_of_eq_some _ (RankingData.toEncodableNat_decode r m)

/-- The finite ranked object's `nth` and index map are mutually inverse at every point: the point at
a point's own position is that point, and indexing it again returns its index. -/
theorem indexMap_nthMap_rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) (x : X) :
    (EnumeratedSetCat.indexMap (rankedFin n X r)).hom
        ((EnumeratedSetCat.nthMap (rankedFin n X r)).hom
          ⟨(r.rank x).val, RankingData.toEncodableFin_decode_isSome r (r.rank x).isLt⟩) =
      (r.rank x).val := by
  have hnth : (EnumeratedSetCat.nthMap (rankedFin n X r)).hom
        ⟨(r.rank x).val, RankingData.toEncodableFin_decode_isSome r (r.rank x).isLt⟩ =
      r.unrank (r.rank x) := by
    rw [EnumeratedSetCat.nthMap_apply]
    refine Option.get_of_eq_some _ ?_
    rw [RankingData.toEncodableFin_decode_of_lt r (r.rank x).isLt, Fin.eta]
  rw [hnth, RankingData.unrank_rank, EnumeratedSetCat.indexMap_apply,
    RankingData.toEncodableFin_encode]

/-- The countably ranked object's `nth` and index map are mutually inverse at every point. -/
theorem indexMap_nthMap_rankedNat (X : Type) (r : RankingData X ℕ) (x : X) :
    (EnumeratedSetCat.indexMap (rankedCountable X r)).hom
        ((EnumeratedSetCat.nthMap (rankedCountable X r)).hom
          ⟨r.rank x, by rw [RankingData.toEncodableNat_decode]; rfl⟩) =
      r.rank x := by
  have hnth : (EnumeratedSetCat.nthMap (rankedCountable X r)).hom
        ⟨r.rank x, by rw [RankingData.toEncodableNat_decode]; rfl⟩ = r.unrank (r.rank x) := by
    rw [EnumeratedSetCat.nthMap_apply]
    exact Option.get_of_eq_some _ (RankingData.toEncodableNat_decode r (r.rank x))
  rw [hnth, RankingData.unrank_rank, EnumeratedSetCat.indexMap_apply,
    RankingData.toEncodableNat_encode]

/-- The selected order row on the finite ranked object is the selected ranking's order. -/
theorem leMap_rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) (x y : X) :
    (EnumeratedSetCat.leMap (rankedFin n X r)).hom (x, y) ↔ r.le x y :=
  Iff.rfl

/-- The selected order row on the countably ranked object is the selected ranking's order. -/
theorem leMap_rankedCountable (X : Type) (r : RankingData X ℕ) (x y : X) :
    (EnumeratedSetCat.leMap (rankedCountable X r)).hom (x, y) ↔ r.le x y :=
  Iff.rfl

/-- The standard finite ordinal `Fin n` as a ranked enumerated object: its ranking is the identity,
so a point is its own index, `nth` is the identity where the bound holds, and its order type is `n`.
This is the object the ordered-enumeration expectation reads. -/
noncomputable def rankedOrdinal (n : ℕ) : EnumeratedSetCat.{0} :=
  rankedFin n (Fin n) ⟨Equiv.refl (Fin n)⟩

/-- The standard finite ordinal's index map is its own value: the point `i` has index `i`. -/
theorem indexMap_rankedOrdinal (n : ℕ) (i : Fin n) :
    (EnumeratedSetCat.indexMap (rankedOrdinal n)).hom i = i.val :=
  RankingData.toEncodableFin_encode ⟨Equiv.refl (Fin n)⟩ i

/-- The standard finite ordinal's `nth` at a position inside the bound is that position. -/
theorem nthMap_rankedOrdinal (n : ℕ) {m : ℕ} (h : m < n) :
    (EnumeratedSetCat.nthMap (rankedOrdinal n)).hom
        ⟨m, RankingData.toEncodableFin_decode_isSome ⟨Equiv.refl (Fin n)⟩ h⟩ = ⟨m, h⟩ :=
  nthMap_rankedFin n (Fin n) ⟨Equiv.refl (Fin n)⟩ h

/-- The standard finite ordinal's order type is `n`. -/
theorem orderType_rankedOrdinal (n : ℕ) :
    (⟨Equiv.refl (Fin n)⟩ : RankingData (Fin n) (Fin n)).orderType = .finite n :=
  RankingData.orderType_fin _

/-- The order type of the finite ranked object's ranking: the object's selected index is `n`. -/
theorem orderType_rankedFin (n : ℕ) (X : Type) (r : RankingData X (Fin n)) :
    r.orderType = .finite n :=
  RankingData.orderType_fin r

/-- The order type of the countably ranked object's ranking is `ω`. -/
theorem orderType_rankedCountable (X : Type) (r : RankingData X ℕ) :
    r.orderType = .omega :=
  RankingData.orderType_nat r

end CasCatalogue.Foundation.Rankings

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.ranked_fin"⟩, category := CategoryId.enumeratedSets
    name := "RankedFinSet"
    declaration := `CasCatalogue.Foundation.Rankings.rankedFin }

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.ranked_countable"⟩, category := CategoryId.enumeratedSets
    name := "RankedCountableSet"
    declaration := `CasCatalogue.Foundation.Rankings.rankedCountable }

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.naturals"⟩, category := CategoryId.enumeratedSets
    name := "EnumeratedNaturals"
    declaration := `CasCatalogue.Foundation.Rankings.naturalsObj }

normalized_registry .object
  { id := ⟨"obj.enumerated_sets.realized_positions"⟩, category := CategoryId.enumeratedSets
    name := "RealizedPositions"
    declaration := `CasCatalogue.Foundation.Rankings.positionsObj }

normalized_registry .operation
  { id := ⟨"op.enumerated_sets.ranked.rank"⟩, category := CategoryId.enumeratedSets
    name := "rank", arity := 1
    declaration := `LeanCategories.Foundation.EnumeratedSetCat.indexMap
    result := some ⟨"obj.enumerated_sets.naturals"⟩ }

normalized_registry .operation
  { id := ⟨"op.enumerated_sets.ranked.index_of"⟩, category := CategoryId.enumeratedSets
    name := "indexOf", arity := 1
    declaration := `LeanCategories.Foundation.EnumeratedSetCat.indexMap
    result := some ⟨"obj.enumerated_sets.naturals"⟩ }

normalized_registry .operation
  { id := ⟨"op.enumerated_sets.ranked.nth"⟩, category := CategoryId.enumeratedSets
    name := "nth", arity := 1
    declaration := `LeanCategories.Foundation.EnumeratedSetCat.nthMap }

normalized_registry .operation
  { id := ⟨"op.enumerated_sets.ranked.le"⟩, category := CategoryId.enumeratedSets
    name := "≤", arity := 2
    declaration := `LeanCategories.Foundation.EnumeratedSetCat.leMap
    result := some ⟨"obj.sets.truth_values"⟩ }

end CasCatalogue
