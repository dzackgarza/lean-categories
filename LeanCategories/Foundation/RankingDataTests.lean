/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.Rankings
public import LeanCategories.Foundation.EnumeratedMonotone
public import LeanCategories.Foundation.Sets
public import Mathlib.Tactic.FinCases

/-!
# Rankings and encodings are distinct selected data (#96)

On the same carrier, a pre-existing encoding and an encoding derived from a selected ranking need
not agree, and the ranking-derived one does not replace the earlier selection. This is the compiled
control for that: two selections on `Bool`, differing at `true`.

The control now runs at the level of the catalogue's objects as well as of the encodings: the
ranking-derived object `Rankings.rankedFin` and the object of the pre-existing encoding are two
*objects* of `EnumeratedSetCat`, they are unequal, and their selected orders disagree on the pair
`(false, true)`. This file imports the catalogue module for that comparison only.

The pre-existing encoding sends `true ↦ 0`, `false ↦ 1`; the selected ranking is the reverse
standard ranking `true ↦ 1`, `false ↦ 0`, whose derived encoding inherits that order. No monotone
comparison between the two induced orders is claimed — only that they differ.
-/

@[expose] public section

namespace LeanCategories.Foundation

/-- The pre-existing selected encoding on `Bool`: `true` first. -/
def boolEncodingTrueFirst : Encodable Bool where
  encode b := if b then 0 else 1
  decode n := some (if n = 0 then true else false)
  encodek b := by cases b <;> simp

/-- The selected ranking on `Bool`: the reverse standard ranking, `true ↦ 1`, `false ↦ 0`. -/
def boolReverseRanking : RankingData Bool (Fin 2) where
  rank :=
    { toFun := fun b => if b then 1 else 0
      invFun := fun n => decide (n = 1)
      left_inv := by intro b; cases b <;> decide
      right_inv := by
        intro n
        fin_cases n <;> decide }

/-- Under the pre-existing encoding, `true` precedes `false`. -/
theorem boolEncodingTrueFirst_true_before_false :
    boolEncodingTrueFirst.encode true < boolEncodingTrueFirst.encode false := by decide

/-- Under the selected ranking, `false` precedes `true` — the opposite order on the same carrier. -/
theorem boolReverseRanking_le_false_true : boolReverseRanking.le false true := by
  simp [RankingData.le, boolReverseRanking]

/-- The selected ranking is not the order induced by the pre-existing encoding: the two disagree on
the pair `(false, true)`. A ranking is selected data, and a different encoding already present on the
carrier neither determines it nor is replaced by it. -/
theorem boolRanking_not_preexisting_order :
    boolReverseRanking.le false true ∧
      ¬ (boolEncodingTrueFirst.encode false < boolEncodingTrueFirst.encode true) := by
  refine ⟨boolReverseRanking_le_false_true, ?_⟩
  decide

/-- The ranking's inverse recovers the element at a selected index. -/
theorem boolReverseRanking_unrank_one : boolReverseRanking.unrank 1 = true := by
  simp [RankingData.unrank, boolReverseRanking]

/-- The ranking's index map and inverse are mutual inverses on a concrete element. -/
theorem boolReverseRanking_rank_unrank :
    boolReverseRanking.rank (boolReverseRanking.unrank 0) = 0 :=
  boolReverseRanking.rank_unrank 0

/-- The pre-existing enumerated object on `Bool`: the encoding that puts `true` first, selected
before any ranking of this carrier was. -/
noncomputable def boolPreexistingObject : EnumeratedSetCat.{0} :=
  @EnumeratedSetCat.mk Bool boolEncodingTrueFirst

/-- The pre-existing encoding sends `true` to `0`. -/
theorem boolEncodingTrueFirst_encode_true : boolEncodingTrueFirst.encode true = 0 := rfl

/-- The ranking-derived encoding sends `true` to `1`: the natural-number value of its index. -/
theorem boolReverseRanking_toEncodableFin_encode_true :
    boolReverseRanking.toEncodableFin.encode true = 1 := by
  rw [RankingData.toEncodableFin_encode]
  decide

/-- The ranking-derived object's chosen encoding sends `true` to `1`. -/
theorem rankedFin_bool_encode_true :
    (CasCatalogue.Foundation.Rankings.rankedFin 2 Bool boolReverseRanking).enumeration.encode true =
      1 :=
  boolReverseRanking_toEncodableFin_encode_true

/-- The pre-existing encoding sends `false` to `1`. -/
theorem boolEncodingTrueFirst_encode_false : boolEncodingTrueFirst.encode false = 1 := rfl

/-- A ranking-derived presentation and a pre-existing encoding of one carrier are distinct
selected data: the two objects of the enumerated-set category are unequal, because their chosen
encodings send `true` to different numbers. Neither replaces the other. -/
theorem rankedFin_bool_ne_preexisting :
    CasCatalogue.Foundation.Rankings.rankedFin 2 Bool boolReverseRanking ≠
      boolPreexistingObject := by
  intro h
  have hcarrier :
      @EnumeratedSetCat.mk Bool boolReverseRanking.toEncodableFin =
        @EnumeratedSetCat.mk Bool boolEncodingTrueFirst := h
  have henc : boolReverseRanking.toEncodableFin = boolEncodingTrueFirst := by
    injection hcarrier
  have hval := congrFun (congrArg (fun e : Encodable Bool => e.encode) henc) true
  rw [boolReverseRanking_toEncodableFin_encode_true, boolEncodingTrueFirst_encode_true] at hval
  exact Nat.one_ne_zero hval

/-- Two different selected rankings of one carrier give two different objects: the identity ranking
of `Fin 2` and the swap ranking of the same carrier encode `0` differently. -/
theorem rankedFin_two_rankings_distinct :
    CasCatalogue.Foundation.Rankings.rankedOrdinal 2 ≠
      CasCatalogue.Foundation.Rankings.rankedFin 2 (Fin 2) ⟨Equiv.swap (0 : Fin 2) 1⟩ := by
  intro h
  have hcarrier :
      @EnumeratedSetCat.mk (Fin 2)
          (⟨Equiv.refl (Fin 2)⟩ : RankingData (Fin 2) (Fin 2)).toEncodableFin =
        @EnumeratedSetCat.mk (Fin 2)
          (⟨Equiv.swap (0 : Fin 2) 1⟩ : RankingData (Fin 2) (Fin 2)).toEncodableFin := h
  have henc : (⟨Equiv.refl (Fin 2)⟩ : RankingData (Fin 2) (Fin 2)).toEncodableFin =
      (⟨Equiv.swap (0 : Fin 2) 1⟩ : RankingData (Fin 2) (Fin 2)).toEncodableFin := by
    injection hcarrier
  have hval := congrFun (congrArg (fun e : Encodable (Fin 2) => e.encode) henc) 0
  rw [RankingData.toEncodableFin_encode, RankingData.toEncodableFin_encode] at hval
  simp at hval

/-- The two selected orders on `Bool` disagree: `false` precedes `true` under the ranking-derived
object, and does not under the pre-existing encoding. No identification of the two selected
rankings is available, and none is claimed. -/
theorem rankedFin_bool_le_not_preexisting :
    (CasCatalogue.Foundation.Rankings.rankedFin 2 Bool boolReverseRanking).leMap.hom (false, true) ∧
      ¬ boolPreexistingObject.leMap.hom (false, true) := by
  refine ⟨(CasCatalogue.Foundation.Rankings.leMap_rankedFin 2 Bool boolReverseRanking false
    true).mpr boolReverseRanking_le_false_true, ?_⟩
  intro hle
  have hle' := (EnumeratedSetCat.leMap_apply boolPreexistingObject false true).mp hle
  exact absurd hle' (by decide)

/-! ### The selected order is the counting order, and its order type is `n` or `ω` (#96 item 3)

The research expectations read off the ranking, on the smallest inputs that decide each one: the
finite ordinal `Fin 3` ranked by its own order (ordered enumeration, `enumeration`/`inverse`,
`ranking_map()(three(2)) == NN(2)`, `order_type() == ordinal(3)`) and `ℕ` ranked by itself (the
counting well-order, `counting_well_order().cardinality() == cardinal(3)` and `NN is NN`). -/

/-- The selected order is antisymmetric and total, so the comparison the ranking contract uses is a
linear order on the carrier, not merely a preorder. -/
theorem boolReverseRanking_le_isLinear (x y : Bool) :
    (boolReverseRanking.le x y → boolReverseRanking.le y x → x = y) ∧
      (boolReverseRanking.le x y ∨ boolReverseRanking.le y x) :=
  ⟨fun h₁ h₂ => boolReverseRanking.le_antisymm h₁ h₂, boolReverseRanking.le_total x y⟩

/-- The strict selected order of a finite ranking is well founded: the counting order on a finite
carrier is a well-order, read through the ranking. -/
theorem boolReverseRanking_wellFounded_lt : WellFounded boolReverseRanking.lt :=
  boolReverseRanking.wellFounded_lt_fin

/-- A ranking by `Fin 2` has a carrier of exactly two elements: no finiteness is assumed of `Bool`,
it is read along the ranking. -/
theorem boolReverseRanking_natCard : Nat.card Bool = 2 :=
  boolReverseRanking.natCard_fin

/-- The standard finite ordinal `Fin 3` ranked by its own order. -/
def finThreeIdentityRanking : RankingData (Fin 3) (Fin 3) := ⟨Equiv.refl (Fin 3)⟩

/-- `ranking_map()(three(2)) == NN(2)`: indexing the point `2` returns `2`. -/
theorem finThreeIdentityRanking_indexOf_two : finThreeIdentityRanking.indexOf 2 = 2 := rfl

/-- The inverse of the indexing: the point at position `2` is `2`. -/
theorem finThreeIdentityRanking_nth_two : finThreeIdentityRanking.nth 2 = 2 := rfl

/-- `order_type() == ordinal(3)`: the selected index is `Fin 3`, so the order type is `3`. -/
theorem finThreeIdentityRanking_orderType : finThreeIdentityRanking.orderType = .finite 3 :=
  RankingData.orderType_fin finThreeIdentityRanking

/-- `cardinality() == cardinal(3)`, read along the ranking. -/
theorem finThreeIdentityRanking_natCard : Nat.card (Fin 3) = 3 :=
  finThreeIdentityRanking.natCard_fin

/-- The finite half of the classification on the same carrier: the carrier is a finite type because
a ranking by `Fin 3` says so, not because `Fin 3` happens to be one. -/
theorem finThreeIdentityRanking_finite : Finite (Fin 3) :=
  finThreeIdentityRanking.finite_fin

/-- The standard countable index `ℕ` ranked by its own order: `NN.counting_well_order() is NN`. -/
def natIdentityRanking : RankingData ℕ ℕ := ⟨Equiv.refl ℕ⟩

/-- Indexing is the identity on the counting order: `ranking_map()(n) == NN(n)`, reversed. -/
theorem natIdentityRanking_indexOf (m : ℕ) : natIdentityRanking.indexOf m = m := rfl

/-- `nth` is the identity on the counting order, at every position. -/
theorem natIdentityRanking_nth (m : ℕ) : natIdentityRanking.nth m = m := rfl

/-- The order type of the countable index is `ω`, which has a value rather than being absent. -/
theorem natIdentityRanking_orderType : natIdentityRanking.orderType = .omega :=
  RankingData.orderType_nat natIdentityRanking

/-- The counting order on `ℕ` is a well-order: its strict order is well founded. -/
theorem natIdentityRanking_wellFounded_lt : WellFounded natIdentityRanking.lt :=
  natIdentityRanking.wellFounded_lt_nat

/-- The ω side of the classification: a ranking by `ℕ` makes the carrier infinite — the chosen
encoding of a *selected* enumeration is not evidence of this, the ranking is. -/
theorem natIdentityRanking_infinite : Infinite ℕ :=
  natIdentityRanking.infinite_nat

/-- The ω side counts as `0` under `Nat.card`, the `cardinality()` reading of a countably infinite
carrier: `NN.counting_well_order()` is `NN`, not a finite set of some size. -/
theorem natIdentityRanking_natCard : Nat.card ℕ = 0 :=
  natIdentityRanking.natCard_nat

/-! ### Derived rankings: `Denumerable.ofEncodableOfInfinite` and `Denumerable.mk'` (#96)

A chosen `Encodable` does determine a ranking, and a supplied equivalence with `ℕ` is retained
rather than re-derived. These are the two directions the issue's design note names, and neither is
an identification of a derived ranking with an independently supplied one. -/

/-- An infinite encodable carrier's derived ranking has order type `ω`. -/
theorem derivedCountable_nat_orderType :
    (RankingData.derivedCountable ℕ).orderType = .omega :=
  RankingData.orderType_derivedCountable ℕ

/-- The derived ranking's carrier counts as `0` under `Nat.card`: it is infinite, not finite. -/
theorem derivedCountable_nat_card : Nat.card ℕ = 0 :=
  RankingData.natCard_derivedCountable ℕ

/-- A supplied ranking by `ℕ` reaches `Denumerable.mk'` with its own equivalence: the denumeration
retains supplied data instead of deriving a ranking from an encoding. -/
theorem eqv_toDenumerable_natIdentity :
    @Denumerable.eqv ℕ natIdentityRanking.toDenumerable = natIdentityRanking.rank :=
  RankingData.eqv_toDenumerable natIdentityRanking

/-! ### Two presentations of one carrier are related by a map, not by their orders (#96)

A ranking-derived object and the object of a pre-existing encoding of the same carrier are distinct
selected data. What relates them is an ordinary map of the all-function category; whether that map
compares their selected orders is a separate question, and here the answer is no. -/

/-- The identity on `Bool` as a morphism from the ranking-derived object to the object of the
pre-existing encoding. -/
noncomputable def rankedFinBoolHom :
    CasCatalogue.Foundation.Rankings.rankedFin 2 Bool boolReverseRanking ⟶
      boolPreexistingObject :=
  EnumeratedSetCat.homOfFun id

/-- The map between the two presentations is the identity on the carrier. -/
theorem rankedFinBoolHom_apply (b : Bool) : rankedFinBoolHom.hom b = b := rfl

/-- It is not a comparison of the selected orders: `false ≤ true` holds under the ranking-derived
object and fails under the pre-existing encoding, so the identity of carriers is an ordinary map of
the all-function category and nothing more. A monotone comparison between the two selected rankings
would have to be supplied as data, and none is claimed. -/
theorem rankedFinBoolHom_not_monotone :
    ¬ ∀ x y : Bool,
        (EnumeratedSetCat.leMap
            (CasCatalogue.Foundation.Rankings.rankedFin 2 Bool boolReverseRanking)).hom (x, y) →
          (EnumeratedSetCat.leMap boolPreexistingObject).hom (x, y) := by
  intro h
  exact rankedFin_bool_le_not_preexisting.2 (h false true rankedFin_bool_le_not_preexisting.1)

/-! ### The two ranked-object constructions coincide (#96)

A ranked object is built twice: from `toEncodableFin`/`toEncodableNat`
(`CasCatalogue.Foundation.Rankings.rankedFin`, `.rankedCountable`) and from `toEncodable`
(`RankingData.rankedEnumeratedSet`). They are two constructions of one object, and these say so. -/

/-- For a finite index the two derived encodings are equal: they encode alike, and their decoders
agree — the value's index inside the bound and `none` outside it, which is the check `decode_fin`
supplies. -/
theorem toEncodableFin_eq_toEncodable {n : ℕ} {X : Type} (r : RankingData X (Fin n)) :
    r.toEncodableFin = r.toEncodable := by
  have hdec : ∀ m, r.toEncodableFin.decode m = r.toEncodable.decode m := by
    intro m
    by_cases h : m < n
    · rw [RankingData.toEncodableFin_decode_of_lt r h]
      show some (r.unrank ⟨m, h⟩) = (Encodable.decode (α := Fin n) m).map r.unrank
      rw [RankingData.decode_fin, dite_eq_left h, Option.map_some]
    · rw [RankingData.toEncodableFin_decode_of_not_lt r h]
      show none = (Encodable.decode (α := Fin n) m).map r.unrank
      rw [RankingData.decode_fin, dite_eq_right h, Option.map_none]
  exact EnumeratedSetCat.encodable_ext (fun _ => rfl) hdec

/-- `rankedFin` is `rankedEnumeratedSet`: two constructions of the ranked object, one object. -/
theorem rankedFin_eq_rankedEnumeratedSet {n : ℕ} (X : Type) (r : RankingData X (Fin n)) :
    CasCatalogue.Foundation.Rankings.rankedFin n X r = r.rankedEnumeratedSet :=
  congrArg (fun e => @EnumeratedSetCat.mk X e) (toEncodableFin_eq_toEncodable r)

/-- `rankedCountable` is `rankedEnumeratedSet`, definitionally. -/
theorem rankedCountable_eq_rankedEnumeratedSet (X : Type) (r : RankingData X ℕ) :
    CasCatalogue.Foundation.Rankings.rankedCountable X r = r.rankedEnumeratedSet := rfl

end LeanCategories.Foundation
