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
public import Mathlib.SetTheory.Cardinal.Finite
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

/-- Extensionality for morphisms of enumerated sets: two morphisms are equal when their underlying
functions agree. The category instance is `InducedCategory (Type u) carrier` (`inferInstanceAs`), so
Mathlib's `@[ext]` lemma for `InducedCategory.Hom` is not reached by `ext` at reducible transparency;
this restates it at the type consumers actually see. -/
@[ext] theorem hom_ext {X Y : EnumeratedSetCat.{u}} {f g : X ⟶ Y}
    (h : InducedCategory.Hom.hom f = InducedCategory.Hom.hom g) : f = g :=
  InducedCategory.Hom.ext h

/-- Forget the chosen enumeration. -/
def forget : EnumeratedSetCat.{u} ⥤ Type u where
  obj X := X.carrier
  map f := f.hom

end EnumeratedSetCat

/-- The order type of a selected standard index: `n` for the finite index `Fin n`, `ω` for `ℕ`.
This is the classification the ranking contract's order-type accessor returns, and it is a value at
every index: `ω` is a constructor, not the absence of an answer. -/
inductive SelectedOrderType where
  /-- The finite order type `n`, the order type of `Fin n`. -/
  | finite (n : ℕ)
  /-- The order type `ω`, the order type of `ℕ`. -/
  | omega
  deriving DecidableEq, Repr

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

/-- The selected order is antisymmetric: the ranking is injective, so two points of one index are
one point. With `le_refl`, `le_trans` and `le_total` this is the linear order the standard index
carries, read through `rank` — the comparison the ranking contract uses, and the order whose order
type `orderType` reports. -/
theorem le_antisymm (r : RankingData X I) {x y : X} (h₁ : r.le x y) (h₂ : r.le y x) : x = y :=
  r.rank.injective (_root_.le_antisymm h₁ h₂)

/-- The selected order is total: the standard order of the index decides every pair of points. -/
theorem le_total (r : RankingData X I) (x y : X) : r.le x y ∨ r.le y x :=
  _root_.le_total (r.rank x) (r.rank y)

/-- The strict selected order: `x < y` when the index of `x` precedes the index of `y`. -/
def lt (r : RankingData X I) (x y : X) : Prop := r.rank x < r.rank y

/-- The ranking-derived encoding of the carrier by its selected index, when the index is itself
encodable: an element is encoded by the encoding of its selected index and decoded by the same
inverse. Whether it orders the carrier as the selected ranking does depends on the index's own
encoding and is `toEncodable_le_iff` below; the index-specific constructions (`toEncodableFin`,
`toEncodableNat`) are the ones that preserve the selected standard order with no further
hypothesis. -/
def toEncodable (r : RankingData X I) [Encodable I] : Encodable X where
  encode x := Encodable.encode (r.rank x)
  decode n := (Encodable.decode n).map r.unrank
  encodek x := by
    simp only [Encodable.encodek]
    exact congrArg some (r.unrank_rank x)

/-- Encoding a point by the ranking-derived encoding is the encoding of its selected index. -/
theorem toEncodable_encode (r : RankingData X I) [Encodable I] (x : X) :
    r.toEncodable.encode x = Encodable.encode (r.rank x) := rfl

/-- The ranking-derived encoding keeps the carrier's own selected ranking: decoding the encoding of
an element returns that element. -/
theorem toEncodable_encodek (r : RankingData X I) [Encodable I] (x : X) :
    r.toEncodable.decode (r.toEncodable.encode x) = some x :=
  r.toEncodable.encodek x

/-- The ranking-derived encoding orders the carrier exactly as the selected ranking does, provided
the index's own chosen encoding reflects the order of the index. That hypothesis is what the index
supplies; both selected standard indices supply it (`toEncodableFin_le_iff`,
`toEncodableNat_le_iff`). -/
theorem toEncodable_le_iff (r : RankingData X I) [Encodable I]
    (hI : ∀ i j : I, Encodable.encode i ≤ Encodable.encode j ↔ i ≤ j) (x y : X) :
    r.toEncodable.encode x ≤ r.toEncodable.encode y ↔ r.le x y := by
  simp only [toEncodable_encode, le]
  exact hI _ _

/-- The standard finite index encodes by its value. -/
theorem encode_fin {n : ℕ} (i : Fin n) : Encodable.encode i = i.val := by
  rw [Fin.encodable, Encodable.encode_ofEquiv]
  rfl

/-- The standard finite index decodes by its value, inside its bound. -/
theorem decode_fin {n m : ℕ} :
    Encodable.decode (α := Fin n) m = if h : m < n then some ⟨m, h⟩ else none := by
  rw [Fin.encodable, Encodable.decode_ofEquiv,
    show Encodable.decode (α := {a : ℕ // a < n}) m =
      (some m).bind (fun a => if h : a < n then some ⟨a, h⟩ else none) from rfl,
    Option.bind_some]
  split_ifs with h
  · rw [Option.map_some]
    rfl
  · rfl

/-- The finite ranking-derived encoding: the encoding of the standard finite index along the
selected ranking, so a point is encoded by the natural-number value of its index and decoded by the
same inverse with the bound checked. This is the encoding a finite ranked object is built from, so
the object's chosen encoding *is* the selected ranking read into `ℕ`. -/
def toEncodableFin {n : ℕ} (r : RankingData X (Fin n)) : Encodable X :=
  Encodable.ofEquiv (Fin n) r.rank

/-- Encoding a point by the finite ranking-derived encoding returns the value of its index. -/
theorem toEncodableFin_encode {n : ℕ} (r : RankingData X (Fin n)) (x : X) :
    r.toEncodableFin.encode x = (r.rank x).val := by
  rw [toEncodableFin, Encodable.encode_ofEquiv, encode_fin]

/-- Inside the finite bound, decoding returns the ranked point at that position. -/
theorem toEncodableFin_decode_of_lt {n : ℕ} (r : RankingData X (Fin n)) {m : ℕ} (h : m < n) :
    r.toEncodableFin.decode m = some (r.unrank ⟨m, h⟩) := by
  rw [toEncodableFin, Encodable.decode_ofEquiv, decode_fin, dite_eq_left h]
  rfl

/-- Outside the finite bound the encoding realizes no point: the bound is checked, not ignored. -/
theorem toEncodableFin_decode_of_not_lt {n : ℕ} (r : RankingData X (Fin n)) {m : ℕ}
    (h : ¬ m < n) : r.toEncodableFin.decode m = none := by
  rw [toEncodableFin, Encodable.decode_ofEquiv, decode_fin, dite_eq_right h]
  rfl

/-- Every position inside the finite bound is realized, so indexing by it is total there. -/
theorem toEncodableFin_decode_isSome {n : ℕ} (r : RankingData X (Fin n)) {m : ℕ} (h : m < n) :
    (r.toEncodableFin.decode m).isSome = true := by
  rw [toEncodableFin_decode_of_lt r h]
  rfl

/-- Encoding the point at a selected index returns that index: the encoding's partner is the
ranking's own inverse. -/
theorem toEncodableFin_encode_unrank {n : ℕ} (r : RankingData X (Fin n)) (i : Fin n) :
    r.toEncodableFin.encode (r.unrank i) = i.val := by
  rw [toEncodableFin_encode, r.rank_unrank]

/-- The finite ranking-derived encoding preserves the selected ranking, with no hypothesis: the
standard index `Fin n` encodes by its value, whose order is the index's own order. -/
theorem toEncodableFin_le_iff {n : ℕ} (r : RankingData X (Fin n)) (x y : X) :
    r.toEncodableFin.encode x ≤ r.toEncodableFin.encode y ↔ r.le x y := by
  rw [toEncodableFin_encode, toEncodableFin_encode]
  exact Iff.rfl

/-- The countable ranking-derived encoding: the encoding of `ℕ` along the selected ranking, so a
point is encoded by its index and decoded by the same inverse. -/
def toEncodableNat (r : RankingData X ℕ) : Encodable X :=
  Encodable.ofEquiv ℕ r.rank

/-- Encoding a point by the countable ranking-derived encoding returns its index. -/
theorem toEncodableNat_encode (r : RankingData X ℕ) (x : X) :
    r.toEncodableNat.encode x = r.rank x := by
  rw [toEncodableNat, Encodable.encode_ofEquiv]
  rfl

/-- Decoding a position by the countable ranking-derived encoding returns the ranked point there;
every position is realized, so indexing is total on `ℕ`. -/
theorem toEncodableNat_decode (r : RankingData X ℕ) (m : ℕ) :
    r.toEncodableNat.decode m = some (r.unrank m) := by
  rw [toEncodableNat, Encodable.decode_ofEquiv]
  rfl

/-- Encoding the point at a position returns that position. -/
theorem toEncodableNat_encode_unrank (r : RankingData X ℕ) (m : ℕ) :
    r.toEncodableNat.encode (r.unrank m) = m := by
  rw [toEncodableNat_encode, r.rank_unrank]

/-- The countable ranking-derived encoding preserves the selected ranking, with no hypothesis. -/
theorem toEncodableNat_le_iff (r : RankingData X ℕ) (x y : X) :
    r.toEncodableNat.encode x ≤ r.toEncodableNat.encode y ↔ r.le x y := by
  rw [toEncodableNat_encode, toEncodableNat_encode]
  exact Iff.rfl

/-- The selected index is finite when it carries a `Fintype` structure. A selected index is a
`Fin n` or `ℕ`, so this is the finite-versus-`ω` classification; it is stated on the index because
that is the data the ranking supplies, and the carrier's own finiteness then follows by transport
along the ranking (`fintypeCarrier`). -/
def IsFiniteIndex (I : Type v) : Prop := Nonempty (Fintype I)

/-- `ℕ` is not a finite index: the `ω` side of the classification is inhabited by the standard
countable index itself. -/
theorem not_isFiniteIndex_nat : ¬ IsFiniteIndex ℕ := by
  intro h
  have hf : Fintype ℕ := Classical.choice h
  exact Infinite.not_finite (Finite.of_fintype ℕ)

/-- The order type of the selected index of supplied ranking data: `n` when the index has `n`
elements and `ω` otherwise, which for a selected standard index is the `ℕ` case. Reading it is a
case split on the supplied index, not an executable procedure deciding finiteness of, or ranking,
an arbitrary encoded input. -/
noncomputable def orderType (_r : RankingData X I) : SelectedOrderType := by
  classical
  exact if IsFiniteIndex I then .finite (Nat.card I) else .omega

/-- A ranking with index `Fin n` has order type `n`. -/
theorem orderType_fin {n : ℕ} (r : RankingData X (Fin n)) : r.orderType = .finite n := by
  classical
  simp only [orderType, Nat.card_fin,
    ite_eq_left (show IsFiniteIndex (Fin n) from ⟨Fin.fintype n⟩)]

/-- A ranking with index `ℕ` has order type `ω`. -/
theorem orderType_nat (r : RankingData X ℕ) : r.orderType = .omega := by
  classical
  simp only [orderType, ite_eq_right not_isFiniteIndex_nat]

/-- The order type of a finite ranking is `n` for its own `n` and nothing else. -/
theorem orderType_fin_eq_iff {n m : ℕ} (r : RankingData X (Fin n)) :
    r.orderType = .finite m ↔ m = n := by
  rw [orderType_fin r]
  exact ⟨fun h => (SelectedOrderType.finite.inj h).symm, fun h => by rw [h]⟩

/-- The carrier of a ranking with finite index is itself finite: finiteness is transported along the
selected equivalence, not asserted independently. -/
noncomputable def fintypeCarrier (r : RankingData X I) (h : IsFiniteIndex I) : Fintype X := by
  classical
  letI := Classical.choice h
  exact Fintype.ofEquiv I r.rank.symm

/-- The selected strict order of a ranking by `ℕ` is well founded: it is the standard order of `ℕ`
pulled back along the ranking. This is the `ω` half of the counting well-order, stated on the
selected order rather than on the chosen encoding. -/
theorem wellFounded_lt_nat (r : RankingData X ℕ) : WellFounded r.lt :=
  InvImage.wf r.rank Nat.lt_wfRel.wf

/-- The selected strict order of a ranking by `Fin n` is well founded: it is the standard order of
`ℕ` pulled back along the value of the ranking. This is the finite half of the counting well-order.
-/
theorem wellFounded_lt_fin {n : ℕ} (r : RankingData X (Fin n)) : WellFounded r.lt :=
  InvImage.wf (fun x => (r.rank x).val) Nat.lt_wfRel.wf

/-- The carrier of a ranking by `Fin n` has exactly `n` elements: the selected index classifies the
carrier, and the count is read along the ranking rather than assumed
(`cardinality() == cardinal(n)` of the counting-order contract). -/
theorem natCard_fin {n : ℕ} (r : RankingData X (Fin n)) : Nat.card X = n := by
  rw [Nat.card_congr r.rank, Nat.card_fin]

/-- `rank` as a plain function on carriers, the underlying map of the ranking morphism. -/
def rankFun (r : RankingData X I) : X → I := r.rank

/-- `unrank` as a plain function on carriers, the underlying map of the inverse-ranking morphism. -/
def unrankFun (r : RankingData X I) : I → X := r.unrank

/-- `unrank` after `rank` is the identity: the composite law cited by the ranking morphism rows. -/
theorem unrank_comp_rank (r : RankingData X I) : r.unrankFun ∘ r.rankFun = id := by
  funext x
  exact r.unrank_rank x

/-- `rank` after `unrank` is the identity. -/
theorem rank_comp_unrank (r : RankingData X I) : r.rankFun ∘ r.unrankFun = id := by
  funext i
  exact r.rank_unrank i

end RankingData

namespace EnumeratedSetCat

/-- The positions a chosen encoding realizes: the total domain of the inverse index map. A chosen
`Encodable` decodes only where its encoding realizes a point, so the `m`-th element of an enumerated
set is read at a *realized* position rather than at every natural number. -/
abbrev realizedPositions (X : EnumeratedSetCat.{0}) : Type :=
  {m : ℕ // (X.enumeration.decode m).isSome}

/-- The selected index map of an enumerated object: its chosen encoding, which on a
ranking-derived object is the value of the selected ranking (`Rankings.indexMap_rankedFin`,
`Rankings.indexMap_rankedCountable`). Total — every point has an index. -/
noncomputable def indexMap (X : EnumeratedSetCat.{0}) : X ⟶ of ℕ :=
  InducedCategory.homMk (TypeCat.ofHom fun x => X.enumeration.encode x)

/-- The value of the index map at a point: its chosen encoding. -/
theorem indexMap_apply (X : EnumeratedSetCat.{0}) (x : X.carrier) :
    (indexMap X).hom x = X.enumeration.encode x := rfl

/-- The inverse index map, at a realized position: iteration and indexing use this map, the inverse
of `indexMap` where the encoding realizes the position. -/
noncomputable def nthMap (X : EnumeratedSetCat.{0}) : of (realizedPositions X) ⟶ X :=
  InducedCategory.homMk (TypeCat.ofHom fun p => (X.enumeration.decode p.1).get p.2)

/-- The value of the inverse index map at a realized position. -/
theorem nthMap_apply (X : EnumeratedSetCat.{0}) (p : realizedPositions X) :
    (nthMap X).hom p = (X.enumeration.decode p.1).get p.2 := rfl

/-- The selected order of an enumerated object: `x ≤ y` when the encoding of `x` is no later than
the encoding of `y`. Total, and a total order because `ℕ`'s order is one. -/
noncomputable def leMap (X : EnumeratedSetCat.{0}) :
    of (X.carrier × X.carrier) ⟶ of Prop :=
  InducedCategory.homMk (TypeCat.ofHom fun p =>
    X.enumeration.encode p.1 ≤ X.enumeration.encode p.2)

/-- The value of the selected order at a pair of points: the comparison of their indices. -/
theorem leMap_apply (X : EnumeratedSetCat.{0}) (x y : X.carrier) :
    (leMap X).hom (x, y) ↔ X.enumeration.encode x ≤ X.enumeration.encode y := Iff.rfl

/-- The selected order is reflexive. -/
theorem leMap_refl (X : EnumeratedSetCat.{0}) (x : X.carrier) : (leMap X).hom (x, x) :=
  (leMap_apply X x x).mpr _root_.le_rfl

/-- The selected order is transitive. -/
theorem leMap_trans (X : EnumeratedSetCat.{0}) {x y z : X.carrier}
    (h₁ : (leMap X).hom (x, y)) (h₂ : (leMap X).hom (y, z)) : (leMap X).hom (x, z) :=
  (leMap_apply X x z).mpr <|
    _root_.le_trans ((leMap_apply X x y).mp h₁) ((leMap_apply X y z).mp h₂)

/-- Indexing the index of a point returns that point: the inverse law of the chosen encoding, which
is the law `Encodable.encodek` supplies and nothing more. The converse — that the index map
recovers the position of a realized point — is not a law of an arbitrary chosen encoding; it is
proved for the ranking-derived objects (`Rankings.indexMap_nthMap_rankedFin`). -/
theorem nthMap_indexMap (X : EnumeratedSetCat.{0}) (x : X.carrier) :
    (nthMap X).hom ⟨X.enumeration.encode x, by rw [Encodable.encodek]; rfl⟩ = x := by
  rw [nthMap_apply]
  exact Option.get_of_eq_some _ (Encodable.encodek x)

end EnumeratedSetCat


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
