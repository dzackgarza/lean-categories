/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.WellOrderedSets
public import Mathlib.Tactic.FinCases
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# The selected order of an enumerated set, and its monotone maps

`EnumeratedSetCat` keeps **all** functions as morphisms. This file does not restrict it. It adds

* `EnumeratedSetCat.inducedLinearOrder`: the order a selected encoding `e_X` selects on the carrier,
  `x ≤ y ↔ e_X x ≤ e_X y`, with its well-order certificate and the induced well-ordered object;
* `enumeratedMonotoneProperty`, the wide subcategory property of maps that are monotone for those
  selected orders, and hence `EnumeratedMonotoneSetCat`, the wide subcategory `E_mon ⊆ E` with the
  same objects;
* the identity-on-objects inclusion `E_mon → E` retaining each underlying function, the functor
  `E_mon → WellOrderedSets`, and the comparison of both routes with `E_mon → E → Sets`.

The two-point swap is the control: it is a morphism of `E` and an isomorphism there (all functions),
while for the standard ranking it is not monotone, so it is not a morphism of `E_mon`. No ordered
action is claimed for it on the strength of being computable or of lying in a backend.

## Source

sage-extensions `src/sage_extensions/categories/sets/set_categories.py`: `class EnumeratedSets`
(with `super_categories` `[Sets().Countable(), WellOrderedSets()]` and `ParentMethods.le` reading
`x <= y` from the ranking map) and `class WellOrderedSets` ("Well-ordered sets with order-preserving
maps"). The issue fixing this construction is `lean-categories` #97, whose audit row #97 (comment of
2026-10-29) records that `EnumeratedSets` cannot map into `WellOrderedSets` on all its morphisms,
since the swap on two points is a morphism of the former and is not monotone.

## Search record (LC-09)

`scripts/formalization_corpus.py search` for `WellOrderedSets`, `WellOrdered`, `well_order` and
`wofun`, plus whole-file reads of `UniMath/CategoryTheory/Categories/Woset.v` and
`UniMath/OrderTheory/OrderedSets/WellOrderedSets.v`. UniMath builds both `wosetfuncat` (morphisms
preserving the order *and initial segments*) and `WOSET` (all functions); neither is the monotone
wide subcategory of an enumerated-sets category, and the issue forbids both the smaller and the
larger morphism class. The wide subcategory itself is Mathlib's `CategoryTheory.WideSubcategory`
with a `MorphismProperty`, so nothing is reimplemented: `LinearOrder.lift'` transports the order
along the injective encoding and `InvImage.wf` transports well-foundedness.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace LeanCategories.Foundation

namespace EnumeratedSetCat

/-- The order a selected encoding of an enumerated set induces on its carrier:
`x ≤ y ↔ e_X x ≤ e_X y`. It is a linear order because the encoding is injective. -/
@[instance_reducible] noncomputable def inducedLinearOrder (X : EnumeratedSetCat.{u}) :
    LinearOrder X.carrier :=
  LinearOrder.lift' (Encodable.encode) Encodable.encode_injective

/-- The induced order is the encoding's pullback of the standard order of `ℕ`, on the nose. -/
theorem inducedLinearOrder_le_iff (X : EnumeratedSetCat.{u}) (x y : X.carrier) :
    @LE.le X.carrier X.inducedLinearOrder.toLE x y
      ↔ Encodable.encode x ≤ Encodable.encode y :=
  Iff.rfl

/-- The induced strict order is the encoding's pullback of the standard strict order. -/
theorem inducedLinearOrder_lt_iff (X : EnumeratedSetCat.{u}) (x y : X.carrier) :
    @LT.lt X.carrier X.inducedLinearOrder.toLT x y
      ↔ Encodable.encode x < Encodable.encode y :=
  Iff.rfl

/-- The induced order is a well-order: an injective pullback of the standard order of `ℕ` is
well-founded, and a linear order's strict order is total. -/
theorem induced_wellFoundedLT (X : EnumeratedSetCat.{u}) :
    @WellFoundedLT X.carrier X.inducedLinearOrder.toLT :=
  @WellFounded.intro X.carrier (fun a b => X.inducedLinearOrder.lt a b)
    (InvImage.wf (Encodable.encode) Nat.lt_wfRel.wf).apply

/-- The induced well-ordered object: the same carrier and the same encoding, carrying the order the
encoding selects. This is the induced order available on every selected enumerated object. -/
noncomputable def inducedWellOrder (X : EnumeratedSetCat.{u}) : WellOrderedSetCat.{u} :=
  ⟨@LinOrd.of X.carrier X.inducedLinearOrder,
    @isWellOrder_lt X.carrier X.inducedLinearOrder X.induced_wellFoundedLT⟩

@[simp] theorem inducedWellOrder_carrier (X : EnumeratedSetCat.{u}) :
    X.inducedWellOrder.carrier = X.carrier := rfl

end EnumeratedSetCat

/-- The wide subcategory property: a function between enumerated sets that is monotone for the
induced selected orders. -/
abbrev enumeratedMonotoneProperty : MorphismProperty EnumeratedSetCat.{u} :=
  fun {X Y} f => ∀ x x' : X.carrier,
    @LE.le X.carrier X.inducedLinearOrder.toLE x x' →
      @LE.le Y.carrier Y.inducedLinearOrder.toLE (f.hom x) (f.hom x')

/-- Identities and composites of monotone functions are monotone for the induced orders. -/
instance enumeratedMonotoneProperty.isMultiplicative :
    MorphismProperty.IsMultiplicative enumeratedMonotoneProperty where
  id_mem X := by
    intro x x' h
    change @LE.le X.carrier X.inducedLinearOrder.toLE x x'
    exact h
  comp_mem {X Y Z} f g hf hg := by
    intro x x' h
    change @LE.le Z.carrier Z.inducedLinearOrder.toLE (g.hom (f.hom x)) (g.hom (f.hom x'))
    exact hg (f.hom x) (f.hom x') (hf x x' h)

/-- `E_mon`: the wide subcategory of enumerated sets whose morphisms are the maps monotone for the
selected orders. Its objects are those of `E`. -/
abbrev EnumeratedMonotoneSetCat : Type (u + 1) :=
  WideSubcategory enumeratedMonotoneProperty

/-- The identity-on-objects inclusion `E_mon → E`, retaining each underlying function. -/
def enumeratedMonotoneInclusion :
    EnumeratedMonotoneSetCat.{u} ⥤ EnumeratedSetCat.{u} :=
  wideSubcategoryInclusion enumeratedMonotoneProperty

@[simp] theorem enumeratedMonotoneInclusion_obj (X : EnumeratedMonotoneSetCat.{u}) :
    enumeratedMonotoneInclusion.obj X = X.obj := rfl

@[simp] theorem enumeratedMonotoneInclusion_map {X Y : EnumeratedMonotoneSetCat.{u}}
    (f : X ⟶ Y) : enumeratedMonotoneInclusion.map f = f.hom := rfl

/-- The functor `E_mon → WellOrderedSets`: an enumerated set goes to the well-ordered set its
encoding induces, and a monotone map goes to that same function with its monotonicity evidence. -/
noncomputable def enumeratedMonotoneToWellOrdered :
    EnumeratedMonotoneSetCat.{u} ⥤ WellOrderedSetCat.{u} where
  obj X := X.obj.inducedWellOrder
  map {X Y} f := by
    letI := X.obj.inducedLinearOrder
    letI := Y.obj.inducedLinearOrder
    exact InducedCategory.homMk (LinOrd.ofHom ⟨⇑f.hom.hom, f.property⟩)
  map_id X := by
    apply InducedCategory.hom_ext
    apply LinOrd.hom_ext
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply LinOrd.hom_ext
    rfl

/-- The functor `E_mon → WellOrderedSets` retains each underlying function. -/
theorem enumeratedMonotoneToWellOrdered_map_apply
    {X Y : EnumeratedMonotoneSetCat.{u}} (f : X ⟶ Y) (x : X.obj.carrier) :
    (enumeratedMonotoneToWellOrdered.map f).hom.hom x = f.hom.hom x := rfl

/-- The two routes out of `E_mon` agree: forgetting the order after `E_mon → WellOrderedSets` is the
same functor as going `E_mon → E → Sets`, on objects and on each underlying function. -/
noncomputable def enumeratedMonotoneToSetsComparison :
    (enumeratedMonotoneInclusion ⋙ EnumeratedSetCat.forget) ≅
      (enumeratedMonotoneToWellOrdered ⋙ wellOrderedToSets) :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
    ext x
    rfl)

/-! ## The induced order of a selected ranking

A `RankingData` fixes which ranking a consumer selected. Its derived encoding (`toEncodable`) is an
encoding whose induced order is exactly the ranking's order, so the encoded construction above
may be used for it. An unrelated encoding need not agree, which is why the agreement is proved
rather than assumed. -/

namespace RankingData

variable {X : Type u} {I : Type v} [LinearOrder I]

/-- The enumerated set whose selected encoding is the one this ranking derives. -/
def rankedEnumeratedSet (r : RankingData X I) [Encodable I] : EnumeratedSetCat.{u} where
  carrier := X
  enumeration := r.toEncodable

/-- The induced order of a ranking-derived encoding is the ranking's selected order, provided the
index's own chosen encoding reflects the order of the index. That hypothesis is exactly the
agreement the encoding-derived construction needs: without it the encoding is a bijection whose
order need not be the selected one, and it must not silently replace the selected order. -/
theorem inducedLinearOrder_rankedEnumeratedSet (r : RankingData X I) [Encodable I]
    (hI : ∀ i j : I, Encodable.encode i ≤ Encodable.encode j ↔ i ≤ j) (x y : X) :
    @LE.le X r.rankedEnumeratedSet.inducedLinearOrder.toLE x y ↔ r.le x y := by
  change @Encodable.encode X r.toEncodable x ≤ @Encodable.encode X r.toEncodable y ↔ r.le x y
  exact hI _ _

end RankingData

/-! ## The two-point control

For the standard ranking of the two-point set, the swap is a morphism of `E` — and an isomorphism
there, so its image in `Sets` is a bijection — while it is not monotone, so it is not a morphism of
`E_mon`. -/

/-- The standard enumeration of the two-point set: each point is encoded by its own value. This is
the encoding the standard ranking derives, written out so its order is the standard order. -/
@[instance_reducible] def twoPointEnumeration : Encodable (Fin 2) where
  encode x := x.val
  decode m := if h : m < 2 then some ⟨m, h⟩ else none
  encodek x := by
    rw [dite_eq_left x.isLt]

/-- The encoding of a point of the two-point set is its value. -/
theorem twoPointEnumeration_encode (x : Fin 2) :
    Encodable.encode (self := twoPointEnumeration) x = x.val := rfl

/-- The two-point enumerated set: `Fin 2` with the standard enumeration. -/
def twoPointEnumeratedSet : EnumeratedSetCat.{0} where
  carrier := Fin 2
  enumeration := twoPointEnumeration

/-- The induced order of the two-point enumerated set is the standard order of `Fin 2`. -/
theorem twoPointEnumeratedSet_le_iff (x y : Fin 2) :
    @LE.le (Fin 2) twoPointEnumeratedSet.inducedLinearOrder.toLE x y ↔ x ≤ y := by
  change Encodable.encode (self := twoPointEnumeration) x
      ≤ Encodable.encode (self := twoPointEnumeration) y ↔ x ≤ y
  rw [twoPointEnumeration_encode, twoPointEnumeration_encode]
  exact Fin.le_def

/-- The swap of the two points, as a function. -/
def twoPointSwapFunction : Fin 2 → Fin 2 := fun x => Equiv.swap (0 : Fin 2) 1 x

/-- The swap of the two points, as a morphism of `E`: `E` has all functions. -/
def twoPointSwap : twoPointEnumeratedSet ⟶ twoPointEnumeratedSet :=
  InducedCategory.homMk (TypeCat.ofHom twoPointSwapFunction)

/-- The swap is not monotone for the selected orders: `0 ≤ 1` but `swap 0 = 1 ≰ 0 = swap 1`. -/
theorem twoPointSwap_not_monotone : ¬ enumeratedMonotoneProperty twoPointSwap := by
  intro h
  have h01 : @LE.le (Fin 2) twoPointEnumeratedSet.inducedLinearOrder.toLE 0 1 := by
    rw [twoPointEnumeratedSet_le_iff]
    decide
  have h' : @LE.le (Fin 2) twoPointEnumeratedSet.inducedLinearOrder.toLE
      (twoPointSwapFunction 0) (twoPointSwapFunction 1) := h (0 : Fin 2) (1 : Fin 2) h01
  rw [twoPointEnumeratedSet_le_iff] at h'
  simp [twoPointSwapFunction] at h'

/-- Swapping the two points twice is the identity. -/
theorem twoPointSwapFunction_involutive (x : Fin 2) :
    twoPointSwapFunction (twoPointSwapFunction x) = x := by
  fin_cases x <;> rfl

/-- The swap is an isomorphism of `E`, hence a bijection of underlying sets, while it is not a
morphism of `E_mon`: `E_mon` is a proper wide subcategory of `E`. -/
theorem twoPointSwap_comp_self : twoPointSwap ≫ twoPointSwap = 𝟙 twoPointEnumeratedSet := by
  apply InducedCategory.hom_ext
  apply ConcreteCategory.hom_ext
  intro x
  change twoPointSwapFunction (twoPointSwapFunction x) = x
  exact twoPointSwapFunction_involutive x

/-- There is a morphism of `E` that is not a morphism of `E_mon`: the inclusion does not hit every
morphism, and no functor from all of `E` to `WellOrderedSets` restricts to this one. -/
theorem exists_not_enumeratedMonotone :
    ∃ (f : twoPointEnumeratedSet ⟶ twoPointEnumeratedSet), ¬ enumeratedMonotoneProperty f :=
  ⟨twoPointSwap, twoPointSwap_not_monotone⟩

/-- The category of enumerated sets and the wide subcategory of monotone maps, bundled for the
semantic catalogue. -/
abbrev EnumeratedMonotoneSets : ObjCat.{u + 1, u} := Cat.of EnumeratedMonotoneSetCat.{u}

end LeanCategories.Foundation
