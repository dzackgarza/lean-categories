/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Foundation.Subsets
public import LeanCategories.Foundation.IsoElements
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Order.SymmDiff
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Operations on subsets, enumerations, finite enumerated subsets, and multisets

**Subsets.** On the core of `Subobjects(Set)`, with an argument subset `T` of the ambient set:
`subsetOf` (`range i ⊆ T`) and the binary operations `range i ∪ T`, `∩`, `\`, `∆`, each a natural
section (`sectionFunctor`) of the operations on subsets of the ambient set, transported by
conjugation along isomorphisms.

**Enumerations.** A set presented together with an order of its elements is a *partial sequence*
`s : ℕ → Option X` (the `n`-th element, if there is one). `Enumerations := IsoElements seqFunctor`
over sets; `nth` reads the sequence, and `enumerationRange` forgets the order, sending it to the
subset `range s` (without `none`) of `X`.

**Finite enumerated subsets.** A duplicate-free list `l` in `X`: `FiniteLists := IsoElements`
of `X ↦ {l : List X // l.Nodup}`; it is an enumeration (`listSequence`). Over commutative rings,
`RingFiniteLists` carries `sum` and `prod` (iso-natural, by `map_list_sum`/`map_list_prod`) and
forgets to `FiniteLists`.

**Multisets.** `MultisetPoints := IsoElements multisetFunctor` over sets: `multisetContains`,
`multisetCard` (with multiplicity) and `multisetEquals` (as a subset of the ambient set, the answer
of `=` against a set).
-/

open CategoryTheory
open scoped symmDiff

namespace LeanCategories.Foundation

universe u

/-! ### Binary operations on subsets -/

/-- Operations on subsets of the ambient set, transported by conjugation. -/
def ambientSubsetOperations : Core Subsets.{u} ⥤ Type u :=
  typeFunctor (fun S => Set S.of.ambient → Set S.of.ambient)
    (fun f op T => Subsets.ambientEquiv f '' op (Subsets.ambientEquiv f ⁻¹' T))
    (fun _ op => funext fun T => by
      change id '' op (id ⁻¹' T) = op T
      simp)
    (fun f g op => funext fun T => by
      change _ '' op (_ ⁻¹' T) = _ '' (_ '' op (_ ⁻¹' (_ ⁻¹' T)))
      rw [Set.image_image, Set.preimage_preimage]
      rfl)

/-- A pointwise binary operation on subsets that commutes with images and preimages along
equivalences is a natural section of `ambientSubsetOperations`. -/
def subsetOperation (op : ∀ {X : Type u}, Set X → Set X → Set X)
    (h : ∀ {X Y : Type u} (e : X ≃ Y) (A B : Set X), e '' op A B = op (e '' A) (e '' B)) :
    Core Subsets.{u} ⥤ ambientSubsetOperations.{u}.Elements :=
  sectionFunctor ambientSubsetOperations (fun S T => op S.of.range T) fun {X Y} f => by
    funext T
    change Subsets.ambientEquiv f '' op X.of.range (Subsets.ambientEquiv f ⁻¹' T) =
      op Y.of.range T
    rw [h, Subsets.range_ambientEquiv, Equiv.image_preimage]

/-- `union`. -/
def subsetUnion : Core Subsets.{u} ⥤ ambientSubsetOperations.{u}.Elements :=
  subsetOperation (· ∪ ·) fun e A B => Set.image_union e A B

/-- `intersect`. -/
def subsetInter : Core Subsets.{u} ⥤ ambientSubsetOperations.{u}.Elements :=
  subsetOperation (· ∩ ·) fun e A B => Set.image_inter e.injective

/-- `diff`. -/
def subsetDiff : Core Subsets.{u} ⥤ ambientSubsetOperations.{u}.Elements :=
  subsetOperation (· \ ·) fun e A B => Set.image_diff e.injective A B

/-- `symdiff`. -/
def subsetSymmDiff : Core Subsets.{u} ⥤ ambientSubsetOperations.{u}.Elements :=
  subsetOperation (· ∆ ·) fun e A B => Set.image_symmDiff e.injective A B

/-- `subset`: inclusion in a subset of the ambient set. -/
def subsetOf : Core Subsets.{u} ⥤ ambientSubsetPredicates.{u}.Elements :=
  sectionFunctor ambientSubsetPredicates (fun S (T : Set S.of.ambient) => S.of.range ⊆ T)
    fun {X Y} f => by
    funext T
    change (X.of.range ⊆ Subsets.ambientEquiv f ⁻¹' T) = (Y.of.range ⊆ T)
    rw [← Subsets.range_ambientEquiv f, Set.image_subset_iff]

/-! ### Enumerations -/

/-- Partial sequences `ℕ → Option X`, transported pointwise. -/
abbrev seqFunctor : Type u ⥤ Type u :=
  typeFunctor (fun X => ℕ → Option X) (fun f s n => (s n).map f)
    (fun _ s => funext fun n => by cases s n <;> rfl)
    (fun f g s => funext fun n => (Option.map_map g f (s n)).symm)

/-- Sets with an order of their elements, up to isomorphism. -/
abbrev Enumerations := IsoElements seqFunctor.{u}

/-- The elements a partial sequence enumerates. -/
def seqRange {X : Type u} (s : ℕ → Option X) : Set X := {x | ∃ n, s n = some x}

/-- `nth`: the `n`-th element of the enumeration, if any, iso-naturally. -/
def nth : Enumerations.{u} ⥤ (Core.inclusion _ ⋙ seqFunctor.{u}).Elements :=
  IsoElements.isoNatural seqFunctor (Core.inclusion _ ⋙ seqFunctor) (fun _ s => s)
    fun _ _ => rfl

/-- The subset of `X` an enumeration enumerates, as a monomorphism `range s ↪ X`. -/
def seqSubset {X : Type u} (s : ℕ → Option X) : Subsets.{u} :=
  ⟨Arrow.mk (TypeCat.ofHom (Subtype.val : seqRange s → X)),
    (mono_iff_injective _).2 Subtype.val_injective⟩

/-- Forgetting the order: an enumeration is the subset it enumerates. -/
def enumerationRange : Enumerations.{u} ⥤ Subsets.{u} where
  obj p := seqSubset p.2
  map {p q} g := ObjectProperty.homMk (Arrow.homMk
    (TypeCat.ofHom fun x => ⟨g.1.iso.hom x.1, by
      obtain ⟨n, hn⟩ := x.2
      refine ⟨n, ?_⟩
      have hg := congrFun (show (fun n => (p.2 n).map g.1.iso.hom) = q.2 from g.2) n
      rw [← hg]
      change (p.2 n).map g.1.iso.hom = _
      rw [hn]
      rfl⟩)
    g.1.iso.hom rfl)

/-! ### Finite enumerated subsets -/

/-- Duplicate-free lists, transported along equivalences: a functor on the core of `Type`. -/
abbrev nodupLists : Core (Type u) ⥤ Type u :=
  typeFunctor (fun X => {l : List X.of // l.Nodup})
    (fun f l => ⟨l.1.map f.iso.hom, l.2.map f.iso.toEquiv.injective⟩)
    (fun _ l => Subtype.ext (List.map_id' l.1))
    (fun f g l => Subtype.ext (by
      change List.map _ _ = List.map _ (List.map _ _)
      rw [List.map_map]
      rfl))

/-- Finite subsets presented as duplicate-free lists, up to isomorphism. -/
abbrev FiniteLists := nodupLists.{u}.Elements

/-- A duplicate-free list enumerates its elements. -/
def listSequence : FiniteLists.{u} ⥤ Enumerations.{u} where
  obj p := ⟨p.1, fun n => p.2.1[n]?⟩
  map {p q} g := ⟨g.1, by
    funext n
    have hg : (⟨p.2.1.map g.1.iso.hom, p.2.2.map g.1.iso.toEquiv.injective⟩ :
      {l : List q.1.of // l.Nodup}) = q.2 := g.2
    change (p.2.1[n]?).map g.1.iso.hom = (q.2.1)[n]?
    exact (List.getElem?_map ..).symm.trans (congrArg (fun l => l.1[n]?) hg)⟩

/-- The underlying set of a commutative ring. -/
abbrev ringUnderlying : CommRingCat.{u} ⥤ Type u := forget CommRingCat

/-- Duplicate-free lists in commutative rings, transported along ring isomorphisms. -/
abbrev ringNodupLists : Core CommRingCat.{u} ⥤ Type u :=
  (ringUnderlying.core) ⋙ nodupLists

/-- Finite subsets of commutative rings presented as duplicate-free lists. -/
abbrev RingFiniteLists := ringNodupLists.{u}.Elements

/-- The list of a finite subset of a ring, as a list of ring elements. -/
def RingFiniteLists.list (p : RingFiniteLists.{u}) : List p.1.of := p.2.1

/-- A finite subset of a ring is a finite subset of its underlying set. -/
def ringFiniteListsForget : RingFiniteLists.{u} ⥤ FiniteLists.{u} where
  obj p := ⟨ringUnderlying.core.obj p.1, p.2⟩
  map g := ⟨ringUnderlying.core.map g.1, g.2⟩

/-- The ring elements, transported along isomorphisms. -/
abbrev ringValues : Core CommRingCat.{u} ⥤ Type u := Core.inclusion _ ⋙ ringUnderlying

theorem ringNodupLists_map {R S : Core CommRingCat.{u}} (f : R ⟶ S) (l : ringNodupLists.obj R) :
    (ringNodupLists.map f l).1 = l.1.map f.iso.hom.hom := rfl

/-- `sum`: the sum of the elements, iso-naturally. -/
def finiteSum : RingFiniteLists.{u} ⥤ ringValues.{u}.Elements where
  obj p := ⟨p.1, (RingFiniteLists.list p).sum⟩
  map {p q} g := ⟨g.1, by
    change g.1.iso.hom.hom (RingFiniteLists.list p).sum = (RingFiniteLists.list q).sum
    have hq : RingFiniteLists.list q = (RingFiniteLists.list p).map g.1.iso.hom.hom :=
      (congrArg Subtype.val g.2).symm
    rw [hq, map_list_sum]⟩

/-- `prod`: the product of the elements, iso-naturally. -/
def finiteProd : RingFiniteLists.{u} ⥤ ringValues.{u}.Elements where
  obj p := ⟨p.1, (RingFiniteLists.list p).prod⟩
  map {p q} g := ⟨g.1, by
    change g.1.iso.hom.hom (RingFiniteLists.list p).prod = (RingFiniteLists.list q).prod
    have hq : RingFiniteLists.list q = (RingFiniteLists.list p).map g.1.iso.hom.hom :=
      (congrArg Subtype.val g.2).symm
    rw [hq, map_list_prod]⟩

/-! ### Multisets -/

/-- Multisets of elements of a set, up to isomorphism. -/
abbrev MultisetPoints := IsoElements multisetFunctor.{u}

/-- Predicates on the ambient set, transported along isomorphisms. -/
def pointPredicates : Core (Type u) ⥤ Type u :=
  typeFunctor (fun X => X.of → Prop) (fun f p y => p (f.iso.inv y)) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

/-- Predicates on subsets of the ambient set, transported along isomorphisms. -/
def subsetPredicates : Core (Type u) ⥤ Type u :=
  typeFunctor (fun X => Set X.of → Prop) (fun f P T => P (f.iso.hom ⁻¹' T)) (fun _ _ => rfl)
    (fun _ _ _ => rfl)

/-- `contains` for a multiset: membership (multiplicity at least one). -/
def multisetContains : MultisetPoints.{u} ⥤ pointPredicates.{u}.Elements :=
  IsoElements.isoNatural multisetFunctor pointPredicates (fun _ m x => x ∈ m) fun {X Y} f m => by
    funext y
    change (y ∈ m.map f.iso.hom) = (f.iso.inv y ∈ m)
    apply propext
    rw [Multiset.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨_, h, by simp⟩

/-- `cardinality` of a multiset: the number of elements with multiplicity, an invariant. -/
def multisetCard : MultisetPoints.{u} ⥤ Discrete ℕ :=
  IsoElements.isoInvariant multisetFunctor (fun _ m => Multiset.card m) fun _ m =>
    Multiset.card_map _ m

/-- `set_eq` for a multiset against a subset of the ambient set: every element occurs exactly
once and the elements are those of the subset. -/
def multisetEquals : MultisetPoints.{u} ⥤ subsetPredicates.{u}.Elements :=
  IsoElements.isoNatural multisetFunctor subsetPredicates
    (fun _ m T => m.Nodup ∧ ∀ x, x ∈ m ↔ x ∈ T) fun {X Y} f m => by
    funext T
    change ((m.map f.iso.hom).Nodup ∧ ∀ y, y ∈ m.map f.iso.hom ↔ y ∈ T) =
      (m.Nodup ∧ ∀ x, x ∈ m ↔ x ∈ f.iso.hom ⁻¹' T)
    have inj : Function.Injective (f.iso.hom : X.of → Y.of) :=
      fun a b h => f.iso.toEquiv.injective h
    have hinv : ∀ y, f.iso.hom (f.iso.inv y) = y := fun y => f.iso.toEquiv.apply_symm_apply y
    apply propext
    rw [Multiset.nodup_map_iff_of_injective inj]
    refine and_congr_right fun _ => ⟨fun h x => ?_, fun h y => ?_⟩
    · rw [Set.mem_preimage, ← h, Multiset.mem_map]
      exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨x', hx', hxx'⟩ => by rwa [inj hxx'] at hx'⟩
    · rw [Multiset.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (h x).1 hx
      · intro hy
        refine ⟨f.iso.inv y, (h _).2 ?_, hinv y⟩
        rw [Set.mem_preimage, hinv]
        exact hy

end LeanCategories.Foundation
