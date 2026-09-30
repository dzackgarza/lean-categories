/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.Set.Function
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor

@[expose] public section

/-!
# Subsets as subobjects, and the set-level operations on them

A subset of a set `X` is a subobject `i : A ↪ X`: an object of `Subobjects(Set)`, the full
subcategory of `Arr(Set)` on monomorphisms (`LeanCategories.isMonoArrow`). Two functors connect it
with `Set`:

* `wholeSubset : Set ⥤ Subobjects(Set)`, `X ↦ (𝟙 : X ↪ X)`, the inclusion of each set as its own
  largest subset;
* `subsetCarrier : Subobjects(Set) ⥤ Set`, `(i : A ↪ X) ↦ A`, the domain.

Operations of a subset that take an argument in its ambient set are *natural sections*: for a
functor `G : C ⥤ Type`, a family `s X ∈ G X` natural in `X` is a natural transformation from the
terminal functor to `G`, hence (`NatTrans.mapElements`) a functor `C ⥤ ∫G` over `C`
(`sectionFunctor`). On the core of `Subobjects(Set)`:

* `subsetContains`: `(i : A ↪ X) ↦ (x ↦ x ∈ range i)`, a predicate on the ambient set;
* `subsetEquals`: `(i : A ↪ X) ↦ (T ↦ range i = T)`, a predicate on subsets of the ambient set.

Both are natural only for isomorphisms (a non-injective map of pairs does not reflect
membership), so they are functors on the core.
-/

open CategoryTheory

namespace LeanCategories.Foundation

universe u v w

section Sections

variable {C : Type u} [Category.{v} C]

/-- A natural section `s` of `G`: a natural transformation from the terminal functor. -/
def naturalSection (G : C ⥤ Type w) (s : ∀ X, G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y), G.map f (s X) = s Y) :
    (Functor.const C).obj PUnit.{w + 1} ⟶ G where
  app X := TypeCat.ofHom fun _ => s X
  naturality _ _ f := by ext; exact (h f).symm

/-- Every object is the unique element of the terminal functor over it. -/
def toTerminalElements : C ⥤ ((Functor.const C).obj PUnit.{w + 1}).Elements where
  obj X := ⟨X, PUnit.unit⟩
  map f := ⟨f, rfl⟩

/-- A natural section of `G`, as a functor `C ⥤ ∫G` over `C`. -/
def sectionFunctor (G : C ⥤ Type w) (s : ∀ X, G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y), G.map f (s X) = s Y) : C ⥤ G.Elements :=
  toTerminalElements ⋙ NatTrans.mapElements (naturalSection G s h)

@[simp] theorem sectionFunctor_obj (G : C ⥤ Type w) (s : ∀ X, G.obj X)
    (h : ∀ {X Y : C} (f : X ⟶ Y), G.map f (s X) = s Y) (X : C) :
    (sectionFunctor G s h).obj X = ⟨X, s X⟩ := rfl

end Sections

/-- Subsets: monomorphisms of sets, the full subcategory of `Arr(Type u)`. -/
abbrev Subsets := (isMonoArrow (Type u)).FullSubcategory

/-- The ambient set of a subset. -/
abbrev Subsets.ambient (S : Subsets.{u}) : Type u := S.obj.right

/-- The subset of its ambient set that a subobject is: the range of its inclusion. -/
abbrev Subsets.range (S : Subsets.{u}) : Set S.ambient := Set.range S.obj.hom

/-- Each set as its own largest subset. -/
def wholeSubset : Type u ⥤ Subsets.{u} where
  obj X := ⟨Arrow.mk (𝟙 X), inferInstanceAs (Mono (𝟙 X))⟩
  map f := ObjectProperty.homMk (Arrow.homMk f f rfl)

/-- A subset is the set it is: the domain of its inclusion. -/
def subsetCarrier : Subsets.{u} ⥤ Type u :=
  (isMonoArrow (Type u)).ι ⋙ Arrow.leftFunc

/-- An isomorphism of subsets, on ambient sets. -/
def Subsets.ambientEquiv {S T : Core Subsets.{u}} (f : S ⟶ T) : S.of.ambient ≃ T.of.ambient :=
  ((isMonoArrow (Type u)).ι ⋙ Arrow.rightFunc).mapIso f.iso |>.toEquiv

/-- An isomorphism of subsets commutes with the inclusions. -/
theorem Subsets.ambientEquiv_apply {S T : Core Subsets.{u}} (f : S ⟶ T) (a : S.of.obj.left) :
    Subsets.ambientEquiv f (S.of.obj.hom a) = T.of.obj.hom (f.iso.hom.hom.left a) :=
  (ConcreteCategory.congr_hom f.iso.hom.hom.w a).symm

theorem Subsets.ambientEquiv_symm_apply {S T : Core Subsets.{u}} (f : S ⟶ T)
    (b : T.of.obj.left) :
    (Subsets.ambientEquiv f).symm (T.of.obj.hom b) = S.of.obj.hom (f.iso.inv.hom.left b) :=
  (ConcreteCategory.congr_hom f.iso.inv.hom.w b).symm

theorem Subsets.range_ambientEquiv {S T : Core Subsets.{u}} (f : S ⟶ T) :
    (Subsets.ambientEquiv f) '' S.of.range = T.of.range := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨f.iso.hom.hom.left a, (Subsets.ambientEquiv_apply f a).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨_, ⟨f.iso.inv.hom.left b, (Subsets.ambientEquiv_symm_apply f b).symm⟩,
      Equiv.apply_symm_apply _ _⟩

/-- Predicates on the ambient set, transported along isomorphisms of subsets. -/
def ambientPredicates : Core Subsets.{u} ⥤ Type u where
  obj S := S.of.ambient → Prop
  map f := TypeCat.ofHom fun p y => p ((Subsets.ambientEquiv f).symm y)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Predicates on subsets of the ambient set, transported along isomorphisms of subsets. -/
def ambientSubsetPredicates : Core Subsets.{u} ⥤ Type u where
  obj S := Set S.of.ambient → Prop
  map f := TypeCat.ofHom fun P T => P ((Subsets.ambientEquiv f) ⁻¹' T)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Membership in a subset, `x ↦ x ∈ range i`, as a functor on the core of subsets. -/
def subsetContains : Core Subsets.{u} ⥤ ambientPredicates.{u}.Elements :=
  sectionFunctor ambientPredicates (fun S (x : S.of.ambient) => x ∈ S.of.range)
    fun {X Y} f => by
    funext y
    change ((Subsets.ambientEquiv f).symm y ∈ X.of.range) = (y ∈ Y.of.range)
    rw [← Subsets.range_ambientEquiv f, Equiv.image_eq_preimage_symm]
    rfl

/-- Equality with a subset of the ambient set, `T ↦ range i = T`, as a functor on the core of
subsets. -/
def subsetEquals : Core Subsets.{u} ⥤ ambientSubsetPredicates.{u}.Elements :=
  sectionFunctor ambientSubsetPredicates (fun S (T : Set S.of.ambient) => S.of.range = T)
    fun {X Y} f => by
    funext T
    change (X.of.range = (Subsets.ambientEquiv f) ⁻¹' T) = (Y.of.range = T)
    rw [← Subsets.range_ambientEquiv f]
    apply propext
    constructor
    · rintro h
      rw [h, Equiv.image_preimage]
    · rintro rfl
      rw [Equiv.preimage_image]

end LeanCategories.Foundation
