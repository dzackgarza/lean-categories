/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Set.Image

@[expose] public section

/-!
# Elements of structured objects, up to isomorphism, and their operations

For a functor `U : C ⥤ Type` (the underlying set of a class of structures), the *points* of `C`
are the pairs `(X, x)` with `x ∈ U X`, and an isomorphism of points is an isomorphism `φ : X ≅ Y`
of `C` with `φ x = y`: the category of elements of `U` restricted to the core of `C`,

  `IsoElements U := ∫ (Core.inclusion C ⋙ U)`  (Mathlib `Functor.Elements`).

An *operation on elements* is a family of values `f X x` depending on the structure only up to
isomorphism:

* `isoInvariant`: values in a fixed set `T`, invariant under isomorphisms, is a functor
  `IsoElements U ⥤ Discrete T` (primality of an element, the degree of a polynomial);
* `isoNatural`: values in `G X` for a functor `G` on the core, natural under isomorphisms, is a
  functor `IsoElements U ⥤ ∫G` over the core (the derivative of a polynomial, the determinant of
  a matrix, a factorization of an element).

An operation that takes further arguments in the same structure is curried: its values lie in a
functor of functions (`gcd x : R → R/~`).

`IsoElements.restrict F` carries points along a functor `F : C ⥤ D` over which the underlying sets
agree (`F ⋙ U'`), e.g. the inclusion of euclidean domains into principal ideal domains.
-/

open CategoryTheory

namespace LeanCategories.Foundation

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C]

/-- A `Type`-valued functor from a family of functions satisfying the functor laws pointwise. -/
def typeFunctor (obj : C → Type w) (map : ∀ {X Y : C}, (X ⟶ Y) → obj X → obj Y)
    (map_id : ∀ (X : C) (x : obj X), map (𝟙 X) x = x)
    (map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : obj X),
      map (f ≫ g) x = map g (map f x)) : C ⥤ Type w where
  obj := obj
  map f := TypeCat.ofHom (map f)
  map_id X := TypeCat.Hom.ext (TypeCat.Fun.ext (funext (map_id X)))
  map_comp f g := TypeCat.Hom.ext (TypeCat.Fun.ext (funext (map_comp f g)))

@[simp] theorem typeFunctor_map_apply (obj : C → Type w)
    (map : ∀ {X Y : C}, (X ⟶ Y) → obj X → obj Y) (map_id map_comp) {X Y : C} (f : X ⟶ Y)
    (x : obj X) : (typeFunctor obj map map_id map_comp).map f x = map f x := rfl

/-- The covariant powerset functor: `X ↦ Set X`, `f ↦ f ''`. -/
def powersetFunctor : Type u ⥤ Type u :=
  typeFunctor Set (fun f S => f '' S) (fun _ S => Set.image_id S)
    (fun f g S => (Set.image_image g f S).symm)

/-- The multiset functor: `X ↦ Multiset X`, `f ↦ Multiset.map f`. -/
def multisetFunctor : Type u ⥤ Type u :=
  typeFunctor Multiset (fun f s => s.map f) (fun _ s => Multiset.map_id' s)
    (fun f g s => (Multiset.map_map g f s).symm)

/-- Points of the objects of `C`, with isomorphisms: `∫ (U ∘ Core.inclusion)`. -/
abbrev IsoElements (U : C ⥤ Type w) := (Core.inclusion C ⋙ U).Elements

namespace IsoElements

/-- An isomorphism of points carries the element. -/
theorem map_snd {U : C ⥤ Type w} {p q : IsoElements U} (g : p ⟶ q) :
    U.map g.1.iso.hom p.2 = q.2 := g.2

/-- An iso-invariant function of elements, as a functor into a discrete category. -/
def isoInvariant (U : C ⥤ Type w) {T : Type w'} (f : ∀ X, U.obj X → T)
    (h : ∀ {X Y : C} (φ : X ≅ Y) (x : U.obj X), f Y (U.map φ.hom x) = f X x) :
    IsoElements U ⥤ Discrete T where
  obj p := ⟨f p.1.of p.2⟩
  map {p q} g := eqToHom (congrArg Discrete.mk
    ((h g.1.iso p.2).symm.trans (congrArg (f q.1.of) (map_snd g))))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp] theorem isoInvariant_obj (U : C ⥤ Type w) {T : Type w'} (f : ∀ X, U.obj X → T)
    (h : ∀ {X Y : C} (φ : X ≅ Y) (x : U.obj X), f Y (U.map φ.hom x) = f X x)
    (p : IsoElements U) : ((isoInvariant U f h).obj p).as = f p.1.of p.2 := rfl

/-- An iso-natural family of values in `G`, a functor on the core, as a functor over the core
into `∫G`. For an operation natural for all morphisms, `G` is `Core.inclusion C ⋙ G'`. -/
def isoNatural (U : C ⥤ Type w) (G : Core C ⥤ Type w') (f : ∀ X, U.obj X → G.obj ⟨X⟩)
    (h : ∀ {X Y : Core C} (φ : X ⟶ Y) (x : U.obj X.of),
      f Y.of (U.map φ.iso.hom x) = G.map φ (f X.of x)) :
    IsoElements U ⥤ G.Elements where
  obj p := ⟨p.1, f p.1.of p.2⟩
  map {p q} g := ⟨g.1, (h g.1 p.2).symm.trans (congrArg (f q.1.of) (map_snd g))⟩

@[simp] theorem isoNatural_obj (U : C ⥤ Type w) (G : Core C ⥤ Type w')
    (f : ∀ X, U.obj X → G.obj ⟨X⟩)
    (h : ∀ {X Y : Core C} (φ : X ⟶ Y) (x : U.obj X.of),
      f Y.of (U.map φ.iso.hom x) = G.map φ (f X.of x))
    (p : IsoElements U) : (isoNatural U G f h).obj p = ⟨p.1, f p.1.of p.2⟩ := rfl

variable {D : Type u'} [Category.{v'} D]

/-- Points along a functor `F : C ⥤ D`: `(X, x) ↦ (F X, x)`. -/
def restrict (F : C ⥤ D) (U : D ⥤ Type w) : IsoElements (F ⋙ U) ⥤ IsoElements U where
  obj p := ⟨⟨F.obj p.1.of⟩, p.2⟩
  map g := ⟨F.core.map g.1, g.2⟩

end IsoElements

end LeanCategories.Foundation
