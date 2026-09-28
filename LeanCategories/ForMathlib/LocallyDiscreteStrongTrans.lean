/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Strong transformations out of a locally discrete bicategory

The transformation analogue of `pseudofunctorOfIsLocallyDiscrete` and
`LocallyDiscrete.mkPseudofunctor`: when the source bicategory is locally discrete, every
2-morphism is an identity, so the field `naturality_naturality` of a strong transformation holds
automatically and only the components, the naturality isomorphisms and the unit and composition
coherences are supplied.

Mathlib has no such constructor (formalization-corpus searches `mkStrongTrans`,
`StrongTrans LocallyDiscrete Cat mk`,
`strong transformation between pseudofunctors locally discrete`). Upstream candidate;
recorded in COMPLAINTS.md (LC-11).
-/

@[expose] public section

namespace CategoryTheory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- Constructor for strong transformations between pseudofunctors out of a locally discrete
bicategory. In that case the naturality of the naturality isomorphisms with respect to
2-morphisms holds automatically. -/
@[simps app naturality]
def strongTransOfIsLocallyDiscrete {B : Type u₁} [Bicategory.{w₁, v₁} B] [IsLocallyDiscrete B]
    {C : Type u₂} [Bicategory.{w₂, v₂} C] {F G : B ⥤ᵖ C}
    (app : ∀ a : B, F.obj a ⟶ G.obj a)
    (naturality : ∀ {a b : B} (f : a ⟶ b), F.map f ≫ app b ≅ app a ≫ G.map f)
    (naturality_id : ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by cat_disch)
    (naturality_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by cat_disch) :
    Pseudofunctor.StrongTrans F G where
  app := app
  naturality := naturality
  naturality_naturality {a b f g} η := by
    obtain rfl := obj_ext_of_isDiscrete η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    simp
  naturality_id := naturality_id
  naturality_comp := naturality_comp

namespace LocallyDiscrete

/-- Constructor for strong transformations between pseudofunctors out of `LocallyDiscrete B₀`,
indexed by the morphisms of `B₀`. -/
def mkStrongTrans {B₀ : Type u₁} [Category.{v₁} B₀] {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {F G : LocallyDiscrete B₀ ⥤ᵖ C}
    (app : ∀ b : B₀, F.obj ⟨b⟩ ⟶ G.obj ⟨b⟩)
    (naturality : ∀ {b b' : B₀} (f : b ⟶ b'),
      F.map f.toLoc ≫ app b' ≅ app b ≫ G.map f.toLoc)
    (naturality_id : ∀ b : B₀,
      (naturality (𝟙 b)).hom ≫ app b ◁ (G.mapId ⟨b⟩).hom =
        (F.mapId ⟨b⟩).hom ▷ app b ≫ (λ_ (app b)).hom ≫ (ρ_ (app b)).inv := by cat_disch)
    (naturality_comp : ∀ {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),
      (naturality (f ≫ g)).hom ≫ app b₀ ◁ (G.mapComp f.toLoc g.toLoc).hom =
        (F.mapComp f.toLoc g.toLoc).hom ▷ app b₂ ≫ (α_ _ _ _).hom ≫
        F.map f.toLoc ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫
        (naturality f).hom ▷ G.map g.toLoc ≫ (α_ _ _ _).hom := by cat_disch) :
    Pseudofunctor.StrongTrans F G :=
  strongTransOfIsLocallyDiscrete (fun b ↦ app b.as) (fun f ↦ naturality f.as)
    (fun b ↦ naturality_id b.as) (fun f g ↦ naturality_comp f.as g.as)

end LocallyDiscrete

end CategoryTheory
