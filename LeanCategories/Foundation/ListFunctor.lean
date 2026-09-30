/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Data.List.Monad

@[expose] public section

/-!
# The list monad on sets

`L = List : Sets ⥤ Sets` is the free-monoid monad on sets (Mathlib's `ofTypeMonad List`): its unit
`η_X : X → L X` is `x ↦ [x]` and its multiplication `μ_X : L (L X) → L X` is concatenation.
List reversal `ρ_X : L X → L X` is a natural automorphism of `L` and its own inverse: it is natural
because `map f ∘ reverse = reverse ∘ map f` (`List.map_reverse`), and `reverse ∘ reverse = id`
(`List.reverse_reverse`). None of these components is an identity, and every component is a rule on
all of `L X`, whether or not `X` is finite.
-/

open CategoryTheory

namespace LeanCategories.Foundation

universe u

/-- The list monad on sets, `ofTypeMonad List`. -/
def listMonad : Monad (Type u) := ofTypeMonad List

/-- The list functor `L : Sets ⥤ Sets` (`Sets = Type u`, `Mathlib.Sets`). -/
def listFunctor : Type u ⥤ Type u := listMonad.toFunctor

/-- The unit `η : 𝟭 ⟶ L`, `x ↦ [x]`. -/
def listUnit : 𝟭 (Type u) ⟶ listFunctor.{u} := listMonad.η

/-- The multiplication `μ : L ⋙ L ⟶ L`, concatenation. -/
def listJoin : listFunctor.{u} ⋙ listFunctor.{u} ⟶ listFunctor.{u} := listMonad.μ

/-- Reversal, a natural transformation `L ⟶ L`. -/
def listReverseHom : listFunctor.{u} ⟶ listFunctor.{u} where
  app X := TypeCat.ofHom (List.reverse (α := X))
  naturality X Y f := by
    ext l
    exact (List.map_reverse (f := ⇑f) (l := l)).symm

theorem listReverseHom_comp_self : listReverseHom.{u} ≫ listReverseHom = 𝟙 listFunctor := by
  ext X l
  exact List.reverse_reverse (as := l)

/-- Reversal is a natural automorphism of `L`, its own inverse. -/
def listReverse : listFunctor.{u} ≅ listFunctor.{u} where
  hom := listReverseHom
  inv := listReverseHom
  hom_inv_id := listReverseHom_comp_self
  inv_hom_id := listReverseHom_comp_self

/-- The unit component `η_X = (x ↦ [x])`. Stated on the component, not applied to an element: an
applied form carries `(𝟭 _).obj X` in its coercion, which `simp` rewrites first. -/
@[simp] theorem listUnit_app (X : Type u) : listUnit.app X = ↾(fun x : X => [x]) := rfl

/-- The multiplication component `μ_X = List.flatten`. -/
@[simp] theorem listJoin_app (X : Type u) : listJoin.app X = ↾(List.flatten (α := X)) := by
  ext l
  change joinM l = l.flatten
  simp only [joinM]
  change List.flatMap id l = l.flatten
  exact List.flatMap_id

@[simp] theorem listReverse_hom_app_apply (X : Type u) (l : List X) :
    listReverse.hom.app X l = l.reverse := rfl

@[simp] theorem listReverse_inv_app_apply (X : Type u) (l : List X) :
    listReverse.inv.app X l = l.reverse := rfl

@[simp] theorem listFunctor_map_apply {X Y : Type u} (f : X ⟶ Y) (l : List X) :
    listFunctor.map f l = l.map f := rfl

end LeanCategories.Foundation
