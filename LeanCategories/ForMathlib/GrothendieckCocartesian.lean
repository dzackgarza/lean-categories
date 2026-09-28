/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Grothendieck
public import LeanCategories.ForMathlib.Cofibered

/-!
# Cocartesian lifts in covariant Grothendieck constructions

This file supplies the covariant duals of the cartesian lifts proved for
`Pseudofunctor.CoGrothendieck` in
`Mathlib.CategoryTheory.FiberedCategory.Grothendieck`.

The proofs follow that Mathlib implementation. The strict-functor construction uses the same
argument with the definitions in `Mathlib.CategoryTheory.Grothendieck`.
-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor.Grothendieck

open Bicategory Category Functor

variable {C : Type*} [Category* C] {F : LocallyDiscrete C ⥤ᵖ Cat}
variable {R S : C} (a : F.obj ⟨R⟩) (f : R ⟶ S)

/-- The codomain of the canonical cocartesian lift of `f`. -/
abbrev codomainCocartesianLift : ∫ F := ⟨S, (F.map f.toLoc).toFunctor.obj a⟩

/-- The canonical cocartesian lift of `f`. -/
abbrev cocartesianLift : ⟨R, a⟩ ⟶ codomainCocartesianLift a f := ⟨f, 𝟙 _⟩

instance isHomLift_cocartesianLift :
    IsHomLift (forget F) f (cocartesianLift a f) :=
  IsHomLift.map (forget F) (cocartesianLift a f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {a} in
/-- The canonical factorization through a cocartesian lift. -/
abbrev homCocartesianLift {b' : ∫ F} (g : S ⟶ b'.base) (φ' : ⟨R, a⟩ ⟶ b')
    [IsHomLift (forget F) (f ≫ g) φ'] : codomainCocartesianLift a f ⟶ b' where
  base := g
  fiber :=
    have : φ'.base = f ≫ g := by simpa using IsHomLift.fac' (forget F) (f ≫ g) φ'
    (F.mapComp f.toLoc g.toLoc).inv.toNatTrans.app a ≫ eqToHom (by simp [this]) ≫ φ'.fiber

set_option backward.isDefEq.respectTransparency.types false in
instance isHomLift_homCocartesianLift {b' : ∫ F} {g : S ⟶ b'.base}
    {φ' : ⟨R, a⟩ ⟶ b'} [IsHomLift (forget F) (f ≫ g) φ'] :
    IsHomLift (forget F) g (homCocartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCocartesianLift f g φ')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isStronglyCocartesian_cocartesianLift :
    IsStronglyCocartesian (forget F) f (cocartesianLift a f) where
  universal_property' {b'} g φ' hφ' := by
    refine ⟨homCocartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (f ≫ g) φ')
        (by simp)
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp

variable (F) in
/-- The projection of a covariant Grothendieck construction is a cocartesian fibration. -/
instance isCofibered_forget : (forget F).IsCofibered :=
  IsCofibered.of_exists_isStronglyCocartesian fun x _ f ↦
    ⟨_, cocartesianLift x.fiber f, isStronglyCocartesian_cocartesianLift x.fiber f⟩

end CategoryTheory.Pseudofunctor.Grothendieck

namespace CategoryTheory.Grothendieck

open Category Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Cat.{v₂, u₂}}
variable {R S : C} (a : F.obj R) (f : R ⟶ S)

/-- The codomain of the canonical cocartesian lift of `f`. -/
abbrev codomainCocartesianLift : Grothendieck F :=
  ⟨S, (F.map f).toFunctor.obj a⟩

/-- The canonical cocartesian lift of `f` in the strict Grothendieck construction. -/
abbrev cocartesianLift :
    (⟨R, a⟩ : Grothendieck F) ⟶ codomainCocartesianLift a f :=
  ⟨f, 𝟙 _⟩

instance isHomLift_cocartesianLift :
    IsHomLift (forget F) f (cocartesianLift a f) :=
  IsHomLift.map (forget F) (cocartesianLift a f)

set_option backward.isDefEq.respectTransparency.types false in
variable {a} in
/-- The canonical factorization through a strict Grothendieck cocartesian lift. -/
abbrev homCocartesianLift {b' : Grothendieck F} (g : S ⟶ b'.base)
    (φ' : (⟨R, a⟩ : Grothendieck F) ⟶ b') [IsHomLift (forget F) (f ≫ g) φ'] :
    codomainCocartesianLift a f ⟶ b' where
  base := g
  fiber :=
    have h : φ'.base = f ≫ g := by
      simpa [forget] using IsHomLift.fac' (forget F) (f ≫ g) φ'
    eqToHom (by rw [h, ← Cat.Hom.comp_obj, ← F.map_comp]) ≫ φ'.fiber

set_option backward.isDefEq.respectTransparency.types false in
instance isHomLift_homCocartesianLift {b' : Grothendieck F} {g : S ⟶ b'.base}
    {φ' : (⟨R, a⟩ : Grothendieck F) ⟶ b'} [IsHomLift (forget F) (f ≫ g) φ'] :
    IsHomLift (forget F) g (homCocartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCocartesianLift f g φ')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isStronglyCocartesian_cocartesianLift :
    IsStronglyCocartesian (forget F) f (cocartesianLift a f) where
  universal_property' {b'} g φ' hφ' := by
    refine ⟨homCocartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Grothendieck.ext _ _ (by simpa using IsHomLift.fac (forget F) (f ≫ g) φ')
        (by simp)
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain rfl : g = χ'.base := by
      simpa [forget] using IsHomLift.fac (forget F) g χ'
    apply Grothendieck.ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism of the strict Grothendieck construction whose fibre component is an
isomorphism is strongly cocartesian: it is the canonical lift followed by a vertical
isomorphism. -/
lemma isStronglyCocartesian_of_isIso_fiber {X Y : Grothendieck F} (φ : X ⟶ Y)
    [IsIso φ.fiber] : IsStronglyCocartesian (forget F) φ.base φ := by
  rcases X with ⟨R, a⟩
  rcases Y with ⟨S, b⟩
  rcases φ with ⟨f, ψ⟩
  dsimp only at ψ ⊢
  let ι : codomainCocartesianLift a f ≅ ⟨S, b⟩ :=
    isoMk (Iso.refl _) (eqToIso (by simp) ≪≫ asIso ψ)
  have hφ : cocartesianLift a f ≫ ι.hom = ⟨f, ψ⟩ := by
    refine Grothendieck.ext _ _ (by simp [ι]) ?_
    simp [ι]
  have : IsHomLift (forget F) (𝟙 S) ι.hom := IsHomLift.map (forget F) ι.hom
  have := IsStronglyCocartesian.of_iso (forget F) (𝟙 S) ι
  have := isStronglyCocartesian_cocartesianLift a f
  have : IsStronglyCocartesian (forget F) (f ≫ 𝟙 S) (cocartesianLift a f ≫ ι.hom) :=
    inferInstance
  rwa [hφ, comp_id] at this

variable (F) in
/-- The projection of a strict covariant Grothendieck construction is a cocartesian
fibration. -/
instance isCofibered_forget : (forget F).IsCofibered :=
  IsCofibered.of_exists_isStronglyCocartesian fun x _ f ↦
    ⟨_, cocartesianLift x.fiber f, isStronglyCocartesian_cocartesianLift x.fiber f⟩

end CategoryTheory.Grothendieck
