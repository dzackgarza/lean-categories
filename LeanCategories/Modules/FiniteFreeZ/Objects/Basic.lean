module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

namespace LeanCategories.Modules.FiniteFreeZ

open CategoryTheory

universe u v

/-- Property defining objects of ZLat: finite free Z-modules. -/
structure ZLat where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℤ carrier]
  [finite : Module.Finite ℤ carrier]
  [free : Module.Free ℤ carrier]

attribute [instance] ZLat.addCommGroup ZLat.module ZLat.finite ZLat.free

/-- Morphisms in ZLat are all Z-linear maps. -/
structure Hom (M N : ZLat.{u}) where
  toLinearMap : M.carrier →ₗ[ℤ] N.carrier

def Hom.id (M : ZLat.{u}) : Hom M M where
  toLinearMap := LinearMap.id

def Hom.comp {L M N : ZLat.{u}} (g : Hom M N) (f : Hom L M) : Hom L N where
  toLinearMap := g.toLinearMap.comp f.toLinearMap

instance : Category ZLat.{u} where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end LeanCategories.Modules.FiniteFreeZ
