/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

open CategoryTheory
open Opposite

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- The contravariant functor of `W`-valued quadratic maps on `R`-modules. -/
def quadraticMaps : (ModuleCat.{u} R)ᵒᵖ ⥤ Type u where
  obj M := QuadraticMap R ((M.unop : ModuleCat R) : Type u) W
  map f := ↾fun q ↦ q.comp f.unop.hom
  map_id M := by
    ext q x
    rfl
  map_comp f g := by
    ext q x
    rfl

/-- The category of `W`-valued quadratic modules. -/
abbrev QuadModuleCat := (quadraticMaps R W).Elementsᵒᵖ

namespace QuadModuleCat

variable {R W}

/-- The underlying `R`-module. -/
def carrierObj (Q : QuadModuleCat R W) : ModuleCat R :=
  (unop Q).1.unop

abbrev carrier (Q : QuadModuleCat R W) := Q.carrierObj

/-- The quadratic map of a quadratic module. -/
def form (Q : QuadModuleCat R W) : QuadraticMap R Q.carrier W :=
  (unop Q).2

/-- The underlying linear map of a morphism. -/
def underlyingMap {Q P : QuadModuleCat R W} (f : Q ⟶ P) :
    Q.carrier →ₗ[R] P.carrier :=
  f.unop.val.unop.hom

/-- Morphisms preserve the quadratic map. -/
theorem map_form {Q P : QuadModuleCat R W} (f : Q ⟶ P) (x : Q.carrier) :
    P.form (underlyingMap f x) = Q.form x := by
  have h := f.unop.property
  exact QuadraticMap.congr_fun h x

end QuadModuleCat

/-- The forgetful functor from quadratic modules to modules. -/
def forget : QuadModuleCat R W ⥤ ModuleCat R where
  obj := QuadModuleCat.carrierObj
  map := fun f ↦ ModuleCat.ofHom (QuadModuleCat.underlyingMap f)
  map_id _ := rfl
  map_comp _ _ := rfl

end LeanCategories.Modules.Quadratic.Valued
